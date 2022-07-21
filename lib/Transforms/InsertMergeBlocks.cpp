//===- InsertMergeBlocks.cpp - Insert Merge Blocks --------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "circt/Transforms/InsertMergeBlocks.h"
#include "PassDetail.h"
#include "circt/Analysis/ControlFlowLoopAnalysis.h"
#include "mlir/Conversion/LLVMCommon/ConversionTarget.h"
#include "mlir/Conversion/LLVMCommon/Pattern.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlow.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Dominance.h"
#include "mlir/Transforms/DialectConversion.h"
#include "llvm/ADT/TypeSwitch.h"

using namespace mlir;
using namespace circt;
using namespace circt::analysis;

/// Replaces the branching to oldDest of with an equivalent operation that
/// instead branches to newDest
static LogicalResult changeBranchTarget(Block *block, Block *oldDest,
                                        Block *newDest,
                                        ConversionPatternRewriter &rewriter) {
  rewriter.setInsertionPointToEnd(block);
  auto term = block->getTerminator();
  return llvm::TypeSwitch<Operation *, LogicalResult>(term)
      .Case<cf::BranchOp>([&](auto branchOp) {
        rewriter.replaceOpWithNewOp<cf::BranchOp>(branchOp, newDest,
                                                  branchOp->getOperands());
        return success();
      })
      .Case<cf::CondBranchOp>([&](auto condBr) {
        auto cond = condBr.getCondition();
        ValueRange trueOperands = condBr.getTrueOperands();
        ValueRange falseOperands = condBr.getFalseOperands();

        Block *trueDest = condBr.getTrueDest();
        Block *falseDest = condBr.getFalseDest();

        // change to the correct destination
        if (trueDest == oldDest)
          trueDest = newDest;

        if (falseDest == oldDest)
          falseDest = newDest;

        rewriter.replaceOpWithNewOp<cf::CondBranchOp>(
            condBr, cond, trueDest, trueOperands, falseDest, falseOperands);
        return success();
      })
      .Default([&](Operation *op) {
        return op->emitError("Unexpected terminator that cannot be handled.");
      });
}

/// Creates a new intermediate block that b1 and b2 branch to. The new block
/// branches to their common successor oldSucc.
static Block *buildMergeBlock(Block *b1, Block *b2, Block *oldSucc,
                              ConversionPatternRewriter &rewriter) {
  auto blockArgTypes = oldSucc->getArgumentTypes();
  SmallVector<Location> argLocs(blockArgTypes.size(), rewriter.getUnknownLoc());

  Block *res = rewriter.createBlock(oldSucc, blockArgTypes, argLocs);
  rewriter.create<cf::BranchOp>(rewriter.getUnknownLoc(), oldSucc,
                                res->getArguments());

  if (failed(changeBranchTarget(b1, oldSucc, res, rewriter)))
    return nullptr;
  if (failed(changeBranchTarget(b2, oldSucc, res, rewriter)))
    return nullptr;

  return res;
}

namespace {
/// A dual CFG that contracts cycles into single logical blocks.
struct DualGraph {
  DualGraph(Region &r, ControlFlowLoopAnalysis &loopAnalysis);

  size_t getNumPredecessors(Block *b) { return predCnts.lookup(b); }
  void getPredecessors(Block *b, SmallVectorImpl<Block *> &res);

  size_t getNumSuccessors(Block *b) { return succMap.lookup(b).size(); }
  ArrayRef<Block *> getSuccessors(Block *b) {
    return succMap.find(b)->getSecond();
  }

  // If the block is part of a contracted block, the header of the contracted
  // block is returned. Otherwise, the block itself is returned.
  Block *lookupDualBlock(Block *b);
  DenseMap<Block *, size_t> getPredCountMapCopy() { return predCnts; }

private:
  Region &r;
  ControlFlowLoopAnalysis &loopAnalysis;

  DenseMap<Block *, SmallVector<Block *>> succMap;
  DenseMap<Block *, size_t> predCnts;
};
} // namespace

DualGraph::DualGraph(Region &r, ControlFlowLoopAnalysis &loopAnalysis)
    : r(r), loopAnalysis(loopAnalysis), succMap(), predCnts() {
  for (Block &b : r) {
    if (!loopAnalysis.isLoopHeader(&b) && loopAnalysis.isLoopElement(&b))
      continue;

    // Create and get new succ map entry for the current block
    SmallVector<Block *> &succs =
        succMap.try_emplace(&b, SmallVector<Block *>()).first->getSecond();

    // NOTE: This assumes that there is only one exitting node, i.e., not
    // two blocks from the same loop can be predecessors of one block
    unsigned predCnt = 0;
    LoopInfo *info = loopAnalysis.getLoopInfoForHeader(&b);
    for (auto *pred : b.getPredecessors())
      if (!info || !info->inLoop.contains(pred))
        predCnt++;

    if (loopAnalysis.isLoopHeader(&b)) {
      llvm::copy(info->exitBlocks, std::back_inserter(succs));
    } else {
      llvm::copy(b.getSuccessors(), std::back_inserter(succs));
    }

    predCnts.try_emplace(&b, predCnt);
  }
}

Block *DualGraph::lookupDualBlock(Block *b) {
  if (!loopAnalysis.isLoopElement(b))
    return b;

  return loopAnalysis.getLoopInfo(b)->loopHeader;
}

void DualGraph::getPredecessors(Block *b, SmallVectorImpl<Block *> &res) {
  assert((loopAnalysis.isLoopHeader(b) || !loopAnalysis.isLoopElement(b)) &&
         "can only get predecessors of blocks in the graph");

  LoopInfo *info = loopAnalysis.getLoopInfoForHeader(b);
  for (auto *pred : b->getPredecessors()) {
    if (info && info->inLoop.contains(pred))
      continue;

    // NOTE: This will break down once multiple exit nodes are allowed
    if (loopAnalysis.isLoopElement(pred)) {
      // push back other loop header
      res.push_back(loopAnalysis.getLoopInfo(pred)->loopHeader);
      continue;
    }
    res.push_back(pred);
  }
}

namespace {
using BlockToBlockMap = DenseMap<Block *, Block *>;
/// A helper class to store the split block information gathered during analysis
/// of the CFG.
struct SplitInfo {
  /// Points to the last split block that dominates the block.
  BlockToBlockMap in;
  /// Either points to the last split block or to itself, if the block itself is
  /// a split block.
  BlockToBlockMap out;
};
} // namespace

/// Builds a binary merge block tree for the predecessors of currBlock.
static LogicalResult buildMergeBlocks(Block *currBlock, SplitInfo &splitInfo,
                                      Block *predDom,
                                      ConversionPatternRewriter &rewriter,
                                      DualGraph &graph) {
  SmallVector<Block *> preds;
  llvm::copy(currBlock->getPredecessors(), std::back_inserter(preds));

  // Map from split blocks to blocks that descend from it.
  DenseMap<Block *, Block *> predsToConsider;

  while (!preds.empty()) {
    Block *pred = preds.back();
    preds.pop_back();
    Block *splitBlock = splitInfo.out.lookup(graph.lookupDualBlock(pred));
    if (splitBlock == predDom)
      // Needs no additional merge block
      continue;

    if (predsToConsider.count(splitBlock) == 0) {
      // no other block with the same split block was found yet, so just store
      // it and continue
      predsToConsider.try_emplace(splitBlock, pred);
      continue;
    }

    // Found a pair, so insert a new merge block for them
    Block *other = predsToConsider.lookup(splitBlock);
    predsToConsider.erase(splitBlock);

    Block *mergeBlock = buildMergeBlock(pred, other, currBlock, rewriter);
    if (!mergeBlock)
      return failure();

    // update info for the newly created block
    Block *splitIn = splitInfo.in.lookup(splitBlock);
    splitInfo.in.try_emplace(mergeBlock, splitIn);
    // only one succ, so out = in
    splitInfo.out.try_emplace(mergeBlock, splitIn);

    preds.push_back(mergeBlock);
  }
  if (predsToConsider.size() != 0)
    return currBlock->getParentOp()->emitError(
        "irregular control flow is not yet supported");
  return success();
}

static LogicalResult preconditionCheck(Region &r,
                                       ControlFlowLoopAnalysis &analysis) {
  for (auto &info : analysis.topLevelLoops)
    if (info.exitBlocks.size() > 1)
      return r.getParentOp()->emitError(
          "multiple exit nodes are not yet supported");

  return success();
}

static void setupStack(DenseMap<Block *, size_t> &predCntMap,
                       SmallVector<Block *> &stack) {
  for (auto it : predCntMap)
    if (it.second == 0)
      stack.push_back(it.first);
}

/// Insert additional blocks that serve as counterparts to the blocks that
/// diverged the control flow.
/// The resulting merge block tree is guaranteed to be a binary tree.
///
/// This transformation does not affect any blocks that are part of a loop as it
/// treats a loop as one logical block.
/// Irregular control flow is not supported and results in a failed
/// transformation.
LogicalResult
circt::insertExplicitMergeBlocks(Region &r,
                                 ConversionPatternRewriter &rewriter) {
  Block *entry = &r.front();
  DominanceInfo domInfo(r.getParentOp());

  ControlFlowLoopAnalysis loopAnalysis(r);
  if (failed(loopAnalysis.analyzeRegion()))
    return failure();

  if (failed(preconditionCheck(r, loopAnalysis)))
    return failure();

  // Traversing the graph in topological order
  SmallVector<Block *> stack;

  // Holds the graph that contains the relevant blocks. It for example contracts
  // loops into one block to preserve a DAG structure.
  DualGraph graph(r, loopAnalysis);

  // Counts the amount of predecessors remaining, if it reaches 0, insert into
  // stack.
  auto predsToVisit = graph.getPredCountMapCopy();
  setupStack(predsToVisit, stack);

  // Similar to a dataflow analysis
  SplitInfo splitInfo;
  splitInfo.in.try_emplace(entry, nullptr);

  while (!stack.empty()) {
    Block *currBlock = stack.back();
    stack.pop_back();

    Block *in;
    Block *out;

    bool isMergeBlock = graph.getNumPredecessors(currBlock) > 1;
    bool isSplitBlock = graph.getNumSuccessors(currBlock) > 1;

    SmallVector<Block *> preds;
    graph.getPredecessors(currBlock, preds);

    if (isMergeBlock) {
      Block *predDom = currBlock;
      for (auto *pred : preds) {
        predDom = domInfo.findNearestCommonDominator(predDom, pred);
      }

      if (failed(
              buildMergeBlocks(currBlock, splitInfo, predDom, rewriter, graph)))
        return failure();

      // The predDom has similar properties as a normal predecessor, so we can
      // just use its IN info
      in = splitInfo.in.lookup(predDom);
    } else if (!preds.empty()) {
      Block *pred = preds.front();

      in = splitInfo.out.lookup(pred);
    }

    if (isSplitBlock) {
      out = currBlock;
    } else {
      out = in;
    }

    splitInfo.in.try_emplace(currBlock, in);
    splitInfo.out.try_emplace(currBlock, out);

    for (auto *succ : graph.getSuccessors(currBlock)) {
      auto it = predsToVisit.find(succ);
      unsigned predsRemaining = --(it->getSecond());
      // Pushing the block on the stack once all it's successors were visited
      // ensures a topological traversal.
      if (predsRemaining == 0)
        stack.push_back(succ);
    }
  }

  return success();
}

namespace {

using PtrSet = SmallPtrSet<Operation *, 4>;

struct FuncOpPattern : public OpConversionPattern<func::FuncOp> {

  FuncOpPattern(PtrSet &rewrittenFuncs, MLIRContext *ctx)
      : OpConversionPattern(ctx), rewrittenFuncs(rewrittenFuncs) {}

  LogicalResult
  matchAndRewrite(func::FuncOp op, OpAdaptor adaptor,
                  ConversionPatternRewriter &rewriter) const override {
    rewriter.startRootUpdate(op);

    if (!op.isExternal())
      if (failed(insertExplicitMergeBlocks(op.getRegion(), rewriter)))
        return failure();

    rewriter.finalizeRootUpdate(op);

    // Insert this function into the set of processed functions
    rewrittenFuncs.insert(op);

    return success();
  }

private:
  PtrSet &rewrittenFuncs;
};

struct InsertMergeBlocksPass
    : public InsertMergeBlocksBase<InsertMergeBlocksPass> {
public:
  void runOnOperation() override {
    auto *ctx = &getContext();
    RewritePatternSet patterns(ctx);
    // Remembers traversed functions to only apply the conversion once
    PtrSet rewrittenFuncs;
    patterns.add<FuncOpPattern>(rewrittenFuncs, ctx);

    ConversionTarget target(*ctx);
    target.addDynamicallyLegalOp<func::FuncOp>(
        [&](func::FuncOp func) { return rewrittenFuncs.contains(func); });
    target.addLegalDialect<cf::ControlFlowDialect>();

    if (applyPartialConversion(getOperation(), target, std::move(patterns))
            .failed())
      signalPassFailure();
  }
};

} // namespace

namespace circt {
std::unique_ptr<mlir::Pass> createInsertMergeBlocksPass() {
  return std::make_unique<InsertMergeBlocksPass>();
}
} // namespace circt
