//===- StandardToHandshake.h ------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file declares passes which together will lower the Standard dialect to
// Handshake dialect.
//
//===----------------------------------------------------------------------===//

#ifndef CIRCT_CONVERSION_STANDARDTOHANDSHAKE_H_
#define CIRCT_CONVERSION_STANDARDTOHANDSHAKE_H_

#include "circt/Dialect/Handshake/HandshakeOps.h"
#include "circt/Dialect/Handshake/HandshakePasses.h"
#include "circt/Support/BackedgeBuilder.h"
#include "mlir/Transforms/DialectConversion.h"

#include <memory>

namespace mlir {
class ModuleOp;
template <typename T>
class OperationPass;
} // namespace mlir

namespace circt {

/// Converts a single value within a function into maximal SSA form. This
/// removes any implicit dataflow of this specific value within the enclosing
/// function. The function adds new block arguments wherever necessary to carry
/// the value explicitly between blocks.
/// Succeeds when it was possible to convert the value into maximal SSA form.
LogicalResult maximizeSSA(Value value, PatternRewriter &rewriter);

namespace handshake {

// ============================================================================
// Partial lowering infrastructure
// ============================================================================

using RegionLoweringFunc =
    llvm::function_ref<LogicalResult(Region &, ConversionPatternRewriter &)>;
// Convenience function for executing a PartialLowerRegion with a provided
// partial lowering function.
LogicalResult partiallyLowerRegion(const RegionLoweringFunc &loweringFunc,
                                   MLIRContext *ctx, Region &r);

// Holds the shared state of the different transformations required to transform
// Standard to Handshake operations. The transformations are expressed as member
// functions to simplify access to the state.
//
// This class' member functions expect a rewriter that matched on the parent
// operation of the encapsulated region.
class HandshakeLowering {
public:
  struct MergeOpInfo {
    Operation *op;
    Value val;
    SmallVector<Backedge> dataEdges;
    std::optional<Backedge> indexEdge{};
  };

  using BlockValues = DenseMap<Block *, std::vector<Value>>;
  using BlockOps = DenseMap<Block *, std::vector<MergeOpInfo>>;
  using ValueMap = DenseMap<Value, Value>;
  using MemRefToMemoryAccessOp =
      llvm::MapVector<Value, std::vector<Operation *>>;

  explicit HandshakeLowering(Region &r) : r(r) {}
  /// Converts every value in the region into maximal SSA form, unless the value
  /// is a block argument of type MemRef or the result of an allocation
  /// operation
  LogicalResult maximizeSSANoMem(ConversionPatternRewriter &rewriter);
  LogicalResult addMergeOps(ConversionPatternRewriter &rewriter);
  LogicalResult addBranchOps(ConversionPatternRewriter &rewriter);
  LogicalResult replaceCallOps(ConversionPatternRewriter &rewriter);

  template <typename TTerm>
  LogicalResult setControlOnlyPath(ConversionPatternRewriter &rewriter) {
    // Creates start and end points of the control-only path

    // Add start point of the control-only path to the entry block's arguments
    Block *entryBlock = &r.front();
    startCtrl = entryBlock->addArgument(rewriter.getNoneType(),
                                        rewriter.getUnknownLoc());
    setBlockEntryControl(entryBlock, startCtrl);

    // Replace original return ops with new returns with additional control
    // input
    for (auto retOp : llvm::make_early_inc_range(r.getOps<TTerm>())) {
      rewriter.setInsertionPoint(retOp);
      SmallVector<Value, 8> operands(retOp->getOperands());
      operands.push_back(startCtrl);
      rewriter.replaceOpWithNewOp<handshake::ReturnOp>(retOp, operands);
    }

    // Store the number of block arguments in each block
    DenseMap<Block *, unsigned> numArgsPerBlock;
    for (auto &block : r.getBlocks())
      numArgsPerBlock[&block] = block.getNumArguments();

    // Apply SSA maximixation on the newly added entry block argument to
    // propagate it explicitly between the start-point of the control-only
    // network and the function's terminators
    if (failed(maximizeSSA(startCtrl, rewriter)))
      return failure();

    // Identify all block arguments belonging to the control-only network
    // (needed to later insert control merges after those values). These are the
    // last arguments to blocks that got a new argument during SSA maximization
    for (auto &[block, numArgs] : numArgsPerBlock)
      if (block->getNumArguments() != numArgs)
        setBlockEntryControl(block, block->getArguments().back());

    return success();
  }

  LogicalResult connectConstantsToControl(ConversionPatternRewriter &rewriter,
                                          bool sourceConstants);

  LogicalResult feedForwardRewriting(ConversionPatternRewriter &rewriter);
  LogicalResult loopNetworkRewriting(ConversionPatternRewriter &rewriter);

  BlockOps insertMergeOps(ValueMap &mergePairs, BackedgeBuilder &edgeBuilder,
                          ConversionPatternRewriter &rewriter);

  // Insert appropriate type of Merge CMerge for control-only path,
  // Merge for single-successor blocks, Mux otherwise
  MergeOpInfo insertMerge(Block *block, Value val, BackedgeBuilder &edgeBuilder,
                          ConversionPatternRewriter &rewriter);

  // Replaces standard memory ops with their handshake version (i.e.,
  // ops which connect to memory/LSQ). Returns a map with an ordered
  // list of new ops corresponding to each memref. Later, we instantiate
  // a memory node for each memref and connect it to its load/store ops
  LogicalResult replaceMemoryOps(ConversionPatternRewriter &rewriter,
                                 MemRefToMemoryAccessOp &memRefOps);

  LogicalResult connectToMemory(ConversionPatternRewriter &rewriter,
                                MemRefToMemoryAccessOp memRefOps, bool lsq);
  void setMemOpControlInputs(ConversionPatternRewriter &rewriter,
                             ArrayRef<Operation *> memOps, Operation *memOp,
                             int offset, ArrayRef<int> cntrlInd);

  // Returns the entry control value for operations contained within this
  // block.
  Value getBlockEntryControl(Block *block) const;

  void setBlockEntryControl(Block *block, Value v);

  Region &getRegion() { return r; }
  MLIRContext *getContext() { return r.getContext(); }

protected:
  Region &r;

  /// Start point of the control-only network
  BlockArgument startCtrl;

private:
  DenseMap<Block *, Value> blockEntryControlMap;
};

// Driver for the HandshakeLowering class.
// Note: using two different vararg template names due to potantial references
// that would cause a type mismatch
template <typename T, typename... TArgs, typename... TArgs2>
LogicalResult runPartialLowering(
    T &instance,
    LogicalResult (T::*memberFunc)(ConversionPatternRewriter &, TArgs2...),
    TArgs &...args) {
  return partiallyLowerRegion(
      [&](Region &, ConversionPatternRewriter &rewriter) -> LogicalResult {
        return (instance.*memberFunc)(rewriter, args...);
      },
      instance.getContext(), instance.getRegion());
}

// Helper to check the validity of the dataflow conversion
// Driver that applies the partial lowerings expressed in HandshakeLowering to
// the region encapsulated in it. The region is assumed to have a terminator of
// type TTerm. See HandshakeLowering for the different lowering steps.
template <typename TTerm>
LogicalResult lowerRegion(HandshakeLowering &hl, bool sourceConstants,
                          bool disableTaskPipelining) {
  //  Perform initial dataflow conversion. This process allows for the use of
  //  non-deterministic merge-like operations.
  HandshakeLowering::MemRefToMemoryAccessOp memOps;

  if (failed(
          runPartialLowering(hl, &HandshakeLowering::replaceMemoryOps, memOps)))
    return failure();
  if (failed(runPartialLowering(hl, &HandshakeLowering::maximizeSSANoMem))) {
    return failure();
  }
  if (failed(runPartialLowering(hl,
                                &HandshakeLowering::setControlOnlyPath<TTerm>)))
    return failure();
  if (failed(runPartialLowering(hl, &HandshakeLowering::addMergeOps)))
    return failure();
  if (failed(runPartialLowering(hl, &HandshakeLowering::replaceCallOps)))
    return failure();
  if (failed(runPartialLowering(hl, &HandshakeLowering::addBranchOps)))
    return failure();

  // The following passes modifies the dataflow graph to being safe for task
  // pipelining. In doing so, non-deterministic merge structures are replaced
  // for deterministic structures.
  if (!disableTaskPipelining) {
    if (failed(
            runPartialLowering(hl, &HandshakeLowering::loopNetworkRewriting)))
      return failure();
    if (failed(
            runPartialLowering(hl, &HandshakeLowering::feedForwardRewriting)))
      return failure();
  }

  if (failed(runPartialLowering(
          hl, &HandshakeLowering::connectConstantsToControl, sourceConstants)))
    return failure();

  bool lsq = false;
  if (failed(runPartialLowering(hl, &HandshakeLowering::connectToMemory, memOps,
                                lsq)))
    return failure();

  return success();
}

/// Remove basic blocks inside the given region. This allows the result to be
/// a valid graph region, since multi-basic block regions are not allowed to
/// be graph regions currently.
void removeBasicBlocks(Region &r);

/// Lowers the mlir operations into handshake that are not part of the dataflow
/// conversion.
LogicalResult postDataflowConvert(Operation *op);

} // namespace handshake

std::unique_ptr<mlir::OperationPass<mlir::ModuleOp>>
createHandshakeAnalysisPass();

std::unique_ptr<mlir::OperationPass<mlir::ModuleOp>>
createStandardToHandshakePass(bool sourceConstants = false,
                              bool disableTaskPipelining = false);

std::unique_ptr<mlir::OperationPass<handshake::FuncOp>>
createHandshakeCanonicalizePass();

std::unique_ptr<mlir::OperationPass<handshake::FuncOp>>
createHandshakeRemoveBlockPass();

/// Insert additional blocks that serve as counterparts to the blocks that
/// diverged the control flow.
/// The resulting merge block tree is guaranteed to be a binary tree.
///
/// This transformation does treat loops like a single block and thus does not
/// affect them.
mlir::LogicalResult
insertMergeBlocks(mlir::Region &r, mlir::ConversionPatternRewriter &rewriter);

std::unique_ptr<mlir::Pass> createInsertMergeBlocksPass();

// Returns true if the region is into maximal SSA form i.e., if all the values
// within the region are in maximal SSA form.
bool isRegionSSAMaximized(Region &region);

/// Converts an operation's results within a function into maximal SSA form.
/// This removes any implicit dataflow of the operation's results within the
/// enclosing function. The function adds new block arguments wherever necessary
/// to carry the results explicitly between blocks.
/// Succeeds when it was possible to convert the operation's results into
/// maximal SSA form.
LogicalResult maximizeSSA(Operation *op, PatternRewriter &rewriter);

/// Converts all values defined by a block (i.e., block arguments and block's
/// operations' results) within a function into maximal SSA form. This removes
/// any implicit dataflow of those values within the enclosing function. The
/// function adds new block arguments wherever necessary to carry the values
/// explicitly between blocks.
/// Succeeds when it was possible to convert the values defined by the block
/// into maximal SSA form.
LogicalResult maximizeSSA(Block *block, PatternRewriter &rewriter);

/// Converts a region within a function into maximal SSA form. This removes any
/// implicit dataflow of the region's values. The function adds new block
/// arguments wherever necessary to carry the region's values explicitly between
/// blocks.
/// Succeeds when it was possible to convert all of the region's values into
/// maximal SSA form.
LogicalResult maximizeSSA(mlir::Region &region,
                          mlir::PatternRewriter &rewriter);

std::unique_ptr<mlir::Pass> createMaximizeSSAPass();

} // namespace circt

#endif // CIRCT_CONVERSION_STANDARDTOHANDSHAKE_H_
