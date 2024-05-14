//===- SplitFuncs.cpp -----------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/Arc/ArcOps.h"
#include "circt/Dialect/Arc/ArcPasses.h"
#include "mlir/Analysis/Liveness.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Value.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Transforms/RegionUtils.h"
#include "llvm/ADT/STLExtras.h"
#include <string>

#define DEBUG_TYPE "arc-split-funcs"

namespace circt {
namespace arc {
#define GEN_PASS_DEF_SPLITFUNCS
#include "circt/Dialect/Arc/ArcPasses.h.inc"
} // namespace arc
} // namespace circt

using namespace mlir;
using namespace circt;
using namespace func;

//===----------------------------------------------------------------------===//
// Pass Implementation
//===----------------------------------------------------------------------===//

namespace {
struct SplitFuncsPass : public arc::impl::SplitFuncsBase<SplitFuncsPass> {
  SplitFuncsPass() = default;
  explicit SplitFuncsPass(unsigned splitBound) : SplitFuncsPass() {
    this->splitBound.setValue(splitBound);
  }
  SplitFuncsPass(const SplitFuncsPass &pass) : SplitFuncsPass() {}

  void runOnOperation() override;
  LogicalResult lowerFunc(FuncOp funcOp);

  SymbolTable *symbolTable;

  Statistic numFuncsCreated{this, "funcs-created",
                            "Number of new functions created"};

  using SplitFuncsBase::splitBound;
};
} // namespace

void SplitFuncsPass::runOnOperation() {
  symbolTable = &getAnalysis<SymbolTable>();
  for (auto op : llvm::make_early_inc_range(getOperation().getOps<FuncOp>()))
    if (failed(lowerFunc(op)))
      return signalPassFailure();
}

LogicalResult SplitFuncsPass::lowerFunc(FuncOp funcOp) {
  assert(splitBound != 0 && "Cannot split functions into functions of size 0");
  unsigned numOps = funcOp.front().getOperations().size();
  if (numOps < splitBound)
    return success();
  int numBlocks = ceil((float)numOps / splitBound);
  OpBuilder opBuilder(funcOp->getContext());
  std::vector<Block *> blocks;
  assert(funcOp->getNumRegions() == 1);
  Block *frontBlock = &(funcOp.getBody().front());
  blocks.push_back(frontBlock);
  for (int i = 0; i < numBlocks - 1; i++) {
    std::vector<Location> locs;
    for (unsigned long j = 0; j < frontBlock->getArgumentTypes().size(); j++) {
      locs.push_back(funcOp.getLoc());
    }
    auto *block = opBuilder.createBlock(&(funcOp.getBody()), {},
                                        frontBlock->getArgumentTypes(), locs);
    blocks.push_back(block);
  }

  unsigned numOpsInBlock = 0;
  std::vector<Block *>::iterator blockIter = blocks.begin();
  for (auto &op : llvm::make_early_inc_range(*frontBlock)) {
    if (numOpsInBlock >= splitBound) {
      blockIter++;
      numOpsInBlock = 0;
      opBuilder.setInsertionPointToEnd(*blockIter);
    }
    numOpsInBlock++;
    // Don't bother moving ops to the original block
    if (*blockIter == (frontBlock))
      continue;
    // Remove op from original block and insert in new block
    op.remove();
    (*blockIter)->push_back(&op);
  }
  DenseMap<Value, Value> argMap;
  // Move function arguments to the block that will stay in the function
  for (unsigned argIndex = 0; argIndex < frontBlock->getNumArguments();
       argIndex++) {
    auto oldArg = frontBlock->getArgument(argIndex);
    auto newArg = blocks.back()->getArgument(argIndex);
    replaceAllUsesInRegionWith(oldArg, newArg, funcOp.getBody());
  }
  Liveness liveness(funcOp);
  auto argTypes = blocks.back()->getArgumentTypes();
  auto args = blocks.back()->getArguments();

  // Create return ops
  for (int i = blocks.size() - 2; i >= 0; --i) {
    liveness = Liveness(funcOp);
    Block *currentBlock = blocks[i];
    Liveness::ValueSetT liveOut = liveness.getLiveIn(blocks[i + 1]);
    std::vector<Value> outValues;
    llvm::for_each(liveOut, [&outValues](auto el) {
      if (!dyn_cast<BlockArgument>(el))
        outValues.push_back(el);
    });
    opBuilder.setInsertionPointToEnd(currentBlock);
    opBuilder.create<ReturnOp>(funcOp->getLoc(), outValues);
  }
  // Create and populate new FuncOps
  for (long unsigned i = 0; i < blocks.size() - 1; i++) {
    Block *currentBlock = blocks[i];
    Liveness::ValueSetT liveOut = liveness.getLiveIn(blocks[i + 1]);
    std::vector<Type> outTypes;
    std::vector<Value> outValues;
    llvm::for_each(liveOut, [&outTypes, &outValues](auto el) {
      if (!dyn_cast<BlockArgument>(el)) {
        outValues.push_back(el);
        outTypes.push_back(el.getType());
      }
    });
    opBuilder.setInsertionPoint(funcOp);
    SmallString<64> funcName;
    funcName.append(funcOp.getName());
    funcName.append("_split_func");
    funcName.append(std::to_string(i));
    auto newFunc =
        opBuilder.create<FuncOp>(funcOp->getLoc(), funcName,
                                 opBuilder.getFunctionType(argTypes, outTypes));
    numFuncsCreated++;
    symbolTable->insert(newFunc);
    auto *funcBlock = newFunc.addEntryBlock();
    for (auto &op : make_early_inc_range(currentBlock->getOperations())) {
      op.remove();
      funcBlock->push_back(&op);
    }
    currentBlock->erase();

    opBuilder.setInsertionPointToEnd(funcBlock);
    int j = 0;
    for (auto el : args) {
      replaceAllUsesInRegionWith(el, newFunc.getArgument(j++),
                                 newFunc.getRegion());
    }
    for (auto pair : argMap) {
      replaceAllUsesInRegionWith(pair.first, pair.second, newFunc.getRegion());
    }
    opBuilder.setInsertionPointToStart(blocks[i + 1]);
    Operation *callOp = opBuilder.create<func::CallOp>(
        funcOp->getLoc(), outTypes, funcName, args);
    auto callResults = callOp->getResults();
    argMap.clear();
    for (unsigned long k = 0; k < outValues.size(); k++) {
      argMap.insert(std::pair(outValues[k], callResults[k]));
    }
  }
  for (auto pair : argMap) {
    replaceAllUsesInRegionWith(pair.first, pair.second, funcOp.getRegion());
  }
  return success();
}

std::unique_ptr<Pass> arc::createSplitFuncsPass(unsigned splitBound) {
  return std::make_unique<SplitFuncsPass>(splitBound);
}
