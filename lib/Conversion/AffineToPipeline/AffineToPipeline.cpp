//===- AffineToStaticlogic.cpp --------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "circt/Conversion/AffineToPipeline.h"
#include "../PassDetail.h"
#include "circt/Analysis/DependenceAnalysis.h"
#include "circt/Analysis/SchedulingAnalysis.h"
#include "circt/Dialect/Pipeline/Pipeline.h"
#include "circt/Scheduling/Algorithms.h"
#include "circt/Scheduling/Problems.h"
#include "mlir/Conversion/AffineToStandard/AffineToStandard.h"
#include "mlir/Dialect/Affine/Analysis/AffineAnalysis.h"
#include "mlir/Dialect/Affine/Analysis/LoopAnalysis.h"
#include "mlir/Dialect/Affine/IR/AffineMemoryOpInterfaces.h"
#include "mlir/Dialect/Affine/IR/AffineOps.h"
#include "mlir/Dialect/Affine/LoopUtils.h"
#include "mlir/Dialect/Affine/Utils.h"
#include "mlir/Dialect/Arithmetic/IR/Arithmetic.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlow.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/IR/BlockAndValueMapping.h"
#include "mlir/IR/BuiltinDialect.h"
#include "mlir/IR/Dominance.h"
#include "mlir/IR/ImplicitLocOpBuilder.h"
#include "mlir/Transforms/DialectConversion.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/TypeSwitch.h"
#include "llvm/Support/Debug.h"

#define DEBUG_TYPE "affine-to-pipeline"

using namespace mlir;
using namespace mlir::arith;
using namespace mlir::memref;
using namespace mlir::scf;
using namespace mlir::func;
using namespace circt;
using namespace circt::analysis;
using namespace circt::scheduling;
using namespace circt::pipeline;

namespace {

struct AffineToPipeline : public AffineToPipelineBase<AffineToPipeline> {
  void runOnOperation() override;

private:
  LogicalResult
  lowerAffineStructures(MemoryDependenceAnalysis &dependenceAnalysis);
  LogicalResult populateOperatorTypes(SmallVectorImpl<AffineForOp> &loopNest);
  LogicalResult solveSchedulingProblem(SmallVectorImpl<AffineForOp> &loopNest);
  LogicalResult createPipelinePipeline(SmallVectorImpl<AffineForOp> &loopNest);
  LogicalResult constantCSE();
  LogicalResult unrollAndForwardStores();

  CyclicSchedulingAnalysis *schedulingAnalysis;
};

// This forwards stores to loads for a very specific, particular pattern: store-load pairs on memrefs that accumulate
// accumulates results in the body of a for loop:
//  affine.for %arg3 = 0 to 8 {
//    %3 = affine.load %arg0[%arg1, %arg3] : memref<1x8xi32>
//    %4 = affine.load %1[%arg3, %arg2] : memref<8x8xi32>
//    %5 = affine.load %2[%arg1, %arg2] : memref<1x8xi32>
//    %6 = arith.muli %3, %4 : i32
//    %7 = arith.addi %5, %6 : i32
//    affine.store %7, %2[%arg1, %arg2] : memref<1x8xi32>
//  }
// After unrolling this looks like
//  ...
//  %281 = arith.muli %278, %279 : i32
//  %282 = arith.addi %280, %281 : i32
//  affine.store %282, %1[%arg1, %241] : memref<1x8xi32>
//  %283 = affine.apply #map6(%c0_0)
//  %284 = affine.load %arg0[%arg1, %283] : memref<1x8xi32>
//  %285 = affine.load %0[%283, %241] : memref<8x8xi32>
//  %286 = affine.load %1[%arg1, %241] : memref<1x8xi32>
//  %287 = arith.muli %284, %285 : i32
// where we observe that affine.store %282 can be forwarded to %284 = affine.load.
// Thus, in this method we search for such pairs - a load and its immediately prior store.
static LogicalResult forwardFullyUnrolledStoreToLoad(AffineReadOpInterface loadOp,
                                                     SmallVectorImpl<Operation *> &opsToErase) {
  Operation *prevOp = loadOp->getPrevNode();
  while (prevOp) {
    auto storeOp = dyn_cast<AffineWriteOpInterface>(prevOp);
    if (!storeOp) {
      prevOp = prevOp->getPrevNode();
      continue;
    }

    MemRefAccess srcAccess(storeOp);
    MemRefAccess dstAccess(loadOp);

    if (srcAccess != dstAccess)
      return failure();

    // Since we forward only from the immediately prior store, we verify that there are neither intervening
    // stores nor intervening loads in between.
    if (!mlir::hasNoInterveningEffect<MemoryEffects::Write>(storeOp, loadOp))
      return failure();

    // Perform the actual store to load forwarding.
    Value storeVal = cast<AffineWriteOpInterface>(storeOp).getValueToStore();
    // Check if 2 values have the same shape. This is needed for affine
    // vector loads and stores.
    if (storeVal.getType() != loadOp.getValue().getType())
      return failure();
    loadOp.getValue().replaceAllUsesWith(storeVal);
    // Record this to erase later.
    opsToErase.push_back(storeOp);
    // Record this to erase later.
    opsToErase.push_back(loadOp);
    return success();
  }
  return failure();
}

} // namespace

void AffineToPipeline::runOnOperation() {
  if (failed(unrollAndForwardStores()))
    return signalPassFailure();

  // auto dependenceAnalysis = getAnalysis<MemoryDependenceAnalysis>();
  auto funcOp = getOperation();
  ImplicitLocOpBuilder builder(funcOp.getLoc(), funcOp);
  auto dummyFuncOp =
      builder.create<func::FuncOp>("dummyFuncOp", funcOp.getFunctionType());
  MemoryDependenceAnalysis dependenceAnalysis(dummyFuncOp);
  dummyFuncOp.erase();

  // After dependence analysis, materialize affine structures.
  if (failed(lowerAffineStructures(dependenceAnalysis)))
    return signalPassFailure();

  if (failed(constantCSE()))
    return signalPassFailure();

  // Get scheduling analysis for the whole function.
  schedulingAnalysis = &getAnalysis<CyclicSchedulingAnalysis>();

  // Collect perfectly nested loops and work on them.
  auto outerLoops = getOperation().getOps<AffineForOp>();
  for (auto root : llvm::make_early_inc_range(outerLoops)) {
    SmallVector<AffineForOp> nestedLoops;
    getPerfectlyNestedLoops(nestedLoops, root);

    // Populate the target operator types.
    if (failed(populateOperatorTypes(nestedLoops)))
      return signalPassFailure();

    // Solve the scheduling problem computed by the analysis.
    if (failed(solveSchedulingProblem(nestedLoops)))
      return signalPassFailure();

    // Convert the IR.
    if (failed(createPipelinePipeline(nestedLoops)))
      return signalPassFailure();
  }
}

/// Apply the affine map from an 'affine.load' operation to its operands, and
/// feed the results to a newly created 'memref.load' operation (which replaces
/// the original 'affine.load').
/// Also replaces the affine load with the memref load in dependenceAnalysis.
/// TODO(mikeurbach): this is copied from AffineToStandard, see if we can reuse.
class AffineLoadLowering : public OpConversionPattern<AffineLoadOp> {
public:
  AffineLoadLowering(MLIRContext *context,
                     MemoryDependenceAnalysis &dependenceAnalysis)
      : OpConversionPattern(context), dependenceAnalysis(dependenceAnalysis) {}

  LogicalResult
  matchAndRewrite(AffineLoadOp op, OpAdaptor adaptor,
                  ConversionPatternRewriter &rewriter) const override {
    // Expand affine map from 'affineLoadOp'.
    SmallVector<Value, 8> indices(op.getMapOperands());
    auto resultOperands =
        expandAffineMap(rewriter, op.getLoc(), op.getAffineMap(), indices);
    if (!resultOperands)
      return failure();

    // Build memref.load memref[expandedMap.results].
    auto memrefLoad = rewriter.replaceOpWithNewOp<memref::LoadOp>(
        op, op.getMemRef(), *resultOperands);

    dependenceAnalysis.replaceOp(op, memrefLoad);

    return success();
  }

private:
  MemoryDependenceAnalysis &dependenceAnalysis;
};

/// Apply the affine map from an 'affine.store' operation to its operands, and
/// feed the results to a newly created 'memref.store' operation (which replaces
/// the original 'affine.store').
/// Also replaces the affine store with the memref store in dependenceAnalysis.
/// TODO(mikeurbach): this is copied from AffineToStandard, see if we can reuse.
class AffineStoreLowering : public OpConversionPattern<AffineStoreOp> {
public:
  AffineStoreLowering(MLIRContext *context,
                      MemoryDependenceAnalysis &dependenceAnalysis)
      : OpConversionPattern(context), dependenceAnalysis(dependenceAnalysis) {}

  LogicalResult
  matchAndRewrite(AffineStoreOp op, OpAdaptor adaptor,
                  ConversionPatternRewriter &rewriter) const override {
    // Expand affine map from 'affineStoreOp'.
    SmallVector<Value, 8> indices(op.getMapOperands());
    auto maybeExpandedMap =
        expandAffineMap(rewriter, op.getLoc(), op.getAffineMap(), indices);
    if (!maybeExpandedMap)
      return failure();

    // Build memref.store valueToStore, memref[expandedMap.results].
    auto memrefStore = rewriter.replaceOpWithNewOp<memref::StoreOp>(
        op, op.getValueToStore(), op.getMemRef(), *maybeExpandedMap);

    dependenceAnalysis.replaceOp(op, memrefStore);

    return success();
  }

private:
  MemoryDependenceAnalysis &dependenceAnalysis;
};

/// Helper to hoist computation out of scf::IfOp branches, turning it into a
/// mux-like operation, and exposing potentially concurrent execution of its
/// branches.
struct IfOpHoisting : OpConversionPattern<IfOp> {
  using OpConversionPattern<IfOp>::OpConversionPattern;

  LogicalResult
  matchAndRewrite(IfOp op, OpAdaptor adaptor,
                  ConversionPatternRewriter &rewriter) const override {
    rewriter.updateRootInPlace(op, [&]() {
      if (!op.thenBlock()->without_terminator().empty()) {
        rewriter.splitBlock(op.thenBlock(), --op.thenBlock()->end());
        rewriter.mergeBlockBefore(&op.getThenRegion().front(), op);
      }
      if (op.elseBlock() && !op.elseBlock()->without_terminator().empty()) {
        rewriter.splitBlock(op.elseBlock(), --op.elseBlock()->end());
        rewriter.mergeBlockBefore(&op.getElseRegion().front(), op);
      }
    });

    return success();
  }
};

class AffineApplyLowering : public OpRewritePattern<AffineApplyOp> {
public:
  using OpRewritePattern<AffineApplyOp>::OpRewritePattern;

  LogicalResult matchAndRewrite(AffineApplyOp op,
                                PatternRewriter &rewriter) const override {
    auto maybeExpandedMap =
        expandAffineMap(rewriter, op.getLoc(), op.getAffineMap(),
                        llvm::to_vector<8>(op.getOperands()));
    if (!maybeExpandedMap)
      return failure();
    rewriter.replaceOp(op, *maybeExpandedMap);
    return success();
  }
};

/// Helper to determine if an scf::IfOp is in mux-like form.
static bool ifOpLegalityCallback(IfOp op) {
  return op.thenBlock()->without_terminator().empty() &&
         (!op.elseBlock() || op.elseBlock()->without_terminator().empty());
}

/// Helper to mark AffineYieldOp legal, unless it is inside a partially
/// converted scf::IfOp.
static bool yieldOpLegalityCallback(AffineYieldOp op) {
  return !op->getParentOfType<IfOp>();
}

/// After analyzing memory dependences, and before creating the schedule, we
/// want to materialize affine operations with arithmetic, scf, and memref
/// operations, which make the condition computation of addresses, etc.
/// explicit. This is important so the schedule can consider potentially complex
/// computations in the condition of ifs, or the addresses of loads and stores.
/// The dependence analysis will be updated so the dependences from the affine
/// loads and stores are now on the memref loads and stores.
LogicalResult AffineToPipeline::lowerAffineStructures(
    MemoryDependenceAnalysis &dependenceAnalysis) {
  auto *context = &getContext();
  auto op = getOperation();

  ConversionTarget target(*context);
  target.addLegalDialect<AffineDialect, ArithmeticDialect, MemRefDialect,
                         SCFDialect>();
  target.addIllegalOp<AffineIfOp, AffineLoadOp, AffineStoreOp, AffineApplyOp>();
  target.addDynamicallyLegalOp<IfOp>(ifOpLegalityCallback);
  target.addDynamicallyLegalOp<AffineYieldOp>(yieldOpLegalityCallback);

  RewritePatternSet patterns(context);
  populateAffineToStdConversionPatterns(patterns);
  patterns.add<AffineLoadLowering>(context, dependenceAnalysis);
  patterns.add<AffineStoreLowering>(context, dependenceAnalysis);
  patterns.add<IfOpHoisting>(context);
  patterns.add<AffineApplyLowering>(context);

  if (failed(applyPartialConversion(op, target, std::move(patterns))))
    return failure();

  return success();
}

/// Populate the schedling problem operator types for the dialect we are
/// targetting. Right now, we assume Calyx, which has a standard library with
/// well-defined operator latencies. Ultimately, we should move this to a
/// dialect interface in the Scheduling dialect.
LogicalResult AffineToPipeline::populateOperatorTypes(
    SmallVectorImpl<AffineForOp> &loopNest) {
  // Scheduling analyis only considers the innermost loop nest for now.
  auto forOp = loopNest.back();

  // Retrieve the cyclic scheduling problem for this loop.
  CyclicProblem &problem = schedulingAnalysis->getProblem(forOp);

  // Load the Calyx operator library into the problem. This is a very minimal
  // set of arithmetic and memory operators for now. This should ultimately be
  // pulled out into some sort of dialect interface.
  Problem::OperatorType combOpr = problem.getOrInsertOperatorType("comb");
  problem.setLatency(combOpr, 0);
  Problem::OperatorType seqOpr = problem.getOrInsertOperatorType("seq");
  problem.setLatency(seqOpr, 1);
  Problem::OperatorType mcOpr = problem.getOrInsertOperatorType("multicycle");
  problem.setLatency(mcOpr, 3);

  Operation *unsupported;
  WalkResult result = forOp.getBody()->walk([&](Operation *op) {
    return TypeSwitch<Operation *, WalkResult>(op)
        .Case<AddIOp, IfOp, AffineYieldOp, arith::ConstantOp, CmpIOp,
              IndexCastOp, memref::AllocaOp, YieldOp, arith::SelectOp>(
            [&](Operation *combOp) {
              // Some known combinational ops.
              problem.setLinkedOperatorType(combOp, combOpr);
              return WalkResult::advance();
            })
        .Case<AffineLoadOp, AffineStoreOp, memref::LoadOp, memref::StoreOp>(
            [&](Operation *seqOp) {
              // Some known sequential ops. In certain cases, reads may be
              // combinational in Calyx, but taking advantage of that is left as
              // a future enhancement.
              problem.setLinkedOperatorType(seqOp, seqOpr);
              return WalkResult::advance();
            })
        .Case<MulIOp>([&](Operation *mcOp) {
          // Some known multi-cycle ops.
          problem.setLinkedOperatorType(mcOp, mcOpr);
          return WalkResult::advance();
        })
        .Default([&](Operation *badOp) {
          unsupported = op;
          return WalkResult::interrupt();
        });
  });

  if (result.wasInterrupted())
    return forOp.emitError("unsupported operation ") << *unsupported;

  return success();
}

/// Solve the pre-computed scheduling problem.
LogicalResult AffineToPipeline::solveSchedulingProblem(
    SmallVectorImpl<AffineForOp> &loopNest) {
  // Scheduling analyis only considers the innermost loop nest for now.
  auto forOp = loopNest.back();

  // Retrieve the cyclic scheduling problem for this loop.
  CyclicProblem &problem = schedulingAnalysis->getProblem(forOp);

  // Optionally debug problem inputs.
  LLVM_DEBUG(forOp.getBody()->walk<WalkOrder::PreOrder>([&](Operation *op) {
    llvm::dbgs() << "Scheduling inputs for " << *op;
    auto opr = problem.getLinkedOperatorType(op);
    llvm::dbgs() << "\n  opr = " << opr;
    llvm::dbgs() << "\n  latency = " << problem.getLatency(*opr);
    for (auto dep : problem.getDependences(op))
      if (dep.isAuxiliary())
        llvm::dbgs() << "\n  dep = { distance = " << problem.getDistance(dep)
                     << ", source = " << *dep.getSource() << " }";
    llvm::dbgs() << "\n\n";
  }));

  // Verify and solve the problem.
  if (failed(problem.check()))
    return failure();

  auto *anchor = forOp.getBody()->getTerminator();
  if (failed(scheduleSimplex(problem, anchor)))
    return failure();

  // Verify the solution.
  if (failed(problem.verify()))
    return failure();

  // Optionally debug problem outputs.
  LLVM_DEBUG({
    llvm::dbgs() << "Scheduled initiation interval = "
                 << problem.getInitiationInterval() << "\n\n";
    forOp.getBody()->walk<WalkOrder::PreOrder>([&](Operation *op) {
      llvm::dbgs() << "Scheduling outputs for " << *op;
      llvm::dbgs() << "\n  start = " << problem.getStartTime(op);
      llvm::dbgs() << "\n\n";
    });
  });

  return success();
}

LogicalResult AffineToPipeline::constantCSE() {
  auto funcOp = mlir::OperationPass<FuncOp>::getOperation();
  SmallVector<arith::ConstantOp, 8> constsToRemove;
  llvm::SmallDenseMap<TypedAttr, arith::ConstantOp> knownConstants;
  funcOp.walk([&](arith::ConstantOp constOp) {
    auto val = constOp.getValue();
    if (!knownConstants.count(val))
      knownConstants[val] = constOp;
    else
      constsToRemove.push_back(constOp);
  });
  if (knownConstants.empty())
    return success();

  auto firstConst = *funcOp.getOps<arith::ConstantOp>().begin();
  for (auto &item : knownConstants) {
    auto constOp = item.getSecond();
    if (constOp != firstConst)
      constOp->moveAfter(firstConst);
  }
  for (auto &constOp : constsToRemove) {
    constOp->replaceAllUsesWith(knownConstants[constOp.getValue()]);
  }
  for (auto &constOp : constsToRemove) {
    constOp->erase();
  }
  return success();
}

LogicalResult AffineToPipeline::unrollAndForwardStores() {
  auto outerLoops = getOperation().getOps<AffineForOp>();
  for (auto root : llvm::make_early_inc_range(outerLoops)) {
    SmallVector<AffineForOp> nestedLoops;
    getPerfectlyNestedLoops(nestedLoops, root);
    if (nestedLoops.size() != 1) {
      nestedLoops[0].getBody(0)->walk<WalkOrder::PostOrder>([&](AffineForOp forOp) {
        // TODO(max): figure out a smarter way to compute factor (something something dependence analysis)
        auto unrollFactor = getConstantTripCount(forOp).value_or(std::numeric_limits<int>::max());
        if (failed(loopUnrollUpToFactor(forOp, unrollFactor)))
          return signalPassFailure();
      });
    }
  }

  SmallVector<Operation *, 8> opsToErase;
  for (auto forOp : llvm::make_early_inc_range(outerLoops)) {
    // Walk all load's and perform store to load forwarding.
    forOp.walk([&](AffineReadOpInterface loadOp) {
      forwardFullyUnrolledStoreToLoad(loadOp, opsToErase);
    });
    // Erase all load op's whose results were replaced with store fwd'ed ones.
    for (auto *op : opsToErase)
      op->erase();
    opsToErase.clear();
  }
  return success();
}

/// Create the pipeline op for a loop nest.
LogicalResult AffineToPipeline::createPipelinePipeline(
    SmallVectorImpl<AffineForOp> &loopNest) {
  // Scheduling analyis only considers the innermost loop nest for now.
  auto forOp = loopNest.back();

  // Retrieve the cyclic scheduling problem for this loop.
  CyclicProblem &problem = schedulingAnalysis->getProblem(forOp);

  auto outerLoop = loopNest.front();
  auto innerLoop = loopNest.back();
  ImplicitLocOpBuilder builder(outerLoop.getLoc(), outerLoop);

  // Create Values for the loop's lower and upper bounds.
  Value lowerBound = lowerAffineLowerBound(innerLoop, builder);
  Value upperBound = lowerAffineUpperBound(innerLoop, builder);
  int64_t stepValue = innerLoop.getStep();
  auto step = builder.create<arith::ConstantOp>(
      IntegerAttr::get(builder.getIndexType(), stepValue));

  // Create the pipeline op, with the same result types as the inner loop. An
  // iter arg is created for the induction variable.
  TypeRange resultTypes = innerLoop.getResultTypes();

  auto ii = builder.getI64IntegerAttr(problem.getInitiationInterval().value());

  SmallVector<Value> iterArgs;
  iterArgs.push_back(lowerBound);
  iterArgs.append(innerLoop.getIterOperands().begin(),
                  innerLoop.getIterOperands().end());

  // If possible, attach a constant trip count attribute. This could be
  // generalized to support non-constant trip counts by supporting an AffineMap.
  Optional<IntegerAttr> tripCountAttr;
  if (auto tripCount = getConstantTripCount(forOp))
    tripCountAttr = builder.getI64IntegerAttr(*tripCount);

  auto pipeline =
      builder.create<PipelineWhileOp>(resultTypes, ii, tripCountAttr, iterArgs);

  // Create the condition, which currently just compares the induction variable
  // to the upper bound.
  Block &condBlock = pipeline.getCondBlock();
  builder.setInsertionPointToStart(&condBlock);
  auto cmpResult = builder.create<arith::CmpIOp>(
      builder.getI1Type(), arith::CmpIPredicate::ult, condBlock.getArgument(0),
      upperBound);
  condBlock.getTerminator()->insertOperands(0, {cmpResult});

  // Add the non-yield operations to their start time groups.
  DenseMap<unsigned, SmallVector<Operation *>> startGroups;
  for (auto *op : problem.getOperations()) {
    if (isa<AffineYieldOp, YieldOp>(op))
      continue;
    auto startTime = problem.getStartTime(op);
    startGroups[*startTime].push_back(op);
  }

  // Maintain mappings of values in the loop body and results of stages,
  // initially populated with the iter args.
  BlockAndValueMapping valueMap;
  for (size_t i = 0; i < iterArgs.size(); ++i)
    valueMap.map(forOp.getBody()->getArgument(i),
                 pipeline.getStagesBlock().getArgument(i));

  // Create the stages.
  Block &stagesBlock = pipeline.getStagesBlock();
  builder.setInsertionPointToStart(&stagesBlock);

  // Iterate in order of the start times.
  SmallVector<unsigned> startTimes;
  for (auto group : startGroups)
    startTimes.push_back(group.first);
  llvm::sort(startTimes);

  DominanceInfo dom(getOperation());
  for (auto startTime : startTimes) {
    auto group = startGroups[startTime];
    OpBuilder::InsertionGuard g(builder);

    // Collect the return types for this stage. Operations whose results are not
    // used within this stage are returned.
    auto isLoopTerminator = [forOp](Operation *op) {
      return isa<AffineYieldOp>(op) && op->getParentOp() == forOp;
    };
    SmallVector<Type> stageTypes;
    DenseSet<Operation *> opsWithReturns;
    for (auto *op : group) {
      for (auto *user : op->getUsers()) {
        if (*problem.getStartTime(user) > startTime || isLoopTerminator(user)) {
          opsWithReturns.insert(op);
          stageTypes.append(op->getResultTypes().begin(),
                            op->getResultTypes().end());
          break;
        }
      }
    }

    // Add the induction variable increment in the first stage.
    if (startTime == 0)
      stageTypes.push_back(lowerBound.getType());

    // Create the stage itself.
    auto startTimeAttr = builder.getIntegerAttr(
        builder.getIntegerType(64, /*isSigned=*/true), startTime);
    auto stage =
        builder.create<PipelineWhileStageOp>(stageTypes, startTimeAttr);
    auto &stageBlock = stage.getBodyBlock();
    auto *stageTerminator = stageBlock.getTerminator();
    builder.setInsertionPointToStart(&stageBlock);

    // Sort the group according to original dominance.
    //    llvm::sort(group,
    //               [&](Operation *a, Operation *b) { return dom.dominates(a,
    //               b); });

    // Move over the operations and add their results to the terminator.
    SmallVector<std::tuple<Operation *, Operation *, unsigned>> movedOps;
    for (auto *op : group) {
      unsigned resultIndex = stageTerminator->getNumOperands();
      auto *newOp = builder.clone(*op, valueMap);
      if (opsWithReturns.contains(op)) {
        stageTerminator->insertOperands(resultIndex, newOp->getResults());
        movedOps.emplace_back(op, newOp, resultIndex);
      }
    }

    // Add the stage results to the value map for the original op.
    for (auto tuple : movedOps) {
      Operation *op = std::get<0>(tuple);
      Operation *newOp = std::get<1>(tuple);
      unsigned resultIndex = std::get<2>(tuple);
      for (size_t i = 0; i < newOp->getNumResults(); ++i) {
        auto newValue = stage->getResult(resultIndex + i);
        auto oldValue = op->getResult(i);
        valueMap.map(oldValue, newValue);
      }
    }

    // Add the induction variable increment to the first stage.
    if (startTime == 0) {
      auto incResult =
          builder.create<arith::AddIOp>(stagesBlock.getArgument(0), step);
      stageTerminator->insertOperands(stageTerminator->getNumOperands(),
                                      incResult->getResults());
    }
  }

  // Add the iter args and results to the terminator.
  auto stagesTerminator =
      cast<PipelineTerminatorOp>(stagesBlock.getTerminator());

  // Collect iter args and results from the induction variable increment and any
  // mapped values that were originally yielded.
  SmallVector<Value> termIterArgs;
  SmallVector<Value> termResults;
  termIterArgs.push_back(
      stagesBlock.front().getResult(stagesBlock.front().getNumResults() - 1));
  for (auto value : forOp.getBody()->getTerminator()->getOperands()) {
    termIterArgs.push_back(valueMap.lookup(value));
    termResults.push_back(valueMap.lookup(value));
  }

  stagesTerminator.getIterArgsMutable().append(termIterArgs);
  stagesTerminator.getResultsMutable().append(termResults);

  // Replace loop results with pipeline results.
  for (size_t i = 0; i < forOp.getNumResults(); ++i)
    forOp.getResult(i).replaceAllUsesWith(pipeline.getResult(i));

  // Remove the loop nest from the IR.
  loopNest.front().walk([](Operation *op) {
    op->dropAllUses();
    op->dropAllDefinedValueUses();
    op->dropAllReferences();
    op->erase();
  });

  return success();
}

std::unique_ptr<mlir::Pass> circt::createAffineToPipeline() {
  return std::make_unique<AffineToPipeline>();
}
