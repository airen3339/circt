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
#include "mlir/Dialect/Arith/IR/Arith.h"
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
#include <cassert>

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
  LogicalResult populateOperatorTypes(SmallVectorImpl<AffineForOp> &loopNest,
                                      ModuloProblem &problem);
  LogicalResult solveSchedulingProblem(SmallVectorImpl<AffineForOp> &loopNest,
                                       ModuloProblem &problem);
  LogicalResult createPipelinePipeline(SmallVectorImpl<AffineForOp> &loopNest,
                                       ModuloProblem &problem);

  CyclicSchedulingAnalysis *schedulingAnalysis;
};

} // namespace

void AffineToPipeline::runOnOperation() {
  // Get dependence analysis for the whole function.
  auto dependenceAnalysis = getAnalysis<MemoryDependenceAnalysis>();

  // After dependence analysis, materialize affine structures.
  if (failed(lowerAffineStructures(dependenceAnalysis)))
    return signalPassFailure();

  // Get scheduling analysis for the whole function.
  schedulingAnalysis = &getAnalysis<CyclicSchedulingAnalysis>();

  // Collect perfectly nested loops and work on them.
  auto outerLoops = getOperation().getOps<AffineForOp>();
  for (auto root : llvm::make_early_inc_range(outerLoops)) {
    SmallVector<AffineForOp> nestedLoops;
    getPerfectlyNestedLoops(nestedLoops, root);

    // Restrict to single loops to simplify things for now.
    if (nestedLoops.size() != 1)
      continue;

    ModuloProblem moduloProblem =
        ModuloProblem::get(schedulingAnalysis->getProblem(nestedLoops.back()));

    // Populate the target operator types.
    if (failed(populateOperatorTypes(nestedLoops, moduloProblem)))
      return signalPassFailure();

    // Solve the scheduling problem computed by the analysis.
    if (failed(solveSchedulingProblem(nestedLoops, moduloProblem)))
      return signalPassFailure();

    // Convert the IR.
    if (failed(createPipelinePipeline(nestedLoops, moduloProblem)))
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
  target.addLegalDialect<AffineDialect, ArithDialect, MemRefDialect,
                         SCFDialect>();
  target.addIllegalOp<AffineIfOp, AffineLoadOp, AffineStoreOp>();
  target.addDynamicallyLegalOp<IfOp>(ifOpLegalityCallback);
  target.addDynamicallyLegalOp<AffineYieldOp>(yieldOpLegalityCallback);

  RewritePatternSet patterns(context);
  populateAffineToStdConversionPatterns(patterns);
  patterns.add<AffineLoadLowering>(context, dependenceAnalysis);
  patterns.add<AffineStoreLowering>(context, dependenceAnalysis);
  patterns.add<IfOpHoisting>(context);

  if (failed(applyPartialConversion(op, target, std::move(patterns))))
    return failure();

  return success();
}

/// Populate the schedling problem operator types for the dialect we are
/// targetting. Right now, we assume Calyx, which has a standard library with
/// well-defined operator latencies. Ultimately, we should move this to a
/// dialect interface in the Scheduling dialect.
LogicalResult
AffineToPipeline::populateOperatorTypes(SmallVectorImpl<AffineForOp> &loopNest,
                                        ModuloProblem &problem) {
  // Scheduling analyis only considers the innermost loop nest for now.
  auto forOp = loopNest.back();

  // Load the Calyx operator library into the problem. This is a very minimal
  // set of arithmetic and memory operators for now. This should ultimately be
  // pulled out into some sort of dialect interface.
  Problem::OperatorType combOpr = problem.getOrInsertOperatorType("comb");
  problem.setLatency(combOpr, 0);
  Problem::OperatorType seqOpr = problem.getOrInsertOperatorType("seq");
  problem.setLatency(seqOpr, 1);
  Problem::OperatorType mcOpr = problem.getOrInsertOperatorType("multicycle");
  problem.setLatency(mcOpr, 3);

  SmallDenseMap<TypedValue<MemRefType> *, std::pair<unsigned, unsigned>> memOps;
  Operation *unsupported;
  WalkResult result = forOp.getBody()->walk([&](Operation *op) {
    return TypeSwitch<Operation *, WalkResult>(op)
        .Case<AddIOp, IfOp, AffineYieldOp, arith::ConstantOp, CmpIOp,
              IndexCastOp, memref::AllocaOp, YieldOp>([&](Operation *combOp) {
          // Some known combinational ops.
          problem.setLinkedOperatorType(combOp, combOpr);
          return WalkResult::advance();
        })
        .Case<AddIOp, CmpIOp>([&](Operation *seqOp) {
          // These ops need to be sequential for now because we do not
          // have enough information to chain them together yet.
          problem.setLinkedOperatorType(seqOp, seqOpr);
          return WalkResult::advance();
        })
        .Case<AffineStoreOp, memref::StoreOp>([&](Operation *memOp) {
          // Some known sequential ops. In certain cases, reads may be
          // combinational in Calyx, but taking advantage of that is left as
          // a future enhancement.
          TypedValue<MemRefType> memRef =
              isa<AffineStoreOp>(*memOp)
                  ? cast<AffineStoreOp>(*memOp).getMemRef()
                  : cast<memref::StoreOp>(*memOp).getMemRef();
          memOps[&memRef] =
              std::pair(memOps[&memRef].first, memOps[&memRef].second + 1);
          Problem::OperatorType memOpr = problem.getOrInsertOperatorType(
              "mem_" + std::to_string(hash_value(memRef)));
          problem.setLatency(memOpr, 1);
          problem.setLimit(memOpr, 1);
          problem.setLinkedOperatorType(memOp, memOpr);
          return WalkResult::advance();
        })
        .Case<AffineLoadOp, memref::LoadOp>([&](Operation *memOp) {
          // Some known sequential ops. In certain cases, reads may be
          // combinational in Calyx, but taking advantage of that is left as
          // a future enhancement.
          TypedValue<MemRefType> memRef =
              isa<AffineLoadOp>(*memOp)
                  ? cast<AffineLoadOp>(*memOp).getMemRef()
                  : cast<memref::LoadOp>(*memOp).getMemRef();
          memOps[&memRef] =
              std::pair(memOps[&memRef].first + 1, memOps[&memRef].second);
          Problem::OperatorType memOpr = problem.getOrInsertOperatorType(
              "mem_" + std::to_string(hash_value(memRef)));
          problem.setLatency(memOpr, 1);
          problem.setLimit(memOpr, 1);
          problem.setLinkedOperatorType(memOp, memOpr);
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
LogicalResult
AffineToPipeline::solveSchedulingProblem(SmallVectorImpl<AffineForOp> &loopNest,
                                         ModuloProblem &problem) {
  // Scheduling analyis only considers the innermost loop nest for now.
  auto forOp = loopNest.back();

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

/// Create the pipeline op for a loop nest.
LogicalResult
AffineToPipeline::createPipelinePipeline(SmallVectorImpl<AffineForOp> &loopNest,
                                         ModuloProblem &problem) {
  // Scheduling analyis only considers the innermost loop nest for now.
  auto forOp = loopNest.back();

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
  BlockAndValueMapping iterValueMap;
  for (size_t i = 0; i < forOp.getBody()->getNumArguments(); ++i)
    iterValueMap.map(forOp.getBody()->getArgument(i),
                     pipeline.getStagesBlock().getArgument(i));

  // Create the stages.
  Block &stagesBlock = pipeline.getStagesBlock();
  builder.setInsertionPointToStart(&stagesBlock);

  // Iterate in order of the start times.
  SmallVector<unsigned> startTimes;
  for (const auto &group : startGroups)
    startTimes.push_back(group.first);
  llvm::sort(startTimes);

  DominanceInfo dom(getOperation());
  SmallVector<DenseSet<Value>> registerValues;
  SmallVector<SmallVector<mlir::Type>> registerTypes;
  SmallVector<BlockAndValueMapping> valueMaps;
  unsigned pipelineDepth = 0;
  for (auto startTime : startTimes) {
    auto group = startGroups[startTime];
    // OpBuilder::InsertionGuard g(builder);

    // Collect the return types for this stage. Operations whose results are not
    // used within this stage are returned.
    auto isLoopTerminator = [forOp](Operation *op) {
      return isa<AffineYieldOp>(op) && op->getParentOp() == forOp;
    };
    registerValues.push_back(DenseSet<Value>());

    for (auto *op : group) {
      if (op->getUsers().empty())
        continue;
      unsigned finTime =
          startTime + *problem.getLatency(*problem.getLinkedOperatorType(op));
      for (auto *user : op->getUsers()) {
        if (*problem.getStartTime(user) > startTime || isLoopTerminator(user))
          finTime = std::max(finTime, *problem.getStartTime(user));
      }

      pipelineDepth = std::max(finTime, pipelineDepth);
      unsigned opLatency =
          *problem.getLatency(*problem.getLinkedOperatorType(op));
      for (unsigned i = opLatency > 0 ? startTime + opLatency - 1 : startTime;
           i < finTime; i++) {
        if (registerValues.size() <= i)
          registerValues.push_back(DenseSet<Value>());

        for (auto result : op->getResults())
          registerValues.data()[i].insert(result);
      }
    }
  }

  for (auto iterArg : innerLoop.getLoopBody().getArguments()) {
    unsigned iterArgPipeLen = 0;
    for (auto *user : iterArg.getUsers())
      iterArgPipeLen = std::max(iterArgPipeLen, *problem.getStartTime(user));

    for (unsigned i = 0; i < iterArgPipeLen; i++)
      registerValues.data()[i].insert(iterArg);
  }

  // Now make register Types and valueMaps
  for (unsigned i = 0; i < registerValues.size(); i++) {
    SmallVector<mlir::Type> types;
    for (auto val : registerValues.data()[i]) {
      types.push_back(val.getType());
    }
    registerTypes.push_back(types);
    valueMaps.push_back(BlockAndValueMapping(iterValueMap));
  }

  // Create stages along with maps
  for (auto startTime : startTimes) {
    auto group = startGroups[startTime];
    llvm::sort(group,
               [&](Operation *a, Operation *b) { return dom.dominates(a, b); });
    auto stageTypes = registerTypes.data()[startTime];
    // Add the induction variable increment in the first stage.
    if (startTime == 0)
      stageTypes.push_back(lowerBound.getType());

    // Create the stage itself.
    builder.setInsertionPoint(stagesBlock.getTerminator());
    auto startTimeAttr = builder.getIntegerAttr(
        builder.getIntegerType(64, /*isSigned=*/true), startTime);
    auto stage =
        builder.create<PipelineWhileStageOp>(stageTypes, startTimeAttr);
    auto &stageBlock = stage.getBodyBlock();
    auto *stageTerminator = stageBlock.getTerminator();
    builder.setInsertionPointToStart(&stageBlock);

    for (auto *op : group) {
      auto *newOp = builder.clone(*op, valueMaps.data()[startTime]);

      for (auto result : op->getResults())
        valueMaps.data()[startTime].map(
            result, newOp->getResult(result.getResultNumber()));
    }

    SmallVector<Value> stageOperands;
    for (auto res : registerValues.data()[startTime]) {
      stageOperands.push_back(valueMaps.data()[startTime].lookup(res));
    }
    stageTerminator->insertOperands(stageTerminator->getNumOperands(),
                                    stageOperands);

    // Give the next stage the mappings it needs
    unsigned destTime = startTime + 1;
    unsigned resIndex = 0;
    if (destTime < registerValues.size())
      for (auto res : registerValues.data()[startTime]) {
        valueMaps.data()[destTime].map(res, stage.getResult(resIndex++));
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
    termIterArgs.push_back(iterValueMap.lookup(value));
    termResults.push_back(iterValueMap.lookup(value));
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
