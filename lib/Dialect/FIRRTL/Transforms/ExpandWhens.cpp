//===- ExpandWhens.cpp - Expand WhenOps into muxed operations ---*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the ExpandWhens pass.
//
//===----------------------------------------------------------------------===//

#include "./PassDetails.h"
#include "circt/Dialect/FIRRTL/FIRRTLOps.h"
#include "circt/Dialect/FIRRTL/FIRRTLTypes.h"
#include "circt/Dialect/FIRRTL/FIRRTLVisitors.h"
#include "circt/Dialect/FIRRTL/Passes.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/STLExtras.h"

using namespace circt;
using namespace firrtl;

/// Move all operations from a source block in to a destination block. Leaves
/// the source block empty.
static void mergeBlock(Block &destination, Block::iterator insertPoint,
                       Block &source) {
  destination.getOperations().splice(insertPoint, source.getOperations());
}

namespace {

class ExpandWhensVisitor : public FIRRTLVisitor<ExpandWhensVisitor> {
public:
  ExpandWhensVisitor(llvm::MapVector<Value, Operation *> &scope,
                     Value condition)
      : scope(scope), condition(condition) {}

  /// Run expand whens on the Module.  This will emit an error for each
  /// incomplete initialization found. If an initialiazation error was detected,
  /// this will return failure and leave the IR in an inconsistent state.
  static LogicalResult run(FModuleOp op);

  using FIRRTLVisitor<ExpandWhensVisitor>::visitExpr;
  using FIRRTLVisitor<ExpandWhensVisitor>::visitDecl;
  using FIRRTLVisitor<ExpandWhensVisitor>::visitStmt;

  void visitDecl(FModuleOp op);
  void visitDecl(InstanceOp op);
  void visitDecl(MemOp op);
  void visitDecl(RegOp op);
  void visitDecl(RegResetOp op);
  void visitDecl(WireOp op);
  void visitInvalidOp(Operation *op) {}
  void visitStmt(AssertOp op);
  void visitStmt(AssumeOp op);
  void visitStmt(ConnectOp op);
  void visitStmt(CoverOp op);
  void visitStmt(ModuleOp op);
  void visitStmt(PartialConnectOp op);
  void visitStmt(PrintFOp op);
  void visitStmt(StopOp op);
  void visitStmt(WhenOp op);
  void visitUnhandledOp(Operation *op) {}

private:
  /// Process a block, recording each declaration, and expanding all whens.
  void process(Block &block);

  /// Records a connection to a destination. This will delete a previous
  /// connection to a destination if there was one.
  void setLastConnect(Value dest, Operation *connection) {
    // Try to insert, if it doesn't insert, replace the previous value.
    auto itAndInserted = scope.insert({dest, connection});
    if (!std::get<1>(itAndInserted)) {
      auto iterator = std::get<0>(itAndInserted);
      // Delete the old connection if it exists. Null connections are inserted
      // on declarations.
      if (auto oldConnect = iterator->second)
        oldConnect->erase();
      iterator->second = connection;
    }
  }

  /// Get the source value from a connection. This supports any operation which
  /// is capable of driving a value.
  static Value getConnectedValue(Operation *op) {
    return TypeSwitch<Operation *, Value>(op)
        .Case<ConnectOp>([](auto op) { return op.src(); })
        .Case<PartialConnectOp>([](auto op) { return op.src(); })
        .Default([](Operation *op) {
          llvm_unreachable("unknown operation");
          return nullptr;
        });
  }

  /// And a 1-bit value with the current condition.  If we are in the outer
  /// scope, i.e. not in a WhenOp region, then there is no condition.
  Value andWithCondition(Operation *op, Value value) {
    // If there is no condition, it means we are not inside any WhenOp.
    if (!condition)
      return value;
    // 'and' the value with the current condition.
    return OpBuilder(op).createOrFold<AndPrimOp>(
        condition.getLoc(), condition.getType(), condition, value);
  }

  /// Take two connection operations and merge them in to a new connect under a
  /// condition.  Destination of both connects should be `dest`.
  Operation *flattenConditionalConnections(OpBuilder &b, Location loc,
                                           Value dest, Value cond,
                                           Operation *whenTrueConn,
                                           Operation *whenFalseConn) {
    auto whenTrue = getConnectedValue(whenTrueConn);
    auto whenFalse = getConnectedValue(whenFalseConn);
    auto newValue = b.createOrFold<MuxPrimOp>(loc, whenTrue.getType(), cond,
                                              whenTrue, whenFalse);
    auto newConnect = b.create<ConnectOp>(loc, dest, newValue);
    whenTrueConn->erase();
    whenFalseConn->erase();
    return newConnect;
  }

private:
  /// Map of destinations and the operation which is driving a value to it in
  /// the current scope. This is used for resolving last connect semantics, and
  /// for retrieving the responsible connect operation.
  llvm::MapVector<Value, Operation *> &scope;

  /// The current wrapping condition. If null, we are in the outer scope.
  Value condition;
};
} // namespace

LogicalResult ExpandWhensVisitor::run(FModuleOp module) {
  llvm::MapVector<Value, Operation *> outerScope;
  ExpandWhensVisitor(outerScope, nullptr).visitDecl(module);

  // Check for any incomplete initialization.
  LogicalResult result = success();
  for (auto destAndConnect : outerScope) {
    // Check if there is valid connection to this destination.
    auto connect = std::get<1>(destAndConnect);
    if (connect)
      continue;

    // This pass has failed, and there is an incompletely initialized sink. We
    // have to find the type of the sink and print a useful error message.
    result = failure();
    auto dest = std::get<0>(destAndConnect);
    auto op = dest.getDefiningOp();

    // Module ports.
    if (auto arg = dest.dyn_cast<BlockArgument>()) {
      // Get the module ports and get the name.
      SmallVector<ModulePortInfo> ports = module.getPorts();
      module.emitError("module port ")
          << ports[arg.getArgNumber()].name << " not fully initialized.";
      continue;
    }

    // Instance operation.
    if (auto instance = dyn_cast<InstanceOp>(op)) {
      auto result = dest.cast<OpResult>();
      instance->emitError("instance port ")
          << instance.getPortName(result.getResultNumber())
          << " not fully initialized.";
      continue;
    }

    // Memory operation.
    // TODO: Memories currently are capable of returning bundles. The pass is
    // not capable of tracking individual fields in a bundle, and can only
    // detect connections to the bundle as a whole.  After issue #888 is solved,
    // LowerTypes will transform memories to only return ground types.
    if (auto memory = dyn_cast<MemOp>(op)) {
      result = success();
      continue;
    }

    // Registers and Wires.
    op->emitError("sink not fully initialized.");
  }

  return result;
}

void ExpandWhensVisitor::process(Block &block) {
  for (auto &op : llvm::make_early_inc_range(block)) {
    dispatchVisitor(&op);
  }
}

void ExpandWhensVisitor::visitDecl(FModuleOp op) {
  // Track any results (flipped arguments) of the module for init coverage.
  for (auto arg : op.getArguments()) {
    auto type = arg.getType().cast<FIRRTLType>();
    if (!type.isPassive())
      scope[arg] = nullptr;
  }

  process(*op.getBodyBlock());
}

void ExpandWhensVisitor::visitDecl(WireOp op) { scope[op.result()] = nullptr; }

void ExpandWhensVisitor::visitDecl(RegOp op) { scope[op.result()] = nullptr; }

void ExpandWhensVisitor::visitDecl(RegResetOp op) {
  scope[op.result()] = nullptr;
}

void ExpandWhensVisitor::visitDecl(InstanceOp op) {
  // Track any instance inputs which need to be connected to for init coverage.
  for (auto result : op.results()) {
    auto type = result.getType().cast<FIRRTLType>();
    if (!type.isPassive())
      scope[result] = nullptr;
  }
}

void ExpandWhensVisitor::visitDecl(MemOp op) {
  // Track any memory inputs which require connections.
  for (auto result : op.results()) {
    auto type = result.getType().cast<FIRRTLType>();
    if (!type.isPassive())
      scope[result] = nullptr;
  }
}

void ExpandWhensVisitor::visitStmt(PartialConnectOp op) {
  setLastConnect(op.dest(), op);
}

void ExpandWhensVisitor::visitStmt(ConnectOp op) {
  setLastConnect(op.dest(), op);
}

void ExpandWhensVisitor::visitStmt(PrintFOp op) {
  op.condMutable().assign(andWithCondition(op, op.cond()));
}

void ExpandWhensVisitor::visitStmt(StopOp op) {
  op.condMutable().assign(andWithCondition(op, op.cond()));
}

void ExpandWhensVisitor::visitStmt(AssertOp op) {
  op.enableMutable().assign(andWithCondition(op, op.enable()));
}

void ExpandWhensVisitor::visitStmt(AssumeOp op) {
  op.enableMutable().assign(andWithCondition(op, op.enable()));
}

void ExpandWhensVisitor::visitStmt(CoverOp op) {
  op.enableMutable().assign(andWithCondition(op, op.enable()));
}

void ExpandWhensVisitor::visitStmt(WhenOp whenOp) {
  OpBuilder b(whenOp);
  Block *parentBlock = whenOp->getBlock();

  // Process both sides of the the WhenOp, fixing up all simulation
  // contructs, and resolving last connect semantics in each block. This process
  // returns the set of connects in each side of the when op.

  // Process the `then` block.
  llvm::MapVector<Value, Operation *> thenScope;
  auto thenCondition = andWithCondition(whenOp, whenOp.condition());
  auto &thenBlock = whenOp.getThenBlock();
  ExpandWhensVisitor(thenScope, thenCondition).process(thenBlock);
  mergeBlock(*parentBlock, Block::iterator(whenOp), thenBlock);

  // Process the `else` block.
  llvm::MapVector<Value, Operation *> elseScope;
  if (whenOp.hasElseRegion()) {
    auto condition = whenOp.condition();
    auto notOp = b.createOrFold<NotPrimOp>(whenOp.getLoc(), condition.getType(),
                                           condition);
    Value elseCondition = andWithCondition(whenOp, notOp);
    auto &elseBlock = whenOp.getElseBlock();
    ExpandWhensVisitor(elseScope, elseCondition).process(elseBlock);
    mergeBlock(*parentBlock, Block::iterator(whenOp), elseBlock);
  }

  // Combine the connect statements from each side of the block. There are 5
  // cases to consider. If all are set, last connect semantics dictate that it
  // is actually the third case.
  //
  // Prev | Then | Else | Outcome
  // -----|------|------|-------
  //      |  set |      | then
  //      |      |  set | else
  //      |  set |  set | mux(p, then, else)
  //  set |  set |      | mux(p, then, prev)
  //  set |      |  set | mux(p, prev, else)
  //
  // If the value was declared in the block, then it does not need to have been
  // assigned a previous value.  If the value was declared before the block,
  // then there is an incomplete initialization error.

  // Process all connects in the `then` block.
  for (auto &destAndConnect : thenScope) {
    auto dest = std::get<0>(destAndConnect);
    auto thenConnect = std::get<1>(destAndConnect);

    // `dest` is set in `then` only.
    auto itAndInserted = scope.insert({dest, thenConnect});
    if (std::get<1>(itAndInserted))
      continue;
    auto outerIt = std::get<0>(itAndInserted);

    // `dest` is set in `then` and `else`.
    auto elseIt = elseScope.find(dest);
    if (elseIt != elseScope.end()) {
      auto &elseConnect = std::get<1>(*elseIt);
      // Create a new connect with `mux(p, then, else)`.
      OpBuilder connectBuilder(elseConnect);
      auto newConnect = flattenConditionalConnections(
          connectBuilder, elseConnect->getLoc(), dest, thenCondition,
          thenConnect, elseConnect);
      setLastConnect(dest, newConnect);
      // Do not process connect in the else scope.
      elseScope.erase(dest);
      continue;
    }

    // `dest` is null in the outer scope.
    auto &outerConnect = std::get<1>(*outerIt);
    if (!outerConnect) {
      thenConnect->erase();
      continue;
    }

    // `dest` is set in the outer scope.
    // Create a new connect with mux(p, then, outer)
    OpBuilder connectBuilder(thenConnect);
    auto newConnect = flattenConditionalConnections(
        connectBuilder, thenConnect->getLoc(), dest, thenCondition, thenConnect,
        outerConnect);
    outerIt->second = newConnect;
  }

  // Process all connects in the `else` block.
  for (auto &destAndConnect : elseScope) {
    auto dest = std::get<0>(destAndConnect);
    auto elseConnect = std::get<1>(destAndConnect);

    // `dest` is set in `then` only.
    auto itAndInserted = scope.insert({dest, elseConnect});
    if (std::get<1>(itAndInserted))
      continue;

    // `dest` is null in the outer scope.
    auto outerIt = std::get<0>(itAndInserted);
    auto &outerConnect = std::get<1>(*outerIt);
    if (!outerConnect) {
      elseConnect->erase();
      continue;
    }

    // `dest` is set in the outer scope.
    // Create a new connect with mux(p, outer, else).
    OpBuilder connectBuilder(elseConnect);
    auto newConnect = flattenConditionalConnections(
        connectBuilder, elseConnect->getLoc(), dest, thenCondition,
        outerConnect, elseConnect);
    outerIt->second = newConnect;
  }

  // Delete the now empty WhenOp.
  whenOp.erase();
}

//===----------------------------------------------------------------------===//
// Pass Infrastructure
//===----------------------------------------------------------------------===//

class ExpandWhensPass : public ExpandWhensBase<ExpandWhensPass> {
  void runOnOperation() override;
};

void ExpandWhensPass::runOnOperation() {
  if (failed(ExpandWhensVisitor::run(getOperation())))
    signalPassFailure();
}

std::unique_ptr<mlir::Pass> circt::firrtl::createExpandWhensPass() {
  return std::make_unique<ExpandWhensPass>();
}
