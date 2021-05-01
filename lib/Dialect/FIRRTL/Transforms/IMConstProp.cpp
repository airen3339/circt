//===- IMConstProp.cpp - Intermodule ConstProp and DCE ----------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "./PassDetails.h"
#include "circt/Dialect/FIRRTL/Passes.h"
#include "llvm/ADT/TinyPtrVector.h"
using namespace circt;
using namespace firrtl;

//===----------------------------------------------------------------------===//
// Pass Infrastructure
//===----------------------------------------------------------------------===//

namespace {
/// This class represents a single lattice value. A lattive value corresponds to
/// the various different states that a value in the SCCP dataflow analysis can
/// take. See 'Kind' below for more details on the different states a value can
/// take.
class LatticeValue {
  enum Kind {
    /// A value with a yet to be determined value. This state may be changed to
    /// anything.
    Unknown,

    /// A value that is known to be a constant. This state may be changed to
    /// overdefined.
    Constant,

    /// A value that cannot statically be determined to be a constant. This
    /// state cannot be changed.
    Overdefined
  };

public:
  /// Initialize a lattice value with "Unknown".
  LatticeValue() : constantAndTag(nullptr, Kind::Unknown) {}
  /// Initialize a lattice value with a constant.
  LatticeValue(Attribute attr) : constantAndTag(attr, Kind::Constant) {}

  static LatticeValue getOverdefined() {
    LatticeValue result;
    result.markOverdefined();
    return result;
  }

  bool isUnknown() const { return constantAndTag.getInt() == Kind::Unknown; }
  bool isConstant() const { return constantAndTag.getInt() == Kind::Constant; }
  bool isOverdefined() const {
    return constantAndTag.getInt() == Kind::Overdefined;
  }

  /// Mark the lattice value as overdefined.
  void markOverdefined() {
    constantAndTag.setPointerAndInt(nullptr, Kind::Overdefined);
  }

  /// Mark the lattice value as constant.
  void markConstant(Attribute value) {
    constantAndTag.setPointerAndInt(value, Kind::Constant);
  }

  /// If this lattice is constant, return the constant. Returns nullptr
  /// otherwise.
  Attribute getConstant() const { return constantAndTag.getPointer(); }

  /// Merge in the value of the 'rhs' lattice into this one. Returns true if the
  /// lattice value changed.
  bool meet(LatticeValue rhs) {
    // If we are already overdefined, or rhs is unknown, there is nothing to do.
    if (isOverdefined() || rhs.isUnknown())
      return false;
    // If we are unknown, just take the value of rhs.
    if (isUnknown()) {
      constantAndTag = rhs.constantAndTag;
      return true;
    }

    // Otherwise, if this value doesn't match rhs go straight to overdefined.
    if (constantAndTag != rhs.constantAndTag) {
      markOverdefined();
      return true;
    }
    return false;
  }

private:
  /// The attribute value if this is a constant and the tag for the element
  /// kind.
  llvm::PointerIntPair<Attribute, 2, Kind> constantAndTag;
};
} // end anonymous namespace

namespace {
struct IMConstPropPass : public IMConstPropBase<IMConstPropPass> {
  void runOnOperation() override;
  void rewriteModuleBody(FModuleOp module);

  /// Returns true if the given block is executable.
  bool isBlockExecutable(Block *block) const {
    return executableBlocks.count(block);
  }

  bool isOverdefined(Value value) const {
    auto it = latticeValues.find(value);
    return it != latticeValues.end() && it->second.isOverdefined();
  }

  /// Mark the given value as overdefined. This means that we cannot refine a
  /// specific constant for this value.
  void markOverdefined(Value value) {
    auto &entry = latticeValues[value];
    if (!entry.isOverdefined()) {
      entry.markOverdefined();
      changedLatticeValueWorklist.push_back(value);
    }
  }

  /// Merge information from the 'from' lattice value into value.  If it
  /// changes, then users of the value are added to the worklist for
  /// revisitation.
  void mergeLatticeValue(Value value, LatticeValue &valueEntry,
                         LatticeValue source) {
    if (valueEntry.meet(source))
      changedLatticeValueWorklist.push_back(value);
  }
  void mergeLatticeValue(Value value, LatticeValue source) {
    // Don't even do a map lookup if from has no info in it.
    if (source.isUnknown())
      return;
    mergeLatticeValue(value, latticeValues[value], source);
  }
  void mergeLatticeValue(Value result, Value from) {
    // If 'from' hasn't been computed yet, then it is unknown, don't do
    // anything.
    auto it = latticeValues.find(from);
    if (it == latticeValues.end())
      return;
    mergeLatticeValue(result, it->second);
  }

  /// Mark the given block as executable.
  void markBlockExecutable(Block *block);
  void markWire(WireOp wire);
  void markConstant(ConstantOp constant);
  void markInstance(InstanceOp instance);

  void visitConnect(ConnectOp connect);
  void visitPartialConnect(PartialConnectOp connect);
  void visitOperation(Operation *op);

private:
  /// This keeps track of the current state of each tracked value.
  DenseMap<Value, LatticeValue> latticeValues;

  /// The set of blocks that are known to execute, or are intrinsically live.
  SmallPtrSet<Block *, 16> executableBlocks;

  /// A worklist containing blocks that need to be processed.
  SmallVector<Block *, 64> blockWorklist;

  /// A worklist of values whose LatticeValue recently changed, indicating the
  /// users need to be reprocessed.
  SmallVector<Value, 64> changedLatticeValueWorklist;

  /// This keeps track of users the instance results that correspond to output
  /// ports.
  DenseMap<BlockArgument, llvm::TinyPtrVector<Value>>
      resultPortToInstanceResultMapping;
};
} // end anonymous namespace

// TODO: handle annotations: [[OptimizableExtModuleAnnotation]],
//  [[DontTouchAnnotation]]
void IMConstPropPass::runOnOperation() {
  auto circuit = getOperation();

  // If the top level module is an external module, mark the input ports
  // overdefined.
  if (auto module = dyn_cast<FModuleOp>(circuit.getMainModule())) {
    markBlockExecutable(module.getBodyBlock());
    for (auto port : module.getBodyBlock()->getArguments())
      markOverdefined(port);
  } else {
    // Otherwise, mark all module ports as being overdefined.
    for (auto &circuitBodyOp : circuit.getBody()->getOperations()) {
      if (auto module = dyn_cast<FModuleOp>(circuitBodyOp)) {
        markBlockExecutable(module.getBodyBlock());
        for (auto port : module.getBodyBlock()->getArguments())
          markOverdefined(port);
      }
    }
  }

  // If a value changed lattice state then reprocess any of its users.
  while (!changedLatticeValueWorklist.empty()) {
    Value changedVal = changedLatticeValueWorklist.pop_back_val();
    for (Operation *user : changedVal.getUsers()) {
      if (isBlockExecutable(user->getBlock()))
        visitOperation(user);
    }
  }

  // Rewrite any constants in the modules.
  // TODO: parallelize.
  for (auto &circuitBodyOp : *circuit.getBody())
    if (auto module = dyn_cast<FModuleOp>(circuitBodyOp))
      rewriteModuleBody(module);

  // Clean up our state for next time.
  latticeValues.clear();
  executableBlocks.clear();
  resultPortToInstanceResultMapping.clear();
}

/// Mark a block executable if it isn't already.  This does an initial scan of
/// the block, processing nullary operations like wires, instances, and
/// constants that only get processed once.
void IMConstPropPass::markBlockExecutable(Block *block) {
  if (!executableBlocks.insert(block).second)
    return; // Already executable.

  for (auto &op : *block) {
    // We only handle nullary firrtl nodes in the prepass.  Other nodes will get
    // handled as part of top-down worklist processing.
    if (op.getNumOperands() != 0)
      continue;

    // Handle each of the nullary operations in the firrtl dialect.
    if (auto wire = dyn_cast<WireOp>(op))
      markWire(wire);
    else if (auto constant = dyn_cast<ConstantOp>(op))
      markConstant(constant);
    else if (auto instance = dyn_cast<InstanceOp>(op))
      markInstance(instance);
    else {
      // TODO: Mems, instances, etc.
      for (auto result : op.getResults())
        markOverdefined(result);
    }
  }
}

void IMConstPropPass::markWire(WireOp wire) {
  // If the wire has a non-ground type, then it is too complex for us to handle,
  // mark the wire as overdefined.
  // TODO: Eventually add a field-sensitive model.
  if (!wire.getType().getPassiveType().isGround())
    return markOverdefined(wire);

  // Otherwise, we leave this value undefined and allow connects to change its
  // state.
}

void IMConstPropPass::markConstant(ConstantOp constant) {
  mergeLatticeValue(constant, LatticeValue(constant.valueAttr()));
}

/// Instances have no operands, so they are visited exactly once when their
/// enclosing block is marked live.  This sets up the def-use edges for ports.
void IMConstPropPass::markInstance(InstanceOp instance) {
  // Get the module being reference or a null pointer if this is an extmodule.
  auto module = dyn_cast<FModuleOp>(instance.getReferencedModule());

  // If this is an extmodule, just remember that any results and inouts are
  // overdefined.
  if (!module) {
    for (size_t resultNo = 0, e = instance.getNumResults(); resultNo != e;
         ++resultNo) {
      auto portVal = instance.getResult(resultNo);
      // If this is a flip value, then this is an input to the extmodule which
      // we can ignore.
      if (portVal.getType().isa<FlipType>())
        continue;

      // Otherwise this is a result from it or an inout, mark it as overdefined.
      markOverdefined(portVal);
    }
    return;
  }

  markBlockExecutable(module.getBodyBlock());

  // Ok, it is a normal internal module reference.  Populate
  // resultPortToInstanceResultMapping, and forward any already-computed values.
  for (size_t resultNo = 0, e = instance.getNumResults(); resultNo != e;
       ++resultNo) {
    auto instancePortVal = instance.getResult(resultNo);
    // If this is a flip value then this is an input to the instance, which will
    // get handled when any connects to it are processed.
    if (instancePortVal.getType().isa<FlipType>())
      continue;
    // We only support simple values so far.
    if (!instancePortVal.getType().cast<FIRRTLType>().isGround()) {
      // TODO: Add field sensitivity.
      markOverdefined(instancePortVal);
      continue;
    }

    // Otherwise we have a result from the instance.  We need to forward results
    // from the body to this instance result's SSA value, so remember it.
    BlockArgument modulePortVal = module.getPortArgument(resultNo);
    resultPortToInstanceResultMapping[modulePortVal].push_back(instancePortVal);

    // If there is already a value known for modulePortVal make sure to forward
    // it here.
    mergeLatticeValue(instancePortVal, modulePortVal);
  }
}

// We merge the value from the RHS into the value of the LHS.
void IMConstPropPass::visitConnect(ConnectOp connect) {
  // TODO: Generalize to subaccesses etc when we have a field sensitive model.
  if (!connect.dest().getType().cast<FIRRTLType>().getPassiveType().isGround())
    return;

  // FIXME: Handle implicit extensions etc.

  // Driving result ports propagates the value to each instance using the
  // module.
  if (auto blockArg = connect.dest().dyn_cast<BlockArgument>()) {
    for (auto userOfResultPort : resultPortToInstanceResultMapping[blockArg])
      mergeLatticeValue(userOfResultPort, connect.src());
    return;
  }

  auto dest = connect.dest().cast<mlir::OpResult>();

  // For wires, we just drive the value of the wire itself, which automatically
  // propagates to users.
  if (isa<WireOp>(dest.getOwner()))
    return mergeLatticeValue(connect.dest(), connect.src());

  // Driving an instance argument port drives the corresponding argument of the
  // referenced module.
  if (auto instance = dyn_cast<InstanceOp>(dest.getOwner())) {
    auto module = dyn_cast<FModuleOp>(instance.getReferencedModule());
    if (!module)
      return;

    BlockArgument modulePortVal =
        module.getPortArgument(dest.getResultNumber());
    return mergeLatticeValue(modulePortVal, connect.src());
  }

  connect.emitError("connect unhandled by IMConstProp");
}

void IMConstPropPass::visitPartialConnect(PartialConnectOp partialConnect) {
  partialConnect.emitError("IMConstProp cannot handle partial connect");
}

/// This method is invoked when an operand of the specified op changes its
/// lattice value state and when the block containing the operation is first
/// noticed as being alive.
///
/// This should update the lattice value state for any result values.
///
void IMConstPropPass::visitOperation(Operation *op) {
  // If this is a operation with special handling, handle it specially.
  if (auto connectOp = dyn_cast<ConnectOp>(op))
    return visitConnect(connectOp);
  if (auto partialConnectOp = dyn_cast<PartialConnectOp>(op))
    return visitPartialConnect(partialConnectOp);
  // TODO: Handle 'when' operations.

  // If this op produces no results, it can't produce any constants.
  if (op->getNumResults() == 0)
    return;

  // Collect all of the constant operands feeding into this operation. If any
  // are not ready to be resolved, bail out and wait for them to resolve.
  SmallVector<Attribute, 8> operandConstants;
  operandConstants.reserve(op->getNumOperands());
  for (Value operand : op->getOperands()) {
    // Make sure all of the operands are resolved first.
    auto &operandLattice = latticeValues[operand];
    if (operandLattice.isUnknown())
      return;
    operandConstants.push_back(operandLattice.getConstant());
  }

  // If all of the results of this operation are already overdefined, bail out
  // early.
  auto isOverdefinedFn = [&](Value value) { return isOverdefined(value); };
  if (llvm::all_of(op->getResults(), isOverdefinedFn))
    return;

  // Save the original operands and attributes just in case the operation folds
  // in-place. The constant passed in may not correspond to the real runtime
  // value, so in-place updates are not allowed.
  SmallVector<Value, 8> originalOperands(op->getOperands());
  DictionaryAttr originalAttrs = op->getAttrDictionary();

  // Simulate the result of folding this operation to a constant. If folding
  // fails or was an in-place fold, mark the results as overdefined.
  SmallVector<OpFoldResult, 8> foldResults;
  foldResults.reserve(op->getNumResults());
  if (failed(op->fold(operandConstants, foldResults))) {
    for (auto value : op->getResults())
      markOverdefined(value);
    return;
  }

  // If the folding was in-place, mark the results as overdefined and reset the
  // operation. We don't allow in-place folds as the desire here is for
  // simulated execution, and not general folding.
  if (foldResults.empty()) {
    op->setOperands(originalOperands);
    op->setAttrs(originalAttrs);
    for (auto value : op->getResults())
      markOverdefined(value);
    return;
  }

  // Merge the fold results into the lattice for this operation.
  assert(foldResults.size() == op->getNumResults() && "invalid result size");
  for (unsigned i = 0, e = foldResults.size(); i != e; ++i) {
    // Merge in the result of the fold, either a constant or a value.
    LatticeValue resultLattice;
    OpFoldResult foldResult = foldResults[i];
    if (Attribute foldAttr = foldResult.dyn_cast<Attribute>())
      resultLattice = LatticeValue(foldAttr);
    else // Folding to an operand results in its value.
      resultLattice = latticeValues[foldResult.get<Value>()];
    mergeLatticeValue(op->getResult(i), resultLattice);
  }
}

void IMConstPropPass::rewriteModuleBody(FModuleOp module) {
  auto *body = module.getBodyBlock();
  // If a module is unreachable, then nuke its body.
  if (!executableBlocks.count(body)) {
    while (!body->empty())
      body->back().erase();
    return;
  }

  auto builder = OpBuilder::atBlockBegin(body);

  auto replaceValueWithConstant = [&](Value value, Attribute constantValue) {
    // FIXME: Unique constants into the entry block of the module.
    auto *cst = module->getDialect()->materializeConstant(
        builder, constantValue, value.getType(), value.getLoc());
    if (!cst)
      return;
    value.replaceAllUsesWith(cst->getResult(0));
  };

  auto getAttributeIfConstant = [&](Value value) -> Attribute {
    auto it = latticeValues.find(value);
    if (it != latticeValues.end() && it->second.isConstant())
      return it->second.getConstant();
    return {};
  };

  // Constant propagate any ports that are always constant.
  for (auto &port : body->getArguments()) {
    if (auto attr = getAttributeIfConstant(port))
      replaceValueWithConstant(port, attr);
  }

  // TODO: Walk 'when's preorder with `walk`.
  for (auto &op : llvm::make_early_inc_range(*body)) {
    // Connects to values that we found to be constant can be dropped.  These
    // will already have been replaced since we're walking top-down.
    if (auto connect = dyn_cast<ConnectOp>(op)) {
      if (connect.dest().getDefiningOp<ConstantOp>()) {
        connect.erase();
        continue;
      }
    }

    // Other ops with no results don't need processing.
    if (op.getNumResults() == 0)
      continue;

    // Don't "refold" constants.  TODO: Unique in the module entry block.
    if (isa<ConstantOp>(op))
      continue;

    // If the op had any constants folded, replace them.

    for (auto result : op.getResults()) {
      if (auto attr = getAttributeIfConstant(result)) {
        builder.setInsertionPoint(&op);
        replaceValueWithConstant(result, attr);
      }
    }
    if (op.use_empty() && (wouldOpBeTriviallyDead(&op) || isa<WireOp>(op))) {
      op.erase();
      continue;
    }
  }
}

std::unique_ptr<mlir::Pass> circt::firrtl::createIMConstPropPass() {
  return std::make_unique<IMConstPropPass>();
}
