//===- CalyxLoweringUtils.cpp - Calyx lowering utility methods --*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Various lowering utility methods converting to and from Calyx programs.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/Calyx/CalyxLoweringUtils.h"
#include "circt/Dialect/Calyx/CalyxHelpers.h"
#include "circt/Dialect/Calyx/CalyxOps.h"
#include "circt/Support/LLVM.h"
#include "mlir/Dialect/ControlFlow/IR/ControlFlowOps.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/IR/Matchers.h"

#include <variant>

using namespace llvm;
using namespace mlir;
using namespace mlir::arith;

namespace circt {
namespace calyx {

void appendPortsForExternalMemref(PatternRewriter &rewriter, StringRef memName,
                                  Value memref, unsigned memoryID,
                                  SmallVectorImpl<calyx::PortInfo> &inPorts,
                                  SmallVectorImpl<calyx::PortInfo> &outPorts) {
  MemRefType memrefType = memref.getType().cast<MemRefType>();

  // Ports constituting a memory interface are added a set of attributes under
  // a "mem : {...}" dictionary. These attributes allows for deducing which
  // top-level I/O signals constitutes a unique memory interface.
  auto getMemoryInterfaceAttr = [&](StringRef tag,
                                    Optional<unsigned> addrIdx = {}) {
    auto attrs = SmallVector<NamedAttribute>{
        // "id" denotes a unique memory interface.
        rewriter.getNamedAttr("id", rewriter.getI32IntegerAttr(memoryID)),
        // "tag" denotes the function of this signal.
        rewriter.getNamedAttr("tag", rewriter.getStringAttr(tag))};
    if (addrIdx.hasValue())
      // "addr_idx" denotes the address index of this signal, for
      // multi-dimensional memory interfaces.
      attrs.push_back(rewriter.getNamedAttr(
          "addr_idx", rewriter.getI32IntegerAttr(addrIdx.getValue())));

    return rewriter.getNamedAttr("mem", rewriter.getDictionaryAttr(attrs));
  };

  // Read data
  inPorts.push_back(calyx::PortInfo{
      rewriter.getStringAttr(memName + "_read_data"),
      memrefType.getElementType(), calyx::Direction::Input,
      DictionaryAttr::get(rewriter.getContext(),
                          {getMemoryInterfaceAttr("read_data")})});

  // Done
  inPorts.push_back(
      calyx::PortInfo{rewriter.getStringAttr(memName + "_done"),
                      rewriter.getI1Type(), calyx::Direction::Input,
                      DictionaryAttr::get(rewriter.getContext(),
                                          {getMemoryInterfaceAttr("done")})});

  // Write data
  outPorts.push_back(calyx::PortInfo{
      rewriter.getStringAttr(memName + "_write_data"),
      memrefType.getElementType(), calyx::Direction::Output,
      DictionaryAttr::get(rewriter.getContext(),
                          {getMemoryInterfaceAttr("write_data")})});

  // Memory address outputs
  for (auto dim : enumerate(memrefType.getShape())) {
    outPorts.push_back(calyx::PortInfo{
        rewriter.getStringAttr(memName + "_addr" + std::to_string(dim.index())),
        rewriter.getIntegerType(calyx::handleZeroWidth(dim.value())),
        calyx::Direction::Output,
        DictionaryAttr::get(rewriter.getContext(),
                            {getMemoryInterfaceAttr("addr", dim.index())})});
  }

  // Write enable
  outPorts.push_back(calyx::PortInfo{
      rewriter.getStringAttr(memName + "_write_en"), rewriter.getI1Type(),
      calyx::Direction::Output,
      DictionaryAttr::get(rewriter.getContext(),
                          {getMemoryInterfaceAttr("write_en")})});
}

WalkResult
getCiderSourceLocationMetadata(calyx::ComponentOp component,
                               SmallVectorImpl<Attribute> &sourceLocations) {
  Builder builder(component->getContext());
  return component.getControlOp().walk([&](Operation *op) {
    if (!calyx::isControlLeafNode(op))
      return WalkResult::advance();

    std::string sourceLocation;
    llvm::raw_string_ostream os(sourceLocation);
    op->getLoc()->print(os);
    int64_t position = sourceLocations.size();
    sourceLocations.push_back(
        StringAttr::get(op->getContext(), sourceLocation));

    op->setAttr("pos", builder.getI64IntegerAttr(position));
    return WalkResult::advance();
  });
}

bool matchConstantOp(Operation *op, APInt &value) {
  return mlir::detail::constant_int_op_binder(&value).match(op);
}

bool singleLoadFromMemory(Value memoryReference) {
  return llvm::count_if(memoryReference.getUses(), [](OpOperand &user) {
           return isa<mlir::memref::LoadOp>(user.getOwner());
         }) <= 1;
}

bool noStoresToMemory(Value memoryReference) {
  return llvm::none_of(memoryReference.getUses(), [](OpOperand &user) {
    return isa<mlir::memref::StoreOp>(user.getOwner());
  });
}

Value getComponentOutput(calyx::ComponentOp compOp, unsigned outPortIdx) {
  size_t index = compOp.getInputPortInfo().size() + outPortIdx;
  assert(index < compOp.getNumArguments() &&
         "Exceeded number of arguments in the Component");
  return compOp.getArgument(index);
}

Type convIndexType(OpBuilder &builder, Type type) {
  if (type.isIndex())
    return builder.getI32Type();
  return type;
}

void buildAssignmentsForRegisterWrite(OpBuilder &builder,
                                      calyx::GroupOp groupOp,
                                      calyx::ComponentOp componentOp,
                                      calyx::RegisterOp &reg,
                                      Value inputValue) {
  mlir::IRRewriter::InsertionGuard guard(builder);
  auto loc = inputValue.getLoc();
  builder.setInsertionPointToEnd(groupOp.getBody());
  builder.create<calyx::AssignOp>(loc, reg.in(), inputValue);
  builder.create<calyx::AssignOp>(
      loc, reg.write_en(), createConstant(loc, builder, componentOp, 1, 1));
  builder.create<calyx::GroupDoneOp>(loc, reg.done());
}

//===----------------------------------------------------------------------===//
// MemoryInterface
//===----------------------------------------------------------------------===//

MemoryInterface::MemoryInterface() {}
MemoryInterface::MemoryInterface(const MemoryPortsImpl &ports) : impl(ports) {}
MemoryInterface::MemoryInterface(calyx::MemoryOp memOp) : impl(memOp) {}

Value MemoryInterface::readData() {
  if (auto *memOp = std::get_if<calyx::MemoryOp>(&impl); memOp) {
    return memOp->readData();
  }
  return std::get<MemoryPortsImpl>(impl).readData;
}

Value MemoryInterface::done() {
  if (auto *memOp = std::get_if<calyx::MemoryOp>(&impl); memOp) {
    return memOp->done();
  }
  return std::get<MemoryPortsImpl>(impl).done;
}

Value MemoryInterface::writeData() {
  if (auto *memOp = std::get_if<calyx::MemoryOp>(&impl); memOp) {
    return memOp->writeData();
  }
  return std::get<MemoryPortsImpl>(impl).writeData;
}

Value MemoryInterface::writeEn() {
  if (auto *memOp = std::get_if<calyx::MemoryOp>(&impl); memOp) {
    return memOp->writeEn();
  }
  return std::get<MemoryPortsImpl>(impl).writeEn;
}

ValueRange MemoryInterface::addrPorts() {
  if (auto *memOp = std::get_if<calyx::MemoryOp>(&impl); memOp) {
    return memOp->addrPorts();
  }
  return std::get<MemoryPortsImpl>(impl).addrPorts;
}

//===----------------------------------------------------------------------===//
// LoopInterface
//===----------------------------------------------------------------------===//

LoopInterface::~LoopInterface() = default;

//===----------------------------------------------------------------------===//
// ComponentLoweringStateInterface
//===----------------------------------------------------------------------===//

ComponentLoweringStateInterface::ComponentLoweringStateInterface(
    calyx::ComponentOp component)
    : component(component) {}

ComponentLoweringStateInterface::~ComponentLoweringStateInterface() = default;

calyx::ComponentOp ComponentLoweringStateInterface::getComponentOp() {
  return component;
}

void ComponentLoweringStateInterface::addBlockArgReg(Block *block,
                                                     calyx::RegisterOp reg,
                                                     unsigned idx) {
  assert(blockArgRegs[block].count(idx) == 0);
  assert(idx < block->getArguments().size());
  blockArgRegs[block][idx] = reg;
}

const DenseMap<unsigned, calyx::RegisterOp> &
ComponentLoweringStateInterface::getBlockArgRegs(Block *block) {
  return blockArgRegs[block];
}

void ComponentLoweringStateInterface::addBlockArgGroup(Block *from, Block *to,
                                                       calyx::GroupOp grp) {
  blockArgGroups[from][to].push_back(grp);
}

ArrayRef<calyx::GroupOp>
ComponentLoweringStateInterface::getBlockArgGroups(Block *from, Block *to) {
  return blockArgGroups[from][to];
}

std::string ComponentLoweringStateInterface::getUniqueName(StringRef prefix) {
  std::string prefixStr = prefix.str();
  unsigned idx = prefixIdMap[prefixStr];
  ++prefixIdMap[prefixStr];
  return (prefix + "_" + std::to_string(idx)).str();
}

StringRef ComponentLoweringStateInterface::getUniqueName(Operation *op) {
  auto it = opNames.find(op);
  assert(it != opNames.end() && "A unique name should have been set for op");
  return it->second;
}

void ComponentLoweringStateInterface::setUniqueName(Operation *op,
                                                    StringRef prefix) {
  assert(opNames.find(op) == opNames.end() &&
         "A unique name was already set for op");
  opNames[op] = getUniqueName(prefix);
}

void ComponentLoweringStateInterface::registerEvaluatingGroup(
    Value v, calyx::GroupInterface group) {
  valueGroupAssigns[v] = group;
}

void ComponentLoweringStateInterface::addReturnReg(calyx::RegisterOp reg,
                                                   unsigned idx) {
  assert(returnRegs.count(idx) == 0 &&
         "A register was already registered for this index");
  returnRegs[idx] = reg;
}

calyx::RegisterOp ComponentLoweringStateInterface::getReturnReg(unsigned idx) {
  assert(returnRegs.count(idx) && "No register registered for index!");
  return returnRegs[idx];
}

void ComponentLoweringStateInterface::registerMemoryInterface(
    Value memref, const calyx::MemoryInterface &memoryInterface) {
  assert(memref.getType().isa<MemRefType>());
  assert(memories.find(memref) == memories.end() &&
         "Memory already registered for memref");
  memories[memref] = memoryInterface;
}

calyx::MemoryInterface
ComponentLoweringStateInterface::getMemoryInterface(Value memref) {
  assert(memref.getType().isa<MemRefType>());
  auto it = memories.find(memref);
  assert(it != memories.end() && "No memory registered for memref");
  return it->second;
}

Optional<calyx::MemoryInterface>
ComponentLoweringStateInterface::isInputPortOfMemory(Value v) {
  for (auto &memIf : memories) {
    auto &mem = memIf.getSecond();
    if (mem.writeEn() == v || mem.writeData() == v ||
        llvm::any_of(mem.addrPorts(), [=](Value port) { return port == v; }))
      return {mem};
  }
  return {};
}

void ComponentLoweringStateInterface::setFuncOpResultMapping(
    const DenseMap<unsigned, unsigned> &mapping) {
  funcOpResultMapping = mapping;
}

unsigned ComponentLoweringStateInterface::getFuncOpResultMapping(
    unsigned funcReturnIdx) {
  auto it = funcOpResultMapping.find(funcReturnIdx);
  assert(it != funcOpResultMapping.end() &&
         "No component return port index recorded for the requested function "
         "return index");
  return it->second;
}

//===----------------------------------------------------------------------===//
// ProgramLoweringState
//===----------------------------------------------------------------------===//

ProgramLoweringState::ProgramLoweringState(calyx::ProgramOp program,
                                           StringRef topLevelFunction)
    : topLevelFunction(topLevelFunction), program(program) {}

calyx::ProgramOp ProgramLoweringState::getProgram() {
  assert(program.getOperation() != nullptr);
  return program;
}

StringRef ProgramLoweringState::getTopLevelFunction() const {
  return topLevelFunction;
}

std::string ProgramLoweringState::blockName(Block *b) {
  std::string blockName = irName(*b);
  blockName.erase(std::remove(blockName.begin(), blockName.end(), '^'),
                  blockName.end());
  return blockName;
}

//===----------------------------------------------------------------------===//
// ModuleOpConversion
//===----------------------------------------------------------------------===//

ModuleOpConversion::ModuleOpConversion(MLIRContext *context,
                                       StringRef topLevelFunction,
                                       calyx::ProgramOp *programOpOutput)
    : OpRewritePattern<mlir::ModuleOp>(context),
      programOpOutput(programOpOutput), topLevelFunction(topLevelFunction) {
  assert(programOpOutput->getOperation() == nullptr &&
         "this function will set programOpOutput post module conversion");
}

LogicalResult
ModuleOpConversion::matchAndRewrite(mlir::ModuleOp moduleOp,
                                    PatternRewriter &rewriter) const {
  if (!moduleOp.getOps<calyx::ProgramOp>().empty())
    return failure();

  rewriter.updateRootInPlace(moduleOp, [&] {
    // Create ProgramOp
    rewriter.setInsertionPointAfter(moduleOp);
    auto programOp = rewriter.create<calyx::ProgramOp>(
        moduleOp.getLoc(), StringAttr::get(getContext(), topLevelFunction));

    // Inline the module body region
    rewriter.inlineRegionBefore(moduleOp.getBodyRegion(),
                                programOp.getBodyRegion(),
                                programOp.getBodyRegion().end());

    // Inlining the body region also removes ^bb0 from the module body
    // region, so recreate that, before finally inserting the programOp
    auto *moduleBlock = rewriter.createBlock(&moduleOp.getBodyRegion());
    rewriter.setInsertionPointToStart(moduleBlock);
    rewriter.insert(programOp);
    *programOpOutput = programOp;
  });
  return success();
}

//===----------------------------------------------------------------------===//
// Partial lowering patterns
//===----------------------------------------------------------------------===//

FuncOpPartialLoweringPattern::FuncOpPartialLoweringPattern(
    MLIRContext *context, LogicalResult &resRef,
    DenseMap<mlir::func::FuncOp, calyx::ComponentOp> &map,
    calyx::ProgramLoweringState &state)
    : PartialLoweringPattern(context, resRef), functionMapping(map),
      programLoweringState(state) {}

LogicalResult
FuncOpPartialLoweringPattern::partiallyLower(mlir::func::FuncOp funcOp,
                                             PatternRewriter &rewriter) const {
  // Initialize the component op references if a calyx::ComponentOp has been
  // created for the matched funcOp.
  if (auto it = functionMapping.find(funcOp); it != functionMapping.end()) {
    calyx::ComponentOp op = it->second;
    componentOp = &op;
    componentLoweringState =
        programLoweringState.getState<ComponentLoweringStateInterface>(op);
  }

  return PartiallyLowerFuncToComp(funcOp, rewriter);
}

calyx::ComponentOp *FuncOpPartialLoweringPattern::getComponent() const {
  assert(componentOp != nullptr &&
         "Component operation should be set during pattern construction");
  return componentOp;
}

ProgramLoweringState &FuncOpPartialLoweringPattern::programState() const {
  return programLoweringState;
}

//===----------------------------------------------------------------------===//
// ConvertIndexTypes
//===----------------------------------------------------------------------===//

LogicalResult
ConvertIndexTypes::PartiallyLowerFuncToComp(mlir::func::FuncOp funcOp,
                                            PatternRewriter &rewriter) const {
  funcOp.walk([&](Block *block) {
    for (Value arg : block->getArguments())
      arg.setType(calyx::convIndexType(rewriter, arg.getType()));
  });

  funcOp.walk([&](Operation *op) {
    for (Value result : op->getResults()) {
      Type resType = result.getType();
      if (!resType.isIndex())
        continue;

      result.setType(calyx::convIndexType(rewriter, resType));
      auto constant = dyn_cast<mlir::arith::ConstantOp>(op);
      if (!constant)
        continue;

      APInt value;
      calyx::matchConstantOp(constant, value);
      rewriter.setInsertionPoint(constant);
      rewriter.replaceOpWithNewOp<mlir::arith::ConstantOp>(
          constant, rewriter.getI32IntegerAttr(value.getSExtValue()));
    }
  });
  return success();
}

} // namespace calyx
} // namespace circt
