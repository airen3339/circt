//===- ESIDialect.cpp - ESI dialect code defs -------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Dialect definitions. Should be relatively standard boilerplate.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/ESI/ESIDialect.h"
#include "circt/Dialect/ESI/ESIOps.h"
#include "circt/Dialect/ESI/ESITypes.h"
#include "circt/Dialect/RTL/RTLOps.h"
#include "circt/Support/ImplicitLocOpBuilder.h"
#include "circt/Support/LLVM.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Support/FormatVariadic.h"

using namespace circt;
using namespace circt::esi;

ESIDialect::ESIDialect(MLIRContext *context)
    : Dialect("esi", context, TypeID::get<ESIDialect>()) {

  registerTypes();

  addOperations<
#define GET_OP_LIST
#include "circt/Dialect/ESI/ESI.cpp.inc"
      >();
}

struct ESIPortMapping {
  rtl::ModulePortInfo data, valid, ready;
};

/// Find all the port triples on a module which fit the
/// <name>/<name>_valid/<name>_ready pattern. Ready must be the opposite
/// direction of the other two.
void findValidReadySignals(Operation *modOp,
                           SmallVectorImpl<ESIPortMapping> &names) {
  SmallVector<rtl::ModulePortInfo, 64> ports;
  rtl::getModulePortInfo(modOp, ports);

  llvm::StringMap<rtl::ModulePortInfo> nameMap(ports.size());
  for (auto port : ports)
    nameMap[port.getName()] = port;

  for (auto port : ports) {
    if (port.direction == rtl::PortDirection::INOUT)
      continue;

    // Try to find a corresponding 'valid' port.
    SmallString<64> portName = port.getName();
    portName.append("_valid");
    auto valid = nameMap.find(portName);
    if (valid == nameMap.end() || valid->second.direction != port.direction ||
        !valid->second.type.isSignlessInteger(1))
      continue;

    // Try to find a corresponding 'ready' port.
    portName = port.getName();
    portName.append("_ready");
    rtl::PortDirection readyDir = port.direction == rtl::PortDirection::INPUT
                                      ? rtl::PortDirection::OUTPUT
                                      : rtl::PortDirection::INPUT;
    auto ready = nameMap.find(portName);
    if (ready == nameMap.end() || ready->second.direction != readyDir ||
        !valid->second.type.isSignlessInteger(1))
      continue;

    // Found one.
    names.push_back(ESIPortMapping{
        .data = port, .valid = valid->second, .ready = ready->second});
  }
}

/// Build an ESI module wrapper, converting the wires with latency-insensitive
/// semantics with ESI channels and passing through the rest.
Operation *buildESIWrapper(OpBuilder &b, Operation *mod,
                           ArrayRef<ESIPortMapping> esiPortNames) {
  auto *ctxt = b.getContext();
  Location loc = mod->getLoc();
  FunctionType modType = rtl::getModuleType(mod);

  SmallVector<rtl::ModulePortInfo, 64> ports;
  rtl::getModulePortInfo(mod, ports);

  StringSet<> controlPorts;
  // Store a lookup table indexed on the data port name.
  llvm::StringMap<ESIPortMapping> dataPortMap;
  for (const auto &esiPort : esiPortNames) {
    assert(esiPort.data.direction != rtl::PortDirection::INOUT);
    dataPortMap[esiPort.data.name.getValue()] = esiPort;

    assert(esiPort.valid.direction == esiPort.data.direction &&
           "Valid port direction must match data port.");
    controlPorts.insert(esiPort.valid.name.getValue());

    assert(esiPort.ready.direction == (esiPort.data.isOutput()
                                           ? rtl::PortDirection::INPUT
                                           : rtl::PortDirection::OUTPUT) &&
           "Ready must be opposite direction to data.");
    controlPorts.insert(esiPort.ready.name.getValue());
  }

  // Build the list of ports, skipping the valid/ready, and converting the ESI
  // data ports to the ESI channel port type.
  SmallVector<rtl::ModulePortInfo, 64> wrapperPorts;
  // Map the new operand to the old port.
  SmallVector<rtl::ModulePortInfo, 64> inputPortMap;
  // Map the new result to the old port.
  SmallVector<rtl::ModulePortInfo, 64> outputPortMap;
  // Count of the number of input and inout ports of the module we are wrapping.
  size_t wrappedModuleOperands = 0;

  for (auto port : ports) {
    if (!port.isOutput())
      ++wrappedModuleOperands;
    if (controlPorts.contains(port.name.getValue()))
      continue;

    if (dataPortMap.find(port.name.getValue()) != dataPortMap.end())
      port.type = esi::ChannelPort::get(ctxt, port.type);

    if (port.isOutput()) {
      port.argNum = outputPortMap.size();
      outputPortMap.push_back(port);
    } else {
      port.argNum = inputPortMap.size();
      inputPortMap.push_back(port);
    }
    wrapperPorts.push_back(port);
  }

  // Create the wrapper module.
  SmallString<64> wrapperNameBuf;
  StringAttr wrapperName = b.getStringAttr(
      (SymbolTable::getSymbolName(mod) + "_esi").toStringRef(wrapperNameBuf));
  auto wrapper = b.create<rtl::RTLModuleOp>(loc, wrapperName, wrapperPorts);

  // Gather the regular input and inout ports -- they just get passed through.
  SmallVector<Value, 64> wrappedOperands(wrappedModuleOperands);
  for (auto port : wrapperPorts) {
    if (port.isOutput())
      continue;
    if (port.type.isa<esi::ChannelPort>())
      continue;
    size_t wrappedOpNum = inputPortMap[port.argNum].argNum;
    Value arg = wrapper.getArgument(port.argNum);
    wrappedOperands[wrappedOpNum] = arg;
  }

  ImplicitLocOpBuilder modBuilder(wrapper);
  // Instantiate the wrapped module.
  auto wrappedInst = modBuilder.create<rtl::InstanceOp>(
      modType.getResults(), "wrapped", SymbolTable::getSymbolName(mod),
      wrappedOperands, DictionaryAttr());

  SmallVector<Value, 64> outputs(wrapper.getNumResults());
  for (auto port : wrapperPorts) {
    if (!port.isOutput())
      continue;

    size_t wrappedResNum = outputPortMap[port.argNum].argNum;
    outputs[port.argNum] = wrappedInst.getResult(wrappedResNum);
  }

  modBuilder.create<rtl::OutputOp>(outputs);
  return wrapper;

  // if (data->isOutput()) {
  //   assert(valid->direction == rtl::PortDirection::OUTPUT);
  //   assert(ready->direction == rtl::PortDirection::INPUT);
  //   Value dataValue = inst.getResult(data->argNum);
  //   Value validValue = inst.getResult(valid->argNum);
  //   Value readyValue = inst.getOperand(ready->argNum);
  //   b.create<WrapValidReady>(loc, dataValue, )
  // } else {
  //   assert(valid->direction == rtl::PortDirection::INPUT);
  //   assert(ready->direction == rtl::PortDirection::OUTPUT);
  //   Value dataValue = inst.getOperand(data->argNum);
  //   Value validValue = inst.getOperand(valid->argNum);
  //   Value readyValue = inst.getResult(ready->argNum);
  // }
}

#include "circt/Dialect/ESI/ESIAttrs.cpp.inc"
