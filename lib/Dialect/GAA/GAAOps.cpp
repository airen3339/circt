//===- GAAOps.cpp - Handshake MLIR Operations -----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the declaration of the GAA operations struct.
//
//===----------------------------------------------------------------------===//
#include "circt/Dialect/GAA/GAAOps.h"
#include "circt/Dialect/HW/HWOps.h"
#include "circt/Dialect/HW/HWTypes.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/DialectImplementation.h"
#include "mlir/IR/FunctionImplementation.h"
#include "mlir/IR/PatternMatch.h"

using namespace mlir;
using namespace circt::gaa;

namespace circt {
namespace gaa {
GAAModuleLike getReferenceModule(InstanceOp instance) {
  auto circuit =
      instance.getOperation()->getParentOfType<circt::gaa::CircuitOp>();
  if (!circuit)
    return nullptr;
  return circuit.lookupSymbol<GAAModuleLike>(instance.moduleNameAttr());
}
llvm::SmallVector<GAAFunctionLike, 4> getFunctions(GAAModuleLike module) {
  llvm::SmallVector<GAAFunctionLike, 4> functions;
  module.getOperation()->walk(
      [&](GAAFunctionLike function) { functions.push_back(function); });
  return functions;
}
llvm::SmallVector<MethodOp, 4> getMethods(ModuleOp module) {
  llvm::SmallVector<MethodOp, 4> methods;
  module.getOperation()->walk(
      [&](MethodOp method) { methods.push_back(method); });
  return methods;
}

llvm::SmallVector<ValueOp, 4> getValues(ModuleOp module) {
  llvm::SmallVector<ValueOp, 4> values;
  module.getOperation()->walk([&](ValueOp value) { values.push_back(value); });
  return values;
}

llvm::SmallVector<RuleOp, 4> getRules(ModuleOp module) {
  llvm::SmallVector<RuleOp, 4> rules;
  module.getOperation()->walk([&](RuleOp rule) { rules.push_back(rule); });
  return rules;
}

llvm::SmallVector<InstanceOp, 4> getInstances(ModuleOp module) {
  llvm::SmallVector<InstanceOp, 4> instances;
  module.getOperation()->walk(
      [&](InstanceOp instance) { instances.push_back(instance); });
  return instances;
}

llvm::SmallVector<BindMethodOp, 4> getMethods(ExtModuleOp module) {
  llvm::SmallVector<BindMethodOp, 4> methods;
  module.getOperation()->walk(
      [&](BindMethodOp method) { methods.push_back(method); });
  return methods;
}

llvm::SmallVector<BindValueOp, 4> getValues(ExtModuleOp module) {
  llvm::SmallVector<BindValueOp, 4> values;
  module.getOperation()->walk(
      [&](BindValueOp value) { values.push_back(value); });
  return values;
}

llvm::SmallVector<InstanceOp, 4> getInstances(GAAModuleLike module) {
  llvm::SmallVector<InstanceOp, 4> instances;
  module.getOperation()->walk(
      [&](InstanceOp instance) { instances.push_back(instance); });
  return instances;
}

} // namespace gaa
} // namespace circt

// Provide the autogenerated implementation guts for the Op classes.
#define GET_OP_CLASSES
#include "circt/Dialect/GAA/GAA.cpp.inc"
