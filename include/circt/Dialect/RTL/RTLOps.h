//===- RTLOps.h - Declare RTL dialect operations ----------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file declares the operation classes for the RTL dialect.
//
//===----------------------------------------------------------------------===//

#ifndef CIRCT_DIALECT_RTL_OPS_H
#define CIRCT_DIALECT_RTL_OPS_H

#include "circt/Dialect/RTL/RTLDialect.h"
#include "circt/Dialect/RTL/RTLTypes.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/FunctionSupport.h"
#include "mlir/IR/OpImplementation.h"
#include "mlir/IR/RegionKindInterface.h"
#include "mlir/IR/SymbolTable.h"
#include "mlir/Interfaces/ControlFlowInterfaces.h"
#include "mlir/Interfaces/SideEffectInterfaces.h"

namespace circt {
namespace rtl {

/// A RTL module ports direction.
enum PortDirection {
  INPUT = 1,
  OUTPUT = 2,
  INOUT = 3,
};

/// This holds the name, type, direction of a module's ports
struct ModulePortInfo {
  StringAttr name;
  PortDirection direction;
  Type type;
  size_t argNum = ~0U; // Either the argument index or the result index
                       // depending on the direction.

  StringRef getName() const { return name.getValue(); }
  bool isOutput() const { return direction == OUTPUT; }
};

// Helpers for working with modules.

/// Return true if this is an rtl.module, external module, generated module etc.
bool isAnyModule(Operation *module);

/// Return the signature for the specified module as a function type.
FunctionType getModuleType(Operation *module);

/// Return the port name for the specified argument or result.
StringAttr getModuleArgumentNameAttr(Operation *module, size_t argNo);
StringAttr getModuleResultNameAttr(Operation *module, size_t argNo);

static inline StringRef getModuleArgumentName(Operation *module, size_t argNo) {
  return getModuleArgumentNameAttr(module, argNo).getValue();
}
static inline StringRef getModuleResultName(Operation *module,
                                            size_t resultNo) {
  return getModuleResultNameAttr(module, resultNo).getValue();
}

void setModuleArgumentNames(Operation *module, ArrayRef<Attribute> names);
void setModuleResultNames(Operation *module, ArrayRef<Attribute> names);

/// Return an encapsulated set of information about input and output ports.
SmallVector<ModulePortInfo> getModulePortInfo(Operation *op);

/// Return true if the specified operation is a combinatorial logic op.
bool isCombinatorial(Operation *op);

} // namespace rtl
} // namespace circt

#define GET_OP_CLASSES
#include "circt/Dialect/RTL/RTL.h.inc"

#endif // CIRCT_DIALECT_RTL_OPS_H
