//===- MSFTDialect.cpp - Implement the MSFT dialect -----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the MSFT dialect.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/MSFT/MSFTDialect.h"
#include "circt/Dialect/MSFT/MSFTOps.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/DialectImplementation.h"

using namespace circt;
using namespace msft;

//===----------------------------------------------------------------------===//
// Dialect specification.
//===----------------------------------------------------------------------===//

void MSFTDialect::initialize() {
  addOperations<
#define GET_OP_LIST
#include "circt/Dialect/MSFT/MSFT.cpp.inc"
      >();
  registerAttributes();
}

/// Registered hook to materialize a single constant operation from a given
/// attribute value with the desired resultant type. This method should use
/// the provided builder to create the operation without changing the
/// insertion position. The generated operation is expected to be constant
/// like, i.e. single result, zero operands, non side-effecting, etc. On
/// success, this hook should return the value generated to represent the
/// constant value. Otherwise, it should return null on failure.
Operation *MSFTDialect::materializeConstant(OpBuilder &builder, Attribute value,
                                            Type type, Location loc) {
  // Placeholder
  return nullptr;
}

static msft::InstanceOp getInstance(MSFTModuleOp root,
                                    ArrayRef<StringRef> path) {
  assert(!path.empty());

  // Unfortunately, instance names are not symbols and modules are not symbol
  // tables, so we have to do a full walk.
  StringRef searchName = path[0];
  msft::InstanceOp match = nullptr;
  root.walk([&](msft::InstanceOp inst) {
    if (inst.instanceName() != searchName)
      return WalkResult::advance();
    match = inst;
    return WalkResult::interrupt();
  });
  if (!match)
    return nullptr;
  if (path.size() == 1)
    return match;

  // We're not the leaf, so recurse.
  auto subPath = path.slice(1);
  Operation *submoduleOp = match.getReferencedModule();
  auto submodule = dyn_cast<msft::MSFTModuleOp>(submoduleOp);
  if (!submodule)
    return nullptr;
  return getInstance(submodule, subPath);
}

msft::InstanceOp circt::msft::getInstance(MSFTModuleOp root,
                                          SymbolRefAttr pathAttr) {
  SmallVector<StringRef, 16> path;
  path.push_back(pathAttr.getRootReference().getValue());
  for (auto sym : pathAttr.getNestedReferences())
    path.push_back(sym.getValue());
  return ::getInstance(root, path);
}

#include "circt/Dialect/MSFT/MSFTDialect.cpp.inc"
#include "circt/Dialect/MSFT/MSFTEnums.cpp.inc"
