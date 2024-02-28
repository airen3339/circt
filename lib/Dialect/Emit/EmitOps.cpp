//===- EmitOps.cpp - Implement the Emit operations ------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements `sim` dialect ops.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/Emit/EmitOps.h"
#include "circt/Dialect/Emit/EmitOpInterfaces.h"

using namespace mlir;
using namespace circt;
using namespace emit;

//===----------------------------------------------------------------------===//
// FileOp
//===----------------------------------------------------------------------===//

void FileOp::build(OpBuilder &builder, OperationState &result,
                   StringRef fileName, StringRef symName,
                   llvm::function_ref<void()> bodyCtor) {
  MLIRContext *context = builder.getContext();
  OpBuilder::InsertionGuard guard(builder);

  auto &props = result.getOrAddProperties<Properties>();
  props.sym_name = StringAttr::get(context, symName);
  props.file_name = StringAttr::get(context, fileName);

  builder.createBlock(result.addRegion());
  if (bodyCtor)
    bodyCtor();
}

void FileOp::build(OpBuilder &builder, OperationState &result,
                   StringAttr fileName, llvm::function_ref<void()> bodyCtor) {
  OpBuilder::InsertionGuard guard(builder);

  auto &props = result.getOrAddProperties<Properties>();
  props.file_name = fileName;

  builder.createBlock(result.addRegion());
  if (bodyCtor)
    bodyCtor();
}

//===----------------------------------------------------------------------===//
// RefOp
//===----------------------------------------------------------------------===//

LogicalResult RefOp::verifySymbolUses(SymbolTableCollection &symbolTable) {
  auto target = getTargetAttr();
  auto *op = symbolTable.lookupNearestSymbolFrom(getOperation(), target);
  if (!op)
    return emitError("invalid symbol reference: ") << target;
  if (!op->hasTrait<emit::Emittable>())
    return emitError("does not target an emittable op: ") << target;
  return success();
}

//===----------------------------------------------------------------------===//
// FileListOp
//===----------------------------------------------------------------------===//

LogicalResult FileListOp::verifySymbolUses(SymbolTableCollection &symbolTable) {
  for (auto sym : getFiles()) {
    Operation *op = symbolTable.lookupNearestSymbolFrom(
        getOperation(), sym.cast<FlatSymbolRefAttr>());
    if (!op)
      return emitError("invalid symbol reference: ") << sym;

    if (!isa<emit::FileOp>(op))
      return emitError("referenced operation is not a file: ") << sym;
  }
  return success();
}

//===----------------------------------------------------------------------===//
// TableGen generated logic.
//===----------------------------------------------------------------------===//

// Provide the autogenerated implementation guts for the Op classes.
#define GET_OP_CLASSES
#include "circt/Dialect/Emit/Emit.cpp.inc"
