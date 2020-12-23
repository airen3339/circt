//===- Dialect.cpp - Implement the SV dialect -----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/SV/Dialect.h"
#include "circt/Dialect/SV/Ops.h"
#include "circt/Dialect/SV/Types.h"

#include "mlir/IR/DialectImplementation.h"

using namespace circt::sv;
using namespace mlir;

//===----------------------------------------------------------------------===//
// Dialect specification.
//===----------------------------------------------------------------------===//

SVDialect::SVDialect(MLIRContext *context)
    : Dialect(getDialectNamespace(), context,
    ::mlir::TypeID::get<SVDialect>()) {

  // Register types.
  addTypes<
#define GET_TYPEDEF_LIST
#include "circt/Dialect/SV/SVTypes.cpp.inc"
      >();

  // Register operations.
  addOperations<
#define GET_OP_LIST
#include "circt/Dialect/SV/SV.cpp.inc"
      >();
}

SVDialect::~SVDialect() {}
