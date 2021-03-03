//===- RTLDialect.cpp - C Interface for the RTL Dialect -------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  Implements a C Interface for the RTL Dialect
//
//===----------------------------------------------------------------------===//

#include "circt-c/Dialect/RTL.h"
#include "circt/Dialect/RTL/RTLOps.h"
#include "mlir/CAPI/IR.h"
#include "mlir/CAPI/Registration.h"
#include "mlir/CAPI/Support.h"

using namespace circt::rtl;

//===----------------------------------------------------------------------===//
// Dialect API.
//===----------------------------------------------------------------------===//

MLIR_DEFINE_CAPI_DIALECT_REGISTRATION(RTL, rtl, RTLDialect)

//===----------------------------------------------------------------------===//
// Type API.
//===----------------------------------------------------------------------===//

int64_t rtlGetBitWidth(MlirType type) { return getBitWidth(unwrap(type)); }

bool rtlTypeIsAValueType(MlirType type) { return isRTLValueType(unwrap(type)); }

bool rtlTypeIsAArrayType(MlirType type) {
  return unwrap(type).isa<ArrayType>();
}

MlirType rtlArrayTypeGet(MlirType element, size_t size) {
  return wrap(ArrayType::get(unwrap(element), size));
}

MlirType rtlArrayTypeGetElementType(MlirType type) {
  return wrap(unwrap(type).cast<ArrayType>().getElementType());
}

intptr_t rtlArrayTypeGetSize(MlirType type) {
  return unwrap(type).cast<ArrayType>().getSize();
}
