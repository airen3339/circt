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
#include "circt/Dialect/MSFT/MSFTAttributes.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/DialectImplementation.h"

#include "llvm/ADT/TypeSwitch.h"

using namespace circt;
using namespace msft;

//===----------------------------------------------------------------------===//
// Dialect specification.
//===----------------------------------------------------------------------===//

MSFTDialect::MSFTDialect(MLIRContext *context)
    : Dialect(getDialectNamespace(), context,
              ::mlir::TypeID::get<MSFTDialect>()) {
  registerAttributes();
}

MSFTDialect::~MSFTDialect() {}

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

Attribute MSFTDialect::parseAttribute(DialectAsmParser &p, Type type) const {
  StringRef attrName;
  if (p.parseKeyword(&attrName))
    return Attribute();
  if (attrName == "physloc")
    return PhysLocationAttr::parse(p);
  p.emitError(p.getNameLoc(), "Unexpected msft attribute '" + attrName + "'");
  return Attribute();
}

void MSFTDialect::printAttribute(Attribute attr, DialectAsmPrinter &p) const {
  TypeSwitch<Attribute>(attr)
      .Case([&p](PhysLocationAttr a) { a.print(p); })
      .Default([](Attribute) { llvm_unreachable("Unexpected attribute"); });
}

#include "circt/Dialect/MSFT/MSFTEnums.cpp.inc"
