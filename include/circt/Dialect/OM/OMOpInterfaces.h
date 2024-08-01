//===- OMOpInterfaces.h - Object Model operation interfaces ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the Object Model operation declarations.
//
//===----------------------------------------------------------------------===//

#ifndef CIRCT_DIALECT_OM_OMOPINTERFACES_H
#define CIRCT_DIALECT_OM_OMOPINTERFACES_H

#include "mlir/IR/OpDefinition.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/ADT/MapVector.h"

namespace circt::om {

class Field {
  mlir::StringAttr name;
  mlir::Location loc;
  mlir::Type type;

public:
  Field(mlir::StringAttr name, mlir::Location loc, mlir::Type type)
      : name(name), loc(loc), type(type) {}
  mlir::StringAttr getName() { return this->name; };
  mlir::Location getLoc() { return this->loc; };
  mlir::Type getType() { return this->type; };
};

class FieldValue : public Field {
  mlir::Value value;

public:
  FieldValue(mlir::StringAttr name, mlir::Value value)
      : Field(name, value.getLoc(), value.getType()), value(value) {}
  mlir::Value getValue() { return this->value; };
};

} // namespace circt::om

#include "circt/Dialect/OM/OMOpInterfaces.h.inc"

#endif // CIRCT_DIALECT_OM_OMOPINTERFACES_H
