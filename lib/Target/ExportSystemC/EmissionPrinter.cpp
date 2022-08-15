//===- EmissionPrinter.cpp - EmissionPrinter implementation ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This implements the EmissionPrinter class.
//
//===----------------------------------------------------------------------===//

#include "EmissionPrinter.h"

using namespace circt;
using namespace circt::ExportSystemC;

void EmissionPrinter::emitOp(Operation *op) {
  auto patterns = opPatterns.getSpecificNativePatterns().lookup(op->getName());
  for (auto *pat : patterns) {
    if (pat->matchStatement(op, config)) {
      pat->emitStatement(op, config, *this);
      return;
    }
  }

  // Emit a placeholder to the output and an error to stderr in case no valid
  // emission pattern was found.
  mlir::emitError(op->getLoc(), "no emission pattern found for '")
      << op->getName() << "'\n";
  os << "\n<<UNSUPPORTED OPERATION (" << op->getName() << ")>>\n";
  emissionFailed = true;
}

void EmissionPrinter::emitType(Type type) {
  auto patterns =
      typePatterns.getSpecificNativePatterns().lookup(type.getTypeID());
  for (auto *pat : patterns) {
    if (pat->match(type, config)) {
      pat->emitType(type, config, *this);
      return;
    }
  }

  // Emit a placeholder to the output and an error to stderr in case no valid
  // emission pattern was found. Unfortunately, we cannot use MLIR's error
  // emission here because a type does not carry any location information.
  llvm::errs() << "no emission pattern found for type '" << type << "'\n";
  os << "<<UNSUPPORTED TYPE (" << type << ")>>";
  emissionFailed = true;
}

InlineEmitter EmissionPrinter::getInlinable(Value value) {
  auto *op = value.isa<BlockArgument>() ? value.getParentRegion()->getParentOp()
                                        : value.getDefiningOp();
  auto patterns = opPatterns.getSpecificNativePatterns().lookup(op->getName());
  for (auto *pat : patterns) {
    MatchResult match = pat->matchInlinable(value, config);
    if (!match.failed()) {
      return InlineEmitter([=]() { pat->emitInlined(value, config, *this); },
                           match.getPrecedence());
    }
  }

  // Emit a placeholder to the output and an error to stderr in case no valid
  // emission pattern was found.
  emissionFailed = true;
  mlir::emitError(value.getLoc(), "inlining not supported for value '")
      << value << "'\n";
  return InlineEmitter(
      [&]() { os << "<<INVALID VALUE TO INLINE (" << value << ")>>"; },
      Precedence::LIT);
}

void EmissionPrinter::emitRegion(Region &region) {
  auto scope = os.scope("{\n", "}\n");
  emitRegion(region, scope);
}

void EmissionPrinter::emitRegion(
    Region &region, mlir::raw_indented_ostream::DelimitedScope &scope) {
  assert(region.hasOneBlock() &&
         "only regions with exactly one block are supported for now");

  for (Operation &op : region.getBlocks().front()) {
    emitOp(&op);
  }
}

EmissionPrinter &EmissionPrinter::operator<<(StringRef str) {
  os << str;
  return *this;
}

EmissionPrinter &EmissionPrinter::operator<<(int64_t num) {
  os << std::to_string(num);
  return *this;
}
