//===- SeqOps.cpp - Implement the Seq operations ------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements sequential ops.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/Seq/SeqOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"

#include "llvm/ADT/SmallString.h"

using namespace mlir;
using namespace circt;
using namespace seq;

ParseResult parseCompRegOp(OpAsmParser &parser, OperationState &result) {
  llvm::SMLoc loc = parser.getCurrentLocation();
  SmallVector<OpAsmParser::OperandType, 4> operands;
  if (parser.parseOperandList(operands))
    return failure();
  switch (operands.size()) {
  case 0:
    return parser.emitError(loc, "expected operands");
  case 1:
    return parser.emitError(loc, "expected clock operand");
  case 2:
    // No reset.
    break;
  case 3:
    return parser.emitError(loc, "expected resetValue operand");
  case 4:
    // reset and reset value included.
    break;
  default:
    return parser.emitError(loc, "too many operands");
  }

  Type ty;
  if (parser.parseOptionalAttrDict(result.attributes) || parser.parseColon() ||
      parser.parseType(ty))
    return failure();
  Type i1 = IntegerType::get(result.getContext(), 1);

  // If there was no name specified, check to see if there was a useful name
  // specified in the asm file.
  if (!result.attributes.getNamed("name")) {
    // If there is no explicit name attribute, get it from the SSA result name.
    // If numeric, just use an empty name.
    auto resultName = parser.getResultName(0).first;
    if (!resultName.empty() && !isdigit(resultName[0]))
      result.addAttribute("name",
                          parser.getBuilder().getStringAttr(resultName));
    else
      result.addAttribute("name", parser.getBuilder().getStringAttr(""));
  }

  result.addTypes({ty});
  if (operands.size() == 2)
    return parser.resolveOperands(operands, {ty, i1}, loc, result.operands);
  else
    return parser.resolveOperands(operands, {ty, i1, i1, ty}, loc,
                                  result.operands);
}

static void printCompRegOp(::mlir::OpAsmPrinter &p, CompRegOp reg) {
  p << ' ' << reg.input() << ", " << reg.clk();
  if (reg.reset())
    p << ", " << reg.reset() << ", " << reg.resetValue() << ' ';

  SmallVector<StringRef> elidedAttrs;
  // Determine if 'name' can be elided.
  if (reg.name().empty()) {
    elidedAttrs.push_back("name");
  } else {
    SmallString<32> resultNameStr;
    llvm::raw_svector_ostream tmpStream(resultNameStr);
    p.printOperand(reg.data(), tmpStream);
    auto actualName = tmpStream.str().drop_front();
    if (actualName == reg.name())
      elidedAttrs.push_back("name");
  }

  p.printOptionalAttrDict(reg->getAttrs(), elidedAttrs);
  p << " : " << reg.input().getType();
}

/// Suggest a name for each result value based on the saved result names
/// attribute.
void CompRegOp::getAsmResultNames(OpAsmSetValueNameFn setNameFn) {
  // If the wire has an optional 'name' attribute, use it.
  if (!name().empty())
    setNameFn(getResult(), name());
}

//===----------------------------------------------------------------------===//
// TableGen generated logic.
//===----------------------------------------------------------------------===//

// Provide the autogenerated implementation guts for the Op classes.
#define GET_OP_CLASSES
#include "circt/Dialect/Seq/Seq.cpp.inc"
