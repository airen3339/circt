//===- SSPAttributes.cpp - SSP attribute implementation -------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the SSP (static scheduling problem) dialect attributes.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/SSP/SSPAttributes.h"
#include "circt/Dialect/SSP/SSPDialect.h"
#include "circt/Support/LLVM.h"

#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"

#include "llvm/ADT/TypeSwitch.h"

using namespace circt;
using namespace ssp;

#define GET_ATTRDEF_CLASSES
#include "circt/Dialect/SSP/SSPAttributes.cpp.inc"

void SSPDialect::registerAttributes() {
  addAttributes<
#define GET_ATTRDEF_LIST
#include "circt/Dialect/SSP/SSPAttributes.cpp.inc"
      >();
}

mlir::OptionalParseResult ssp::parseOptionalPropertyArray(ArrayAttr &attr,
                                                          AsmParser &parser) {
  if (parser.parseOptionalLSquare())
    return {};

  SmallVector<Attribute> elements;
  auto parseListResult = parser.parseCommaSeparatedList([&]() -> ParseResult {
    StringRef mnemonic;
    Attribute elem;
    if (parser.parseOptionalKeyword(&mnemonic)) {
      // not a short-form SSP attribute, delegate to the generic machinery.
      if (parser.parseAttribute(elem))
        return failure();

      elements.push_back(elem);
      return success();
    }

    // Try to parse one of the built-in SSP property attributes.
    auto parseElemResult =
        generatedAttributeParser(parser, mnemonic, Type(), elem);
    if (!parseElemResult.hasValue() || failed(*parseElemResult))
      return parser.emitError(
          parser.getCurrentLocation(),
          "carries unknown or malformed shortform property");

    elements.push_back(elem);
    return success();
  });

  if (parseListResult || parser.parseRSquare())
    return failure();

  attr = parser.getBuilder().getArrayAttr(elements);
  return success();
}

void ssp::printPropertyArray(ArrayAttr attr, AsmPrinter &p) {
  p << '[';
  llvm::interleaveComma(attr.getAsRange<Attribute>(), p, [&](Attribute elem) {
    // Try to emit the shortform for the built-in SSP property attributes, and
    // if that fails, fall back to the generic form.
    if (failed(generatedAttributePrinter(elem, p)))
      p.printAttribute(attr);
  });
  p << ']';
}
