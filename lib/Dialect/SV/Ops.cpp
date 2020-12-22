//===- Ops.cpp - Implement the SV operations ------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/SV/Ops.h"
#include "circt/Dialect/RTL/Types.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/BuiltinTypes.h"

using namespace circt;
using namespace sv;

//===----------------------------------------------------------------------===//
// Control flow like-operations
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// IfDefOp

void IfDefOp::build(OpBuilder &odsBuilder, OperationState &result,
                    StringRef cond, std::function<void()> bodyCtor) {
  result.addAttribute("cond", odsBuilder.getStringAttr(cond));
  Region *body = result.addRegion();
  IfDefOp::ensureTerminator(*body, odsBuilder, result.location);

  // Fill in the body of the #ifdef.
  if (bodyCtor) {
    auto oldIP = &*odsBuilder.getInsertionPoint();
    odsBuilder.setInsertionPointToStart(&*body->begin());
    bodyCtor();
    odsBuilder.setInsertionPoint(oldIP);
  }
}

//===----------------------------------------------------------------------===//
// IfOp

void IfOp::build(OpBuilder &odsBuilder, OperationState &result, Value cond,
                 std::function<void()> bodyCtor) {
  result.addOperands(cond);
  Region *body = result.addRegion();
  IfOp::ensureTerminator(*body, odsBuilder, result.location);

  // Fill in the body of the #ifdef.
  if (bodyCtor) {
    auto oldIP = &*odsBuilder.getInsertionPoint();
    odsBuilder.setInsertionPointToStart(&*body->begin());
    bodyCtor();
    odsBuilder.setInsertionPoint(oldIP);
  }
}

//===----------------------------------------------------------------------===//
// AlwaysAtPosEdgeOp

void AlwaysAtPosEdgeOp::build(OpBuilder &odsBuilder, OperationState &result,
                              Value clock, std::function<void()> bodyCtor) {
  result.addOperands(clock);
  Region *body = result.addRegion();
  AlwaysAtPosEdgeOp::ensureTerminator(*body, odsBuilder, result.location);

  // Fill in the body of the #ifdef.
  if (bodyCtor) {
    auto oldIP = &*odsBuilder.getInsertionPoint();
    odsBuilder.setInsertionPointToStart(&*body->begin());
    bodyCtor();
    odsBuilder.setInsertionPoint(oldIP);
  }
}

//===----------------------------------------------------------------------===//
// TypeDecl operations
//===----------------------------------------------------------------------===//

ModportType InterfaceOp::getModportType(StringRef modportName) {
  InterfaceModportOp modportOp = lookupSymbol<InterfaceModportOp>(modportName);
  assert(modportOp && "Modport symbol not found.");
  return ModportType::get(getContext(),
                          SymbolRefAttr::get(modportName, getContext()));
}

static ParseResult parseModportStructs(OpAsmParser &parser,
                                       ArrayAttr &portsAttr) {
  if (parser.parseLParen())
    return failure();

  auto context = parser.getBuilder().getContext();

  SmallVector<Attribute, 8> ports;
  do {
    NamedAttrList tmpAttrs;
    StringAttr direction;
    FlatSymbolRefAttr signal;
    if (parser.parseAttribute(direction, "port", tmpAttrs) ||
        parser.parseAttribute(signal, "signal", tmpAttrs))
      return failure();

    ports.push_back(ModportStructAttr::get(direction, signal, context));
  } while (succeeded(parser.parseOptionalComma()));

  if (parser.parseRParen())
    return failure();

  portsAttr = ArrayAttr::get(ports, context);

  return success();
}

static void printModportStructs(OpAsmPrinter &p, Operation *,
                                ArrayAttr portsAttr) {
  p << " (";
  for (size_t i = 0, e = portsAttr.size(); i != e; ++i) {
    auto port = portsAttr[i].dyn_cast<ModportStructAttr>();
    p << port.direction();
    p << ' ';
    p.printSymbolName(port.signal().getRootReference());
    if (i < e - 1) {
      p << ", ";
    }
  }
  p << ')';
}

void InterfaceSignalOp::build(mlir::OpBuilder &builder,
                              ::mlir::OperationState &state, StringRef name,
                              mlir::Type type) {
  build(builder, state, name, mlir::TypeAttr::get(type));
}

void InterfaceModportOp::build(OpBuilder &builder, OperationState &state,
                               StringRef name, ArrayRef<StringRef> inputs,
                               ArrayRef<StringRef> outputs) {
  auto *ctxt = builder.getContext();
  SmallVector<Attribute, 8> directions;
  StringAttr inputDir = StringAttr::get("input", ctxt);
  StringAttr outputDir = StringAttr::get("output", ctxt);
  for (auto input : inputs)
    directions.push_back(ModportStructAttr::get(
        inputDir, SymbolRefAttr::get(input, ctxt), ctxt));
  for (auto output : outputs)
    directions.push_back(ModportStructAttr::get(
        outputDir, SymbolRefAttr::get(output, ctxt), ctxt));
  build(builder, state, name, ArrayAttr::get(directions, ctxt));
}

/// Ensure that the symbol being instantiated exists and is an InterfaceOp.
static LogicalResult verifyInterfaceInstanceOp(InterfaceInstanceOp op) {
  auto symtable = SymbolTable::getNearestSymbolTable(op);
  if (!symtable)
    return op.emitError("sv.interface.instance must exist within a region "
                        "which has a symbol table.");
  auto ifaceTy = op.getType().cast<InterfaceType>();
  auto referencedOp =
      SymbolTable::lookupSymbolIn(symtable, ifaceTy.getInterface());
  if (!referencedOp)
    return op.emitError("Symbol not found: ") << ifaceTy.getInterface() << ".";
  if (!isa<InterfaceOp>(referencedOp))
    return op.emitError("Symbol ")
           << ifaceTy.getInterface() << " is not an InterfaceOp.";
  return success();
}

/// Ensure that the symbol being instantiated exists and is an
/// InterfaceModportOp.
static LogicalResult verifyGetModportOp(GetModportOp op) {
  auto symtable = SymbolTable::getNearestSymbolTable(op);
  if (!symtable)
    return op.emitError("sv.interface.instance must exist within a region "
                        "which has a symbol table.");
  auto ifaceTy = op.getType().cast<ModportType>();
  auto referencedOp =
      SymbolTable::lookupSymbolIn(symtable, ifaceTy.getModport());
  if (!referencedOp)
    return op.emitError("Symbol not found: ") << ifaceTy.getModport() << ".";
  if (!isa<InterfaceModportOp>(referencedOp))
    return op.emitError("Symbol ")
           << ifaceTy.getModport() << " is not an InterfaceModportOp.";
  return success();
}

void GetModportOp::build(OpBuilder &builder, OperationState &state, Value value,
                         StringRef field) {
  auto ifaceTy = value.getType().dyn_cast<InterfaceType>();
  assert(ifaceTy && "GetModportOp expects an InterfaceType.");
  auto fieldAttr = SymbolRefAttr::get(field, builder.getContext());
  auto modportSym =
      SymbolRefAttr::get(ifaceTy.getInterface().getRootReference(), {fieldAttr},
                         builder.getContext());
  // state.addTypes();
  // state.addOperands({value});
  // state.addAttribute("field", fieldAttr);
  build(builder, state, {ModportType::get(builder.getContext(), modportSym)},
        {value}, fieldAttr);
}

//===----------------------------------------------------------------------===//
// Other ops.
//===----------------------------------------------------------------------===//

static LogicalResult verifyAliasOp(AliasOp op) {
  // Must have at least two operands.
  if (op.operands().size() < 2)
    return op.emitOpError("alias must have at least two operands");

  return success();
}

//===----------------------------------------------------------------------===//
// TableGen generated logic.
//===----------------------------------------------------------------------===//

// Provide the autogenerated implementation guts for the Op classes.
#define GET_OP_CLASSES
#include "circt/Dialect/SV/SV.cpp.inc"
#include "circt/Dialect/SV/SVEnums.cpp.inc"
#include "circt/Dialect/SV/SVStructs.cpp.inc"
