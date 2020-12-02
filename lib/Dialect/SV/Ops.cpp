//===- Ops.cpp - Implement the SV operations ------------------------------===//
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/SV/Ops.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/StandardTypes.h"
#include "llvm/Support/FormatVariadic.h"

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

//===----------------------------------------------------------------------===//
// Extract operation.
//===----------------------------------------------------------------------===//

static ParseResult parseExtractOp(OpAsmParser &p, OperationState &result) {
  MLIRContext *ctxt = result.getContext();
  FlatSymbolRefAttr field;
  OpAsmParser::OperandType extractable;
  Type inputType;
  if (p.parseAttribute(field) || p.parseOperand(extractable) || p.parseColon())
    return failure();
  result.addAttribute("field", field);

  auto typeLoc = p.getCurrentLocation();
  if (p.parseType(inputType))
    return failure();

  if (p.resolveOperand(extractable, inputType, result.operands))
    return failure();

  if (auto ifaceTy = inputType.dyn_cast<InterfaceType>()) {
    SymbolRefAttr ifaceSym = ifaceTy.getInterface();
    SmallVector<FlatSymbolRefAttr, 4> refs;
    auto nested = ifaceSym.getNestedReferences();
    refs.append(nested.begin(), nested.end());
    refs.push_back(field);

    SymbolRefAttr modportSym =
        SymbolRefAttr::get(ifaceSym.getRootReference(), refs, ctxt);
    auto resultPort = InterfaceModportType::get(ctxt, modportSym);
    result.addTypes({resultPort});
    return success();
  } else {
    p.emitError(typeLoc, llvm::formatv("Expected extractable type, got '{0}'",
                                       inputType));
    return failure();
  }
}

static void printExtractOp(OpAsmPrinter &p, ExtractOp &op) {
  p << "sv.extract " << op.fieldAttr() << " " << op.extractable() << " ";
  p.printOptionalAttrDict(op.getAttrs(), /* elidedAttrs */ {"field"});
  p << ": " << op.extractable().getType();
}

// TableGen generated logic.
//===----------------------------------------------------------------------===//

// Provide the autogenerated implementation guts for the Op classes.
#define GET_OP_CLASSES
#include "circt/Dialect/SV/SV.cpp.inc"
#include "circt/Dialect/SV/SVEnums.cpp.inc"
#include "circt/Dialect/SV/SVStructs.cpp.inc"
