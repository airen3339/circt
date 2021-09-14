//===- HWOps.cpp - Implement the HW operations ----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implement the HW ops.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/HW/HWOps.h"
#include "circt/Dialect/Comb/CombOps.h"
#include "circt/Dialect/HW/HWVisitors.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/FunctionImplementation.h"

using namespace circt;
using namespace hw;

/// Return true if this string parses as a valid MLIR keyword, false otherwise.
static bool isValidKeyword(StringRef name) {
  if (name.empty() || (!isalpha(name[0]) && name[0] != '_'))
    return false;
  for (auto c : name.drop_front()) {
    if (!isalpha(c) && !isdigit(c) && c != '_' && c != '$' && c != '.')
      return false;
  }

  return true;
}

// Parse a portname as a keyword or a quote surrounded string, followed by a
// colon.
static StringAttr parsePortName(OpAsmParser &parser) {
  StringAttr result;
  StringRef keyword;
  if (succeeded(parser.parseOptionalKeyword(&keyword))) {
    result = parser.getBuilder().getStringAttr(keyword);
  } else if (parser.parseAttribute(result,
                                   parser.getBuilder().getType<NoneType>()))
    return {};
  return succeeded(parser.parseColon()) ? result : StringAttr();
}

/// Return true if the specified operation is a combinatorial logic op.
bool hw::isCombinatorial(Operation *op) {
  struct IsCombClassifier : public TypeOpVisitor<IsCombClassifier, bool> {
    bool visitInvalidTypeOp(Operation *op) { return false; }
    bool visitUnhandledTypeOp(Operation *op) { return true; }
  };

  return (op->getDialect() && op->getDialect()->getNamespace() == "comb") ||
         IsCombClassifier().dispatchTypeOpVisitor(op);
}

//===----------------------------------------------------------------------===//
// ConstantOp
//===----------------------------------------------------------------------===//

static void printConstantOp(OpAsmPrinter &p, ConstantOp &op) {
  p << " ";
  p.printAttribute(op.valueAttr());
  p.printOptionalAttrDict(op->getAttrs(), /*elidedAttrs=*/{"value"});
}

static ParseResult parseConstantOp(OpAsmParser &parser,
                                   OperationState &result) {
  IntegerAttr valueAttr;

  if (parser.parseAttribute(valueAttr, "value", result.attributes) ||
      parser.parseOptionalAttrDict(result.attributes))
    return failure();

  result.addTypes(valueAttr.getType());
  return success();
}

static LogicalResult verifyConstantOp(ConstantOp constant) {
  // If the result type has a bitwidth, then the attribute must match its width.
  if (constant.value().getBitWidth() != constant.getType().getWidth())
    return constant.emitError(
        "hw.constant attribute bitwidth doesn't match return type");

  return success();
}

/// Build a ConstantOp from an APInt, infering the result type from the
/// width of the APInt.
void ConstantOp::build(OpBuilder &builder, OperationState &result,
                       const APInt &value) {

  auto type = IntegerType::get(builder.getContext(), value.getBitWidth());
  auto attr = builder.getIntegerAttr(type, value);
  return build(builder, result, type, attr);
}

/// Build a ConstantOp from an APInt, infering the result type from the
/// width of the APInt.
void ConstantOp::build(OpBuilder &builder, OperationState &result,
                       IntegerAttr value) {
  return build(builder, result, value.getType(), value);
}

/// This builder allows construction of small signed integers like 0, 1, -1
/// matching a specified MLIR IntegerType.  This shouldn't be used for general
/// constant folding because it only works with values that can be expressed in
/// an int64_t.  Use APInt's instead.
void ConstantOp::build(OpBuilder &builder, OperationState &result, Type type,
                       int64_t value) {
  auto numBits = type.cast<IntegerType>().getWidth();
  build(builder, result, APInt(numBits, (uint64_t)value, /*isSigned=*/true));
}

void ConstantOp::getAsmResultNames(
    function_ref<void(Value, StringRef)> setNameFn) {
  auto intTy = getType();
  auto intCst = getValue();

  // Sugar i1 constants with 'true' and 'false'.
  if (intTy.getWidth() == 1)
    return setNameFn(getResult(), intCst.isNullValue() ? "false" : "true");

  // Otherwise, build a complex name with the value and type.
  SmallVector<char, 32> specialNameBuffer;
  llvm::raw_svector_ostream specialName(specialNameBuffer);
  specialName << 'c' << intCst << '_' << intTy;
  setNameFn(getResult(), specialName.str());
}

OpFoldResult ConstantOp::fold(ArrayRef<Attribute> constants) {
  assert(constants.empty() && "constant has no operands");
  return valueAttr();
}

//===----------------------------------------------------------------------===//
// HWModuleOp
//===----------------------------------------------------------------------===/

/// Return true if this is an hw.module, external module, generated module etc.
bool hw::isAnyModule(Operation *module) {
  return isa<HWModuleOp>(module) || isa<HWModuleExternOp>(module) ||
         isa<HWModuleGeneratedOp>(module);
}

/// Return the signature for a module as a function type from the module itself
/// or from an hw::InstanceOp.
FunctionType hw::getModuleType(Operation *moduleOrInstance) {
  if (auto instance = dyn_cast<InstanceOp>(moduleOrInstance)) {
    SmallVector<Type> inputs(instance->getOperandTypes());
    SmallVector<Type> results(instance->getResultTypes());
    return FunctionType::get(instance->getContext(), inputs, results);
  }

  assert(isAnyModule(moduleOrInstance) &&
         "must be called on instance or module");
  auto typeAttr =
      moduleOrInstance->getAttrOfType<TypeAttr>(HWModuleOp::getTypeAttrName());
  return typeAttr.getValue().cast<FunctionType>();
}

/// Return the name to use for the Verilog module that we're referencing
/// here.  This is typically the symbol, but can be overridden with the
/// verilogName attribute.
StringAttr hw::getVerilogModuleNameAttr(Operation *module) {
  auto nameAttr = module->getAttrOfType<StringAttr>("verilogName");
  if (nameAttr)
    return nameAttr;

  return module->getAttrOfType<StringAttr>(SymbolTable::getSymbolAttrName());
}

/// Return the port name for the specified argument or result.
StringAttr hw::getModuleArgumentNameAttr(Operation *module, size_t argNo) {
  auto argNames = module->getAttrOfType<ArrayAttr>("argNames");
  // Tolerate malformed IR here to enable debug printing etc.
  if (argNames && argNo < argNames.size())
    return argNames[argNo].cast<StringAttr>();
  return StringAttr();
}

StringAttr hw::getModuleResultNameAttr(Operation *module, size_t resultNo) {
  auto resultNames = module->getAttrOfType<ArrayAttr>("resultNames");
  // Tolerate malformed IR here to enable debug printing etc.
  if (resultNames && resultNo < resultNames.size())
    return resultNames[resultNo].cast<StringAttr>();
  return StringAttr();
}

void hw::setModuleArgumentNames(Operation *module, ArrayRef<Attribute> names) {
  assert(isAnyModule(module) && "Must be called on a module");
  assert(getModuleType(module).getNumInputs() == names.size() &&
         "incorrect number of arguments names specified");
  module->setAttr("argNames", ArrayAttr::get(module->getContext(), names));
}

void hw::setModuleResultNames(Operation *module, ArrayRef<Attribute> names) {
  assert(isAnyModule(module) && "Must be called on a module");
  assert(getModuleType(module).getNumResults() == names.size() &&
         "incorrect number of arguments names specified");
  module->setAttr("resultNames", ArrayAttr::get(module->getContext(), names));
}

// Flag for parsing different module types
enum ExternModKind { PlainMod, ExternMod, GenMod };

static void buildModule(OpBuilder &builder, OperationState &result,
                        StringAttr name, const ModulePortInfo &ports,
                        ArrayRef<NamedAttribute> attributes) {
  using namespace mlir::function_like_impl;

  // Add an attribute for the name.
  result.addAttribute(SymbolTable::getSymbolAttrName(), name);

  SmallVector<Attribute> argNames, resultNames;

  SmallVector<Type, 4> argTypes;
  for (auto elt : ports.inputs) {
    if (elt.direction == PortDirection::INOUT && !elt.type.isa<hw::InOutType>())
      elt.type = hw::InOutType::get(elt.type);
    argTypes.push_back(elt.type);
    argNames.push_back(elt.name);
  }

  SmallVector<Type, 4> resultTypes;
  for (auto elt : ports.outputs) {
    resultTypes.push_back(elt.type);
    resultNames.push_back(elt.name);
  }

  // Record the argument and result types as an attribute.
  auto type = builder.getFunctionType(argTypes, resultTypes);
  result.addAttribute(getTypeAttrName(), TypeAttr::get(type));
  result.addAttribute("argNames", builder.getArrayAttr(argNames));
  result.addAttribute("resultNames", builder.getArrayAttr(resultNames));
  result.addAttributes(attributes);
  result.addRegion();
}

void HWModuleOp::build(OpBuilder &builder, OperationState &result,
                       StringAttr name, const ModulePortInfo &ports,
                       ArrayRef<NamedAttribute> attributes) {
  buildModule(builder, result, name, ports, attributes);

  // Create a region and a block for the body.
  auto *bodyRegion = result.regions[0].get();
  Block *body = new Block();
  bodyRegion->push_back(body);

  // Add arguments to the body block.
  for (auto elt : ports.inputs)
    body->addArgument(elt.type);

  HWModuleOp::ensureTerminator(*bodyRegion, builder, result.location);
}

void HWModuleOp::build(OpBuilder &builder, OperationState &result,
                       StringAttr name, ArrayRef<PortInfo> ports,
                       ArrayRef<NamedAttribute> attributes) {
  build(builder, result, name, ModulePortInfo(ports), attributes);
}

/// Return the name to use for the Verilog module that we're referencing
/// here.  This is typically the symbol, but can be overridden with the
/// verilogName attribute.
StringRef HWModuleExternOp::getVerilogModuleName() {
  if (auto vname = verilogName())
    return vname.getValue();
  return getName();
}

/// Return the name to use for the Verilog module that we're referencing
/// here.  This is typically the symbol, but can be overridden with the
/// verilogName attribute.
StringAttr HWModuleExternOp::getVerilogModuleNameAttr() {
  if (auto vName = verilogNameAttr())
    return vName;

  return (*this)->getAttrOfType<StringAttr>(SymbolTable::getSymbolAttrName());
}

void HWModuleExternOp::build(OpBuilder &builder, OperationState &result,
                             StringAttr name, const ModulePortInfo &ports,
                             StringRef verilogName,
                             ArrayRef<NamedAttribute> attributes) {
  buildModule(builder, result, name, ports, attributes);

  if (!verilogName.empty())
    result.addAttribute("verilogName", builder.getStringAttr(verilogName));
}

void HWModuleExternOp::build(OpBuilder &builder, OperationState &result,
                             StringAttr name, ArrayRef<PortInfo> ports,
                             StringRef verilogName,
                             ArrayRef<NamedAttribute> attributes) {
  build(builder, result, name, ModulePortInfo(ports), verilogName, attributes);
}

void HWModuleGeneratedOp::build(OpBuilder &builder, OperationState &result,
                                FlatSymbolRefAttr genKind, StringAttr name,
                                const ModulePortInfo &ports,
                                StringRef verilogName,
                                ArrayRef<NamedAttribute> attributes) {
  buildModule(builder, result, name, ports, attributes);
  result.addAttribute("generatorKind", genKind);
  if (!verilogName.empty())
    result.addAttribute("verilogName", builder.getStringAttr(verilogName));
}

void HWModuleGeneratedOp::build(OpBuilder &builder, OperationState &result,
                                FlatSymbolRefAttr genKind, StringAttr name,
                                ArrayRef<PortInfo> ports, StringRef verilogName,
                                ArrayRef<NamedAttribute> attributes) {
  build(builder, result, genKind, name, ModulePortInfo(ports), verilogName,
        attributes);
}

/// Return an encapsulated set of information about input and output ports of
/// the specified module or instance.  The input ports always come before the
/// output ports in the list.
ModulePortInfo hw::getModulePortInfo(Operation *op) {
  assert((isa<InstanceOp>(op) || isAnyModule(op)) &&
         "Can only get module ports from an instance or module");

  // TODO: Remove when argNames/resultNames are stored on instances.
  if (auto instance = dyn_cast<InstanceOp>(op))
    op = instance.getReferencedModule();

  SmallVector<PortInfo> inputs, outputs;
  auto argTypes = getModuleType(op).getInputs();

  auto argNames = op->getAttrOfType<ArrayAttr>("argNames");
  for (unsigned i = 0, e = argTypes.size(); i < e; ++i) {
    bool isInOut = false;
    auto type = argTypes[i];

    if (auto inout = type.dyn_cast<InOutType>()) {
      isInOut = true;
      type = inout.getElementType();
    }

    auto direction = isInOut ? PortDirection::INOUT : PortDirection::INPUT;
    inputs.push_back({argNames[i].cast<StringAttr>(), direction, type, i});
  }

  auto resultNames = op->getAttrOfType<ArrayAttr>("resultNames");
  auto resultTypes = getModuleType(op).getResults();
  for (unsigned i = 0, e = resultTypes.size(); i < e; ++i) {
    outputs.push_back({resultNames[i].cast<StringAttr>(), PortDirection::OUTPUT,
                       resultTypes[i], i});
  }
  return ModulePortInfo(inputs, outputs);
}

/// Return an encapsulated set of information about input and output ports of
/// the specified module or instance.  The input ports always come before the
/// output ports in the list.
SmallVector<PortInfo> hw::getAllModulePortInfos(Operation *op) {
  assert((isa<InstanceOp>(op) || isAnyModule(op)) &&
         "Can only get module ports from an instance or module");

  SmallVector<PortInfo> results;
  auto argTypes = getModuleType(op).getInputs();
  auto argNames = op->getAttrOfType<ArrayAttr>("argNames");
  for (unsigned i = 0, e = argTypes.size(); i < e; ++i) {
    bool isInOut = false;
    auto type = argTypes[i];

    if (auto inout = type.dyn_cast<InOutType>()) {
      isInOut = true;
      type = inout.getElementType();
    }

    auto direction = isInOut ? PortDirection::INOUT : PortDirection::INPUT;
    results.push_back({argNames[i].cast<StringAttr>(), direction, type, i});
  }

  auto resultNames = op->getAttrOfType<ArrayAttr>("resultNames");
  auto resultTypes = getModuleType(op).getResults();
  for (unsigned i = 0, e = resultTypes.size(); i < e; ++i) {
    results.push_back({resultNames[i].cast<StringAttr>(), PortDirection::OUTPUT,
                       resultTypes[i], i});
  }
  return results;
}

static StringAttr getPortNameAttr(MLIRContext *context, StringRef name) {
  if (!name.empty()) {
    // Ignore numeric names like %42
    assert(name.size() > 1 && name[0] == '%' && "Unknown MLIR name");
    if (isdigit(name[1]))
      name = StringRef();
    else
      name = name.drop_front();
  }
  return StringAttr::get(context, name);
}

/// Parse a function result list.
///
///   function-result-list ::= function-result-list-parens
///   function-result-list-parens ::= `(` `)`
///                                 | `(` function-result-list-no-parens `)`
///   function-result-list-no-parens ::= function-result (`,` function-result)*
///   function-result ::= (percent-identifier `:`) type attribute-dict?
///
static ParseResult
parseFunctionResultList(OpAsmParser &parser, SmallVectorImpl<Type> &resultTypes,
                        SmallVectorImpl<NamedAttrList> &resultAttrs,
                        SmallVectorImpl<Attribute> &resultNames) {
  if (parser.parseLParen())
    return failure();

  // Special case for an empty set of parens.
  if (succeeded(parser.parseOptionalRParen()))
    return success();

  // Parse individual function results.
  do {
    resultNames.push_back(parsePortName(parser));
    if (!resultNames.back())
      return failure();

    resultTypes.emplace_back();
    resultAttrs.emplace_back();
    if (parser.parseType(resultTypes.back()) ||
        parser.parseOptionalAttrDict(resultAttrs.back()))
      return failure();
  } while (succeeded(parser.parseOptionalComma()));
  return parser.parseRParen();
}

/// This is a variant of mlor::parseFunctionSignature that allows names on
/// result arguments.
static ParseResult parseModuleFunctionSignature(
    OpAsmParser &parser, SmallVectorImpl<OpAsmParser::OperandType> &argNames,
    SmallVectorImpl<Type> &argTypes, SmallVectorImpl<NamedAttrList> &argAttrs,
    bool &isVariadic, SmallVectorImpl<Type> &resultTypes,
    SmallVectorImpl<NamedAttrList> &resultAttrs,
    SmallVectorImpl<Attribute> &resultNames) {

  using namespace mlir::function_like_impl;
  bool allowArgAttrs = true;
  bool allowVariadic = false;
  if (parseFunctionArgumentList(parser, allowArgAttrs, allowVariadic, argNames,
                                argTypes, argAttrs, isVariadic))
    return failure();

  if (succeeded(parser.parseOptionalArrow()))
    return parseFunctionResultList(parser, resultTypes, resultAttrs,
                                   resultNames);
  return success();
}

static bool hasAttribute(StringRef name, ArrayRef<NamedAttribute> attrs) {
  for (auto &argAttr : attrs)
    if (argAttr.first == name)
      return true;
  return false;
}

static ParseResult parseHWModuleOp(OpAsmParser &parser, OperationState &result,
                                   ExternModKind modKind = PlainMod) {
  using namespace mlir::function_like_impl;

  auto loc = parser.getCurrentLocation();

  SmallVector<OpAsmParser::OperandType, 4> entryArgs;
  SmallVector<NamedAttrList, 4> argAttrs;
  SmallVector<NamedAttrList, 4> resultAttrs;
  SmallVector<Type, 4> argTypes;
  SmallVector<Type, 4> resultTypes;
  auto &builder = parser.getBuilder();

  // Parse the name as a symbol.
  StringAttr nameAttr;
  if (parser.parseSymbolName(nameAttr, SymbolTable::getSymbolAttrName(),
                             result.attributes))
    return failure();

  FlatSymbolRefAttr kindAttr;
  if (modKind == GenMod) {
    if (parser.parseComma() ||
        parser.parseAttribute(kindAttr, "generatorKind", result.attributes)) {
      return failure();
    }
  }

  // Parse the function signature.
  bool isVariadic = false;
  SmallVector<Attribute> resultNames;
  if (parseModuleFunctionSignature(parser, entryArgs, argTypes, argAttrs,
                                   isVariadic, resultTypes, resultAttrs,
                                   resultNames))
    return failure();

  // Record the argument and result types as an attribute.  This is necessary
  // for external modules.
  auto type = builder.getFunctionType(argTypes, resultTypes);
  result.addAttribute(getTypeAttrName(), TypeAttr::get(type));

  // If function attributes are present, parse them.
  if (parser.parseOptionalAttrDictWithKeyword(result.attributes))
    return failure();

  auto *context = result.getContext();

  if (hasAttribute("argNames", result.attributes) ||
      hasAttribute("resultNames", result.attributes)) {
    parser.emitError(
        loc, "explicit argNames and resultNames attributes not allowed");
    return failure();
  }

  // Use the argument and result names if not already specified.
  SmallVector<Attribute> argNames;
  if (!entryArgs.empty()) {
    for (auto &arg : entryArgs)
      argNames.push_back(getPortNameAttr(context, arg.name));
  } else if (!argTypes.empty()) {
    // The parser returns empty names in a special way.
    argNames.assign(argTypes.size(), StringAttr::get(context, ""));
  }

  result.addAttribute("argNames", ArrayAttr::get(context, argNames));
  result.addAttribute("resultNames", ArrayAttr::get(context, resultNames));

  assert(argAttrs.size() == argTypes.size());
  assert(resultAttrs.size() == resultTypes.size());

  // Add the attributes to the function arguments.
  addArgAndResultAttrs(builder, result, argAttrs, resultAttrs);

  // Parse the optional function body.
  auto *body = result.addRegion();
  if (modKind == PlainMod) {
    if (parser.parseRegion(*body, entryArgs,
                           entryArgs.empty() ? ArrayRef<Type>() : argTypes))
      return failure();

    HWModuleOp::ensureTerminator(*body, parser.getBuilder(), result.location);
  }
  return success();
}

static ParseResult parseHWModuleExternOp(OpAsmParser &parser,
                                         OperationState &result) {
  return parseHWModuleOp(parser, result, ExternMod);
}

static ParseResult parseHWModuleGeneratedOp(OpAsmParser &parser,
                                            OperationState &result) {
  return parseHWModuleOp(parser, result, GenMod);
}

FunctionType getHWModuleOpType(Operation *op) {
  auto typeAttr = op->getAttrOfType<TypeAttr>(HWModuleOp::getTypeAttrName());
  return typeAttr.getValue().cast<FunctionType>();
}

static void printModuleSignature(OpAsmPrinter &p, Operation *op,
                                 ArrayRef<Type> argTypes, bool isVariadic,
                                 ArrayRef<Type> resultTypes,
                                 bool &needArgNamesAttr) {
  using namespace mlir::function_like_impl;

  Region &body = op->getRegion(0);
  bool isExternal = body.empty();
  SmallString<32> resultNameStr;

  p << '(';
  for (unsigned i = 0, e = argTypes.size(); i < e; ++i) {
    if (i > 0)
      p << ", ";

    auto argName = getModuleArgumentName(op, i);

    if (!isExternal) {
      // Get the printed format for the argument name.
      resultNameStr.clear();
      llvm::raw_svector_ostream tmpStream(resultNameStr);
      p.printOperand(body.front().getArgument(i), tmpStream);

      // If the name wasn't printable in a way that agreed with argName, make
      // sure to print out an explicit argNames attribute.
      if (tmpStream.str().drop_front() != argName)
        needArgNamesAttr = true;

      p << tmpStream.str() << ": ";
    } else if (!argName.empty()) {
      p << '%' << argName << ": ";
    }

    p.printType(argTypes[i]);
    p.printOptionalAttrDict(getArgAttrs(op, i));
  }

  if (isVariadic) {
    if (!argTypes.empty())
      p << ", ";
    p << "...";
  }

  p << ')';

  // We print result types specially since we support named arguments.
  if (!resultTypes.empty()) {
    p << " -> (";
    for (size_t i = 0, e = resultTypes.size(); i < e; ++i) {
      if (i != 0)
        p << ", ";
      StringAttr name = getModuleResultNameAttr(op, i);
      if (isValidKeyword(name.getValue()))
        p << name.getValue();
      else
        p << name;
      p << ": ";

      p.printType(resultTypes[i]);
      p.printOptionalAttrDict(getResultAttrs(op, i));
    }
    p << ')';
  }
}

static void printModuleOp(OpAsmPrinter &p, Operation *op,
                          ExternModKind modKind) {
  using namespace mlir::function_like_impl;

  FunctionType fnType = getHWModuleOpType(op);
  auto argTypes = fnType.getInputs();
  auto resultTypes = fnType.getResults();

  // Print the operation and the function name.
  p << ' ';
  p.printSymbolName(SymbolTable::getSymbolName(op).getValue());
  if (modKind == GenMod) {
    p << ", ";
    p.printSymbolName(cast<HWModuleGeneratedOp>(op).generatorKind());
  }

  bool needArgNamesAttr = false;
  printModuleSignature(p, op, argTypes, /*isVariadic=*/false, resultTypes,
                       needArgNamesAttr);

  SmallVector<StringRef, 3> omittedAttrs;
  if (modKind == GenMod)
    omittedAttrs.push_back("generatorKind");
  if (!needArgNamesAttr)
    omittedAttrs.push_back("argNames");
  omittedAttrs.push_back("resultNames");

  printFunctionAttributes(p, op, argTypes.size(), resultTypes.size(),
                          omittedAttrs);
}

static void printHWModuleExternOp(OpAsmPrinter &p, HWModuleExternOp op) {
  printModuleOp(p, op, ExternMod);
}
static void printHWModuleGeneratedOp(OpAsmPrinter &p, HWModuleGeneratedOp op) {
  printModuleOp(p, op, GenMod);
}

static void printHWModuleOp(OpAsmPrinter &p, HWModuleOp op) {
  printModuleOp(p, op, PlainMod);

  // Print the body if this is not an external function.
  Region &body = op.getBody();
  if (!body.empty())
    p.printRegion(body, /*printEntryBlockArgs=*/false,
                  /*printBlockTerminators=*/true);
}

static LogicalResult verifyModuleCommon(Operation *module) {
  assert(isAnyModule(module) &&
         "verifier hook should only be called on modules");

  auto moduleType = getModuleType(module);
  auto argNames = module->getAttrOfType<ArrayAttr>("argNames");
  auto resultNames = module->getAttrOfType<ArrayAttr>("resultNames");
  if (argNames.size() != moduleType.getNumInputs())
    return module->emitOpError("incorrect number of argument names");
  if (resultNames.size() != moduleType.getNumResults())
    return module->emitOpError("incorrect number of result names");
  return success();
}

static LogicalResult verifyHWModuleOp(HWModuleOp op) {
  return verifyModuleCommon(op);
}

static LogicalResult verifyHWModuleExternOp(HWModuleExternOp op) {
  return verifyModuleCommon(op);
}

/// Lookup the generator for the symbol.  This returns null on
/// invalid IR.
Operation *HWModuleGeneratedOp::getGeneratorKindOp() {
  auto topLevelModuleOp = (*this)->getParentOfType<ModuleOp>();
  return topLevelModuleOp.lookupSymbol(generatorKind());
}

static LogicalResult verifyHWModuleGeneratedOp(HWModuleGeneratedOp op) {
  if (failed(verifyModuleCommon(op)))
    return failure();

  auto referencedKind = op.getGeneratorKindOp();
  if (referencedKind == nullptr)
    return op.emitError("Cannot find generator definition '")
           << op.generatorKind() << "'";

  if (!isa<HWGeneratorSchemaOp>(referencedKind))
    return op.emitError("Symbol resolved to '")
           << referencedKind->getName()
           << "' which is not a HWGeneratorSchemaOp";

  auto referencedKindOp = dyn_cast<HWGeneratorSchemaOp>(referencedKind);
  auto paramRef = referencedKindOp.requiredAttrs();
  auto dict = op->getAttrDictionary();
  for (auto str : paramRef) {
    auto strAttr = str.dyn_cast<StringAttr>();
    if (!strAttr)
      return op.emitError("Unknown attribute type, expected a string");
    if (!dict.get(strAttr.getValue()))
      return op.emitError("Missing attribute '") << strAttr.getValue() << "'";
  }

  return success();
}

//===----------------------------------------------------------------------===//
// InstanceOp
//===----------------------------------------------------------------------===//

/// Create a instance that refers to a known module.
void InstanceOp::build(OpBuilder &builder, OperationState &result,
                       Operation *module, StringAttr name,
                       ArrayRef<Value> inputs, DictionaryAttr parameters,
                       StringAttr sym_name) {
  assert(isAnyModule(module) && "Can only reference a module");
  FunctionType modType = getModuleType(module);
  build(builder, result, modType.getResults(), name,
        FlatSymbolRefAttr::get(SymbolTable::getSymbolName(module)), inputs,
        module->getAttrOfType<ArrayAttr>("argNames"),
        module->getAttrOfType<ArrayAttr>("resultNames"), parameters, sym_name);
}

/// Lookup the module or extmodule for the symbol.  This returns null on
/// invalid IR.
Operation *InstanceOp::getReferencedModule(const SymbolCache *cache) {
  if (cache)
    if (auto *result = cache->getDefinition(moduleNameAttr()))
      return result;

  auto topLevelModuleOp = (*this)->getParentOfType<ModuleOp>();
  if (!topLevelModuleOp)
    return nullptr;

  return topLevelModuleOp.lookupSymbol(moduleName());
}

// Helper function to verify instance op types
static LogicalResult verifyInstanceOpTypes(InstanceOp op, Operation *module) {
  assert(module && "referenced module must not be null");

  // Make sure our port and result names match.
  ArrayAttr argNames = op.argNamesAttr();
  ArrayAttr modArgNames = module->getAttrOfType<ArrayAttr>("argNames");

  // Check operand types first.
  auto numOperands = op->getNumOperands();
  auto expectedOperandTypes = getModuleType(module).getInputs();

  if (expectedOperandTypes.size() != numOperands) {
    auto diag = op.emitOpError()
                << "has a wrong number of operands; expected "
                << expectedOperandTypes.size() << " but got " << numOperands;
    diag.attachNote(module->getLoc()) << "original module declared here";
    return failure();
  }

  if (argNames.size() != numOperands) {
    auto diag = op.emitOpError()
                << "has a wrong number of input port names; expected "
                << numOperands << " but got " << argNames.size();
    diag.attachNote(module->getLoc()) << "original module declared here";
    return failure();
  }

  for (size_t i = 0; i != numOperands; ++i) {
    auto expectedType = expectedOperandTypes[i];
    auto operandType = op.getOperand(i).getType();
    if (operandType != expectedType) {
      auto diag = op.emitOpError()
                  << "operand type #" << i << " must be " << expectedType
                  << ", but got " << operandType;
      diag.attachNote(module->getLoc()) << "original module declared here";
      return failure();
    }

    if (argNames[i] != modArgNames[i]) {
      auto diag = op.emitOpError()
                  << "input label #" << i << " must be " << modArgNames[i]
                  << ", but got " << argNames[i];
      diag.attachNote(module->getLoc()) << "original module declared here";
      module->dump();
      return failure();
    }
  }

  // Check result types and labels.
  auto numResults = op->getNumResults();
  auto expectedResultTypes = getModuleType(module).getResults();
  ArrayAttr resultNames = op.resultNamesAttr();
  ArrayAttr modResultNames = module->getAttrOfType<ArrayAttr>("resultNames");

  if (expectedResultTypes.size() != numResults) {
    auto diag = op.emitOpError()
                << "has a wrong number of results; expected "
                << expectedResultTypes.size() << " but got " << numResults;
    diag.attachNote(module->getLoc()) << "original module declared here";
    return failure();
  }
  if (resultNames.size() != numResults) {
    auto diag = op.emitOpError()
                << "has a wrong number of results port labels; expected "
                << numResults << " but got " << resultNames.size();
    diag.attachNote(module->getLoc()) << "original module declared here";
    return failure();
  }

  for (size_t i = 0; i != numResults; ++i) {
    auto expectedType = expectedResultTypes[i];
    auto resultType = op.getResult(i).getType();
    if (resultType != expectedType) {
      auto diag = op.emitOpError()
                  << "result type #" << i << " must be " << expectedType
                  << ", but got " << resultType;
      diag.attachNote(module->getLoc()) << "original module declared here";
      return failure();
    }

    if (resultNames[i] != modResultNames[i]) {
      auto diag = op.emitOpError()
                  << "input label #" << i << " must be " << modResultNames[i]
                  << ", but got " << resultNames[i];
      diag.attachNote(module->getLoc()) << "original module declared here";
      return failure();
    }
  }

  return success();
}

LogicalResult InstanceOp::verifySymbolUses(SymbolTableCollection &symbolTable) {
  auto *module = symbolTable.lookupNearestSymbolFrom(*this, moduleNameAttr());
  if (module == nullptr)
    return emitError("Cannot find module definition '") << moduleName() << "'";

  // It must be some sort of module.
  if (!isAnyModule(module))
    return emitError("symbol reference '")
           << moduleName() << "' isn't a module";

  // Check that input and result types are consistent with the referenced
  // module.
  return verifyInstanceOpTypes(*this, module);
}

static ParseResult parseInstanceOp(OpAsmParser &parser,
                                   OperationState &result) {
  StringAttr instanceNameAttr;
  StringAttr sym_nameAttr;
  FlatSymbolRefAttr moduleNameAttr;
  SmallVector<OpAsmParser::OperandType, 4> inputsOperands;
  SmallVector<Type> inputsTypes;
  SmallVector<Type> allResultTypes;
  auto noneType = parser.getBuilder().getType<NoneType>();

  if (parser.parseAttribute(instanceNameAttr, noneType, "instanceName",
                            result.attributes))
    return failure();

  if (succeeded(parser.parseOptionalKeyword("sym"))) {
    // Parsing an optional symbol name doesn't fail, so no need to check the
    // result.
    (void)parser.parseOptionalSymbolName(sym_nameAttr, "sym_name",
                                         result.attributes);
  }

  // Parse a paren-enclosed list of comma-separated items.
  auto parseCommaSeparatedList = [&](auto fn) -> ParseResult {
    if (parser.parseLParen())
      return failure();

    // Empty list.
    if (succeeded(parser.parseOptionalRParen()))
      return success();

    do {
      if (failed(fn()))
        return failure();
    } while (succeeded(parser.parseOptionalComma()));
    return parser.parseRParen();
  };

  SmallVector<Attribute> argNames, resultNames;
  llvm::SMLoc inputsOperandsLoc;
  if (parser.parseAttribute(moduleNameAttr, noneType, "moduleName",
                            result.attributes) ||
      parser.getCurrentLocation(&inputsOperandsLoc) ||
      parseCommaSeparatedList([&]() -> ParseResult {
        argNames.push_back(parsePortName(parser));
        if (!argNames.back())
          return failure();
        inputsOperands.push_back({});
        inputsTypes.push_back({});
        return failure(parser.parseOperand(inputsOperands.back()) ||
                       parser.parseColon() ||
                       parser.parseType(inputsTypes.back()));
      }) ||
      parser.resolveOperands(inputsOperands, inputsTypes, inputsOperandsLoc,
                             result.operands) ||
      parser.parseArrow() || parseCommaSeparatedList([&]() -> ParseResult {
        resultNames.push_back(parsePortName(parser));
        if (!resultNames.back())
          return failure();
        allResultTypes.push_back({});
        return parser.parseType(allResultTypes.back());
      }) ||
      parser.parseOptionalAttrDict(result.attributes)) {
    return failure();
  }

  result.addAttribute("argNames", parser.getBuilder().getArrayAttr(argNames));
  result.addAttribute("resultNames",
                      parser.getBuilder().getArrayAttr(resultNames));
  result.addTypes(allResultTypes);
  return success();
}

static void printInstanceOp(OpAsmPrinter &p, InstanceOp op) {
  ModulePortInfo portInfo = getModulePortInfo(op);
  size_t nextInputPort = 0, nextOutputPort = 0;

  auto printPortName = [&](size_t &nextPort, SmallVector<PortInfo> &portList) {
    // Allow printing mangled instances.
    if (nextPort >= portList.size()) {
      p << "<corrupt port>: ";
      return;
    }

    // Print this as a bareword if it can be parsed as an MLIR keyword,
    // otherwise print it as a quoted string.
    StringAttr name = portList[nextPort++].name;
    if (isValidKeyword(name.getValue()))
      p << name.getValue();
    else
      p << name;
    p << ": ";
  };

  p << ' ';
  p.printAttributeWithoutType(op.instanceNameAttr());
  if (auto attr = op.sym_nameAttr()) {
    p << " sym ";
    p.printSymbolName(attr.getValue());
  }
  p << ' ';
  p.printAttributeWithoutType(op.moduleNameAttr());
  p << '(';
  llvm::interleaveComma(op.inputs(), p, [&](Value op) {
    printPortName(nextInputPort, portInfo.inputs);
    p << op << ": " << op.getType();
  });
  p << ") -> (";
  llvm::interleaveComma(op.getResults(), p, [&](Value res) {
    printPortName(nextOutputPort, portInfo.outputs);
    p << res.getType();
  });
  p << ')';
  p.printOptionalAttrDict(
      op->getAttrs(), /*elidedAttrs=*/{"instanceName", "sym_name", "moduleName",
                                       "argNames", "resultNames"});
}

/// Return the name of the specified input port or null if it cannot be
/// determined.
StringAttr InstanceOp::getArgumentName(size_t idx) {
  auto names = argNames();
  // Tolerate malformed IR here to enable debug printing etc.
  if (names && idx < names.size())
    return names[idx].cast<StringAttr>();
  return StringAttr();
}

/// Return the name of the specified result or null if it cannot be
/// determined.
StringAttr InstanceOp::getResultName(size_t idx) {
  auto names = resultNames();
  // Tolerate malformed IR here to enable debug printing etc.
  if (names && idx < names.size())
    return names[idx].cast<StringAttr>();
  return StringAttr();
}

/// Change the name of the specified input port.
void InstanceOp::setArgumentName(size_t i, StringAttr name) {
  auto names = argNames();
  SmallVector<Attribute> newNames(names.begin(), names.end());
  if (newNames[i] == name)
    return;
  newNames[i] = name;
  setArgumentNames(ArrayAttr::get(getContext(), names));
}

/// Change the name of the specified output port.
void InstanceOp::setResultName(size_t i, StringAttr name) {
  auto names = resultNames();
  SmallVector<Attribute> newNames(names.begin(), names.end());
  if (newNames[i] == name)
    return;
  newNames[i] = name;
  setResultNames(ArrayAttr::get(getContext(), names));
}

/// Suggest a name for each result value based on the saved result names
/// attribute.
void InstanceOp::getAsmResultNames(OpAsmSetValueNameFn setNameFn) {
  // Provide default names for instance results.
  std::string name = instanceName().str() + ".";
  size_t baseNameLen = name.size();

  for (size_t i = 0, e = getNumResults(); i != e; ++i) {
    auto resName = getResultName(i);
    name.resize(baseNameLen);
    if (resName && !resName.getValue().empty())
      name += resName.getValue().str();
    else
      name += std::to_string(i);
    setNameFn(getResult(i), name);
  }
}

//===----------------------------------------------------------------------===//
// HWOutputOp
//===----------------------------------------------------------------------===//

/// Verify that the num of operands and types fit the declared results.
static LogicalResult verifyOutputOp(OutputOp *op) {
  // Check that the we (hw.output) have the same number of operands as our
  // region has results.
  auto opParent = (*op)->getParentOp();
  FunctionType modType = getModuleType(opParent);
  ArrayRef<Type> modResults = modType.getResults();
  OperandRange outputValues = op->getOperands();
  if (modResults.size() != outputValues.size()) {
    op->emitOpError("must have same number of operands as region results.");
    return failure();
  }

  // Check that the types of our operands and the region's results match.
  for (size_t i = 0, e = modResults.size(); i < e; ++i) {
    if (modResults[i] != outputValues[i].getType()) {
      op->emitOpError("output types must match module. In "
                      "operand ")
          << i << ", expected " << modResults[i] << ", but got "
          << outputValues[i].getType() << ".";
      return failure();
    }
  }

  return success();
}

//===----------------------------------------------------------------------===//
// Other Operations
//===----------------------------------------------------------------------===//

static ParseResult parseSliceTypes(OpAsmParser &p, Type &srcType,
                                   Type &idxType) {
  Type type;
  if (p.parseType(type))
    return p.emitError(p.getCurrentLocation(), "Expected type");
  auto arrType = type_dyn_cast<ArrayType>(type);
  if (!arrType)
    return p.emitError(p.getCurrentLocation(), "Expected !hw.array type");
  srcType = type;
  unsigned idxWidth = llvm::Log2_64_Ceil(arrType.getSize());
  idxType = IntegerType::get(p.getBuilder().getContext(), idxWidth);
  return success();
}

static void printSliceTypes(OpAsmPrinter &p, Operation *, Type srcType,
                            Type idxType) {
  p.printType(srcType);
}

static ParseResult parseArrayCreateOp(OpAsmParser &parser,
                                      OperationState &result) {
  llvm::SMLoc inputOperandsLoc = parser.getCurrentLocation();
  llvm::SmallVector<OpAsmParser::OperandType, 16> operands;
  Type elemType;

  if (parser.parseOperandList(operands) ||
      parser.parseOptionalAttrDict(result.attributes) || parser.parseColon() ||
      parser.parseType(elemType))
    return failure();

  if (operands.size() == 0)
    return parser.emitError(inputOperandsLoc,
                            "Cannot construct an array of length 0");
  result.addTypes({ArrayType::get(elemType, operands.size())});

  for (auto operand : operands)
    if (parser.resolveOperand(operand, elemType, result.operands))
      return failure();
  return success();
}

static void printArrayCreateOp(OpAsmPrinter &p, ArrayCreateOp op) {
  p << " ";
  p.printOperands(op.inputs());
  p << " : " << op.inputs()[0].getType();
}

void ArrayCreateOp::build(OpBuilder &b, OperationState &state,
                          ValueRange values) {
  assert(values.size() > 0 && "Cannot build array of zero elements");
  Type elemType = values[0].getType();
  assert(llvm::all_of(
             values,
             [elemType](Value v) -> bool { return v.getType() == elemType; }) &&
         "All values must have same type.");
  build(b, state, ArrayType::get(elemType, values.size()), values);
}

static ParseResult parseArrayConcatTypes(OpAsmParser &p,
                                         SmallVectorImpl<Type> &inputTypes,
                                         Type &resultType) {
  Type elemType;
  uint64_t resultSize = 0;
  do {
    Type ty;
    if (p.parseType(ty))
      return p.emitError(p.getCurrentLocation(), "Expected type");
    auto arrTy = type_dyn_cast<ArrayType>(ty);
    if (!arrTy)
      return p.emitError(p.getCurrentLocation(), "Expected !hw.array type");
    if (elemType && elemType != arrTy.getElementType())
      return p.emitError(p.getCurrentLocation(), "Expected array element type ")
             << elemType;

    elemType = arrTy.getElementType();
    inputTypes.push_back(ty);
    resultSize += arrTy.getSize();
  } while (!p.parseOptionalComma());

  resultType = ArrayType::get(elemType, resultSize);
  return success();
}

static void printArrayConcatTypes(OpAsmPrinter &p, Operation *,
                                  TypeRange inputTypes, Type resultType) {
  llvm::interleaveComma(inputTypes, p, [&p](Type t) { p << t; });
}

void ArrayConcatOp::build(OpBuilder &b, OperationState &state,
                          ValueRange values) {
  assert(!values.empty() && "Cannot build array of zero elements");
  ArrayType arrayTy = values[0].getType().cast<ArrayType>();
  Type elemTy = arrayTy.getElementType();
  assert(llvm::all_of(values,
                      [elemTy](Value v) -> bool {
                        return v.getType().isa<ArrayType>() &&
                               v.getType().cast<ArrayType>().getElementType() ==
                                   elemTy;
                      }) &&
         "All values must be of ArrayType with the same element type.");

  uint64_t resultSize = 0;
  for (Value val : values)
    resultSize += val.getType().cast<ArrayType>().getSize();
  build(b, state, ArrayType::get(elemTy, resultSize), values);
}

//===----------------------------------------------------------------------===//
// StructCreateOp
//===----------------------------------------------------------------------===//

static ParseResult parseStructCreateOp(OpAsmParser &parser,
                                       OperationState &result) {
  llvm::SMLoc inputOperandsLoc = parser.getCurrentLocation();
  llvm::SmallVector<OpAsmParser::OperandType, 4> operands;
  Type declOrAliasType;

  if (parser.parseLParen() || parser.parseOperandList(operands) ||
      parser.parseRParen() || parser.parseOptionalAttrDict(result.attributes) ||
      parser.parseColonType(declOrAliasType))
    return failure();

  auto declType = type_dyn_cast<StructType>(declOrAliasType);
  if (!declType)
    return parser.emitError(parser.getNameLoc(),
                            "expected !hw.struct type or alias");

  llvm::SmallVector<Type, 4> structInnerTypes;
  declType.getInnerTypes(structInnerTypes);
  result.addTypes(declOrAliasType);

  if (parser.resolveOperands(operands, structInnerTypes, inputOperandsLoc,
                             result.operands))
    return failure();
  return success();
}

static void printStructCreateOp(OpAsmPrinter &printer, hw::StructCreateOp op) {
  printer << " (";
  printer.printOperands(op.input());
  printer << ")";
  printer.printOptionalAttrDict(op->getAttrs());
  printer << " : " << op.getType();
}

//===----------------------------------------------------------------------===//
// StructExplodeOp
//===----------------------------------------------------------------------===//

static ParseResult parseStructExplodeOp(OpAsmParser &parser,
                                        OperationState &result) {
  OpAsmParser::OperandType operand;
  Type declType;

  if (parser.parseOperand(operand) ||
      parser.parseOptionalAttrDict(result.attributes) ||
      parser.parseColonType(declType))
    return failure();
  auto structType = type_dyn_cast<StructType>(declType);
  if (!structType)
    return parser.emitError(parser.getNameLoc(),
                            "invalid kind of type specified");

  llvm::SmallVector<Type, 4> structInnerTypes;
  structType.getInnerTypes(structInnerTypes);
  result.addTypes(structInnerTypes);

  if (parser.resolveOperand(operand, declType, result.operands))
    return failure();
  return success();
}

static void printStructExplodeOp(OpAsmPrinter &printer,
                                 hw::StructExplodeOp op) {
  printer << " ";
  printer.printOperand(op.input());
  printer.printOptionalAttrDict(op->getAttrs());
  printer << " : " << op.input().getType();
}

//===----------------------------------------------------------------------===//
// StructExtractOp
//===----------------------------------------------------------------------===//

/// Use the same parser for both struct_extract and union_extract since the
/// syntax is identical.
template <typename AggregateType>
static ParseResult parseExtractOp(OpAsmParser &parser, OperationState &result) {
  OpAsmParser::OperandType operand;
  StringAttr fieldName;
  Type declType;

  if (parser.parseOperand(operand) || parser.parseLSquare() ||
      parser.parseAttribute(fieldName, "field", result.attributes) ||
      parser.parseRSquare() ||
      parser.parseOptionalAttrDict(result.attributes) ||
      parser.parseColonType(declType))
    return failure();
  auto aggType = type_dyn_cast<AggregateType>(declType);
  if (!aggType)
    return parser.emitError(parser.getNameLoc(),
                            "invalid kind of type specified");

  Type resultType = aggType.getFieldType(fieldName.getValue());
  if (!resultType) {
    parser.emitError(parser.getNameLoc(), "invalid field name specified");
    return failure();
  }
  result.addTypes(resultType);

  if (parser.resolveOperand(operand, declType, result.operands))
    return failure();
  return success();
}

/// Use the same printer for both struct_extract and union_extract since the
/// syntax is identical.
template <typename AggType>
static void printExtractOp(OpAsmPrinter &printer, AggType op) {
  printer << " ";
  printer.printOperand(op.input());
  printer << "[\"" << op.field() << "\"]";
  printer.printOptionalAttrDict(op->getAttrs(), {"field"});
  printer << " : " << op.input().getType();
}

static ParseResult parseStructExtractOp(OpAsmParser &parser,
                                        OperationState &result) {
  return parseExtractOp<StructType>(parser, result);
}

static void printStructExtractOp(OpAsmPrinter &printer,
                                 hw::StructExtractOp op) {
  printExtractOp(printer, op);
}

void StructExtractOp::build(OpBuilder &builder, OperationState &odsState,
                            Value input, StructType::FieldInfo field) {
  build(builder, odsState, field.type, input, field.name);
}

//===----------------------------------------------------------------------===//
// StructInjectOp
//===----------------------------------------------------------------------===//

static ParseResult parseStructInjectOp(OpAsmParser &parser,
                                       OperationState &result) {
  llvm::SMLoc inputOperandsLoc = parser.getCurrentLocation();
  OpAsmParser::OperandType operand, val;
  StringAttr fieldName;
  Type declType;

  if (parser.parseOperand(operand) || parser.parseLSquare() ||
      parser.parseAttribute(fieldName, "field", result.attributes) ||
      parser.parseRSquare() || parser.parseComma() ||
      parser.parseOperand(val) ||
      parser.parseOptionalAttrDict(result.attributes) ||
      parser.parseColonType(declType))
    return failure();
  auto structType = type_dyn_cast<StructType>(declType);
  if (!structType)
    return parser.emitError(inputOperandsLoc, "invalid kind of type specified");

  Type resultType = structType.getFieldType(fieldName.getValue());
  if (!resultType) {
    parser.emitError(inputOperandsLoc, "invalid field name specified");
    return failure();
  }
  result.addTypes(declType);

  if (parser.resolveOperands({operand, val}, {declType, resultType},
                             inputOperandsLoc, result.operands))
    return failure();
  return success();
}

static void printStructInjectOp(OpAsmPrinter &printer, hw::StructInjectOp op) {
  printer << " ";
  printer.printOperand(op.input());
  printer << "[\"" << op.field() << "\"], ";
  printer.printOperand(op.newValue());
  printer.printOptionalAttrDict(op->getAttrs(), {"field"});
  printer << " : " << op.input().getType();
}

//===----------------------------------------------------------------------===//
// UnionCreateOp
//===----------------------------------------------------------------------===//

static ParseResult parseUnionCreateOp(OpAsmParser &parser,
                                      OperationState &result) {
  Type declOrAliasType;
  StringAttr field;
  OpAsmParser::OperandType input;
  llvm::SMLoc fieldLoc = parser.getCurrentLocation();

  if (parser.parseAttribute(field, "field", result.attributes) ||
      parser.parseComma() || parser.parseOperand(input) ||
      parser.parseOptionalAttrDict(result.attributes) ||
      parser.parseColonType(declOrAliasType))
    return failure();

  auto declType = type_dyn_cast<UnionType>(declOrAliasType);
  if (!declType)
    return parser.emitError(parser.getNameLoc(),
                            "expected !hw.union type or alias");

  Type inputType = declType.getFieldType(field.getValue());
  if (!inputType) {
    parser.emitError(fieldLoc, "cannot find union field '")
        << field.getValue() << '\'';
    return failure();
  }

  if (parser.resolveOperand(input, inputType, result.operands))
    return failure();
  result.addTypes({declOrAliasType});
  return success();
}

static void printUnionCreateOp(OpAsmPrinter &printer, hw::UnionCreateOp op) {
  printer << " \"" << op.field() << "\", ";
  printer.printOperand(op.input());
  printer.printOptionalAttrDict(op->getAttrs(), {"field"});
  printer << " : " << op.getType();
}

//===----------------------------------------------------------------------===//
// UnionExtractOp
//===----------------------------------------------------------------------===//

static ParseResult parseUnionExtractOp(OpAsmParser &parser,
                                       OperationState &result) {
  return parseExtractOp<UnionType>(parser, result);
}

static void printUnionExtractOp(OpAsmPrinter &printer, hw::UnionExtractOp op) {
  printExtractOp(printer, op);
}

//===----------------------------------------------------------------------===//
// ArrayGetOp
//===----------------------------------------------------------------------===//

void ArrayGetOp::build(OpBuilder &builder, OperationState &result, Value input,
                       Value index) {
  auto resultType = type_cast<ArrayType>(input.getType()).getElementType();
  build(builder, result, resultType, input, index);
}

//===----------------------------------------------------------------------===//
// TypedeclOp
//===----------------------------------------------------------------------===//

StringRef TypedeclOp::getPreferredName() {
  return verilogName().getValueOr(getName());
}

//===----------------------------------------------------------------------===//
// TableGen generated logic.
//===----------------------------------------------------------------------===//

// Provide the autogenerated implementation guts for the Op classes.
#define GET_OP_CLASSES
#include "circt/Dialect/HW/HW.cpp.inc"
