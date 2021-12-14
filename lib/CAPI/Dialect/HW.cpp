//===- HW.cpp - C Interface for the HW Dialect ----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  Implements a C Interface for the HW Dialect
//
//===----------------------------------------------------------------------===//

#include "circt-c/Dialect/HW.h"
#include "circt/Dialect/HW/HWAttributes.h"
#include "circt/Dialect/HW/HWOps.h"
#include "circt/Dialect/HW/HWTypes.h"
#include "circt/Support/LLVM.h"
#include "mlir/CAPI/IR.h"
#include "mlir/CAPI/Registration.h"
#include "mlir/CAPI/Support.h"

using namespace circt;
using namespace circt::hw;

//===----------------------------------------------------------------------===//
// Dialect API.
//===----------------------------------------------------------------------===//

MLIR_DEFINE_CAPI_DIALECT_REGISTRATION(HW, hw, HWDialect)

//===----------------------------------------------------------------------===//
// Type API.
//===----------------------------------------------------------------------===//

int64_t hwGetBitWidth(MlirType type) { return getBitWidth(unwrap(type)); }

bool hwTypeIsAValueType(MlirType type) { return isHWValueType(unwrap(type)); }

bool hwTypeIsAArrayType(MlirType type) { return unwrap(type).isa<ArrayType>(); }

MlirType hwArrayTypeGet(MlirType element, size_t size) {
  return wrap(ArrayType::get(unwrap(element), size));
}

MlirType hwArrayTypeGetElementType(MlirType type) {
  return wrap(unwrap(type).cast<ArrayType>().getElementType());
}

intptr_t hwArrayTypeGetSize(MlirType type) {
  return unwrap(type).cast<ArrayType>().getSize();
}

MlirType hwInOutTypeGet(MlirType element) {
  return wrap(InOutType::get(unwrap(element)));
}

MlirType hwInOutTypeGetElementType(MlirType type) {
  return wrap(unwrap(type).cast<InOutType>().getElementType());
}

bool hwTypeIsAInOut(MlirType type) { return unwrap(type).isa<InOutType>(); }

bool hwTypeIsAStructType(MlirType type) {
  return unwrap(type).isa<StructType>();
}

MlirType hwStructTypeGet(MlirContext ctx, intptr_t numElements,
                         HWStructFieldInfo const *elements) {
  SmallVector<StructType::FieldInfo> fieldInfos;
  fieldInfos.reserve(numElements);
  for (intptr_t i = 0; i < numElements; ++i) {
    fieldInfos.push_back(StructType::FieldInfo{
        unwrap(elements[i].name).cast<StringAttr>(), unwrap(elements[i].type)});
  }
  return wrap(StructType::get(unwrap(ctx), fieldInfos));
}

MlirType hwStructTypeGetField(MlirType structType, MlirStringRef fieldName) {
  StructType st = unwrap(structType).cast<StructType>();
  return wrap(st.getFieldType(unwrap(fieldName)));
}

intptr_t hwStructTypeGetNumFields(MlirType structType) {
  StructType st = unwrap(structType).cast<StructType>();
  return st.getElements().size();
}

HWStructFieldInfo hwStructTypeGetFieldNum(MlirType structType, unsigned idx) {
  StructType st = unwrap(structType).cast<StructType>();
  auto cppField = st.getElements()[idx];
  HWStructFieldInfo ret;
  ret.name = wrap(cppField.name);
  ret.type = wrap(cppField.type);
  return ret;
}

bool hwTypeIsATypeAliasType(MlirType type) {
  return unwrap(type).isa<TypeAliasType>();
}

MlirType hwTypeAliasTypeGet(MlirStringRef cScope, MlirStringRef cName,
                            MlirType cInnerType) {
  StringRef scope = unwrap(cScope);
  StringRef name = unwrap(cName);
  Type innerType = unwrap(cInnerType);
  FlatSymbolRefAttr nameRef =
      FlatSymbolRefAttr::get(innerType.getContext(), name);
  SymbolRefAttr ref =
      SymbolRefAttr::get(innerType.getContext(), scope, {nameRef});
  return wrap(TypeAliasType::get(ref, innerType));
}

MlirType hwTypeAliasTypeGetCanonicalType(MlirType typeAlias) {
  TypeAliasType type = unwrap(typeAlias).cast<TypeAliasType>();
  return wrap(type.getCanonicalType());
}

MlirType hwTypeAliasTypeGetInnerType(MlirType typeAlias) {
  TypeAliasType type = unwrap(typeAlias).cast<TypeAliasType>();
  return wrap(type.getInnerType());
}

MlirStringRef hwTypeAliasTypeGetName(MlirType typeAlias) {
  TypeAliasType type = unwrap(typeAlias).cast<TypeAliasType>();
  return wrap(type.getRef().getLeafReference().getValue());
}

MlirStringRef hwTypeAliasTypeGetScope(MlirType typeAlias) {
  TypeAliasType type = unwrap(typeAlias).cast<TypeAliasType>();
  return wrap(type.getRef().getRootReference().getValue());
}

//===----------------------------------------------------------------------===//
// Attribute API.
//===----------------------------------------------------------------------===//

MLIR_CAPI_EXPORTED bool hwAttrIsAParamDeclAttr(MlirAttribute attr) {
  return unwrap(attr).isa<ParamDeclAttr>();
}
MLIR_CAPI_EXPORTED MlirAttribute hwParamDeclAttrGet(MlirStringRef cName,
                                                    MlirAttribute cType,
                                                    MlirAttribute cValue) {
  TypeAttr type = unwrap(cType).cast<TypeAttr>();
  auto name = StringAttr::get(type.getContext(), unwrap(cName));
  return wrap(
      ParamDeclAttr::get(type.getContext(), name, type, unwrap(cValue)));
}
MLIR_CAPI_EXPORTED MlirStringRef hwParamDeclAttrGetName(MlirAttribute decl) {
  return wrap(unwrap(decl).cast<ParamDeclAttr>().getName().getValue());
}
MLIR_CAPI_EXPORTED MlirAttribute hwParamDeclAttrGetType(MlirAttribute decl) {
  return wrap(unwrap(decl).cast<ParamDeclAttr>().getType());
}
MLIR_CAPI_EXPORTED MlirAttribute hwParamDeclAttrGetValue(MlirAttribute decl) {
  return wrap(unwrap(decl).cast<ParamDeclAttr>().getValue());
}

MLIR_CAPI_EXPORTED bool hwAttrIsAParamVerbatimAttr(MlirAttribute attr) {
  return unwrap(attr).isa<ParamVerbatimAttr>();
}
MLIR_CAPI_EXPORTED MlirAttribute hwParamVerbatimAttrGet(MlirAttribute text) {
  auto textAttr = unwrap(text).cast<StringAttr>();
  MLIRContext *ctx = textAttr.getContext();
  auto type = NoneType::get(ctx);
  return wrap(ParamVerbatimAttr::get(ctx, textAttr, type));
}
