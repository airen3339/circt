//===- HWTypeInterfaces.cpp - Implement HW type interfaces ------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements type interfaces of the HW Dialect.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/HW/HWTypeInterfaces.h"

using namespace mlir;
using namespace circt;
using namespace hw;
using namespace FieldIdImpl;

Type circt::hw::FieldIdImpl::getFinalTypeByFieldID(Type type,
                                                   uint64_t fieldID) {
  std::pair<Type, uint64_t> pair(type, fieldID);
  while (pair.second) {
    if (auto ftype = dyn_cast<FieldIDTypeInterface>(pair.first)) {
      pair = ftype.getSubTypeByFieldID(pair.second);
    } else {
      assert(0 && "fieldID indexing into a non-aggregate type");
      abort();
    }
  }
  return pair.first;
}

std::pair<Type, uint64_t>
circt::hw::FieldIdImpl::getSubTypeByFieldID(Type type, uint64_t fieldID) {
  if (!fieldID)
    return {type, 0};
  if (auto ftype = dyn_cast<FieldIDTypeInterface>(type))
    return ftype.getSubTypeByFieldID(fieldID);

  assert(0 && "fieldID indexing into a non-aggregate type");
  abort();
}

uint64_t circt::hw::FieldIdImpl::getMaxFieldID(Type type) {
  if (auto ftype = dyn_cast<FieldIDTypeInterface>(type))
    return ftype.getMaxFieldID();
  return 0;
}

std::pair<uint64_t, bool>
circt::hw::FieldIdImpl::rootChildFieldID(Type type, uint64_t fieldID,
                                         uint64_t index) {
  if (auto ftype = dyn_cast<FieldIDTypeInterface>(type))
    return ftype.rootChildFieldID(fieldID, index);
  return {0, fieldID == 0};
}

#include "circt/Dialect/HW/HWTypeInterfaces.cpp.inc"
