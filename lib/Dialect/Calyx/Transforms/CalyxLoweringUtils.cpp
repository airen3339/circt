//===- CalyxLoweringUtils.cpp - Calyx lowering utility methods --*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Various lowering utility methods converting to and from Calyx programs.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/Calyx/CalyxLoweringUtils.h"
#include "circt/Dialect/Calyx/CalyxHelpers.h"
#include "circt/Dialect/Calyx/CalyxOps.h"

#include <variant>

namespace circt {
namespace calyx {

MemoryInterface::MemoryInterface() {}
MemoryInterface::MemoryInterface(const MemoryPortsImpl &ports) : impl(ports) {}
MemoryInterface::MemoryInterface(calyx::MemoryOp memOp) : impl(memOp) {}

} // namespace calyx
} // namespace circt
