//===- PassDetails.h - Seq pass class details -----------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Contains the stuff shared between the different Seq passes.
//
//===----------------------------------------------------------------------===//

// clang-tidy seems to expect the absolute path in the
// header guard on some systems, so just disable it.
// NOLINTNEXTLINE(llvm-header-guard)
#ifndef DIALECT_SEQ_TRANSFORMS_PASSDETAILS_H
#define DIALECT_SEQ_TRANSFORMS_PASSDETAILS_H

#include "circt/Dialect/Seq/SeqOps.h"
#include "mlir/Pass/Pass.h"

namespace circt {
namespace seq {

#define GEN_PASS_CLASSES
#include "circt/Dialect/Seq/SeqPasses.h.inc"

} // namespace seq
} // namespace circt

#endif // DIALECT_SEQ_TRANSFORMS_PASSDETAILS_H
