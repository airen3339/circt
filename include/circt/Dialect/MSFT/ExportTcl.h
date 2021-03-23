//===- ExportTcl.h - MSFT Tcl Exporters -------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Expose the TCL exporters.
//
//===----------------------------------------------------------------------===//

#ifndef CIRCT_DIALECT_MSFT_EXPORTTCL_H
#define CIRCT_DIALECT_MSFT_EXPORTTCL_H

namespace llvm {
class raw_ostream;
} // namespace llvm

namespace mlir {
struct LogicalResult;
class ModuleOp;
} // namespace mlir

namespace circt {
namespace msft {
/// Export TCL for a module.
mlir::LogicalResult exportQuartusTCL(mlir::ModuleOp module,
                                     llvm::raw_ostream &os);

/// Register the various TCL exports.
void registerMSFTTclTranslation();

} // namespace msft
} // namespace circt

#endif // CIRCT_DIALECT_MSFT_EXPORTTCL_H
