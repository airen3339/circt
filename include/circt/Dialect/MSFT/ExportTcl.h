//===- ExportTcl.h - MSFT Tcl Exporters -------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Expose the Tcl exporters.
//
//===----------------------------------------------------------------------===//

#ifndef CIRCT_DIALECT_MSFT_EXPORTTCL_H
#define CIRCT_DIALECT_MSFT_EXPORTTCL_H

#include "circt/Dialect/HW/HWSymCache.h"
#include "circt/Dialect/MSFT/MSFTOpInterfaces.h"
#include "circt/Support/LLVM.h"
#include "llvm/ADT/StringRef.h"

namespace circt {
namespace msft {
class MSFTModuleOp;

/// Instantiate for all Tcl emissions. We want to cache the symbols and binned
/// ops -- this helper class provides that caching.
class TclEmitter {
public:
  TclEmitter(mlir::ModuleOp topLevel);
  LogicalResult emit(Operation *forMod, StringRef outputFile);

  Operation *getDefinition(FlatSymbolRefAttr);
  const DenseSet<hw::GlobalRefOp> &getRefsUsed() { return refsUsed; }
  void usedRef(hw::GlobalRefOp ref) { refsUsed.insert(ref); }

private:
  mlir::ModuleOp topLevel;

  bool populated;
  hw::HWSymbolCache topLevelSymbols;
  DenseMap<Operation *,
           DenseMap<StringAttr, SmallVector<DynInstDataOpInterface, 0>>>
      tclOpsForModInstance;
  DenseSet<hw::GlobalRefOp> refsUsed;

  LogicalResult populate();
};

} // namespace msft
} // namespace circt

#endif // CIRCT_DIALECT_MSFT_EXPORTTCL_H
