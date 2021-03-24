//===- RTLDialect.cpp - C Interface EmitVerilog ---------------------------===//
//
//  Implements a C Interface for emitVerilog
//
//===----------------------------------------------------------------------===//

#include "circt-c/ExportVerilog.h"

#include "circt/Translation/ExportVerilog.h"
#include "mlir/CAPI/IR.h"
#include "mlir/CAPI/Support.h"
#include "mlir/CAPI/Utils.h"
#include "llvm/Support/raw_ostream.h"

using namespace circt;

MlirLogicalResult mlirExportVerilog(MlirModule module,
                                    MlirStringCallback callback,
                                    void *userData) {
  mlir::detail::CallbackOstream stream(callback, userData);
  return wrap(exportVerilog(unwrap(module), stream));
}
