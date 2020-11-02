//===- RTLDialect.cpp - C Interface for RTL Dialect -----------------------===//
//
//===----------------------------------------------------------------------===//

#include "circt-c/RTLDialect.h"
#include "circt/Dialect/RTL/Ops.h"
#include "mlir-c/IR.h"
#include "mlir/CAPI/IR.h"
#include "mlir/CAPI/Support.h"

void mlirContextRegisterRTLDialect(MlirContext context) {
  unwrap(context)->getDialectRegistry().insert<circt::rtl::RTLDialect>();
}

MlirDialect mlirContextLoadRTLDialect(MlirContext context) {
  return wrap(unwrap(context)->getOrLoadDialect<circt::rtl::RTLDialect>());
}

MlirStringRef mlirRTLDialectGetNamespace() {
  return wrap(circt::rtl::RTLDialect::getDialectNamespace());
}
