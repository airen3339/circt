//===- SV/IR/Dialect.h - SV dialect declaration -----------------*- C++ -*-===//
//
// This file defines an SV MLIR dialect.
//
//===----------------------------------------------------------------------===//

#ifndef CIRCT_DIALECT_SV_DIALECT_H
#define CIRCT_DIALECT_SV_DIALECT_H

#include "mlir/IR/Dialect.h"

namespace circt {
namespace sv {
using namespace mlir;

class SVDialect : public Dialect {
public:
  explicit SVDialect(MLIRContext *context);
  ~SVDialect();

  static StringRef getDialectNamespace() { return "sv"; }

  /// Parses a type registered to this dialect
  mlir::Type parseType(mlir::DialectAsmParser &parser) const override;

  /// Print a type registered to this dialect
  void printType(mlir::Type type,
                 mlir::DialectAsmPrinter &printer) const override;
};

} // namespace sv
} // namespace circt

#endif // CIRCT_DIALECT_SV_DIALECT_H
