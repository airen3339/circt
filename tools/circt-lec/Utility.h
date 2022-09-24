#ifndef LEC_UTILITY_H
#define LEC_UTILITY_H

#include "mlir/IR/Value.h"
#include "mlir/Support/IndentedOstream.h"
#include "llvm/ADT/APInt.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include <z3++.h>

namespace lec {
// Defining persistent output streams such that text will be printed in
// accordance with the globally set indentation level.
inline mlir::raw_indented_ostream dbgs(llvm::dbgs());
inline mlir::raw_indented_ostream errs(llvm::errs());
inline mlir::raw_indented_ostream outs(llvm::outs());

#define INDENT()                                                               \
  auto _indentDbgs = lec::dbgs.scope();                                        \
  auto _indentErrs = lec::errs.scope();                                        \
  auto _indentOuts = lec::outs.scope()

/// Helper function to provide a common debug formatting for z3 expressions.
inline void printExpr(const z3::expr &expr) {
  lec::dbgs << "symbol: " << expr.to_string() << "\n";
  lec::dbgs << "sort: " << expr.get_sort().to_string() << "\n";
  lec::dbgs << "expression id: " << expr.id() << "\n";
  lec::dbgs << "expression hash: " << expr.hash() << "\n";
}

/// Helper function to provide a common debug formatting for MLIR values.
inline void printValue(const mlir::Value &value) {
  lec::dbgs << "value: " << value << "\n";
  lec::dbgs << "type: " << value.getType() << "\n";
  lec::dbgs << "value hash: " << mlir::hash_value(value) << "\n";
}

/// Helper function to provide a common debug formatting for MLIR APInt'egers.
inline void printAPInt(const mlir::APInt &value) {
  lec::dbgs << "APInt: " << value.getZExtValue() << "\n";
}
} // namespace lec

// Grant access to command-line option values to users of this header.
extern bool verboseOpt;
extern bool statisticsOpt;

// This macro allows executing instructions only when the tool is invoked with
// the `verbose` command-line option set to true.
#define VERBOSE(X)                                                             \
  do {                                                                         \
    if (verboseOpt) {                                                          \
      X;                                                                       \
    }                                                                          \
  } while (false)

#endif // LEC_UTILITY_H
