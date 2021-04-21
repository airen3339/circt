//===- BackedgeBuilder.h - Support for building backedges -------*- C++ -*-===//
//
// Backedges are operations/values which have to exist as operands before
// they are produced in a result. Since it isn't clear how to build backedges
// in MLIR, these helper classes set up a canonical way to do so.
//
//===----------------------------------------------------------------------===//

#ifndef CIRCT_SUPPORT_BACKEDGEBUILDER_H
#define CIRCT_SUPPORT_BACKEDGEBUILDER_H

#include "mlir/IR/Location.h"
#include "mlir/IR/Value.h"
#include "llvm/ADT/SmallVector.h"

namespace mlir {
class PatternRewriter;
class Operation;
} // namespace mlir

namespace circt {

class Backedge;

/// Instantiate one of these and use it to build typed backedges. Backedges
/// which get used as operands must be assigned to with the actual value before
/// this class is destructed, usually at the end of a scope. It will check that
/// invariant then erase all the backedge ops during destruction.
///
/// Example use:
/// ```
///   circt::BackedgeBuilder back(rewriter, loc);
///   circt::Backedge ready = back.get(rewriter.getI1Type());
///   // Use `ready` as a `Value`.
///   auto addOp = rewriter.create<addOp>(loc, ready);
///   // When the actual value is available,
///   ready.set(anotherOp.getResult(0));
/// ```
class BackedgeBuilder {
  friend class Backedge;

public:
  /// To build a backedge op and manipulate it, we need a `PatternRewriter` and
  /// a `Location`. Store them during construct of this instance and use them
  /// when building.
  BackedgeBuilder(mlir::PatternRewriter &rewriter, mlir::Location loc);
  ~BackedgeBuilder();
  /// Create a typed backedge.
  Backedge get(mlir::Type resultType);

private:
  mlir::PatternRewriter &rewriter;
  mlir::Location loc;
  llvm::SmallVector<mlir::Operation *, 16> edges;
};

/// `Backedge` is a wrapper class around a `Value`. When assigned another
/// `Value`, it replaces all uses of itself with the new `Value` then become a
/// wrapper around the new `Value`.
class Backedge {
  friend class BackedgeBuilder;

  /// `Backedge` is constructed exclusively by `BackedgeBuilder`.
  Backedge(mlir::Operation *op);

public:
  operator mlir::Value();
  void setValue(mlir::Value);

private:
  mlir::Value value;
};

} // namespace circt

#endif // CIRCT_SUPPORT_BACKEDGEBUILDER_H
