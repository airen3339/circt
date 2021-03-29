//===- FIRRTLFolds.cpp - Implement folds and canonicalizations for ops ----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implement the folding and canonicalizations for FIRRTL ops.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/FIRRTL/FIRRTLOps.h"
#include "circt/Support/LLVM.h"
#include "mlir/Dialect/CommonFolders.h"
#include "mlir/IR/Matchers.h"
#include "mlir/IR/PatternMatch.h"

// Declarative canonicalization patterns
namespace circt {
namespace firrtl {
namespace patterns {
#include "circt/Dialect/FIRRTL/Canonicalization.h.inc"
} // namespace patterns
} // namespace firrtl
} // namespace circt

using namespace circt;
using namespace firrtl;

using mlir::constFoldBinaryOp;

static Attribute getIntAttr(const APInt &value, MLIRContext *context) {
  return IntegerAttr::get(IntegerType::get(context, value.getBitWidth()),
                          value);
}

namespace {
struct ConstantIntMatcher {
  APInt &value;
  ConstantIntMatcher(APInt &value) : value(value) {}
  bool match(Operation *op) {
    if (auto cst = dyn_cast<ConstantOp>(op)) {
      value = cst.value();
      return true;
    }
    return false;
  }
};
} // end anonymous namespace

static inline ConstantIntMatcher m_FConstant(APInt &value) {
  return ConstantIntMatcher(value);
}

// TODO: Should move to MLIR upstream.
template <typename OpType>
static void
addCanonicalizer(RewritePatternSet &results, MLIRContext *context,
                 LogicalResult (*implFn)(OpType, PatternRewriter &rewriter)) {
  // std::function<LogicalResult(OpType, PatternRewriter &rewriter)> implFn) {
  struct Folder final : public OpRewritePattern<OpType> {
    LogicalResult (*implFn)(OpType, PatternRewriter &rewriter);

    Folder(LogicalResult (*implFn)(OpType, PatternRewriter &rewriter),
           MLIRContext *context)
        : OpRewritePattern<OpType>(context), implFn(implFn) {}

    LogicalResult matchAndRewrite(OpType op,
                                  PatternRewriter &rewriter) const override {
      return implFn(op, rewriter);
    }
  };

  results.insert(std::make_unique<Folder>(std::move(implFn), context));
}

template <typename OpType>
static void addCanonicalizerMethod(RewritePatternSet &results,
                                   MLIRContext *context) {
  struct Folder final : public OpRewritePattern<OpType> {
    using OpRewritePattern<OpType>::OpRewritePattern;

    LogicalResult matchAndRewrite(OpType op,
                                  PatternRewriter &rewriter) const override {
      return OpType::canonicalize(op, rewriter);
    }
  };
  results.insert<Folder>(context);
}

//===----------------------------------------------------------------------===//
// Fold Hooks
//===----------------------------------------------------------------------===//

OpFoldResult ConstantOp::fold(ArrayRef<Attribute> operands) {
  assert(operands.empty() && "constant has no operands");
  return valueAttr();
}

//===----------------------------------------------------------------------===//
// Binary Operators
//===----------------------------------------------------------------------===//

OpFoldResult DivPrimOp::fold(ArrayRef<Attribute> operands) {
  APInt value;

  /// div(x, x) -> 1
  ///
  /// Division by zero is undefined in the FIRRTL specification. This
  /// fold exploits that fact to optimize self division to one.
  if (lhs() == rhs()) {
    auto width = getType().getWidthOrSentinel();
    if (width == -1)
      width = 2;
    if (width != 0)
      return IntegerAttr::get(IntegerType::get(getContext(), width), 1);
  }

  /// div(x, 1) -> x : (uint, uint) -> uint
  ///
  /// UInt division by one returns the numerator. SInt division can't
  /// be folded here because it increases the return type bitwidth by
  /// one and requires sign extension (a new op).
  if (matchPattern(rhs(), m_FConstant(value)) && value.isOneValue() &&
      lhs().getType() == getType())
    return lhs();

  return {};
}

// TODO: Move to DRR.
OpFoldResult AndPrimOp::fold(ArrayRef<Attribute> operands) {
  APInt value;

  /// and(x, 0) -> 0
  if (matchPattern(rhs(), m_FConstant(value)) && value.isNullValue() &&
      rhs().getType() == getType())
    return rhs();

  /// and(x, -1) -> x
  if (matchPattern(rhs(), m_FConstant(value)) && value.isAllOnesValue() &&
      lhs().getType() == getType() && rhs().getType() == getType())
    return lhs();

  /// and(x, x) -> x
  if (lhs() == rhs() && rhs().getType() == getType())
    return rhs();

  return constFoldBinaryOp<IntegerAttr>(operands,
                                        [](APInt a, APInt b) { return a & b; });
}

OpFoldResult OrPrimOp::fold(ArrayRef<Attribute> operands) {
  APInt value;

  /// or(x, 0) -> x
  if (matchPattern(rhs(), m_FConstant(value)) && value.isNullValue() &&
      lhs().getType() == getType())
    return lhs();

  /// or(x, -1) -> -1
  if (matchPattern(rhs(), m_FConstant(value)) && value.isAllOnesValue() &&
      rhs().getType() == getType() && lhs().getType() == getType())
    return rhs();

  /// or(x, x) -> x
  if (lhs() == rhs() && rhs().getType() == getType())
    return rhs();

  return constFoldBinaryOp<IntegerAttr>(operands,
                                        [](APInt a, APInt b) { return a | b; });
}

OpFoldResult XorPrimOp::fold(ArrayRef<Attribute> operands) {
  APInt value;

  /// xor(x, 0) -> x
  if (matchPattern(rhs(), m_FConstant(value)) && value.isNullValue() &&
      lhs().getType() == getType())
    return lhs();

  /// xor(x, x) -> 0
  if (lhs() == rhs()) {
    auto width = abs(getType().getWidthOrSentinel());
    if (width != 0) // We cannot create a zero bit APInt.
      return getIntAttr(APInt(width, 0), getContext());
  }

  return constFoldBinaryOp<IntegerAttr>(operands,
                                        [](APInt a, APInt b) { return a ^ b; });
}

void LEQPrimOp::getCanonicalizationPatterns(OwningRewritePatternList &results,
                                            MLIRContext *context) {
  results.insert<patterns::LEQWithConstLHS>(context);
}

void LTPrimOp::getCanonicalizationPatterns(OwningRewritePatternList &results,
                                           MLIRContext *context) {
  results.insert<patterns::LTWithConstLHS>(context);
}

void GEQPrimOp::getCanonicalizationPatterns(OwningRewritePatternList &results,
                                            MLIRContext *context) {
  results.insert<patterns::GEQWithConstLHS>(context);
}

void GTPrimOp::getCanonicalizationPatterns(OwningRewritePatternList &results,
                                           MLIRContext *context) {
  results.insert<patterns::GTWithConstLHS>(context);
}

OpFoldResult EQPrimOp::fold(ArrayRef<Attribute> operands) {
  APInt value;

  if (matchPattern(rhs(), m_FConstant(value))) {
    APInt lhsCst;
    // Constant fold.
    if (matchPattern(lhs(), m_FConstant(lhsCst)) &&
        value.getBitWidth() == lhsCst.getBitWidth()) {
      return getIntAttr(APInt(1, value == lhsCst), getContext());
    }

    /// eq(x, 1) -> x when x is 1 bit.
    /// TODO: Support SInt<1> on the LHS etc.
    if (value.isAllOnesValue() && lhs().getType() == getType() &&
        rhs().getType() == getType())
      return lhs();

    /// TODO: eq(x, 0) -> not(x) when x is 1 bit.
    /// TODO: eq(x, 0) -> not(orr(x)) when x is >1 bit
    /// TODO: eq(x, ~0) -> andr(x)) when x is >1 bit
  }

  return {};
}

OpFoldResult NEQPrimOp::fold(ArrayRef<Attribute> operands) {
  APInt value;

  if (matchPattern(rhs(), m_FConstant(value))) {
    APInt lhsCst;
    // Constant fold.
    if (matchPattern(lhs(), m_FConstant(lhsCst)) &&
        value.getBitWidth() == lhsCst.getBitWidth()) {
      return getIntAttr(APInt(1, value != lhsCst), getContext());
    }

    /// neq(x, 0) -> x when x is 1 bit.
    /// TODO: Support SInt<1> on the LHS etc.
    if (value.isNullValue() && lhs().getType() == getType() &&
        rhs().getType() == getType())
      return lhs();

    /// TODO: neq(x, 0) -> not(orr(x)) when x is >1 bit
    /// TODO: neq(x, 1) -> not(x) when x is 1 bit.
    /// TODO: neq(x, ~0) -> andr(x)) when x is >1 bit
  }

  return {};
}

//===----------------------------------------------------------------------===//
// Unary Operators
//===----------------------------------------------------------------------===//

OpFoldResult AsSIntPrimOp::fold(ArrayRef<Attribute> operands) {
  if (auto attr = operands[0].dyn_cast_or_null<IntegerAttr>())
    return getIntAttr(attr.getValue(), getContext());
  return {};
}

OpFoldResult AsUIntPrimOp::fold(ArrayRef<Attribute> operands) {
  if (auto attr = operands[0].dyn_cast_or_null<IntegerAttr>())
    return getIntAttr(attr.getValue(), getContext());
  return {};
}

//===----------------------------------------------------------------------===//
// Other Operators
//===----------------------------------------------------------------------===//

static LogicalResult canonicalize(CatPrimOp op, PatternRewriter &rewriter) {
  // cat(bits(x, ...), bits(x, ...)) -> bits(x ...) when the two ...'s are
  // consequtive in the input.
  if (auto lhsBits = dyn_cast_or_null<BitsPrimOp>(op.lhs().getDefiningOp())) {
    if (auto rhsBits = dyn_cast_or_null<BitsPrimOp>(op.rhs().getDefiningOp())) {
      if (lhsBits.input() == rhsBits.input() &&
          lhsBits.lo() - 1 == rhsBits.hi()) {
        rewriter.replaceOpWithNewOp<BitsPrimOp>(
            op, op.getType(), lhsBits.input(), lhsBits.hi(), rhsBits.lo());
        return success();
      }
    }
  }
  return failure();
}

void CatPrimOp::getCanonicalizationPatterns(RewritePatternSet &results,
                                            MLIRContext *context) {
  addCanonicalizer<CatPrimOp>(results, context, canonicalize);
}

OpFoldResult BitsPrimOp::fold(ArrayRef<Attribute> operands) {
  auto inputType = input().getType().cast<FIRRTLType>();
  // If we are extracting the entire input, then return it.
  if (inputType == getType() &&
      inputType.cast<IntType>().getWidthOrSentinel() != -1)
    return input();

  // Constant fold.
  APInt value;
  if (inputType.cast<IntType>().hasWidth() &&
      matchPattern(input(), m_FConstant(value)))
    return getIntAttr(value.lshr(lo()).truncOrSelf(hi() - lo() + 1),
                      getContext());

  return {};
}

static LogicalResult canonicalize(BitsPrimOp op, PatternRewriter &rewriter) {
  auto inputOp = op.input().getDefiningOp();
  // bits(bits(x, ...), ...) -> bits(x, ...).
  if (auto innerBits = dyn_cast_or_null<BitsPrimOp>(inputOp)) {
    auto newLo = op.lo() + innerBits.lo();
    auto newHi = newLo + op.hi() - op.lo();
    rewriter.replaceOpWithNewOp<BitsPrimOp>(op, innerBits.input(), newHi,
                                            newLo);
    return success();
  }
  return failure();
}

void BitsPrimOp::getCanonicalizationPatterns(RewritePatternSet &results,
                                             MLIRContext *context) {
  addCanonicalizer<BitsPrimOp>(results, context, canonicalize);
}

/// Replace the specified operation with a 'bits' op from the specified hi/lo
/// bits.  Insert a cast to handle the case where the original operation
/// returned a signed integer.
static void replaceWithBits(Operation *op, Value value, unsigned hiBit,
                            unsigned loBit, PatternRewriter &rewriter) {
  auto resType = op->getResult(0).getType().cast<IntType>();
  if (value.getType().cast<IntType>().getWidth() != resType.getWidth())
    value = rewriter.create<BitsPrimOp>(op->getLoc(), value, hiBit, loBit);

  if (resType.isSigned() && !value.getType().cast<IntType>().isSigned()) {
    value = rewriter.createOrFold<AsSIntPrimOp>(op->getLoc(), resType, value);
  } else if (resType.isUnsigned() &&
             !value.getType().cast<IntType>().isUnsigned()) {
    value = rewriter.createOrFold<AsUIntPrimOp>(op->getLoc(), resType, value);
  }
  rewriter.replaceOp(op, value);
}

static LogicalResult canonicalize(HeadPrimOp op, PatternRewriter &rewriter) {
  auto inputWidth = op.input().getType().cast<IntType>().getWidthOrSentinel();
  if (inputWidth == -1)
    return failure();

  // If we know the input width, we can canonicalize this into a BitsPrimOp.
  unsigned keepAmount = op.amount();
  if (keepAmount)
    replaceWithBits(op, op.input(), inputWidth - 1, inputWidth - keepAmount,
                    rewriter);
  return success();
}

void HeadPrimOp::getCanonicalizationPatterns(RewritePatternSet &results,
                                             MLIRContext *context) {
  addCanonicalizer<HeadPrimOp>(results, context, canonicalize);
}

OpFoldResult MuxPrimOp::fold(ArrayRef<Attribute> operands) {
  APInt value;

  /// mux(0/1, x, y) -> x or y
  if (matchPattern(sel(), m_FConstant(value))) {
    if (value.isNullValue() && low().getType() == getType())
      return low();
    if (!value.isNullValue() && high().getType() == getType())
      return high();
  }

  // mux(cond, x, x) -> x
  if (high() == low())
    return high();

  // mux(cond, x, cst)
  if (matchPattern(low(), m_FConstant(value))) {
    APInt c1;
    // mux(cond, c1, c2)
    if (matchPattern(high(), m_FConstant(c1))) {
      // mux(cond, 1, 0) -> cond
      if (c1.isOneValue() && value.isNullValue() &&
          getType() == sel().getType())
        return sel();

      // TODO: x ? ~0 : 0 -> sext(x)
      // TODO: "x ? c1 : c2" -> many tricks
    }
    // TODO: "x ? a : 0" -> sext(x) & a
  }

  // TODO: "x ? c1 : y" -> "~x ? y : c1"

  return {};
}

OpFoldResult PadPrimOp::fold(ArrayRef<Attribute> operands) {
  auto input = this->input();

  // pad(x) -> x  if the width doesn't change.
  if (input.getType() == getType())
    return input;

  // Need to know the input width.
  auto inputType = input.getType().cast<IntType>();
  int32_t width = inputType.getWidthOrSentinel();
  if (width == -1)
    return {};

  // Constant fold.
  APInt value;
  if (matchPattern(input, m_FConstant(value))) {
    auto destWidth = getType().getWidthOrSentinel();
    if (destWidth == -1)
      return {};

    if (inputType.isSigned())
      return getIntAttr(value.sext(destWidth), getContext());
    return getIntAttr(value.zext(destWidth), getContext());
  }

  return {};
}

OpFoldResult ShlPrimOp::fold(ArrayRef<Attribute> operands) {
  auto input = this->input();
  auto inputType = input.getType().cast<IntType>();
  int shiftAmount = amount();

  // shl(x, 0) -> x
  if (shiftAmount == 0)
    return input;

  // Constant fold.
  APInt value;
  if (matchPattern(input, m_FConstant(value))) {
    auto inputWidth = inputType.getWidthOrSentinel();
    if (inputWidth != -1) {
      auto resultWidth = inputWidth + shiftAmount;
      shiftAmount = std::min(shiftAmount, resultWidth);
      return getIntAttr(value.zext(resultWidth).shl(shiftAmount), getContext());
    }
  }
  return {};
}

OpFoldResult ShrPrimOp::fold(ArrayRef<Attribute> operands) {
  auto input = this->input();
  auto inputType = input.getType().cast<IntType>();
  int shiftAmount = amount();

  // shl(x, 0) -> x
  if (shiftAmount == 0)
    return input;

  auto inputWidth = inputType.getWidthOrSentinel();
  if (inputWidth == -1)
    return {};

  // shr(x, cst) where cst is all of x's bits and x is unsigned is 0.
  // If x is signed, it is the sign bit.
  if (shiftAmount >= inputWidth && inputType.isUnsigned())
    return getIntAttr(APInt(1, 0), getContext());

  // Constant fold.
  APInt value;
  if (matchPattern(input, m_FConstant(value))) {
    if (!inputType.isSigned())
      value = value.lshr(std::min(shiftAmount, inputWidth));
    else
      value = value.ashr(std::min(shiftAmount, inputWidth - 1));
    auto resultWidth = std::max(inputWidth - shiftAmount, 1);
    return getIntAttr(value.truncOrSelf(resultWidth), getContext());
  }
  return {};
}

static LogicalResult canonicalize(ShrPrimOp op, PatternRewriter &rewriter) {
  auto inputWidth = op.input().getType().cast<IntType>().getWidthOrSentinel();
  if (inputWidth == -1)
    return failure();

  // If we know the input width, we can canonicalize this into a BitsPrimOp.
  unsigned shiftAmount = op.amount();
  if (int(shiftAmount) >= inputWidth) {
    // shift(x, 32) => 0 when x has 32 bits.  This is handled by fold().
    if (op.getType().isUnsigned())
      return failure();

    // Shifting a signed value by the full width is actually taking the
    // sign bit. If the shift amount is greater than the input width, it
    // is equivalent to shifting by the input width.
    shiftAmount = inputWidth - 1;
  }

  replaceWithBits(op, op.input(), inputWidth - 1, shiftAmount, rewriter);
  return success();
}

void ShrPrimOp::getCanonicalizationPatterns(RewritePatternSet &results,
                                            MLIRContext *context) {
  addCanonicalizer<ShrPrimOp>(results, context, canonicalize);
}

static LogicalResult canonicalize(TailPrimOp op, PatternRewriter &rewriter) {
  auto inputWidth = op.input().getType().cast<IntType>().getWidthOrSentinel();
  if (inputWidth == -1)
    return failure();

  // If we know the input width, we can canonicalize this into a BitsPrimOp.
  unsigned dropAmount = op.amount();
  if (dropAmount != unsigned(inputWidth))
    replaceWithBits(op, op.input(), inputWidth - dropAmount - 1, 0, rewriter);
  return success();
}

void TailPrimOp::getCanonicalizationPatterns(RewritePatternSet &results,
                                             MLIRContext *context) {
  addCanonicalizer<TailPrimOp>(results, context, canonicalize);
}

//===----------------------------------------------------------------------===//
// Declarations
//===----------------------------------------------------------------------===//

/// Scan all the uses of the specified value, checking to see if there is
/// exactly one connect that sets the value as its destination.  This returns
/// the operation if found and if all the other users are "reads" from the
/// value.
static bool isOnlyConnectToValue(ConnectOp connect, Value value) {
  for (Operation *user : value.getUsers()) {
    // If we see a partial connect or attach, just conservatively fail.
    if (isa<PartialConnectOp>(user) || isa<AttachOp>(user))
      return {};

    if (auto aConnect = dyn_cast<ConnectOp>(user)) {
      if (aConnect.dest() == value && aConnect != connect)
        return false;
    }
  }
  return true;
}

// Forward simple values through wire's and reg's.
static LogicalResult foldSingleSetConnect(ConnectOp op,
                                          PatternRewriter &rewriter) {
  //
  // While we can do this for nearly all wires, we currently limit it to simple
  // things.
  Operation *connectedDecl = op.dest().getDefiningOp();
  if (!connectedDecl)
    return failure();

  // Only support wire and reg for now.
  if (!isa<WireOp>(connectedDecl) && !isa<RegOp>(connectedDecl))
    return failure();

  // Only forward if the types exactly match and there is one connect.
  if (op.dest().getType() != op.src().getType() ||
      !isOnlyConnectToValue(op, op.dest()))
    return failure();

  // Only do this if the connectee and the declaration are in the same block.
  auto *declBlock = connectedDecl->getBlock();
  auto *srcValueOp = op.src().getDefiningOp();
  if (!srcValueOp) {
    // Ports are ok for wires but not registers.
    if (!isa<WireOp>(connectedDecl))
      return failure();

  } else {
    // Constants/invalids in the same block are ok to forward, even through
    // reg's since the clocking doesn't matter for constants.
    if (!isa<ConstantOp>(srcValueOp) && !isa<InvalidValuePrimOp>(srcValueOp))
      return failure();
    if (srcValueOp->getBlock() != declBlock)
      return failure();
  }

  // Ok, we know we are doing the transformation.

  // Make sure the constant dominates all users.
  if (srcValueOp && srcValueOp != &declBlock->front())
    srcValueOp->moveBefore(&declBlock->front());

  // Remove the connect.
  rewriter.eraseOp(op);

  // Replace all things *using* the decl with the constant/port, and
  // remove the declaration.
  rewriter.replaceOp(connectedDecl, op.src());
  return success();
}

static LogicalResult canonicalize(ConnectOp op, PatternRewriter &rewriter) {
  // TODO: Canonicalize towards explicit extensions and flips here.

  // If there is a simple value connected to a foldable decl like a wire or reg,
  // see if we can eliminate the decl.
  if (succeeded(foldSingleSetConnect(op, rewriter)))
    return success();

  return failure();
}

void ConnectOp::getCanonicalizationPatterns(RewritePatternSet &results,
                                            MLIRContext *context) {
  addCanonicalizer<ConnectOp>(results, context, canonicalize);
}

//===----------------------------------------------------------------------===//
// Conversions
//===----------------------------------------------------------------------===//

OpFoldResult StdIntCastOp::fold(ArrayRef<Attribute> operands) {
  if (auto castInput =
          dyn_cast_or_null<StdIntCastOp>(getOperand().getDefiningOp()))
    if (castInput.getOperand().getType() == getType())
      return castInput.getOperand();

  return {};
}

OpFoldResult AnalogInOutCastOp::fold(ArrayRef<Attribute> operands) {
  if (auto castInput =
          dyn_cast_or_null<AnalogInOutCastOp>(getOperand().getDefiningOp()))
    if (castInput.getOperand().getType() == getType())
      return castInput.getOperand();

  return {};
}

OpFoldResult AsPassivePrimOp::fold(ArrayRef<Attribute> operands) {
  // If the input is already passive, then we don't need a conversion.
  if (getOperand().getType() == getType())
    return getOperand();

  if (auto castInput =
          dyn_cast_or_null<AsNonPassivePrimOp>(getOperand().getDefiningOp()))
    if (castInput.getOperand().getType() == getType())
      return castInput.getOperand();

  return {};
}

OpFoldResult AsNonPassivePrimOp::fold(ArrayRef<Attribute> operands) {
  if (auto castInput =
          dyn_cast_or_null<AsPassivePrimOp>(getOperand().getDefiningOp()))
    if (castInput.getOperand().getType() == getType())
      return castInput.getOperand();

  return {};
}

//===----------------------------------------------------------------------===//
// Statements
//===----------------------------------------------------------------------===//

/// If the specified value has an AttachOp user strictly dominating by
/// "dominatingAttach" then return it.
static AttachOp getDominatingAttachUser(Value value, AttachOp dominatedAttach) {
  for (auto *user : value.getUsers()) {
    auto attach = dyn_cast<AttachOp>(user);
    if (!attach || attach == dominatedAttach)
      continue;
    if (attach->isBeforeInBlock(dominatedAttach))
      return attach;
  }
  return {};
}

LogicalResult AttachOp::canonicalize(AttachOp op, PatternRewriter &rewriter) {
  // Single operand attaches are a noop.
  if (op.getNumOperands() <= 1) {
    rewriter.eraseOp(op);
    return success();
  }

  for (auto operand : op.getOperands()) {
    // Check to see if any of our operands has other attaches to it:
    //    attach x, y
    //      ...
    //    attach x, z
    // If so, we can merge these into "attach x, y, z".
    if (auto attach = getDominatingAttachUser(operand, op)) {
      SmallVector<Value> newOperands(op.getOperands());
      for (auto newOperand : attach.getOperands())
        if (newOperand != operand) // Don't add operand twice.
          newOperands.push_back(newOperand);
      rewriter.create<AttachOp>(op->getLoc(), newOperands);
      rewriter.eraseOp(attach);
      rewriter.eraseOp(op);
      return success();
    }

    // If this wire is *only* used by an attach then we can just delete
    // it.
    // TODO: May need to be sensitive to "don't touch" or other
    // annotations.
    if (auto wire = dyn_cast_or_null<WireOp>(operand.getDefiningOp())) {
      if (wire->hasOneUse()) {
        SmallVector<Value> newOperands;
        for (auto newOperand : op.getOperands())
          if (newOperand != operand) // Don't the add wire.
            newOperands.push_back(newOperand);

        rewriter.create<AttachOp>(op->getLoc(), newOperands);
        rewriter.eraseOp(op);
        rewriter.eraseOp(wire);
        return success();
      }
    }
  }
  return failure();
}

void AttachOp::getCanonicalizationPatterns(RewritePatternSet &results,
                                           MLIRContext *context) {
  addCanonicalizer<AttachOp>(results, context, canonicalize);
}

LogicalResult PartialConnectOp::canonicalize(PartialConnectOp op,
                                             PatternRewriter &rewriter) {
  // If a partial connect exists from a longer int to a shorter int, simplify
  // to a truncation and connect.
  auto destType =
      op.getOperand(0).getType().cast<FIRRTLType>().getPassiveType();
  auto srcType = op.getOperand(1).getType().cast<FIRRTLType>();
  if (destType == srcType)
    return failure();

  auto srcWidth = srcType.getBitWidthOrSentinel();
  auto destWidth = destType.getBitWidthOrSentinel();

  if (destType.isa<IntType>() && srcType.isa<IntType>() && srcWidth > 0 &&
      destWidth > 0 && destWidth < srcWidth) {
    auto shortened = rewriter.createOrFold<TailPrimOp>(
        op.getLoc(), destType, op.getOperand(1), srcWidth - destWidth);
    rewriter.create<ConnectOp>(op.getLoc(), op.getOperand(0), shortened);
    rewriter.eraseOp(op);
    return success();
  }
  return failure();
}

void PartialConnectOp::getCanonicalizationPatterns(RewritePatternSet &results,
                                                   MLIRContext *context) {
  addCanonicalizerMethod<PartialConnectOp>(results, context);
}
