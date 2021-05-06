//===- RTLOps.cpp - Implement the RTL operations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implement the RTL ops.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/Comb/CombOps.h"
#include "circt/Dialect/RTL/RTLOps.h"
#include "mlir/Dialect/CommonFolders.h"
#include "mlir/IR/Matchers.h"
#include "mlir/IR/PatternMatch.h"

using namespace mlir;
using namespace circt;
using namespace comb;

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
    if (auto cst = dyn_cast<rtl::ConstantOp>(op)) {
      value = cst.value();
      return true;
    }
    return false;
  }
};
} // end anonymous namespace

static inline ConstantIntMatcher m_RConstant(APInt &value) {
  return ConstantIntMatcher(value);
}

/// Flattens a single input in `op` if `hasOneUse` is true and it can be defined
/// as an Op. Returns true if successful, and false otherwise.
///
/// Example: op(1, 2, op(3, 4), 5) -> op(1, 2, 3, 4, 5)  // returns true
///
template <typename Op>
static bool tryFlatteningOperands(Op op, PatternRewriter &rewriter) {
  auto inputs = op.inputs();

  for (size_t i = 0, size = inputs.size(); i != size; ++i) {
    // Don't duplicate logic.
    if (!inputs[i].hasOneUse())
      continue;
    auto flattenOp = inputs[i].template getDefiningOp<Op>();
    if (!flattenOp)
      continue;
    auto flattenOpInputs = flattenOp.inputs();

    SmallVector<Value, 4> newOperands;
    newOperands.reserve(size + flattenOpInputs.size());

    auto flattenOpIndex = inputs.begin() + i;
    newOperands.append(inputs.begin(), flattenOpIndex);
    newOperands.append(flattenOpInputs.begin(), flattenOpInputs.end());
    newOperands.append(flattenOpIndex + 1, inputs.end());

    rewriter.replaceOpWithNewOp<Op>(op, op.getType(), newOperands);
    return true;
  }
  return false;
}

//===----------------------------------------------------------------------===//
// Unary Operations
//===----------------------------------------------------------------------===//

OpFoldResult SExtOp::fold(ArrayRef<Attribute> constants) {
  // Constant fold.
  if (auto input = constants[0].dyn_cast_or_null<IntegerAttr>()) {
    auto destWidth = getType().getWidth();
    return getIntAttr(input.getValue().sext(destWidth), getContext());
  }

  if (getType().getWidth() == input().getType().cast<IntegerType>().getWidth())
    return input();

  return {};
}

OpFoldResult ParityOp::fold(ArrayRef<Attribute> constants) {
  // Constant fold.
  if (auto input = constants[0].dyn_cast_or_null<IntegerAttr>())
    return getIntAttr(APInt(1, input.getValue().countPopulation() & 1),
                      getContext());

  return {};
}

//===----------------------------------------------------------------------===//
// Binary Operations
//===----------------------------------------------------------------------===//

OpFoldResult ShlOp::fold(ArrayRef<Attribute> operands) {
  return constFoldBinaryOp<IntegerAttr>(
      operands, [](APInt a, APInt b) { return a.shl(b); });
}

OpFoldResult ShrUOp::fold(ArrayRef<Attribute> operands) {
  return constFoldBinaryOp<IntegerAttr>(
      operands, [](APInt a, APInt b) { return a.lshr(b); });
}

OpFoldResult ShrSOp::fold(ArrayRef<Attribute> operands) {
  return constFoldBinaryOp<IntegerAttr>(
      operands, [](APInt a, APInt b) { return a.ashr(b); });
}

//===----------------------------------------------------------------------===//
// Other Operations
//===----------------------------------------------------------------------===//

OpFoldResult ExtractOp::fold(ArrayRef<Attribute> constants) {
  // If we are extracting the entire input, then return it.
  if (input().getType() == getType())
    return input();

  // Constant fold.
  if (auto input = constants[0].dyn_cast_or_null<IntegerAttr>()) {
    unsigned dstWidth = getType().getWidth();
    return getIntAttr(input.getValue().lshr(lowBit()).trunc(dstWidth),
                      getContext());
  }
  return {};
}

//===----------------------------------------------------------------------===//
// Variadic operations
//===----------------------------------------------------------------------===//

// Reduce all operands to a single value by applying the `calculate` function.
// This will fail if any of the operands are not constant.
template <class AttrElementT,
          class ElementValueT = typename AttrElementT::ValueType,
          class CalculationT =
              function_ref<ElementValueT(ElementValueT, ElementValueT)>>
static Attribute constFoldVariadicOp(ArrayRef<Attribute> operands,
                                     const CalculationT &calculate) {
  if (!operands.size())
    return {};

  if (!operands[0])
    return {};

  ElementValueT accum = operands[0].cast<AttrElementT>().getValue();
  for (auto i = operands.begin() + 1, end = operands.end(); i != end; ++i) {
    auto attr = *i;
    if (!attr)
      return {};

    auto typedAttr = attr.cast<AttrElementT>();
    calculate(accum, typedAttr.getValue());
  }
  return AttrElementT::get(operands[0].getType(), accum);
}

OpFoldResult AndOp::fold(ArrayRef<Attribute> constants) {
  APInt value = APInt::getAllOnesValue(getType().getWidth());

  // and(x, 01, 10) -> 00 -- annulment.
  for (auto operand : constants) {
    if (!operand)
      continue;
    value &= operand.cast<IntegerAttr>().getValue();
    if (value.isNullValue())
      return getIntAttr(value, getContext());
  }

  // and(x, -1) -> x.
  if (constants.size() == 2 && constants[1] &&
      constants[1].cast<IntegerAttr>().getValue().isAllOnesValue())
    return inputs()[0];

  // and(x, x, x) -> x.  This also handles and(x) -> x.
  if (llvm::all_of(inputs(), [&](auto in) { return in == this->inputs()[0]; }))
    return inputs()[0];

  // Constant fold
  return constFoldVariadicOp<IntegerAttr>(
      constants, [](APInt &a, const APInt &b) { a &= b; });
}

LogicalResult AndOp::canonicalize(AndOp op, PatternRewriter &rewriter) {
  auto inputs = op.inputs();
  auto size = inputs.size();
  assert(size > 1 && "expected 2 or more operands, `fold` should handle this");

  // TODO: remove all duplicate arguments
  // and(..., x, x) -> and(..., x) -- idempotent
  if (inputs[size - 1] == inputs[size - 2]) {
    rewriter.replaceOpWithNewOp<AndOp>(op, op.getType(), inputs.drop_back());
    return success();
  }

  // Patterns for and with a constant on RHS.
  APInt value;
  if (matchPattern(inputs.back(), m_RConstant(value))) {
    // and(..., '1) -> and(...) -- identity
    if (value.isAllOnesValue()) {
      rewriter.replaceOpWithNewOp<AndOp>(op, op.getType(), inputs.drop_back());
      return success();
    }

    // TODO: Combine multiple constants together even if they aren't at the end.
    // and(..., c1, c2) -> and(..., c3) where c3 = c1 & c2 -- constant folding
    APInt value2;
    if (matchPattern(inputs[size - 2], m_RConstant(value2))) {
      auto cst = rewriter.create<rtl::ConstantOp>(op.getLoc(), value & value2);
      SmallVector<Value, 4> newOperands(inputs.drop_back(/*n=*/2));
      newOperands.push_back(cst);
      rewriter.replaceOpWithNewOp<AndOp>(op, op.getType(), newOperands);
      return success();
    }

    // Handle 'and' with a single bit constant on the RHS.
    if (size == 2 && value.isPowerOf2()) {
      // If the LHS is a sign extend from a single bit, we can 'concat' it into
      // place.  e.g.:
      //   `sext(x) & 4` -> `concat(zeros, x, zeros)`
      if (auto sext = inputs[0].getDefiningOp<SExtOp>()) {
        auto sextOperand = sext.getOperand();
        if (sextOperand.getType().isInteger(1)) {
          unsigned resultWidth = op.getType().getIntOrFloatBitWidth();
          auto trailingZeros = value.countTrailingZeros();

          // We have to dance around the top and bottom bits because we can't
          // make zero bit wide APInts.
          SmallVector<Value, 3> concatOperands;
          if (trailingZeros != resultWidth - 1) {
            auto highZeros = rewriter.create<rtl::ConstantOp>(
                op.getLoc(), APInt(resultWidth - trailingZeros - 1, 0));
            concatOperands.push_back(highZeros);
          }
          concatOperands.push_back(sextOperand);
          if (trailingZeros != 0) {
            auto lowZeros = rewriter.create<rtl::ConstantOp>(
                op.getLoc(), APInt(trailingZeros, 0));
            concatOperands.push_back(lowZeros);
          }
          rewriter.replaceOpWithNewOp<ConcatOp>(op, op.getType(),
                                                concatOperands);
          return success();
        }
      }
    }
  }

  // and(x, and(...)) -> and(x, ...) -- flatten
  if (tryFlatteningOperands(op, rewriter))
    return success();

  /// TODO: and(..., x, not(x)) -> and(..., 0) -- complement
  return failure();
}

OpFoldResult OrOp::fold(ArrayRef<Attribute> constants) {
  APInt value(/*numBits=*/getType().getWidth(), 0, /*isSigned=*/false);

  // or(x, 10, 01) -> 11
  for (auto operand : constants) {
    if (!operand)
      continue;
    value |= operand.cast<IntegerAttr>().getValue();
    if (value.isAllOnesValue())
      return getIntAttr(value, getContext());
  }

  // or(x, 0) -> x
  if (constants.size() == 2 && constants[1] &&
      constants[1].cast<IntegerAttr>().getValue().isNullValue())
    return inputs()[0];

  // or(x, x, x) -> x.  This also handles or(x) -> x
  if (llvm::all_of(inputs(), [&](auto in) { return in == this->inputs()[0]; }))
    return inputs()[0];

  // Constant fold
  return constFoldVariadicOp<IntegerAttr>(
      constants, [](APInt &a, const APInt &b) { a |= b; });
}

LogicalResult OrOp::canonicalize(OrOp op, PatternRewriter &rewriter) {
  auto inputs = op.inputs();
  auto size = inputs.size();
  assert(size > 1 && "expected 2 or more operands");

  APInt value, value2;

  // or(..., 0) -> or(...) -- identity
  if (matchPattern(inputs.back(), m_RConstant(value)) && value.isNullValue()) {

    rewriter.replaceOpWithNewOp<OrOp>(op, op.getType(), inputs.drop_back());
    return success();
  }

  // or(..., x, x) -> or(..., x) -- idempotent
  if (inputs[size - 1] == inputs[size - 2]) {
    rewriter.replaceOpWithNewOp<OrOp>(op, op.getType(), inputs.drop_back());
    return success();
  }

  // or(..., c1, c2) -> or(..., c3) where c3 = c1 | c2 -- constant folding
  if (matchPattern(inputs[size - 1], m_RConstant(value)) &&
      matchPattern(inputs[size - 2], m_RConstant(value2))) {
    auto cst = rewriter.create<rtl::ConstantOp>(op.getLoc(), value | value2);
    SmallVector<Value, 4> newOperands(inputs.drop_back(/*n=*/2));
    newOperands.push_back(cst);
    rewriter.replaceOpWithNewOp<OrOp>(op, op.getType(), newOperands);
    return success();
  }

  // or(x, or(...)) -> or(x, ...) -- flatten
  if (tryFlatteningOperands(op, rewriter))
    return success();

  /// TODO: or(..., x, not(x)) -> or(..., '1) -- complement
  return failure();
}

OpFoldResult XorOp::fold(ArrayRef<Attribute> constants) {
  auto size = inputs().size();

  // xor(x) -> x -- noop
  if (size == 1)
    return inputs()[0];

  // xor(x, x) -> 0 -- idempotent
  if (size == 2 && inputs()[0] == inputs()[1])
    return IntegerAttr::get(getType(), 0);

  // xor(x, 0) -> x
  if (constants.size() == 2 && constants[1] &&
      constants[1].cast<IntegerAttr>().getValue().isNullValue())
    return inputs()[0];

  // Constant fold
  return constFoldVariadicOp<IntegerAttr>(
      constants, [](APInt &a, const APInt &b) { a ^= b; });
}

LogicalResult XorOp::canonicalize(XorOp op, PatternRewriter &rewriter) {
  auto inputs = op.inputs();
  auto size = inputs.size();
  assert(size > 1 && "expected 2 or more operands");

  // xor(..., x, x) -> xor (...) -- idempotent
  if (inputs[size - 1] == inputs[size - 2]) {
    assert(size > 2 &&
           "expected idempotent case for 2 elements handled already.");
    rewriter.replaceOpWithNewOp<XorOp>(op, op.getType(),
                                       inputs.drop_back(/*n=*/2));
    return success();
  }

  // Patterns for xor with a constant on RHS.
  APInt value;
  if (matchPattern(inputs.back(), m_RConstant(value))) {
    // xor(..., 0) -> xor(...) -- identity
    if (value.isNullValue()) {
      rewriter.replaceOpWithNewOp<XorOp>(op, op.getType(), inputs.drop_back());
      return success();
    }

    // xor(..., c1, c2) -> xor(..., c3) where c3 = c1 ^ c2.
    APInt value2;
    if (matchPattern(inputs[size - 2], m_RConstant(value2))) {
      auto cst = rewriter.create<rtl::ConstantOp>(op.getLoc(), value ^ value2);
      SmallVector<Value, 4> newOperands(inputs.drop_back(/*n=*/2));
      newOperands.push_back(cst);
      rewriter.replaceOpWithNewOp<XorOp>(op, op.getType(), newOperands);
      return success();
    }
  }

  // xor(x, xor(...)) -> xor(x, ...) -- flatten
  if (tryFlatteningOperands(op, rewriter))
    return success();

  return failure();
}

OpFoldResult MergeOp::fold(ArrayRef<Attribute> constants) {
  // rtl.merge(x, x, x) -> x.
  if (llvm::all_of(inputs(), [&](auto in) { return in == this->inputs()[0]; }))
    return inputs()[0];

  return {};
}

OpFoldResult SubOp::fold(ArrayRef<Attribute> constants) {
  APInt value;
  // sub(x - 0) -> x
  if (matchPattern(rhs(), m_RConstant(value)) && value.isNullValue())
    return lhs();

  // sub(x - x) -> 0
  if (rhs() == lhs())
    return getIntAttr(APInt(lhs().getType().getIntOrFloatBitWidth(), 0),
                      getContext());

  // Constant fold
  return constFoldBinaryOp<IntegerAttr>(constants,
                                        [](APInt a, APInt b) { return a - b; });
}

OpFoldResult AddOp::fold(ArrayRef<Attribute> constants) {
  auto size = inputs().size();

  // add(x) -> x -- noop
  if (size == 1u)
    return inputs()[0];

  // Constant fold
  return constFoldVariadicOp<IntegerAttr>(
      constants, [](APInt &a, const APInt &b) { a += b; });
}

LogicalResult AddOp::canonicalize(AddOp op, PatternRewriter &rewriter) {
  auto inputs = op.inputs();
  auto size = inputs.size();
  assert(size > 1 && "expected 2 or more operands");

  APInt value, value2;

  // add(..., 0) -> add(...) -- identity
  if (matchPattern(inputs.back(), m_RConstant(value)) && value.isNullValue()) {
    rewriter.replaceOpWithNewOp<AddOp>(op, op.getType(), inputs.drop_back());
    return success();
  }

  // add(..., c1, c2) -> add(..., c3) where c3 = c1 + c2 -- constant folding
  if (matchPattern(inputs[size - 1], m_RConstant(value)) &&
      matchPattern(inputs[size - 2], m_RConstant(value2))) {
    auto cst = rewriter.create<rtl::ConstantOp>(op.getLoc(), value + value2);
    SmallVector<Value, 4> newOperands(inputs.drop_back(/*n=*/2));
    newOperands.push_back(cst);
    rewriter.replaceOpWithNewOp<AddOp>(op, op.getType(), newOperands);
    return success();
  }

  // add(..., x, x) -> add(..., shl(x, 1))
  if (inputs[size - 1] == inputs[size - 2]) {
    SmallVector<Value, 4> newOperands(inputs.drop_back(/*n=*/2));

    auto one = rewriter.create<rtl::ConstantOp>(op.getLoc(), op.getType(), 1);
    auto shiftLeftOp =
        rewriter.create<comb::ShlOp>(op.getLoc(), inputs.back(), one);

    newOperands.push_back(shiftLeftOp);
    rewriter.replaceOpWithNewOp<AddOp>(op, op.getType(), newOperands);
    return success();
  }

  auto shlOp = inputs[size - 1].getDefiningOp<comb::ShlOp>();
  // add(..., x, shl(x, c)) -> add(..., mul(x, (1 << c) + 1))
  if (shlOp && shlOp.lhs() == inputs[size - 2] &&
      matchPattern(shlOp.rhs(), m_RConstant(value))) {

    APInt one(/*numBits=*/value.getBitWidth(), 1, /*isSigned=*/false);
    auto rhs =
        rewriter.create<rtl::ConstantOp>(op.getLoc(), (one << value) + one);

    std::array<Value, 2> factors = {shlOp.lhs(), rhs};
    auto mulOp = rewriter.create<comb::MulOp>(op.getLoc(), factors);

    SmallVector<Value, 4> newOperands(inputs.drop_back(/*n=*/2));
    newOperands.push_back(mulOp);
    rewriter.replaceOpWithNewOp<AddOp>(op, op.getType(), newOperands);
    return success();
  }

  auto mulOp = inputs[size - 1].getDefiningOp<comb::MulOp>();
  // add(..., x, mul(x, c)) -> add(..., mul(x, c + 1))
  if (mulOp && mulOp.inputs().size() == 2 &&
      mulOp.inputs()[0] == inputs[size - 2] &&
      matchPattern(mulOp.inputs()[1], m_RConstant(value))) {

    APInt one(/*numBits=*/value.getBitWidth(), 1, /*isSigned=*/false);
    auto rhs = rewriter.create<rtl::ConstantOp>(op.getLoc(), value + one);
    std::array<Value, 2> factors = {mulOp.inputs()[0], rhs};
    auto newMulOp = rewriter.create<comb::MulOp>(op.getLoc(), factors);

    SmallVector<Value, 4> newOperands(inputs.drop_back(/*n=*/2));
    newOperands.push_back(newMulOp);
    rewriter.replaceOpWithNewOp<AddOp>(op, op.getType(), newOperands);
    return success();
  }

  // add(x, add(...)) -> add(x, ...) -- flatten
  if (tryFlatteningOperands(op, rewriter))
    return success();

  return failure();
}

OpFoldResult MulOp::fold(ArrayRef<Attribute> constants) {
  auto size = inputs().size();

  // mul(x) -> x -- noop
  if (size == 1u)
    return inputs()[0];

  auto width = getType().getWidth();
  APInt value(/*numBits=*/width, 1, /*isSigned=*/false);

  // mul(x, 0, 1) -> 0 -- annulment
  for (auto operand : constants) {
    if (!operand)
      continue;
    value *= operand.cast<IntegerAttr>().getValue();
    if (value.isNullValue())
      return getIntAttr(value, getContext());
  }

  // Constant fold
  return constFoldVariadicOp<IntegerAttr>(
      constants, [](APInt &a, const APInt &b) { a *= b; });
}

LogicalResult MulOp::canonicalize(MulOp op, PatternRewriter &rewriter) {
  auto inputs = op.inputs();
  auto size = inputs.size();
  assert(size > 1 && "expected 2 or more operands");

  APInt value, value2;

  // mul(x, c) -> shl(x, log2(c)), where c is a power of two.
  if (size == 2 && matchPattern(inputs.back(), m_RConstant(value)) &&
      value.isPowerOf2()) {
    auto shift = rewriter.create<rtl::ConstantOp>(op.getLoc(), op.getType(),
                                                  value.exactLogBase2());
    auto shlOp = rewriter.create<comb::ShlOp>(op.getLoc(), inputs[0], shift);

    rewriter.replaceOpWithNewOp<MulOp>(op, op.getType(),
                                       ArrayRef<Value>(shlOp));
    return success();
  }

  // mul(..., 1) -> mul(...) -- identity
  if (matchPattern(inputs.back(), m_RConstant(value)) && (value == 1u)) {
    rewriter.replaceOpWithNewOp<MulOp>(op, op.getType(), inputs.drop_back());
    return success();
  }

  // mul(..., c1, c2) -> mul(..., c3) where c3 = c1 * c2 -- constant folding
  if (matchPattern(inputs[size - 1], m_RConstant(value)) &&
      matchPattern(inputs[size - 2], m_RConstant(value2))) {
    auto cst = rewriter.create<rtl::ConstantOp>(op.getLoc(), value * value2);
    SmallVector<Value, 4> newOperands(inputs.drop_back(/*n=*/2));
    newOperands.push_back(cst);
    rewriter.replaceOpWithNewOp<MulOp>(op, op.getType(), newOperands);
    return success();
  }

  // mul(a, mul(...)) -> mul(a, ...) -- flatten
  if (tryFlatteningOperands(op, rewriter))
    return success();

  return failure();
}

//===----------------------------------------------------------------------===//
// ConcatOp
//===----------------------------------------------------------------------===//

// Constant folding
OpFoldResult ConcatOp::fold(ArrayRef<Attribute> constants) {
  // If all the operands are constant, we can fold.
  for (auto attr : constants)
    if (!attr || !attr.isa<IntegerAttr>())
      return {};

  // If we got here, we can constant fold.
  unsigned resultWidth = getType().getIntOrFloatBitWidth();
  APInt result(resultWidth, 0);

  unsigned nextInsertion = resultWidth;
  // Insert each chunk into the result.
  for (auto attr : constants) {
    auto chunk = attr.cast<IntegerAttr>().getValue();
    nextInsertion -= chunk.getBitWidth();
    result |= chunk.zext(resultWidth) << nextInsertion;
  }

  return getIntAttr(result, getContext());
}

LogicalResult ConcatOp::canonicalize(ConcatOp op, PatternRewriter &rewriter) {
  auto inputs = op.inputs();
  auto size = inputs.size();
  assert(size > 1 && "expected 2 or more operands");

  // This function is used when we flatten neighboring operands of a (variadic)
  // concat into a new vesion of the concat.  first/last indices are inclusive.
  auto flattenConcat = [&](size_t firstOpIndex, size_t lastOpIndex,
                           ValueRange replacements) -> LogicalResult {
    SmallVector<Value, 4> newOperands;
    newOperands.append(inputs.begin(), inputs.begin() + firstOpIndex);
    newOperands.append(replacements.begin(), replacements.end());
    newOperands.append(inputs.begin() + lastOpIndex + 1, inputs.end());
    if (newOperands.size() == 1)
      rewriter.replaceOp(op, newOperands[0]);
    else
      rewriter.replaceOpWithNewOp<ConcatOp>(op, op.getType(), newOperands);
    return success();
  };

  for (size_t i = 0; i != size; ++i) {
    // If an operand to the concat is itself a concat, then we can fold them
    // together.
    if (auto subConcat = inputs[i].getDefiningOp<ConcatOp>())
      return flattenConcat(i, i, subConcat->getOperands());

    // We can flatten a sext into the concat, since a sext is an extraction of
    // a sign bit plus the input value itself.
    if (auto sext = inputs[i].getDefiningOp<SExtOp>()) {
      unsigned inputWidth = sext.input().getType().getIntOrFloatBitWidth();

      auto sign = rewriter.create<ExtractOp>(op.getLoc(), rewriter.getI1Type(),
                                             sext.input(), inputWidth - 1);
      SmallVector<Value> replacements;
      unsigned signWidth = sext.getType().getIntOrFloatBitWidth() - inputWidth;
      replacements.append(signWidth, sign);
      replacements.push_back(sext.input());
      return flattenConcat(i, i, replacements);
    }

    // Check for canonicalization due to neighboring operands.
    if (i != 0) {
      // Merge neighboring constants.
      if (auto cst = inputs[i].getDefiningOp<rtl::ConstantOp>()) {
        if (auto prevCst = inputs[i - 1].getDefiningOp<rtl::ConstantOp>()) {
          unsigned prevWidth = prevCst.getValue().getBitWidth();
          unsigned thisWidth = cst.getValue().getBitWidth();
          auto resultCst = cst.getValue().zext(prevWidth + thisWidth);
          resultCst |= prevCst.getValue().zext(prevWidth + thisWidth)
                       << thisWidth;
          Value replacement =
              rewriter.create<rtl::ConstantOp>(op.getLoc(), resultCst);
          return flattenConcat(i - 1, i, replacement);
        }
      }

      // Merge neighboring extracts of neighboring inputs, e.g.
      // {A[3], A[2]} -> A[3,2]
      if (auto extract = inputs[i].getDefiningOp<ExtractOp>()) {
        if (auto prevExtract = inputs[i - 1].getDefiningOp<ExtractOp>()) {
          if (extract.input() == prevExtract.input()) {
            auto thisWidth = extract.getType().getIntOrFloatBitWidth();
            if (prevExtract.lowBit() == extract.lowBit() + thisWidth) {
              auto prevWidth = prevExtract.getType().getIntOrFloatBitWidth();
              auto resType = rewriter.getIntegerType(thisWidth + prevWidth);
              Value replacement = rewriter.create<ExtractOp>(
                  op.getLoc(), resType, extract.input(), extract.lowBit());
              return flattenConcat(i - 1, i, replacement);
            }
          }
        }
      }
    }
  }

  // Return true if this extract is an extract of the sign bit of its input.
  auto isSignBitExtract = [](ExtractOp op) -> bool {
    if (op.getType().getIntOrFloatBitWidth() != 1)
      return false;
    return op.lowBit() == op.input().getType().getIntOrFloatBitWidth() - 1;
  };

  // Folds concat back into a sext.
  if (auto extract = inputs[0].getDefiningOp<ExtractOp>()) {
    if (extract.input() == inputs.back() && isSignBitExtract(extract)) {
      // Check intermediate bits.
      bool allMatch = true;
      // The intermediate bits are allowed to be difference instances of extract
      // (because canonicalize doesn't do CSE automatically) so long as they are
      // getting the sign bit.
      for (size_t i = 1, e = inputs.size() - 1; i != e; ++i) {
        auto extractInner = inputs[i].getDefiningOp<ExtractOp>();
        if (!extractInner || extractInner.input() != inputs.back() ||
            !isSignBitExtract(extractInner)) {
          allMatch = false;
          break;
        }
      }
      if (allMatch) {
        rewriter.replaceOpWithNewOp<SExtOp>(op, op.getType(), inputs.back());
        return success();
      }
    }
  }

  return failure();
}

//===----------------------------------------------------------------------===//
// MuxOp
//===----------------------------------------------------------------------===//

OpFoldResult MuxOp::fold(ArrayRef<Attribute> constants) {
  // mux (c, b, b) -> b
  if (trueValue() == falseValue())
    return trueValue();

  // mux(0, a, b) -> b
  // mux(1, a, b) -> a
  if (auto pred = constants[0].dyn_cast_or_null<IntegerAttr>()) {
    if (pred.getValue().isNullValue())
      return falseValue();
    return trueValue();
  }

  return {};
}

static mlir::Value sextToDestTypeAndFlip(mlir::Value op, Type destType,
                                         PatternRewriter &rewriter) {
  op = rewriter.createOrFold<SExtOp>(op.getLoc(), destType, op);
  Value newOperands[] = {
      op, rewriter.create<rtl::ConstantOp>(op.getLoc(), destType, -1)};
  return rewriter.create<XorOp>(op.getLoc(), destType, newOperands);
}

LogicalResult MuxOp::canonicalize(MuxOp op, PatternRewriter &rewriter) {
  APInt value;

  if (matchPattern(op.trueValue(), m_RConstant(value))) {
    // mux(a, 11...1, b) -> or(a, b)
    if (value.isAllOnesValue()) {
      auto cond =
          rewriter.createOrFold<SExtOp>(op.getLoc(), op.getType(), op.cond());

      Value newOperands[] = {cond, op.falseValue()};
      rewriter.replaceOpWithNewOp<OrOp>(op, op.getType(), newOperands);
      return success();
    }

    // mux(a, 0, b) -> and(not(a), b)
    if (value.isNullValue()) {
      auto cond = sextToDestTypeAndFlip(op.cond(), op.getType(), rewriter);
      Value newOperands[] = {cond, op.falseValue()};
      rewriter.replaceOpWithNewOp<AndOp>(op, op.getType(), newOperands);
      return success();
    }
  }

  if (matchPattern(op.falseValue(), m_RConstant(value))) {
    // mux(a, b, 0) -> and(a, b)
    if (value.isNullValue()) {
      auto cond =
          rewriter.createOrFold<SExtOp>(op.getLoc(), op.getType(), op.cond());

      Value newOperands[] = {cond, op.trueValue()};
      rewriter.replaceOpWithNewOp<AndOp>(op, op.getType(), newOperands);
      return success();
    }

    // mux(a, b, 11...1) -> or(not(a), b)
    if (value.isAllOnesValue()) {
      auto cond = sextToDestTypeAndFlip(op.cond(), op.getType(), rewriter);
      Value newOperands[] = {cond, op.trueValue()};
      rewriter.replaceOpWithNewOp<OrOp>(op, op.getType(), newOperands);
      return success();
    }
  }
  return failure();
}

//===----------------------------------------------------------------------===//
// ICmpOp
//===----------------------------------------------------------------------===//

// Calculate the result of a comparison when the LHS and RHS are both
// constants.
static bool applyCmpPredicate(ICmpPredicate predicate, const APInt &lhs,
                              const APInt &rhs) {
  switch (predicate) {
  case ICmpPredicate::eq:
    return lhs.eq(rhs);
  case ICmpPredicate::ne:
    return lhs.ne(rhs);
  case ICmpPredicate::slt:
    return lhs.slt(rhs);
  case ICmpPredicate::sle:
    return lhs.sle(rhs);
  case ICmpPredicate::sgt:
    return lhs.sgt(rhs);
  case ICmpPredicate::sge:
    return lhs.sge(rhs);
  case ICmpPredicate::ult:
    return lhs.ult(rhs);
  case ICmpPredicate::ule:
    return lhs.ule(rhs);
  case ICmpPredicate::ugt:
    return lhs.ugt(rhs);
  case ICmpPredicate::uge:
    return lhs.uge(rhs);
  }
  llvm_unreachable("unknown comparison predicate");
}

// Returns the result of applying the predicate when the LHS and RHS are the
// exact same value.
static bool applyCmpPredicateToEqualOperands(ICmpPredicate predicate) {
  switch (predicate) {
  case ICmpPredicate::eq:
  case ICmpPredicate::sle:
  case ICmpPredicate::sge:
  case ICmpPredicate::ule:
  case ICmpPredicate::uge:
    return true;
  case ICmpPredicate::ne:
  case ICmpPredicate::slt:
  case ICmpPredicate::sgt:
  case ICmpPredicate::ult:
  case ICmpPredicate::ugt:
    return false;
  }
  llvm_unreachable("unknown comparison predicate");
}

OpFoldResult ICmpOp::fold(ArrayRef<Attribute> constants) {

  // gt a, a -> false
  // gte a, a -> true
  if (lhs() == rhs()) {
    auto val = applyCmpPredicateToEqualOperands(predicate());
    return IntegerAttr::get(getType(), val);
  }

  // gt 1, 2 -> false
  if (auto lhs = constants[0].dyn_cast_or_null<IntegerAttr>()) {
    if (auto rhs = constants[1].dyn_cast_or_null<IntegerAttr>()) {
      auto val = applyCmpPredicate(predicate(), lhs.getValue(), rhs.getValue());
      return IntegerAttr::get(getType(), val);
    }
  }
  return {};
}

// Canonicalizes a ICmp with a single constant
LogicalResult ICmpOp::canonicalize(ICmpOp op, PatternRewriter &rewriter) {
  APInt lhs, rhs;

  // icmp 1, x -> icmp x, 1
  if (matchPattern(op.lhs(), m_RConstant(lhs))) {
    assert(!matchPattern(op.rhs(), m_RConstant(rhs)) && "Should be folded");
    rewriter.replaceOpWithNewOp<ICmpOp>(
        op, ICmpOp::getFlippedPredicate(op.predicate()), op.rhs(), op.lhs());
    return success();
  }

  // Canonicalize with RHS constant
  if (matchPattern(op.rhs(), m_RConstant(rhs))) {
    rtl::ConstantOp constant;

    auto getConstant = [&](APInt constant) -> Value {
      return rewriter.create<rtl::ConstantOp>(op.getLoc(), std::move(constant));
    };

    auto replaceWith = [&](ICmpPredicate predicate, Value lhs,
                           Value rhs) -> LogicalResult {
      rewriter.replaceOpWithNewOp<ICmpOp>(op, predicate, lhs, rhs);
      return success();
    };

    auto replaceWithConstantI1 = [&](bool constant) -> LogicalResult {
      rewriter.replaceOpWithNewOp<rtl::ConstantOp>(op, APInt(1, constant));
      return success();
    };

    switch (op.predicate()) {
    case ICmpPredicate::slt:
      // x < max -> x != max
      if (rhs.isMaxSignedValue())
        return replaceWith(ICmpPredicate::ne, op.lhs(), op.rhs());
      // x < min -> false
      if (rhs.isMinSignedValue())
        return replaceWithConstantI1(0);
      // x < min+1 -> x == min
      if ((rhs - 1).isMinSignedValue())
        return replaceWith(ICmpPredicate::eq, op.lhs(), getConstant(rhs - 1));
      break;
    case ICmpPredicate::sgt:
      // x > min -> x != min
      if (rhs.isMinSignedValue())
        return replaceWith(ICmpPredicate::ne, op.lhs(), op.rhs());
      // x > max -> false
      if (rhs.isMaxSignedValue())
        return replaceWithConstantI1(0);
      // x > max-1 -> x == max
      if ((rhs + 1).isMaxSignedValue())
        return replaceWith(ICmpPredicate::eq, op.lhs(), getConstant(rhs + 1));
      break;
    case ICmpPredicate::ult:
      // x < max -> x != max
      if (rhs.isMaxValue())
        return replaceWith(ICmpPredicate::ne, op.lhs(), op.rhs());
      // x < min -> false
      if (rhs.isMinValue())
        return replaceWithConstantI1(0);
      // x < min+1 -> x == min
      if ((rhs - 1).isMinValue())
        return replaceWith(ICmpPredicate::eq, op.lhs(), getConstant(rhs - 1));
      break;
    case ICmpPredicate::ugt:
      // x > min -> x != min
      if (rhs.isMinValue())
        return replaceWith(ICmpPredicate::ne, op.lhs(), op.rhs());
      // x > max -> false
      if (rhs.isMaxValue())
        return replaceWithConstantI1(0);
      // x > max-1 -> x == max
      if ((rhs + 1).isMaxValue())
        return replaceWith(ICmpPredicate::eq, op.lhs(), getConstant(rhs + 1));
      break;
    case ICmpPredicate::sle:
      // x <= max -> true
      if (rhs.isMaxSignedValue())
        return replaceWithConstantI1(1);
      // x <= c -> x < (c+1)
      return replaceWith(ICmpPredicate::slt, op.lhs(), getConstant(rhs + 1));
    case ICmpPredicate::sge:
      // x >= min -> true
      if (rhs.isMinSignedValue())
        return replaceWithConstantI1(1);
      // x >= c -> x > (c-1)
      return replaceWith(ICmpPredicate::sgt, op.lhs(), getConstant(rhs - 1));
    case ICmpPredicate::ule:
      // x <= max -> true
      if (rhs.isMaxValue())
        return replaceWithConstantI1(1);
      // x <= c -> x < (c+1)
      return replaceWith(ICmpPredicate::ult, op.lhs(), getConstant(rhs + 1));
    case ICmpPredicate::uge:
      // x >= min -> true
      if (rhs.isMinValue())
        return replaceWithConstantI1(1);
      // x >= c -> x > (c-1)
      return replaceWith(ICmpPredicate::ugt, op.lhs(), getConstant(rhs - 1));
    case ICmpPredicate::eq:
      if (rhs.getBitWidth() != 1)
        break;
      if (rhs.isNullValue()) {
        // x == 0 -> x ^ 1
        rewriter.replaceOpWithNewOp<XorOp>(op, op.lhs(),
                                           getConstant(APInt(1, 1)));
        return success();
      }
      if (rhs.isAllOnesValue()) {
        // x == 1 -> x
        rewriter.replaceOp(op, op.lhs());
        return success();
      }
      break;
    case ICmpPredicate::ne:
      if (rhs.getBitWidth() != 1)
        break;
      if (rhs.isNullValue()) {
        // x != 0 -> x
        rewriter.replaceOp(op, op.lhs());
        return success();
      }
      if (rhs.isAllOnesValue()) {
        // x != 1 -> x ^ 1
        rewriter.replaceOpWithNewOp<XorOp>(op, op.lhs(),
                                           getConstant(APInt(1, 1)));
        return success();
      }
      break;
    }
  }

  return failure();
}
