//===- VerifToSV.cpp - HW To SV Conversion Pass ---------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This is the main Verif to SV Conversion Pass Implementation.
//
//===----------------------------------------------------------------------===//

#include "circt/Conversion/VerifToSV.h"
#include "circt/Dialect/Comb/CombOps.h"
#include "circt/Dialect/HW/HWOpInterfaces.h"
#include "circt/Dialect/HW/HWOps.h"
#include "circt/Dialect/SV/"
#include "circt/Dialect/SV/SVOps.h"
#include "circt/Dialect/Verif/VerifOps.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Transforms/DialectConversion.h"
#include "llvm/ADT/TypeSwitch.h"

namespace circt {
#define GEN_PASS_DEF_LOWERVERIFTOSV
#include "circt/Conversion/Passes.h.inc"
} // namespace circt

using namespace mlir;
using namespace circt;
using namespace sv;
using namespace verif;

//===----------------------------------------------------------------------===//
// Conversion Patterns
//===----------------------------------------------------------------------===//

namespace {

static sv::EventControl verifToSVEventControl(verif::ClockEdge ce) {
  switch (ce) {
  case verif::ClockEdge::Pos:
    return sv::EventControl::AtPosEdge;
  case verif::ClockEdge::Neg:
    return sv::EventControl::AtNegEdge;
  case verif::ClockEdge::Both:
    return sv::EventControl::AtEdge;
  }
  llvm_unreachable("Unknown event control kind");
}

struct PrintOpConversionPattern : public OpConversionPattern<PrintOp> {
  using OpConversionPattern<PrintOp>::OpConversionPattern;

  LogicalResult
  matchAndRewrite(PrintOp op, OpAdaptor operands,
                  ConversionPatternRewriter &rewriter) const override {

    // Printf's will be emitted to stdout (32'h8000_0001 in IEEE Std 1800-2012).
    Value fdStdout = rewriter.create<hw::ConstantOp>(
        op.getLoc(), APInt(32, 0x80000001, false));

    auto fstrOp =
        dyn_cast_or_null<FormatVerilogStringOp>(op.getString().getDefiningOp());
    if (!fstrOp)
      return op->emitOpError() << "expected FormatVerilogStringOp as the "
                                  "source of the formatted string";

    rewriter.replaceOpWithNewOp<sv::FWriteOp>(
        op, fdStdout, fstrOp.getFormatString(), fstrOp.getSubstitutions());
    return success();
  }
};

struct HasBeenResetConversion : public OpConversionPattern<HasBeenResetOp> {
  using OpConversionPattern<HasBeenResetOp>::OpConversionPattern;

  LogicalResult
  matchAndRewrite(HasBeenResetOp op, OpAdaptor operands,
                  ConversionPatternRewriter &rewriter) const override {
    auto i1 = rewriter.getI1Type();
    auto constOne = rewriter.create<hw::ConstantOp>(op.getLoc(), i1, 1);
    auto constZero = rewriter.create<hw::ConstantOp>(op.getLoc(), i1, 0);
    auto constX = rewriter.create<sv::ConstantXOp>(op.getLoc(), i1);

    // Declare the register that will track the reset state.
    auto reg = rewriter.create<sv::RegOp>(
        op.getLoc(), i1, rewriter.getStringAttr("hasBeenResetReg"));

    auto clock = operands.getClock();
    auto reset = operands.getReset();

    // Explicitly initialize the register in an `initial` block. In general, the
    // register will come up as X, but this may be overridden by simulator
    // configuration options.
    //
    // In case the reset is async, check if the reset is already active during
    // the `initial` block and immediately set the register to 1. Otherwise
    // initialize to X.
    rewriter.create<sv::InitialOp>(op.getLoc(), [&] {
      auto assignOne = [&] {
        rewriter.create<sv::BPAssignOp>(op.getLoc(), reg, constOne);
      };
      auto assignX = [&] {
        rewriter.create<sv::BPAssignOp>(op.getLoc(), reg, constX);
      };
      if (op.getAsync())
        rewriter.create<sv::IfOp>(op.getLoc(), reset, assignOne, assignX);
      else
        assignX();
    });

    // Create the `always` block that sets the register to 1 as soon as the
    // reset is initiated. For async resets this happens at the reset's posedge;
    // for sync resets this happens on the clock's posedge if the reset is set.
    Value triggerOn = op.getAsync() ? reset : clock;
    rewriter.create<sv::AlwaysOp>(
        op.getLoc(), sv::EventControl::AtPosEdge, triggerOn, [&] {
          auto assignOne = [&] {
            rewriter.create<sv::PAssignOp>(op.getLoc(), reg, constOne);
          };
          if (op.getAsync())
            assignOne();
          else
            rewriter.create<sv::IfOp>(op.getLoc(), reset, assignOne);
        });

    // Derive the actual result value:
    //   hasBeenReset = (hasBeenResetReg === 1) && (reset === 0);
    auto regRead = rewriter.create<sv::ReadInOutOp>(op.getLoc(), reg);
    auto regIsOne = rewriter.createOrFold<comb::ICmpOp>(
        op.getLoc(), comb::ICmpPredicate::ceq, regRead, constOne);
    auto resetIsZero = rewriter.createOrFold<comb::ICmpOp>(
        op.getLoc(), comb::ICmpPredicate::ceq, reset, constZero);
    auto resetStartedAndEnded = rewriter.createOrFold<comb::AndOp>(
        op.getLoc(), regIsOne, resetIsZero, true);
    rewriter.replaceOpWithNewOp<hw::WireOp>(
        op, resetStartedAndEnded, rewriter.getStringAttr("hasBeenReset"));

    return success();
  }
};

namespace VerifAssertLikeOp {
// Convert the verif.assert like op that uses an enable, into an equivalent
// sv.assert_property op that has the negated enable as its disable.
template <typename TargetOp, typename Op, typename Conversion>
static LogicalResult convert(Op op, Conversion::OpAdaptor operands,
                             ConversionPatternRewriter &rewriter) {
  // negate the enable if it exists
  Value enable, wdisable;
  if ((enable = operands.getEnable())) {
    Value disable = rewriter.create<comb::XorOp>(op.getLoc(), enable, enable);
    wdisable = rewriter.create<hw::WireOp>(op.getLoc(), disable);
  }

  rewriter.replaceOpWithNewOp<TargetOp>(op, operands.getProperty(), wdisable,
                                        operands.getLabelAttr());
  return success();
}

template <typename TargetOp, typename Op, typename Conversion>
static LogicalResult convertClocked(Op op, Conversion::OpAdaptor operands,
                                    ConversionPatternRewriter &rewriter) {
  // negate the enable if it exists
  Value enable, wdisable;
  if ((enable = operands.getEnable())) {
    Value disable = rewriter.create<comb::XorOp>(op.getLoc(), enable, enable);
    wdisable = rewriter.create<hw::WireOp>(op.getLoc(), disable);
  }

  rewriter.replaceOpWithNewOp<TargetOp>(
      op, operands.getProperty(), verifToSVEventControl(operands.getEvent()),
      operands.getClock(), wdisable, operands.getLabelAttr());
  return success();
}
} // namespace VerifAssertLikeOp

struct VerifAssertConversion : public OpConversionPattern<AssertOp> {
  using OpConversionPattern<AssertOp>::OpConversionPattern;

  LogicalResult
  matchAndRewrite(AssertOp op, OpAdaptor operands,
                  ConversionPatternRewriter &rewriter) const override {
    return VerifAssertLikeOp::convert<sv::AssertPropertyOp, AssertOp,
                                      VerifAssertConversion>(op, operands,
                                                             rewriter);
  }
};

struct VerifAssumeConversion : public OpConversionPattern<AssumeOp> {
  using OpConversionPattern<AssumeOp>::OpConversionPattern;

  LogicalResult
  matchAndRewrite(AssumeOp op, OpAdaptor operands,
                  ConversionPatternRewriter &rewriter) const override {
    return VerifAssertLikeOp::convert<sv::AssumePropertyOp, AssumeOp,
                                      VerifAssumeConversion>(op, operands,
                                                             rewriter);
  }
};

struct VerifCoverConversion : public OpConversionPattern<CoverOp> {
  using OpConversionPattern<CoverOp>::OpConversionPattern;

  LogicalResult
  matchAndRewrite(CoverOp op, OpAdaptor operands,
                  ConversionPatternRewriter &rewriter) const override {
    return VerifAssertLikeOp::convert<sv::CoverPropertyOp, CoverOp,
                                      VerifCoverConversion>(op, operands,
                                                            rewriter);
  }
};

// Clocked assert like
struct VerifClockedAssertConversion
    : public OpConversionPattern<ClockedAssertOp> {
  using OpConversionPattern<ClockedAssertOp>::OpConversionPattern;

  LogicalResult
  matchAndRewrite(ClockedAssertOp op, OpAdaptor operands,
                  ConversionPatternRewriter &rewriter) const override {
    return VerifAssertLikeOp::convertClocked<
        sv::AssertPropertyOp, ClockedAssertOp, VerifClockedAssertConversion>(
        op, operands, rewriter);
  }
};

struct VerifClockedAssumeConversion
    : public OpConversionPattern<ClockedAssumeOp> {
  using OpConversionPattern<ClockedAssumeOp>::OpConversionPattern;

  LogicalResult
  matchAndRewrite(ClockedAssumeOp op, OpAdaptor operands,
                  ConversionPatternRewriter &rewriter) const override {
    return VerifAssertLikeOp::convertClocked<
        sv::AssumePropertyOp, ClockedAssumeOp, VerifClockedAssumeConversion>(
        op, operands, rewriter);
  }
};

struct VerifClockedCoverConversion : public OpConversionPattern<CoverOp> {
  using OpConversionPattern<ClockedCoverOp>::OpConversionPattern;

  LogicalResult
  matchAndRewrite(CoverOp op, OpAdaptor operands,
                  ConversionPatternRewriter &rewriter) const override {
    return VerifAssertLikeOp::convertClocked<
        sv::CoverPropertyOp, ClockedCoverOp, VerifClockedCoverConversion>(
        op, operands, rewriter);
  }
};

} // namespace

//===----------------------------------------------------------------------===//
// Pass Infrastructure
//===----------------------------------------------------------------------===//

namespace {
struct VerifToSVPass : public circt::impl::LowerVerifToSVBase<VerifToSVPass> {
  void runOnOperation() override;
};
} // namespace

void VerifToSVPass::runOnOperation() {
  MLIRContext &context = getContext();
  hw::HWModuleOp module = getOperation();

  ConversionTarget target(context);
  RewritePatternSet patterns(&context);

  target.addIllegalOp<PrintOp, HasBeenResetOp>();
  target.addLegalDialect<sv::SVDialect, hw::HWDialect, comb::CombDialect>();
  patterns.add<PrintOpConversionPattern, HasBeenResetConversion>(&context);

  if (failed(applyPartialConversion(module, target, std::move(patterns))))
    signalPassFailure();
}

std::unique_ptr<OperationPass<hw::HWModuleOp>>
circt::createLowerVerifToSVPass() {
  return std::make_unique<VerifToSVPass>();
}
