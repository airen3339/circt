//===- SeqToSV.cpp - Implement Seq passes -------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "circt/Conversion/SeqToSV.h"
#include "../PassDetail.h"
#include "circt/Dialect/SV/SVOps.h"
#include "circt/Dialect/Seq/SeqOps.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/DialectImplementation.h"
#include "mlir/Pass/Pass.h"
#include "mlir/Transforms/DialectConversion.h"

using namespace mlir;
using namespace circt;
using namespace seq;

namespace {
/// Lower CompRegOp to `sv.reg` and `sv.alwaysff`. Use a posedge clock and
/// synchronous reset.
struct CompRegLower : public OpConversionPattern<CompRegOp> {
public:
  using OpConversionPattern::OpConversionPattern;

  LogicalResult
  matchAndRewrite(CompRegOp reg, OpAdaptor adaptor,
                  ConversionPatternRewriter &rewriter) const final {
    Location loc = reg.getLoc();

    auto svReg = rewriter.create<sv::RegOp>(loc, reg.getResult().getType(),
                                            reg.nameAttr());
    svReg->setDialectAttrs(reg->getDialectAttrs());

    // If the seq::CompRegOp has an inner_sym attribute, set this for the
    // sv::RegOp inner_sym attribute.
    if (reg.sym_name().hasValue())
      svReg.inner_symAttr(reg.sym_nameAttr());

    auto regVal = rewriter.create<sv::ReadInOutOp>(loc, svReg);
    if (reg.reset() && reg.resetValue()) {
      rewriter.create<sv::AlwaysFFOp>(
          loc, sv::EventControl::AtPosEdge, reg.clk(), ResetType::SyncReset,
          sv::EventControl::AtPosEdge, reg.reset(),
          [&]() { rewriter.create<sv::PAssignOp>(loc, svReg, reg.input()); },
          [&]() {
            rewriter.create<sv::PAssignOp>(loc, svReg, reg.resetValue());
          });
    } else {
      rewriter.create<sv::AlwaysFFOp>(
          loc, sv::EventControl::AtPosEdge, reg.clk(),
          [&]() { rewriter.create<sv::PAssignOp>(loc, svReg, reg.input()); });
    }

    rewriter.replaceOp(reg, {regVal});
    return success();
  }
};

struct ConvertSeqToSVPass : public ConvertSeqToSVBase<ConvertSeqToSVPass> {
  void runOnOperation() override;
};
} // anonymous namespace

void ConvertSeqToSVPass::runOnOperation() {
  ModuleOp top = getOperation();
  MLIRContext &ctxt = getContext();

  ConversionTarget target(ctxt);
  target.addIllegalDialect<SeqDialect>();
  target.addLegalDialect<sv::SVDialect>();
  RewritePatternSet patterns(&ctxt);
  patterns.add<CompRegLower>(&ctxt);

  if (failed(applyPartialConversion(top, target, std::move(patterns))))
    signalPassFailure();
}

namespace circt {
std::unique_ptr<OperationPass<ModuleOp>> createConvertSeqToSVPass() {
  return std::make_unique<ConvertSeqToSVPass>();
}
} // namespace circt
