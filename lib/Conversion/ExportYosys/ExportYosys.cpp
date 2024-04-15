//===- LowerFirMem.cpp - Seq FIRRTL memory lowering -----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This transform translate Seq FirMem ops to instances of HW generated modules.
//
//===----------------------------------------------------------------------===//
#include "circt/Conversion/ExportYosys.h"
#include "../PassDetail.h"
#include "backends/rtlil/rtlil_backend.h"
#include "circt/Dialect/Comb/CombVisitors.h"
#include "circt/Dialect/HW/HWOps.h"
#include "circt/Dialect/HW/HWVisitors.h"
#include "circt/Dialect/Seq/SeqOps.h"
#include "circt/Support/Namespace.h"
#include "mlir/IR/Builders.h"
#include "mlir/IR/Threading.h"
#include "mlir/Pass/Pass.h"
#include "llvm/ADT/FunctionExtras.h"
#include "llvm/Support/Debug.h"

#include "kernel/rtlil.h"
#include "kernel/yosys.h"

#define DEBUG_TYPE "export-yosys"

using namespace circt;
using namespace hw;
using namespace comb;
using namespace Yosys;

namespace {
#define GEN_PASS_DEF_EXPORTYOSYS
#include "circt/Conversion/Passes.h.inc"

struct ExportYosysPass : public impl::ExportYosysBase<ExportYosysPass> {
  void runOnOperation() override;
};

std::string getEscapedName(StringRef name) {
  return RTLIL::escape_id(name.str());
}

struct RTLILConverter {};
struct ModuleConverter;

struct ExprEmitter
    : public hw::TypeOpVisitor<ExprEmitter, FailureOr<Yosys::SigSpec>>,
      public comb::CombinationalVisitor<ExprEmitter,
                                        FailureOr<Yosys::SigSpec>> {
  ExprEmitter(ModuleConverter &moduleEmitter) : moduleEmitter(moduleEmitter) {}
  ModuleConverter &moduleEmitter;
  FailureOr<Yosys::SigSpec> getValue(Value value);
  FailureOr<Yosys::SigSpec> emitExpression(Operation *op) {
    return dispatchCombinationalVisitor(op);
  }
  FailureOr<Yosys::SigSpec> visitUnhandledTypeOp(Operation *op) {
    return op->emitError() << " is unsupported";
  }
  FailureOr<Yosys::SigSpec> visitUnhandledExpr(Operation *op) {
    return op->emitError() << " is unsupported";
  }
  FailureOr<Yosys::SigSpec> visitInvalidComb(Operation *op) {
    return dispatchTypeOpVisitor(op);
  }
  FailureOr<Yosys::SigSpec> visitUnhandledComb(Operation *op) {
    return visitUnhandledExpr(op);
  }
  FailureOr<Yosys::SigSpec> visitInvalidTypeOp(Operation *op) {
    return visitUnhandledExpr(op);
  }

  FailureOr<Yosys::SigSpec> visitTypeOp(ConstantOp op) {
    if (op.getValue().getBitWidth() >= 32)
      return op.emitError() << "unsupported";
    return Yosys::SigSpec(RTLIL::Const(op.getValue().getZExtValue(), op.getValue().getBitWidth()));
  }

  using hw::TypeOpVisitor<ExprEmitter, FailureOr<SigSpec>>::visitTypeOp;
  using comb::CombinationalVisitor<ExprEmitter, FailureOr<SigSpec>>::visitComb;

  FailureOr<Yosys::SigSpec> visitComb(AddOp op);
  FailureOr<Yosys::SigSpec> visitComb(SubOp op);

  // Comb.
  // ResultTy visitComb(MuxOp op);
  template <typename BinaryFn>
  FailureOr<Yosys::SigSpec> emitVariadicOp(Operation *op, BinaryFn fn) {
    // Construct n-1 binary op (currently linear) chains.
    // TODO: Need to create a tree?
    std::optional<SigSpec> cur;
    for (auto operand : op->getOperands()) {
      auto result = getValue(operand);
      if (failed(result))
        return failure();
      if (cur) {
        cur = fn(getNewName(), *cur, result.value());
      } else
        cur = result.value();
    }

    return cur.value();
  }
  RTLIL::IdString getNewName(StringRef name = "_GEN_");
};

using ResultTy = FailureOr<bool>;
constexpr bool ResultTySuccess = true;

struct ModuleConverter
    : public hw::TypeOpVisitor<ModuleConverter, FailureOr<bool>>,
      public comb::CombinationalVisitor<ModuleConverter, FailureOr<bool>> {

  FailureOr<SigSpec> getValue(Value value) {
    auto it = mapping.find(value);
    if (it != mapping.end())
      return it->second;
    if (isa<OpResult>(value)) {
      // TODO: If it's instance like ...
      auto *op = value.getDefiningOp();
      auto result = ExprEmitter(*this).emitExpression(op);
      // auto result = visit(op);
      if (failed(result))
        return op->emitError() << "lowering failed";

      setLowering(op->getResult(0), result.value());
      return result;
    }
    // TODO: Convert ports.
    return failure();
  }

  circt::Namespace moduleNameSpace;
  RTLIL::IdString getNewName(StringRef name = "_GEN_") {
    return getEscapedName(moduleNameSpace.newName(name));
  }

  ResultTy visitStmt(OutputOp op) {
    assert(op.getNumOperands() == outputs.size());
    for (auto [wire, op] : llvm::zip(outputs, op.getOperands())) {
      auto result = getValue(op);
      if (failed(result))
        return failure();
      rtlilModule->connect(Yosys::SigSpec(wire), result.value());
    }

    return ResultTySuccess;
  }

  /*
    ResultTy visitComb(MulOp op) {}
    ResultTy visitComb(DivUOp op) {}
    ResultTy visitComb(DivSOp op) {}
    ResultTy visitComb(ModUOp op) {}
    ResultTy visitComb(ModSOp op) {}
    ResultTy visitComb(ShlOp op) {}
    ResultTy visitComb(ShrUOp op) {}
    ResultTy visitComb(ShrSOp op) {}
    ResultTy visitComb(AndOp op) {};
      return emitVariadicOp(op, [&](auto name, auto l, auto r) {
        return rtlilModule->And(name, l, r);
      });
    }
    ResultTy visitComb(OrOp op) {
      return emitVariadicOp(op, [&](auto name, auto l, auto r) {
        return rtlilModule->Or(name, l, r);
      });
    }
    ResultTy visitComb(XorOp op) {}

    // SystemVerilog spec 11.8.1: "Reduction operator results are unsigned,
    // regardless of the operands."
    ResultTy visitComb(ParityOp op) {}
    */

  // ResultTy visitComb(ReplicateOp op);
  // ResultTy visitComb(ConcatOp op);
  // ResultTy visitComb(ExtractOp op);
  // ResultTy visitComb(ICmpOp op);

  LogicalResult run() {
    return LogicalResult::failure(
        module
            .walk<mlir::WalkOrder::PostOrder>([this](Operation *op) {
              // Skip zero result operatins.
              if (module == op)
                return WalkResult::advance();
              if (auto out = dyn_cast<hw::OutputOp>(op)) {
                auto result = visitStmt(out);
                if (failed(result))
                  return op->emitError() << "failed to lower",
                         WalkResult::interrupt();
                return WalkResult::advance();
              }
              return WalkResult::advance();
            })
            .wasInterrupted());
  }

  ModuleConverter(Yosys::RTLIL::Design *design,
                  Yosys::RTLIL::Module *rtlilModule, hw::HWModuleOp module)
      : design(design), rtlilModule(rtlilModule), module(module) {
    ModulePortInfo ports(module.getPortList());
    size_t inputPos = 0;
    for (auto [idx, port] : llvm::enumerate(ports)) {
      auto *wire = rtlilModule->addWire(getEscapedName(port.getName()));
      wire->port_id = idx + 1;
      auto bitWidth = hw::getBitWidth(port.type);
      assert(bitWidth >= 0);
      wire->width = bitWidth;
      if (port.isOutput()) {
        wire->port_output = true;
        outputs.push_back(wire);
      } else {
        setLowering(module.getBodyBlock()->getArgument(inputPos++),
                    Yosys::SigSpec(wire));
        // TODO: Need to consider inout?
        wire->port_input = true;
      }
    }
    // Need to call fixup ports after port mutations.
    rtlilModule->fixup_ports();
  }

  DenseMap<Value, SigSpec> mapping;
  SmallVector<RTLIL::Wire *> outputs;

  LogicalResult setLowering(Value value, SigSpec s) {
    return success(mapping.insert({value, s}).second);
  }

  Yosys::RTLIL::Design *design;
  Yosys::RTLIL::Module *rtlilModule;
  hw::HWModuleOp module;
  RTLIL::Wire *getWireForValue(Value value);
  RTLIL::Cell *getCellForValue(Value value);
};

FailureOr<SigSpec> ExprEmitter::getValue(Value value) {
  return moduleEmitter.getValue(value);
}

FailureOr<Yosys::SigSpec> ExprEmitter::visitComb(AddOp op) {
  return emitVariadicOp(op, [&](auto name, auto l, auto r) {
    return moduleEmitter.rtlilModule->Add(name, l, r);
  });
}

FailureOr<Yosys::SigSpec> ExprEmitter::visitComb(SubOp op) {
  return emitVariadicOp(op, [&](auto name, auto l, auto r) {
    return moduleEmitter.rtlilModule->Sub(name, l, r);
  });
}

RTLIL::IdString ExprEmitter::getNewName(StringRef name) {
  return moduleEmitter.getNewName(name);
}

} // namespace

void ExportYosysPass::runOnOperation() {
  auto *design = new Yosys::RTLIL::Design;
  Yosys::log_streams.push_back(&std::cout);
	Yosys::log_error_stderr = true;
  Yosys::yosys_setup();
  SmallVector<ModuleConverter> converter;
  for (auto op : getOperation().getOps<hw::HWModuleOp>()) {
    auto *newModule = design->addModule(getEscapedName(op.getModuleName()));
    converter.emplace_back(design, newModule, op);
  }
  for (auto &c : converter)
    if (failed(c.run()))
      signalPassFailure();

  RTLIL_BACKEND::dump_design(std::cout, design, false);
  // Yosys::run_pass("synth;write_verilog synth.v", design);
  Yosys::shell(design);

  RTLIL_BACKEND::dump_design(std::cout, design, false);
}

//===----------------------------------------------------------------------===//
// Pass Infrastructure
//===----------------------------------------------------------------------===//
std::unique_ptr<mlir::Pass> circt::createExportYosys() {
  return std::make_unique<ExportYosysPass>();
}
