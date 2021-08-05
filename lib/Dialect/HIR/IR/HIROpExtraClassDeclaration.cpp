//=========- HIROpExtraClassDecl.cpp - extraClassDeclarations for Ops -----===//
//
// This file implements the extraClassDeclarations for HIR ops.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/HIR/IR/HIR.h"
#include "circt/Dialect/HIR/IR/HIRDialect.h"

using namespace circt;
using namespace hir;

namespace {
SmallVector<Value> filterIndices(DimKind idxKind, OperandRange indices,
                                 ArrayRef<DimKind> dimKinds) {
  SmallVector<Value> addrIndices;
  for (size_t i = 0; i < indices.size(); i++) {
    if (dimKinds[i] == idxKind) {
      auto idx = indices[i];
      addrIndices.push_back(idx);
    }
  }
  return addrIndices;
}
} // namespace
SmallVector<Value> LoadOp::filterIndices(DimKind idxKind) {

  OperandRange indices = this->indices();
  auto dimKinds =
      this->mem().getType().dyn_cast<hir::MemrefType>().getDimKinds();
  return ::filterIndices(idxKind, indices, dimKinds);
}

SmallVector<Value> StoreOp::filterIndices(DimKind idxKind) {

  OperandRange indices = this->indices();
  auto dimKinds =
      this->mem().getType().dyn_cast<hir::MemrefType>().getDimKinds();
  return ::filterIndices(idxKind, indices, dimKinds);
}

SmallVector<Value, 4> hir::FuncOp::getOperands() {
  SmallVector<Value, 4> operands;

  auto &entryBlock = this->getFuncBody().front();
  for (Value arg :
       entryBlock.getArguments().slice(0, entryBlock.getNumArguments() - 1))
    operands.push_back(arg);
  return operands;
}

SmallVector<Value, 4> hir::CallOp::getOperands() {
  SmallVector<Value, 4> operands;
  for (Value arg : this->operands().slice(0, this->getNumOperands() - 1))
    operands.push_back(arg);
  return operands;
}

void hir::FuncOp::updateArguments(ArrayRef<DictionaryAttr> inputAttrs) {
  auto &entryBlock = this->getFuncBody().front();
  SmallVector<Type> inputTypes;
  for (uint64_t i = 0; i < entryBlock.getNumArguments() - 1; i++) {
    auto ty = entryBlock.getArgumentTypes()[i];
    inputTypes.push_back(ty);
  }
  assert(inputTypes.size() == inputAttrs.size() ||
         succeeded(this->emitError("Mismatch in number of types and attrs")));

  auto newFuncTy =
      hir::FuncType::get(this->getContext(), inputTypes, inputAttrs,
                         this->getFuncType().getResultTypes(),
                         this->getFuncType().getResultAttrs());

  this->typeAttr(TypeAttr::get(newFuncTy.getFunctionType()));
  this->funcTyAttr(TypeAttr::get(newFuncTy));
  this->setAllArgAttrs(inputAttrs);
}
