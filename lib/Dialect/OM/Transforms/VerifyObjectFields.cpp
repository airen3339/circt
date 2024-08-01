//===- VerifyObjectFields.cpp - Verify Object fields -------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Contains the definitions of the OM verify object fields pass.
//
//===----------------------------------------------------------------------===//

#include "circt/Dialect/HW/HWInstanceGraph.h"
#include "circt/Dialect/HW/HWOps.h"
#include "circt/Dialect/HW/InnerSymbolTable.h"
#include "circt/Dialect/OM/OMAttributes.h"
#include "circt/Dialect/OM/OMOps.h"
#include "circt/Dialect/OM/OMPasses.h"
#include "mlir/IR/Threading.h"
#include "mlir/Pass/Pass.h"
#include "llvm/ADT/DenseMap.h"

namespace circt {
namespace om {
#define GEN_PASS_DEF_VERIFYOBJECTFIELDS
#include "circt/Dialect/OM/OMPasses.h.inc"
} // namespace om
} // namespace circt

using namespace mlir;
using namespace circt;
using namespace om;

namespace {
struct VerifyObjectFieldsPass
    : public circt::om::impl::VerifyObjectFieldsBase<VerifyObjectFieldsPass> {
  void runOnOperation() override;
  bool canScheduleOn(RegisteredOperationName opName) const override {
    return opName.getStringRef() == "firrtl.circuit" ||
           opName.getStringRef() == "builtin.module";
  }
};
} // namespace

void VerifyObjectFieldsPass::runOnOperation() {
  auto *module = getOperation();
  assert(module->getNumRegions() == 1 &&
         module->hasTrait<OpTrait::SymbolTable>() &&
         "op must have a single region and symbol table trait");
  auto &symbolTable = getAnalysis<SymbolTable>();

  /// A map from a class and field name to a field.
  llvm::MapVector<ClassLike, llvm::DenseMap<StringAttr, Type>> tables;
  for (auto op : module->getRegion(0).getOps<om::ClassLike>())
    tables.insert({op, llvm::DenseMap<StringAttr, Type>()});

  // Peel tables parallelly.
  if (failed(
          mlir::failableParallelForEach(&getContext(), tables, [](auto &entry) {
            ClassLike classLike = entry.first;
            auto &table = entry.second;
            std::optional<llvm::MapVector<mlir::StringAttr, mlir::Type>>
                fieldTypes = classLike.getFieldTypes();
            if (!fieldTypes.has_value()) {
              return LogicalResult::failure();
            }
            for (auto [name, type] : fieldTypes.value()) {
              table.insert({name, type});
            }
            return LogicalResult::success();
          })))
    return signalPassFailure();

  // Run actual verification. Make sure not to mutate `tables`.
  auto result = mlir::failableParallelForEach(
      &getContext(), tables, [&tables, &symbolTable](const auto &entry) {
        ClassLike classLike = entry.first;
        auto result =
            classLike.walk([&](ObjectFieldOp objectField) -> WalkResult {
              auto objectInstType =
                  cast<ClassType>(objectField.getObject().getType());
              ClassLike classDef =
                  symbolTable.lookupNearestSymbolFrom<ClassLike>(
                      objectField, objectInstType.getClassName());
              if (!classDef) {
                objectField.emitError()
                    << "class " << objectInstType.getClassName()
                    << " was not found";
                return WalkResult::interrupt();
              }

              // Traverse the field path, verifying each field exists.
              Type finalFieldType;
              auto fields = SmallVector<FlatSymbolRefAttr>(
                  objectField.getFieldPath().getAsRange<FlatSymbolRefAttr>());
              for (size_t i = 0, e = fields.size(); i < e; ++i) {
                // Verify the field exists on the ClassOp.
                auto field = fields[i];
                auto *it = tables.find(classDef);
                assert(it != tables.end() && "must be visited");
                Type fieldType = it->second.lookup(field.getAttr());

                if (!fieldType) {
                  auto error =
                      objectField.emitOpError("referenced non-existent field ")
                      << field;
                  error.attachNote(classDef.getLoc()) << "class defined here";
                  return WalkResult::interrupt();
                }

                // If there are more fields, verify the current field is of
                // ClassType, and look up the ClassOp for that field.
                if (i < e - 1) {
                  auto classType = dyn_cast<ClassType>(fieldType);
                  if (!classType) {
                    objectField.emitOpError("nested field access into ")
                        << field << " requires a ClassType, but found "
                        << fieldType;
                    return WalkResult::interrupt();
                  }

                  // Check if the nested ClassOp exists. ObjectInstOp verifier
                  // already checked the class exits but it's not verified yet
                  // if the object is an input argument.
                  classDef = symbolTable.lookupNearestSymbolFrom<ClassOp>(
                      objectField, classType.getClassName());

                  if (!classDef) {
                    objectField.emitError()
                        << "class " << classType.getClassName()
                        << " was not found";
                    return WalkResult::interrupt();
                  }

                  // Proceed to the next field in the path.
                  continue;
                }

                // On the last iteration down the path, save the final field
                // being accessed.
                finalFieldType = fieldType;
              }

              // Verify the accessed field type matches the result type.
              if (finalFieldType != objectField.getResult().getType()) {
                objectField.emitOpError("expected type ")
                    << objectField.getResult().getType()
                    << ", but accessed field has type " << finalFieldType;

                return WalkResult::interrupt();
              }
              return WalkResult::advance();
            });
        return LogicalResult::failure(result.wasInterrupted());
      });
  if (failed(result))
    return signalPassFailure();
  return markAllAnalysesPreserved();
}

std::unique_ptr<mlir::Pass> circt::om::createVerifyObjectFieldsPass() {
  return std::make_unique<VerifyObjectFieldsPass>();
}
