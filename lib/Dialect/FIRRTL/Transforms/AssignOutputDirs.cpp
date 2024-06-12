//===- AssignOutputDirs.cpp - Assign Output Directories ---------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "PassDetails.h"
#include "circt/Dialect/FIRRTL/AnnotationDetails.h"
#include "circt/Dialect/FIRRTL/FIRRTLAnnotations.h"
#include "circt/Dialect/FIRRTL/FIRRTLInstanceGraph.h"
#include "circt/Dialect/FIRRTL/Passes.h"
#include "circt/Dialect/HW/HWAttributes.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"

#define DEBUG_TYPE "firrtl-assign-output-dirs"

using namespace circt;
using namespace firrtl;
namespace path = llvm::sys::path;
namespace fs = llvm::sys::fs;

using hw::OutputFileAttr;

// if moduleOutputDir is a relative path, convert it to an absolute path, by
// interpreting moduleOutputDir as relative to the outputDir.
static void makeAbsolute(StringRef outputDir,
                         SmallString<64> &moduleOutputDir) {
  fs::make_absolute(outputDir, moduleOutputDir);
  path::remove_dots(moduleOutputDir, true);
}

// if outputDir is a prefix of moduleOutputDir, then make moduleOutputDir
// relative to outputDir. Otherwise, leave moduleOutputDir as absolute.
static void makeRelative(StringRef outputDir,
                         SmallString<64> &moduleOutputDir) {
  if (moduleOutputDir.starts_with(outputDir))
    moduleOutputDir.erase(moduleOutputDir.begin(),
                          moduleOutputDir.begin() + outputDir.size());
}

static void makeCommonPrefix(SmallString<64> &a, StringRef b) {
  // truncate 'a' to the common prefix of 'a' and 'b'.
  size_t i = 0;
  size_t e = std::min(a.size(), b.size());
  for (; i < e; ++i)
    if (a[i] != b[i])
      break;
  a.resize(i);

  // truncate 'a' so it ends on a directory seperator.
  auto sep = path::get_separator();
  while (!a.empty() && !a.ends_with(sep))
    a.pop_back();
}

static void makeCommonPrefix(StringRef outputDir, SmallString<64> &a,
                             OutputFileAttr attr) {
  if (attr) {
    SmallString<64> b(attr.getFilename());
    makeAbsolute(outputDir, b);
    makeCommonPrefix(a, b);
  } else {
    makeCommonPrefix(a, outputDir);
  }
}

static OutputFileAttr getOutputFile(Operation *op) {
  return op->getAttrOfType<hw::OutputFileAttr>("output_file");
}

namespace {
class AssignOutputDirsPass : public AssignOutputDirsBase<AssignOutputDirsPass> {
  void runOnOperation() override;
};
} // namespace

void AssignOutputDirsPass::runOnOperation() {
  SmallString<64> outputDir(outputDirOption);
  if (fs::make_absolute(outputDir)) {
    signalPassFailure();
    return;
  }

  auto sep = path::get_separator();
  if (!outputDir.ends_with(sep))
    outputDir.append(sep);

  bool changed = false;

  DenseSet<InstanceGraphNode *> visited;
  for (auto *root : getAnalysis<InstanceGraph>()) {
    for (auto *node : llvm::inverse_post_order_ext(root, visited)) {
      auto module = dyn_cast<FModuleOp>(node->getModule().getOperation());
      if (!module || module->getAttrOfType<hw::OutputFileAttr>("output_file") ||
          module.isPublic())
        continue;

      // Get the output directory of the first parent, and then fold the current
      // output directory with the LCA of all other discovered output
      // directories.
      SmallString<64> moduleOutputDir;
      auto i = node->usesBegin();
      auto e = node->usesEnd();
      for (; i != e; ++i) {
        if (auto parent = dyn_cast<FModuleOp>((*i)->getParent()->getModule())) {
          auto file = getOutputFile(parent);
          if (file) {
            moduleOutputDir = file.getDirectory();
            makeAbsolute(outputDir, moduleOutputDir);
          } else {
            moduleOutputDir = outputDir;
          }
          ++i;
          break;
        }
      }
      for (; i != e; ++i) {
        if (auto parent =
                dyn_cast<FModuleOp>((*i)->getParent()->getModule<FModuleOp>()))
          makeCommonPrefix(outputDir, moduleOutputDir, getOutputFile(parent));
      }

      makeRelative(outputDir, moduleOutputDir);
      if (!moduleOutputDir.empty()) {
        auto f =
            hw::OutputFileAttr::getAsDirectory(&getContext(), moduleOutputDir);
        module->setAttr("output_file", f);
        changed = true;
      }
    }
  }

  if (!changed)
    markAllAnalysesPreserved();
}

std::unique_ptr<mlir::Pass> circt::firrtl::createAssignOutputDirsPass() {
  return std::make_unique<AssignOutputDirsPass>();
}
