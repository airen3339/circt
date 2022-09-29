//===- circt-lec.cpp - The circt-lec driver ---------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// This file initiliazes the 'circt-lec' tool, which interfaces with a logical
/// engine to allow its user to check whether two input circuit descriptions
/// are equivalent, and when not provides a counterexample as for why.
///
//===----------------------------------------------------------------------===//

#include "LogicExporter.h"
#include "Solver.h"
#include "Utility.h"
#include "circt/InitAllDialects.h"
#include "circt/Support/Version.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/OwningOpRef.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "mlir/Support/LogicalResult.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/SourceMgr.h"

namespace cl = llvm::cl;

//===----------------------------------------------------------------------===//
// Command-line options declaration
//===----------------------------------------------------------------------===//

static cl::OptionCategory mainCategory("circt-lec Options");

static cl::opt<std::string> moduleName1(
    "c1",
    cl::desc("Specify a named module for the first circuit of the comparison"),
    cl::value_desc("module name"), cl::cat(mainCategory));

static cl::opt<std::string> moduleName2(
    "c2",
    cl::desc("Specify a named module for the second circuit of the comparison"),
    cl::value_desc("module name"), cl::cat(mainCategory));

static cl::opt<std::string> fileName1(cl::Positional, cl::Required,
                                      cl::desc("<input file>"),
                                      cl::cat(mainCategory));

static cl::opt<std::string> fileName2(cl::Positional, cl::desc("[input file]"),
                                      cl::cat(mainCategory));

// The following options are stored externally for their value to be accessible
// to other components of the tool; see `Utility.h` for more definitions.
bool verboseOpt;
static cl::opt<bool, true>
    verbose("v", cl::location(verboseOpt), cl::init(false),
            cl::desc("Print extensive execution progress information"),
            cl::cat(mainCategory));

bool statisticsOpt;
static cl::opt<bool, true> statistics(
    "s", cl::location(statisticsOpt), cl::init(false),
    cl::desc("Print statistics about the logical engine's execution"),
    cl::cat(mainCategory));

//===----------------------------------------------------------------------===//
// Tool implementation
//===----------------------------------------------------------------------===//

/// This functions initializes the various components of the tool and
/// orchestrates the work to be done. It first parses the input files, then it
/// runs a pass to export the logical constraints from the given circuit
/// description to an internal circuit representation, lastly, these will be
/// compared and solved for equivalence.
static mlir::LogicalResult executeLEC(mlir::MLIRContext &context) {
  // Parse the provided input files.
  VERBOSE(lec::outs << "Parsing input file\n");
  mlir::OwningOpRef<circt::ModuleOp> file1 =
      mlir::parseSourceFile<mlir::ModuleOp>(fileName1, &context);
  if (!file1)
    return circt::failure();

  mlir::OwningOpRef<mlir::ModuleOp> file2;
  if (!fileName2.empty()) {
    VERBOSE(lec::outs << "Parsing second input file\n");
    file2 = mlir::parseSourceFile<circt::ModuleOp>(fileName2, &context);
    if (!file2)
      return circt::failure();
  } else
    VERBOSE(lec::outs << "Second input file not specified\n");

  // Initiliaze the constraints solver and the circuits to be compared.
  Solver s;
  Solver::Circuit *c1 = s.addCircuit(moduleName1, true);
  Solver::Circuit *c2 = s.addCircuit(moduleName2, false);

  // Initialize the logic-exporting pass for the first circuit then run the
  // pass manager on the top-level module of the first input file.
  VERBOSE(lec::outs << "Analyzing the first circuit\n";);
  mlir::PassManager pm(&context);
  pm.addPass(std::make_unique<LogicExporter>(moduleName1, c1));
  circt::ModuleOp m = file1.get();
  if (failed(pm.run(m)))
    return circt::failure();

  // Repeat the same procedure for the second circuit.
  VERBOSE(lec::outs << "Analyzing the second circuit\n");
  mlir::PassManager pm2(&context);
  pm2.addPass(std::make_unique<LogicExporter>(moduleName2, c2));
  // In case a second input file was not specified, the first input file will
  // be used instead.
  circt::ModuleOp m2 = fileName2.empty() ? m : file2.get();
  if (failed(pm2.run(m2)))
    return mlir::failure();

  // The logical constraints have been exported to their respective circuit
  // representations and can now be solved for equivalence.
  VERBOSE(lec::outs << "Solving constraints\n");
  return s.solve();
}

/// The entry point for the `circt-lec` tool:
/// configures and parses the command-line options,
/// registers all dialects within a MLIR context,
/// and calls the `executeLEC` function to do the actual work.
int main(int argc, char **argv) {
  // Configure the relevant command-line options.
  cl::HideUnrelatedOptions(mainCategory);
  mlir::registerMLIRContextCLOptions();
  cl::AddExtraVersionPrinter(
      [](llvm::raw_ostream &os) { os << circt::getCirctVersion() << '\n'; });

  // Parse the command-line options provided by the user.
  cl::ParseCommandLineOptions(
      argc, argv,
      "circt-lec - logical equivalence checker\n\n"
      "\tThis tool compares two input circuit descriptions to determine whether"
      " they are logically equivalent.\n");

  // Register all the CIRCT dialects and create a context to work with.
  mlir::DialectRegistry registry;
  circt::registerAllDialects(registry);
  mlir::MLIRContext context(registry);

  // Setup of diagnostic handling.
  llvm::SourceMgr sourceMgr;
  mlir::SourceMgrDiagnosticHandler sourceMgrHandler(sourceMgr, &context);
  // Avoid printing a superfluous note on diagnostic emission.
  context.printOpOnDiagnostic(false);

  // Perform the logical equivalence checking; using `exit` to avoid the slow
  // teardown of the MLIR context.
  VERBOSE(lec::outs << "Starting execution\n");
  exit(failed(executeLEC(context)));
}
