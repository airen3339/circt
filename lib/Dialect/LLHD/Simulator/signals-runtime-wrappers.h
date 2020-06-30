#ifndef CIRCT_DIALECT_LLHD_SIMULATOR_SIGNALS_RUNTIME_WRAPPERS_H
#define CIRCT_DIALECT_LLHD_SIMULATOR_SIGNALS_RUNTIME_WRAPPERS_H

#include "State.h"

extern "C" {

//===----------------------------------------------------------------------===//
// Runtime interfaces
//===----------------------------------------------------------------------===//

/// Allocate a new signal. The index of the new signal in the state's list of
/// signals is returned.
int alloc_signal(mlir::llhd::sim::State *state, int index, char *owner,
                 uint8_t *value, int64_t size);

/// Add allocated constructs to a process instance.
void alloc_proc(mlir::llhd::sim::State *state, char *owner,
                mlir::llhd::sim::ProcState *procState);

/// Gather information of the signal at index.
mlir::llhd::sim::SignalDetail *probe_signal(mlir::llhd::sim::State *state,
                                            int index);

/// Drive a value onto a signal.
void drive_signal(mlir::llhd::sim::State *state, int index, uint8_t *value,
                  uint64_t width, int time, int delta, int eps);

/// Add a temporary subsignal to the global signal table
int add_subsignal(mlir::llhd::sim::State *state, int origin, uint8_t *ptr,
                  uint64_t len, uint64_t offset);

/// Suspend a process
void llhd_suspend(mlir::llhd::sim::State *state,
                  mlir::llhd::sim::ProcState *procState, int time, int delta,
                  int eps);
}

#endif // CIRCT_DIALECT_LLHD_SIMULATOR_SIGNALS_RUNTIME_WRAPPERS_H
