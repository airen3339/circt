// REQUIRES: iverilog,cocotb

// This test is executed with all different buffering strategies

// RUN: hlstool %s --dynamic-firrtl --ir-input-level 1 --verilog --lowering-options=disallowLocalVariables > %t.sv && \
// RUN: %PYTHON% %S/../cocotb_driver.py --objdir=%T --topLevel=top --pythonModule=tuple_input --pythonFolder=%S %t.sv 2>&1 | FileCheck %s

// RUN: circt-opt %s \
// RUN:   --canonicalize='top-down=true region-simplify=true' \
// RUN:   --handshake-materialize-forks-sinks --canonicalize \
// RUN:   --handshake-insert-buffers=strategy=allFIFO --lower-handshake-to-firrtl | \
// RUN: firtool --format=mlir --verilog --lowering-options=disallowLocalVariables > %t.sv && \
// RUN: %PYTHON% %S/../cocotb_driver.py --objdir=%T --topLevel=top --pythonModule=tuple_input --pythonFolder=%S %t.sv 2>&1 | FileCheck %s

// RUN: circt-opt %s \
// RUN:   --canonicalize='top-down=true region-simplify=true' \
// RUN:   --handshake-materialize-forks-sinks --canonicalize \
// RUN:   --handshake-insert-buffers=strategy=cycles --lower-handshake-to-firrtl | \
// RUN: firtool --format=mlir --verilog --lowering-options=disallowLocalVariables > %t.sv && \
// RUN: %PYTHON% %S/../cocotb_driver.py --objdir=%T --topLevel=top --pythonModule=tuple_input --pythonFolder=%S %t.sv 2>&1 | FileCheck %s

// CHECK: ** TEST
// CHECK: ** TESTS=[[N:.*]] PASS=[[N]] FAIL=0 SKIP=0

module {
  handshake.func @top(%arg0: tuple<i32, i32>, %arg1: none, ...) -> (i32, none) attributes {argNames = ["in0", "inCtrl"], resNames = ["out0", "outCtrl"]} {
    %res:2 = handshake.unpack %arg0 : tuple<i32, i32>
    %sum = arith.addi %res#0, %res#1 : i32
    return %sum, %arg1 : i32, none
  }
}

