// REQUIRES: ieee-sim

// RUN: circt-opt %s \ 
// RUN:   --canonicalize='top-down=true region-simplify=true' \
// RUN:   --handshake-materialize-forks-sinks --canonicalize \
// RUN:   --handshake-insert-buffers=strategy=all --lower-handshake-to-firrtl | \
// RUN: firtool --format=mlir --verilog --lowering-options=disallowLocalVariables > %t.sv && \
// RUN: circt-rtl-sim.py %t.sv %S/driver.sv --sim %ieee-sim --no-default-driver --top driver | FileCheck %s
// CHECK: Result={{.*}}579

module {
  handshake.func @top(%arg0: none, ...) -> (i32, none) attributes {argNames = ["inCtrl"], resNames = ["out0", "outCtrl"]} {
    %0:4 = fork [4] %arg0 : none
    %const0 = constant %0#0 {value = 123 : i32} : i32
    %const1 = constant %0#1 {value = 456 : i32} : i32
    %const2 = constant %0#2 {value = 0 : i32} : i32

    %tuple = handshake.pack %const0, %const1, %const2 : tuple<i32, i32, i32>
    %res:3 = handshake.unpack %tuple : tuple<i32, i32, i32>

    %sum = arith.addi %res#0, %res#1 : i32
    sink %res#2 : i32

    return %sum, %0#3 : i32, none
  }
}
