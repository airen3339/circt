// REQUIRES: verilator
// RUN: circt-rtl-sim.py --cycles 2 %s | FileCheck %s

module top(
  input clk,
  input rstn
);

  always@(posedge clk)
    if (rstn)
      $display("tock");
  // CHECK:      tock
  // CHECK-NEXT: tock

endmodule
