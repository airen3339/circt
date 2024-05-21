// RUN: circt-opt -pass-pipeline='builtin.module(firrtl.circuit(firrtl.module(firrtl-eliminate-wires)))' --allow-unregistered-dialect %s | FileCheck %s

firrtl.circuit "TopLevel" {

  // CHECK-LABEL: @TopLevel
  firrtl.module @TopLevel(in %source: !firrtl.uint<1>, 
                             out %sink: !firrtl.uint<1>) {
    // CHECK-NOT: firrtl.wire
    %w = firrtl.wire : !firrtl.uint<1>
    firrtl.strictconnect %w, %source : !firrtl.uint<1>
    %wn = firrtl.not %w : (!firrtl.uint<1>) -> !firrtl.uint<1>
    %x = firrtl.wire : !firrtl.uint<1>
    firrtl.strictconnect %x, %wn : !firrtl.uint<1>
    firrtl.strictconnect %sink, %x : !firrtl.uint<1>
    firrtl.strictconnect %sink, %w : !firrtl.uint<1>
  }

  // CHECK-LABEL: @Foo
  firrtl.module private @Foo() {
    %a = firrtl.wire : !firrtl.uint<3>
    %b = firrtl.wire : !firrtl.uint<3>
    %invalid_ui3 = firrtl.invalidvalue : !firrtl.uint<3>
    firrtl.strictconnect %b, %invalid_ui3 : !firrtl.uint<3>
    firrtl.strictconnect %a, %b : !firrtl.uint<3>
    // CHECK: %[[inv:.*]] = firrtl.invalidvalue : !firrtl.uint<3>
    // CHECK-NEXT:  %b = firrtl.node %[[inv]] : !firrtl.uint<3>
    // CHECK-NEXT:  %a = firrtl.node %b : !firrtl.uint<3>
  }
}