// RUN: circt-opt -pass-pipeline='builtin.module(firrtl.circuit(firrtl.module(firrtl-strict-wires)))' %s | FileCheck %s

firrtl.circuit "TopLevel" {

  // CHECK-LABEL: @TopLevel
  firrtl.module @TopLevel(in %source: !firrtl.bundle<valid: uint<1>, ready: uint<1>, data: uint<64>>,
                             out %sink: !firrtl.bundle<valid: uint<1>, ready: uint<1>, data: uint<64>>) {
    %w = firrtl.wire : !firrtl.bundle<valid: uint<1>, ready: uint<1>, data: uint<64>>
    firrtl.matchingconnect %w, %source : !firrtl.bundle<valid: uint<1>, ready: uint<1>, data: uint<64>>
    firrtl.matchingconnect %sink, %w : !firrtl.bundle<valid: uint<1>, ready: uint<1>, data: uint<64>>

// CHECK: %w, %w_write = firrtl.strictwire : !firrtl.bundle<valid: uint<1>, ready: uint<1>, data: uint<64>> 
// CHECK: firrtl.strictconnect %w_write, %source : !firrtl.bundle<valid: uint<1>, ready: uint<1>, data: uint<64>> 
// CHECK: firrtl.matchingconnect %sink, %w : !firrtl.bundle<valid: uint<1>, ready: uint<1>, data: uint<64>> 
  }

  // CHECK-LABEL: @Subfield
  firrtl.module @Subfield(in %source: !firrtl.uint<1>,
                             out %sink: !firrtl.uint<1>) {
    %w = firrtl.wire : !firrtl.bundle<valid: uint<1>>
    %w_valid = firrtl.subfield %w[valid] : !firrtl.bundle<valid: uint<1>>
    firrtl.matchingconnect %w_valid, %source : !firrtl.uint<1>
    firrtl.matchingconnect %sink, %w_valid : !firrtl.uint<1>

// CHECK: %w, %w_write = firrtl.strictwire : !firrtl.bundle<valid: uint<1>> 
// CHECK: %0 = firrtl.lhssubfield %w_write[valid] : !firrtl.lhs<bundle<valid: uint<1>>> 
// CHECK: %1 = firrtl.subfield %w[valid] : !firrtl.bundle<valid: uint<1>> 
// CHECK: firrtl.strictconnect %0, %source : !firrtl.uint<1>
// CHECK: firrtl.matchingconnect %sink, %1 : !firrtl.uint<1>
  }

  // CHECK-LABEL: @Subindex
  firrtl.module @Subindex(in %source: !firrtl.uint<1>,
                             out %sink: !firrtl.uint<1>) {
    %w = firrtl.wire : !firrtl.vector<uint<1>,1>
    %w_valid = firrtl.subindex %w[0] : !firrtl.vector<uint<1>,1>
    firrtl.matchingconnect %w_valid, %source : !firrtl.uint<1>
    firrtl.matchingconnect %sink, %w_valid : !firrtl.uint<1>

// CHECK: %w, %w_write = firrtl.strictwire : !firrtl.vector<uint<1>, 1> 
// CHECK: %0 = firrtl.lhssubindex %w_write[0] : !firrtl.lhs<vector<uint<1>, 1>> 
// CHECK: %1 = firrtl.subindex %w[0] : !firrtl.vector<uint<1>, 1> 
// CHECK: firrtl.strictconnect %0, %source : !firrtl.uint<1>
// CHECK: firrtl.matchingconnect %sink, %1 : !firrtl.uint<1>
  }


    // CHECK-LABEL: @Inst
  firrtl.module @Inst(in %source: !firrtl.uint<1>,
                             out %sink: !firrtl.uint<1>) {
    %s_source, %s_sink = firrtl.instance s @Subfield(in source : !firrtl.uint<1>, out sink : !firrtl.uint<1>)
    firrtl.matchingconnect %s_source, %source : !firrtl.uint<1>
    firrtl.matchingconnect %sink, %s_sink : !firrtl.uint<1>

// CHECK: %s_source, %s_sink = firrtl.strictinstance s @Subfield(in source: !firrtl.uint<1>, out sink: !firrtl.uint<1>) 
// CHECK: firrtl.strictconnect %s_source, %source : !firrtl.uint<1> 
// CHECK: firrtl.matchingconnect %sink, %s_sink : !firrtl.uint<1> 
  }


}
