// RUN: circt-opt -pass-pipeline='builtin.module(firrtl.circuit(firrtl-imconstprop), canonicalize{top-down region-simplify}, firrtl.circuit(firrtl.module(firrtl-register-optimizer)))'  %s | FileCheck %s
// XFAIL: *

// These depend on more than constant prop.  They need to move.

  // CHECK-LABEL: firrtl.module @padZeroReg
  firrtl.module @padZeroReg(in %clock: !firrtl.clock, out %z: !firrtl.uint<16>) {
      %_r = firrtl.reg droppable_name %clock  :  !firrtl.uint<8>
      firrtl.strictconnect %_r, %_r : !firrtl.uint<8>
      %c171_ui8 = firrtl.constant 171 : !firrtl.uint<8>
      %_n = firrtl.node droppable_name %c171_ui8  : !firrtl.uint<8>
      %1 = firrtl.cat %_n, %_r : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
      firrtl.strictconnect %z, %1 : !firrtl.uint<16>
    // CHECK: %[[TMP:.+]] = firrtl.constant 43776 : !firrtl.uint<16>
    // CHECK-NEXT: firrtl.strictconnect %z, %[[TMP]] : !firrtl.uint<16>
  }
}


// should "pad constant connections to outputs when propagating"
firrtl.circuit "padConstOut"   {
  firrtl.module private @padConstOutChild(out %x: !firrtl.uint<8>) {
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    firrtl.connect %x, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
  }
  // CHECK-LABEL: firrtl.module @padConstOut
  firrtl.module @padConstOut(out %z: !firrtl.uint<16>) {
    %c_x = firrtl.instance c @padConstOutChild(out x: !firrtl.uint<8>)
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    %0 = firrtl.cat %c3_ui2, %c_x : (!firrtl.uint<2>, !firrtl.uint<8>) -> !firrtl.uint<10>
    // CHECK: %[[C8:.+]] = firrtl.constant 771 : !firrtl.uint<16>
    // CHECK: firrtl.strictconnect %z, %[[C8]] : !firrtl.uint<16>
    firrtl.connect %z, %0 : !firrtl.uint<16>, !firrtl.uint<10>
  }
}

//"pad constant connections to wires when propagating"
firrtl.circuit "padConstWire"   {
  // CHECK-LABEL: firrtl.module @padConstWire
  firrtl.module @padConstWire(out %z: !firrtl.uint<16>) {
    %_w_a = firrtl.wire droppable_name  : !firrtl.uint<8>
    %_w_b = firrtl.wire droppable_name : !firrtl.uint<8>
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    firrtl.connect %_w_a, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
    firrtl.connect %_w_b, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
    %0 = firrtl.cat %_w_a, %_w_b : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
    firrtl.strictconnect %z, %0 : !firrtl.uint<16>
    // CHECK: %[[C6:.+]] = firrtl.constant 771 : !firrtl.uint<16>
    // CHECK-NEXT: firrtl.strictconnect %z, %[[C6]] : !firrtl.uint<16>
  }
}

// "pad constant connections to registers when propagating"
firrtl.circuit "padConstReg"   {
  // CHECK-LABEL: firrtl.module @padConstReg
  firrtl.module @padConstReg(in %clock: !firrtl.clock, out %z: !firrtl.uint<16>) {
    %r_a = firrtl.reg droppable_name %clock  :  !firrtl.uint<8>
    %r_b = firrtl.reg droppable_name %clock  :  !firrtl.uint<8>
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<8>
    firrtl.connect %r_a, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<8>
    firrtl.connect %r_b, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<8>
    %0 = firrtl.cat %r_a, %r_b : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
    firrtl.strictconnect %z, %0 : !firrtl.uint<16>
    // CHECK: %[[C6:.+]] = firrtl.constant 771 : !firrtl.uint<16>
    // CHECK-NEXT: firrtl.strictconnect %z, %[[C6]] : !firrtl.uint<16>
  }
}

// "pad constant connections to submodule inputs when propagating"
firrtl.circuit "padConstIn"   {
  // CHECK-LABEL: firrtl.module private @padConstInChild
  firrtl.module private @padConstInChild(in %x: !firrtl.uint<8>, out %y: !firrtl.uint<16>) {
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    %0 = firrtl.cat %c3_ui2, %x : (!firrtl.uint<2>, !firrtl.uint<8>) -> !firrtl.uint<10>
    // CHECK: %[[C9:.+]] = firrtl.constant 771 : !firrtl.uint<16>
    // CHECK: firrtl.strictconnect %y, %[[C9]] : !firrtl.uint<16>
    firrtl.connect %y, %0 : !firrtl.uint<16>, !firrtl.uint<10>
  }
  // CHECK-LABEL: firrtl.module @padConstIn
  firrtl.module @padConstIn(out %z: !firrtl.uint<16>) {
    %c_x, %c_y = firrtl.instance c @padConstInChild(in x: !firrtl.uint<8>, out y: !firrtl.uint<16>)
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    firrtl.connect %c_x, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
    firrtl.strictconnect %z, %c_y : !firrtl.uint<16>
    // CHECK: %[[C10:.+]] = firrtl.constant 771 : !firrtl.uint<16>
    // CHECK: firrtl.strictconnect %z, %[[C10]] : !firrtl.uint<16>
  }
}


//"Const prop of registers" should "do limited speculative expansion of optimized muxes to absorb bigger cones"
firrtl.circuit "constPropRegMux"   {
  // CHECK-LABEL: firrtl.module @constPropRegMux
  firrtl.module @constPropRegMux(in %clock: !firrtl.clock, in %en: !firrtl.uint<1>, out %out: !firrtl.uint<1>) {
  %r1 = firrtl.reg %clock  : !firrtl.uint<1>
  %r2 = firrtl.reg %clock  : !firrtl.uint<1>
  %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
  %0 = firrtl.mux(%en, %c1_ui1, %r1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.strictconnect %r1, %0 : !firrtl.uint<1>
  %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  %1 = firrtl.mux(%en, %r2, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.strictconnect %r2, %1 : !firrtl.uint<1>
  %2 = firrtl.xor %r1, %r2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  firrtl.strictconnect %out, %2 : !firrtl.uint<1>
    // CHECK: %[[C23:.+]] = firrtl.constant 1
    // CHECK: firrtl.strictconnect %out, %[[C23]]
  }
}


//"Registers with ONLY constant connection" should "be replaced with that constant"
firrtl.circuit "constReg2"   {
  // CHECK-LABEL: firrtl.module @constReg2
  firrtl.module @constReg2(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, out %z: !firrtl.sint<8>) {
    %r = firrtl.reg %clock  :  !firrtl.clock, !firrtl.sint<8>
    %c-5_si4 = firrtl.constant -5 : !firrtl.sint<4>
    firrtl.connect %r, %c-5_si4 : !firrtl.sint<8>, !firrtl.sint<4>
    firrtl.strictconnect %z, %r : !firrtl.sint<8>
    // CHECK: %[[C12:.+]] = firrtl.constant -5 : !firrtl.sint<8>
    // CHECK: firrtl.strictconnect %z, %[[C12]] : !firrtl.sint<8>
  }
}
