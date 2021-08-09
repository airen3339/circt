// RUN: circt-opt -pass-pipeline='firrtl.circuit(firrtl-imconstprop)' -canonicalize='top-down=true region-simplify=true' %s | FileCheck %s

//propagate constant inputs  
firrtl.circuit "ConstInput"   {
  firrtl.module @ConstInput(in %x: !firrtl.uint<1>, out %z: !firrtl.uint<1>) {
    %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
    %c_in0, %c_in1, %c_out = firrtl.instance @Child  {name = "c"} : !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %c_in0, %x : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %c_in1, %c1_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %z, %c_out : !firrtl.uint<1>, !firrtl.uint<1>
  }
  // CHECK-LABEL: firrtl.module @Child
  firrtl.module @Child(in %in0: !firrtl.uint<1>, in %in1: !firrtl.uint<1>, out %out: !firrtl.uint<1>) {
    %0 = firrtl.and %in0, %in1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
    // CHECK: firrtl.connect %out, %in0 :
    firrtl.connect %out, %0 : !firrtl.uint<1>, !firrtl.uint<1>
  }
}

//propagate constant inputs ONLY if ALL instance inputs get the same value
firrtl.circuit "InstanceInput"   {
  // CHECK-LABEL: firrtl.module @Bottom1
  firrtl.module @Bottom1(in %in: !firrtl.uint<1>, out %out: !firrtl.uint<1>) {
      // CHECK: %c1_ui1 = firrtl.constant 1
      // CHECK: firrtl.connect %out, %c1_ui1
    firrtl.connect %out, %in : !firrtl.uint<1>, !firrtl.uint<1>
  }
  // CHECK-LABEL: firrtl.module @Child1
  firrtl.module @Child1(out %out: !firrtl.uint<1>) {
    %c1_ui = firrtl.constant 1 : !firrtl.uint
    %b0_in, %b0_out = firrtl.instance @Bottom1  {name = "b0"} : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %b0_in, %c1_ui : !firrtl.uint<1>, !firrtl.uint
    // CHECK: %[[C1:.+]] = firrtl.constant 1 :
    // CHECK: firrtl.connect %out, %[[C1]]
    firrtl.connect %out, %b0_out : !firrtl.uint<1>, !firrtl.uint<1>
  }
  // CHECK-LABEL:  firrtl.module @InstanceInput
  firrtl.module @InstanceInput(in %x: !firrtl.uint<1>, out %z: !firrtl.uint<1>) {
    %c1_ui = firrtl.constant 1 : !firrtl.uint
    %c_out = firrtl.instance @Child1  {name = "c"} : !firrtl.uint<1>
    %b0_in, %b0_out = firrtl.instance @Bottom1  {name = "b0"} : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %b0_in, %c1_ui : !firrtl.uint<1>, !firrtl.uint
    %b1_in, %b1_out = firrtl.instance @Bottom1  {name = "b1"} : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %b1_in, %c1_ui : !firrtl.uint<1>, !firrtl.uint
    %0 = firrtl.and %b0_out, %b1_out : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
    %1 = firrtl.and %0, %c_out : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
    // CHECK: %[[C0:.+]] = firrtl.constant 1 : !firrtl.uint<1>
    // CHECK: firrtl.connect %z, %[[C0]] : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %z, %1 : !firrtl.uint<1>, !firrtl.uint<1>
  }
}

//propagate constant inputs ONLY if ALL instance inputs get the same value
firrtl.circuit "InstanceInput2"   {
  // CHECK-LABEL: firrtl.module @Bottom2
  firrtl.module @Bottom2(in %in: !firrtl.uint<1>, out %out: !firrtl.uint<1>) {
    // CHECK: firrtl.connect %out, %in 
    firrtl.connect %out, %in : !firrtl.uint<1>, !firrtl.uint<1>
  }
 // CHECK-LABEL:  firrtl.module @Child2
  firrtl.module @Child2(out %out: !firrtl.uint<1>) {
    %c1_ui = firrtl.constant 1 : !firrtl.uint
    %b0_in, %b0_out = firrtl.instance @Bottom2  {name = "b0"} : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %b0_in, %c1_ui : !firrtl.uint<1>, !firrtl.uint
    // CHECK: firrtl.connect %out, %b0_out
    firrtl.connect %out, %b0_out : !firrtl.uint<1>, !firrtl.uint<1>
  }
 // CHECK-LABEL:  firrtl.module @InstanceInput2
  firrtl.module @InstanceInput2(in %x: !firrtl.uint<1>, out %z: !firrtl.uint<1>) {
    %c1_ui = firrtl.constant 1 : !firrtl.uint
    %c_out = firrtl.instance @Child2  {name = "c"} : !firrtl.uint<1>
    %b0_in, %b0_out = firrtl.instance @Bottom2  {name = "b0"} : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %b0_in, %x : !firrtl.uint<1>, !firrtl.uint<1>
    %b1_in, %b1_out = firrtl.instance @Bottom2  {name = "b1"} : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %b1_in, %c1_ui : !firrtl.uint<1>, !firrtl.uint
    %0 = firrtl.and %b0_out, %b1_out : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
    %1 = firrtl.and %0, %c_out : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
   // CHECK:  firrtl.connect %z, %1
    firrtl.connect %z, %1 : !firrtl.uint<1>, !firrtl.uint<1>
  }
}

// ConstProp should work across wires
firrtl.circuit "acrossWire"   {
  // CHECK-LABEL: firrtl.module @acrossWire
  firrtl.module @acrossWire(in %x: !firrtl.uint<1>, out %y: !firrtl.uint<1>) {
    %z = firrtl.wire  : !firrtl.uint<1>
    firrtl.connect %y, %z : !firrtl.uint<1>, !firrtl.uint<1>
    %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
    %0 = firrtl.mux(%x, %c0_ui1, %c0_ui1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
    firrtl.connect %z, %0 : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: %[[C2:.+]] = firrtl.constant 0 : !firrtl.uint<1>
    // CHECK-NEXT: firrtl.connect %y, %[[C2]] : !firrtl.uint<1>, !firrtl.uint<1>
  }
}

//"ConstProp" should "propagate constant outputs"
firrtl.circuit "constOutput"   {
  firrtl.module @constOutChild(out %out: !firrtl.uint<1>) {
    %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
    firrtl.connect %out, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
  }
  firrtl.module @constOutput(in %x: !firrtl.uint<1>, out %z: !firrtl.uint<1>) {
    %c_out = firrtl.instance @constOutChild  {name = "c"} : !firrtl.uint<1>
    %0 = firrtl.and %x, %c_out : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
    firrtl.connect %z, %0 : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: %[[C3_0:.+]] = firrtl.constant 0 : !firrtl.uint<1>
    // CHECK: %[[C3:.+]] = firrtl.constant 0 : !firrtl.uint<1>
    // CHECK: firrtl.connect %z, %[[C3:.+]] : !firrtl.uint<1>, !firrtl.uint<1>
  }
}

// Optimizing this mux gives: z <= pad(UInt<2>(0), 4)
// Thus this checks that we then optimize that pad
//"ConstProp" should "optimize nested Expressions" in {
firrtl.circuit "optiMux"   {
  // CHECK-LABEL: firrtl.module @optiMux
  firrtl.module @optiMux(out %z: !firrtl.uint<4>) {
    %c1_ui = firrtl.constant 1 : !firrtl.uint
    %c0_ui2 = firrtl.constant 0 : !firrtl.uint<2>
    %c0_ui4 = firrtl.constant 0 : !firrtl.uint<4>
    %0 = firrtl.mux(%c1_ui, %c0_ui2, %c0_ui4) : (!firrtl.uint, !firrtl.uint<2>, !firrtl.uint<4>) -> !firrtl.uint<4>
    // CHECK: %[[C4:.+]] = firrtl.constant 0 :
    // CHECK: firrtl.connect %z, %[[C4]]
    firrtl.connect %z, %0 : !firrtl.uint<4>, !firrtl.uint<4>
  }
}

firrtl.circuit "divFold"   {
  // CHECK-LABEL: firrtl.module @divFold
  firrtl.module @divFold(in %a: !firrtl.uint<8>, out %b: !firrtl.uint<8>) {
    %0 = firrtl.div %a, %a : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<8>
    firrtl.connect %b, %0 : !firrtl.uint<8>, !firrtl.uint<8>
    // CHECK: %[[C5:.+]] = firrtl.constant 1 : !firrtl.uint<8>
    // CHECK: firrtl.connect %b, %[[C5]] : !firrtl.uint<8>, !firrtl.uint<8>
  }
}

//"pad constant connections to wires when propagating"
firrtl.circuit "padConstWire"   {
  // CHECK-LABEL: firrtl.module @padConstWire
  firrtl.module @padConstWire(out %z: !firrtl.uint<16>) {
    %w_a = firrtl.wire  : !firrtl.uint<8>
    %w_b = firrtl.wire  : !firrtl.uint<8>
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    firrtl.connect %w_a, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
    firrtl.connect %w_b, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
    %0 = firrtl.cat %w_a, %w_b : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
    firrtl.connect %z, %0 : !firrtl.uint<16>, !firrtl.uint<16>
    // CHECK: %[[C6:.+]] = firrtl.constant 771 : !firrtl.uint<16>
    // CHECK-NEXT: firrtl.connect %z, %[[C6]] : !firrtl.uint<16>, !firrtl.uint<16>
  }
}

// "pad constant connections to registers when propagating"
firrtl.circuit "padConstReg"   {
  // CHECK-LABEL: firrtl.module @padConstReg
  firrtl.module @padConstReg(in %clock: !firrtl.clock, out %z: !firrtl.uint<16>) {
    %r_a = firrtl.reg %clock  :  !firrtl.uint<8>
    %r_b = firrtl.reg %clock  :  !firrtl.uint<8>
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    firrtl.connect %r_a, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
    firrtl.connect %r_b, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
    %0 = firrtl.cat %r_a, %r_b : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
    firrtl.connect %z, %0 : !firrtl.uint<16>, !firrtl.uint<16>
    // CHECK: %[[C6:.+]] = firrtl.constant 771 : !firrtl.uint<16>
    // CHECK-NEXT: firrtl.connect %z, %[[C6]] : !firrtl.uint<16>, !firrtl.uint<16>
  }
}

// "pad zero when constant propping a register replaced with zero"
firrtl.circuit "padZeroReg"   {
  // CHECK-LABEL: firrtl.module @padZeroReg
  firrtl.module @padZeroReg(in %clock: !firrtl.clock, out %z: !firrtl.uint<16>) {
      %r = firrtl.reg %clock  :  !firrtl.uint<8>
      %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
      %0 = firrtl.or %r, %c0_ui1 : (!firrtl.uint<8>, !firrtl.uint<1>) -> !firrtl.uint<8>
      firrtl.connect %r, %0 : !firrtl.uint<8>, !firrtl.uint<8>
      %c171_ui8 = firrtl.constant 171 : !firrtl.uint<8>
      %n = firrtl.node %c171_ui8  : !firrtl.uint<8>
      %1 = firrtl.cat %n, %r : (!firrtl.uint<8>, !firrtl.uint<8>) -> !firrtl.uint<16>
      firrtl.connect %z, %1 : !firrtl.uint<16>, !firrtl.uint<16>
    // CHECK: %[[C7:.+]] = firrtl.constant 171 : !firrtl.uint<8>
    // CHECK: %[[invalid:.+]] = firrtl.invalidvalue : !firrtl.uint<8>
    // CHECK: %[[C7_0:.+]] = firrtl.cat %c171_ui8, %invalid_ui8 
    // CHECK-NEXT: firrtl.connect %z, %[[C7_0]] : !firrtl.uint<16>, !firrtl.uint<16>
  }
}

// should "pad constant connections to outputs when propagating"
firrtl.circuit "padConstOut"   {
  firrtl.module @padConstOutChild(out %x: !firrtl.uint<8>) {
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    firrtl.connect %x, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
  }
  // CHECK-LABEL: firrtl.module @padConstOut
  firrtl.module @padConstOut(out %z: !firrtl.uint<16>) {
    %c_x = firrtl.instance @padConstOutChild  {name = "c"} : !firrtl.uint<8>
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    %0 = firrtl.cat %c3_ui2, %c_x : (!firrtl.uint<2>, !firrtl.uint<8>) -> !firrtl.uint<10>
    // CHECK: %[[C8:.+]] = firrtl.constant 771 : !firrtl.uint<10>
    // CHECK: firrtl.connect %z, %[[C8]] : !firrtl.uint<16>, !firrtl.uint<10>
    firrtl.connect %z, %0 : !firrtl.uint<16>, !firrtl.uint<10>
  }
}

// "pad constant connections to submodule inputs when propagating"
firrtl.circuit "padConstIn"   {
  // CHECK-LABEL: firrtl.module @padConstInChild
  firrtl.module @padConstInChild(in %x: !firrtl.uint<8>, out %y: !firrtl.uint<16>) {
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    %0 = firrtl.cat %c3_ui2, %x : (!firrtl.uint<2>, !firrtl.uint<8>) -> !firrtl.uint<10>
    // CHECK: %[[C9:.+]] = firrtl.constant 771 : !firrtl.uint<10>
    // CHECK: firrtl.connect %y, %[[C9]] : !firrtl.uint<16>, !firrtl.uint<10>
    firrtl.connect %y, %0 : !firrtl.uint<16>, !firrtl.uint<10>
  }
  // CHECK-LABEL: firrtl.module @padConstIn
  firrtl.module @padConstIn(out %z: !firrtl.uint<16>) {
    %c_x, %c_y = firrtl.instance @padConstInChild  {name = "c"} : !firrtl.uint<8>, !firrtl.uint<16>
    %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
    firrtl.connect %c_x, %c3_ui2 : !firrtl.uint<8>, !firrtl.uint<2>
    firrtl.connect %z, %c_y : !firrtl.uint<16>, !firrtl.uint<16>
    // CHECK: %[[C10:.+]] = firrtl.constant 771 : !firrtl.uint<16>
    // CHECK: firrtl.connect %z, %[[C10]] : !firrtl.uint<16>, !firrtl.uint<16>
  }
}

//  "remove pads if the width is <= the width of the argument"
firrtl.circuit "removePad"   {
  // CHECK-LABEL: firrtl.module @removePad
  firrtl.module @removePad(in %x: !firrtl.uint<8>, out %z: !firrtl.uint<8>) {
    %0 = firrtl.pad %x, 6 : (!firrtl.uint<8>) -> !firrtl.uint<8>
    // CHECK: firrtl.connect %z, %x : !firrtl.uint<8>, !firrtl.uint<8>
    firrtl.connect %z, %0 : !firrtl.uint<8>, !firrtl.uint<8>
  }
}

// Registers with no reset or connections" should "be replaced with constant zero
firrtl.circuit "uninitSelfReg"   {
  // CHECK-LABEL: firrtl.module @uninitSelfReg
  firrtl.module @uninitSelfReg(in %clock: !firrtl.clock, out %z: !firrtl.uint<8>) {
    %r = firrtl.reg %clock  :  !firrtl.uint<8>
    firrtl.connect %r, %r : !firrtl.uint<8>, !firrtl.uint<8>
    firrtl.connect %z, %r : !firrtl.uint<8>, !firrtl.uint<8>
    // CHECK: %invalid_ui8 = firrtl.invalidvalue : !firrtl.uint<8>
    // CHECK: firrtl.connect %z, %invalid_ui8 : !firrtl.uint<8>, !firrtl.uint<8>
  }
}

//"Registers with ONLY constant reset" should "be replaced with that constant" in {
firrtl.circuit "constResetReg"   {
  // CHECK-LABEL: firrtl.module @constResetReg(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, out %z: !firrtl.uint<8>) {
  firrtl.module @constResetReg(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, out %z: !firrtl.uint<8>) {
    %c11_ui4 = firrtl.constant 11 : !firrtl.uint<4>
    %r = firrtl.regreset %clock, %reset, %c11_ui4  : !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<8>
    firrtl.connect %r, %r : !firrtl.uint<8>, !firrtl.uint<8>
    firrtl.connect %z, %r : !firrtl.uint<8>, !firrtl.uint<8>
    // CHECK: %[[C11:.+]] = firrtl.constant 11 : !firrtl.uint<8>
    // CHECK: firrtl.connect %z, %[[C11]] : !firrtl.uint<8>, !firrtl.uint<8>
  }
}

//"Registers async reset and a constant connection" should "NOT be removed
firrtl.circuit "asyncReset"   {
  // CHECK-LABEL: firrtl.module @asyncReset
  firrtl.module @asyncReset(in %clock: !firrtl.clock, in %reset: !firrtl.asyncreset, in %en: !firrtl.uint<1>, out %z: !firrtl.uint<8>) {
    %c11_ui4 = firrtl.constant 11 : !firrtl.uint<4>
    %r = firrtl.regreset %clock, %reset, %c11_ui4  : !firrtl.asyncreset, !firrtl.uint<4>, !firrtl.uint<8>
    %c0_ui4 = firrtl.constant 0 : !firrtl.uint<4>
    %0 = firrtl.mux(%en, %c0_ui4, %r) : (!firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<8>) -> !firrtl.uint<8>
    firrtl.connect %r, %0 : !firrtl.uint<8>, !firrtl.uint<8>
    firrtl.connect %z, %r : !firrtl.uint<8>, !firrtl.uint<8>
    // CHECK: firrtl.connect %r, %0 : !firrtl.uint<8>, !firrtl.uint<8>
    // CHECK: firrtl.connect %z, %r : !firrtl.uint<8>, !firrtl.uint<8>
  }
}

//"Registers with ONLY constant connection" should "be replaced with that constant"
firrtl.circuit "constReg2"   {
  // CHECK-LABEL: firrtl.module @constReg2
  firrtl.module @constReg2(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, out %z: !firrtl.sint<8>) {
    %r = firrtl.reg %clock  :  !firrtl.sint<8>
    %c-5_si4 = firrtl.constant -5 : !firrtl.sint<4>
    firrtl.connect %r, %c-5_si4 : !firrtl.sint<8>, !firrtl.sint<4>
    firrtl.connect %z, %r : !firrtl.sint<8>, !firrtl.sint<8>
    // CHECK: %[[C12:.+]] = firrtl.constant -5 : !firrtl.sint<8>
    // CHECK: firrtl.connect %z, %[[C12]] : !firrtl.sint<8>, !firrtl.sint<8>
  }
}

//"Registers with identical constant reset and connection" should "be replaced with that constant" in {
firrtl.circuit "regSameConstReset"   {
  // CHECK-LABEL: firrtl.module @regSameConstReset
  firrtl.module @regSameConstReset(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, out %z: !firrtl.uint<8>) {
    %c11_ui4 = firrtl.constant 11 : !firrtl.uint<4>
    %r = firrtl.regreset %clock, %reset, %c11_ui4  : !firrtl.uint<1>, !firrtl.uint<4>, !firrtl.uint<8>
    firrtl.connect %r, %c11_ui4 : !firrtl.uint<8>, !firrtl.uint<4>
    firrtl.connect %z, %r : !firrtl.uint<8>, !firrtl.uint<8>
    // CHECK: %[[C13:.+]] = firrtl.constant 11 : !firrtl.uint<8>
    // CHECK: firrtl.connect %z, %[[C13]] : !firrtl.uint<8>, !firrtl.uint<8>
  }
}
