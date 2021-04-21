// REQUIRES: verilator
// RUN: circt-translate %s -export-verilog -verify-diagnostics > %t1.sv
// RUN: verilator --lint-only --top-module A %t1.sv
// RUN: verilator --lint-only --top-module AB %t1.sv
// RUN: verilator --lint-only --top-module shl %t1.sv
// RUN: verilator --lint-only --top-module TESTSIMPLE %t1.sv
// RUN: verilator --lint-only --top-module casts %t1.sv
// RUN: verilator --lint-only --top-module exprInlineTestIssue439 %t1.sv

rtl.module @B(%a: i1 { rtl.inout }) -> (i1 {rtl.name = "b"}, i1 {rtl.name = "c"}) {
  %0 = comb.or %a, %a : i1
  %1 = comb.and %a, %a : i1
  rtl.output %0, %1 : i1, i1
}

rtl.module @A(%d: i1, %e: i1) -> (i1 {rtl.name = "f"}) {
  %1 = comb.mux %d, %d, %e : i1
  rtl.output %1 : i1
}

rtl.module @AAA(%d: i1, %e: i1) -> (i1 {rtl.name = "f"}) {
  %z = comb.constant ( 0 : i1 ) : i1
  rtl.output %z : i1
}

rtl.module @AB(%w: i1, %x: i1) -> (i1 {rtl.name = "y"}, i1 {rtl.name = "z"}) {
  %w2 = rtl.instance "a1" @AAA(%w, %w1) : (i1, i1) -> (i1)
  %w1, %y = rtl.instance "b1" @B(%w2) : (i1) -> (i1, i1)
  rtl.output %y, %x : i1, i1
}

rtl.module @shl(%a: i1) -> (i1 {rtl.name = "b"}) {
  %0 = comb.shl %a, %a : i1
  rtl.output %0 : i1
}

rtl.module @TESTSIMPLE(%a: i4, %b: i4, %cond: i1, %array: !rtl.array<10xi4>,
                        %uarray: !rtl.uarray<16xi8>) -> (
  %r0: i4, %r2: i4, %r4: i4, %r6: i4,
  %r7: i4, %r8: i4, %r9: i4, %r10: i4,
  %r11: i4, %r12: i4, %r13: i4, %r14: i4,
  %r15: i4, %r16: i1,
  %r17: i1, %r18: i1, %r19: i1, %r20: i1,
  %r21: i1, %r22: i1, %r23: i1, %r24: i1,
  %r25: i1, %r26: i1, %r27: i1, %r28: i1,
  %r29: i12, %r30: i2, %r31: i9, %r33: i4, %r34: i4,
  %r35: !rtl.array<3xi4>
  ) {

  %0 = comb.add %a, %b : i4
  %2 = comb.sub %a, %b : i4
  %4 = comb.mul %a, %b : i4
  %6 = comb.divu %a, %b : i4
  %7 = comb.divs %a, %b : i4
  %8 = comb.modu %a, %b : i4
  %9 = comb.mods %a, %b : i4
  %10 = comb.shl %a, %b : i4
  %11 = comb.shru %a, %b : i4
  %12 = comb.shrs %a, %b : i4
  %13 = comb.or %a, %b : i4
  %14 = comb.and %a, %b : i4
  %15 = comb.xor %a, %b : i4
  %16 = comb.icmp eq %a, %b : i4
  %17 = comb.icmp ne %a, %b : i4
  %18 = comb.icmp slt %a, %b : i4
  %19 = comb.icmp sle %a, %b : i4
  %20 = comb.icmp sgt %a, %b : i4
  %21 = comb.icmp sge %a, %b : i4
  %22 = comb.icmp ult %a, %b : i4
  %23 = comb.icmp ule %a, %b : i4
  %24 = comb.icmp ugt %a, %b : i4
  %25 = comb.icmp uge %a, %b : i4
  %26 = comb.andr %a : i4
  %27 = comb.orr %a : i4
  %28 = comb.xorr %a : i4
  %29 = comb.concat %a, %a, %b : (i4, i4, i4) -> i12
  %30 = comb.extract %a from 1 : (i4) -> i2
  %31 = comb.sext %a : (i4) -> i9
  %33 = comb.mux %cond, %a, %b : i4

  %allone = comb.constant (15 : i4) : i4
  %34 = comb.xor %a, %allone : i4

  %one = comb.constant (1 : i4) : i4
  %aPlusOne = comb.add %a, %one : i4
  %35 = rtl.array_slice %array at %aPlusOne: (!rtl.array<10xi4>) -> !rtl.array<3xi4>


  rtl.output %0, %2, %4, %6, %7, %8, %9, %10, %11, %12, %13, %14, %15, %16, %17, %18, %19, %20, %21, %22, %23, %24, %25, %26, %27, %28, %29, %30, %31, %33, %34, %35:
    i4,i4, i4,i4,i4,i4,i4, i4,i4,i4,i4,i4,
    i4,i1,i1,i1,i1, i1,i1,i1,i1,i1, i1,i1,i1,i1,
    i12, i2,i9,i4, i4, !rtl.array<3xi4>
}

rtl.module @exprInlineTestIssue439(%clk: i1) {
  %c = comb.constant (0:i32) : i32

  sv.always posedge %clk {
    %e = comb.extract %c from 0 : (i32) -> i16
    %f = comb.add %e, %e : i16
    sv.fwrite "%d"(%f) : i16
  }
}

rtl.module @casts(%in1: i64) -> (%r1: !rtl.array<5xi8>) {
  %bits = comb.bitcast %in1 : (i64) -> !rtl.array<64xi1>
  %idx = comb.constant (10 : i6) : i6
  %midBits = rtl.array_slice %bits at %idx : (!rtl.array<64xi1>) -> !rtl.array<40xi1>
  %r1 = comb.bitcast %midBits : (!rtl.array<40xi1>) -> !rtl.array<5xi8>
  rtl.output %r1 : !rtl.array<5xi8>
}
