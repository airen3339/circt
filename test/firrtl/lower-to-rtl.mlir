// RUN: circt-opt -lower-firrtl-to-rtl %s | FileCheck %s

module attributes {firrtl.mainModule = "Simple"} {

  // CHECK-LABEL: rtl.module @Simple
  rtl.module @Simple(%in1: i4, %in2: i2, %in3: i8) -> (%out4: i4, %out5: i4) {
    %in1c = firrtl.stdIntCast %in1 : (i4) -> !firrtl.uint<4>
    %in2c = firrtl.stdIntCast %in2 : (i2) -> !firrtl.uint<2>
    %in3c = firrtl.stdIntCast %in3 : (i8) -> !firrtl.sint<8>
    // CHECK-NEXT: %tmp3 = rtl.wire : i4
    %tmp3 = rtl.wire : i4
    %tmp4 = firrtl.stdIntCast %tmp3 : (i4) -> !firrtl.uint<4>
    %out4 = firrtl.asNonPassive %tmp4 : (!firrtl.uint<4>) -> !firrtl.flip<uint<4>>
    %out5 = firrtl.asNonPassive %tmp4 : (!firrtl.uint<4>) -> !firrtl.flip<uint<4>>

    // CHECK: [[ZERO4:%.+]] = rtl.constant(0 : i4) : i4
    // CHECK: rtl.connect %tmp3, [[ZERO4]] : i4
    firrtl.invalid %out5 : !firrtl.flip<uint<4>>

    // CHECK: rtl.constant(-4 : i4) : i4
    %c12_ui4 = firrtl.constant(12 : ui4) : !firrtl.uint<4>

    // CHECK: rtl.constant(2 : i3) : i3
    %c2_si3 = firrtl.constant(2 : si3) : !firrtl.sint<3>

    // CHECK: %0 = rtl.add %c-4_i4, %in1 : i4
    %0 = firrtl.add %c12_ui4, %in1c : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>

    %1 = firrtl.asUInt %in1c : (!firrtl.uint<4>) -> !firrtl.uint<4>

    // CHECK-NEXT: [[SUB:%.+]] = rtl.sub %0, %in1 : i4
    %2 = firrtl.sub %0, %1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>

    // CHECK: [[PADRES:%.+]] = rtl.sext %in2 : (i2) -> i3
    %3 = firrtl.pad %in2c, 3 : (!firrtl.uint<2>) -> !firrtl.sint<3>

    // CHECK: [[PADRES2:%.+]] = rtl.zext [[PADRES]] : (i3) -> i4
    %4 = firrtl.pad %3, 4 : (!firrtl.sint<3>) -> !firrtl.uint<4>

    // CHECK: [[IN2EXT:%.+]] = rtl.zext %in2 : (i2) -> i4
    // CHECK: [[XOR:%.+]] = rtl.xor [[IN2EXT]], [[PADRES2]] : i4
    %5 = firrtl.xor %in2c, %4 : (!firrtl.uint<2>, !firrtl.uint<4>) -> !firrtl.uint<4>

    // CHECK: rtl.and [[XOR]]
    %and = firrtl.and %5, %4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>

    // CHECK: rtl.or [[XOR]]
    %or = firrtl.or %5, %4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>

    // CHECK: [[CONCAT1:%.+]] = rtl.concat [[PADRES2]], [[XOR]] : (i4, i4) -> i8
    %6 = firrtl.cat %4, %5 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<8>

    // CHECK: rtl.concat %in1, %in2
    %7 = firrtl.cat %in1c, %in2c : (!firrtl.uint<4>, !firrtl.uint<2>) -> !firrtl.uint<6>

    // CHECK-NEXT: rtl.connect [[SUB]], [[PADRES2]] : i4
    firrtl.connect %2, %4 : !firrtl.uint<4>, !firrtl.uint<4>

    // CHECK-NEXT: rtl.connect %tmp3, [[XOR]] : i4
    firrtl.connect %out4, %5 : !firrtl.flip<uint<4>>, !firrtl.uint<4>

    // CHECK-NEXT: [[ZEXT:%.+]] = rtl.zext %in2 : (i2) -> i4
    // CHECK-NEXT: rtl.connect %tmp3, [[ZEXT]] : i4
    firrtl.connect %out4, %in2c : !firrtl.flip<uint<4>>, !firrtl.uint<2>

    // CHECK-NEXT: %test-name = rtl.wire : i4
    firrtl.wire {name = "test-name"} : !firrtl.uint<4>

    // CHECK-NEXT: = rtl.wire : i2
    firrtl.wire : !firrtl.uint<2>

    // CHECK-NEXT: = firrtl.wire : !firrtl.vector<uint<1>, 13>
    %_t_2 = firrtl.wire : !firrtl.vector<uint<1>, 13>

    // CHECK-NEXT: = firrtl.wire : !firrtl.vector<uint<2>, 13>
    %_t_3 = firrtl.wire : !firrtl.vector<uint<2>, 13>

    // CHECK-NEXT: = rtl.extract [[CONCAT1]] from 3 : (i8) -> i5
    %8 = firrtl.bits %6 7 to 3 : (!firrtl.uint<8>) -> !firrtl.uint<5>

    // CHECK-NEXT: = rtl.extract [[CONCAT1]] from 5 : (i8) -> i3
    %9 = firrtl.head %6, 3 : (!firrtl.uint<8>) -> !firrtl.uint<3>

    // CHECK-NEXT: = rtl.extract [[CONCAT1]] from 0 : (i8) -> i5
    %10 = firrtl.tail %6, 3 : (!firrtl.uint<8>) -> !firrtl.uint<5>

    // CHECK-NEXT: = rtl.extract [[CONCAT1]] from 3 : (i8) -> i5
    %11 = firrtl.shr %6, 3 : (!firrtl.uint<8>) -> !firrtl.uint<5>

    // CHECK-NEXT: = rtl.constant(false) : i1
    %12 = firrtl.shr %6, 8 : (!firrtl.uint<8>) -> !firrtl.uint<1>

    // CHECK-NEXT: = rtl.extract %in3 from 7 : (i8) -> i1
    %13 = firrtl.shr %in3c, 8 : (!firrtl.sint<8>) -> !firrtl.sint<1>

    // CHECK-NEXT: [[ZERO:%.+]] = rtl.constant(0 : i3) : i3
    // CHECK-NEXT: = rtl.concat [[CONCAT1]], [[ZERO]] : (i8, i3) -> i11
    %14 = firrtl.shl %6, 3 : (!firrtl.uint<8>) -> !firrtl.uint<11>

    // CHECK-NEXT: = rtl.xorr [[CONCAT1]] : i8
    %15 = firrtl.xorr %6 : (!firrtl.uint<8>) -> !firrtl.uint<1>

    // CHECK-NEXT: = rtl.andr [[CONCAT1]] : i8
    %16 = firrtl.andr %6 : (!firrtl.uint<8>) -> !firrtl.uint<1>

    // CHECK-NEXT: = rtl.orr [[CONCAT1]] : i8
    %17 = firrtl.orr %6 : (!firrtl.uint<8>) -> !firrtl.uint<1>

    // CHECK-NEXT: [[ZEXTC1:%.+]] = rtl.zext [[CONCAT1]] : (i8) -> i12
    // CHECK-NEXT: [[ZEXT2:%.+]] = rtl.zext [[SUB]] : (i4) -> i12
    // CHECK-NEXT: [[VAL18:%.+]] = rtl.mul  [[ZEXTC1]], [[ZEXT2]] : i12
    %18 = firrtl.mul %6, %2 : (!firrtl.uint<8>, !firrtl.uint<4>) -> !firrtl.uint<12>

    // CHECK-NEXT: [[IN3SEXT:%.+]] = rtl.sext %in3 : (i8) -> i9
    // CHECK-NEXT: [[PADRESSEXT:%.+]] = rtl.zext [[PADRES]] : (i3) -> i9
    // CHECK-NEXT: = rtl.divs [[IN3SEXT]], [[PADRESSEXT]] : i9
    %19 = firrtl.div %in3c, %3 : (!firrtl.sint<8>, !firrtl.sint<3>) -> !firrtl.sint<9>

    // CHECK-NEXT: [[IN3EX:%.+]] = rtl.sext [[PADRES]] : (i3) -> i8
    // CHECK-NEXT: [[MOD1:%.+]] = rtl.mods %in3, [[IN3EX]] : i8
    // CHECK-NEXT: = rtl.extract [[MOD1]] from 0 : (i8) -> i3
    %20 = firrtl.rem %in3c, %3 : (!firrtl.sint<8>, !firrtl.sint<3>) -> !firrtl.sint<3>

    // CHECK-NEXT: [[IN4EX:%.+]] = rtl.sext [[PADRES]] : (i3) -> i8
    // CHECK-NEXT: [[MOD2:%.+]] = rtl.mods [[IN4EX]], %in3 : i8
    // CHECK-NEXT: = rtl.extract [[MOD2]] from 0 : (i8) -> i3
    %21 = firrtl.rem %3, %in3c : (!firrtl.sint<3>, !firrtl.sint<8>) -> !firrtl.sint<3>

    // CHECK-NEXT: [[WIRE:%n1]] = rtl.wire : i2
    // CHECK-NEXT: rtl.connect [[WIRE]], %in2 : i2
    %n1 = firrtl.node %in2c  {name = "n1"} : !firrtl.uint<2>

    // Nodes with no names are just dropped.
    %22 = firrtl.node %n1 : !firrtl.uint<2>

    // CHECK-NEXT: %false_{{.*}} = rtl.constant(false) : i1
    // CHECK-NEXT: [[CVT:%.+]] = rtl.concat %false_{{.*}}, %in2 : (i1, i2) -> i3
    %23 = firrtl.cvt %22 : (!firrtl.uint<2>) -> !firrtl.sint<3>

    // Will be dropped, here because this triggered a crash
    %s23 = firrtl.cvt %in3c : (!firrtl.sint<8>) -> !firrtl.sint<8>

    // CHECK-NEXT: %c-1_i3 = rtl.constant(-1 : i3) : i3
    // CHECK-NEXT: [[XOR:%.+]] = rtl.xor [[CVT]], %c-1_i3 : i3
    %24 = firrtl.not %23 : (!firrtl.sint<3>) -> !firrtl.uint<3>

    %s24 = firrtl.asSInt %24 : (!firrtl.uint<3>) -> !firrtl.sint<3>

    // CHECK-NEXT: [[SEXT:%.+]] = rtl.sext [[XOR]] : (i3) -> i4
    // CHECK-NEXT: [[ZERO4b:%.+]] = rtl.constant(0 : i4) : i4
    // CHECK-NEXT: [[SUB:%.+]] = rtl.sub [[ZERO4b]], [[SEXT]] : i4
    %25 = firrtl.neg %s24 : (!firrtl.sint<3>) -> !firrtl.sint<4>

    // CHECK-NEXT: [[CVT4:%.+]] = rtl.sext [[CVT]] : (i3) -> i4
    // CHECK-NEXT: rtl.mux %false, [[CVT4]], [[SUB]] : i4
    %26 = firrtl.mux(%12, %23, %25) : (!firrtl.uint<1>, !firrtl.sint<3>, !firrtl.sint<4>) -> !firrtl.sint<4>
  
    // Noop
    %27 = firrtl.validif %12, %18 : (!firrtl.uint<1>, !firrtl.uint<12>) -> !firrtl.uint<12>
    // CHECK-NEXT: rtl.andr
    %28 = firrtl.andr %27 : (!firrtl.uint<12>) -> !firrtl.uint<1>

    // CHECK-NEXT: = rtl.extract [[VAL18]] from 0 : (i12) -> i3
    // CHECK-NEXT: = rtl.shru [[XOR]], {{.*}} : i3
    %29 = firrtl.dshr %24, %18 : (!firrtl.uint<3>, !firrtl.uint<12>) -> !firrtl.uint<3>

    // CHECK-NEXT: = rtl.zext %2 : (i3) -> i8
    // CHECK-NEXT: = rtl.shrs %in3, {{.*}} : i8
    %a29 = firrtl.dshr %in3c, %3 : (!firrtl.sint<8>, !firrtl.sint<3>) -> !firrtl.sint<3>

    // CHECK-NEXT: = rtl.zext %2 : (i3) -> i8
    // CHECK-NEXT: = rtl.shl %in3, {{.*}} : i8
    %30 = firrtl.dshl %in3c, %3 : (!firrtl.sint<8>, !firrtl.sint<3>) -> !firrtl.sint<8>

    // CHECK-NEXT: rtl.icmp "ule" {{.*}}, {{.*}} : i4
    %41 = firrtl.leq %in1c, %4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<1>
    // CHECK-NEXT: rtl.icmp "ult" {{.*}}, {{.*}} : i4
    %42 = firrtl.lt %in1c, %4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<1>
    // CHECK-NEXT: rtl.icmp "uge" {{.*}}, {{.*}} : i4
    %43 = firrtl.geq %in1c, %4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<1>
    // CHECK-NEXT: rtl.icmp "ugt" {{.*}}, {{.*}} : i4
    %44 = firrtl.gt %in1c, %4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<1>
    // CHECK-NEXT: rtl.icmp "eq" {{.*}}, {{.*}} : i4
    %45 = firrtl.eq %in1c, %4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<1>
    // CHECK-NEXT: rtl.icmp "ne" {{.*}}, {{.*}} : i4
    %46 = firrtl.neq %in1c, %4 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<1>

    // Noop
    %47 = firrtl.asClock %44 : (!firrtl.uint<1>) -> !firrtl.clock
    %48 = firrtl.asAsyncReset %44 : (!firrtl.uint<1>) -> !firrtl.asyncreset

    // CHECK-NEXT: rtl.output %tmp3, %tmp3 : i4, i4
    rtl.output %tmp3, %tmp3 : i4,i4
  }

//   module Print :
//    input clock: Clock
//    input reset: UInt<1>
//    input a: UInt<4>
//    input b: UInt<4>
//    printf(clock, reset, "No operands!\n")
//    printf(clock, reset, "Hi %x %x\n", add(a, a), b)

  // CHECK-LABEL: rtl.module @Print
  rtl.module @Print(%clock: i1, %reset: i1, %a: i4, %b: i4) {
    %clock1 = firrtl.stdIntCast %clock : (i1) -> !firrtl.clock
    %reset1 = firrtl.stdIntCast %reset : (i1) -> !firrtl.uint<1>
    %a1 = firrtl.stdIntCast %a : (i4) -> !firrtl.uint<4>
    %b1 = firrtl.stdIntCast %b : (i4) -> !firrtl.uint<4>
 
    // CHECK-NEXT: sv.alwaysat_posedge %clock {
    // CHECK-NEXT:   sv.ifdef "!SYNTHESIS" {
    // CHECK-NEXT:     [[TV:%.+]] = sv.textual_value "`PRINTF_COND_" : i1
    // CHECK-NEXT:     [[AND:%.+]] = rtl.and [[TV]], %reset
    // CHECK-NEXT:     sv.if [[AND]] {
    // CHECK-NEXT:       sv.fwrite "No operands!\0A"
    // CHECK-NEXT:     }
    // CHECK-NEXT:   }
    // CHECK-NEXT: }
   firrtl.printf %clock1, %reset1, "No operands!\0A"

    // CHECK: [[ADD:%.+]] = rtl.add
    %0 = firrtl.add %a1, %a1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<5>

    // CHECK: sv.fwrite "Hi %x %x\0A"({{.*}}) : i5, i4
    firrtl.printf %clock1, %reset1, "Hi %x %x\0A"(%0, %b1) : !firrtl.uint<5>, !firrtl.uint<4>

    // CHECK: rtl.output
    rtl.output
   }



// module Stop3 :
//    input clock1: Clock
//    input clock2: Clock
//    input reset: UInt<1>
//    stop(clock1, reset, 42)
//    stop(clock2, reset, 0)

  // CHECK-LABEL: rtl.module @Stop
  rtl.module @Stop(%clock1: i1, %clock2: i1, %reset: i1) {
    %clock1c = firrtl.stdIntCast %clock1 : (i1) -> !firrtl.clock
    %clock2c = firrtl.stdIntCast %clock2 : (i1) -> !firrtl.clock
    %resetc = firrtl.stdIntCast %reset : (i1) -> !firrtl.uint<1>

    // CHECK-NEXT: sv.alwaysat_posedge %clock1 {
    // CHECK-NEXT:   sv.ifdef "!SYNTHESIS" {
    // CHECK-NEXT:     %0 = sv.textual_value "`STOP_COND_" : i1
    // CHECK-NEXT:     %1 = rtl.and %0, %reset : i1
    // CHECK-NEXT:     sv.if %1 {
    // CHECK-NEXT:       sv.fatal
    // CHECK-NEXT:     }
    // CHECK-NEXT:   }
    // CHECK-NEXT: }
    firrtl.stop %clock1c, %resetc, 42

    // CHECK-NEXT: sv.alwaysat_posedge %clock2 {
    // CHECK-NEXT:   sv.ifdef "!SYNTHESIS" {
    // CHECK-NEXT:     %0 = sv.textual_value "`STOP_COND_" : i1
    // CHECK-NEXT:     %1 = rtl.and %0, %reset : i1
    // CHECK-NEXT:     sv.if %1 {
    // CHECK-NEXT:       sv.finish
    // CHECK-NEXT:     }
    // CHECK-NEXT:   }
    // CHECK-NEXT: }
    firrtl.stop %clock2c, %resetc, 0
  }

// circuit Verification:
//   module Verification:
//     input clock: Clock
//     input aCond: UInt<8>
//     input aEn: UInt<8>
//     input bCond: UInt<1>
//     input bEn: UInt<1>
//     input cCond: UInt<1>
//     input cEn: UInt<1>
//     assert(clock, bCond, bEn, "assert0")
//     assume(clock, aCond, aEn, "assume0")
//     cover(clock,  cCond, cEn, "cover0")

  // CHECK-LABEL: rtl.module @Verification
  rtl.module @Verification(%clock: i1, %aCond: i1, %aEn: i1, %bCond: i1, %bEn: i1, %cCond: i1, %cEn: i1) {
    %clockC = firrtl.stdIntCast %clock : (i1) -> !firrtl.clock
    %aCondC = firrtl.stdIntCast %aCond : (i1) -> !firrtl.uint<1>
    %aEnC = firrtl.stdIntCast %aEn : (i1) -> !firrtl.uint<1>
    %bCondC = firrtl.stdIntCast %bCond : (i1) -> !firrtl.uint<1>
    %bEnC = firrtl.stdIntCast %bEn : (i1) -> !firrtl.uint<1>
    %cCondC = firrtl.stdIntCast %cCond : (i1) -> !firrtl.uint<1>
    %cEnC = firrtl.stdIntCast %cEn : (i1) -> !firrtl.uint<1>

    // CHECK-NEXT: sv.alwaysat_posedge %clock {
    // CHECK-NEXT:   sv.if %aEn {
    // CHECK-NEXT:     sv.assert %aCond : i1
    // CHECK-NEXT:   }
    // CHECK-NEXT: }
    firrtl.assert %clockC, %aCondC, %aEnC, "assert0"
    // CHECK-NEXT: sv.alwaysat_posedge %clock {
    // CHECK-NEXT:   sv.if %bEn {
    // CHECK-NEXT:     sv.assume %bCond  : i1
    // CHECK-NEXT:   }
    // CHECK-NEXT: }
    firrtl.assume %clockC, %bCondC, %bEnC, "assume0"
    // CHECK-NEXT: sv.alwaysat_posedge %clock {
    // CHECK-NEXT:   sv.if %cEn {
    // CHECK-NEXT:     sv.cover %cCond : i1
    // CHECK-NEXT:   }
    // CHECK-NEXT: }
    firrtl.cover %clockC, %cCondC, %cEnC, "cover0"
    // CHECK-NEXT: rtl.output
    rtl.output
  }

  rtl.module @bar(%io_cpu_flush: i1) {
    rtl.output
  }

  // CHECK-LABEL: rtl.module @foo
  rtl.module @foo() {
    // CHECK-NEXT:  %io_cpu_flush.wire = rtl.wire : i1
    %io_cpu_flush.wire = rtl.wire : i1
    // CHECK-NEXT: rtl.instance "fetch"
    rtl.instance "fetch" @bar(%io_cpu_flush.wire)  : (i1) -> ()
    %0 = firrtl.stdIntCast %io_cpu_flush.wire : (i1) -> !firrtl.uint<1>
    %1454 = firrtl.asNonPassive %0 : (!firrtl.uint<1>) -> !firrtl.flip<uint<1>>

    %hits_1_7 = firrtl.node %1454 {name = "hits_1_7"} : !firrtl.flip<uint<1>>
    // CHECK-NEXT:  %hits_1_7 = rtl.wire : i1
    // CHECK-NEXT:  rtl.connect %hits_1_7, %io_cpu_flush.wire : i1
    %1455 = firrtl.asPassive %hits_1_7 : (!firrtl.flip<uint<1>>) -> !firrtl.uint<1>
  }

  // https://github.com/llvm/circt/issues/314
  // CHECK-LABEL: rtl.module @issue314
  rtl.module @issue314(%inp2: i27, %inpi: i65) {
    %inp_2 = firrtl.stdIntCast %inp2 : (i27) -> !firrtl.uint<27>
    %inp_i = firrtl.stdIntCast %inpi : (i65) -> !firrtl.uint<65>

    // CHECK-NEXT: %tmp48 = rtl.wire : i27
    %tmp48 = firrtl.wire {name = "tmp48"} : !firrtl.uint<27>
    // CHECK-NEXT: %0 = rtl.extract %inpi from 0 : (i65) -> i27
    // CHECK-NEXT: %1 = rtl.divu %inp2, %0 : i27
    %0 = firrtl.div %inp_2, %inp_i : (!firrtl.uint<27>, !firrtl.uint<65>) -> !firrtl.uint<27>
    // CHECK-NEXT: rtl.connect %tmp48, %1 : i27
    firrtl.connect %tmp48, %0 : !firrtl.uint<27>, !firrtl.uint<27>
  }

  // https://github.com/llvm/circt/issues/318
  // CHECK-LABEL: rtl.module @test_rem
  // CHECK-NEXT:     %0 = rtl.modu
  // CHECK-NEXT:     rtl.output %0
  rtl.module @test_rem(%tmp85: i1, %tmp79: i1) -> (%tmp106: i1) {
    %0 = firrtl.stdIntCast %tmp85 : (i1) -> !firrtl.uint<1>
    %1 = firrtl.stdIntCast %tmp79 : (i1) -> !firrtl.uint<1>
    %2 = firrtl.rem %1, %0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
    %3 = firrtl.stdIntCast %2 : (!firrtl.uint<1>) -> i1
    rtl.output %3 : i1
  }

  // CHECK-LABEL: rtl.module @Analog
  // CHECK-NEXT:   sv.ifdef "!SYNTHESIS"  {
  // CHECK-NEXT:     sv.alias %a1, %a1, %a1 : !rtl.inout<i1>
  // CHECK-NEXT:   }
  // CHECK-NEXT:   sv.ifdef "SYNTHESIS"  {
  // CHECK-NEXT:     %1 = rtl.read_inout %a1 : i1
  // CHECK-NEXT:     %2 = rtl.read_inout %a1 : i1
  // CHECK-NEXT:     %3 = rtl.read_inout %a1 : i1
  // CHECK-NEXT:     rtl.connect %1, %2 : i1
  // CHECK-NEXT:     rtl.connect %1, %3 : i1
  // CHECK-NEXT:     rtl.connect %2, %1 : i1
  // CHECK-NEXT:     rtl.connect %2, %3 : i1
  // CHECK-NEXT:     rtl.connect %3, %1 : i1
  // CHECK-NEXT:     rtl.connect %3, %2 : i1
  // CHECK-NEXT:   }
  // CHECK-NEXT:    %0 = rtl.read_inout %a1 : i1
  // CHECK-NEXT:    rtl.output %0 : i1
  rtl.module @Analog(%a1: !rtl.inout<i1>, %b1: !rtl.inout<i1>,
                     %c1: !rtl.inout<i1>) -> (%outClock: i1) {
    %a = firrtl.analogInOutCast %a1 : (!rtl.inout<i1>) -> !firrtl.analog<1>
    %b = firrtl.analogInOutCast %a1 : (!rtl.inout<i1>) -> !firrtl.analog<1>
    %c = firrtl.analogInOutCast %a1 : (!rtl.inout<i1>) -> !firrtl.analog<1>

    firrtl.attach %a, %b, %c : !firrtl.analog<1>, !firrtl.analog<1>, !firrtl.analog<1>

    %1 = firrtl.asClock %a : (!firrtl.analog<1>) -> !firrtl.clock
    %2 = firrtl.stdIntCast %1 : (!firrtl.clock) -> i1
    rtl.output %2 : i1
  }
}

