// RUN: circt-opt %s --lower-esi-to-physical -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck %s
// RUN: circt-opt %s --lower-esi-ports -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck --check-prefix=IFACE %s
// RUN: circt-opt %s --lower-esi-to-physical --lower-esi-ports --lower-esi-to-rtl -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck --check-prefix=RTL %s

rtl.module.extern @Sender(%clk: i1) -> ( %x: !esi.channel<i4>, %y: i8 )
rtl.module.extern @ArrSender() -> (%x: !esi.channel<!rtl.array<4xi64>>)
rtl.module.extern @Reciever(%a: !esi.channel<i4>, %clk: i1)

// CHECK-LABEL: rtl.module.extern @Sender(i1 {rtl.name = "clk"}) -> (%x: !esi.channel<i4>, %y: i8)
// CHECK-LABEL: rtl.module.extern @Reciever(!esi.channel<i4> {rtl.name = "a"}, i1 {rtl.name = "clk"})

// IFACE-LABEL: sv.interface @IValidReady_i4 {
// IFACE-NEXT:    sv.interface.signal @valid : i1
// IFACE-NEXT:    sv.interface.signal @ready : i1
// IFACE-NEXT:    sv.interface.signal @data : i4
// IFACE-NEXT:    sv.interface.modport @sink ("input" @ready, "output" @valid, "output" @data)
// IFACE-NEXT:    sv.interface.modport @source ("input" @valid, "input" @data, "output" @ready)
// IFACE-LABEL: sv.interface @IValidReady_ArrayOf4xi64 {
// IFACE-NEXT:    sv.interface.signal @valid : i1
// IFACE-NEXT:    sv.interface.signal @ready : i1
// IFACE-NEXT:    sv.interface.signal @data : !rtl.array<4xi64>
// IFACE-NEXT:    sv.interface.modport @sink  ("input" @ready, "output" @valid, "output" @data)
// IFACE-NEXT:    sv.interface.modport @source  ("input" @valid, "input" @data, "output" @ready)
// IFACE-LABEL: rtl.module.extern @Sender(i1 {rtl.name = "clk"}, !sv.modport<@IValidReady_i4::@sink> {rtl.name = "x"}) -> (%y: i8)
// IFACE-LABEL: rtl.module.extern @ArrSender(!sv.modport<@IValidReady_ArrayOf4xi64::@sink> {rtl.name = "x"})
// IFACE-LABEL: rtl.module.extern @Reciever(!sv.modport<@IValidReady_i4::@source> {rtl.name = "a"}, i1 {rtl.name = "clk"})


rtl.module @test(%clk:i1, %rstn:i1) {

  %esiChan2, %0 = rtl.instance "sender2" @Sender (%clk) : (i1) -> (!esi.channel<i4>, i8)
  %bufferedChan2 = esi.buffer %clk, %rstn, %esiChan2 { stages = 4 } : i4
  rtl.instance "recv2" @Reciever (%bufferedChan2, %clk) : (!esi.channel<i4>, i1) -> ()

  // CHECK:      %sender2.x, %sender2.y = rtl.instance "sender2" @Sender(%clk) : (i1) -> (!esi.channel<i4>, i8)
  // CHECK-NEXT:  %0 = esi.stage %clk, %rstn, %sender2.x : i4
  // CHECK-NEXT:  %1 = esi.stage %clk, %rstn, %0 : i4
  // CHECK-NEXT:  %2 = esi.stage %clk, %rstn, %1 : i4
  // CHECK-NEXT:  %3 = esi.stage %clk, %rstn, %2 : i4
  // CHECK-NEXT:  rtl.instance "recv2" @Reciever(%3, %clk)  : (!esi.channel<i4>, i1) -> ()

  // IFACE-LABEL: rtl.module @test(%clk: i1, %rstn: i1) {
  // IFACE-NEXT:    %0 = sv.interface.instance : !sv.interface<@IValidReady_i4>
  // IFACE-NEXT:    %1 = sv.modport.get %0 @source : !sv.interface<@IValidReady_i4> -> !sv.modport<@IValidReady_i4::@source>
  // IFACE-NEXT:    %2 = esi.wrap.iface %1 : !sv.modport<@IValidReady_i4::@source> -> !esi.channel<i4>
  // IFACE-NEXT:    %3 = sv.modport.get %0 @sink : !sv.interface<@IValidReady_i4> -> !sv.modport<@IValidReady_i4::@sink>
  // IFACE-NEXT:    %sender2.y = rtl.instance "sender2" @Sender(%clk, %3) : (i1, !sv.modport<@IValidReady_i4::@sink>) -> i8
  // IFACE-NEXT:    %4 = esi.buffer %clk, %rstn, %2 {stages = 4 : i64} : i4
  // IFACE-NEXT:    %5 = sv.interface.instance : !sv.interface<@IValidReady_i4>
  // IFACE-NEXT:    %6 = sv.modport.get %5 @sink : !sv.interface<@IValidReady_i4> -> !sv.modport<@IValidReady_i4::@sink>
  // IFACE-NEXT:    esi.unwrap.iface %4 into %6 : (!esi.channel<i4>, !sv.modport<@IValidReady_i4::@sink>)
  // IFACE-NEXT:    %7 = sv.modport.get %5 @source : !sv.interface<@IValidReady_i4> -> !sv.modport<@IValidReady_i4::@source>
  // IFACE-NEXT:    rtl.instance "recv2" @Reciever(%7, %clk) : (!sv.modport<@IValidReady_i4::@source>, i1) -> ()

  // After all 3 ESI lowering passes, there shouldn't be any ESI constructs!
  // RTL-NOT: esi
}

rtl.module @add11(%clk: i1, %ints: !esi.channel<i32>) -> (%mutatedInts: !esi.channel<i32>, %c4: i4) {
  %i, %i_valid = esi.unwrap.vr %ints, %rdy : i32
  %c11 = rtl.constant 11 : i32
  %m = comb.add %c11, %i : i32
  %mutInts, %rdy = esi.wrap.vr %m, %i_valid : i32
  %c4 = rtl.constant 0 : i4
  rtl.output %mutInts, %c4 : !esi.channel<i32>, i4
}
// RTL: rtl.module @add11(%clk: i1, %ints: i32, %ints_valid: i1, %mutatedInts_ready: i1) -> (%mutatedInts: i32, %mutatedInts_valid: i1, %c4: i4, %ints_ready: i1) {
// RTL:   %{{.+}} = rtl.constant 11 : i32
// RTL:   [[RES0:%.+]] = comb.add %{{.+}}, %ints : i32
// RTL:   %{{.+}} = rtl.constant 0 : i4
// RTL:   rtl.output [[RES0]], %ints_valid, %{{.+}}, %mutatedInts_ready : i32, i1, i4, i1


rtl.module @test2(%clk:i1, %rstn:i1) {
  %ints, %c4 = rtl.instance "adder" @add11(%clk, %ints) : (i1, !esi.channel<i32>) -> (!esi.channel<i32>, i4)
}
// RTL: rtl.module @test2(%clk: i1, %rstn: i1) {
// RTL:   %adder.mutatedInts, %adder.mutatedInts_valid, %adder.c4, %adder.ints_ready = rtl.instance "adder" @add11(%clk, %adder.mutatedInts, %adder.mutatedInts_valid, %adder.ints_ready)

rtl.module @twoChannelArgs(%clk: i1, %ints: !esi.channel<i32>, %foo: !esi.channel<i7>) -> () {
  %rdy = rtl.constant 1 : i1
  %i, %i_valid = esi.unwrap.vr %ints, %rdy : i32
  %i2, %i2_valid = esi.unwrap.vr %foo, %rdy : i7
}
// RTL: rtl.module @twoChannelArgs(%clk: i1, %ints: i32, %ints_valid: i1, %foo: i7, %foo_valid: i1) -> (%ints_ready: i1, %foo_ready: i1)
// RTL:   %true = rtl.constant true
// RTL:   rtl.output %true, %true : i1, i1
