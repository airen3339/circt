// RUN: circt-opt %s | circt-opt | FileCheck %s

esi.service.decl @HostComms {
  esi.service.to_server @Send : !esi.channel<!esi.any>
  esi.service.to_client @Recv : !esi.channel<i8>
}
// CHECK-LABEL: esi.service.decl @HostComms {
// CHECK:         esi.service.to_server @Send : !esi.channel<!esi.any>
// CHECK:         esi.service.to_client @Recv : !esi.channel<i8>

hw.module @Top (%clk: i1) -> () {
  esi.service.instance "topComms" @HostComms (%clk) : (i1) -> ()
  hw.instance "m1" @Loopback (clk: %clk: i1) -> ()
}
// CHECK-LABEL: hw.module @Top(%clk: i1) {
// CHECK:         esi.service.instance "topComms" @HostComms(%clk) : (i1) -> ()
// CHECK:         hw.instance "m1" @Loopback(clk: %clk: i1) -> ()

hw.module @Loopback (%clk: i1) -> () {
  %dataIn = esi.service.req.to_client <@HostComms::@Recv> (["loopback_tohw"]) : !esi.channel<i8>
  esi.service.req.to_server %dataIn -> <@HostComms::@Send> (["loopback_fromhw"]) : !esi.channel<i8>
}
// CHECK-LABEL: hw.module @Loopback(%clk: i1) {
// CHECK:         %0 = esi.service.req.to_client <@HostComms::@Recv>(["loopback_tohw"]) : !esi.channel<i8>
// CHECK:         esi.service.req.to_server %0 -> <@HostComms::@Send>(["loopback_fromhw"]) : !esi.channel<i8>
