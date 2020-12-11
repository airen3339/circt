// RUN: circt-opt %s --lower-esi-to-physical -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck %s
// RUN: circt-opt %s --lower-esi-to-physical --lower-esi-to-rtl -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck --check-prefix=RTL %s

module {
  rtl.externmodule @Sender() -> ( %x: !esi.channel<i1> )
  rtl.externmodule @Reciever(%a: !esi.channel<i1>)

  // CHECK-LABEL: rtl.externmodule @Sender() -> (%x: !esi.channel<i1>)
  // CHECK-LABEL: rtl.externmodule @Reciever(!esi.channel<i1> {rtl.name = "a"})

  // RTL-LABEL: rtl.externmodule @Sender() -> (%x: !esi.channel<i1>)

  rtl.module @test() {
    %esiChan = rtl.instance "sender" @Sender () : () -> (!esi.channel<i1>)
    %bufferedChan = esi.buffer %esiChan { } : i1
    rtl.instance "recv" @Reciever (%bufferedChan) : (!esi.channel<i1>) -> ()

    // CHECK:  %sender.x = rtl.instance "sender" @Sender()  : () -> !esi.channel<i1>
    // CHECK-NEXT:  %0 = esi.stage %sender.x : i1
    // CHECK-NEXT:  rtl.instance "recv" @Reciever(%0)  : (!esi.channel<i1>) -> ()

    %esiChan2 = rtl.instance "sender2" @Sender () : () -> (!esi.channel<i1>)
    %bufferedChan2 = esi.buffer %esiChan2 { stages = 4 } : i1
    rtl.instance "recv2" @Reciever (%bufferedChan2) : (!esi.channel<i1>) -> ()

    // CHECK-NEXT:  %sender2.x = rtl.instance "sender2" @Sender()  : () -> !esi.channel<i1>
    // CHECK-NEXT:  %1 = esi.stage %sender2.x : i1
    // CHECK-NEXT:  %2 = esi.stage %1 : i1
    // CHECK-NEXT:  %3 = esi.stage %2 : i1
    // CHECK-NEXT:  %4 = esi.stage %3 : i1
    // CHECK-NEXT:  rtl.instance "recv2" @Reciever(%4)  : (!esi.channel<i1>) -> ()
  }
}
