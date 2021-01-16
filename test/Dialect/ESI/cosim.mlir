// REQUIRES: capnp
// RUN: circt-opt %s -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck %s
// RUN: circt-opt %s --lower-esi-ports --lower-esi-to-rtl -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck --check-prefix=COSIM %s
// RUN: circt-opt %s --lower-esi-ports --lower-esi-to-rtl | circt-translate --emit-verilog | FileCheck --check-prefix=SV %s
// RUN: circt-translate %s -emit-esi-capnp -verify-diagnostics | FileCheck --check-prefix=CAPNP %s

module {
  rtl.externmodule @Sender() -> ( !esi.channel<si14> { rtl.name = "x"})
  rtl.externmodule @Reciever(%a: !esi.channel<i32>)

  // CHECK-LABEL: rtl.externmodule @Sender() -> (%x: !esi.channel<si14>)
  // CHECK-LABEL: rtl.externmodule @Reciever(!esi.channel<i32> {rtl.name = "a"})

  rtl.module @top(%clk:i1, %rstn:i1) -> () {
    rtl.instance "recv" @Reciever (%cosimRecv) : (!esi.channel<i32>) -> ()
    // CHECK:  rtl.instance "recv" @Reciever(%0)  : (!esi.channel<i32>) -> ()

    %send.x = rtl.instance "send" @Sender () : () -> (!esi.channel<si14>)
    // CHECK:  %send.x = rtl.instance "send" @Sender() : () -> !esi.channel<si14>

    %cosimRecv = esi.cosim %clk, %rstn, %send.x, 1 {name="TestEP"} : !esi.channel<si14> -> !esi.channel<i32>
    // CHECK:  %0 = esi.cosim %clk, %rstn, %send.x, 1 {name = "TestEP"} : !esi.channel<si14> -> !esi.channel<i32>

    // Ensure that the file hash is deterministic.
    // CAPNP: @0xdc4810c19280c1d2;
    // CAPNP-LABEL: struct TYi32 @0xc24ad8e97bb0ff57
    // CAPNP:         i @0 :UInt32;
    // CAPNP-LABEL: struct TYsi14 @0x8ee0bd493e80e8a1
    // CAPNP:         i @0 :Int16;

    // COSIM: rtl.instance "TestEP" @Cosim_Endpoint(%clk, %rstn, %{{.*}}, %{{.*}}, %{{.*}}) {parameters = {ENDPOINT_ID = 1 : i32, RECV_TYPE_ID = 14000240888948784983 : ui64, RECV_TYPE_SIZE_BITS = 128 : i32, SEND_TYPE_ID = 10295436870447851681 : ui64, SEND_TYPE_SIZE_BITS = 128 : i32}} : (i1, i1, i1, i1, i128) -> (i1, !rtl.array<128xi1>, i1)

    // SV: Reciever recv (
    // SV:   .a ({{.*}}.source)
    // SV: );
    // SV: assign _T_0.ready = TestEP_DataInReady;
    // SV: Sender send (
    // SV:   .x ({{.*}}.sink)
    // SV: );
    // SV: Cosim_Endpoint #(.ENDPOINT_ID(32'd1), .RECV_TYPE_ID(64'd14000240888948784983), .RECV_TYPE_SIZE_BITS(32'd128), .SEND_TYPE_ID(64'd10295436870447851681), .SEND_TYPE_SIZE_BITS(32'd128)) TestEP (        // <stdin>:42:66
    // SV:   .clk (clk),
    // SV:   .rstn (rstn),
    // SV:   .DataOutReady ({{.*}}.ready),
    // SV:   .DataInValid ({{.*}}.valid),
    // SV:   .DataIn ({{[{]}}{50'h0, _T_1}, {16'h0, 16'h1, 32'h0}}),
    // SV:   .DataOutValid (TestEP_DataOutValid),
    // SV:   .DataOut (TestEP_DataOut),
    // SV:   .DataInReady (TestEP_DataInReady)
    // SV: );
    // SV: always @(posedge clk) begin
    // SV:   if (TestEP_DataOutValid) begin
    // SV:     assert(/*cast(bit[31:0])*/rootPointer[6'h0+:32] == 32'h0);
    // SV:     assert(/*cast(bit[15:0])*/rootPointer[6'h20+:16] == 16'h1);
    // SV:     assert(/*cast(bit[15:0])*/rootPointer[6'h30+:16] == 16'h0);
    // SV: assign rootPointer = TestEP_DataOut[_T_2+:64];
    // SV: assign dataSection = TestEP_DataOut[_T_3+:64];
    // SV: assign decodedValue = /*cast(bit[31:0])*/dataSection[_T_4+:32];
  }
}
