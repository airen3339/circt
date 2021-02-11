// REQUIRES: capnp
// RUN: circt-opt %s -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck %s
// RUN: circt-opt %s --lower-esi-ports --lower-esi-to-rtl -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck --check-prefix=COSIM %s
// RUN: circt-opt %s --lower-esi-ports --lower-esi-to-rtl | circt-translate --export-verilog | FileCheck --check-prefix=SV %s
// RUN: circt-translate %s -export-esi-capnp -verify-diagnostics | FileCheck --check-prefix=CAPNP %s

rtl.module.extern @Sender() -> ( !esi.channel<si14> { rtl.name = "x"})
rtl.module.extern @Reciever(%a: !esi.channel<i32>)
rtl.module.extern @ArrReciever(%x: !esi.channel<!rtl.array<4xsi64>>)

// CHECK-LABEL: rtl.module.extern @Sender() -> (%x: !esi.channel<si14>)
// CHECK-LABEL: rtl.module.extern @Reciever(!esi.channel<i32> {rtl.name = "a"})
// CHECK-LABEL: rtl.module.extern @ArrReciever(!esi.channel<!rtl.array<4xsi64>> {rtl.name = "x"})

rtl.module @top(%clk:i1, %rstn:i1) -> () {
  rtl.instance "recv" @Reciever (%cosimRecv) : (!esi.channel<i32>) -> ()
  // CHECK:  rtl.instance "recv" @Reciever(%0)  : (!esi.channel<i32>) -> ()

  %send.x = rtl.instance "send" @Sender () : () -> (!esi.channel<si14>)
  // CHECK:  %send.x = rtl.instance "send" @Sender() : () -> !esi.channel<si14>

  %cosimRecv = esi.cosim %clk, %rstn, %send.x, 1 {name="TestEP"} : !esi.channel<si14> -> !esi.channel<i32>
  // CHECK:  esi.cosim %clk, %rstn, %send.x, 1 {name = "TestEP"} : !esi.channel<si14> -> !esi.channel<i32>

  %send2.x = rtl.instance "send2" @Sender () : () -> (!esi.channel<si14>)
  // CHECK:  %send2.x = rtl.instance "send2" @Sender() : () -> !esi.channel<si14>

  %cosimArrRecv = esi.cosim %clk, %rstn, %send2.x, 2 {name="ArrTestEP"} : !esi.channel<si14> -> !esi.channel<!rtl.array<4xsi64>>
  // CHECK:  esi.cosim %clk, %rstn, %send2.x, 2 {name = "ArrTestEP"} : !esi.channel<si14> -> !esi.channel<!rtl.array<4xsi64>>

  rtl.instance "arrRecv" @ArrReciever (%cosimArrRecv) : (!esi.channel<!rtl.array<4 x si64>>) -> ()

  // Ensure that the file hash is deterministic.
  // CAPNP: @0xd3e298e39d351062;
  // CAPNP-LABEL: struct Si14 @0x9bd5e507cce05cc1
  // CAPNP:         i @0 :Int16;
  // CAPNP-LABEL: struct I32 @0x92cd59dfefaacbdb
  // CAPNP:         i @0 :UInt32;
  // Ensure the standard RPC interface is tacked on.
  // CAPNP: interface CosimDpiServer
  // CAPNP: list @0 () -> (ifaces :List(EsiDpiInterfaceDesc));
  // CAPNP: open @1 [S, T] (iface :EsiDpiInterfaceDesc) -> (iface :EsiDpiEndpoint(S, T));

  // COSIM: rtl.instance "TestEP" @Cosim_Endpoint(%clk, %rstn, %{{.+}}, %{{.+}}, %{{.+}}) {parameters = {ENDPOINT_ID = 1 : i32, RECV_TYPE_ID = 10578209918096690139 : ui64, RECV_TYPE_SIZE_BITS = 128 : i32, SEND_TYPE_ID = 11229133067582987457 : ui64, SEND_TYPE_SIZE_BITS = 128 : i32}} : (i1, i1, i1, i1, !rtl.array<128xi1>) -> (i1, !rtl.array<128xi1>, i1)

  // SV: assign _T.valid = TestEP_DataOutValid;
  // SV: assign _T.data = dataSection[6'h0+:32];
  // SV: Reciever recv (
  // SV:   .a ({{.+}}.source)
  // SV: );
  // SV: {{.+}}.ready = TestEP_DataInReady;
  // SV: Sender send (
  // SV:   .x ({{.+}}.sink)
  // SV: );
  // SV: Cosim_Endpoint #(
  // SV:   .ENDPOINT_ID(32'd1),
  // SV:   .RECV_TYPE_ID(64'd10578209918096690139),
  // SV:   .RECV_TYPE_SIZE_BITS(32'd128),
  // SV:   .SEND_TYPE_ID(64'd11229133067582987457),
  // SV:   .SEND_TYPE_SIZE_BITS(32'd128)
  // SV: ) TestEP (
  // SV:   .clk (clk),
  // SV:   .rstn (rstn),
  // SV:   .DataOutReady ({{.+}}.ready),
  // SV:   .DataInValid ({{.+}}.valid),
  // SV:   .DataIn ({50'h0, {{.+}}.data, {16'h0, 16'h1, 30'h0, 2'h0}})
  // SV:   .DataOutValid (TestEP_DataOutValid),
  // SV:   .DataOut (TestEP_DataOut),
  // SV:   .DataInReady (TestEP_DataInReady)
  // SV: );
  // SV: rootPointer = TestEP_DataOut[{{.+}}+:64];
  // SV: dataSection = TestEP_DataOut[{{.+}}+:64];

  // SV:  assign [[IF1:.+]].ready = ArrTestEP_DataInReady;
  // SV:  Sender send2 (
  // SV:    .x ([[IF1]].sink)
  // SV:  );
  // SV:  Cosim_Endpoint #(
  // SV:    .ENDPOINT_ID(32'd2),
  // SV:    .RECV_TYPE_ID(64'd16793803313215739890),
  // SV:    .RECV_TYPE_SIZE_BITS(32'd384),
  // SV:    .SEND_TYPE_ID(64'd11229133067582987457),
  // SV:    .SEND_TYPE_SIZE_BITS(32'd128)
  // SV:  ) ArrTestEP (
  // SV:    .clk          (clk),
  // SV:    .rstn         (rstn),
  // SV:    .DataOutReady ({{.+}}.ready),
  // SV:    .DataInValid  ([[IF1]].valid),
  // SV:    .DataIn       ({50'h0, [[IF1]].data, {16'h0, 16'h1, 30'h0, 2'h0}}),
  // SV:    .DataOutValid (ArrTestEP_DataOutValid),
  // SV:    .DataOut      (ArrTestEP_DataOut),
  // SV:    .DataInReady  (ArrTestEP_DataInReady)
  // SV:  );
  // SV:  always @(posedge clk) begin
  // SV:    if (ArrTestEP_DataOutValid) begin
  // SV:      assert(rootPointer_2[6'h0+:32] == 32'h0);
  // SV:      assert(rootPointer_2[6'h20+:16] == 16'h0);
  // SV:      assert(rootPointer_2[6'h30+:16] == 16'h1);
  // SV:      assert(i_ptr[6'h0+:2] == 2'h0);
  // SV:      assert(i_ptr[6'h1F+:3] == 3'h5);
  // SV:      assert($signed(i_ptr[6'h22+:29]) <= 29'sh0);
  // SV:    end
  // SV:  end // always @(posedge)
  // SV:  wire [63:0] rootPointer_2 = ArrTestEP_DataOut[9'h0+:64];
  // SV:  wire [63:0] ptrSection = ArrTestEP_DataOut[9'h40+:64];
  // SV:  wire [63:0] i_ptr = ptrSection[6'h0+:64];

  // The decode part is missing, but ExportVerilog is currently not using the
  // names I'm assigning since it's inlining them. More work on ExportVerilog is
  // necessary to improve it and I'll fill in the rest when this is done.
}
