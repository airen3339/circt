// RUN: circt-opt -pass-pipeline='firrtl.circuit(firrtl-lower-types)' -split-input-file %s | FileCheck %s

firrtl.circuit "TopLevel" {

  // CHECK-LABEL: firrtl.module @Simple
  // CHECK-SAME: in %[[SOURCE_VALID_NAME:source_valid]]: [[SOURCE_VALID_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: out %[[SOURCE_READY_NAME:source_ready]]: [[SOURCE_READY_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: in %[[SOURCE_DATA_NAME:source_data]]: [[SOURCE_DATA_TYPE:!firrtl.uint<64>]]
  // CHECK-SAME: out %[[SINK_VALID_NAME:sink_valid]]: [[SINK_VALID_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: in %[[SINK_READY_NAME:sink_ready]]: [[SINK_READY_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: out %[[SINK_DATA_NAME:sink_data]]: [[SINK_DATA_TYPE:!firrtl.uint<64>]]
  firrtl.module @Simple(in %source: !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>,
                        out %sink: !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>) {

    // CHECK-NEXT: firrtl.when %[[SOURCE_VALID_NAME]]
    // CHECK-NEXT:   firrtl.connect %[[SINK_DATA_NAME]], %[[SOURCE_DATA_NAME]] : [[SINK_DATA_TYPE]], [[SOURCE_DATA_TYPE]]
    // CHECK-NEXT:   firrtl.connect %[[SINK_VALID_NAME]], %[[SOURCE_VALID_NAME]] : [[SINK_VALID_TYPE]], [[SOURCE_VALID_TYPE]]
    // CHECK-NEXT:   firrtl.connect %[[SOURCE_READY_NAME]], %[[SINK_READY_NAME]] : [[SOURCE_READY_TYPE]], [[SINK_READY_TYPE]]

    %0 = firrtl.subfield %source("valid") : (!firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>) -> !firrtl.uint<1>
    %1 = firrtl.subfield %source("ready") : (!firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>) -> !firrtl.uint<1>
    %2 = firrtl.subfield %source("data") : (!firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>) -> !firrtl.uint<64>
    %3 = firrtl.subfield %sink("valid") : (!firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>) -> !firrtl.uint<1>
    %4 = firrtl.subfield %sink("ready") : (!firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>) -> !firrtl.uint<1>
    %5 = firrtl.subfield %sink("data") : (!firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>) -> !firrtl.uint<64>
    firrtl.when %0 {
      firrtl.connect %5, %2 : !firrtl.uint<64>, !firrtl.uint<64>
      firrtl.connect %3, %0 : !firrtl.uint<1>, !firrtl.uint<1>
      firrtl.connect %1, %4 : !firrtl.uint<1>, !firrtl.uint<1>
    }
  }

  // CHECK-LABEL: firrtl.module @TopLevel
  // CHECK-SAME: in %source_valid: [[SOURCE_VALID_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: out %source_ready: [[SOURCE_READY_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: in %source_data: [[SOURCE_DATA_TYPE:!firrtl.uint<64>]]
  // CHECK-SAME: out %sink_valid: [[SINK_VALID_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: in %sink_ready: [[SINK_READY_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: out %sink_data: [[SINK_DATA_TYPE:!firrtl.uint<64>]]
  firrtl.module @TopLevel(in %source: !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>,
                          out %sink: !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>) {

    // CHECK-NEXT: %inst_source_valid, %inst_source_ready, %inst_source_data, %inst_sink_valid, %inst_sink_ready, %inst_sink_data
    // CHECK-SAME: = firrtl.instance @Simple {name = ""} :
    // CHECK-SAME: !firrtl.flip<uint<1>>, !firrtl.uint<1>, !firrtl.flip<uint<64>>, !firrtl.uint<1>, !firrtl.flip<uint<1>>, !firrtl.uint<64>
    %sourceV, %sinkV = firrtl.instance @Simple {name = ""} : !firrtl.flip<bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>>, !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>

    // CHECK-NEXT: firrtl.connect %inst_source_valid, %source_valid
    // CHECK-NEXT: firrtl.connect %source_ready, %inst_source_ready
    // CHECK-NEXT: firrtl.connect %inst_source_data, %source_data
    // CHECK-NEXT: firrtl.connect %sink_valid, %inst_sink_valid
    // CHECK-NEXT: firrtl.connect %inst_sink_ready, %sink_ready
    // CHECK-NEXT: firrtl.connect %sink_data, %inst_sink_data
    firrtl.connect %sourceV, %source : !firrtl.flip<bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>>, !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>

    firrtl.connect %sink, %sinkV : !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>, !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>
  }
}

// -----

firrtl.circuit "Recursive" {

  // CHECK-LABEL: firrtl.module @Recursive
  // CHECK-SAME: in %[[FLAT_ARG_1_NAME:arg_foo_bar_baz]]: [[FLAT_ARG_1_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: in %[[FLAT_ARG_2_NAME:arg_foo_qux]]: [[FLAT_ARG_2_TYPE:!firrtl.sint<64>]]
  // CHECK-SAME: out %[[OUT_1_NAME:out1]]: [[OUT_1_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: out %[[OUT_2_NAME:out2]]: [[OUT_2_TYPE:!firrtl.sint<64>]]
  firrtl.module @Recursive(in %arg: !firrtl.bundle<foo: bundle<bar: bundle<baz: uint<1>>, qux: sint<64>>>,
                           out %out1: !firrtl.uint<1>, out %out2: !firrtl.sint<64>) {

    // CHECK-NEXT: firrtl.connect %[[OUT_1_NAME]], %[[FLAT_ARG_1_NAME]] : [[OUT_1_TYPE]], [[FLAT_ARG_1_TYPE]]
    // CHECK-NEXT: firrtl.connect %[[OUT_2_NAME]], %[[FLAT_ARG_2_NAME]] : [[OUT_2_TYPE]], [[FLAT_ARG_2_TYPE]]

    %0 = firrtl.subfield %arg("foo") : (!firrtl.bundle<foo: bundle<bar: bundle<baz: uint<1>>, qux: sint<64>>>) -> !firrtl.bundle<bar: bundle<baz: uint<1>>, qux: sint<64>>
    %1 = firrtl.subfield %0("bar") : (!firrtl.bundle<bar: bundle<baz: uint<1>>, qux: sint<64>>) -> !firrtl.bundle<baz: uint<1>>
    %2 = firrtl.subfield %1("baz") : (!firrtl.bundle<baz: uint<1>>) -> !firrtl.uint<1>
    %3 = firrtl.subfield %0("qux") : (!firrtl.bundle<bar: bundle<baz: uint<1>>, qux: sint<64>>) -> !firrtl.sint<64>
    firrtl.connect %out1, %2 : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %out2, %3 : !firrtl.sint<64>, !firrtl.sint<64>
  }

}

// -----

firrtl.circuit "Uniquification" {

  // CHECK-LABEL: firrtl.module @Uniquification
  // CHECK-SAME: in %[[FLATTENED_ARG:a_b]]: [[FLATTENED_TYPE:!firrtl.uint<1>]],
  // CHECK-NOT: %[[FLATTENED_ARG]]
  // CHECK-SAME: in %[[RENAMED_ARG:a_b.+]]: [[RENAMED_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: {portNames = ["a_b", "a_b"]}
  firrtl.module @Uniquification(in %a: !firrtl.bundle<b: uint<1>>, in %a_b: !firrtl.uint<1>) {
  }

}

// -----

firrtl.circuit "Top" {

  // CHECK-LABEL: firrtl.module @Top
  firrtl.module @Top(in %in : !firrtl.bundle<a: uint<1>, b: uint<1>>,
                     out %out : !firrtl.bundle<a: uint<1>, b: uint<1>>) {
    // CHECK: firrtl.connect %out_a, %in_a : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: firrtl.connect %out_b, %in_b : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %out, %in : !firrtl.bundle<a: uint<1>, b: uint<1>>, !firrtl.bundle<a: uint<1>, b: uint<1>>
  }

}

// -----

firrtl.circuit "Foo" {
  // CHECK-LABEL: firrtl.module @Foo
  // CHECK-SAME: in %[[FLAT_ARG_INPUT_NAME:a_b_c]]: [[FLAT_ARG_INPUT_TYPE:!firrtl.uint<1>]]
  // CHECK-SAME: out %[[FLAT_ARG_OUTPUT_NAME:b_b_c]]: [[FLAT_ARG_OUTPUT_TYPE:!firrtl.uint<1>]]
  firrtl.module @Foo(in %a: !firrtl.bundle<b: bundle<c: uint<1>>>, out %b: !firrtl.bundle<b: bundle<c: uint<1>>>) {
    // CHECK: firrtl.connect %[[FLAT_ARG_OUTPUT_NAME]], %[[FLAT_ARG_INPUT_NAME]] : [[FLAT_ARG_OUTPUT_TYPE]], [[FLAT_ARG_INPUT_TYPE]]
    firrtl.connect %b, %a : !firrtl.bundle<b: bundle<c: uint<1>>>, !firrtl.bundle<b: bundle<c: uint<1>>>
  }
}

// -----

// COM: Test lower of a 1-read 1-write aggregate memory
//
// COM: circuit Foo :
// COM:   module Foo :
// COM:     input clock: Clock
// COM:     input rAddr: UInt<4>
// COM:     input rEn: UInt<1>
// COM:     output rData: {a: UInt<8>, b: UInt<8>}
// COM:     input wAddr: UInt<4>
// COM:     input wEn: UInt<1>
// COM:     input wMask: {a: UInt<1>, b: UInt<1>}
// COM:     input wData: {a: UInt<8>, b: UInt<8>}
// COM:
// COM:     mem memory:
// COM:       data-type => {a: UInt<8>, b: UInt<8>}
// COM:       depth => 16
// COM:       reader => r
// COM:       writer => w
// COM:       read-latency => 0
// COM:       write-latency => 1
// COM:       read-under-write => undefined
// COM:
// COM:     memory.r.clk <= clock
// COM:     memory.r.en <= rEn
// COM:     memory.r.addr <= rAddr
// COM:     rData <= memory.r.data
// COM:
// COM:     memory.w.clk <= clock
// COM:     memory.w.en <= wEn
// COM:     memory.w.addr <= wAddr
// COM:     memory.w.mask <= wMask
// COM:     memory.w.data <= wData

firrtl.circuit "Foo" {

  // CHECK-LABEL: firrtl.module @Foo
  firrtl.module @Foo(in %clock: !firrtl.clock, in %rAddr: !firrtl.uint<4>, in %rEn: !firrtl.uint<1>, out %rData: !firrtl.bundle<a: uint<8>, b: uint<8>>, in %wAddr: !firrtl.uint<4>, in %wEn: !firrtl.uint<1>, in %wMask: !firrtl.bundle<a: uint<1>, b: uint<1>>, in %wData: !firrtl.bundle<a: uint<8>, b: uint<8>>) {
    %memory_r, %memory_w = firrtl.mem Undefined {depth = 16 : i64, name = "memory", portNames = ["r", "w"], readLatency = 0 : i32, writeLatency = 1 : i32} : !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: flip<bundle<a: uint<8>, b: uint<8>>>>>, !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: bundle<a: uint<8>, b: uint<8>>, mask: bundle<a: uint<1>, b: uint<1>>>>
    %0 = firrtl.subfield %memory_r("clk") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: flip<bundle<a: uint<8>, b: uint<8>>>>>) -> !firrtl.clock
    firrtl.connect %0, %clock : !firrtl.clock, !firrtl.clock
    %1 = firrtl.subfield %memory_r("en") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: flip<bundle<a: uint<8>, b: uint<8>>>>>) -> !firrtl.uint<1>
    firrtl.connect %1, %rEn : !firrtl.uint<1>, !firrtl.uint<1>
    %2 = firrtl.subfield %memory_r("addr") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: flip<bundle<a: uint<8>, b: uint<8>>>>>) -> !firrtl.uint<4>
    firrtl.connect %2, %rAddr : !firrtl.uint<4>, !firrtl.uint<4>
    %3 = firrtl.subfield %memory_r("data") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: flip<bundle<a: uint<8>, b: uint<8>>>>>) -> !firrtl.bundle<a: uint<8>, b: uint<8>>
    firrtl.connect %rData, %3 : !firrtl.bundle<a: uint<8>, b: uint<8>>, !firrtl.bundle<a: uint<8>, b: uint<8>>
    %4 = firrtl.subfield %memory_w("clk") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: bundle<a: uint<8>, b: uint<8>>, mask: bundle<a: uint<1>, b: uint<1>>>>) -> !firrtl.clock
    firrtl.connect %4, %clock : !firrtl.clock, !firrtl.clock
    %5 = firrtl.subfield %memory_w("en") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: bundle<a: uint<8>, b: uint<8>>, mask: bundle<a: uint<1>, b: uint<1>>>>) -> !firrtl.uint<1>
    firrtl.connect %5, %wEn : !firrtl.uint<1>, !firrtl.uint<1>
    %6 = firrtl.subfield %memory_w("addr") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: bundle<a: uint<8>, b: uint<8>>, mask: bundle<a: uint<1>, b: uint<1>>>>) -> !firrtl.uint<4>
    firrtl.connect %6, %wAddr : !firrtl.uint<4>, !firrtl.uint<4>
    %7 = firrtl.subfield %memory_w("mask") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: bundle<a: uint<8>, b: uint<8>>, mask: bundle<a: uint<1>, b: uint<1>>>>) -> !firrtl.bundle<a: uint<1>, b: uint<1>>
    firrtl.connect %7, %wMask : !firrtl.bundle<a: uint<1>, b: uint<1>>, !firrtl.bundle<a: uint<1>, b: uint<1>>
    %8 = firrtl.subfield %memory_w("data") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: bundle<a: uint<8>, b: uint<8>>, mask: bundle<a: uint<1>, b: uint<1>>>>) -> !firrtl.bundle<a: uint<8>, b: uint<8>>
    firrtl.connect %8, %wData : !firrtl.bundle<a: uint<8>, b: uint<8>>, !firrtl.bundle<a: uint<8>, b: uint<8>>

    // COM: ---------------------------------------------------------------------------------
    // COM: Split memory "a" should exist
    // CHECK: %[[MEMORY_A_R:.+]], %[[MEMORY_A_W:.+]] = firrtl.mem {{.+}} data: uint<8>, mask: uint<1>
    // COM: ---------------------------------------------------------------------------------
    // COM: Read port
    // CHECK-DAG: %[[MEMORY_A_R_ADDR:.+]] = firrtl.subfield %[[MEMORY_A_R]]("addr")
    // CHECK-DAG: %[[MEMORY_R_ADDR:.+]] = firrtl.wire
    // CHECK: firrtl.connect %[[MEMORY_A_R_ADDR]], %[[MEMORY_R_ADDR]]
    // CHECK-DAG: %[[MEMORY_A_R_EN:.+]] = firrtl.subfield %[[MEMORY_A_R]]("en")
    // CHECK-DAG: %[[MEMORY_R_EN:.+]] = firrtl.wire
    // CHECK: firrtl.connect %[[MEMORY_A_R_EN]], %[[MEMORY_R_EN]]
    // CHECK-DAG: %[[MEMORY_A_R_CLK:.+]] = firrtl.subfield %[[MEMORY_A_R]]("clk")
    // CHECK-DAG: %[[MEMORY_R_CLK:.+]] = firrtl.wire
    // CHECK: firrtl.connect %[[MEMORY_A_R_CLK]], %[[MEMORY_R_CLK]]
    // CHECK: %[[MEMORY_A_R_DATA:.+]] = firrtl.subfield %[[MEMORY_A_R]]("data")
    // COM: ---------------------------------------------------------------------------------
    // COM: Write Port
    // CHECK-DAG: %[[MEMORY_A_W_ADDR:.+]] = firrtl.subfield %[[MEMORY_A_W]]("addr")
    // CHECK-DAG: %[[MEMORY_W_ADDR:.+]] = firrtl.wire
    // CHECK: firrtl.connect %[[MEMORY_A_W_ADDR]], %[[MEMORY_W_ADDR]]
    // CHECK-DAG: %[[MEMORY_A_W_EN:.+]] = firrtl.subfield %[[MEMORY_A_W]]("en")
    // CHECK-DAG: %[[MEMORY_W_EN:.+]] = firrtl.wire
    // CHECK: firrtl.connect %[[MEMORY_A_W_EN]], %[[MEMORY_W_EN]]
    // CHECK-DAG: %[[MEMORY_A_W_CLK:.+]] = firrtl.subfield %[[MEMORY_A_W]]("clk")
    // CHECK-DAG: %[[MEMORY_W_CLK:.+]] = firrtl.wire
    // CHECK: firrtl.connect %[[MEMORY_A_W_CLK]], %[[MEMORY_W_CLK]]
    // CHECK: %[[MEMORY_A_W_DATA:.+]] = firrtl.subfield %[[MEMORY_A_W]]("data")
    // CHECK: %[[MEMORY_A_W_MASK:.+]] = firrtl.subfield %[[MEMORY_A_W]]("mask")
    // COM: ---------------------------------------------------------------------------------
    // COM: Split memory "b" should exist
    // CHECK: %[[MEMORY_B_R:.+]], %[[MEMORY_B_W:.+]] = firrtl.mem {{.+}} data: uint<8>, mask: uint<1>
    // COM: ---------------------------------------------------------------------------------
    // COM: Read port
    // CHECK: %[[MEMORY_B_R_ADDR:.+]] = firrtl.subfield %[[MEMORY_B_R]]("addr")
    // CHECK: firrtl.connect %[[MEMORY_B_R_ADDR]], %[[MEMORY_R_ADDR]]
    // CHECK: %[[MEMORY_B_R_EN:.+]] = firrtl.subfield %[[MEMORY_B_R]]("en")
    // CHECK: firrtl.connect %[[MEMORY_B_R_EN]], %[[MEMORY_R_EN]]
    // CHECK: %[[MEMORY_B_R_CLK:.+]] = firrtl.subfield %[[MEMORY_B_R]]("clk")
    // CHECK: firrtl.connect %[[MEMORY_B_R_CLK]], %[[MEMORY_R_CLK]]
    // CHECK: %[[MEMORY_B_R_DATA:.+]] = firrtl.subfield %[[MEMORY_B_R]]("data")
    // COM: ---------------------------------------------------------------------------------
    // COM: Write port
    // CHECK: %[[MEMORY_B_W_ADDR:.+]] = firrtl.subfield %[[MEMORY_B_W]]("addr")
    // CHECK: firrtl.connect %[[MEMORY_B_W_ADDR]], %[[MEMORY_W_ADDR]]
    // CHECK: %[[MEMORY_B_W_EN:.+]] = firrtl.subfield %[[MEMORY_B_W]]("en")
    // CHECK: firrtl.connect %[[MEMORY_B_W_EN]], %[[MEMORY_W_EN]]
    // CHECK: %[[MEMORY_B_W_CLK:.+]] = firrtl.subfield %[[MEMORY_B_W]]("clk")
    // CHECK: firrtl.connect %[[MEMORY_B_W_CLK]], %[[MEMORY_W_CLK]]
    // CHECK: %[[MEMORY_B_W_DATA:.+]] = firrtl.subfield %[[MEMORY_B_W]]("data")
    // CHECK: %[[MEMORY_B_W_MASK:.+]] = firrtl.subfield %[[MEMORY_B_W]]("mask")
    // COM: ---------------------------------------------------------------------------------
    // COM: Connections to module ports
    // CHECK: firrtl.connect %[[MEMORY_R_CLK]], %clock
    // CHECK: firrtl.connect %[[MEMORY_R_EN]], %rEn
    // CHECK: firrtl.connect %[[MEMORY_R_ADDR]], %rAddr
    // CHECK: firrtl.connect %rData_a, %[[MEMORY_A_R_DATA]]
    // CHECK: firrtl.connect %rData_b, %[[MEMORY_B_R_DATA]]
    // CHECK: firrtl.connect %[[MEMORY_W_CLK]], %clock
    // CHECK: firrtl.connect %[[MEMORY_W_EN]], %wEn
    // CHECK: firrtl.connect %[[MEMORY_W_ADDR]], %wAddr
    // CHECK: firrtl.connect %[[MEMORY_A_W_MASK]], %wMask_a
    // CHECK: firrtl.connect %[[MEMORY_B_W_MASK]], %wMask_b
    // CHECK: firrtl.connect %[[MEMORY_A_W_DATA]], %wData_a
    // CHECK: firrtl.connect %[[MEMORY_B_W_DATA]], %wData_b

  }
}

// -----

// COM: Test that a memory with a readwrite port is split into 1r1w
//
// circuit Foo:
//  module Foo:
//    input clock: Clock
//    input rwEn: UInt<1>
//    input rwMode: UInt<1>
//    input rwAddr: UInt<4>
//    input rwMask: UInt<1>
//    input rwDataIn: UInt<8>
//    output rwDataOut: UInt<8>
//
//    mem memory:
//      data-type => UInt<8>
//      depth => 16
//      readwriter => rw
//      read-latency => 0
//      write-latency => 1
//      read-under-write => undefined
//
//    memory.rw.clk <= clock
//    memory.rw.en <= rwEn
//    memory.rw.addr <= rwAddr
//    memory.rw.wmode <= rwMode
//    memory.rw.wmask <= rwMask
//    memory.rw.wdata <= rwDataIn
//    rwDataOut <= memory.rw.rdata

firrtl.circuit "MemoryRWSplit" {
  firrtl.module @MemoryRWSplit(in %clock: !firrtl.clock, in %rwEn: !firrtl.uint<1>, in %rwMode: !firrtl.uint<1>, in %rwAddr: !firrtl.uint<4>, in %rwMask: !firrtl.uint<1>, in %rwDataIn: !firrtl.uint<8>, out %rwDataOut: !firrtl.uint<8>) {
    %memory_rw = firrtl.mem Undefined {depth = 16 : i64, name = "memory", portNames = ["rw"], readLatency = 0 : i32, writeLatency = 1 : i32} : !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, wmode: uint<1>, rdata: flip<uint<8>>, wdata: uint<8>, wmask: uint<1>>>
    %0 = firrtl.subfield %memory_rw("clk") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, wmode: uint<1>, rdata: flip<uint<8>>, wdata: uint<8>, wmask: uint<1>>>) -> !firrtl.clock
    firrtl.connect %0, %clock : !firrtl.clock, !firrtl.clock
    %1 = firrtl.subfield %memory_rw("en") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, wmode: uint<1>, rdata: flip<uint<8>>, wdata: uint<8>, wmask: uint<1>>>) -> !firrtl.uint<1>
    firrtl.connect %1, %rwEn : !firrtl.uint<1>, !firrtl.uint<1>
    %2 = firrtl.subfield %memory_rw("addr") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, wmode: uint<1>, rdata: flip<uint<8>>, wdata: uint<8>, wmask: uint<1>>>) -> !firrtl.uint<4>
    firrtl.connect %2, %rwAddr : !firrtl.uint<4>, !firrtl.uint<4>
    %3 = firrtl.subfield %memory_rw("wmode") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, wmode: uint<1>, rdata: flip<uint<8>>, wdata: uint<8>, wmask: uint<1>>>) -> !firrtl.uint<1>
    firrtl.connect %3, %rwMode : !firrtl.uint<1>, !firrtl.uint<1>
    %4 = firrtl.subfield %memory_rw("wmask") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, wmode: uint<1>, rdata: flip<uint<8>>, wdata: uint<8>, wmask: uint<1>>>) -> !firrtl.uint<1>
    firrtl.connect %4, %rwMask : !firrtl.uint<1>, !firrtl.uint<1>
    %5 = firrtl.subfield %memory_rw("wdata") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, wmode: uint<1>, rdata: flip<uint<8>>, wdata: uint<8>, wmask: uint<1>>>) -> !firrtl.uint<8>
    firrtl.connect %5, %rwDataIn : !firrtl.uint<8>, !firrtl.uint<8>
    %6 = firrtl.subfield %memory_rw("rdata") : (!firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, wmode: uint<1>, rdata: flip<uint<8>>, wdata: uint<8>, wmask: uint<1>>>) -> !firrtl.uint<8>
    firrtl.connect %rwDataOut, %6 : !firrtl.uint<8>, !firrtl.uint<8>
  }

  // CHECK-LABEL: firrtl.module @MemoryRWSplit
  // COM: ---------------------------------------------------------------------------------
  // COM: The read write port, "rw", was split into "rw_r" and "rw_w"
  // CHECK: %memory_rw_r, %memory_rw_w = firrtl.mem
  // COM:   - port names are updated correctly
  // CHECK-SAME: portNames = ["rw_r", "rw_w"]
  // COM:   - the types are correct for read and write ports
  // CHECK-SAME: !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: flip<uint<8>>>>, !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: uint<8>, mask: uint<1>>>
  // COM: ---------------------------------------------------------------------------------
  // COM: Read port is hooked up correctly
  // COM:   - address is "rw_addr"
  // CHECK: %memory_rw_addr = firrtl.wire
  // CHECK: %[[R_ADDR:.+]] = firrtl.subfield %memory_rw_r("addr")
  // CHECK: firrtl.connect %[[R_ADDR]], %memory_rw_addr
  // COM:   - enable is "rw_en && !rw_wmode"
  // CHECK: %memory_rw_en = firrtl.wire
  // CHECK: %memory_rw_wmode = firrtl.wire
  // CHECK: %[[NOT_WRITE:.+]] = firrtl.not %memory_rw_wmode
  // CHECK: %[[EN_AND_NOT_WRITE:.+]] = firrtl.and %memory_rw_en, %[[NOT_WRITE]]
  // CHECK: %[[R_EN:.+]] = firrtl.subfield %memory_rw_r("en")
  // CHECK: firrtl.connect %[[R_EN]], %[[EN_AND_NOT_WRITE]]
  // COM:   - clk is "rw_clk"
  // CHECK: %memory_rw_clk = firrtl.wire
  // CHECK: %[[R_CLK:.+]] = firrtl.subfield %memory_rw_r("clk")
  // CHECK: firrtl.connect %[[R_CLK]], %memory_rw_clk
  // COM:   - data has a reference
  // CHECK: %[[R_DATA:.+]] = firrtl.subfield %memory_rw_r("data")
  // COM: ---------------------------------------------------------------------------------
  // COM: Write port is hooked up correctly.
  // COM:   - address is "rw_addr"
  // CHECK: %[[W_ADDR:.+]] = firrtl.subfield %memory_rw_w("addr")
  // CHECK: firrtl.connect %[[W_ADDR]], %memory_rw_addr
  // COM:   - enable is "rw_en && rw_wmode"
  // CHECK: %[[EN_AND_WRITE:.+]] = firrtl.and %memory_rw_en, %memory_rw_wmode
  // CHECK: %[[W_EN:.+]] = firrtl.subfield %memory_rw_w("en")
  // CHECK: firrtl.connect %[[W_EN]], %[[EN_AND_WRITE]]
  // COM:   - clk is "rw_clk"
  // CHECK: %[[W_CLK:.+]] = firrtl.subfield %memory_rw_w("clk")
  // CHECK: firrtl.connect %[[W_CLK]], %memory_rw_clk
  // COM:   - data has a reference
  // CHECK: %[[W_DATA:.+]] = firrtl.subfield %memory_rw_w("data")
  // COM:   - mask has a reference
  // CHECK: %[[W_MASK:.+]] = firrtl.subfield %memory_rw_w("mask")
  // COM: ---------------------------------------------------------------------------------
  // COM: Check that the lowering is worked.
  // CHECK: firrtl.connect %memory_rw_clk, %clock
  // CHECK: firrtl.connect %memory_rw_en, %rwEn
  // CHECK: firrtl.connect %memory_rw_addr, %rwAddr
  // CHECK: firrtl.connect %memory_rw_wmode, %rwMode
  // CHECK: firrtl.connect %[[W_MASK]], %rwMask
  // CHECK: firrtl.connect %[[W_DATA]], %rwDataIn
  // CHECK: firrtl.connect %rwDataOut, %[[R_DATA]]
}

// -----

firrtl.circuit "MemoryRWSplitUnique" {
  firrtl.module @MemoryRWSplitUnique() {
    %memory_rw, %memory_rw_r, %memory_rw_w = firrtl.mem Undefined {depth = 16 : i64, name = "memory", portNames = ["rw", "rw_r", "rw_w"], readLatency = 0 : i32, writeLatency = 1 : i32} : !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, wmode: uint<1>, rdata: flip<uint<8>>, wdata: uint<8>, wmask: uint<1>>>, !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: flip<uint<8>>>>, !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: uint<8>, mask: uint<1>>>
  }

  // CHECK-LABEL: firrtl.module @MemoryRWSplitUnique
  // CHECK: %memory_rw_r, %memory_rw_w, %memory_rw_r0, %memory_rw_w0 = firrtl.mem
  // COM:   - port names are updated correctly
  // CHECK-SAME: portNames = ["rw_r", "rw_w", "rw_r0", "rw_w0"]

}

// -----
// https://github.com/llvm/circt/issues/593

module  {
  firrtl.circuit "top_mod" {
    firrtl.module @mod_2(in %clock: !firrtl.clock, in %inp_a: !firrtl.bundle<inp_d: uint<14>>) {
    }
    firrtl.module @top_mod(in %clock: !firrtl.clock) {
      %U0_clock, %U0_inp_a = firrtl.instance @mod_2 {name = "U0"} : !firrtl.flip<clock>, !firrtl.flip<bundle<inp_d: uint<14>>>
      %0 = firrtl.invalidvalue : !firrtl.clock
      firrtl.connect %U0_clock, %0 : !firrtl.flip<clock>, !firrtl.clock
      %1 = firrtl.invalidvalue : !firrtl.bundle<inp_d: uint<14>>
      firrtl.connect %U0_inp_a, %1 : !firrtl.flip<bundle<inp_d: uint<14>>>, !firrtl.bundle<inp_d: uint<14>>
    }
  }
}

//CHECK-LABEL: module  {
//CHECK-NEXT:   firrtl.circuit "top_mod" {
//CHECK-NEXT:     firrtl.module @mod_2(in %clock: !firrtl.clock, in %inp_a_inp_d: !firrtl.uint<14>) {
//CHECK-NEXT:     }
//CHECK-NEXT:    firrtl.module @top_mod(in %clock: !firrtl.clock) {
//CHECK-NEXT:      %U0_clock, %U0_inp_a_inp_d = firrtl.instance @mod_2 {name = "U0"} : !firrtl.flip<clock>, !firrtl.flip<uint<14>>
//CHECK-NEXT:      %invalid_clock = firrtl.invalidvalue : !firrtl.clock
//CHECK-NEXT:      firrtl.connect %U0_clock, %invalid_clock : !firrtl.flip<clock>, !firrtl.clock
//CHECK-NEXT:      %invalid_ui14 = firrtl.invalidvalue : !firrtl.uint<14>
//CHECK-NEXT:      firrtl.connect %U0_inp_a_inp_d, %invalid_ui14 : !firrtl.flip<uint<14>>, !firrtl.uint<14>
//CHECK-NEXT:    }
//CHECK-NEXT:  }
//CHECK-NEXT:}

// -----
// https://github.com/llvm/circt/issues/661

// COM: This test is just checking that the following doesn't error.
module  {
  firrtl.circuit "Issue661" {
    // CHECK-LABEL: firrtl.module @Issue661
    firrtl.module @Issue661(in %clock: !firrtl.clock) {
      %head_MPORT_2, %head_MPORT_6 = firrtl.mem Undefined {depth = 20 : i64, name = "head", portNames = ["MPORT_2", "MPORT_6"], readLatency = 0 : i32, writeLatency = 1 : i32}
      : !firrtl.flip<bundle<addr: uint<5>, en: uint<1>, clk: clock, data: uint<5>, mask: uint<1>>>,
        !firrtl.flip<bundle<addr: uint<5>, en: uint<1>, clk: clock, data: uint<5>, mask: uint<1>>>
      %127 = firrtl.subfield %head_MPORT_6("clk") : (!firrtl.flip<bundle<addr: uint<5>, en: uint<1>, clk: clock, data: uint<5>, mask: uint<1>>>) -> !firrtl.clock
    }
  }
}

// -----

// Check that a non-bundled mux ops are untouched.
firrtl.circuit "Mux" {
    // check-label: firrtl.module @Mux
    firrtl.module @Mux(in %p: !firrtl.uint<1>, in %a: !firrtl.uint<1>, in %b: !firrtl.uint<1>, out %c: !firrtl.uint<1>) {
      // check-next: %0 = firrtl.mux(%p, %a, %b) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
      // check-next: firrtl.connect %c, %0 : !firrtl.uint<1>, !firrtl.uint<1>
      %0 = firrtl.mux(%p, %a, %b) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
      firrtl.connect %c, %0 : !firrtl.uint<1>, !firrtl.uint<1>
    }
}

// -----


firrtl.circuit "MuxBundle" {
    // CHECK-LABEL: firrtl.module @MuxBundle
    firrtl.module @MuxBundle(in %p: !firrtl.uint<1>, in %a: !firrtl.bundle<a: uint<1>>, in %b: !firrtl.bundle<a: uint<1>>, out %c: !firrtl.bundle<a: uint<1>>) {
      // CHECK-NEXT: %0 = firrtl.mux(%p, %a_a, %b_a) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
      // CHECK-NEXT: firrtl.connect %c_a, %0 : !firrtl.uint<1>, !firrtl.uint<1>
      %0 = firrtl.mux(%p, %a, %b) : (!firrtl.uint<1>, !firrtl.bundle<a: uint<1>>, !firrtl.bundle<a: uint<1>>) -> !firrtl.bundle<a: uint<1>>
      firrtl.connect %c, %0 : !firrtl.bundle<a: uint<1>>, !firrtl.bundle<a: uint<1>>
    }
}

// -----

firrtl.circuit "NodeBundle" {
    // CHECK-LABEL: firrtl.module @NodeBundle
    firrtl.module @NodeBundle(in %a: !firrtl.bundle<a: uint<1>>, out %b: !firrtl.uint<1>) {
      // CHECK-NEXT: %n_a = firrtl.node %a_a  : !firrtl.uint<1>
      // CHECK-NEXT: firrtl.connect %b, %n_a : !firrtl.uint<1>, !firrtl.uint<1>
      %n = firrtl.node %a : !firrtl.bundle<a: uint<1>>
      %n_a = firrtl.subfield %n("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
      firrtl.connect %b, %n_a : !firrtl.uint<1>, !firrtl.uint<1>
    }
}

// -----

firrtl.circuit "RegBundle" {
    // CHECK-LABEL: firrtl.module @RegBundle(in %a_a: !firrtl.uint<1>, in %clk: !firrtl.clock, out %b_a: !firrtl.uint<1>) {
    firrtl.module @RegBundle(in %a: !firrtl.bundle<a: uint<1>>, in %clk: !firrtl.clock, out %b: !firrtl.bundle<a: uint<1>>) {
      // CHECK-NEXT: %x_a = firrtl.reg %clk : (!firrtl.clock) -> !firrtl.uint<1>
      // CHECK-NEXT: firrtl.connect %x_a, %a_a : !firrtl.uint<1>, !firrtl.uint<1>
      // CHECK-NEXT: firrtl.connect %b_a, %x_a : !firrtl.uint<1>, !firrtl.uint<1>
      %x = firrtl.reg %clk {name = "x"} : (!firrtl.clock) -> !firrtl.bundle<a: uint<1>>
      %0 = firrtl.subfield %x("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
      %1 = firrtl.subfield %a("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
      firrtl.connect %0, %1 : !firrtl.uint<1>, !firrtl.uint<1>
      %2 = firrtl.subfield %b("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
      %3 = firrtl.subfield %x("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
      firrtl.connect %2, %3 : !firrtl.uint<1>, !firrtl.uint<1>
    }
}

// -----

firrtl.circuit "RegBundleWithBulkConnect" {
    // CHECK-LABEL: firrtl.module @RegBundleWithBulkConnect(in %a_a: !firrtl.uint<1>, in %clk: !firrtl.clock, out %b_a: !firrtl.uint<1>) {
    firrtl.module @RegBundleWithBulkConnect(in %a: !firrtl.bundle<a: uint<1>>, in %clk: !firrtl.clock, out %b: !firrtl.bundle<a: uint<1>>) {
      // CHECK-NEXT: %x_a = firrtl.reg %clk : (!firrtl.clock) -> !firrtl.uint<1>
      // CHECK-NEXT: firrtl.connect %x_a, %a_a : !firrtl.uint<1>, !firrtl.uint<1>
      // CHECK-NEXT: firrtl.connect %b_a, %x_a : !firrtl.uint<1>, !firrtl.uint<1>
      %x = firrtl.reg %clk {name = "x"} : (!firrtl.clock) -> !firrtl.bundle<a: uint<1>>
      firrtl.connect %x, %a : !firrtl.bundle<a: uint<1>>, !firrtl.bundle<a: uint<1>>
      firrtl.connect %b, %x : !firrtl.bundle<a: uint<1>>, !firrtl.bundle<a: uint<1>>
    }
}

// -----

firrtl.circuit "WireBundle" {
    // CHECK-LABEL: firrtl.module @WireBundle(in %a_a: !firrtl.uint<1>,  out %b_a: !firrtl.uint<1>) {
    firrtl.module @WireBundle(in %a: !firrtl.bundle<a: uint<1>>,  out %b: !firrtl.bundle<a: uint<1>>) {
      // CHECK-NEXT: %x_a = firrtl.wire  : !firrtl.uint<1>
      // CHECK-NEXT: firrtl.connect %x_a, %a_a : !firrtl.uint<1>, !firrtl.uint<1>
      // CHECK-NEXT: firrtl.connect %b_a, %x_a : !firrtl.uint<1>, !firrtl.uint<1>
      %x = firrtl.wire : !firrtl.bundle<a: uint<1>>
      %0 = firrtl.subfield %x("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
      %1 = firrtl.subfield %a("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
      firrtl.connect %0, %1 : !firrtl.uint<1>, !firrtl.uint<1>
      %2 = firrtl.subfield %b("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
      %3 = firrtl.subfield %x("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
      firrtl.connect %2, %3 : !firrtl.uint<1>, !firrtl.uint<1>
    }
}

// -----

firrtl.circuit "WireBundlesWithBulkConnect" {
  // CHECK-LABEL: firrtl.module @WireBundlesWithBulkConnect
  firrtl.module @WireBundlesWithBulkConnect(in %source: !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>,
                             out %sink: !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>) {
    // CHECK: %w_valid = firrtl.wire  : !firrtl.uint<1>
    // CHECK: %w_ready = firrtl.wire  : !firrtl.uint<1>
    // CHECK: %w_data = firrtl.wire  : !firrtl.uint<64>
    %w = firrtl.wire : !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>
    // CHECK: firrtl.connect %w_valid, %source_valid : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: firrtl.connect %source_ready, %w_ready : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: firrtl.connect %w_data, %source_data : !firrtl.uint<64>, !firrtl.uint<64>
    firrtl.connect %w, %source : !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>, !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>
    // CHECK: firrtl.connect %sink_valid, %w_valid : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: firrtl.connect %w_ready, %sink_ready : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: firrtl.connect %sink_data, %w_data : !firrtl.uint<64>, !firrtl.uint<64>
    firrtl.connect %sink, %w : !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>, !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>
  }
}

// -----
// COM: Test vector lowering
firrtl.circuit "LowerVectors" {
  firrtl.module @LowerVectors(in %a: !firrtl.vector<uint<1>, 2>, out %b: !firrtl.vector<uint<1>, 2>) {
    firrtl.connect %b, %a: !firrtl.vector<uint<1>, 2>, !firrtl.vector<uint<1>, 2>
  }
  // CHECK-LABEL: firrtl.module @LowerVectors(in %a_0: !firrtl.uint<1>, in %a_1: !firrtl.uint<1>, out %b_0: !firrtl.uint<1>, out %b_1: !firrtl.uint<1>)
  // CHECK: firrtl.connect %b_0, %a_0
  // CHECK: firrtl.connect %b_1, %a_1
}

// -----

// COM: Test vector of bundles lowering
firrtl.circuit "LowerVectorsOfBundles" {
  // CHECK-LABEL: firrtl.module @LowerVectorsOfBundles(in %in_0_a: !firrtl.uint<1>, out %in_0_b: !firrtl.uint<1>, in %in_1_a: !firrtl.uint<1>, out %in_1_b: !firrtl.uint<1>, out %out_0_a: !firrtl.uint<1>, in %out_0_b: !firrtl.uint<1>, out %out_1_a: !firrtl.uint<1>, in %out_1_b: !firrtl.uint<1>) {
  firrtl.module @LowerVectorsOfBundles(in %in: !firrtl.vector<bundle<a : uint<1>, b : flip<uint<1>>>, 2>,
                                       out %out: !firrtl.vector<bundle<a : uint<1>, b : flip<uint<1>>>, 2>) {
    // CHECK: firrtl.connect %out_0_a, %in_0_a : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: firrtl.connect %in_0_b, %out_0_b : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: firrtl.connect %out_1_a, %in_1_a : !firrtl.uint<1>, !firrtl.uint<1>
    // CHECK: firrtl.connect %in_1_b, %out_1_b : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.connect %out, %in: !firrtl.vector<bundle<a : uint<1>, b : flip<uint<1>>>, 2>, !firrtl.vector<bundle<a : uint<1>, b : flip<uint<1>>>, 2>
  }
}

// -----
firrtl.circuit "ExternalModule" {
  // CHECK-LABEL: firrtl.extmodule @ExternalModule(in %source_valid: !firrtl.uint<1>, out %source_ready: !firrtl.uint<1>, in %source_data: !firrtl.uint<64>)
  firrtl.extmodule @ExternalModule(in %source: !firrtl.bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>> )
  firrtl.module @Test() {
    // CHECK:  %inst_source_valid, %inst_source_ready, %inst_source_data = firrtl.instance @ExternalModule  {name = ""} : !firrtl.flip<uint<1>>, !firrtl.uint<1>, !firrtl.flip<uint<64>>
    %inst_source = firrtl.instance @ExternalModule {name = ""} : !firrtl.flip<bundle<valid: uint<1>, ready: flip<uint<1>>, data: uint<64>>>
  }
}

// -----

// Test RegResetOp lowering
firrtl.circuit "LowerRegResetOp" {
  // CHECK-LABEL: firrtl.module @LowerRegResetOp
  firrtl.module @LowerRegResetOp(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %a_d: !firrtl.vector<uint<1>, 2>, out %a_q: !firrtl.vector<uint<1>, 2>) {
    %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
    %init = firrtl.wire  : !firrtl.vector<uint<1>, 2>
    %0 = firrtl.subindex %init[0] : !firrtl.vector<uint<1>, 2>
    firrtl.connect %0, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
    %1 = firrtl.subindex %init[1] : !firrtl.vector<uint<1>, 2>
    firrtl.connect %1, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
    %r = firrtl.regreset %clock, %reset, %init {name = "r"} : (!firrtl.clock, !firrtl.uint<1>, !firrtl.vector<uint<1>, 2>) -> !firrtl.vector<uint<1>, 2>
    firrtl.connect %r, %a_d : !firrtl.vector<uint<1>, 2>, !firrtl.vector<uint<1>, 2>
    firrtl.connect %a_q, %r : !firrtl.vector<uint<1>, 2>, !firrtl.vector<uint<1>, 2>
  }
  // CHECK:   %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  // CHECK:   %init_0 = firrtl.wire  : !firrtl.uint<1>
  // CHECK:   %init_1 = firrtl.wire  : !firrtl.uint<1>
  // CHECK:   firrtl.connect %init_0, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   firrtl.connect %init_1, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   %r_0 = firrtl.regreset %clock, %reset, %init_0 : (!firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  // CHECK:   %r_1 = firrtl.regreset %clock, %reset, %init_1 : (!firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  // CHECK:   firrtl.connect %r_0, %a_d_0 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   firrtl.connect %r_1, %a_d_1 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   firrtl.connect %a_q_0, %r_0 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   firrtl.connect %a_q_1, %r_1 : !firrtl.uint<1>, !firrtl.uint<1>
}

// -----

// Test RegResetOp lowering without name attribute
// https://github.com/llvm/circt/issues/795
firrtl.circuit "LowerRegResetOpNoName" {
  // CHECK-LABEL: firrtl.module @LowerRegResetOpNoName
  firrtl.module @LowerRegResetOpNoName(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %a_d: !firrtl.vector<uint<1>, 2>, out %a_q: !firrtl.vector<uint<1>, 2>) {
    %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
    %init = firrtl.wire  : !firrtl.vector<uint<1>, 2>
    %0 = firrtl.subindex %init[0] : !firrtl.vector<uint<1>, 2>
    firrtl.connect %0, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
    %1 = firrtl.subindex %init[1] : !firrtl.vector<uint<1>, 2>
    firrtl.connect %1, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
    %r = firrtl.regreset %clock, %reset, %init {name = ""} : (!firrtl.clock, !firrtl.uint<1>, !firrtl.vector<uint<1>, 2>) -> !firrtl.vector<uint<1>, 2>
    firrtl.connect %r, %a_d : !firrtl.vector<uint<1>, 2>, !firrtl.vector<uint<1>, 2>
    firrtl.connect %a_q, %r : !firrtl.vector<uint<1>, 2>, !firrtl.vector<uint<1>, 2>
  }
  // CHECK:   %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
  // CHECK:   %init_0 = firrtl.wire  : !firrtl.uint<1>
  // CHECK:   %init_1 = firrtl.wire  : !firrtl.uint<1>
  // CHECK:   firrtl.connect %init_0, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   firrtl.connect %init_1, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   %0 = firrtl.regreset %clock, %reset, %init_0 : (!firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  // CHECK:   %1 = firrtl.regreset %clock, %reset, %init_1 : (!firrtl.clock, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
  // CHECK:   firrtl.connect %0, %a_d_0 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   firrtl.connect %1, %a_d_1 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   firrtl.connect %a_q_0, %0 : !firrtl.uint<1>, !firrtl.uint<1>
  // CHECK:   firrtl.connect %a_q_1, %1 : !firrtl.uint<1>, !firrtl.uint<1>
}

// -----

// Test RegOp lowering without name attribute
// https://github.com/llvm/circt/issues/795
firrtl.circuit "lowerRegOpNoName" {
  // CHECK-LABEL: firrtl.module @lowerRegOpNoName
  firrtl.module @lowerRegOpNoName(in %clock: !firrtl.clock, in %a_d: !firrtl.vector<uint<1>, 2>, out %a_q: !firrtl.vector<uint<1>, 2>) {
    %r = firrtl.reg %clock {name = ""} : (!firrtl.clock) -> !firrtl.vector<uint<1>, 2>
      firrtl.connect %r, %a_d : !firrtl.vector<uint<1>, 2>, !firrtl.vector<uint<1>, 2>
      firrtl.connect %a_q, %r : !firrtl.vector<uint<1>, 2>, !firrtl.vector<uint<1>, 2>
  }
 // CHECK:    %0 = firrtl.reg %clock : (!firrtl.clock) -> !firrtl.uint<1>
 // CHECK:    %1 = firrtl.reg %clock : (!firrtl.clock) -> !firrtl.uint<1>
 // CHECK:    firrtl.connect %0, %a_d_0 : !firrtl.uint<1>, !firrtl.uint<1>
 // CHECK:    firrtl.connect %1, %a_d_1 : !firrtl.uint<1>, !firrtl.uint<1>
 // CHECK:    firrtl.connect %a_q_0, %0 : !firrtl.uint<1>, !firrtl.uint<1>
 // CHECK:    firrtl.connect %a_q_1, %1 : !firrtl.uint<1>, !firrtl.uint<1>
}

// -----

// Test that InstanceOp Annotations are copied to the new instance.
// CHECK-LABEL: firrtl.circuit "AnnotationsInstanceOp"
firrtl.circuit "AnnotationsInstanceOp" {
  firrtl.module @Bar(out %a: !firrtl.vector<uint<1>, 2>) {
    %0 = firrtl.invalidvalue : !firrtl.vector<uint<1>, 2>
    firrtl.connect %a, %0 : !firrtl.vector<uint<1>, 2>, !firrtl.vector<uint<1>, 2>
  }
  firrtl.module @AnnotationsInstanceOp() {
    %bar_a = firrtl.instance @Bar  {annotations = [{a = "a"}], name = "bar"} : !firrtl.vector<uint<1>, 2>
  }
  // CHECK: firrtl.instance
  // CHECK-SAME: annotations = [{a = "a"}]
}

// -----

// Test that MemOp Annotations are copied to lowered MemOps.
firrtl.circuit "AnnotationsMemOp" {
  // CHECK-LABEL: firrtl.module @AnnotationsMemOp
  firrtl.module @AnnotationsMemOp() {
    %bar_r, %bar_w = firrtl.mem Undefined  {annotations = [{a = "a"}], depth = 16 : i64, name = "bar", portNames = ["r", "w"], readLatency = 0 : i32, writeLatency = 1 : i32} : !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: flip<vector<uint<8>, 2>>>>, !firrtl.flip<bundle<addr: uint<4>, en: uint<1>, clk: clock, data: vector<uint<8>, 2>, mask: vector<uint<1>, 2>>>
  }
  // CHECK: firrtl.mem
  // CHECK-SAME: annotations = [{a = "a"}]
  // CHECK: firrtl.mem
  // CHECK-SAME: annotations = [{a = "a"}]
}

// -----

// Test that WireOp Annotations are copied to lowered WireOps.
firrtl.circuit "AnnotationsWireOp" {
  // CHECK-LABEL: firrtl.module @AnnotationsWireOp
  firrtl.module @AnnotationsWireOp() {
    %bar = firrtl.wire  {annotations = [{a = "a"}]} : !firrtl.vector<uint<1>, 2>
  }
  // CHECK: firrtl.wire
  // CHECK-SAME: annotations = [{a = "a"}]
  // CHECK: firrtl.wire
  // CHECK-SAME: annotations = [{a = "a"}]
}

// -----

// Test that Reg/RegResetOp Annotations are copied to lowered registers.
firrtl.circuit "AnnotationsRegOp" {
  // CHECK-LABEL: firrtl.module @AnnotationsRegOp
  firrtl.module @AnnotationsRegOp(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>) {
    %bazInit = firrtl.wire  : !firrtl.vector<uint<1>, 2>
    %0 = firrtl.subindex %bazInit[0] : !firrtl.vector<uint<1>, 2>
    %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
    firrtl.connect %0, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
    %1 = firrtl.subindex %bazInit[1] : !firrtl.vector<uint<1>, 2>
    firrtl.connect %1, %c0_ui1 : !firrtl.uint<1>, !firrtl.uint<1>
    %bar = firrtl.reg %clock  {annotations = [{a = "a"}], name = "bar"} : (!firrtl.clock) -> !firrtl.vector<uint<1>, 2>
    %baz = firrtl.regreset %clock, %reset, %bazInit  {annotations = [{b = "b"}], name = "baz"} : (!firrtl.clock, !firrtl.uint<1>, !firrtl.vector<uint<1>, 2>) -> !firrtl.vector<uint<1>, 2>
  }
  // CHECK: firrtl.reg
  // CHECK-SAME: annotations = [{a = "a"}]
  // CHECK: firrtl.reg
  // CHECK-SAME: annotations = [{a = "a"}]
  // CHECK: firrtl.regreset
  // CHECK-SAME: annotations = [{b = "b"}]
  // CHECK: firrtl.regreset
  // CHECK-SAME: annotations = [{b = "b"}]
}

// -----

// Test that WhenOp with regions has its regions lowered.
firrtl.circuit "WhenOp" {
  firrtl.module @WhenOp (in %p: !firrtl.uint<1>,
                         in %in : !firrtl.bundle<a: uint<1>, b: uint<1>>,
                         out %out : !firrtl.bundle<a: uint<1>, b: uint<1>>) {
    // No else region.
    firrtl.when %p {
      // CHECK: firrtl.connect %out_a, %in_a : !firrtl.uint<1>, !firrtl.uint<1>
      // CHECK: firrtl.connect %out_b, %in_b : !firrtl.uint<1>, !firrtl.uint<1>
      firrtl.connect %out, %in : !firrtl.bundle<a: uint<1>, b: uint<1>>, !firrtl.bundle<a: uint<1>, b: uint<1>>
    }

    // Else region.
    firrtl.when %p {
      // CHECK: firrtl.connect %out_a, %in_a : !firrtl.uint<1>, !firrtl.uint<1>
      // CHECK: firrtl.connect %out_b, %in_b : !firrtl.uint<1>, !firrtl.uint<1>
      firrtl.connect %out, %in : !firrtl.bundle<a: uint<1>, b: uint<1>>, !firrtl.bundle<a: uint<1>, b: uint<1>>
    } else {
      // CHECK: firrtl.connect %out_a, %in_a : !firrtl.uint<1>, !firrtl.uint<1>
      // CHECK: firrtl.connect %out_b, %in_b : !firrtl.uint<1>, !firrtl.uint<1>
      firrtl.connect %out, %in : !firrtl.bundle<a: uint<1>, b: uint<1>>, !firrtl.bundle<a: uint<1>, b: uint<1>>
    }
  }
}

// -----

// Test that subfield annotations on wire are lowred to appropriate instance based on target.
firrtl.circuit "AnnotationsBundle" {
  firrtl.module @AnnotationsBundle() {
    %bar = firrtl.wire  {annotations = [{one, target = [".qux"]}, {target = ["[1]", ".baz"], two}]} : !firrtl.vector<bundle<baz: uint<1>, qux: uint<1>>, 2>

      // CHECK: %bar_0_baz = firrtl.wire  : !firrtl.uint<1>
      // CHECK: %bar_0_qux = firrtl.wire  : !firrtl.uint<1>
      // CHECK: %bar_1_baz = firrtl.wire  {annotations = [{two}]} : !firrtl.uint<1>
      // CHECK: %bar_1_qux = firrtl.wire  : !firrtl.uint<1>
  }
}

// -----

// Test that subfield annotations on reg are lowred to appropriate instance based on target.
firrtl.circuit "AnnotationsBundle2" {
  firrtl.module @AnnotationsBundle2(in %clock: !firrtl.clock) {
    %bar = firrtl.reg %clock  {annotations = [{one, target = [".qux"]}, {target = ["[1]", ".baz"], two}]} : (!firrtl.clock) -> !firrtl.vector<bundle<baz: uint<1>, qux: uint<1>>, 2>

    // CHECK: %bar_0_baz = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_0_qux = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_1_baz = firrtl.reg %clock  {annotations = [{two}]} : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_1_qux = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
  }
}

// -----

// Test that subfield annotations on reg are lowred to appropriate instance based on target. Ignore un-flattened array targets
// circuit Foo: %[[{"one":null,"target":"~Foo|Foo>bar[0].qux[0]"},{"two":null,"target":"~Foo|Foo>bar[1].baz"},{"three":null,"target":"~Foo|Foo>bar[0].yes"} ]]

firrtl.circuit "AnnotationsBundle3" {
  firrtl.module @AnnotationsBundle3(in %clock: !firrtl.clock) {
    %bar = firrtl.reg %clock  {annotations = [{one, target = ["[0]", ".qux", "[0]"]}, {target = ["[1]", ".baz"], two}, {target = ["[0]", ".yes"], three}]} : (!firrtl.clock) -> !firrtl.vector<bundle<baz: vector<uint<1>, 2>, qux: vector<uint<1>, 2>, yes: bundle<a: uint<1>, b: uint<1>>>, 2>

    // CHECK: %bar_0_baz_0 = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_0_baz_1 = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_0_qux_0 = firrtl.reg %clock  {annotations = [{one}]} : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_0_qux_1 = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_0_yes_a = firrtl.reg %clock  {annotations = [{three}]} : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_0_yes_b = firrtl.reg %clock  {annotations = [{three}]} : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_1_baz_0 = firrtl.reg %clock  {annotations = [{two}]} : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_1_baz_1 = firrtl.reg %clock  {annotations = [{two}]} : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_1_qux_0 = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_1_qux_1 = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_1_yes_a = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
    // CHECK: %bar_1_yes_b = firrtl.reg %clock  : (!firrtl.clock) -> !firrtl.uint<1>
  }
}

// -----

// Test wire connection semantics.  Based on the flippedness of the destination
// type, the connection may be reversed.
firrtl.circuit "WireSemantics"  {
  firrtl.module @WireSemantics() {
    %a = firrtl.wire  : !firrtl.bundle<a: bundle<a: uint<1>>>
    %ax = firrtl.wire  : !firrtl.bundle<a: bundle<a: uint<1>>>
    firrtl.connect %a, %ax : !firrtl.bundle<a: bundle<a: uint<1>>>, !firrtl.bundle<a: bundle<a: uint<1>>>
    firrtl.partialconnect %a, %ax : !firrtl.bundle<a: bundle<a: uint<1>>>, !firrtl.bundle<a: bundle<a: uint<1>>>
    // COM: a <= ax
    // CHECK: firrtl.connect %a_a_a, %ax_a_a
    // COM: a <- ax
    // CHECK-NEXT: firrtl.partialconnect %a_a_a, %ax_a_a
    %0 = firrtl.subfield %a("a") : (!firrtl.bundle<a: bundle<a: uint<1>>>) -> !firrtl.bundle<a: uint<1>>
    %1 = firrtl.subfield %ax("a") : (!firrtl.bundle<a: bundle<a: uint<1>>>) -> !firrtl.bundle<a: uint<1>>
    firrtl.connect %0, %1 : !firrtl.bundle<a: uint<1>>, !firrtl.bundle<a: uint<1>>
    firrtl.partialconnect %0, %1 : !firrtl.bundle<a: uint<1>>, !firrtl.bundle<a: uint<1>>
    // COM: a.a <= ax.a
    // CHECK: firrtl.connect %a_a_a, %ax_a_a
    // COM: a.a <- ax.a
    // CHECK-NEXT: firrtl.partialconnect %a_a_a, %ax_a_a
    %2 = firrtl.subfield %a("a") : (!firrtl.bundle<a: bundle<a: uint<1>>>) -> !firrtl.bundle<a: uint<1>>
    %3 = firrtl.subfield %2("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
    %4 = firrtl.subfield %ax("a") : (!firrtl.bundle<a: bundle<a: uint<1>>>) -> !firrtl.bundle<a: uint<1>>
    %5 = firrtl.subfield %4("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
    firrtl.connect %3, %5 : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.partialconnect %3, %5 : !firrtl.uint<1>, !firrtl.uint<1>
    // COM: a.a.a <= ax.a.a
    // CHECK: firrtl.connect %a_a_a, %ax_a_a
    // COM: a.a.a <- ax.a.a
    // CHECK-NEXT: firrtl.partialconnect %a_a_a, %ax_a_a
    %b = firrtl.wire  : !firrtl.bundle<a: bundle<a: flip<uint<1>>>>
    %bx = firrtl.wire  : !firrtl.bundle<a: bundle<a: flip<uint<1>>>>
    firrtl.connect %b, %bx : !firrtl.bundle<a: bundle<a: flip<uint<1>>>>, !firrtl.bundle<a: bundle<a: flip<uint<1>>>>
    firrtl.partialconnect %b, %bx : !firrtl.bundle<a: bundle<a: flip<uint<1>>>>, !firrtl.bundle<a: bundle<a: flip<uint<1>>>>
    // COM: b <= bx
    // CHECK: firrtl.connect %bx_a_a, %b_a_a
    // COM: b <- bx
    // CHECK: firrtl.partialconnect %bx_a_a, %b_a_a
    %6 = firrtl.subfield %b("a") : (!firrtl.bundle<a: bundle<a: flip<uint<1>>>>) -> !firrtl.bundle<a: flip<uint<1>>>
    %7 = firrtl.subfield %bx("a") : (!firrtl.bundle<a: bundle<a: flip<uint<1>>>>) -> !firrtl.bundle<a: flip<uint<1>>>
    firrtl.connect %6, %7 : !firrtl.bundle<a: flip<uint<1>>>, !firrtl.bundle<a: flip<uint<1>>>
    firrtl.partialconnect %6, %7 : !firrtl.bundle<a: flip<uint<1>>>, !firrtl.bundle<a: flip<uint<1>>>
    // COM: b.a <= bx.a
    // CHECK: firrtl.connect %bx_a_a, %b_a_a
    // COM: b.a <- bx.a
    // CHECK: firrtl.partialconnect %bx_a_a, %b_a_a
    %8 = firrtl.subfield %b("a") : (!firrtl.bundle<a: bundle<a: flip<uint<1>>>>) -> !firrtl.bundle<a: flip<uint<1>>>
    %9 = firrtl.subfield %8("a") : (!firrtl.bundle<a: flip<uint<1>>>) -> !firrtl.uint<1>
    %10 = firrtl.subfield %bx("a") : (!firrtl.bundle<a: bundle<a: flip<uint<1>>>>) -> !firrtl.bundle<a: flip<uint<1>>>
    %11 = firrtl.subfield %10("a") : (!firrtl.bundle<a: flip<uint<1>>>) -> !firrtl.uint<1>
    firrtl.connect %9, %11 : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.partialconnect %9, %11 : !firrtl.uint<1>, !firrtl.uint<1>
    // COM: b.a.a <= bx.a.a
    // CHECK: firrtl.connect %b_a_a, %bx_a_a
    // COM: b.a.a <- bx.a.a
    // CHECK: firrtl.partialconnect %b_a_a, %bx_a_a
    %c = firrtl.wire  : !firrtl.bundle<a: flip<bundle<a: uint<1>>>>
    %cx = firrtl.wire  : !firrtl.bundle<a: flip<bundle<a: uint<1>>>>
    firrtl.connect %c, %cx : !firrtl.bundle<a: flip<bundle<a: uint<1>>>>, !firrtl.bundle<a: flip<bundle<a: uint<1>>>>
    firrtl.partialconnect %c, %cx : !firrtl.bundle<a: flip<bundle<a: uint<1>>>>, !firrtl.bundle<a: flip<bundle<a: uint<1>>>>
    // COM: c <= cx
    // CHECK: firrtl.connect %cx_a_a, %c_a_a
    // COM: c <- cx
    // CHECK: firrtl.partialconnect %cx_a_a, %c_a_a
    %12 = firrtl.subfield %c("a") : (!firrtl.bundle<a: flip<bundle<a: uint<1>>>>) -> !firrtl.bundle<a: uint<1>>
    %13 = firrtl.subfield %cx("a") : (!firrtl.bundle<a: flip<bundle<a: uint<1>>>>) -> !firrtl.bundle<a: uint<1>>
    firrtl.connect %12, %13 : !firrtl.bundle<a: uint<1>>, !firrtl.bundle<a: uint<1>>
    firrtl.partialconnect %12, %13 : !firrtl.bundle<a: uint<1>>, !firrtl.bundle<a: uint<1>>
    // COM: c.a <= cx.a
    // CHECK: firrtl.connect %c_a_a, %cx_a_a
    // COM: c.a <- cx.a
    // CHECK: firrtl.partialconnect %c_a_a, %cx_a_a
    %14 = firrtl.subfield %c("a") : (!firrtl.bundle<a: flip<bundle<a: uint<1>>>>) -> !firrtl.bundle<a: uint<1>>
    %15 = firrtl.subfield %14("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
    %16 = firrtl.subfield %cx("a") : (!firrtl.bundle<a: flip<bundle<a: uint<1>>>>) -> !firrtl.bundle<a: uint<1>>
    %17 = firrtl.subfield %16("a") : (!firrtl.bundle<a: uint<1>>) -> !firrtl.uint<1>
    firrtl.connect %15, %17 : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.partialconnect %15, %17 : !firrtl.uint<1>, !firrtl.uint<1>
    // COM: c.a.a <= cx.a.a
    // CHECK: firrtl.connect %c_a_a, %cx_a_a
    // COM: c.a.a <- cx.a.a
    // CHECK: firrtl.partialconnect %c_a_a, %cx_a_a
    %d = firrtl.wire  : !firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>
    %dx = firrtl.wire  : !firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>
    firrtl.connect %d, %dx : !firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>, !firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>
    firrtl.partialconnect %d, %dx : !firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>, !firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>
    // COM: d <= dx
    // CHECK: firrtl.connect %d_a_a, %dx_a_a
    // COM: d <- dx
    // CHECK: firrtl.partialconnect %d_a_a, %dx_a_a
    %18 = firrtl.subfield %d("a") : (!firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>) -> !firrtl.bundle<a: flip<uint<1>>>
    %19 = firrtl.subfield %dx("a") : (!firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>) -> !firrtl.bundle<a: flip<uint<1>>>
    firrtl.connect %18, %19 : !firrtl.bundle<a: flip<uint<1>>>, !firrtl.bundle<a: flip<uint<1>>>
    firrtl.partialconnect %18, %19 : !firrtl.bundle<a: flip<uint<1>>>, !firrtl.bundle<a: flip<uint<1>>>
    // COM: d.a <= dx.a
    // CHECK: firrtl.connect %dx_a_a, %d_a_a
    // COM: d.a <- dx.a
    // CHECK: firrtl.partialconnect %dx_a_a, %d_a_a
    %20 = firrtl.subfield %d("a") : (!firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>) -> !firrtl.bundle<a: flip<uint<1>>>
    %21 = firrtl.subfield %20("a") : (!firrtl.bundle<a: flip<uint<1>>>) -> !firrtl.uint<1>
    %22 = firrtl.subfield %dx("a") : (!firrtl.bundle<a: flip<bundle<a: flip<uint<1>>>>>) -> !firrtl.bundle<a: flip<uint<1>>>
    %23 = firrtl.subfield %22("a") : (!firrtl.bundle<a: flip<uint<1>>>) -> !firrtl.uint<1>
    firrtl.connect %21, %23 : !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.partialconnect %21, %23 : !firrtl.uint<1>, !firrtl.uint<1>
    // COM: d.a.a <= dx.a.a
    // CHECK: firrtl.connect %d_a_a, %dx_a_a
    // COM: d.a.a <- dx.a.a
    // CHECK: firrtl.partialconnect %d_a_a, %dx_a_a
  }
}

// -----

// Test corner cases of partial connect semantics.
firrtl.circuit "PartialConnectEdgeCases" {
  firrtl.module @PartialConnectEdgeCases() {
    // COM: Only matching fields are connected.
    %a = firrtl.wire : !firrtl.bundle<a: uint<1>, b: uint<1>, c: uint<1>>
    %b = firrtl.wire : !firrtl.bundle<a: uint<1>, b: uint<1>>
    firrtl.partialconnect %a, %b : !firrtl.bundle<a: uint<1>, b: uint<1>, c: uint<1>>, !firrtl.bundle<a: uint<1>, b: uint<1>>
    // CHECK: firrtl.partialconnect %a_a, %b_a
    // CHECK-NEXT: firrtl.partialconnect %a_b, %b_b
    // CHECK-NOT: firrtl.partialconnect %a_

    firrtl.partialconnect %b, %a : !firrtl.bundle<a: uint<1>, b: uint<1>>, !firrtl.bundle<a: uint<1>, b: uint<1>, c: uint<1>>
    // CHECK: firrtl.partialconnect %b_a, %a_a
    // CHECK-NEXT: firrtl.partialconnect %b_b, %a_b
    // CHECK-NOT: firrtl.partialconnect %b_

    // COM: Only the first 'n' elements in a vector are connected.
    %c = firrtl.wire : !firrtl.vector<uint<1>, 2>
    %d = firrtl.wire : !firrtl.vector<uint<1>, 3>
    firrtl.partialconnect %c, %d : !firrtl.vector<uint<1>, 2>, !firrtl.vector<uint<1>, 3>
    // CHECK: firrtl.partialconnect %c_0, %d_0
    // CHECK-NEXT: firrtl.partialconnect %c_1, %d_1
    // CHECK-NOT: firrtl.partialconnect %c_

    firrtl.partialconnect %d, %c : !firrtl.vector<uint<1>, 3>, !firrtl.vector<uint<1>, 2>
    // CHECK: firrtl.partialconnect %d_0, %c_0
    // CHECK-NEXT: firrtl.partialconnect %d_1, %c_1
    // CHECK-NOT: firrtl.partialconnect %d_
  }
}

// -----

// Test that annotations on aggregate ports are copied.
firrtl.circuit "Port" {
  firrtl.extmodule @Sub(in %a: !firrtl.vector<uint<1>, 2> {firrtl.annotations = [{a}]})
  // CHECK: firrtl.extmodule
  // CHECK-COUNT-2: firrtl.annotations = [{a}]
  // CHECK-NOT: firrtl.annotations = [{a}]
  firrtl.module @Port(in %a: !firrtl.vector<uint<1>, 2> {firrtl.annotations = [{b}]}) {
    %sub_a = firrtl.instance @Sub  {name = "sub", portNames = ["a"]} : !firrtl.flip<vector<uint<1>, 2>>
    firrtl.connect %sub_a, %a : !firrtl.flip<vector<uint<1>, 2>>, !firrtl.vector<uint<1>, 2>
  }
  // CHECK: firrtl.module
  // CHECK-COUNT-2: firrtl.annotations = [{b}]
  // CHECK-NOT: firrtl.annotations = [{b}]
}

// -----

// Test that annotations on subfield/subindices of ports are only applied to
// matching targets.  Any other arg attributes should be copied.
module  {
  firrtl.circuit "PortBundle"  {
    // The annotation should be copied to just a.a.  The firrtl.hello arg
    // attribute should be copied to each new port.
    firrtl.module @PortBundle(in %a: !firrtl.bundle<a: uint<1>, b: flip<uint<1>>> {firrtl.annotations = [{a, target = [".a"]}], firrtl.hello}) {}
    // CHECK: firrtl.module @PortBundle
    // CHECK-COUNT-1: firrtl.annotations = [{a}]
    // CHECK-COUNT-2: firrtl.hello
    // CHECK-NOT: firrtl.annotations
    // CHECK-NOT: firrtl.hello

    // The annotation should be copied to just a[0].  The firrtl.world arg
    // attribute should be copied to each port.
    firrtl.extmodule @PortVector(in %a: !firrtl.vector<uint<1>, 2> {firrtl.annotations = [{b, target = ["[0]"]}], firrtl.world})
    // CHECK: firrtl.extmodule @PortVector
    // CHECK-COUNT-1: firrtl.annotations = [{b}]
    // CHECK-COUNT-2: firrtl.world
    // CHECK-NOT: firrtl.annotations
    // CHECK-NOT: firrtl.world
  }
}

// -----
// Test lowering of SubAccessOp
module  {

// COM:  module Foo:
// COM:    input b: UInt<1>
// COM:    input sel: UInt<2>
// COM:    input default: UInt<1>[4]
// COM:    output a: UInt<1>[4]
// COM: 
// COM:     a <= default
// COM:     a[sel] <= b

firrtl.circuit "write1D"  {
  firrtl.module @write1D(in %b: !firrtl.uint<1>, in %sel: !firrtl.uint<2>, in %default: !firrtl.vector<uint<1>, 4>, out %a: !firrtl.vector<uint<1>, 4>) {
    firrtl.connect %a, %default : !firrtl.vector<uint<1>, 4>, !firrtl.vector<uint<1>, 4>
    %0 = firrtl.subaccess %a[%sel] : !firrtl.vector<uint<1>, 4>, !firrtl.uint<2>
    firrtl.connect %0, %b : !firrtl.uint<1>, !firrtl.uint<1>
  }
}
// CHECK: firrtl.module @write1D(in %b: !firrtl.uint<1>, in %sel: !firrtl.uint<2>, in %default_0: !firrtl.uint<1>, in %default_1: !firrtl.uint<1>, in %default_2: !firrtl.uint<1>, in %default_3: !firrtl.uint<1>, out %a_0: !firrtl.uint<1>, out %a_1: !firrtl.uint<1>, out %a_2: !firrtl.uint<1>, out %a_3: !firrtl.uint<1>) {
// CHECK:   firrtl.connect %a_0, %default_0 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   firrtl.connect %a_1, %default_1 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   firrtl.connect %a_2, %default_2 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   firrtl.connect %a_3, %default_3 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   %0 = firrtl.wire  : !firrtl.uint<1>
// CHECK:   %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui2 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %1 = firrtl.eq %sel, %c1_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %2 = firrtl.and %c1_ui1, %1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %3 = firrtl.mux(%2, %0, %a_1) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   firrtl.connect %a_1, %3 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %4 = firrtl.eq %sel, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %5 = firrtl.and %c1_ui1, %4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %6 = firrtl.mux(%5, %0, %a_2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   firrtl.connect %a_2, %6 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %7 = firrtl.eq %sel, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %8 = firrtl.and %c1_ui1, %7 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %9 = firrtl.mux(%8, %0, %a_3) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   firrtl.connect %a_3, %9 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   firrtl.connect %0, %b : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK: }


// COM: circuit read1D:
// COM:   module read1D:
// COM:     input a: UInt<2>[4]
// COM:     input sel: UInt<2>
// COM:     input default: UInt<2>[4]
// COM:     output b: UInt<2>
// COM: 
// COM:     wire z : UInt<2>[4]
// COM:     z <= default 
// COM:     b <= sub(a[sel],z[sel])

firrtl.circuit "read1D"  {
  firrtl.module @read1D(in %a: !firrtl.vector<uint<2>, 4>, in %sel: !firrtl.uint<2>, in %default: !firrtl.vector<uint<2>, 4>, out %b: !firrtl.uint<2>) {
    %z = firrtl.wire  : !firrtl.vector<uint<2>, 4>
    firrtl.connect %z, %default : !firrtl.vector<uint<2>, 4>, !firrtl.vector<uint<2>, 4>
    %0 = firrtl.subaccess %a[%sel] : !firrtl.vector<uint<2>, 4>, !firrtl.uint<2>
    %1 = firrtl.subaccess %z[%sel] : !firrtl.vector<uint<2>, 4>, !firrtl.uint<2>
    %2 = firrtl.sub %0, %1 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<3>
    firrtl.partialconnect %b, %2 : !firrtl.uint<2>, !firrtl.uint<3>
  }
}
// CHECK: firrtl.module @read1D(in %a_0: !firrtl.uint<2>, in %a_1: !firrtl.uint<2>, in %a_2: !firrtl.uint<2>, in %a_3: !firrtl.uint<2>, in %sel: !firrtl.uint<2>, in %default_0: !firrtl.uint<2>, in %default_1: !firrtl.uint<2>, in %default_2: !firrtl.uint<2>, in %default_3: !firrtl.uint<2>, out %b: !firrtl.uint<2>) {
// CHECK:   %z_0 = firrtl.wire  : !firrtl.uint<2>
// CHECK:   %z_1 = firrtl.wire  : !firrtl.uint<2>
// CHECK:   %z_2 = firrtl.wire  : !firrtl.uint<2>
// CHECK:   %z_3 = firrtl.wire  : !firrtl.uint<2>
// CHECK:   firrtl.connect %z_0, %default_0 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   firrtl.connect %z_1, %default_1 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   firrtl.connect %z_2, %default_2 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   firrtl.connect %z_3, %default_3 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui2 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %0 = firrtl.eq %sel, %c1_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %1 = firrtl.and %c1_ui1, %0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %2 = firrtl.mux(%1, %a_1, %a_0) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %3 = firrtl.eq %sel, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %4 = firrtl.and %c1_ui1, %3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %5 = firrtl.mux(%4, %a_2, %2) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %6 = firrtl.eq %sel, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %7 = firrtl.and %c1_ui1, %6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %8 = firrtl.mux(%7, %a_3, %5) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c1_ui1_0 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui2_1 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %9 = firrtl.eq %sel, %c1_ui2_1 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %10 = firrtl.and %c1_ui1_0, %9 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %11 = firrtl.mux(%10, %z_1, %z_0) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c2_ui2_2 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %12 = firrtl.eq %sel, %c2_ui2_2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %13 = firrtl.and %c1_ui1_0, %12 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %14 = firrtl.mux(%13, %z_2, %11) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c3_ui2_3 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %15 = firrtl.eq %sel, %c3_ui2_3 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %16 = firrtl.and %c1_ui1_0, %15 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %17 = firrtl.mux(%16, %z_3, %14) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %18 = firrtl.sub %8, %17 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<3>
// CHECK:   firrtl.partialconnect %b, %18 : !firrtl.uint<2>, !firrtl.uint<3>
// CHECK: }


// COM: circuit Foo:
// COM:   module Foo:
// COM:     input a: {wo: UInt<1>, valid: UInt<2>}
// COM:     input def: {wo: UInt<1>, valid: UInt<2>}[4]
// COM:     input sel: UInt<2>
// COM:     output b: {wo: UInt<1>, valid: UInt<2>}[4]
// COM: 
// COM:     b <= def 
// COM:     b[sel].wo <= a.wo
firrtl.circuit "writeVectorOfBundle1D"  {
  firrtl.module @writeVectorOfBundle1D(in %a: !firrtl.bundle<wo: uint<1>, valid: uint<2>>, in %def: !firrtl.vector<bundle<wo: uint<1>, valid: uint<2>>, 4>, in %sel: !firrtl.uint<2>, out %b: !firrtl.vector<bundle<wo: uint<1>, valid: uint<2>>, 4>) {
    firrtl.connect %b, %def : !firrtl.vector<bundle<wo: uint<1>, valid: uint<2>>, 4>, !firrtl.vector<bundle<wo: uint<1>, valid: uint<2>>, 4>
    %0 = firrtl.subaccess %b[%sel] : !firrtl.vector<bundle<wo: uint<1>, valid: uint<2>>, 4>, !firrtl.uint<2>
    %1 = firrtl.subfield %0("wo") : (!firrtl.bundle<wo: uint<1>, valid: uint<2>>) -> !firrtl.uint<1>
    %2 = firrtl.subfield %a("wo") : (!firrtl.bundle<wo: uint<1>, valid: uint<2>>) -> !firrtl.uint<1>
    firrtl.connect %1, %2 : !firrtl.uint<1>, !firrtl.uint<1>
  }
}
// CHECK: firrtl.module @writeVectorOfBundle1D(in %a_wo: !firrtl.uint<1>, in %a_valid: !firrtl.uint<2>, in %def_0_wo: !firrtl.uint<1>, in %def_0_valid: !firrtl.uint<2>, in %def_1_wo: !firrtl.uint<1>, in %def_1_valid: !firrtl.uint<2>, in %def_2_wo: !firrtl.uint<1>, in %def_2_valid: !firrtl.uint<2>, in %def_3_wo: !firrtl.uint<1>, in %def_3_valid: !firrtl.uint<2>, in %sel: !firrtl.uint<2>, out %b_0_wo: !firrtl.uint<1>, out %b_0_valid: !firrtl.uint<2>, out %b_1_wo: !firrtl.uint<1>, out %b_1_valid: !firrtl.uint<2>, out %b_2_wo: !firrtl.uint<1>, out %b_2_valid: !firrtl.uint<2>, out %b_3_wo: !firrtl.uint<1>, out %b_3_valid: !firrtl.uint<2>) {
// CHECK:   firrtl.connect %b_0_wo, %def_0_wo : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   firrtl.connect %b_0_valid, %def_0_valid : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   firrtl.connect %b_1_wo, %def_1_wo : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   firrtl.connect %b_1_valid, %def_1_valid : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   firrtl.connect %b_2_wo, %def_2_wo : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   firrtl.connect %b_2_valid, %def_2_valid : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   firrtl.connect %b_3_wo, %def_3_wo : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   firrtl.connect %b_3_valid, %def_3_valid : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   %0 = firrtl.wire  : !firrtl.uint<1>
// CHECK:   %1 = firrtl.wire  : !firrtl.uint<2>
// CHECK:   %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui2 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %2 = firrtl.eq %sel, %c1_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %3 = firrtl.and %c1_ui1, %2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %4 = firrtl.mux(%3, %0, %b_1_wo) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   firrtl.connect %b_1_wo, %4 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   %5 = firrtl.mux(%3, %1, %b_1_valid) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   firrtl.connect %b_1_valid, %5 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %6 = firrtl.eq %sel, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %7 = firrtl.and %c1_ui1, %6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %8 = firrtl.mux(%7, %0, %b_2_wo) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   firrtl.connect %b_2_wo, %8 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   %9 = firrtl.mux(%7, %1, %b_2_valid) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   firrtl.connect %b_2_valid, %9 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %10 = firrtl.eq %sel, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %11 = firrtl.and %c1_ui1, %10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %12 = firrtl.mux(%11, %0, %b_3_wo) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   firrtl.connect %b_3_wo, %12 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   %13 = firrtl.mux(%11, %1, %b_3_valid) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   firrtl.connect %b_3_valid, %13 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   firrtl.connect %0, %a_wo : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK: }


// COM:  circuit Foo:
// COM:    module Foo:
// COM:      input a: {wo: UInt<1>[4], valid: UInt<2>[4]}
// COM:      input sel: UInt<2>
// COM:      output b: {wo: UInt<1>, valid: UInt<2>}
// COM:  
// COM:      b.wo <= a.wo[sel]
// COM:      b.valid <= a.valid[sel]

firrtl.circuit "readBundleOfVector1D"  {
  firrtl.module @readBundleOfVector1D(in %a: !firrtl.bundle<wo: vector<uint<1>, 4>, valid: vector<uint<2>, 4>>, in %sel: !firrtl.uint<2>, out %b: !firrtl.bundle<wo: uint<1>, valid: uint<2>>) {
    %0 = firrtl.subfield %b("wo") : (!firrtl.bundle<wo: uint<1>, valid: uint<2>>) -> !firrtl.uint<1>
    %1 = firrtl.subfield %a("wo") : (!firrtl.bundle<wo: vector<uint<1>, 4>, valid: vector<uint<2>, 4>>) -> !firrtl.vector<uint<1>, 4>
    %2 = firrtl.subaccess %1[%sel] : !firrtl.vector<uint<1>, 4>, !firrtl.uint<2>
    firrtl.connect %0, %2 : !firrtl.uint<1>, !firrtl.uint<1>
    %3 = firrtl.subfield %b("valid") : (!firrtl.bundle<wo: uint<1>, valid: uint<2>>) -> !firrtl.uint<2>
    %4 = firrtl.subfield %a("valid") : (!firrtl.bundle<wo: vector<uint<1>, 4>, valid: vector<uint<2>, 4>>) -> !firrtl.vector<uint<2>, 4>
    %5 = firrtl.subaccess %4[%sel] : !firrtl.vector<uint<2>, 4>, !firrtl.uint<2>
    firrtl.connect %3, %5 : !firrtl.uint<2>, !firrtl.uint<2>
  }
}
// CHECK: firrtl.module @readBundleOfVector1D(in %a_wo_0: !firrtl.uint<1>, in %a_wo_1: !firrtl.uint<1>, in %a_wo_2: !firrtl.uint<1>, in %a_wo_3: !firrtl.uint<1>, in %a_valid_0: !firrtl.uint<2>, in %a_valid_1: !firrtl.uint<2>, in %a_valid_2: !firrtl.uint<2>, in %a_valid_3: !firrtl.uint<2>, in %sel: !firrtl.uint<2>, out %b_wo: !firrtl.uint<1>, out %b_valid: !firrtl.uint<2>) {
// CHECK:   %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui2 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %0 = firrtl.eq %sel, %c1_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %1 = firrtl.and %c1_ui1, %0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %2 = firrtl.mux(%1, %a_wo_1, %a_wo_0) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %3 = firrtl.eq %sel, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %4 = firrtl.and %c1_ui1, %3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %5 = firrtl.mux(%4, %a_wo_2, %2) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %6 = firrtl.eq %sel, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %7 = firrtl.and %c1_ui1, %6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %8 = firrtl.mux(%7, %a_wo_3, %5) : (!firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   firrtl.connect %b_wo, %8 : !firrtl.uint<1>, !firrtl.uint<1>
// CHECK:   %c1_ui1_0 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui2_1 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %9 = firrtl.eq %sel, %c1_ui2_1 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %10 = firrtl.and %c1_ui1_0, %9 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %11 = firrtl.mux(%10, %a_valid_1, %a_valid_0) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c2_ui2_2 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %12 = firrtl.eq %sel, %c2_ui2_2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %13 = firrtl.and %c1_ui1_0, %12 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %14 = firrtl.mux(%13, %a_valid_2, %11) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c3_ui2_3 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %15 = firrtl.eq %sel, %c3_ui2_3 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %16 = firrtl.and %c1_ui1_0, %15 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %17 = firrtl.mux(%16, %a_valid_3, %14) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   firrtl.connect %b_valid, %17 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK: }

// COM: circuit Foo:
// COM:   module Foo:
// COM:     input a: UInt<2>[4]
// COM:     input z: UInt<2>[4]
// COM:     input sel: UInt<2>
// COM:     output b: UInt<2>
// COM: 
// COM:     b <= a[z[sel]]

firrtl.circuit "readIndirect1d"  {
  firrtl.module @readIndirect1d(in %a: !firrtl.vector<uint<2>, 4>, in %z: !firrtl.vector<uint<2>, 4>, in %sel: !firrtl.uint<2>, out %b: !firrtl.uint<2>) {
    %0 = firrtl.subaccess %z[%sel] : !firrtl.vector<uint<2>, 4>, !firrtl.uint<2>
    %1 = firrtl.subaccess %a[%0] : !firrtl.vector<uint<2>, 4>, !firrtl.uint<2>
    firrtl.connect %b, %1 : !firrtl.uint<2>, !firrtl.uint<2>
  }
}
// CHECK: firrtl.module @readIndirect1d(in %a_0: !firrtl.uint<2>, in %a_1: !firrtl.uint<2>, in %a_2: !firrtl.uint<2>, in %a_3: !firrtl.uint<2>, in %z_0: !firrtl.uint<2>, in %z_1: !firrtl.uint<2>, in %z_2: !firrtl.uint<2>, in %z_3: !firrtl.uint<2>, in %sel: !firrtl.uint<2>, out %b: !firrtl.uint<2>) {
// CHECK:   %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui2 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %0 = firrtl.eq %sel, %c1_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %1 = firrtl.and %c1_ui1, %0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %2 = firrtl.mux(%1, %z_1, %z_0) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %3 = firrtl.eq %sel, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %4 = firrtl.and %c1_ui1, %3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %5 = firrtl.mux(%4, %z_2, %2) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %6 = firrtl.eq %sel, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %7 = firrtl.and %c1_ui1, %6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %8 = firrtl.mux(%7, %z_3, %5) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c1_ui1_0 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui2_1 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %9 = firrtl.eq %8, %c1_ui2_1 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %10 = firrtl.and %c1_ui1_0, %9 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %11 = firrtl.mux(%10, %a_1, %a_0) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c2_ui2_2 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %12 = firrtl.eq %8, %c2_ui2_2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %13 = firrtl.and %c1_ui1_0, %12 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %14 = firrtl.mux(%13, %a_2, %11) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c3_ui2_3 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %15 = firrtl.eq %8, %c3_ui2_3 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %16 = firrtl.and %c1_ui1_0, %15 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %17 = firrtl.mux(%16, %a_3, %14) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   firrtl.connect %b, %17 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK: }

// COM: circuit Foo:
// COM:   module Foo:
// COM:     input a: UInt<2>[4][4]
// COM:     input sel: UInt<2>
// COM:     output b: UInt<2>
// COM: 
// COM:     b <= a[sel][sel]

firrtl.circuit "multidimRead"  {
  firrtl.module @multidimRead(in %a: !firrtl.vector<vector<uint<2>, 4>, 4>, in %sel: !firrtl.uint<2>, out %b: !firrtl.uint<2>) {
    %0 = firrtl.subaccess %a[%sel] : !firrtl.vector<vector<uint<2>, 4>, 4>, !firrtl.uint<2>
    %1 = firrtl.subaccess %0[%sel] : !firrtl.vector<uint<2>, 4>, !firrtl.uint<2>
    firrtl.connect %b, %1 : !firrtl.uint<2>, !firrtl.uint<2>
  }
}
// CHECK: firrtl.module @multidimRead(in %a_0_0: !firrtl.uint<2>, in %a_0_1: !firrtl.uint<2>, in %a_0_2: !firrtl.uint<2>, in %a_0_3: !firrtl.uint<2>, in %a_1_0: !firrtl.uint<2>, in %a_1_1: !firrtl.uint<2>, in %a_1_2: !firrtl.uint<2>, in %a_1_3: !firrtl.uint<2>, in %a_2_0: !firrtl.uint<2>, in %a_2_1: !firrtl.uint<2>, in %a_2_2: !firrtl.uint<2>, in %a_2_3: !firrtl.uint<2>, in %a_3_0: !firrtl.uint<2>, in %a_3_1: !firrtl.uint<2>, in %a_3_2: !firrtl.uint<2>, in %a_3_3: !firrtl.uint<2>, in %sel: !firrtl.uint<2>, out %b: !firrtl.uint<2>) {
// CHECK:   %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui2 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %0 = firrtl.eq %sel, %c1_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %1 = firrtl.and %c1_ui1, %0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c0_ui2 = firrtl.constant 0 : !firrtl.uint<2>
// CHECK:   %2 = firrtl.eq %sel, %c0_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %3 = firrtl.and %1, %2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %4 = firrtl.mux(%3, %a_0_1, %a_0_0) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c2_ui2 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %5 = firrtl.eq %sel, %c2_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %6 = firrtl.and %c1_ui1, %5 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c0_ui2_0 = firrtl.constant 0 : !firrtl.uint<2>
// CHECK:   %7 = firrtl.eq %sel, %c0_ui2_0 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %8 = firrtl.and %6, %7 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %9 = firrtl.mux(%8, %a_0_2, %4) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c3_ui2 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %10 = firrtl.eq %sel, %c3_ui2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %11 = firrtl.and %c1_ui1, %10 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c0_ui2_1 = firrtl.constant 0 : !firrtl.uint<2>
// CHECK:   %12 = firrtl.eq %sel, %c0_ui2_1 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %13 = firrtl.and %11, %12 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %14 = firrtl.mux(%13, %a_0_3, %9) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c0_ui2_2 = firrtl.constant 0 : !firrtl.uint<2>
// CHECK:   %15 = firrtl.eq %sel, %c0_ui2_2 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %16 = firrtl.and %c1_ui1, %15 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c1_ui2_3 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %17 = firrtl.eq %sel, %c1_ui2_3 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %18 = firrtl.and %16, %17 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %19 = firrtl.mux(%18, %a_1_0, %14) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c1_ui2_4 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %20 = firrtl.eq %sel, %c1_ui2_4 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %21 = firrtl.and %c1_ui1, %20 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c1_ui2_5 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %22 = firrtl.eq %sel, %c1_ui2_5 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %23 = firrtl.and %21, %22 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %24 = firrtl.mux(%23, %a_1_1, %19) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c2_ui2_6 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %25 = firrtl.eq %sel, %c2_ui2_6 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %26 = firrtl.and %c1_ui1, %25 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c1_ui2_7 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %27 = firrtl.eq %sel, %c1_ui2_7 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %28 = firrtl.and %26, %27 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %29 = firrtl.mux(%28, %a_1_2, %24) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c3_ui2_8 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %30 = firrtl.eq %sel, %c3_ui2_8 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %31 = firrtl.and %c1_ui1, %30 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c1_ui2_9 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %32 = firrtl.eq %sel, %c1_ui2_9 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %33 = firrtl.and %31, %32 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %34 = firrtl.mux(%33, %a_1_3, %29) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c0_ui2_10 = firrtl.constant 0 : !firrtl.uint<2>
// CHECK:   %35 = firrtl.eq %sel, %c0_ui2_10 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %36 = firrtl.and %c1_ui1, %35 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c2_ui2_11 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %37 = firrtl.eq %sel, %c2_ui2_11 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %38 = firrtl.and %36, %37 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %39 = firrtl.mux(%38, %a_2_0, %34) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c1_ui2_12 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %40 = firrtl.eq %sel, %c1_ui2_12 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %41 = firrtl.and %c1_ui1, %40 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c2_ui2_13 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %42 = firrtl.eq %sel, %c2_ui2_13 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %43 = firrtl.and %41, %42 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %44 = firrtl.mux(%43, %a_2_1, %39) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c2_ui2_14 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %45 = firrtl.eq %sel, %c2_ui2_14 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %46 = firrtl.and %c1_ui1, %45 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c2_ui2_15 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %47 = firrtl.eq %sel, %c2_ui2_15 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %48 = firrtl.and %46, %47 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %49 = firrtl.mux(%48, %a_2_2, %44) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c3_ui2_16 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %50 = firrtl.eq %sel, %c3_ui2_16 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %51 = firrtl.and %c1_ui1, %50 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c2_ui2_17 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %52 = firrtl.eq %sel, %c2_ui2_17 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %53 = firrtl.and %51, %52 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %54 = firrtl.mux(%53, %a_2_3, %49) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c0_ui2_18 = firrtl.constant 0 : !firrtl.uint<2>
// CHECK:   %55 = firrtl.eq %sel, %c0_ui2_18 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %56 = firrtl.and %c1_ui1, %55 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c3_ui2_19 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %57 = firrtl.eq %sel, %c3_ui2_19 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %58 = firrtl.and %56, %57 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %59 = firrtl.mux(%58, %a_3_0, %54) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c1_ui2_20 = firrtl.constant 1 : !firrtl.uint<2>
// CHECK:   %60 = firrtl.eq %sel, %c1_ui2_20 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %61 = firrtl.and %c1_ui1, %60 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c3_ui2_21 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %62 = firrtl.eq %sel, %c3_ui2_21 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %63 = firrtl.and %61, %62 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %64 = firrtl.mux(%63, %a_3_1, %59) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c2_ui2_22 = firrtl.constant 2 : !firrtl.uint<2>
// CHECK:   %65 = firrtl.eq %sel, %c2_ui2_22 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %66 = firrtl.and %c1_ui1, %65 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c3_ui2_23 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %67 = firrtl.eq %sel, %c3_ui2_23 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %68 = firrtl.and %66, %67 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %69 = firrtl.mux(%68, %a_3_2, %64) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   %c3_ui2_24 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %70 = firrtl.eq %sel, %c3_ui2_24 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %71 = firrtl.and %c1_ui1, %70 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c3_ui2_25 = firrtl.constant 3 : !firrtl.uint<2>
// CHECK:   %72 = firrtl.eq %sel, %c3_ui2_25 : (!firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<1>
// CHECK:   %73 = firrtl.and %71, %72 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %74 = firrtl.mux(%73, %a_3_3, %69) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   firrtl.connect %b, %74 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK: }


// COM: circuit Foo:
// COM:   module Foo:
// COM:     input sel: UInt<1>
// COM:     input b: UInt<2>
// COM:     output a: UInt<2>[2][2]
// COM: 
// COM:     a[sel][sel] <= b

firrtl.circuit "multidimWrite"  {
  firrtl.module @multidimWrite(in %sel: !firrtl.uint<1>, in %b: !firrtl.uint<2>, out %a: !firrtl.vector<vector<uint<2>, 2>, 2>) {
    %0 = firrtl.subaccess %a[%sel] : !firrtl.vector<vector<uint<2>, 2>, 2>, !firrtl.uint<1>
    %1 = firrtl.subaccess %0[%sel] : !firrtl.vector<uint<2>, 2>, !firrtl.uint<1>
    firrtl.connect %1, %b : !firrtl.uint<2>, !firrtl.uint<2>
  }
}
// CHECK: firrtl.module @multidimWrite(in %sel: !firrtl.uint<1>, in %b: !firrtl.uint<2>, out %a_0_0: !firrtl.uint<2>, out %a_0_1: !firrtl.uint<2>, out %a_1_0: !firrtl.uint<2>, out %a_1_1: !firrtl.uint<2>) {
// CHECK:   %0 = firrtl.wire  : !firrtl.uint<2>
// CHECK:   %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %c1_ui1_0 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %1 = firrtl.eq %sel, %c1_ui1_0 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %2 = firrtl.and %c1_ui1, %1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
// CHECK:   %3 = firrtl.eq %sel, %c0_ui1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %4 = firrtl.and %2, %3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %5 = firrtl.mux(%4, %0, %a_0_1) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   firrtl.connect %a_0_1, %5 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   %c0_ui1_1 = firrtl.constant 0 : !firrtl.uint<1>
// CHECK:   %6 = firrtl.eq %sel, %c0_ui1_1 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %7 = firrtl.and %c1_ui1, %6 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c1_ui1_2 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %8 = firrtl.eq %sel, %c1_ui1_2 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %9 = firrtl.and %7, %8 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %10 = firrtl.mux(%9, %0, %a_1_0) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   firrtl.connect %a_1_0, %10 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   %c1_ui1_3 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %11 = firrtl.eq %sel, %c1_ui1_3 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %12 = firrtl.and %c1_ui1, %11 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %c1_ui1_4 = firrtl.constant 1 : !firrtl.uint<1>
// CHECK:   %13 = firrtl.eq %sel, %c1_ui1_4 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %14 = firrtl.and %12, %13 : (!firrtl.uint<1>, !firrtl.uint<1>) -> !firrtl.uint<1>
// CHECK:   %15 = firrtl.mux(%14, %0, %a_1_1) : (!firrtl.uint<1>, !firrtl.uint<2>, !firrtl.uint<2>) -> !firrtl.uint<2>
// CHECK:   firrtl.connect %a_1_1, %15 : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK:   firrtl.connect %0, %b : !firrtl.uint<2>, !firrtl.uint<2>
// CHECK: }
}
