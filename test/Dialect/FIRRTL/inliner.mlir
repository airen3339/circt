// RUN: circt-opt --pass-pipeline='firrtl.circuit(firrtl-inliner)' %s | FileCheck %s

// Test that unused modules are deleted.
firrtl.circuit "delete_dead_modules" {
firrtl.module @delete_dead_modules () {
  firrtl.instance @used {name = "used", portNames = []}
  firrtl.instance @used_ext {name = "used", portNames = []}
}
firrtl.module @unused () { }
firrtl.module @used () { }
firrtl.extmodule @unused_ext ()
firrtl.extmodule @used_ext ()
}
// CHECK-LABEL: firrtl.circuit "delete_dead_modules" {
// CHECK-NEXT:   firrtl.module @delete_dead_modules() {
// CHECK-NEXT:     firrtl.instance @used  {name = "used", portNames = []}
// CHECK-NEXT:     firrtl.instance @used_ext  {name = "used", portNames = []}
// CHECK-NEXT:   }
// CHECK-NEXT:   firrtl.module @used() {
// CHECK-NEXT:   }
// CHECK-NEXT:   firrtl.extmodule @used_ext()
// CHECK-NEXT: }


// Test basic inlining
firrtl.circuit "inlining" {
firrtl.module @inlining() {
  firrtl.instance @test1 {name = "test1", portNames=[]}
}
firrtl.module @test1()
  attributes {annotations = [{class = "firrtl.passes.InlineAnnotation"}]} {
  %test_wire = firrtl.wire : !firrtl.uint<2>
  firrtl.instance @test2 {name = "test2", portNames=[]}
}
firrtl.module @test2()
  attributes {annotations = [{class = "firrtl.passes.InlineAnnotation"}]} {
  %test_wire = firrtl.wire : !firrtl.uint<2>
}
}
// CHECK-LABEL: firrtl.circuit "inlining" {
// CHECK-NEXT:   firrtl.module @inlining() {
// CHECK-NEXT:     %test1_test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:     %test1_test2_test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:   }
// CHECK-NEXT: }


// Test basic flattening
firrtl.circuit "flattening" {
firrtl.module @flattening()
  attributes {annotations = [{class = "firrtl.transforms.FlattenAnnotation"}]} {
  firrtl.instance @test1 {name = "test1", portNames=[]}
}
firrtl.module @test1() {
  %test_wire = firrtl.wire : !firrtl.uint<2>
  firrtl.instance @test2 {name = "test2", portNames=[]}
}
firrtl.module @test2() {
  %test_wire = firrtl.wire : !firrtl.uint<2>
}
}
// CHECK-LABEL: firrtl.circuit "flattening" {
// CHECK-NEXT:   firrtl.module @flattening() attributes {annotations = [{class = "firrtl.transforms.FlattenAnnotation"}]} {
// CHECK-NEXT:     %test1_test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:     %test1_test2_test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:   }
// CHECK-NEXT: }


// Test that inlining and flattening compose well.
firrtl.circuit "compose" {
firrtl.module @compose() {
  firrtl.instance @test1 {name = "test1", portNames=[]}
  firrtl.instance @test2 {name = "test2", portNames=[]}
  firrtl.instance @test3 {name = "test3", portNames=[]}
}
firrtl.module @test1() attributes {annotations = 
        [{class = "firrtl.transforms.FlattenAnnotation"},
         {class = "firrtl.passes.InlineAnnotation"}]} {
  %test_wire = firrtl.wire : !firrtl.uint<2>
  firrtl.instance @test2 {name = "test2", portNames=[]}
  firrtl.instance @test3 {name = "test3", portNames=[]}
}
firrtl.module @test2() attributes {annotations = 
        [{class = "firrtl.passes.InlineAnnotation"}]} {
  %test_wire = firrtl.wire : !firrtl.uint<2>
  firrtl.instance @test3 {name = "test3", portNames=[]}
}
firrtl.module @test3() {
  %test_wire = firrtl.wire : !firrtl.uint<2>
}
}
// CHECK-LABEL: firrtl.circuit "compose" {
// CHECK-NEXT:   firrtl.module @compose() {
// CHECK-NEXT:     %test1_test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:     %test1_test2_test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:     %test1_test2_test3_test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:     %test1_test3_test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:     %test2_test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:     firrtl.instance @test3  {name = "test2_test3", portNames = []}
// CHECK-NEXT:     firrtl.instance @test3  {name = "test3", portNames = []}
// CHECK-NEXT:   }
// CHECK-NEXT:   firrtl.module @test3() {
// CHECK-NEXT:     %test_wire = firrtl.wire  : !firrtl.uint<2>
// CHECK-NEXT:   }
// CHECK-NEXT: }


// This is testing that connects are properly replaced when inlining. This is
// also testing that the deep clone and remapping values is working correctly.
firrtl.circuit "TestConnections" {
firrtl.module @InlineMe0(%in0: !firrtl.uint<4>, %in1: !firrtl.uint<4>,
                        %out0: !firrtl.flip<uint<4>>, %out1: !firrtl.flip<uint<4>>) 
        attributes {annotations = [{class = "firrtl.passes.InlineAnnotation"}]} {
  %0 = firrtl.and %in0, %in1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %out0, %0 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
  %1 = firrtl.and %in0, %in1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
  firrtl.connect %out1, %1 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
}

firrtl.module @InlineMe1(%in0: !firrtl.uint<4>, %in1: !firrtl.uint<4>,
                   %out0: !firrtl.flip<uint<4>>,
                   %out1: !firrtl.flip<uint<4>>)
        attributes {annotations = [{class = "firrtl.passes.InlineAnnotation"}]} {
  %a_in0, %a_in1, %a_out0, %a_out1 = firrtl.instance @InlineMe0 {name = "a", portNames = ["in0", "in1", "out0", "out1"]} : !firrtl.flip<uint<4>>, !firrtl.flip<uint<4>>, !firrtl.uint<4>, !firrtl.uint<4>
  firrtl.connect %a_in0, %in0 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
  firrtl.connect %a_in1, %in1 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
  firrtl.connect %out0, %a_out0 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
  firrtl.connect %out1, %a_out1 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
}
firrtl.module @TestConnections(%in0: !firrtl.uint<4>, %in1: !firrtl.uint<4>,
                   %out0: !firrtl.flip<uint<4>>,
                   %out1: !firrtl.flip<uint<4>>) {
  %b_in0, %b_in1, %b_out0, %b_out1 = firrtl.instance @InlineMe1 {name = "b", portNames = ["in0", "in1", "out0", "out1"]} : !firrtl.flip<uint<4>>, !firrtl.flip<uint<4>>, !firrtl.uint<4>, !firrtl.uint<4>
  firrtl.connect %b_in0, %in0 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
  firrtl.connect %b_in1, %in1 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
  firrtl.connect %out0, %b_out0 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
  firrtl.connect %out1, %b_out1 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
}
}
// CHECK-LABEL: firrtl.module @TestConnections(%in0: !firrtl.uint<4>, %in1: !firrtl.uint<4>, %out0: !firrtl.flip<uint<4>>, %out1: !firrtl.flip<uint<4>>) {
// CHECK-NEXT:   %b_in0 = firrtl.wire  : !firrtl.uint<4>
// CHECK-NEXT:   %b_in1 = firrtl.wire  : !firrtl.uint<4>
// CHECK-NEXT:   %b_out0 = firrtl.wire  : !firrtl.flip<uint<4>>
// CHECK-NEXT:   %b_out1 = firrtl.wire  : !firrtl.flip<uint<4>>
// CHECK-NEXT:   %b_a_in0 = firrtl.wire  : !firrtl.uint<4>
// CHECK-NEXT:   %b_a_in1 = firrtl.wire  : !firrtl.uint<4>
// CHECK-NEXT:   %b_a_out0 = firrtl.wire  : !firrtl.flip<uint<4>>
// CHECK-NEXT:   %b_a_out1 = firrtl.wire  : !firrtl.flip<uint<4>>
// CHECK-NEXT:   %0 = firrtl.and %b_a_in0, %b_a_in1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
// CHECK-NEXT:   firrtl.connect %b_a_out0, %0 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
// CHECK-NEXT:   %1 = firrtl.and %b_a_in0, %b_a_in1 : (!firrtl.uint<4>, !firrtl.uint<4>) -> !firrtl.uint<4>
// CHECK-NEXT:   firrtl.connect %b_a_out1, %1 : !firrtl.flip<uint<4>>, !firrtl.uint<4>
// CHECK-NEXT:   firrtl.connect %b_a_in0, %b_in0 : !firrtl.uint<4>, !firrtl.uint<4>
// CHECK-NEXT:   firrtl.connect %b_a_in1, %b_in1 : !firrtl.uint<4>, !firrtl.uint<4>
// CHECK-NEXT:   firrtl.connect %b_out0, %b_a_out0 : !firrtl.flip<uint<4>>, !firrtl.flip<uint<4>>
// CHECK-NEXT:   firrtl.connect %b_out1, %b_a_out1 : !firrtl.flip<uint<4>>, !firrtl.flip<uint<4>>
// CHECK-NEXT:   firrtl.connect %b_in0, %in0 : !firrtl.uint<4>, !firrtl.uint<4>
// CHECK-NEXT:   firrtl.connect %b_in1, %in1 : !firrtl.uint<4>, !firrtl.uint<4>
// CHECK-NEXT:   firrtl.connect %out0, %b_out0 : !firrtl.flip<uint<4>>, !firrtl.flip<uint<4>>
// CHECK-NEXT:   firrtl.connect %out1, %b_out1 : !firrtl.flip<uint<4>>, !firrtl.flip<uint<4>>
// CHECK-NEXT: }

// Test that all operations with names are renamed.
firrtl.circuit "renaming" {
firrtl.module @renaming() {
  %0, %1, %2 = firrtl.instance @declarations {name = "myinst", portNames=["clock", "u8", "reset"]} : !firrtl.flip<clock>, !firrtl.flip<uint<8>>, !firrtl.flip<asyncreset>
}
firrtl.module @declarations(%clock : !firrtl.clock, %u8 : !firrtl.uint<8>, %reset : !firrtl.asyncreset) attributes {annotations = [{class = "firrtl.passes.InlineAnnotation"}]} {
  // CHECK: %myinst_cmem = firrtl.cmem  {name = "myinst_cmem"} : !firrtl.uint<8>
  %cmem = firrtl.cmem {name = "cmem"} : !firrtl.uint<8>
  // CHECK: %myinst_mem_read = firrtl.mem Undefined  {depth = 1 : i64, name = "myinst_mem", portNames = ["read"], readLatency = 0 : i32, writeLatency = 1 : i32} : !firrtl.bundle<addr: flip<uint<1>>, en: flip<uint<1>>, clk: flip<clock>, data: sint<42>>
  %mem = firrtl.mem Undefined {depth = 1 : i64, name = "mem", portNames = ["read"], readLatency = 0 : i32, writeLatency = 1 : i32} : !firrtl.bundle<addr: flip<uint<1>>, en: flip<uint<1>>, clk: flip<clock>, data: sint<42>>
  // CHECK: %myinst_memoryport = firrtl.memoryport Infer %myinst_cmem, %myinst_u8, %myinst_clock {name = "myinst_memoryport"} : (!firrtl.uint<8>, !firrtl.uint<8>, !firrtl.clock) -> !firrtl.bundle<id: uint<4>, resp: uint<2>>
  %memport = firrtl.memoryport Infer %cmem, %u8, %clock {name = "memoryport"} : (!firrtl.uint<8>, !firrtl.uint<8>, !firrtl.clock) -> !firrtl.bundle<id: uint<4>, resp: uint<2>>
  // CHECK: %myinst_node = firrtl.node %myinst_u8  : !firrtl.uint<8>
  %node = firrtl.node %u8 {name = "node"} : !firrtl.uint<8>
  // CHECK: %myinst_reg = firrtl.reg %myinst_clock  {name = "myinst_reg"} : (!firrtl.clock) -> !firrtl.uint<8>
  %reg = firrtl.reg %clock {name = "reg"} : (!firrtl.clock) -> !firrtl.uint<8>
  // CHECK: %myinst_regreset = firrtl.regreset %myinst_clock, %myinst_reset, %myinst_u8  {name = "myinst_regreset"} : (!firrtl.clock, !firrtl.asyncreset, !firrtl.uint<8>) -> !firrtl.uint<8>
  %regreset = firrtl.regreset %clock, %reset, %u8 {name = "regreset"} : (!firrtl.clock, !firrtl.asyncreset, !firrtl.uint<8>) -> !firrtl.uint<8>
  // CHECK: %myinst_smem = firrtl.smem Undefined  {name = "myinst_smem"} : !firrtl.uint<1>
  %smem = firrtl.smem Undefined {name = "smem"} : !firrtl.uint<1>
  // CHECK: %myinst_wire = firrtl.wire  : !firrtl.uint<1>
  %wire = firrtl.wire : !firrtl.uint<1>
  firrtl.when %wire {
    // CHECK:  %myinst_inwhen = firrtl.wire  : !firrtl.uint<1>
    %inwhen = firrtl.wire : !firrtl.uint<1>
  }
}

}