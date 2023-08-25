// RUN: circt-opt --lower-seq-to-sv %s | FileCheck %s

hw.generator.schema @Some_schema, "Some_schema", ["dummy"]

// CHECK-LABEL: hw.module.generated @generated, @Some_schema(%clock: i1, %other: i1) -> (out: i32)
hw.module.generated @generated, @Some_schema(%clock: !seq.clock, %other: i1) -> (out: i32) attributes { dummy = 1 : i32 }

// CHECK-LABEL: hw.module.extern @extern(%clock: i1, %other: i1) -> (out: i32)
hw.module.extern @extern(%clock: !seq.clock, %other: i1) -> (out: i32)

// CHECK-LABEL: hw.module @top(%clock: i1, %other: i1, %wire: i1) -> (out: i1)
hw.module @top(%clock: !seq.clock, %other: i1, %wire: i1) -> (out: !seq.clock) {

  // CHECK: %tap_generated = hw.wire %clock  : i1
  %tap_generated = hw.wire %clock : !seq.clock

  // CHECK: %generated.out = hw.instance "generated" @generated(clock: %tap_generated: i1, other: %other: i1) -> (out: i32)
  %generated.out = hw.instance "generated" @generated(clock: %tap_generated: !seq.clock, other: %other: i1) -> (out: i32)

  // CHECK: %extern.out = hw.instance "extern" @generated(clock: %clock: i1, other: %other: i1) -> (out: i32)
  %extern.out = hw.instance "extern" @generated(clock: %clock: !seq.clock, other: %other: i1) -> (out: i32)

  // CHECK: %inner.out = hw.instance "inner" @inner(clock: %clock: i1, other: %other: i1) -> (out: i32)
  %out_inner = hw.instance "inner" @inner(clock: %clock: !seq.clock, other: %other: i1) -> (out: i32)

  // CHECK: [[NEGATED:%.+]] = comb.xor %clock, %true : i1
  %clock_wire = seq.from_clock %clock
  %one = hw.constant 1 : i1
  %tmp = comb.xor %clock_wire, %one : i1
  %negated = seq.to_clock %tmp

  // CHECK: hw.output [[NEGATED]] : i1
  hw.output %negated : !seq.clock
}

// CHECK-LABEL: hw.module private @inner(%clock: i1, %other: i1) -> (out: i32)
hw.module private @inner(%clock: !seq.clock, %other: i1) -> (out: i32) {
  %cst = hw.constant 0 : i32
  hw.output %cst : i32
}
