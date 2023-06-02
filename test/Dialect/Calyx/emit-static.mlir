// RUN: circt-translate --export-calyx --split-input-file --verify-diagnostics %s | FileCheck %s --strict-whitespace

module attributes {calyx.entrypoint = "main"} {
  // CHECK-LABEL: component main(@go go: 1, @clk clk: 1, @reset reset: 1) -> (@done done: 1) {
  calyx.component @main(%go: i1 {go}, %clk: i1 {clk}, %reset: i1 {reset}) -> (%done: i1 {done}) {
    %p.in, %p.write_en, %p.clk, %p.reset, %p.out, %p.done = calyx.register @p : i3, i1, i1, i1, i3, i1
    %incr.left, %incr.right, %incr.out = calyx.std_add @incr : i3, i3, i3
    %l.left, %l.right, %l.out = calyx.std_lt @l : i3, i3, i1
    %c1_3 = hw.constant 1 : i3
    %c1_1 = hw.constant 1 : i1
    %c6_3 = hw.constant 6 : i3

    calyx.wires {
      // CHECK: static<1> group A {
      calyx.static_group latency<1> @A {
        calyx.assign %incr.left = %p.out : i3
        calyx.assign %incr.right = %c1_3 : i3
        calyx.assign %p.in = %incr.out : i3
        // CHECK: p.write_en = %0 ? 1'd1;
        %0 = calyx.cycle 0
        calyx.assign %p.write_en = %0 ? %c1_1 : i1
      }
      calyx.assign %l.left = %p.out : i3
      calyx.assign %l.right = %c6_3 : i3
    }
    calyx.control {
      calyx.while %l.out {
        calyx.enable @A
      }
    }
  }
}

// -----

module attributes {calyx.entrypoint = "main"} {
  // CHECK-LABEL: component main(@go go: 1, @clk clk: 1, @reset reset: 1) -> (@done done: 1) {
  calyx.component @main(%go: i1 {go}, %clk: i1 {clk}, %reset: i1 {reset}) -> (%done: i1 {done}) {
    %p.in, %p.write_en, %p.clk, %p.reset, %p.out, %p.done = calyx.register @p : i3, i1, i1, i1, i3, i1
    %incr.left, %incr.right, %incr.out = calyx.std_add @incr : i3, i3, i3
    %l.left, %l.right, %l.out = calyx.std_lt @l : i3, i3, i1
    %c1_3 = hw.constant 1 : i3
    %c1_1 = hw.constant 1 : i1
    %c6_3 = hw.constant 6 : i3

    calyx.wires {
      // CHECK: static<1> group A {
      calyx.static_group latency<1> @A {
        calyx.assign %incr.left = %p.out : i3
        calyx.assign %incr.right = %c1_3 : i3
        calyx.assign %p.in = %incr.out : i3
        // CHECK: p.write_en = %0 ? 1'd1;
        %0 = calyx.cycle 0
        calyx.assign %p.write_en = %0 ? %c1_1 : i1
      }
      calyx.assign %l.left = %p.out : i3
      calyx.assign %l.right = %c6_3 : i3
    }
    calyx.control {
      // CHECK: static repeat 10 {
      calyx.static_repeat 10 {
        calyx.enable @A
      }
    }
  }
}


// -----
module attributes {calyx.entrypoint = "main"} {
  // CHECK-LABEL: component main(@go go: 1, @clk clk: 1, @reset reset: 1) -> (@done done: 1) {
  calyx.component @main(%go: i1 {go}, %clk: i1 {clk}, %reset: i1 {reset}) -> (%done: i1 {done}) {
    %a.in, %a.write_en, %a.clk, %a.reset, %a.out, %a.done = calyx.register @a : i2, i1, i1, i1, i2, i1
    %b.in, %b.write_en, %b.clk, %b.reset, %b.out, %b.done = calyx.register @b : i2, i1, i1, i1, i2, i1

    %c0_2 = hw.constant 0 : i2
    %c2_2 = hw.constant 0 : i2
    %c1_1 = hw.constant 1 : i1

    calyx.wires {
      // CHECK: static<1> group A {
      calyx.static_group latency<1> @A {
        calyx.assign %a.in =%c0_2  : i2
        // CHECK: a.write_en = %0 ? 1'd1;
        %0 = calyx.cycle 0
        calyx.assign %a.write_en = %0 ? %c1_1 : i1
      }
      // CHECK: static<1> group B {
      calyx.static_group latency<1> @B {
        calyx.assign %b.in =%c2_2  : i2
        // CHECK: b.write_en = %0 ? 1'd1;
        %0 = calyx.cycle 0
        calyx.assign %b.write_en = %0 ? %c1_1 : i1
      }
    }
    calyx.control {
      // CHECK: static seq {
      calyx.static_seq { 
        calyx.enable @A
        calyx.enable @B
      }
    }
  }
}
