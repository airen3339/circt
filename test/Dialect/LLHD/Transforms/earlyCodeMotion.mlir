// NOTE: Assertions have been autogenerated by utils/generate-test-checks.py
// RUN: circt-opt %s -llhd-early-code-motion | FileCheck %s

// CHECK-LABEL:   @check_dont_move_sideeffect
// CHECK-SAME:    (inout %[[VAL_0:.*]] : i32)
// CHECK:           llhd.process
// CHECK:           %[[VAL_1:.*]] = hw.constant 4 : i32
// CHECK:           %[[VAL_2:.*]] = llhd.constant_time <1ns, 0d, 0e>
// CHECK:           cf.br ^[[BB1:.+]]
// CHECK:         ^[[BB1]]:
// CHECK:           %[[VAL_3:.*]] = llhd.var %[[VAL_1]] : i32
// CHECK:           llhd.drv %[[VAL_0]], %[[VAL_1]] after %[[VAL_2]] : !hw.inout<i32>
// CHECK:           cf.br ^[[BB2:.+]]
// CHECK:         ^[[BB2]]:
// CHECK:           %[[VAL_4:.*]] = llhd.load %[[VAL_3]] : !llhd.ptr<i32>
// CHECK:           llhd.store %[[VAL_3]], %[[VAL_1]] : !llhd.ptr<i32>
// CHECK:           llhd.halt
// CHECK:         }
hw.module @check_dont_move_sideeffect(inout %sig : i32) {
  llhd.process {
    // TR: -1
    %c = hw.constant 4 : i32
    %time = llhd.constant_time <1ns, 0d, 0e>
    cf.br ^bb1
  ^bb1:
    // TR: -1
    %ptr = llhd.var %c : i32
    llhd.drv %sig, %c after %time : !hw.inout<i32>
    cf.br ^bb2
  ^bb2:
    // TR: -1
    %ld = llhd.load %ptr : !llhd.ptr<i32>
    llhd.store %ptr, %c : !llhd.ptr<i32>
    llhd.halt
  }
}

// Checks that prb is moved to predecessor block if it is in the same TR, but
// not if one predecessor has a wait terminator, but side-effect-free operations
// are moved freely
// CHECK-LABEL:   @check_move_prb1
// CHECK-SAME:      (inout %[[VAL_0:.*]] : i32)
// CHECK:           llhd.process
// CHECK:           %[[VAL_1:.*]] = hw.constant 4 : i32
// CHECK:           %[[VAL_2:.*]] = comb.add %[[VAL_1]], %[[VAL_1]] : i32
// CHECK:           cf.br ^[[BB1:.+]]
// CHECK:         ^[[BB1]]:
// CHECK:           %[[VAL_3:.*]] = llhd.prb %[[VAL_0]] : !hw.inout<i32>
// CHECK:           %[[VAL_4:.*]] = llhd.prb %[[VAL_0]] : !hw.inout<i32>
// CHECK:           cf.br ^[[BB2:.+]]
// CHECK:         ^[[BB2]]:
// CHECK:           llhd.wait ^[[BB1]]
// CHECK:         }
hw.module @check_move_prb1(inout %sig : i32) {
  llhd.process {
    // TR: -1
    cf.br ^bb1
  ^bb1:
    // TR: 0
    %c = hw.constant 4 : i32
    %prb1 = llhd.prb %sig : !hw.inout<i32>
    cf.br ^bb2
  ^bb2:
    // TR: 0
    %double = comb.add %c, %c : i32
    %prb2 = llhd.prb %sig : !hw.inout<i32>
    llhd.wait ^bb1
  }
}

// Checks that prb is not moved to predecessor if not all predecessors are in
// the same TR, but side-effect-free operations are moved freely
// CHECK-LABEL:   @check_move_prb2
// CHECK-SAME:      (inout %[[VAL_0:.*]] : i32)
// CHECK:           llhd.process
// CHECK:           %[[VAL_1:.*]] = hw.constant 4 : i32
// CHECK:           %[[VAL_2:.*]] = comb.add %[[VAL_1]], %[[VAL_1]] : i32
// CHECK:           cf.br ^[[BB1:.+]]
// CHECK:         ^[[BB1]]:
// CHECK:           %[[VAL_3:.*]] = llhd.prb %[[VAL_0]] : !hw.inout<i32>
// CHECK:           llhd.wait ^[[BB2:.+]]
// CHECK:         ^[[BB2]]:
// CHECK:           %[[VAL_4:.*]] = llhd.prb %[[VAL_0]] : !hw.inout<i32>
// CHECK:           cf.br ^[[BB1]]
// CHECK:         }
hw.module @check_move_prb2(inout %sig : i32) {
  llhd.process {
    // TR: -1
    cf.br ^bb1
  ^bb1:
    // TR: 1
    %c = hw.constant 4 : i32
    %prb1 = llhd.prb %sig : !hw.inout<i32>
    llhd.wait ^bb2
  ^bb2:
    // TR: 0
    %double = comb.add %c, %c : i32
    %prb2 = llhd.prb %sig : !hw.inout<i32>
    cf.br ^bb1
  }
}

// CHECK-LABEL:   @check_blockarg
// CHECK-SAME:      (inout %[[VAL_0:.*]] : i32)
// CHECK:           llhd.process
// CHECK:           %[[VAL_1:.*]] = hw.constant 4 : i32
// CHECK:           cf.br ^[[BB1:.+]](%[[VAL_1]] : i32)
// CHECK:         ^[[BB1]](%[[VAL_2:.*]]: i32):
// CHECK:           %[[VAL_3:.*]] = comb.add %[[VAL_2]], %[[VAL_2]] : i32
// CHECK:           llhd.halt
// CHECK:         }
hw.module @check_blockarg(inout %sig : i32) {
  llhd.process {
    // TR: -1
    %c = hw.constant 4 : i32
    cf.br ^bb1(%c : i32)
  ^bb1(%a : i32):
    // TR: -1
    %double = comb.add %a, %a : i32
    llhd.halt
  }
}

// CHECK-LABEL:   @loop
// CHECK-SAME:      (inout %[[VAL_0:.*]] : i2)
// CHECK:           llhd.process
// CHECK:           %[[VAL_1:.*]] = hw.constant 0 : i32
// CHECK:           %[[VAL_2:.*]] = hw.constant 2 : i32
// CHECK:           %[[VAL_3:.*]] = hw.constant 0 : i2
// CHECK:           %[[VAL_4:.*]] = hw.constant 1 : i32
// CHECK:           cf.br ^[[BB1:.+]]
// CHECK:         ^[[BB1]]:
// CHECK:           %[[VAL_5:.*]] = llhd.var %[[VAL_1]] : i32
// CHECK:           cf.br ^[[BB2:.+]]
// CHECK:         ^[[BB2]]:
// CHECK:           %[[VAL_6:.*]] = llhd.load %[[VAL_5]] : !llhd.ptr<i32>
// CHECK:           %[[VAL_7:.*]] = comb.icmp ult %[[VAL_6]], %[[VAL_2]] : i32
// CHECK:           %[[VAL_8:.*]] = llhd.prb %[[VAL_0]] : !hw.inout<i2>
// CHECK:           cf.cond_br %[[VAL_7]], ^[[BB4:.+]], ^[[BB3:.+]]
// CHECK:         ^[[BB3]]:
// CHECK:           llhd.wait (%[[VAL_0]] : !hw.inout<i2>), ^[[BB1]]
// CHECK:         ^[[BB4]]:
// CHECK:           %[[VAL_9:.*]] = llhd.load %[[VAL_5]] : !llhd.ptr<i32>
// CHECK:           %[[VAL_10:.*]] = comb.add %[[VAL_9]], %[[VAL_4]] : i32
// CHECK:           llhd.store %[[VAL_5]], %[[VAL_10]] : !llhd.ptr<i32>
// CHECK:           cf.br ^[[BB2]]
// CHECK:         }
hw.module @loop(inout %in_i : i2) {
  llhd.process {
    // TR: -1
    cf.br ^body
  ^body:
    // TR: 0
    %0 = hw.constant 0 : i32
    %i = llhd.var %0 : i32
    cf.br ^loop_body
  ^loop_body:
    // TR: 1
    %i_ld = llhd.load %i : !llhd.ptr<i32>
    %1 = hw.constant 2 : i32
    %2 = comb.icmp ult %i_ld, %1 : i32
    cf.cond_br %2, ^loop_continue, ^check
  ^check:
    // TR: 1
    llhd.wait (%in_i : !hw.inout<i2>), ^body
  ^loop_continue:
    // TR: 1
    %3 = hw.constant 0 : i2
    %5 = hw.constant 1 : i32
    %prb = llhd.prb %in_i : !hw.inout<i2>
    %i_ld4 = llhd.load %i : !llhd.ptr<i32>
    %14 = comb.add %i_ld4, %5 : i32
    llhd.store %i, %14 : !llhd.ptr<i32>
    cf.br ^loop_body
  }
}

// CHECK-LABEL:   @complicated
// CHECK-SAME:      (inout %[[VAL_0:.*]] : i1, inout %[[VAL_1:.*]] : i1, inout %[[VAL_2:.*]] : i1, inout %[[VAL_3:.*]] : i1, inout %[[VAL_4:.*]] : i1)
// CHECK:           llhd.process
// CHECK:           %[[ALLSET:.*]] = hw.constant true
// CHECK:           %[[VAL_5:.*]] = hw.constant false
// CHECK:           %[[VAL_6:.*]] = llhd.constant_time <0s, 1d, 0e>
// CHECK:           cf.br ^[[BB1:.+]]
// CHECK:         ^[[BB1]]:
// CHECK:           %[[VAL_7:.*]] = llhd.prb %[[VAL_3]] : !hw.inout<i1>
// CHECK:           %[[VAL_8:.*]] = llhd.var %[[VAL_7]] : i1
// CHECK:           cf.br ^[[BB2:.+]]
// CHECK:         ^[[BB2]]:
// CHECK:           %[[VAL_9:.*]] = llhd.prb %[[VAL_1]] : !hw.inout<i1>
// CHECK:           %[[VAL_10:.*]] = llhd.prb %[[VAL_0]] : !hw.inout<i1>
// CHECK:           %[[VAL_11:.*]] = comb.icmp eq %[[VAL_9]], %[[VAL_5]] : i1
// CHECK:           %[[VAL_12:.*]] = comb.icmp ne %[[VAL_10]], %[[VAL_5]] : i1
// CHECK:           llhd.wait (%[[VAL_1]], %[[VAL_0]] : !hw.inout<i1>, !hw.inout<i1>), ^[[BB3:.+]]
// CHECK:         ^[[BB3]]:
// CHECK:           %[[VAL_13:.*]] = llhd.prb %[[VAL_3]] : !hw.inout<i1>
// CHECK:           llhd.store %[[VAL_8]], %[[VAL_13]] : !llhd.ptr<i1>
// CHECK:           llhd.store %[[VAL_8]], %[[VAL_13]] : !llhd.ptr<i1>
// CHECK:           %[[VAL_14:.*]] = llhd.prb %[[VAL_1]] : !hw.inout<i1>
// CHECK:           %[[VAL_15:.*]] = comb.icmp ne %[[VAL_14]], %[[VAL_5]] : i1
// CHECK:           %[[VAL_16:.*]] = comb.and %[[VAL_11]], %[[VAL_15]] : i1
// CHECK:           %[[VAL_17:.*]] = llhd.prb %[[VAL_0]] : !hw.inout<i1>
// CHECK:           %[[VAL_18:.*]] = comb.icmp eq %[[VAL_17]], %[[VAL_5]] : i1
// CHECK:           %[[VAL_19:.*]] = comb.and %[[VAL_18]], %[[VAL_12]] : i1
// CHECK:           %[[VAL_20:.*]] = comb.or %[[VAL_16]], %[[VAL_19]] : i1
// CHECK:           %[[VAL_21:.*]] = comb.icmp ne %[[VAL_17]], %[[VAL_5]] : i1
// CHECK:           %[[VAL_22:.*]] = comb.xor %[[VAL_21]], %[[ALLSET]] : i1
// CHECK:           %[[VAL_23:.*]] = comb.icmp ne %[[VAL_22]], %[[VAL_5]] : i1
// CHECK:           %[[VAL_24:.*]] = llhd.prb %[[VAL_2]] : !hw.inout<i1>
// CHECK:           cf.cond_br %[[VAL_20]], ^[[BB4:.+]], ^[[BB2]]
// CHECK:         ^[[BB4]]:
// CHECK:           cf.cond_br %[[VAL_23]], ^[[BB6:.+]], ^[[BB5:.+]]
// CHECK:         ^[[BB5]]:
// CHECK:           llhd.drv %[[VAL_3]], %[[VAL_24]] after %[[VAL_6]] : !hw.inout<i1>
// CHECK:           %[[VAL_25:.*]] = llhd.load %[[VAL_8]] : !llhd.ptr<i1>
// CHECK:           llhd.drv %[[VAL_4]], %[[VAL_25]] after %[[VAL_6]] : !hw.inout<i1>
// CHECK:           cf.br ^[[BB1]]
// CHECK:         ^[[BB6]]:
// CHECK:           llhd.drv %[[VAL_3]], %[[VAL_5]] after %[[VAL_6]] : !hw.inout<i1>
// CHECK:           llhd.drv %[[VAL_4]], %[[VAL_5]] after %[[VAL_6]] : !hw.inout<i1>
// CHECK:           cf.br ^[[BB1]]
// CHECK:         }
hw.module @complicated(inout %rst_ni: i1, inout %clk_i: i1, inout %async_ack_i: i1, inout %ack_src_q: i1, inout %ack_q: i1) {
  llhd.process {
    %allset = hw.constant 1 : i1
    // TR: -1
    cf.br ^0
  ^0:
    // TR: 1
    %1 = llhd.prb %ack_src_q : !hw.inout<i1>
    %ack_src_q_shadow = llhd.var %1 : i1
    cf.br ^init
  ^init:
    // TR: 2
    %clk_i_prb = llhd.prb %clk_i : !hw.inout<i1>
    %rst_ni_prb = llhd.prb %rst_ni : !hw.inout<i1>
    llhd.wait (%clk_i, %rst_ni : !hw.inout<i1>, !hw.inout<i1>), ^check
  ^check:
    // TR: 0
    %2 = llhd.prb %ack_src_q : !hw.inout<i1>
    llhd.store %ack_src_q_shadow, %2 : !llhd.ptr<i1>
    llhd.store %ack_src_q_shadow, %2 : !llhd.ptr<i1>
    %clk_i_prb1 = llhd.prb %clk_i : !hw.inout<i1>
    %3 = hw.constant 0 : i1
    %4 = comb.icmp eq %clk_i_prb, %3 : i1
    %5 = comb.icmp ne %clk_i_prb1, %3 : i1
    %posedge = comb.and %4, %5 : i1
    %rst_ni_prb1 = llhd.prb %rst_ni : !hw.inout<i1>
    %6 = comb.icmp ne %rst_ni_prb, %3 : i1
    %7 = comb.icmp eq %rst_ni_prb1, %3 : i1
    %negedge = comb.and %7, %6 : i1
    %event_or = comb.or %posedge, %negedge : i1
    cf.cond_br %event_or, ^event, ^init
  ^event:
    // TR: 0
    %8 = comb.icmp ne %rst_ni_prb1, %3 : i1
    %9 = comb.xor %8, %allset : i1
    %10 = comb.icmp ne %9, %3 : i1
    %11 = llhd.constant_time <0s, 1d, 0e>
    cf.cond_br %10, ^if_true, ^if_false
  ^if_false:
    // TR: 0
    %async_ack_i_prb = llhd.prb %async_ack_i : !hw.inout<i1>
    llhd.drv %ack_src_q, %async_ack_i_prb after %11 : !hw.inout<i1>
    %ack_src_q_shadow_ld = llhd.load %ack_src_q_shadow : !llhd.ptr<i1>
    llhd.drv %ack_q, %ack_src_q_shadow_ld after %11 : !hw.inout<i1>
    cf.br ^0
  ^if_true:
    // TR: 0
    llhd.drv %ack_src_q, %3 after %11 : !hw.inout<i1>
    llhd.drv %ack_q, %3 after %11 : !hw.inout<i1>
    cf.br ^0
  }
}
