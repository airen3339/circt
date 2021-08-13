// RUN: circt-opt -convert-fsm-to-hw %s | FileCheck %s

// CHECK: hw.module @foo([[I_VALID:%.+]]: i1, [[I_LEN:%.+]]: i8, %clk: i1, %rst_n: i1) -> (%out0: i1) {
// CHECK:   %state = sv.reg  : !hw.inout<i2>
// CHECK:   [[STATE:%.+]] = sv.read_inout %state : !hw.inout<i2>
// CHECK:   %o_ready = sv.reg  : !hw.inout<i1>
// CHECK:   [[O_READY:%.+]] = sv.read_inout %o_ready : !hw.inout<i1>
// CHECK:   %counter = sv.reg  : !hw.inout<i8>
// CHECK:   [[COUNTER:%.+]] = sv.read_inout %counter : !hw.inout<i8>
// CHECK:   %true = hw.constant true
// CHECK:   %false = hw.constant false
// CHECK:   %c0_i2 = hw.constant 0 : i2
// CHECK:   %c1_i2 = hw.constant 1 : i2
// CHECK:   sv.alwaysff(posedge %clk)  {
// CHECK:     sv.passign %state, [[STATE]] : i2
// CHECK:     sv.passign %o_ready, [[O_READY]] : i1
// CHECK:     sv.passign %counter, [[COUNTER]] : i8
// CHECK:     sv.casez [[STATE]] : i2
// CHECK:     case b00: {
// CHECK:       sv.if [[I_VALID]]  {
// CHECK:         sv.passign %state, %c1_i2 : i2
// CHECK:         sv.passign %o_ready, %false : i1
// CHECK:         sv.passign %counter, [[I_LEN]] : i8
// CHECK:       } else  {
// CHECK:         sv.passign %state, %c0_i2 : i2
// CHECK:         sv.passign %o_ready, %false : i1
// CHECK:         sv.passign %o_ready, %true : i1
// CHECK:       }
// CHECK:     }
// CHECK:     case b01: {
// CHECK:       sv.passign %state, %c1_i2 : i2
// CHECK:     }
// CHECK:   }(asyncreset : negedge %rst_n)  {
// CHECK:     sv.passign %state, %c0_i2 : i2
// CHECK:     %false_0 = hw.constant false
// CHECK:     sv.passign %o_ready, %false_0 : i1
// CHECK:     %c0_i8 = hw.constant 0 : i8
// CHECK:     sv.passign %counter, %c0_i8 : i8
// CHECK:     sv.passign %o_ready, %true : i1
// CHECK:   }
// CHECK:   hw.output [[O_READY]] : i1
// CHECK: }
// CHECK: hw.module @qux(%clock: i1, %reset: i1) {
// CHECK:   %true = hw.constant true
// CHECK:   %c16_i8 = hw.constant 16 : i8
// CHECK:   %foo_inst.out0 = hw.instance "foo_inst" sym @foo_inst @foo(%true, %c16_i8, %clock, %reset) : (i1, i8, i1, i1) -> i1
// CHECK:   hw.output
// CHECK: }

fsm.machine @foo(%i_valid: i1, %i_len: i8) -> i1 attributes {stateType = i2} {
  %o_ready = fsm.variable "o_ready" {initValue = true} : i1
  %counter = fsm.variable "counter" {initValue = 0 : i8} : i8

  %true = constant true
  %false = constant false

  fsm.state "IDLE" entry  {
    fsm.update %o_ready, %true : i1
  } exit  {
    fsm.update %o_ready, %false : i1
  } transitions  {
    fsm.transition @BUSY guard  {
      fsm.return %i_valid : i1
    } action  {
      fsm.update %counter, %i_len : i8
    }
    fsm.transition @IDLE guard  {
    } action  {
    }
  }

  fsm.state "BUSY" entry  {
  } exit  {
  } transitions  {
    fsm.transition @BUSY guard  {
    } action  {
    }
  }
  fsm.output %o_ready : i1
}

hw.module @qux(%clock: i1, %reset: i1) {
  %i_valid = hw.constant true
  %i_len = hw.constant 16 : i8
  %o_ready = fsm.hw_instance "foo_inst" @foo(%i_valid, %i_len) : (i1, i8) -> i1, clock %clock : i1, reset %reset : i1
}
