// RUN: circt-opt -lower-handshake-to-hw -split-input-file %s | FileCheck %s

// CHECK-LABEL:   hw.module @handshake_sync_in_ui32_out_ui32(
// CHECK-SAME:      %[[VAL_0:.*]]: !esi.channel<none>, %[[VAL_1:.*]]: !esi.channel<i32>, %[[VAL_2:.*]]: i1, %[[VAL_3:.*]]: i1) -> (out0: !esi.channel<none>, out1: !esi.channel<i32>) {
// CHECK:           %[[VAL_4:.*]], %[[VAL_5:.*]] = esi.unwrap.vr %[[VAL_0]], %[[VAL_6:.*]] : none
// CHECK:           %[[VAL_7:.*]], %[[VAL_8:.*]] = esi.unwrap.vr %[[VAL_1]], %[[VAL_6]] : i32
// CHECK:           %[[VAL_9:.*]], %[[VAL_10:.*]] = esi.wrap.vr %[[VAL_4]], %[[VAL_11:.*]] : none
// CHECK:           %[[VAL_12:.*]], %[[VAL_13:.*]] = esi.wrap.vr %[[VAL_7]], %[[VAL_14:.*]] : i32
// CHECK:           %[[VAL_15:.*]] = comb.and %[[VAL_5]], %[[VAL_8]] : i1
// CHECK:           %[[VAL_6]] = comb.and %[[VAL_16:.*]], %[[VAL_15]] : i1
// CHECK:           %[[VAL_17:.*]] = hw.constant false
// CHECK:           %[[VAL_18:.*]] = hw.constant true
// CHECK:           %[[VAL_19:.*]] = comb.xor %[[VAL_16]], %[[VAL_18]] : i1
// CHECK:           %[[VAL_20:.*]] = comb.and %[[VAL_21:.*]], %[[VAL_19]] : i1
// CHECK:           %[[VAL_22:.*]] = seq.compreg %[[VAL_20]], %[[VAL_2]], %[[VAL_3]], %[[VAL_17]]  : i1
// CHECK:           %[[VAL_23:.*]] = hw.constant true
// CHECK:           %[[VAL_24:.*]] = comb.xor %[[VAL_22]], %[[VAL_23]] : i1
// CHECK:           %[[VAL_11]] = comb.and %[[VAL_24]], %[[VAL_15]] : i1
// CHECK:           %[[VAL_25:.*]] = comb.and %[[VAL_10]], %[[VAL_15]] : i1
// CHECK:           %[[VAL_21]] = comb.and %[[VAL_25]], %[[VAL_22]] : i1
// CHECK:           %[[VAL_26:.*]] = hw.constant true
// CHECK:           %[[VAL_27:.*]] = comb.xor %[[VAL_16]], %[[VAL_26]] : i1
// CHECK:           %[[VAL_28:.*]] = comb.and %[[VAL_29:.*]], %[[VAL_27]] : i1
// CHECK:           %[[VAL_30:.*]] = seq.compreg %[[VAL_28]], %[[VAL_2]], %[[VAL_3]], %[[VAL_17]]  : i1
// CHECK:           %[[VAL_31:.*]] = hw.constant true
// CHECK:           %[[VAL_32:.*]] = comb.xor %[[VAL_30]], %[[VAL_31]] : i1
// CHECK:           %[[VAL_14]] = comb.and %[[VAL_32]], %[[VAL_15]] : i1
// CHECK:           %[[VAL_33:.*]] = comb.and %[[VAL_13]], %[[VAL_15]] : i1
// CHECK:           %[[VAL_29]] = comb.and %[[VAL_33]], %[[VAL_30]] : i1
// CHECK:           %[[VAL_16]] = comb.and %[[VAL_21]], %[[VAL_29]] : i1
// CHECK:           hw.output %[[VAL_9]], %[[VAL_12]] : !esi.channel<none>, !esi.channel<i32>
// CHECK:         }

handshake.func @main(%arg0: none, %arg1: i32) -> (none, i32) {
  %res:2 = sync %arg0, %arg1 : none, i32
  return %res#0, %res#1 : none, i32
}
