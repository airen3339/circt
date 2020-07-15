// RUN: circt-opt %s -mlir-print-op-generic -canonicalize | circt-opt | circt-opt | FileCheck %s

// CHECK-LABEL: @check_neg_folding
func @check_neg_folding() -> (i16) {
  // CHECK-NEXT: %[[NEG:.*]] = llhd.const -5 : i16
  %a = llhd.const 5 : i16
  %0 = llhd.neg %a : i16

  // CHECK-NEXT: return %[[NEG]] : i16
  return %0 : i16
}

// CHECK-LABEL: @check_smod_folding
// CHECK-SAME: %[[VAL_0:.*]]: i64
func @check_smod_folding(%a : i64) -> (i64, i64, i64) {
  %c0 = llhd.const 0 : i64
  %c1 = llhd.const 1 : i64
  %c9 = llhd.const 9 : i64
  %cn5 = llhd.const -5 : i64
  // CHECK-NEXT: %[[VAL_1:.*]] = llhd.const 0 : i64
  %0 = llhd.smod %a, %c1 : i64
  %1 = llhd.smod %c0, %a : i64
  // CHECK-NEXT: %[[VAL_2:.*]] = llhd.const -1 : i64
  %2 = llhd.smod %c9, %cn5 : i64

  // CHECK-NEXT: return %[[VAL_1]], %[[VAL_1]], %[[VAL_2]] : i64, i64, i64
  return %0, %1, %2 : i64, i64, i64
}

// CHECK-LABEL: @check_eq_folding
// CHECK-SAME: %[[VAL_0:.*]]: i64,
// CHECK-SAME: %[[VAL_1:.*]]: i1,
// CHECK-SAME: %[[VAL_2:.*]]: tuple<i1, i2, i3>
func @check_eq_folding(%a : i64, %b : i1, %tup : tuple<i1, i2, i3>) -> (i1, i1, i1, i1) {
  %c1 = llhd.const 1 : i1
  %c3 = llhd.const 3 : i64
  %c4 = llhd.const 4 : i64
  %0 = llhd.eq %b, %c1 : i1
  // CHECK-NEXT: %[[VAL_3:.*]] = llhd.const true : i1
  %1 = llhd.eq %a, %a : i64
  %2 = llhd.eq %tup, %tup : tuple<i1, i2, i3>
  // CHECK-NEXT: %[[VAL_4:.*]] = llhd.const false : i1
  %3 = llhd.eq %c3, %c4 : i64

  // CHECK-NEXT: return %[[VAL_1]], %[[VAL_3]], %[[VAL_3]], %[[VAL_4]] : i1, i1, i1, i1
  return %0, %1, %2, %3 : i1, i1, i1, i1
}

// CHECK-LABEL: @check_neq_folding
// CHECK-SAME:  %[[VAL_0:.*]]: i64,
// CHECK-SAME:  %[[VAL_1:.*]]: i1,
// CHECK-SAME:  %[[VAL_2:.*]]: tuple<i1, i2, i3>
func @check_neq_folding(%a : i64, %b : i1, %tup : tuple<i1, i2, i3>) -> (i1, i1, i1, i1) {
  %c0 = llhd.const 0 : i1
  %c3 = llhd.const 3 : i64
  %c4 = llhd.const 4 : i64
  %0 = llhd.neq %b, %c0 : i1
  // CHECK-NEXT: %[[VAL_3:.*]] = llhd.const false : i1
  %1 = llhd.neq %a, %a : i64
  %2 = llhd.neq %tup, %tup : tuple<i1, i2, i3>
  // CHECK-NEXT: %[[VAL_4:.*]] = llhd.const true : i1
  %3 = llhd.neq %c3, %c4 : i64

  // CHECK-NEXT: return %[[VAL_1]], %[[VAL_3]], %[[VAL_3]], %[[VAL_4]] : i1, i1, i1, i1
  return %0, %1, %2, %3 : i1, i1, i1, i1
}
