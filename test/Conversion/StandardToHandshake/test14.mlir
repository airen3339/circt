// NOTE: Assertions have been autogenerated by utils/update_mlir_test_checks.py
// RUN: circt-opt -lower-std-to-handshake %s | FileCheck %s
  func @affine_store(%arg0: index) {
// CHECK:       module {

// CHECK-LABEL:   handshake.func @affine_store(
// CHECK-SAME:                                 %[[VAL_0:.*]]: index, %[[VAL_1:.*]]: none, ...) -> none attributes {argNames = ["in0", "inCtrl"], resNames = ["outCtrl"]} {
// CHECK:           %[[VAL_2:.*]] = "handshake.memory"(%[[VAL_3:.*]]#0, %[[VAL_3]]#1) {id = 0 : i32, ld_count = 0 : i32, lsq = false, st_count = 1 : i32, type = memref<10xf32>} : (f32, index) -> none
// CHECK:           %[[VAL_4:.*]] = "handshake.merge"(%[[VAL_0]]) : (index) -> index
// CHECK:           %[[VAL_5:.*]]:5 = "handshake.fork"(%[[VAL_1]]) {control = true} : (none) -> (none, none, none, none, none)
// CHECK:           %[[VAL_6:.*]] = "handshake.constant"(%[[VAL_5]]#3) {value = 1.100000e+01 : f32} : (none) -> f32
// CHECK:           %[[VAL_7:.*]] = "handshake.constant"(%[[VAL_5]]#2) {value = 0 : index} : (none) -> index
// CHECK:           %[[VAL_8:.*]] = "handshake.constant"(%[[VAL_5]]#1) {value = 10 : index} : (none) -> index
// CHECK:           %[[VAL_9:.*]] = "handshake.constant"(%[[VAL_5]]#0) {value = 1 : index} : (none) -> index
// CHECK:           %[[VAL_10:.*]] = "handshake.branch"(%[[VAL_4]]) {control = false} : (index) -> index
// CHECK:           %[[VAL_11:.*]] = "handshake.branch"(%[[VAL_5]]#4) {control = true} : (none) -> none
// CHECK:           %[[VAL_12:.*]] = "handshake.branch"(%[[VAL_6]]) {control = false} : (f32) -> f32
// CHECK:           %[[VAL_13:.*]] = "handshake.branch"(%[[VAL_7]]) {control = false} : (index) -> index
// CHECK:           %[[VAL_14:.*]] = "handshake.branch"(%[[VAL_8]]) {control = false} : (index) -> index
// CHECK:           %[[VAL_15:.*]] = "handshake.branch"(%[[VAL_9]]) {control = false} : (index) -> index
// CHECK:           %[[VAL_16:.*]] = "handshake.mux"(%[[VAL_17:.*]]#4, %[[VAL_18:.*]], %[[VAL_14]]) : (index, index, index) -> index
// CHECK:           %[[VAL_19:.*]]:2 = "handshake.fork"(%[[VAL_16]]) {control = false} : (index) -> (index, index)
// CHECK:           %[[VAL_20:.*]] = "handshake.mux"(%[[VAL_17]]#3, %[[VAL_21:.*]], %[[VAL_10]]) : (index, index, index) -> index
// CHECK:           %[[VAL_22:.*]] = "handshake.mux"(%[[VAL_17]]#2, %[[VAL_23:.*]], %[[VAL_12]]) : (index, f32, f32) -> f32
// CHECK:           %[[VAL_24:.*]] = "handshake.mux"(%[[VAL_17]]#1, %[[VAL_25:.*]], %[[VAL_15]]) : (index, index, index) -> index
// CHECK:           %[[VAL_26:.*]]:2 = "handshake.control_merge"(%[[VAL_27:.*]], %[[VAL_11]]) {control = true} : (none, none) -> (none, index)
// CHECK:           %[[VAL_17]]:5 = "handshake.fork"(%[[VAL_26]]#1) {control = false} : (index) -> (index, index, index, index, index)
// CHECK:           %[[VAL_28:.*]] = "handshake.mux"(%[[VAL_17]]#0, %[[VAL_29:.*]], %[[VAL_13]]) : (index, index, index) -> index
// CHECK:           %[[VAL_30:.*]]:2 = "handshake.fork"(%[[VAL_28]]) {control = false} : (index) -> (index, index)
// CHECK:           %[[VAL_31:.*]] = arith.cmpi slt, %[[VAL_30]]#1, %[[VAL_19]]#1 : index
// CHECK:           %[[VAL_32:.*]]:6 = "handshake.fork"(%[[VAL_31]]) {control = false} : (i1) -> (i1, i1, i1, i1, i1, i1)
// CHECK:           %[[VAL_33:.*]], %[[VAL_34:.*]] = "handshake.conditional_branch"(%[[VAL_32]]#5, %[[VAL_19]]#0) {control = false} : (i1, index) -> (index, index)
// CHECK:           "handshake.sink"(%[[VAL_34]]) : (index) -> ()
// CHECK:           %[[VAL_35:.*]], %[[VAL_36:.*]] = "handshake.conditional_branch"(%[[VAL_32]]#4, %[[VAL_20]]) {control = false} : (i1, index) -> (index, index)
// CHECK:           "handshake.sink"(%[[VAL_36]]) : (index) -> ()
// CHECK:           %[[VAL_37:.*]], %[[VAL_38:.*]] = "handshake.conditional_branch"(%[[VAL_32]]#3, %[[VAL_22]]) {control = false} : (i1, f32) -> (f32, f32)
// CHECK:           "handshake.sink"(%[[VAL_38]]) : (f32) -> ()
// CHECK:           %[[VAL_39:.*]], %[[VAL_40:.*]] = "handshake.conditional_branch"(%[[VAL_32]]#2, %[[VAL_24]]) {control = false} : (i1, index) -> (index, index)
// CHECK:           "handshake.sink"(%[[VAL_40]]) : (index) -> ()
// CHECK:           %[[VAL_41:.*]], %[[VAL_42:.*]] = "handshake.conditional_branch"(%[[VAL_32]]#1, %[[VAL_26]]#0) {control = true} : (i1, none) -> (none, none)
// CHECK:           %[[VAL_43:.*]], %[[VAL_44:.*]] = "handshake.conditional_branch"(%[[VAL_32]]#0, %[[VAL_30]]#0) {control = false} : (i1, index) -> (index, index)
// CHECK:           "handshake.sink"(%[[VAL_44]]) : (index) -> ()
// CHECK:           %[[VAL_45:.*]] = "handshake.merge"(%[[VAL_35]]) : (index) -> index
// CHECK:           %[[VAL_46:.*]]:2 = "handshake.fork"(%[[VAL_45]]) {control = false} : (index) -> (index, index)
// CHECK:           %[[VAL_47:.*]] = "handshake.merge"(%[[VAL_43]]) : (index) -> index
// CHECK:           %[[VAL_48:.*]]:2 = "handshake.fork"(%[[VAL_47]]) {control = false} : (index) -> (index, index)
// CHECK:           %[[VAL_49:.*]] = "handshake.merge"(%[[VAL_37]]) : (f32) -> f32
// CHECK:           %[[VAL_50:.*]]:2 = "handshake.fork"(%[[VAL_49]]) {control = false} : (f32) -> (f32, f32)
// CHECK:           %[[VAL_51:.*]] = "handshake.merge"(%[[VAL_39]]) : (index) -> index
// CHECK:           %[[VAL_52:.*]]:2 = "handshake.fork"(%[[VAL_51]]) {control = false} : (index) -> (index, index)
// CHECK:           %[[VAL_53:.*]] = "handshake.merge"(%[[VAL_33]]) : (index) -> index
// CHECK:           %[[VAL_54:.*]]:2 = "handshake.control_merge"(%[[VAL_41]]) {control = true} : (none) -> (none, index)
// CHECK:           %[[VAL_55:.*]]:2 = "handshake.fork"(%[[VAL_54]]#0) {control = true} : (none) -> (none, none)
// CHECK:           %[[VAL_56:.*]]:3 = "handshake.fork"(%[[VAL_55]]#1) {control = true} : (none) -> (none, none, none)
// CHECK:           %[[VAL_57:.*]] = "handshake.join"(%[[VAL_56]]#2, %[[VAL_2]]) {control = true} : (none, none) -> none
// CHECK:           "handshake.sink"(%[[VAL_54]]#1) : (index) -> ()
// CHECK:           %[[VAL_58:.*]] = "handshake.constant"(%[[VAL_56]]#1) {value = -1 : index} : (none) -> index
// CHECK:           %[[VAL_59:.*]] = arith.muli %[[VAL_46]]#1, %[[VAL_58]] : index
// CHECK:           %[[VAL_60:.*]] = arith.addi %[[VAL_48]]#1, %[[VAL_59]] : index
// CHECK:           %[[VAL_61:.*]] = "handshake.constant"(%[[VAL_56]]#0) {value = 7 : index} : (none) -> index
// CHECK:           %[[VAL_62:.*]] = arith.addi %[[VAL_60]], %[[VAL_61]] : index
// CHECK:           %[[VAL_3]]:2 = "handshake.store"(%[[VAL_50]]#1, %[[VAL_62]], %[[VAL_55]]#0) : (f32, index, none) -> (f32, index)
// CHECK:           %[[VAL_63:.*]] = arith.addi %[[VAL_48]]#0, %[[VAL_52]]#1 : index
// CHECK:           %[[VAL_21]] = "handshake.branch"(%[[VAL_46]]#0) {control = false} : (index) -> index
// CHECK:           %[[VAL_23]] = "handshake.branch"(%[[VAL_50]]#0) {control = false} : (f32) -> f32
// CHECK:           %[[VAL_25]] = "handshake.branch"(%[[VAL_52]]#0) {control = false} : (index) -> index
// CHECK:           %[[VAL_18]] = "handshake.branch"(%[[VAL_53]]) {control = false} : (index) -> index
// CHECK:           %[[VAL_27]] = "handshake.branch"(%[[VAL_57]]) {control = true} : (none) -> none
// CHECK:           %[[VAL_29]] = "handshake.branch"(%[[VAL_63]]) {control = false} : (index) -> index
// CHECK:           %[[VAL_64:.*]]:2 = "handshake.control_merge"(%[[VAL_42]]) {control = true} : (none) -> (none, index)
// CHECK:           "handshake.sink"(%[[VAL_64]]#1) : (index) -> ()
// CHECK:           handshake.return %[[VAL_64]]#0 : none
// CHECK:         }
// CHECK:       }

    %0 = memref.alloc() : memref<10xf32>
    %cst = arith.constant 1.100000e+01 : f32
    %c0 = arith.constant 0 : index
    %c10 = arith.constant 10 : index
    %c1 = arith.constant 1 : index
    br ^bb1(%c0 : index)
  ^bb1(%1: index):      // 2 preds: ^bb0, ^bb2
    %2 = arith.cmpi slt, %1, %c10 : index
    cond_br %2, ^bb2, ^bb3
  ^bb2: // pred: ^bb1
    %c-1 = arith.constant -1 : index
    %3 = arith.muli %arg0, %c-1 : index
    %4 = arith.addi %1, %3 : index
    %c7 = arith.constant 7 : index
    %5 = arith.addi %4, %c7 : index
    memref.store %cst, %0[%5] : memref<10xf32>
    %6 = arith.addi %1, %c1 : index
    br ^bb1(%6 : index)
  ^bb3: // pred: ^bb1
    return
  }
