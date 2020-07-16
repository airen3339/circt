// NOTE: Assertions have been autogenerated by utils/update_mlir_test_checks.py
// RUN: circt-opt -create-dataflow %s | FileCheck %s
func @affine_applies() {
// CHECK:       module {

// CHECK-LABEL:   handshake.func @affine_applies(
// CHECK-SAME:                                   %[[VAL_0:.*]]: none, ...) -> none {
// CHECK:           %[[VAL_1:.*]]:18 = "handshake.fork"(%[[VAL_0]]) {control = true} : (none) -> (none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none)
// CHECK:           %[[VAL_2:.*]] = "handshake.constant"(%[[VAL_1]]#16) {value = 0 : index} : (none) -> index
// CHECK:           %[[VAL_3:.*]]:2 = "handshake.fork"(%[[VAL_2]]) {control = false} : (index) -> (index, index)
// CHECK:           %[[VAL_4:.*]] = "handshake.constant"(%[[VAL_1]]#15) {value = 101 : index} : (none) -> index
// CHECK:           "handshake.sink"(%[[VAL_4]]) : (index) -> ()
// CHECK:           %[[VAL_5:.*]] = "handshake.constant"(%[[VAL_1]]#14) {value = 102 : index} : (none) -> index
// CHECK:           "handshake.sink"(%[[VAL_5]]) : (index) -> ()
// CHECK:           %[[VAL_6:.*]] = addi %[[VAL_3]]#0, %[[VAL_3]]#1 : index
// CHECK:           %[[VAL_7:.*]] = "handshake.constant"(%[[VAL_1]]#13) {value = 1 : index} : (none) -> index
// CHECK:           %[[VAL_8:.*]] = addi %[[VAL_6]], %[[VAL_7]] : index
// CHECK:           "handshake.sink"(%[[VAL_8]]) : (index) -> ()
// CHECK:           %[[VAL_9:.*]] = "handshake.constant"(%[[VAL_1]]#12) {value = 103 : index} : (none) -> index
// CHECK:           %[[VAL_10:.*]] = "handshake.constant"(%[[VAL_1]]#11) {value = 104 : index} : (none) -> index
// CHECK:           %[[VAL_11:.*]] = "handshake.constant"(%[[VAL_1]]#10) {value = 105 : index} : (none) -> index
// CHECK:           %[[VAL_12:.*]] = "handshake.constant"(%[[VAL_1]]#9) {value = 106 : index} : (none) -> index
// CHECK:           %[[VAL_13:.*]] = "handshake.constant"(%[[VAL_1]]#8) {value = 107 : index} : (none) -> index
// CHECK:           %[[VAL_14:.*]] = "handshake.constant"(%[[VAL_1]]#7) {value = 108 : index} : (none) -> index
// CHECK:           %[[VAL_15:.*]] = "handshake.constant"(%[[VAL_1]]#6) {value = 109 : index} : (none) -> index
// CHECK:           %[[VAL_16:.*]] = "handshake.constant"(%[[VAL_1]]#5) {value = 2 : index} : (none) -> index
// CHECK:           %[[VAL_17:.*]] = muli %[[VAL_10]], %[[VAL_16]] : index
// CHECK:           %[[VAL_18:.*]] = addi %[[VAL_9]], %[[VAL_17]] : index
// CHECK:           %[[VAL_19:.*]] = "handshake.constant"(%[[VAL_1]]#4) {value = 3 : index} : (none) -> index
// CHECK:           %[[VAL_20:.*]] = muli %[[VAL_11]], %[[VAL_19]] : index
// CHECK:           %[[VAL_21:.*]] = addi %[[VAL_18]], %[[VAL_20]] : index
// CHECK:           %[[VAL_22:.*]] = "handshake.constant"(%[[VAL_1]]#3) {value = 4 : index} : (none) -> index
// CHECK:           %[[VAL_23:.*]] = muli %[[VAL_12]], %[[VAL_22]] : index
// CHECK:           %[[VAL_24:.*]] = addi %[[VAL_21]], %[[VAL_23]] : index
// CHECK:           %[[VAL_25:.*]] = "handshake.constant"(%[[VAL_1]]#2) {value = 5 : index} : (none) -> index
// CHECK:           %[[VAL_26:.*]] = muli %[[VAL_13]], %[[VAL_25]] : index
// CHECK:           %[[VAL_27:.*]] = addi %[[VAL_24]], %[[VAL_26]] : index
// CHECK:           %[[VAL_28:.*]] = "handshake.constant"(%[[VAL_1]]#1) {value = 6 : index} : (none) -> index
// CHECK:           %[[VAL_29:.*]] = muli %[[VAL_14]], %[[VAL_28]] : index
// CHECK:           %[[VAL_30:.*]] = addi %[[VAL_27]], %[[VAL_29]] : index
// CHECK:           %[[VAL_31:.*]] = "handshake.constant"(%[[VAL_1]]#0) {value = 7 : index} : (none) -> index
// CHECK:           %[[VAL_32:.*]] = muli %[[VAL_15]], %[[VAL_31]] : index
// CHECK:           %[[VAL_33:.*]] = addi %[[VAL_30]], %[[VAL_32]] : index
// CHECK:           "handshake.sink"(%[[VAL_33]]) : (index) -> ()
// CHECK:           handshake.return %[[VAL_1]]#17 : none
// CHECK:         }
// CHECK:       }

    %c0 = constant 0 : index
    %c101 = constant 101 : index
    %c102 = constant 102 : index
    %0 = addi %c0, %c0 : index
    %c1 = constant 1 : index
    %1 = addi %0, %c1 : index
    %c103 = constant 103 : index
    %c104 = constant 104 : index
    %c105 = constant 105 : index
    %c106 = constant 106 : index
    %c107 = constant 107 : index
    %c108 = constant 108 : index
    %c109 = constant 109 : index
    %c2 = constant 2 : index
    %2 = muli %c104, %c2 : index
    %3 = addi %c103, %2 : index
    %c3 = constant 3 : index
    %4 = muli %c105, %c3 : index
    %5 = addi %3, %4 : index
    %c4 = constant 4 : index
    %6 = muli %c106, %c4 : index
    %7 = addi %5, %6 : index
    %c5 = constant 5 : index
    %8 = muli %c107, %c5 : index
    %9 = addi %7, %8 : index
    %c6 = constant 6 : index
    %10 = muli %c108, %c6 : index
    %11 = addi %9, %10 : index
    %c7 = constant 7 : index
    %12 = muli %c109, %c7 : index
    %13 = addi %11, %12 : index
    return
  }
