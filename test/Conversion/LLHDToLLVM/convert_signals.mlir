// NOTE: Assertions have been autogenerated by utils/generate-test-checks.py
// RUN: circt-opt %s --convert-llhd-to-llvm | FileCheck %s

// CHECK-LABEL:   llvm.func @drive_signal(!llvm<"i8*">, !llvm<"{ i8*, i64, i64, i64 }*">, !llvm<"i8*">, !llvm.i64, !llvm.i32, !llvm.i32, !llvm.i32)

// CHECK-LABEL:   llvm.func @convert_sig(
// CHECK-SAME:                           %[[VAL_0:.*]]: !llvm<"i8*">,
// CHECK-SAME:                           %[[VAL_1:.*]]: !llvm<"{ i8*, i64, i64, i64 }*">) {
// CHECK:           %[[VAL_2:.*]] = llvm.mlir.constant(false) : !llvm.i1
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_4:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_3]]] : (!llvm<"{ i8*, i64, i64, i64 }*">, !llvm.i32) -> !llvm<"{ i8*, i64, i64, i64 }*">
// CHECK:           llvm.return
// CHECK:         }
llhd.entity @convert_sig () -> () {
  %init = llhd.const 0 : i1
  %s0 = llhd.sig "sig0" %init : i1
}

// CHECK-LABEL:   llvm.func @convert_prb(
// CHECK-SAME:                           %[[VAL_0:.*]]: !llvm<"i8*">,
// CHECK-SAME:                           %[[VAL_1:.*]]: !llvm<"{ i8*, i64, i64, i64 }*">) {
// CHECK:           %[[VAL_2:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_3:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_2]]] : (!llvm<"{ i8*, i64, i64, i64 }*">, !llvm.i32) -> !llvm<"{ i8*, i64, i64, i64 }*">
// CHECK:           %[[VAL_4:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_5:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_6:.*]] = llvm.getelementptr %[[VAL_3]]{{\[}}%[[VAL_4]], %[[VAL_4]]] : (!llvm<"{ i8*, i64, i64, i64 }*">, !llvm.i32, !llvm.i32) -> !llvm<"i8**">
// CHECK:           %[[VAL_7:.*]] = llvm.load %[[VAL_6]] : !llvm<"i8**">
// CHECK:           %[[VAL_8:.*]] = llvm.getelementptr %[[VAL_3]]{{\[}}%[[VAL_4]], %[[VAL_5]]] : (!llvm<"{ i8*, i64, i64, i64 }*">, !llvm.i32, !llvm.i32) -> !llvm<"i64*">
// CHECK:           %[[VAL_9:.*]] = llvm.load %[[VAL_8]] : !llvm<"i64*">
// CHECK:           %[[VAL_10:.*]] = llvm.bitcast %[[VAL_7]] : !llvm<"i8*"> to !llvm<"i16*">
// CHECK:           %[[VAL_11:.*]] = llvm.load %[[VAL_10]] : !llvm<"i16*">
// CHECK:           %[[VAL_12:.*]] = llvm.trunc %[[VAL_9]] : !llvm.i64 to !llvm.i16
// CHECK:           %[[VAL_13:.*]] = llvm.lshr %[[VAL_11]], %[[VAL_12]] : !llvm.i16
// CHECK:           %[[VAL_14:.*]] = llvm.trunc %[[VAL_13]] : !llvm.i16 to !llvm.i1
// CHECK:           llvm.return
// CHECK:         }
llhd.entity @convert_prb (%sI1 : !llhd.sig<i1>) -> () {
  %p0 = llhd.prb %sI1 : !llhd.sig<i1>
}

// CHECK-LABEL:   llvm.func @convert_drv(
// CHECK-SAME:                           %[[VAL_0:.*]]: !llvm<"i8*">,
// CHECK-SAME:                           %[[VAL_1:.*]]: !llvm<"{ i8*, i64, i64, i64 }*">) {
// CHECK:           %[[VAL_2:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_3:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_2]]] : (!llvm<"{ i8*, i64, i64, i64 }*">, !llvm.i32) -> !llvm<"{ i8*, i64, i64, i64 }*">
// CHECK:           %[[VAL_4:.*]] = llvm.mlir.constant(false) : !llvm.i1
// CHECK:           %[[VAL_5:.*]] = llvm.mlir.constant(dense<[1, 0, 0]> : vector<3xi32>) : !llvm<"[3 x i32]">
// CHECK:           %[[VAL_6:.*]] = llvm.mlir.constant(1 : i64) : !llvm.i64
// CHECK:           %[[VAL_7:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_8:.*]] = llvm.alloca %[[VAL_7]] x !llvm.i1 {alignment = 4 : i64} : (!llvm.i32) -> !llvm<"i1*">
// CHECK:           llvm.store %[[VAL_4]], %[[VAL_8]] : !llvm<"i1*">
// CHECK:           %[[VAL_9:.*]] = llvm.bitcast %[[VAL_8]] : !llvm<"i1*"> to !llvm<"i8*">
// CHECK:           %[[VAL_10:.*]] = llvm.extractvalue %[[VAL_5]][0 : i32] : !llvm<"[3 x i32]">
// CHECK:           %[[VAL_11:.*]] = llvm.extractvalue %[[VAL_5]][1 : i32] : !llvm<"[3 x i32]">
// CHECK:           %[[VAL_12:.*]] = llvm.extractvalue %[[VAL_5]][2 : i32] : !llvm<"[3 x i32]">
// CHECK:           %[[VAL_13:.*]] = llvm.call @drive_signal(%[[VAL_0]], %[[VAL_3]], %[[VAL_9]], %[[VAL_6]], %[[VAL_10]], %[[VAL_11]], %[[VAL_12]]) : (!llvm<"i8*">, !llvm<"{ i8*, i64, i64, i64 }*">, !llvm<"i8*">, !llvm.i64, !llvm.i32, !llvm.i32, !llvm.i32) -> !llvm.void
// CHECK:           llvm.return
// CHECK:         }
llhd.entity @convert_drv (%sI1 : !llhd.sig<i1>) -> () {
  %cI1 = llhd.const 0 : i1
  %t = llhd.const #llhd.time<1ns, 0d, 0e> : !llhd.time
  llhd.drv %sI1, %cI1 after %t : !llhd.sig<i1>
}
