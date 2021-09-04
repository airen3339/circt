// NOTE: Assertions have been autogenerated by utils/generate-test-checks.py
// RUN: circt-opt %s --convert-llhd-to-llvm | FileCheck %s

// CHECK-LABEL:   llvm.func @driveSignal(!llvm.ptr<i8>, !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.ptr<i8>, i64, i64, i64, i64)

// CHECK-LABEL:   llvm.func @convert_sig(
// CHECK-SAME:                           %[[VAL_0:.*]]: !llvm.ptr<i8>,
// CHECK-SAME:                           %[[VAL_1:.*]]: !llvm.ptr<struct<()>>,
// CHECK-SAME:                           %[[VAL_2:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>) {
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(false) : i1
// CHECK:           %[[VAL_4:.*]] = llvm.mlir.undef : !llvm.array<4 x i1>
// CHECK:           %[[VAL_5:.*]] = llvm.insertvalue %[[VAL_3]], %[[VAL_4]][0 : i32] : !llvm.array<4 x i1>
// CHECK:           %[[VAL_6:.*]] = llvm.insertvalue %[[VAL_3]], %[[VAL_5]][1 : i32] : !llvm.array<4 x i1>
// CHECK:           %[[VAL_7:.*]] = llvm.insertvalue %[[VAL_3]], %[[VAL_6]][2 : i32] : !llvm.array<4 x i1>
// CHECK:           %[[VAL_8:.*]] = llvm.insertvalue %[[VAL_3]], %[[VAL_7]][3 : i32] : !llvm.array<4 x i1>
// CHECK:           %[[VAL_9:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_10:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_9]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           %[[VAL_11:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_12:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_11]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.return
// CHECK:         }
llhd.entity @convert_sig () -> () {
  %init = hw.constant 0 : i1
  %initArr = hw.array_create %init, %init, %init, %init : i1
  %s0 = llhd.sig "sig0" %init : i1
  %s1 = llhd.sig "sig1" %initArr : !hw.array<4xi1>
}

// CHECK-LABEL:   llvm.func @convert_prb(
// CHECK-SAME:                           %[[VAL_0:.*]]: !llvm.ptr<i8>,
// CHECK-SAME:                           %[[VAL_1:.*]]: !llvm.ptr<struct<()>>,
// CHECK-SAME:                           %[[VAL_2:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>) {
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_4:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_3]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           %[[VAL_5:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_6:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_5]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           %[[VAL_7:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_8:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_9:.*]] = llvm.getelementptr %[[VAL_4]]{{\[}}%[[VAL_7]], %[[VAL_7]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32, i32) -> !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_10:.*]] = llvm.load %[[VAL_9]] : !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_11:.*]] = llvm.getelementptr %[[VAL_4]]{{\[}}%[[VAL_7]], %[[VAL_8]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32, i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_12:.*]] = llvm.load %[[VAL_11]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_13:.*]] = llvm.bitcast %[[VAL_10]] : !llvm.ptr<i8> to !llvm.ptr<i16>
// CHECK:           %[[VAL_14:.*]] = llvm.load %[[VAL_13]] : !llvm.ptr<i16>
// CHECK:           %[[VAL_15:.*]] = llvm.trunc %[[VAL_12]] : i64 to i16
// CHECK:           %[[VAL_16:.*]] = llvm.lshr %[[VAL_14]], %[[VAL_15]] : i16
// CHECK:           %[[VAL_17:.*]] = llvm.trunc %[[VAL_16]] : i16 to i1
// CHECK:           %[[VAL_18:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_19:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_20:.*]] = llvm.getelementptr %[[VAL_6]]{{\[}}%[[VAL_18]], %[[VAL_18]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32, i32) -> !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_21:.*]] = llvm.load %[[VAL_20]] : !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_22:.*]] = llvm.getelementptr %[[VAL_6]]{{\[}}%[[VAL_18]], %[[VAL_19]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32, i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_23:.*]] = llvm.load %[[VAL_22]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_24:.*]] = llvm.bitcast %[[VAL_21]] : !llvm.ptr<i8> to !llvm.ptr<array<3 x i5>>
// CHECK:           %[[VAL_25:.*]] = llvm.load %[[VAL_24]] : !llvm.ptr<array<3 x i5>>
// CHECK:           llvm.return
// CHECK:         }
llhd.entity @convert_prb (%sI1 : !llhd.sig<i1>, %sArr : !llhd.sig<!hw.array<3xi5>>) -> () {
  %p0 = llhd.prb %sI1 : !llhd.sig<i1>
  %p1 = llhd.prb %sArr : !llhd.sig<!hw.array<3xi5>>
}

// CHECK-LABEL:   llvm.func @convert_drv(
// CHECK-SAME:                           %[[VAL_0:.*]]: !llvm.ptr<i8>,
// CHECK-SAME:                           %[[VAL_1:.*]]: !llvm.ptr<struct<()>>,
// CHECK-SAME:                           %[[VAL_2:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>) {
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_4:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_3]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           %[[VAL_5:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_6:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_5]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           %[[VAL_7:.*]] = llvm.mlir.constant(false) : i1
// CHECK:           %[[VAL_8:.*]] = llvm.mlir.constant(0 : i5) : i5
// CHECK:           %[[VAL_9:.*]] = llvm.mlir.undef : !llvm.array<3 x i5>
// CHECK:           %[[VAL_10:.*]] = llvm.insertvalue %[[VAL_8]], %[[VAL_9]][0 : i32] : !llvm.array<3 x i5>
// CHECK:           %[[VAL_11:.*]] = llvm.insertvalue %[[VAL_8]], %[[VAL_10]][1 : i32] : !llvm.array<3 x i5>
// CHECK:           %[[VAL_12:.*]] = llvm.insertvalue %[[VAL_8]], %[[VAL_11]][2 : i32] : !llvm.array<3 x i5>
// CHECK:           %[[VAL_13:.*]] = llvm.mlir.constant(dense<[1000, 0, 0]> : tensor<3xi64>) : !llvm.array<3 x i64>
// CHECK:           %[[VAL_14:.*]] = llvm.mlir.constant(1 : i64) : i64
// CHECK:           %[[VAL_15:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_16:.*]] = llvm.alloca %[[VAL_15]] x i1 {alignment = 4 : i64} : (i32) -> !llvm.ptr<i1>
// CHECK:           llvm.store %[[VAL_7]], %[[VAL_16]] : !llvm.ptr<i1>
// CHECK:           %[[VAL_17:.*]] = llvm.bitcast %[[VAL_16]] : !llvm.ptr<i1> to !llvm.ptr<i8>
// CHECK:           %[[VAL_18:.*]] = llvm.extractvalue %[[VAL_13]][0 : i32] : !llvm.array<3 x i64>
// CHECK:           %[[VAL_19:.*]] = llvm.extractvalue %[[VAL_13]][1 : i32] : !llvm.array<3 x i64>
// CHECK:           %[[VAL_20:.*]] = llvm.extractvalue %[[VAL_13]][2 : i32] : !llvm.array<3 x i64>
// CHECK:           llvm.call @driveSignal(%[[VAL_0]], %[[VAL_4]], %[[VAL_17]], %[[VAL_14]], %[[VAL_18]], %[[VAL_19]], %[[VAL_20]]) : (!llvm.ptr<i8>, !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.ptr<i8>, i64, i64, i64, i64) -> ()
// CHECK:           %[[VAL_22:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_23:.*]] = llvm.mlir.constant(8 : i64) : i64
// CHECK:           %[[VAL_24:.*]] = llvm.mlir.null : !llvm.ptr<array<3 x i5>>
// CHECK:           %[[VAL_25:.*]] = llvm.getelementptr %[[VAL_24]]{{\[}}%[[VAL_22]]] : (!llvm.ptr<array<3 x i5>>, i32) -> !llvm.ptr<array<3 x i5>>
// CHECK:           %[[VAL_26:.*]] = llvm.ptrtoint %[[VAL_25]] : !llvm.ptr<array<3 x i5>> to i64
// CHECK:           %[[VAL_27:.*]] = llvm.mul %[[VAL_26]], %[[VAL_23]] : i64
// CHECK:           %[[VAL_28:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_29:.*]] = llvm.alloca %[[VAL_28]] x !llvm.array<3 x i5> {alignment = 4 : i64} : (i32) -> !llvm.ptr<array<3 x i5>>
// CHECK:           llvm.store %[[VAL_12]], %[[VAL_29]] : !llvm.ptr<array<3 x i5>>
// CHECK:           %[[VAL_30:.*]] = llvm.bitcast %[[VAL_29]] : !llvm.ptr<array<3 x i5>> to !llvm.ptr<i8>
// CHECK:           %[[VAL_31:.*]] = llvm.extractvalue %[[VAL_13]][0 : i32] : !llvm.array<3 x i64>
// CHECK:           %[[VAL_32:.*]] = llvm.extractvalue %[[VAL_13]][1 : i32] : !llvm.array<3 x i64>
// CHECK:           %[[VAL_33:.*]] = llvm.extractvalue %[[VAL_13]][2 : i32] : !llvm.array<3 x i64>
// CHECK:           llvm.call @driveSignal(%[[VAL_0]], %[[VAL_6]], %[[VAL_30]], %[[VAL_27]], %[[VAL_31]], %[[VAL_32]], %[[VAL_33]]) : (!llvm.ptr<i8>, !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.ptr<i8>, i64, i64, i64, i64) -> ()
// CHECK:           llvm.return
// CHECK:         }
llhd.entity @convert_drv (%sI1 : !llhd.sig<i1>, %sArr : !llhd.sig<!hw.array<3xi5>>) -> () {
  %cI1 = hw.constant 0 : i1
  %cI5 = hw.constant 0 : i5
  %cArr = hw.array_create %cI5, %cI5, %cI5 : i5
  %t = llhd.constant_time #llhd.time<1ns, 0d, 0e>
  llhd.drv %sI1, %cI1 after %t : !llhd.sig<i1>
  llhd.drv %sArr, %cArr after %t : !llhd.sig<!hw.array<3xi5>>
}

// CHECK-LABEL:   llvm.func @convert_drv_enable

// CHECK:           %[[VAL_18:.*]] = llvm.mlir.constant(1 : i16) : i1
// CHECK:           %[[VAL_19:.*]] = llvm.icmp "eq" %{{.*}}, %[[VAL_18]] : i1
// CHECK:           llvm.cond_br %[[VAL_19]], ^bb1, ^bb2
// CHECK:         ^bb1:

// CHECK:           llvm.call @driveSignal
// CHECK:           llvm.br ^bb2
// CHECK:         ^bb2:
// CHECK:           llvm.return
// CHECK:         }
llhd.entity @convert_drv_enable (%sI1 : !llhd.sig<i1>) -> () {
    %cI1 = llhd.prb %sI1 : !llhd.sig<i1>
    %t = llhd.constant_time #llhd.time<1ns, 0d, 0e>
    llhd.drv %sI1, %cI1 after %t if %cI1 : !llhd.sig<i1>
}

// CHECK-LABEL:   llvm.func @convert_reg(
// CHECK-SAME:                           %[[VAL_0:.*]]: !llvm.ptr<i8>,
// CHECK-SAME:                           %[[VAL_1:.*]]: !llvm.ptr<struct<(array<3 x i1>)>>,
// CHECK-SAME:                           %[[VAL_2:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>) {
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(dense<[1000, 0, 0]> : tensor<3xi64>) : !llvm.array<3 x i64>
// CHECK:           %[[VAL_4:.*]] = llvm.mlir.constant(false) : i1
// CHECK:           %[[VAL_5:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_6:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_5]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           %[[VAL_7:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_8:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_9:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_10:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_7]], %[[VAL_8]], %[[VAL_9]]] : (!llvm.ptr<struct<(array<3 x i1>)>>, i32, i32, i32) -> !llvm.ptr<i1>
// CHECK:           %[[VAL_11:.*]] = llvm.load %[[VAL_10]] : !llvm.ptr<i1>
// CHECK:           llvm.store %[[VAL_4]], %[[VAL_10]] : !llvm.ptr<i1>
// CHECK:           %[[VAL_12:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_13:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_14:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_15:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_12]], %[[VAL_13]], %[[VAL_14]]] : (!llvm.ptr<struct<(array<3 x i1>)>>, i32, i32, i32) -> !llvm.ptr<i1>
// CHECK:           %[[VAL_16:.*]] = llvm.load %[[VAL_15]] : !llvm.ptr<i1>
// CHECK:           llvm.store %[[VAL_4]], %[[VAL_15]] : !llvm.ptr<i1>
// CHECK:           %[[VAL_17:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_18:.*]] = llvm.mlir.constant(0 : i32) : i32
// CHECK:           %[[VAL_19:.*]] = llvm.mlir.constant(2 : i32) : i32
// CHECK:           %[[VAL_20:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_17]], %[[VAL_18]], %[[VAL_19]]] : (!llvm.ptr<struct<(array<3 x i1>)>>, i32, i32, i32) -> !llvm.ptr<i1>
// CHECK:           %[[VAL_21:.*]] = llvm.load %[[VAL_20]] : !llvm.ptr<i1>
// CHECK:           llvm.store %[[VAL_4]], %[[VAL_20]] : !llvm.ptr<i1>
// CHECK:           llvm.br ^bb1
// CHECK:         ^bb1:
// CHECK:           %[[VAL_22:.*]] = llvm.mlir.constant(true) : i1
// CHECK:           %[[VAL_23:.*]] = llvm.mlir.constant(false) : i1
// CHECK:           %[[VAL_24:.*]] = llvm.icmp "eq" %[[VAL_4]], %[[VAL_23]] : i1
// CHECK:           %[[VAL_25:.*]] = llvm.icmp "ne" %[[VAL_4]], %[[VAL_11]] : i1
// CHECK:           %[[VAL_26:.*]] = llvm.and %[[VAL_24]], %[[VAL_25]] : i1
// CHECK:           llvm.cond_br %[[VAL_26]], ^bb6(%[[VAL_4]], %[[VAL_3]], %[[VAL_22]] : i1, !llvm.array<3 x i64>, i1), ^bb2
// CHECK:         ^bb2:
// CHECK:           %[[VAL_27:.*]] = llvm.mlir.constant(true) : i1
// CHECK:           %[[VAL_28:.*]] = llvm.mlir.constant(true) : i1
// CHECK:           %[[VAL_29:.*]] = llvm.icmp "eq" %[[VAL_4]], %[[VAL_28]] : i1
// CHECK:           %[[VAL_30:.*]] = llvm.icmp "ne" %[[VAL_4]], %[[VAL_16]] : i1
// CHECK:           %[[VAL_31:.*]] = llvm.and %[[VAL_29]], %[[VAL_30]] : i1
// CHECK:           llvm.cond_br %[[VAL_31]], ^bb6(%[[VAL_4]], %[[VAL_3]], %[[VAL_27]] : i1, !llvm.array<3 x i64>, i1), ^bb3
// CHECK:         ^bb3:
// CHECK:           %[[VAL_32:.*]] = llvm.mlir.constant(true) : i1
// CHECK:           %[[VAL_33:.*]] = llvm.mlir.constant(false) : i1
// CHECK:           %[[VAL_34:.*]] = llvm.icmp "eq" %[[VAL_4]], %[[VAL_33]] : i1
// CHECK:           llvm.cond_br %[[VAL_34]], ^bb6(%[[VAL_4]], %[[VAL_3]], %[[VAL_32]] : i1, !llvm.array<3 x i64>, i1), ^bb4
// CHECK:         ^bb4:
// CHECK:           %[[VAL_35:.*]] = llvm.mlir.constant(true) : i1
// CHECK:           %[[VAL_36:.*]] = llvm.mlir.constant(true) : i1
// CHECK:           %[[VAL_37:.*]] = llvm.icmp "eq" %[[VAL_4]], %[[VAL_36]] : i1
// CHECK:           llvm.cond_br %[[VAL_37]], ^bb6(%[[VAL_4]], %[[VAL_3]], %[[VAL_35]] : i1, !llvm.array<3 x i64>, i1), ^bb5
// CHECK:         ^bb5:
// CHECK:           %[[VAL_38:.*]] = llvm.mlir.constant(true) : i1
// CHECK:           %[[VAL_39:.*]] = llvm.icmp "ne" %[[VAL_4]], %[[VAL_21]] : i1
// CHECK:           llvm.cond_br %[[VAL_39]], ^bb6(%[[VAL_4]], %[[VAL_3]], %[[VAL_38]] : i1, !llvm.array<3 x i64>, i1), ^bb9
// CHECK:         ^bb6(%[[VAL_40:.*]]: i1, %[[VAL_41:.*]]: !llvm.array<3 x i64>, %[[VAL_42:.*]]: i1):
// CHECK:           %[[VAL_43:.*]] = llvm.mlir.constant(1 : i64) : i64
// CHECK:           %[[VAL_44:.*]] = llvm.mlir.constant(1 : i16) : i1
// CHECK:           %[[VAL_45:.*]] = llvm.icmp "eq" %[[VAL_42]], %[[VAL_44]] : i1
// CHECK:           llvm.cond_br %[[VAL_45]], ^bb7, ^bb8
// CHECK:         ^bb7:
// CHECK:           %[[VAL_46:.*]] = llvm.mlir.constant(1 : i32) : i32
// CHECK:           %[[VAL_47:.*]] = llvm.alloca %[[VAL_46]] x i1 {alignment = 4 : i64} : (i32) -> !llvm.ptr<i1>
// CHECK:           llvm.store %[[VAL_40]], %[[VAL_47]] : !llvm.ptr<i1>
// CHECK:           %[[VAL_48:.*]] = llvm.bitcast %[[VAL_47]] : !llvm.ptr<i1> to !llvm.ptr<i8>
// CHECK:           %[[VAL_49:.*]] = llvm.extractvalue %[[VAL_41]][0 : i32] : !llvm.array<3 x i64>
// CHECK:           %[[VAL_50:.*]] = llvm.extractvalue %[[VAL_41]][1 : i32] : !llvm.array<3 x i64>
// CHECK:           %[[VAL_51:.*]] = llvm.extractvalue %[[VAL_41]][2 : i32] : !llvm.array<3 x i64>
// CHECK:           llvm.call @driveSignal(%[[VAL_0]], %[[VAL_6]], %[[VAL_48]], %[[VAL_43]], %[[VAL_49]], %[[VAL_50]], %[[VAL_51]]) : (!llvm.ptr<i8>, !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.ptr<i8>, i64, i64, i64, i64) -> ()
// CHECK:           llvm.br ^bb8
// CHECK:         ^bb8:
// CHECK:           llvm.br ^bb9
// CHECK:         ^bb9:
// CHECK:           llvm.return
// CHECK:         }
llhd.entity @convert_reg () -> () {
  %0 = llhd.constant_time #llhd.time<1ns, 0d, 0e>
  %1 = hw.constant 0 : i1
  %2 = llhd.sig "sig" %1: i1
  llhd.reg %2, (%1, "fall" %1 after %0 : i1), (%1, "rise" %1 after %0 : i1), (%1, "low" %1 after %0 : i1), (%1, "high" %1 after %0 : i1), (%1, "both" %1 after %0 : i1) : !llhd.sig<i1>
}
