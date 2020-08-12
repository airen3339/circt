// NOTE: Assertions have been autogenerated by utils/generate-test-checks.py
// RUN: circt-opt %s --convert-llhd-to-llvm --split-input-file | FileCheck %s

// CHECK-LABEL:   llvm.func @convert_extract_slice(
// CHECK-SAME:                                     %[[VAL_0:.*]]: !llvm.i32,
// CHECK-SAME:                                     %[[VAL_1:.*]]: !llvm.i100,
// CHECK-SAME:                                     %[[VAL_2:.*]]: !llvm.array<4 x i5>) {
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(0 : index) : !llvm.i64
// CHECK:           %[[VAL_4:.*]] = llvm.trunc %[[VAL_3]] : !llvm.i64 to !llvm.i32
// CHECK:           %[[VAL_5:.*]] = llvm.lshr %[[VAL_0]], %[[VAL_4]] : !llvm.i32
// CHECK:           %[[VAL_6:.*]] = llvm.trunc %[[VAL_5]] : !llvm.i32 to !llvm.i10
// CHECK:           %[[VAL_7:.*]] = llvm.mlir.constant(0 : index) : !llvm.i64
// CHECK:           %[[VAL_8:.*]] = llvm.zext %[[VAL_7]] : !llvm.i64 to !llvm.i100
// CHECK:           %[[VAL_9:.*]] = llvm.lshr %[[VAL_1]], %[[VAL_8]] : !llvm.i100
// CHECK:           %[[VAL_10:.*]] = llvm.trunc %[[VAL_9]] : !llvm.i100 to !llvm.i10
// CHECK:           %[[VAL_11:.*]] = llvm.mlir.constant(1 : index) : !llvm.i64
// CHECK:           %[[VAL_12:.*]] = llvm.mlir.undef : !llvm.array<2 x i5>
// CHECK:           %[[VAL_13:.*]] = llvm.extractvalue %[[VAL_2]][1 : i32] : !llvm.array<4 x i5>
// CHECK:           %[[VAL_14:.*]] = llvm.insertvalue %[[VAL_13]], %[[VAL_12]][0 : i32] : !llvm.array<2 x i5>
// CHECK:           %[[VAL_15:.*]] = llvm.extractvalue %[[VAL_2]][2 : i32] : !llvm.array<4 x i5>
// CHECK:           %[[VAL_16:.*]] = llvm.insertvalue %[[VAL_15]], %[[VAL_14]][1 : i32] : !llvm.array<2 x i5>
// CHECK:           llvm.return
// CHECK:         }
func @convert_extract_slice(%cI32 : i32, %cI100 : i100, %arr : !llhd.array<4xi5>) {
  %0 = llhd.extract_slice %cI32, 0 : i32 -> i10
  %1 = llhd.extract_slice %cI100, 0 : i100 -> i10
  %2 = llhd.extract_slice %arr, 1 : !llhd.array<4xi5> -> !llhd.array<2xi5>

  return
}

// CHECK-LABEL:   llvm.func @convert_extract_slice_sig(
// CHECK-SAME:                                         %[[VAL_0:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>,
// CHECK-SAME:                                         %[[VAL_1:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>) {
// CHECK:           %[[VAL_2:.*]] = llvm.mlir.constant(0 : index) : !llvm.i64
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_4:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_5:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_3]], %[[VAL_3]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_6:.*]] = llvm.load %[[VAL_5]] : !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_7:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_3]], %[[VAL_4]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_8:.*]] = llvm.load %[[VAL_7]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_9:.*]] = llvm.mlir.constant(2 : i32) : !llvm.i32
// CHECK:           %[[VAL_10:.*]] = llvm.mlir.constant(3 : i32) : !llvm.i32
// CHECK:           %[[VAL_11:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_3]], %[[VAL_9]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_12:.*]] = llvm.load %[[VAL_11]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_13:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_3]], %[[VAL_10]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_14:.*]] = llvm.load %[[VAL_13]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_15:.*]] = llvm.add %[[VAL_8]], %[[VAL_2]] : !llvm.i64
// CHECK:           %[[VAL_16:.*]] = llvm.ptrtoint %[[VAL_6]] : !llvm.ptr<i8> to !llvm.i64
// CHECK:           %[[VAL_17:.*]] = llvm.mlir.constant(8 : i64) : !llvm.i64
// CHECK:           %[[VAL_18:.*]] = llvm.udiv %[[VAL_15]], %[[VAL_17]] : !llvm.i64
// CHECK:           %[[VAL_19:.*]] = llvm.add %[[VAL_16]], %[[VAL_18]] : !llvm.i64
// CHECK:           %[[VAL_20:.*]] = llvm.inttoptr %[[VAL_19]] : !llvm.i64 to !llvm.ptr<i8>
// CHECK:           %[[VAL_21:.*]] = llvm.urem %[[VAL_15]], %[[VAL_17]] : !llvm.i64
// CHECK:           %[[VAL_22:.*]] = llvm.mlir.undef : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_23:.*]] = llvm.insertvalue %[[VAL_20]], %[[VAL_22]][0 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_24:.*]] = llvm.insertvalue %[[VAL_21]], %[[VAL_23]][1 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_25:.*]] = llvm.insertvalue %[[VAL_12]], %[[VAL_24]][2 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_26:.*]] = llvm.insertvalue %[[VAL_14]], %[[VAL_25]][3 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_27:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_28:.*]] = llvm.alloca %[[VAL_27]] x !llvm.struct<(ptr<i8>, i64, i64, i64)> {alignment = 4 : i64} : (!llvm.i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.store %[[VAL_26]], %[[VAL_28]] : !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           %[[VAL_29:.*]] = llvm.mlir.constant(0 : index) : !llvm.i64
// CHECK:           %[[VAL_30:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_31:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_32:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_30]], %[[VAL_30]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_33:.*]] = llvm.load %[[VAL_32]] : !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_34:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_30]], %[[VAL_31]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_35:.*]] = llvm.load %[[VAL_34]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_36:.*]] = llvm.mlir.constant(2 : i32) : !llvm.i32
// CHECK:           %[[VAL_37:.*]] = llvm.mlir.constant(3 : i32) : !llvm.i32
// CHECK:           %[[VAL_38:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_30]], %[[VAL_36]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_39:.*]] = llvm.load %[[VAL_38]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_40:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_30]], %[[VAL_37]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_41:.*]] = llvm.load %[[VAL_40]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_42:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_43:.*]] = llvm.zext %[[VAL_29]] : !llvm.i64 to !llvm.i65
// CHECK:           %[[VAL_44:.*]] = llvm.bitcast %[[VAL_33]] : !llvm.ptr<i8> to !llvm.ptr<array<2 x i4>>
// CHECK:           %[[VAL_45:.*]] = llvm.getelementptr %[[VAL_44]]{{\[}}%[[VAL_42]], %[[VAL_43]]] : (!llvm.ptr<array<2 x i4>>, !llvm.i32, !llvm.i65) -> !llvm.ptr<i4>
// CHECK:           %[[VAL_46:.*]] = llvm.bitcast %[[VAL_45]] : !llvm.ptr<i4> to !llvm.ptr<i8>
// CHECK:           %[[VAL_47:.*]] = llvm.mlir.undef : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_48:.*]] = llvm.insertvalue %[[VAL_46]], %[[VAL_47]][0 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_49:.*]] = llvm.insertvalue %[[VAL_35]], %[[VAL_48]][1 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_50:.*]] = llvm.insertvalue %[[VAL_39]], %[[VAL_49]][2 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_51:.*]] = llvm.insertvalue %[[VAL_41]], %[[VAL_50]][3 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_52:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_53:.*]] = llvm.alloca %[[VAL_52]] x !llvm.struct<(ptr<i8>, i64, i64, i64)> {alignment = 4 : i64} : (!llvm.i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.store %[[VAL_51]], %[[VAL_53]] : !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.return
// CHECK:         }
func @convert_extract_slice_sig (%sI32 : !llhd.sig<i32>, %sArr : !llhd.sig<!llhd.array<4xi4>>) {
  %0 = llhd.extract_slice %sI32, 0 : !llhd.sig<i32> -> !llhd.sig<i10>
  %1 = llhd.extract_slice %sArr, 0 : !llhd.sig<!llhd.array<4xi4>> -> !llhd.sig<!llhd.array<2xi4>>

  return
}

// CHECK-LABEL:   llvm.func @convert_dyn_extract_slice(
// CHECK-SAME:                                         %[[VAL_0:.*]]: !llvm.i32,
// CHECK-SAME:                                         %[[VAL_1:.*]]: !llvm.i100,
// CHECK-SAME:                                         %[[VAL_2:.*]]: !llvm.array<4 x i5>) {
// CHECK:           %[[VAL_3:.*]] = llvm.lshr %[[VAL_0]], %[[VAL_0]] : !llvm.i32
// CHECK:           %[[VAL_4:.*]] = llvm.trunc %[[VAL_3]] : !llvm.i32 to !llvm.i10
// CHECK:           %[[VAL_5:.*]] = llvm.zext %[[VAL_0]] : !llvm.i32 to !llvm.i100
// CHECK:           %[[VAL_6:.*]] = llvm.lshr %[[VAL_1]], %[[VAL_5]] : !llvm.i100
// CHECK:           %[[VAL_7:.*]] = llvm.trunc %[[VAL_6]] : !llvm.i100 to !llvm.i10
// CHECK:           %[[VAL_8:.*]] = llvm.mlir.constant(0 : i64) : !llvm.i64
// CHECK:           %[[VAL_9:.*]] = llvm.mlir.constant(1 : i64) : !llvm.i64
// CHECK:           %[[VAL_10:.*]] = llvm.zext %[[VAL_0]] : !llvm.i32 to !llvm.i33
// CHECK:           %[[VAL_11:.*]] = llvm.alloca %[[VAL_9]] x !llvm.array<4 x i5> : (!llvm.i64) -> !llvm.ptr<array<4 x i5>>
// CHECK:           llvm.store %[[VAL_2]], %[[VAL_11]] : !llvm.ptr<array<4 x i5>>
// CHECK:           %[[VAL_12:.*]] = llvm.mlir.undef : !llvm.array<2 x i5>
// CHECK:           %[[VAL_13:.*]] = llvm.mlir.constant(0 : i64) : !llvm.i33
// CHECK:           %[[VAL_14:.*]] = llvm.add %[[VAL_13]], %[[VAL_10]] : !llvm.i33
// CHECK:           %[[VAL_15:.*]] = llvm.getelementptr %[[VAL_11]]{{\[}}%[[VAL_8]], %[[VAL_14]]] : (!llvm.ptr<array<4 x i5>>, !llvm.i64, !llvm.i33) -> !llvm.ptr<i5>
// CHECK:           %[[VAL_16:.*]] = llvm.load %[[VAL_15]] : !llvm.ptr<i5>
// CHECK:           %[[VAL_17:.*]] = llvm.insertvalue %[[VAL_16]], %[[VAL_12]][0 : i32] : !llvm.array<2 x i5>
// CHECK:           %[[VAL_18:.*]] = llvm.mlir.constant(1 : i64) : !llvm.i33
// CHECK:           %[[VAL_19:.*]] = llvm.add %[[VAL_18]], %[[VAL_10]] : !llvm.i33
// CHECK:           %[[VAL_20:.*]] = llvm.getelementptr %[[VAL_11]]{{\[}}%[[VAL_8]], %[[VAL_19]]] : (!llvm.ptr<array<4 x i5>>, !llvm.i64, !llvm.i33) -> !llvm.ptr<i5>
// CHECK:           %[[VAL_21:.*]] = llvm.load %[[VAL_20]] : !llvm.ptr<i5>
// CHECK:           %[[VAL_22:.*]] = llvm.insertvalue %[[VAL_21]], %[[VAL_17]][1 : i32] : !llvm.array<2 x i5>
// CHECK:           llvm.return
// CHECK:         }
func @convert_dyn_extract_slice(%cI32 : i32, %cI100 : i100, %arr : !llhd.array<4xi5>) {
  %0 = llhd.dyn_extract_slice %cI32, %cI32 : (i32, i32) -> i10
  %1 = llhd.dyn_extract_slice %cI100, %cI32 : (i100, i32) -> i10
  %2 = llhd.dyn_extract_slice %arr, %cI32 : (!llhd.array<4xi5>, i32) -> !llhd.array<2xi5>

  return
}

// CHECK-LABEL:   llvm.func @convert_dyn_extract_slice_sig(
// CHECK-SAME:                                             %[[VAL_0:.*]]: !llvm.i32,
// CHECK-SAME:                                             %[[VAL_1:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>,
// CHECK-SAME:                                             %[[VAL_2:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>) {
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_4:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_5:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_3]], %[[VAL_3]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_6:.*]] = llvm.load %[[VAL_5]] : !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_7:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_3]], %[[VAL_4]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_8:.*]] = llvm.load %[[VAL_7]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_9:.*]] = llvm.mlir.constant(2 : i32) : !llvm.i32
// CHECK:           %[[VAL_10:.*]] = llvm.mlir.constant(3 : i32) : !llvm.i32
// CHECK:           %[[VAL_11:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_3]], %[[VAL_9]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_12:.*]] = llvm.load %[[VAL_11]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_13:.*]] = llvm.getelementptr %[[VAL_1]]{{\[}}%[[VAL_3]], %[[VAL_10]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_14:.*]] = llvm.load %[[VAL_13]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_15:.*]] = llvm.zext %[[VAL_0]] : !llvm.i32 to !llvm.i64
// CHECK:           %[[VAL_16:.*]] = llvm.add %[[VAL_8]], %[[VAL_15]] : !llvm.i64
// CHECK:           %[[VAL_17:.*]] = llvm.ptrtoint %[[VAL_6]] : !llvm.ptr<i8> to !llvm.i64
// CHECK:           %[[VAL_18:.*]] = llvm.mlir.constant(8 : i64) : !llvm.i64
// CHECK:           %[[VAL_19:.*]] = llvm.udiv %[[VAL_16]], %[[VAL_18]] : !llvm.i64
// CHECK:           %[[VAL_20:.*]] = llvm.add %[[VAL_17]], %[[VAL_19]] : !llvm.i64
// CHECK:           %[[VAL_21:.*]] = llvm.inttoptr %[[VAL_20]] : !llvm.i64 to !llvm.ptr<i8>
// CHECK:           %[[VAL_22:.*]] = llvm.urem %[[VAL_16]], %[[VAL_18]] : !llvm.i64
// CHECK:           %[[VAL_23:.*]] = llvm.mlir.undef : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_24:.*]] = llvm.insertvalue %[[VAL_21]], %[[VAL_23]][0 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_25:.*]] = llvm.insertvalue %[[VAL_22]], %[[VAL_24]][1 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_26:.*]] = llvm.insertvalue %[[VAL_12]], %[[VAL_25]][2 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_27:.*]] = llvm.insertvalue %[[VAL_14]], %[[VAL_26]][3 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_28:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_29:.*]] = llvm.alloca %[[VAL_28]] x !llvm.struct<(ptr<i8>, i64, i64, i64)> {alignment = 4 : i64} : (!llvm.i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.store %[[VAL_27]], %[[VAL_29]] : !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           %[[VAL_30:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_31:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_32:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_30]], %[[VAL_30]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_33:.*]] = llvm.load %[[VAL_32]] : !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_34:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_30]], %[[VAL_31]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_35:.*]] = llvm.load %[[VAL_34]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_36:.*]] = llvm.mlir.constant(2 : i32) : !llvm.i32
// CHECK:           %[[VAL_37:.*]] = llvm.mlir.constant(3 : i32) : !llvm.i32
// CHECK:           %[[VAL_38:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_30]], %[[VAL_36]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_39:.*]] = llvm.load %[[VAL_38]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_40:.*]] = llvm.getelementptr %[[VAL_2]]{{\[}}%[[VAL_30]], %[[VAL_37]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_41:.*]] = llvm.load %[[VAL_40]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_42:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_43:.*]] = llvm.zext %[[VAL_0]] : !llvm.i32 to !llvm.i33
// CHECK:           %[[VAL_44:.*]] = llvm.bitcast %[[VAL_33]] : !llvm.ptr<i8> to !llvm.ptr<array<2 x i4>>
// CHECK:           %[[VAL_45:.*]] = llvm.getelementptr %[[VAL_44]]{{\[}}%[[VAL_42]], %[[VAL_43]]] : (!llvm.ptr<array<2 x i4>>, !llvm.i32, !llvm.i33) -> !llvm.ptr<i4>
// CHECK:           %[[VAL_46:.*]] = llvm.bitcast %[[VAL_45]] : !llvm.ptr<i4> to !llvm.ptr<i8>
// CHECK:           %[[VAL_47:.*]] = llvm.mlir.undef : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_48:.*]] = llvm.insertvalue %[[VAL_46]], %[[VAL_47]][0 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_49:.*]] = llvm.insertvalue %[[VAL_35]], %[[VAL_48]][1 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_50:.*]] = llvm.insertvalue %[[VAL_39]], %[[VAL_49]][2 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_51:.*]] = llvm.insertvalue %[[VAL_41]], %[[VAL_50]][3 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_52:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_53:.*]] = llvm.alloca %[[VAL_52]] x !llvm.struct<(ptr<i8>, i64, i64, i64)> {alignment = 4 : i64} : (!llvm.i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.store %[[VAL_51]], %[[VAL_53]] : !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.return
// CHECK:         }
func @convert_dyn_extract_slice_sig (%c : i32, %sI32 : !llhd.sig<i32>, %sArr : !llhd.sig<!llhd.array<4xi4>>) {
  %0 = llhd.dyn_extract_slice %sI32, %c : (!llhd.sig<i32>, i32) -> !llhd.sig<i10>
  %1 = llhd.dyn_extract_slice %sArr, %c : (!llhd.sig<!llhd.array<4xi4>>, i32) -> !llhd.sig<!llhd.array<2xi4>>

  return
}

// CHECK-LABEL:   llvm.func @convert_extract_element(
// CHECK-SAME:                                       %[[VAL_0:.*]]: !llvm.array<4 x i5>) {
// CHECK:           %[[VAL_1:.*]] = llvm.extractvalue %[[VAL_0]][1 : index] : !llvm.array<4 x i5>
// CHECK:           llvm.return
// CHECK:         }
func @convert_extract_element(%arr : !llhd.array<4xi5>) {
  %2 = llhd.extract_element %arr, 1 : !llhd.array<4xi5> -> i5

  return
}

// CHECK-LABEL:   llvm.func @convert_extract_element_sig(
// CHECK-SAME:                                           %[[VAL_0:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>) {
// CHECK:           %[[VAL_1:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_2:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_3:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_1]], %[[VAL_1]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_4:.*]] = llvm.load %[[VAL_3]] : !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_5:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_1]], %[[VAL_2]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_6:.*]] = llvm.load %[[VAL_5]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_7:.*]] = llvm.mlir.constant(2 : i32) : !llvm.i32
// CHECK:           %[[VAL_8:.*]] = llvm.mlir.constant(3 : i32) : !llvm.i32
// CHECK:           %[[VAL_9:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_1]], %[[VAL_7]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_10:.*]] = llvm.load %[[VAL_9]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_11:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_1]], %[[VAL_8]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_12:.*]] = llvm.load %[[VAL_11]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_13:.*]] = llvm.mlir.constant(0 : index) : !llvm.i64
// CHECK:           %[[VAL_14:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_15:.*]] = llvm.zext %[[VAL_13]] : !llvm.i64 to !llvm.i65
// CHECK:           %[[VAL_16:.*]] = llvm.bitcast %[[VAL_4]] : !llvm.ptr<i8> to !llvm.ptr<array<4 x i4>>
// CHECK:           %[[VAL_17:.*]] = llvm.getelementptr %[[VAL_16]]{{\[}}%[[VAL_14]], %[[VAL_15]]] : (!llvm.ptr<array<4 x i4>>, !llvm.i32, !llvm.i65) -> !llvm.ptr<i4>
// CHECK:           %[[VAL_18:.*]] = llvm.bitcast %[[VAL_17]] : !llvm.ptr<i4> to !llvm.ptr<i8>
// CHECK:           %[[VAL_19:.*]] = llvm.mlir.undef : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_20:.*]] = llvm.insertvalue %[[VAL_18]], %[[VAL_19]][0 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_21:.*]] = llvm.insertvalue %[[VAL_6]], %[[VAL_20]][1 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_22:.*]] = llvm.insertvalue %[[VAL_10]], %[[VAL_21]][2 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_23:.*]] = llvm.insertvalue %[[VAL_12]], %[[VAL_22]][3 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_24:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_25:.*]] = llvm.alloca %[[VAL_24]] x !llvm.struct<(ptr<i8>, i64, i64, i64)> {alignment = 4 : i64} : (!llvm.i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.store %[[VAL_23]], %[[VAL_25]] : !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.return
// CHECK:         }
func @convert_extract_element_sig (%sArr : !llhd.sig<!llhd.array<4xi4>>) {
  %1 = llhd.extract_element %sArr, 0 : !llhd.sig<!llhd.array<4xi4>> -> !llhd.sig<i4>

  return
}

// CHECK-LABEL:   llvm.func @convert_dyn_extract_element(
// CHECK-SAME:                                           %[[VAL_0:.*]]: !llvm.array<4 x i5>,
// CHECK-SAME:                                           %[[VAL_1:.*]]: !llvm.i32) {
// CHECK:           %[[VAL_2:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_4:.*]] = llvm.alloca %[[VAL_3]] x !llvm.array<4 x i5> {alignment = 4 : i64} : (!llvm.i32) -> !llvm.ptr<array<4 x i5>>
// CHECK:           llvm.store %[[VAL_0]], %[[VAL_4]] : !llvm.ptr<array<4 x i5>>
// CHECK:           %[[VAL_5:.*]] = llvm.zext %[[VAL_1]] : !llvm.i32 to !llvm.i33
// CHECK:           %[[VAL_6:.*]] = llvm.getelementptr %[[VAL_4]]{{\[}}%[[VAL_2]], %[[VAL_5]]] : (!llvm.ptr<array<4 x i5>>, !llvm.i32, !llvm.i33) -> !llvm.ptr<i5>
// CHECK:           %[[VAL_7:.*]] = llvm.load %[[VAL_6]] : !llvm.ptr<i5>
// CHECK:           llvm.return
// CHECK:         }
func @convert_dyn_extract_element(%arr : !llhd.array<4xi5>, %c : i32) {
  %2 = llhd.dyn_extract_element %arr, %c : (!llhd.array<4xi5>, i32) -> i5

  return
}

// CHECK-LABEL:   llvm.func @convert_dyn_extract_element_sig(
// CHECK-SAME:                                               %[[VAL_0:.*]]: !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>,
// CHECK-SAME:                                               %[[VAL_1:.*]]: !llvm.i32) {
// CHECK:           %[[VAL_2:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_3:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_4:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_2]], %[[VAL_2]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_5:.*]] = llvm.load %[[VAL_4]] : !llvm.ptr<ptr<i8>>
// CHECK:           %[[VAL_6:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_2]], %[[VAL_3]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_7:.*]] = llvm.load %[[VAL_6]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_8:.*]] = llvm.mlir.constant(2 : i32) : !llvm.i32
// CHECK:           %[[VAL_9:.*]] = llvm.mlir.constant(3 : i32) : !llvm.i32
// CHECK:           %[[VAL_10:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_2]], %[[VAL_8]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_11:.*]] = llvm.load %[[VAL_10]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_12:.*]] = llvm.getelementptr %[[VAL_0]]{{\[}}%[[VAL_2]], %[[VAL_9]]] : (!llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>, !llvm.i32, !llvm.i32) -> !llvm.ptr<i64>
// CHECK:           %[[VAL_13:.*]] = llvm.load %[[VAL_12]] : !llvm.ptr<i64>
// CHECK:           %[[VAL_14:.*]] = llvm.mlir.constant(0 : i32) : !llvm.i32
// CHECK:           %[[VAL_15:.*]] = llvm.zext %[[VAL_1]] : !llvm.i32 to !llvm.i33
// CHECK:           %[[VAL_16:.*]] = llvm.bitcast %[[VAL_5]] : !llvm.ptr<i8> to !llvm.ptr<array<4 x i4>>
// CHECK:           %[[VAL_17:.*]] = llvm.getelementptr %[[VAL_16]]{{\[}}%[[VAL_14]], %[[VAL_15]]] : (!llvm.ptr<array<4 x i4>>, !llvm.i32, !llvm.i33) -> !llvm.ptr<i4>
// CHECK:           %[[VAL_18:.*]] = llvm.bitcast %[[VAL_17]] : !llvm.ptr<i4> to !llvm.ptr<i8>
// CHECK:           %[[VAL_19:.*]] = llvm.mlir.undef : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_20:.*]] = llvm.insertvalue %[[VAL_18]], %[[VAL_19]][0 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_21:.*]] = llvm.insertvalue %[[VAL_7]], %[[VAL_20]][1 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_22:.*]] = llvm.insertvalue %[[VAL_11]], %[[VAL_21]][2 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_23:.*]] = llvm.insertvalue %[[VAL_13]], %[[VAL_22]][3 : i32] : !llvm.struct<(ptr<i8>, i64, i64, i64)>
// CHECK:           %[[VAL_24:.*]] = llvm.mlir.constant(1 : i32) : !llvm.i32
// CHECK:           %[[VAL_25:.*]] = llvm.alloca %[[VAL_24]] x !llvm.struct<(ptr<i8>, i64, i64, i64)> {alignment = 4 : i64} : (!llvm.i32) -> !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.store %[[VAL_23]], %[[VAL_25]] : !llvm.ptr<struct<(ptr<i8>, i64, i64, i64)>>
// CHECK:           llvm.return
// CHECK:         }
func @convert_dyn_extract_element_sig(%sArr : !llhd.sig<!llhd.array<4xi4>>, %c : i32) {
  %1 = llhd.dyn_extract_element %sArr, %c : (!llhd.sig<!llhd.array<4xi4>>, i32) -> !llhd.sig<i4>

  return
}