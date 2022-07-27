// NOTE: Assertions have been autogenerated by utils/generate-test-checks.py
// RUN: circt-opt %s --convert-comb-to-llvm | FileCheck %s

// CHECK-LABEL:   @convertArithmetic
func.func @convertArithmetic(%arg0: i32, %arg1: i32, %arg2: i32) -> i32 {
    // CHECK: %[[R0:.*]] = llvm.add %arg0, %arg1 : i32
    // CHECK: %[[R1:.*]] = llvm.add %[[R0]], %arg2 : i32
    %0 = comb.add %arg0, %arg1, %arg2 : i32
    %1 = comb.add %0 : i32

    // CHECK: %[[R2:.*]] = llvm.mul %arg0, %arg1 : i32
    // CHECK: %[[R3:.*]] = llvm.mul %[[R2]], %arg2 : i32
    %2 = comb.mul %arg0, %arg1, %arg2 : i32
    %3 = comb.mul %2 : i32

    // CHECK: %[[R4:.*]] = llvm.udiv %[[R1]], %[[R3]] : i32
    %4 = comb.divu %1, %3 : i32
    // CHECK: %[[R5:.*]] = llvm.sdiv %arg0, %[[R4]] : i32
    %5 = comb.divs %arg0, %4 : i32
    // CHECK: %[[R6:.*]] = llvm.urem %arg0, %[[R5]] : i32
    %6 = comb.modu %arg0, %5 : i32
    // CHECK: %[[R7:.*]] = llvm.srem %arg0, %[[R6]] : i32
    %7 = comb.mods %arg0, %6 : i32
    // CHECK: %[[R8:.*]] = llvm.sub %arg0, %[[R7]] : i32
    %8 = comb.sub %arg0, %7 : i32

    return %8 : i32
}

// CHECK-LABEL:   @convertRelational
func.func @convertRelational(%arg0: i32, %arg1: i32) {
    // CHECK: llvm.icmp "eq" %arg0, %arg1 : i32
    %0 = comb.icmp eq %arg0, %arg1 : i32
    // CHECK: llvm.icmp "ne" %arg0, %arg1 : i32
    %1 = comb.icmp ne %arg0, %arg1 : i32
    // CHECK: llvm.icmp "slt" %arg0, %arg1 : i32
    %2 = comb.icmp slt %arg0, %arg1 : i32
    // CHECK: llvm.icmp "sle" %arg0, %arg1 : i32
    %3 = comb.icmp sle %arg0, %arg1 : i32
    // CHECK: llvm.icmp "sgt" %arg0, %arg1 : i32
    %4 = comb.icmp sgt %arg0, %arg1 : i32
    // CHECK: llvm.icmp "sge" %arg0, %arg1 : i32
    %5 = comb.icmp sge %arg0, %arg1 : i32
    // CHECK: llvm.icmp "ult" %arg0, %arg1 : i32
    %6 = comb.icmp ult %arg0, %arg1 : i32
    // CHECK: llvm.icmp "ule" %arg0, %arg1 : i32
    %7 = comb.icmp ule %arg0, %arg1 : i32
    // CHECK: llvm.icmp "ugt" %arg0, %arg1 : i32
    %8 = comb.icmp ugt %arg0, %arg1 : i32
    // CHECK: llvm.icmp "uge" %arg0, %arg1 : i32
    %9 = comb.icmp uge %arg0, %arg1 : i32

    return
}
