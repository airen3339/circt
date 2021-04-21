// RUN: circt-opt %s -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck %s

module {
  rtl.module @B(%a: i1) -> (%nameOfPortInSV: i1, i1) {
    %0 = rtl.or %a, %a : i1
    %1 = rtl.and %a, %a : i1
    rtl.output %0, %1: i1, i1
  }

  // CHECK-LABEL: rtl.module @B(%a: i1) -> (%nameOfPortInSV: i1, i1)
  // CHECK-NEXT:    %0 = rtl.or %a, %a : i1
  // CHECK-NEXT:    %1 = rtl.and %a, %a : i1
  // CHECK-NEXT:    rtl.output %0, %1 : i1, i1

  rtl.externmodule @C(%a: i1 {rtl.name = "nameOfPortInSV"}) -> (i1, i1)
  // CHECK-LABEL: rtl.externmodule @C(i1 {rtl.name = "nameOfPortInSV"}) -> (i1, i1)
  // CHECK-NOT: {

  rtl.externmodule @explicitResultName() -> (%x: i1 {rtl.name="FOO"})
  // CHECK-LABEL: rtl.externmodule @explicitResultName() -> (%FOO: i1)

  rtl.externmodule @D_ATTR(%a: i1) -> (i1, i1) attributes {filename = "test.v", parameters = {DEFAULT = 0 : i64}}

  // CHECK-LABEL: rtl.externmodule @D_ATTR(i1 {rtl.name = "a"}) -> (i1, i1) attributes {filename = "test.v", parameters = {DEFAULT = 0 : i64}}
  // CHECK-NOT: {

  rtl.module @A(%d: i1, %e: !rtl.inout<i1>) -> (i1, i1) {
    // Instantiate @B as a RTL module with result-as-output sementics
    %r1, %r2 = rtl.instance "b1" @B(%d) : (i1) -> (i1, i1)
    // Instantiate @C
    %f, %g = rtl.instance "c1" @C(%d) : (i1) -> (i1, i1)
    // Connect the inout port with %f
    rtl.connect %e, %f : i1
    // Output values
    rtl.output %g, %r1 : i1, i1
  }
  // CHECK-LABEL: rtl.module @A(%d: i1, %e: !rtl.inout<i1>) -> (i1, i1)
  // CHECK-NEXT:  %b1.nameOfPortInSV, %b1.1 = rtl.instance "b1" @B(%d) : (i1) -> (i1, i1)
  // CHECK-NEXT:  %c1.0, %c1.1 = rtl.instance "c1" @C(%d) : (i1) -> (i1, i1)

  rtl.module @AnyType1(%a: vector< 3 x i8 >) { }
  // CHECK-LABEL: rtl.module @AnyType1(%a: vector<3xi8>)
  
  // CHECK-LABEL: rtl.module @AnyTypeInstance()
  rtl.module @AnyTypeInstance() {
    %vec = constant dense <0> : vector<3xi8>
    rtl.instance "anyType1" @AnyType1(%vec) : (vector<3xi8>) -> ()
  }

  // CHECK:       %cst = constant dense<0> : vector<3xi8>
  // CHECK-NEXT:  rtl.instance "anyType1" @AnyType1(%cst) : (vector<3xi8>) -> ()
}
