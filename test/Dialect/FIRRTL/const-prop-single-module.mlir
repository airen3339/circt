// RUN: circt-opt -simple-canonicalizer %s | FileCheck %s

// The following tests are derived from `ConstantPropagationSingleModule` in [1].
// They are intended to closely follow the module test case structure in the
// original Scala source file.
// [1]: https://github.com/chipsalliance/firrtl/blob/master/src/test/scala/firrtlTests/ConstantPropagationTests.scala

firrtl.circuit "ConstantPropagationSingleModule" {
firrtl.module @ConstantPropagationSingleModule() {}


// The rule x >= 0 should always be true if x is a UInt
firrtl.module @Top01(%x: !firrtl.uint<5>, %y: !firrtl.flip<uint<1>>) {
  %c0_ui = firrtl.constant(0 : ui64) : !firrtl.uint
  %0 = firrtl.geq %x, %c0_ui : (!firrtl.uint<5>, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top01
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(true)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule x < 0 should never be true if x is a UInt
firrtl.module @Top02(%x: !firrtl.uint<5>, %y: !firrtl.flip<uint<1>>) {
  %c0_ui = firrtl.constant(0 : ui64) : !firrtl.uint
  %0 = firrtl.lt %x, %c0_ui : (!firrtl.uint<5>, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top02
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(false)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 0 <= x should always be true if x is a UInt
firrtl.module @Top03(%x: !firrtl.uint<5>, %y: !firrtl.flip<uint<1>>) {
  %c0_ui = firrtl.constant(0 : ui64) : !firrtl.uint
  %0 = firrtl.leq %c0_ui, %x : (!firrtl.uint, !firrtl.uint<5>) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top03
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(true)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 0 > x should never be true if x is a UInt
firrtl.module @Top04(%x: !firrtl.uint<5>, %y: !firrtl.flip<uint<1>>) {
  %c0_ui = firrtl.constant(0 : ui64) : !firrtl.uint
  %0 = firrtl.gt %c0_ui, %x : (!firrtl.uint, !firrtl.uint<5>) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top04
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(false)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 1 < 3 should always be true
firrtl.module @Top05(%y: !firrtl.flip<uint<1>>) {
  %c1_ui = firrtl.constant(1 : ui4) : !firrtl.uint
  %c3_ui = firrtl.constant(3 : ui4) : !firrtl.uint
  %0 = firrtl.lt %c1_ui, %c3_ui : (!firrtl.uint, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top05
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(true)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule x < 8 should always be true if x only has 3 bits
firrtl.module @Top06(%x: !firrtl.uint<3>, %y: !firrtl.flip<uint<1>>) {
  %c8_ui = firrtl.constant(8 : ui5) : !firrtl.uint
  %0 = firrtl.lt %x, %c8_ui : (!firrtl.uint<3>, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top06
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(true)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule x <= 7 should always be true if x only has 3 bits
firrtl.module @Top07(%x: !firrtl.uint<3>, %y: !firrtl.flip<uint<1>>) {
  %c7_ui = firrtl.constant(7 : ui4) : !firrtl.uint
  %0 = firrtl.leq %x, %c7_ui : (!firrtl.uint<3>, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top07
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(true)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 8 > x should always be true if x only has 3 bits
firrtl.module @Top08(%x: !firrtl.uint<3>, %y: !firrtl.flip<uint<1>>) {
  %c8_ui = firrtl.constant(8 : ui5) : !firrtl.uint
  %0 = firrtl.gt %c8_ui, %x : (!firrtl.uint, !firrtl.uint<3>) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top08
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(true)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 7 >= x should always be true if x only has 3 bits
firrtl.module @Top09(%x: !firrtl.uint<3>, %y: !firrtl.flip<uint<1>>) {
  %c7_ui = firrtl.constant(7 : ui4) : !firrtl.uint
  %0 = firrtl.geq %c7_ui, %x : (!firrtl.uint, !firrtl.uint<3>) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top09
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(true)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 10 == 10 should always be true
firrtl.module @Top10(%y: !firrtl.flip<uint<1>>) {
  %c10_ui = firrtl.constant(10 : ui8) : !firrtl.uint
  %0 = firrtl.eq %c10_ui, %c10_ui : (!firrtl.uint, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top10
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(true)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule x == z should not be true even if they have the same number of bits
firrtl.module @Top11(%x: !firrtl.uint<3>, %z: !firrtl.uint<3>, %y: !firrtl.flip<uint<1>>) {
  %0 = firrtl.eq %x, %z : (!firrtl.uint<3>, !firrtl.uint<3>) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top11
// CHECK-NEXT: %[[K:.+]] = firrtl.eq %x, %z
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 10 != 10 should always be false
firrtl.module @Top12(%y: !firrtl.flip<uint<1>>) {
  %c10_ui = firrtl.constant(10 : ui8) : !firrtl.uint
  %0 = firrtl.neq %c10_ui, %c10_ui : (!firrtl.uint, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top12
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(false)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 1 >= 3 should always be false
firrtl.module @Top13(%y: !firrtl.flip<uint<1>>) {
  %c1_ui = firrtl.constant(1 : ui4) : !firrtl.uint
  %c3_ui = firrtl.constant(3 : ui4) : !firrtl.uint
  %0 = firrtl.geq %c1_ui, %c3_ui : (!firrtl.uint, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top13
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(false)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule x >= 8 should never be true if x only has 3 bits
firrtl.module @Top14(%x: !firrtl.uint<3>, %y: !firrtl.flip<uint<1>>) {
  %c8_ui = firrtl.constant(8 : ui5) : !firrtl.uint
  %0 = firrtl.geq %x, %c8_ui : (!firrtl.uint<3>, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top14
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(false)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule x > 7 should never be true if x only has 3 bits
firrtl.module @Top15(%x: !firrtl.uint<3>, %y: !firrtl.flip<uint<1>>) {
  %c7_ui = firrtl.constant(7 : ui4) : !firrtl.uint
  %0 = firrtl.gt %x, %c7_ui : (!firrtl.uint<3>, !firrtl.uint) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top15
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(false)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 8 <= x should never be true if x only has 3 bits
firrtl.module @Top16(%x: !firrtl.uint<3>, %y: !firrtl.flip<uint<1>>) {
  %c8_ui = firrtl.constant(8 : ui5) : !firrtl.uint
  %0 = firrtl.leq %c8_ui, %x : (!firrtl.uint, !firrtl.uint<3>) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top16
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(false)
// CHECK-NEXT: firrtl.connect %y, %[[K]]


// The rule 7 < x should never be true if x only has 3 bits
firrtl.module @Top17(%x: !firrtl.uint<3>, %y: !firrtl.flip<uint<1>>) {
  %c7_ui = firrtl.constant(7 : ui4) : !firrtl.uint
  %0 = firrtl.lt %c7_ui, %x : (!firrtl.uint, !firrtl.uint<3>) -> !firrtl.uint<1>
  firrtl.connect %y, %0 : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}
// CHECK-LABEL: firrtl.module @Top17
// CHECK-NEXT: %[[K:.+]] = firrtl.constant(false)
// CHECK-NEXT: firrtl.connect %y, %[[K]]

}
