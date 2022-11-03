// RUN: circt-opt -pass-pipeline='firrtl.circuit(firrtl-grand-central,symbol-dce)' -split-input-file %s | FileCheck %s

firrtl.circuit "InterfaceGroundType" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        description = "description of foo",
        name = "foo",
        id = 1 : i64},
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        description = "multi\nline\ndescription\nof\nbar",
        name = "bar",
        id = 2 : i64},
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        name = "baz",
        id = 3 : i64}],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %a = firrtl.wire {annotations = [
      {a},
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 1 : i64}]} : !firrtl.uint<2>
    %b = firrtl.wire {annotations = [
      {a},
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 2 : i64}]} : !firrtl.uint<4>
    %c = firrtl.wire  {annotations = [
      {a},
      {circt.fieldID = 4 : i32, class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 3 : i64}
    ]} : !firrtl.vector<bundle<d: uint<2>>, 2>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @InterfaceGroundType() {
    firrtl.instance dut @DUT()
  }
}

// AugmentedBundleType is removed, ExtractGrandCentral remains.
// CHECK-LABEL: firrtl.circuit "InterfaceGroundType" {{.+}} {annotations =
// CHECK-SAME: class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation"
// CHECK-NOT: class = "sifive.enterprise.grandcentral.AugmentedBundleType"
// CHECK-SAME: {

// CHECK: firrtl.module private @View_companion
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NEXT: sv.interface.instance sym @__View_Foo__ {name = "View"} : !sv.interface<@Foo>
// CHECK-NEXT: sv.verbatim "assign {{[{][{]0[}][}]}}.foo = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}};"
// CHECK-SAME:   #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:   @DUT
// CHECK-SAME:   #hw.innerNameRef<@DUT::@a>
// CHECK-NEXT: sv.verbatim "assign {{[{][{]0[}][}]}}.bar = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}};"
// CHECK-SAME:   #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:   @DUT
// CHECK-SAME:   #hw.innerNameRef<@DUT::@b>
// CHECK-NEXT: sv.verbatim "assign {{[{][{]0[}][}]}}.baz = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}}[1].d;"
// CHECK-SAME:   #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:   @DUT
// CHECK-SAME:   #hw.innerNameRef<@DUT::@c>]

// All Grand Central annotations are removed from the wires.
// CHECK: firrtl.module private @DUT
// CHECK: %a = firrtl.wire
// CHECK-SAME: annotations = [{a}]
// CHECK: %b = firrtl.wire
// CHECK-SAME: annotations = [{a}]
// CHECK: %c = firrtl.wire
// CHECK-SAME: annotations = [{a}]

// CHECK: sv.interface @Foo
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NEXT: sv.verbatim "// description of foo"
// CHECK-NEXT: sv.interface.signal @foo : i2
// CHECK-NEXT: sv.verbatim "// multi\0A// line\0A// description\0A// of\0A// bar"
// CHECK-NEXT: sv.interface.signal @bar : i4

// -----

firrtl.circuit "InterfaceVectorType" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedVectorType",
        description = "description of foo",
        elements = [
          {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
           id = 1 : i64,
           name = "foo"},
          {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
           id = 2 : i64,
           name = "foo"}],
        name = "foo"}],
      id = 0 : i64,
      name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>) attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %a_0 = firrtl.reg %clock {
      annotations = [
        {a},
        {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
         id = 1 : i64}]} : !firrtl.uint<1>
    %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
    %a_1 = firrtl.regreset %clock, %reset, %c0_ui1 {
      annotations = [
        {a},
        {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
         id = 2 : i64}]} : !firrtl.uint<1>, !firrtl.uint<1>, !firrtl.uint<1>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @InterfaceVectorType() {
    %dut_clock, %dut_reset = firrtl.instance dut @DUT(in clock: !firrtl.clock, in reset: !firrtl.uint<1>)
  }
}

// AugmentedBundleType is removed, ExtractGrandCentral remains.
// CHECK-LABEL: firrtl.circuit "InterfaceVectorType" {{.+}} {annotations =
// CHECK-SAME: class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation"
// CHECK-NOT: class = "sifive.enterprise.grandcentral.AugmentedBundleType"
// CHECK-SAME: {

// CHECK: firrtl.module private @View_companion
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"

// All Grand Central annotations are removed from the registers.
// CHECK: firrtl.module private @DUT
// CHECK: %a_0 = firrtl.reg
// CHECK-SAME: annotations = [{a}]
// CHECK: %a_1 = firrtl.regreset
// CHECK-SAME: annotations = [{a}]

// CHECK: sv.interface @Foo
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NEXT: sv.verbatim "// description of foo"
// CHECK-NEXT: sv.interface.signal @foo : !hw.uarray<2xi1>

// -----

firrtl.circuit "InterfaceBundleType" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
        defName = "Bar",
        description = "description of Bar",
        elements = [
          {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
           id = 1 : i64,
           name = "b"},
          {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
           id = 2 : i64,
           name = "a"}],
        name = "bar"}],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]}  {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %x = firrtl.wire {
      annotations = [
        {a},
        {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
         id = 2 : i64}]} : !firrtl.uint<1>
    %y = firrtl.wire {
      annotations = [
        {a},
        {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
         id = 1 : i64}]} : !firrtl.uint<2>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @InterfaceBundleType() {
    firrtl.instance dut @DUT()
  }
}

// AugmentedBundleType is removed, ExtractGrandCentral remains.
// CHECK-LABEL: firrtl.circuit "InterfaceBundleType"
// CHECK-SAME: class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation"
// CHECK-NOT: class = "sifive.enterprise.grandcentral.AugmentedBundleType"
// CHECK-SAME: {

// All Grand Central annotations are removed from the wires.
// CHECK-LABEL: firrtl.module private @DUT
// CHECK: %x = firrtl.wire
// CHECK-SAME: annotations = [{a}]
// CHECK: %y = firrtl.wire
// CHECK-SAME: annotations = [{a}]

// CHECK: sv.interface @Foo
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NEXT: sv.verbatim "// description of Bar"
// CHECK-NEXT: Bar bar();

// CHECK: sv.interface @Bar
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NEXT: sv.interface.signal @b : i2
// CHECK-NEXT: sv.interface.signal @a : i1

// -----

firrtl.circuit "InterfaceVecOfBundleType" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedVectorType",
        elements = [
          {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
           defName = "Bar",
           elements = [
             {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
              id = 1 : i64,
              name = "b"}],
           name = "bar"}],
        name = "bar"}],
     id = 0 : i64,
     name = "View"}]}  {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %x = firrtl.wire {
      annotations = [
        {a},
        {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
         id = 1 : i64}]} : !firrtl.uint<2>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @InterfaceVecOfBundleType() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: firrtl.circuit "InterfaceVecOfBundleType"

// CHECK: sv.interface @Foo
// CHECK-NEXT: sv.verbatim "Bar bar[1]();"

// CHECK: sv.interface @Bar

// -----

firrtl.circuit "VecOfVec" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedVectorType",
        description = "description of foo",
        elements = [
          {class = "sifive.enterprise.grandcentral.AugmentedVectorType",
           description = "description of foo",
           elements = [
             {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
              id = 1 : i64,
              name = "foo"},
             {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
              id = 2 : i64,
              name = "foo"}],
           name = "foo"}],
        name = "foo"}],
      id = 0 : i64,
      name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %a = firrtl.wire {annotations = [
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 1 : i64},
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 2 : i64}]} : !firrtl.uint<3>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @VecOfVec() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: firrtl.circuit "VecOfVec"

// CHECK:      firrtl.module private @View_companion
// CHECK-NEXT:    sv.interface.instance sym @__View_Foo__ {name = "View"} : !sv.interface<@Foo>
// CHECK-NEXT:    assign {{[{][{]0[}][}]}}.foo[0][0]
// CHECK-SAME:      #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-NEXT:    assign {{[{][{]0[}][}]}}.foo[0][1]
// CHECK-SAME:      #hw.innerNameRef<@View_companion::@__View_Foo__>

// CHECK:      sv.interface @Foo
// CHECK:        sv.interface.signal @foo : !hw.uarray<1xuarray<2xi3>>

// -----

firrtl.circuit "InterfaceNode" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        description = "some expression",
        id = 1 : i64,
        name = "foo"}],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %a = firrtl.wire : !firrtl.uint<2>
    %notA = firrtl.not %a : (!firrtl.uint<2>) -> !firrtl.uint<2>
    %b = firrtl.node %notA {
      annotations = [
        {a},
        {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
         defName = "Foo",
         name = "foo",
         id = 1 : i64}]} : !firrtl.uint<2>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @InterfaceNode() {
    firrtl.instance dut @DUT()
  }
}

// AugmentedBundleType is removed, ExtractGrandCentral remains.
// CHECK-LABEL: firrtl.circuit "InterfaceNode" {{.+}} {annotations =
// CHECK-SAME: class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation"
// CHECK-NOT: class = "sifive.enterprise.grandcentral.AugmentedBundleType"
// CHECK-SAME: {

// The Grand Central annotation is removed from the node.
// CHECK: firrtl.node
// CHECK-SAME: annotations = [{a}]

// CHECK: sv.interface @Foo
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NEXT: sv.verbatim "// some expression"
// CHECK-NEXT: sv.interface.signal @foo : i2

// -----

firrtl.circuit "InterfacePort" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        description = "description of foo",
        id = 1 : i64,
        name = "foo"}],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT(in %a : !firrtl.uint<4>) attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ],
    portAnnotations = [[
      {a},
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 1 : i64}]] } {
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @InterfacePort() {
    %dut_a = firrtl.instance dut @DUT(in a : !firrtl.uint<4>)
  }
}

// AugmentedBundleType is removed, ExtractGrandCentral remains.
// CHECK-LABEL: firrtl.circuit "InterfacePort" {{.+}} {annotations =
// CHECK-SAME: class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation"
// CHECK-NOT: class = "sifive.enterprise.grandcentral.AugmentedBundleType"
// CHECK-SAME: {

// The Grand Central annotations are removed.
// CHECK: firrtl.module private @DUT
// CHECK-SAME: %a: !firrtl.uint<4> sym @a [{a}]

// CHECK: sv.interface @Foo
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NEXT: sv.verbatim "// description of foo"
// CHECK-NEXT: sv.interface.signal @foo : i4

// -----

firrtl.circuit "UnsupportedTypes" attributes {
  annotations = [
    {a},
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedStringType",
        name = "string"},
       {class = "sifive.enterprise.grandcentral.AugmentedBooleanType",
        name = "boolean"},
       {class = "sifive.enterprise.grandcentral.AugmentedIntegerType",
        name = "integer"},
       {class = "sifive.enterprise.grandcentral.AugmentedDoubleType",
        name = "double"}],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @UnsupportedTypes() {
    firrtl.instance dut @DUT()
  }
}

// AugmentedBundleType is removed, ExtractGrandCentral and {a} remain.
// CHECK-LABEL: firrtl.circuit "UnsupportedTypes" {{.+}} {annotations =
// CHECK-SAME: {a}
// CHECK-SAME: class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation"
// CHECK-NOT: class = "sifive.enterprise.grandcentral.AugmentedBundleType"
// CHECK-SAME: {

// CHECK: sv.interface @Foo
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NEXT: sv.verbatim "// <unsupported string type> string;"
// CHECK-NEXT: sv.verbatim "// <unsupported boolean type> boolean;"
// CHECK-NEXT: sv.verbatim "// <unsupported integer type> integer;"
// CHECK-NEXT: sv.verbatim "// <unsupported double type> double;"

// -----

firrtl.circuit "BindInterfaceTest"  attributes {
  annotations = [{
    class = "sifive.enterprise.grandcentral.AugmentedBundleType",
    defName = "InterfaceName",
    elements = [{
      class = "sifive.enterprise.grandcentral.AugmentedGroundType",
      id = 1 : i64,
      name = "_a"
    }],
    id = 0 : i64,
    name = "View"
  },
  {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT(
    in %a: !firrtl.uint<8>, out %b: !firrtl.uint<8>) attributes {
      annotations = [{
        class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
        defName = "InterfaceName",
        id = 0 : i64,
        name = "instanceName"}],
      portAnnotations = [[
        {
          circt.fieldID = 0 : i32,
          class = "sifive.enterprise.grandcentral.AugmentedGroundType",
          id = 1 : i64
        }
      ], []
      ]
    }
      {
    firrtl.connect %b, %a : !firrtl.uint<8>, !firrtl.uint<8>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @BindInterfaceTest() {
    %dut_a, %dut_b = firrtl.instance dut @DUT(in a: !firrtl.uint<8>, out b: !firrtl.uint<8>)
  }
}

// CHECK: module {
// CHECK-LABEL: firrtl.circuit "BindInterfaceTest"

// Annotations are removed from the circuit.
// CHECK-NOT: annotations
// CHECK-SAME: {

// CHECK: firrtl.module private @View_companion()
// CHECK-NEXT: sv.interface.instance sym @[[INTERFACE_INSTANCE_SYMBOL:.+]]

// Annotations are removed from the module.
// CHECK: firrtl.module private @DUT
// CHECK-NOT: annotations
// CHECK-SAME: %a

// The interface is added.
// CHECK: sv.interface @InterfaceName
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NEXT: sv.interface.signal @_a : i8

// -----

firrtl.circuit "MultipleGroundTypeInterfaces" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        name = "foo",
        id = 1 : i64}],
     id = 0 : i64,
     name = "View1"},
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Bar",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        name = "foo",
        id = 3 : i64}],
     id = 2 : i64,
     name = "View2"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View1"},
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Bar",
       id = 2 : i64,
       name = "View2"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"},
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 2 : i64,
       name = "view"}
    ]} {
    %a = firrtl.wire {annotations = [
      {a},
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 1 : i64},
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 3 : i64}]} : !firrtl.uint<2>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @MultipleGroundTypeInterfaces() {
    firrtl.instance dut @DUT()
  }
}

// CHECK: sv.interface @Foo
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"

// CHECK: sv.interface @Bar
// CHECK-SAME: comment = "VCS coverage exclude_file"
// CHECK-SAME: output_file = #hw.output_file<"gct-dir{{/|\\\\}}"

// -----

firrtl.circuit "PrefixInterfacesAnnotation"
  attributes {annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
        defName = "Bar",
        elements = [],
        name = "bar"}],
     id = 0 : i64,
     name = "MyView"},
    {class = "sifive.enterprise.grandcentral.PrefixInterfacesAnnotation",
     prefix = "PREFIX_"}]}  {
  firrtl.module private @MyView_companion()
    attributes {annotations = [{
      class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
      id = 0 : i64,
      name = "MyView"}]} {}
  firrtl.module private @DUT()
    attributes {annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "MyView"}]} {
    firrtl.instance MyView_companion  @MyView_companion()
  }
  firrtl.module @PrefixInterfacesAnnotation() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: firrtl.circuit "PrefixInterfacesAnnotation"
// The PrefixInterfacesAnnotation was removed from the circuit.
// CHECK-NOT:     sifive.enterprise.grandcentral.PrefixInterfacesAnnotation

// Interface "Foo" is prefixed.
// CHECK:       sv.interface @PREFIX_Foo
// Interface "Bar" is prefixed, but not its name.
// CHECK-NEXT:    PREFIX_Bar bar()

// Interface "Bar" is prefixed.
// CHECK:       sv.interface @PREFIX_Bar

// -----


firrtl.circuit "NestedInterfaceVectorTypes" attributes {annotations = [
  {
    class = "sifive.enterprise.grandcentral.AugmentedBundleType",
    id = 0,
    name = "View",
    defName = "Foo",
    elements = [{
      class = "sifive.enterprise.grandcentral.AugmentedVectorType",
      name = "bar",
      description = "description of bar",
      elements = [
        {
          class = "sifive.enterprise.grandcentral.AugmentedVectorType",
          name = "baz",
          elements = [
            {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 1, name = "baz"},
            {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 2, name = "baz"},
            {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 3, name = "baz"}
          ]
        },
        {
          class = "sifive.enterprise.grandcentral.AugmentedVectorType",
          name = "baz",
          elements = [
            {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 4, name = "baz"},
            {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 5, name = "baz"},
            {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 6, name = "baz"}
          ]
        }
      ]
    }]
  },
  {
    class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
    directory = "gct-dir",
    filename = "bindings.sv"
  }
]} {

  firrtl.module private @View_companion() attributes {annotations = [
    {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion", defName = "Foo", id = 0, name = "View"}
  ]} {}

  firrtl.module private @DUT() attributes {annotations = [
    {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent", id = 0, name = "view"}
  ]} {
    %a0 = firrtl.wire {annotations = [{class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 1}]} : !firrtl.uint<1>
    %a1 = firrtl.wire {annotations = [{class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 2}]} : !firrtl.uint<1>
    %a2 = firrtl.wire {annotations = [{class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 3}]} : !firrtl.uint<1>
    %b0 = firrtl.wire {annotations = [{class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 4}]} : !firrtl.uint<1>
    %b1 = firrtl.wire {annotations = [{class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 5}]} : !firrtl.uint<1>
    %b2 = firrtl.wire {annotations = [{class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 6}]} : !firrtl.uint<1>
    firrtl.instance View_companion @View_companion()
  }

  firrtl.module @NestedInterfaceVectorTypes() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: firrtl.circuit "NestedInterfaceVectorTypes"
// CHECK:         firrtl.module private @View_companion
// CHECK-NEXT:      sv.interface.instance sym @__View_Foo__ {name = "View"} : !sv.interface<@Foo>
// CHECK-NEXT:      sv.verbatim "assign {{[{][{]0[}][}]}}.bar[0][0] = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}};"
// CHECK-SAME:        #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:        @DUT
// CHECK-SAME:        #hw.innerNameRef<@DUT::@a0>
// CHECK-NEXT:      sv.verbatim "assign {{[{][{]0[}][}]}}.bar[0][1] = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}};"
// CHECK-SAME:        #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:        @DUT
// CHECK-SAME:        #hw.innerNameRef<@DUT::@a1>
// CHECK-NEXT:      sv.verbatim "assign {{[{][{]0[}][}]}}.bar[0][2] = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}};"
// CHECK-SAME:        #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:        @DUT
// CHECK-SAME:        #hw.innerNameRef<@DUT::@a2>
// CHECK-NEXT:      sv.verbatim "assign {{[{][{]0[}][}]}}.bar[1][0] = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}};"
// CHECK-SAME:        #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:        @DUT
// CHECK-SAME:        #hw.innerNameRef<@DUT::@b0>
// CHECK-NEXT:      sv.verbatim "assign {{[{][{]0[}][}]}}.bar[1][1] = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}};"
// CHECK-SAME:        #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:        @DUT
// CHECK-SAME:        #hw.innerNameRef<@DUT::@b1>
// CHECK-NEXT:      sv.verbatim "assign {{[{][{]0[}][}]}}.bar[1][2] = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}};"
// CHECK-SAME:        #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:        @DUT
// CHECK-SAME:        #hw.innerNameRef<@DUT::@b2>
// CHECK:         sv.interface @Foo
// CHECK-NEXT:      sv.verbatim "// description of bar"
// CHECK-NEXT:      sv.interface.signal @bar : !hw.uarray<2xuarray<3xi1>>

// -----

firrtl.circuit "VerbatimTypesInVector" attributes {annotations = [
  {
    class = "sifive.enterprise.grandcentral.AugmentedBundleType",
    id = 0,
    name = "View",
    defName = "Foo",
    elements = [{
      class = "sifive.enterprise.grandcentral.AugmentedVectorType",
      name = "bar",
      description = "description of bar",
      elements = [
        {
          class = "sifive.enterprise.grandcentral.AugmentedVectorType",
          name = "baz",
          description = "description of baz",
          elements = [
            {class = "sifive.enterprise.grandcentral.AugmentedStringType", name = "baz"},
            {class = "sifive.enterprise.grandcentral.AugmentedStringType", name = "baz"},
            {class = "sifive.enterprise.grandcentral.AugmentedStringType", name = "baz"}
          ]
        },
        {
          class = "sifive.enterprise.grandcentral.AugmentedVectorType",
          name = "baz",
          description = "description of baz",
          elements = [
            {class = "sifive.enterprise.grandcentral.AugmentedStringType", name = "baz"},
            {class = "sifive.enterprise.grandcentral.AugmentedStringType", name = "baz"},
            {class = "sifive.enterprise.grandcentral.AugmentedStringType", name = "baz"}
          ]
        }
      ]
    }]
  },
  {
    class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
    directory = "gct-dir",
    filename = "bindings.sv"
  }
]} {

  firrtl.module private @View_companion() attributes {annotations = [
    {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion", defName = "Foo", id = 0, name = "View"}
  ]} {}

  firrtl.module private @DUT() attributes {annotations = [
    {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent", id = 0, name = "view"}
  ]} {
    firrtl.instance View_companion @View_companion()
  }

  firrtl.module @VerbatimTypesInVector() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: firrtl.circuit "VerbatimTypesInVector"
// CHECK:         sv.interface @Foo
// CHECK-NEXT:      sv.verbatim "// description of bar"
// CHECK-NEXT:      sv.verbatim "// <unsupported string type> bar[2][3];"

// -----

firrtl.circuit "ParentIsMainModule" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        name = "foo",
        id = 1 : i64}],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module @ParentIsMainModule() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %a = firrtl.wire {annotations = [
      {a},
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 1 : i64}]} : !firrtl.uint<2>
    firrtl.instance View_companion @View_companion()
  }
}

// Check that this doesn't error out and that the XMR is generated correctly.
//
// CHECK-LABEL: firrtl.circuit "ParentIsMainModule"
// CHECK:       firrtl.module private @View_companion
// CHECK-NEXT:    sv.interface.instance sym @__View_Foo__ {name = "View"} : !sv.interface<@Foo>
// CHECK-NEXT:    sv.verbatim "assign {{[{][{]0[}][}]}}.foo = {{[{][{]1[}][}]}}.{{[{][{]2[}][}]}};"
// CHECK-SAME:      #hw.innerNameRef<@View_companion::@__View_Foo__>
// CHECK-SAME:      @ParentIsMainModule
// CHECK-SAME:      #hw.innerNameRef<@ParentIsMainModule::@a>

// -----

firrtl.circuit "DedupedPath" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        name = "foo",
        id = 1 : i64},
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        name = "bar",
        id = 2 : i64},
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        name = "baz",
        id = 3 : i64},
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        name = "qux",
        id = 4 : i64}],
     id = 0 : i64,
     name = "View"}]} {
  // TODO: Remove @nla_0 and @nla once NLAs are fully migrated to use hierpaths
  // that end at the module.
  firrtl.hierpath private @nla_0 [@DUT::@tile1, @Tile::@w]
  firrtl.hierpath private @nla [@DUT::@tile2, @Tile::@w]
  firrtl.hierpath private @nla_new_0 [@DUT::@tile1, @Tile]
  firrtl.hierpath private @nla_new_1 [@DUT::@tile2, @Tile]
  firrtl.module private @Tile() {
    %w = firrtl.wire sym @w {
      annotations = [
        {
          circt.fieldID = 0 : i32,
          circt.nonlocal = @nla,
          class = "sifive.enterprise.grandcentral.AugmentedGroundType",
          id = 2 : i64
        },
        {
          circt.fieldID = 0 : i32,
          circt.nonlocal = @nla_0,
          class = "sifive.enterprise.grandcentral.AugmentedGroundType",
          id = 1 : i64
        }]} : !firrtl.uint<8>
    %x = firrtl.wire {
      annotations = [
        {
          circt.fieldID = 0 : i32,
          circt.nonlocal = @nla_new_0,
          class = "sifive.enterprise.grandcentral.AugmentedGroundType",
          id = 3 : i64
        },
        {
          circt.fieldID = 0 : i32,
          circt.nonlocal = @nla_new_1,
          class = "sifive.enterprise.grandcentral.AugmentedGroundType",
          id = 4 : i64
        }]} : !firrtl.uint<8>
  }
  firrtl.module private @MyView_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       id = 0 : i64,
       name = "MyView"},
      {class = "firrtl.transforms.NoDedupAnnotation"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "MyView"},
      {class = "sifive.enterprise.firrtl.MarkDUTAnnotation"}]} {
    firrtl.instance tile1 sym @tile1 @Tile()
    firrtl.instance tile2 sym @tile2 @Tile()
    firrtl.instance MyView_companion  @MyView_companion()
  }
  firrtl.module @DedupedPath() {
    firrtl.instance dut @DUT()
  }
}

// Chceck that NLAs that encode a path to a Grand Central leaf work.  This
// should result in two things:
//   1) The compute XMR should include information from the NLA.
//   2) The NLAs should be removed.
//
// CHECK-LABEL:          firrtl.circuit "DedupedPath"
// CHECK-NOT:              firrtl.hierpath
// CHECK-NEXT:             firrtl.module private @Tile()
// CHECK-NOT:                circt.nonlocal
// CHECK:                  firrtl.module private @MyView_companion
// CHECK-NEXT:               sv.interface.instance sym @__MyView_Foo__ {name = "MyView"} : !sv.interface<@Foo>
// CHECK-NEXT{LITERAL}:      sv.verbatim "assign {{0}}.foo = {{1}}.{{2}}.{{3}};"
// CHECK-SAME:                 symbols = [#hw.innerNameRef<@MyView_companion::@__MyView_Foo__>,
// CHECK-SAME:                   @DUT,
// CHECK-SAME:                   #hw.innerNameRef<@DUT::@tile1>,
// CHECK-SAME:                   #hw.innerNameRef<@Tile::@w>]
// CHECK-NEXT{LITERAL}:      sv.verbatim "assign {{0}}.bar = {{1}}.{{2}}.{{3}};"
// CHECK-SAME:                 symbols = [#hw.innerNameRef<@MyView_companion::@__MyView_Foo__>,
// CHECK-SAME:                   @DUT,
// CHECK-SAME:                   #hw.innerNameRef<@DUT::@tile2>,
// CHECK-SAME:                   #hw.innerNameRef<@Tile::@w>]
// CHECK-NEXT{LITERAL}:      sv.verbatim "assign {{0}}.baz = {{1}}.{{2}}.{{3}};"
// CHECK-SAME:                 symbols = [#hw.innerNameRef<@MyView_companion::@__MyView_Foo__>,
// CHECK-SAME:                   @DUT,
// CHECK-SAME:                   #hw.innerNameRef<@DUT::@tile1>,
// CHECK-SAME:                   #hw.innerNameRef<@Tile::@x>]
// CHECK-NEXT{LITERAL}:      sv.verbatim "assign {{0}}.qux = {{1}}.{{2}}.{{3}};"
// CHECK-SAME:                 symbols = [#hw.innerNameRef<@MyView_companion::@__MyView_Foo__>,
// CHECK-SAME:                   @DUT,
// CHECK-SAME:                   #hw.innerNameRef<@DUT::@tile2>,
// CHECK-SAME:                   #hw.innerNameRef<@Tile::@x>]
// CHECK:                  firrtl.module private @DUT()
// CHECK-NOT:                circt.nonlocal
// CHECK:                  firrtl.module @DedupedPath
// CHECK-NEXT:               firrtl.instance dut
// CHECK-NOT:                  sym

// -----

firrtl.circuit "DirectoryBehaviorWithDUT" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {

  // Each of these modules is instantiated in a different location.  A leading
  // "E" indicates that this is an external module.  A leading "M" indicates
  // that this is a module.  The instantiation location is indicated by three
  // binary bits with an "_" indicating the absence of instantiation:
  //   1) "T" indicates this is instantiated in the "Top" (above the DUT)
  //   2) "D" indicates this is instantiated in the "DUT"
  //   3) "C" indicates this is instantiated in the "Companion"
  // E.g., "ET_C" is an external module instantiated above the DUT and in the
  // Companion.
  firrtl.module @MT__() {}
  firrtl.module @M_D_() {}
  firrtl.module @M__C() {}
  firrtl.module @MTD_() {}
  firrtl.module @M_DC() {}
  firrtl.module @MT_C() {}
  firrtl.module @MTDC() {}
  firrtl.extmodule @ET__() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "ET__.v", text = ""}
  ]}
  firrtl.extmodule @E_D_() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "E_D_.v", text = ""}
  ]}
  firrtl.extmodule @E__C() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "E__C.v", text = ""}
  ]}
  firrtl.extmodule @ETD_() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "ETD_.v", text = ""}
  ]}
  firrtl.extmodule @E_DC() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "E_DC.v", text = ""}
  ]}
  firrtl.extmodule @ET_C() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "ET_C.v", text = ""}
  ]}
  firrtl.extmodule @ETDC() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "ETDC.v", text = ""}
  ]}

  // The Grand Central Companion module.
  firrtl.module private @Companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {

    firrtl.instance m__c @M__C()
    firrtl.instance m_dc @M_DC()
    firrtl.instance mt_c @MT_C()
    firrtl.instance mtdc @MTDC()

    firrtl.instance e__c @E__C()
    firrtl.instance e_dc @E_DC()
    firrtl.instance et_c @ET_C()
    firrtl.instance etdc @ETDC()
  }

  // The Design-under-test as indicated by the MarkDUTAnnotation
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"},
      {class = "sifive.enterprise.firrtl.MarkDUTAnnotation"}
    ]} {
    firrtl.instance companion @Companion()

    firrtl.instance m_d_ @M_D_()
    firrtl.instance mtd_ @MTD_()
    firrtl.instance m_dc @M_DC()
    firrtl.instance mtdc @MTDC()

    firrtl.instance e_d_ @E_D_()
    firrtl.instance etd_ @ETD_()
    firrtl.instance e_dc @E_DC()
    firrtl.instance etdc @ETDC()
  }

  // The Top module that instantiates the DUT
  firrtl.module @DirectoryBehaviorWithDUT() {
    firrtl.instance dut @DUT()

    firrtl.instance mt__ @MT__()
    firrtl.instance mtd_ @MTD_()
    firrtl.instance mt_c @MT_C()
    firrtl.instance mtdc @MTDC()

    firrtl.instance et__ @ET__()
    firrtl.instance etd_ @ETD_()
    firrtl.instance et_c @ET_C()
    firrtl.instance etdc @ETDC()
  }
}

// Any module instantiated by the Companion, but not instantiated by the DUT is
// moved to the same directory as the Companion.  I.e., only "*__C" and "*T_C"
// modules should be moved into the "gct-dir".
//
// CHECK-LABEL: "DirectoryBehaviorWithDUT"
//
// CHECK-NOT:    output_file
// CHECK:      firrtl.module @M__C
// CHECK-SAME:   output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NOT:    output_file
// CHECK:      firrtl.module @MT_C
// CHECK-SAME:   output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
//
// CHECK-NOT:    output_file
// CHECK:      firrtl.extmodule @E__C
// CHECK-SAME:   output_file = #hw.output_file<"gct-dir{{/|\\\\}}">
// CHECK-NOT:    output_file
// CHECK:      firrtl.extmodule @ET_C
// CHECK-SAME:   output_file = #hw.output_file<"gct-dir{{/|\\\\}}">
// CHECK-NOT:    output_file
//
// CHECK:      firrtl.module

// -----

firrtl.circuit "DirectoryBehaviorWithoutDUT" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"}]} {

  // Each of these modules is instantiated in a different location.  A leading
  // "E" indicates that this is an external module.  A leading "M" indicates
  // that this is a module.  The instantiation location is indicated by three
  // binary bits with an "_" indicating the absence of instantiation:
  //   1) "T" indicates this is instantiated in the "Top"
  //   2) "C" indicates this is instantiated in the "Companion"
  // E.g., "E_C" is an external module instantiated only in the Companion.
  firrtl.module @MT_() {}
  firrtl.module @M_C() {}
  firrtl.module @MTC() {}
  firrtl.extmodule @ET_() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "ET_.v", text = ""}
  ]}
  firrtl.extmodule @E_C() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "E_C.v", text = ""}
  ]}
  firrtl.extmodule @ETC() attributes {annotations = [
    {class = "firrtl.transforms.BlackBoxInlineAnno", name = "ETC.v", text = ""}
  ]}

  // The Grand Central Companion module.
  firrtl.module private @Companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {

    firrtl.instance m__c @M_C()
    firrtl.instance m_dc @MTC()

    firrtl.instance e__c @E_C()
    firrtl.instance e_dc @ETC()
  }

  // This is the DUT in the previous example, but is no longer marked as the
  // DUT.
  firrtl.module @DirectoryBehaviorWithoutDUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    firrtl.instance companion @Companion()

    firrtl.instance m_d_ @MT_()
    firrtl.instance m_dc @MTC()

    firrtl.instance e_d_ @ET_()
    firrtl.instance e_dc @ETC()
  }

}

// Any module instantiated by the Companion, but not instantiated by the DUT is
// moved to the same directory as the Companion.  I.e., only "*_C" modules
// should be moved into the "gct-dir".
//
// CHECK-LABEL: "DirectoryBehaviorWithoutDUT"
//
// CHECK-NOT:    output_file
// CHECK:      firrtl.module @M_C
// CHECK-SAME:   output_file = #hw.output_file<"gct-dir{{/|\\\\}}"
// CHECK-NOT:    output_file
//
// CHECK:      firrtl.extmodule @E_C
// CHECK-SAME:   output_file = #hw.output_file<"gct-dir{{/|\\\\}}">
// CHECK-NOT:    output_file
//
// CHECK:      firrtl.module

// -----

firrtl.circuit "InterfaceInTestHarness" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        description = "description of foo",
        name = "foo",
        id = 1 : i64}],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"},
    {class = "sifive.enterprise.firrtl.TestBenchDirAnnotation",
     dirname = "testbenchDir"}]} {
  firrtl.module @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.firrtl.MarkDUTAnnotation"}
    ]} {
  }
  firrtl.module @InterfaceInTestHarness() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}]} {
    firrtl.instance dut @DUT()
    %a = firrtl.wire {annotations = [
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 1 : i64},
      {class = "firrtl.transforms.DontTouchAnnotation"}]} : !firrtl.uint<2>
    firrtl.instance View_companion @View_companion()
  }
}

// Check that an interface, instantiated inside the test harness (technically,
// in a module which is not a child of the marked Design Under Test), will not
// be extracted via a bind.  Also, check that interfaces only inside the test
// harness will be written to the test harness directory.
//
// CHECK-LABEL: "InterfaceInTestHarness"
// CHECK:       firrtl.module @View_companion
// CHECK:         sv.interface.instance
// CHECK-NOT:       output_file
// CHECK-NOT:       lowerToBind
// CHECK-SAME:      !sv.interface
// CHECK:       firrtl.module @InterfaceInTestHarness
// CHECK:         firrtl.instance View_companion
// CHECK-NOT:       output_file
// CHECK-NOT:       lowerToBind
// CHECK-NEXT:  }
// CHECK:       sv.interface
// CHECK-SAME:    output_file = #hw.output_file<"testbenchDir{{/|\\\\}}", excludeFromFileList>

// -----

firrtl.circuit "ZeroWidth" attributes {annotations = [
  {
    class = "sifive.enterprise.grandcentral.AugmentedBundleType",
    defName = "MyInterface",
    elements = [
      {
        class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        description = "a zero-width port",
        id = 1 : i64,
        name = "ground"
      }
    ],
    id = 0 : i64,
    name = "MyView"
  }
]} {
  firrtl.module private @MyView_companion() attributes {annotations = [
    {
      class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
      id = 0 : i64,
      name = "MyView"}
  ]} {}
  firrtl.module @ZeroWidth() attributes {annotations = [
    {
      class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
      id = 0 : i64,
      name = "MyView"}
  ]} {
    %w = firrtl.wire {annotations = [
      {
        class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        id = 1 : i64
      }
    ]} : !firrtl.uint<0>
    %invalid_ui0 = firrtl.invalidvalue : !firrtl.uint<0>
    firrtl.strictconnect %w, %invalid_ui0 : !firrtl.uint<0>
    firrtl.instance MyView_companion @MyView_companion()
  }
}

// Check that a view of a zero-width thing produces a comment in the output and
// not XMR.
//
// CHECK-LABEL: firrtl.circuit "ZeroWidth"
//
// CHECK:       firrtl.module private @MyView_companion() {
// CHECK-NOT:     sv.verbatim
// CHECK-NEXT:  }
//
// CHECK-LABEL: sv.interface @MyInterface
// CHECK-NEXT:    sv.verbatim "// a zero-width port"
// CHECK-NEXT:    sv.interface.signal @ground : i0

// -----

firrtl.circuit "ZeroWidth" attributes {annotations = [
  {
    class = "sifive.enterprise.grandcentral.AugmentedBundleType",
    defName = "MyInterface",
    elements = [
      {
        class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        id = 1 : i64,
        name = "ground"
      }
    ],
    id = 0 : i64,
    name = "MyView"
  }
]} {
  firrtl.module private @MyView_companion() attributes {annotations = [
    {
      class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
      id = 0 : i64,
      name = "MyView"}
  ]} {}
  firrtl.module @ZeroWidth() attributes {annotations = [
    {
      class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
      id = 0 : i64,
      name = "MyView"}
  ]} {
    %w = firrtl.wire {annotations = [
      {
        class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        id = 1 : i64
      }
    ]} : !firrtl.uint<1>
    %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
    firrtl.strictconnect %w, %c1_ui1 : !firrtl.uint<1>
    firrtl.instance MyView_companion @MyView_companion()
  }
}

// Check that a constant is sunk into the interface mapping module and that no
// symbol is created on the viewed component.
//
// CHECK-LABEL:         firrtl.circuit "ZeroWidth"
// CHECK:                 firrtl.module private @MyView_companion()
// CHECK-NEXT:              sv.interface.instance
// CHECK-NEXT{LITERAL}:     sv.verbatim "assign {{0}}.ground = 1'h1;
// CHECK:                 firrtl.module @ZeroWidth()
// CHECK-NEXT:            %w = firrtl.wire : !firrtl.uint<1>

// -----

firrtl.circuit "Top" attributes {
  annotations = [
    {
      class = "sifive.enterprise.grandcentral.AugmentedBundleType",
      defName = "MyInterface_w1",
      elements = [
        {
          class = "sifive.enterprise.grandcentral.AugmentedBundleType",
          defName = "SameName",
          elements = [
            {
              class = "sifive.enterprise.grandcentral.AugmentedGroundType",
              id = 1 : i64,
              name = "uint"
            }
          ],
          name = "SameName"
        }
      ],
      id = 0 : i64,
      name = "View_w1"
    },
    {
      class = "sifive.enterprise.grandcentral.AugmentedBundleType",
      defName = "MyInterface_w2",
      elements = [
        {
          class = "sifive.enterprise.grandcentral.AugmentedBundleType",
          defName = "SameName",
          elements = [
            {
              class = "sifive.enterprise.grandcentral.AugmentedGroundType",
              id = 3 : i64,
              name = "uint"
            }
          ],
          name = "SameName"
        }
      ],
      id = 2 : i64,
      name = "View_w2"
    },
    {
      class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
      directory = ".",
      filename = "bindings.sv"
    }
  ]
} {
  firrtl.module @Companion_w1(in %_gen_uint: !firrtl.ref<uint<1>>) attributes {
    annotations = [
      {
        class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
        id = 0 : i64,
        name = "View_w1"
      }
    ]
  } {
    %0 = firrtl.ref.resolve %_gen_uint : !firrtl.ref<uint<1>>
    %view_uintrefPort = firrtl.node  %0  {
      annotations = [
        {
          class = "sifive.enterprise.grandcentral.AugmentedGroundType",
          id = 1 : i64
        }
      ]
    } : !firrtl.uint<1>
  }
  firrtl.module @Companion_w2(in %_gen_uint: !firrtl.ref<uint<2>>) attributes {
    annotations = [
      {
        class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
        id = 2 : i64,
        name = "View_w2"
      }
    ]
  } {
    %0 = firrtl.ref.resolve %_gen_uint : !firrtl.ref<uint<2>>
    %view_uintrefPort = firrtl.node  %0  {
      annotations = [
        {
          class = "sifive.enterprise.grandcentral.AugmentedGroundType",
          id = 3 : i64
        }
      ]
    } : !firrtl.uint<2>
  }
  firrtl.module private @DUT() attributes {
    annotations = [
      {
        class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
        id = 0 : i64,
        name = "View_w1"
      },
      {
        class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
        id = 2 : i64,
        name = "View_w2"
      }
    ]
  } {
    %c0_ui2 = firrtl.constant 0 : !firrtl.uint<2>
    %c0_ui1 = firrtl.constant 0 : !firrtl.uint<1>
    %a_w1 = firrtl.wire   {annotations = [{class = "firrtl.transforms.DontTouchAnnotation"}]} : !firrtl.uint<1>
    firrtl.strictconnect %a_w1, %c0_ui1 : !firrtl.uint<1>
    %a_w2 = firrtl.wire   {annotations = [{class = "firrtl.transforms.DontTouchAnnotation"}]} : !firrtl.uint<2>
    firrtl.strictconnect %a_w2, %c0_ui2 : !firrtl.uint<2>
    %companion_w1__gen_uint = firrtl.instance companion_w1  @Companion_w1(in _gen_uint: !firrtl.ref<uint<1>>)
    %companion_w2__gen_uint = firrtl.instance companion_w2  @Companion_w2(in _gen_uint: !firrtl.ref<uint<2>>)
    %0 = firrtl.ref.send %a_w1 : !firrtl.uint<1>
    firrtl.connect %companion_w1__gen_uint, %0 : !firrtl.ref<uint<1>>, !firrtl.ref<uint<1>>
    %1 = firrtl.ref.send %a_w2 : !firrtl.uint<2>
    firrtl.connect %companion_w2__gen_uint, %1 : !firrtl.ref<uint<2>>, !firrtl.ref<uint<2>>
  }
  firrtl.module @Top() {
    firrtl.instance dut  @DUT()
  }
}

// Check that the correct subinterface name is used when aliasing is possible.
// Here, SameName is used twice as a sub-interface name and we need to make sure
// that MyInterface_w2 uses the uniqued name of SameName.
//
// See: https://github.com/llvm/circt/issues/4234

// CHECK-LABEL:  sv.interface @MyInterface_w1 {{.+}} {
// CHECK-NEXT:     sv.verbatim "SameName SameName();"
// CHECK-NEXT:   }
// CHECK-LABEL:  sv.interface @MyInterface_w2 {{.+}} {
// CHECK-NEXT:     sv.verbatim "SameName_0 SameName();"
// CHECK-NEXT:   }

// -----

firrtl.circuit "YAMLOutputEmptyInterface" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"},
    {class = "sifive.enterprise.grandcentral.GrandCentralHierarchyFileAnnotation",
     filename = "gct.yaml"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @YAMLOutputEmptyInterface() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: module {
// CHECK:        sv.verbatim
// CHECK-SAME:      - name: Foo
// CHECK-SAME:        fields: []
// CHECK-SAME:        instances: []
// CHECK-SAME:      {output_file = #hw.output_file<"gct.yaml"
//
// CHECK-NOT:  class = "sifive.enterprise.grandcentral.GrandCentralHierarchyFileAnnotation"

// -----

firrtl.circuit "YAMLOutputTwoInterfaces" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Bar",
     elements = [],
     id = 1 : i64,
     name = "View2"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"},
    {class = "sifive.enterprise.grandcentral.GrandCentralHierarchyFileAnnotation",
     filename = "gct.yaml"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"},
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Bar",
       id = 1 : i64,
       name = "View2"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"},
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 1 : i64,
       name = "view"}]} {
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @YAMLOutputTwoInterfaces() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: module {
// CHECK:        sv.verbatim
// CHECK-SAME:      - name: Foo
// CHECK-SAME:        fields: []
// CHECK-SAME:        instances: []
// CHECK-SAME:      - name: Bar
// CHECK-SAME:        fields: []
// CHECK-SAME:        instances: []

// -----

firrtl.circuit "YAMLOutputScalarField" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
        description = "description of foo",
        name = "foo",
        id = 1 : i64}
     ],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"},
    {class = "sifive.enterprise.grandcentral.GrandCentralHierarchyFileAnnotation",
     filename = "gct.yaml"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %a = firrtl.wire {annotations = [
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 1 : i64}]} : !firrtl.uint<2>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @YAMLOutputScalarField() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: module {
// CHECK:        sv.verbatim
// CHECK-SAME:      - name: Foo
// CHECK-SAME:        fields:
// CHECK-SAME:          - name: foo
// CHECK-SAME:            description: description of foo
// CHECK-SAME:            dimensions: [ ]
// CHECK-SAME:            width: 2
// CHECK-SAME:        instances: []
//
// Note: Built-in vector serialization works slightly differently than
// user-defined vector serialization.  This results in the verbose "[ ]" for the
// empty dimensions vector, and the terse "[]" for the empty instances vector.

// -----

firrtl.circuit "YAMLOutputVectorField" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedVectorType",
        elements = [
          {class = "sifive.enterprise.grandcentral.AugmentedVectorType",
           elements = [
             {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
             id = 1 : i64,
             name = "foo"}],
           name = "foo"
          },
          {class = "sifive.enterprise.grandcentral.AugmentedVectorType",
           elements = [
             {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
             id = 2 : i64,
             name = "foo"}],
           name = "foo"
          }],
        name = "foo"}],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"},
    {class = "sifive.enterprise.grandcentral.GrandCentralHierarchyFileAnnotation",
     filename = "gct.yaml"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %a = firrtl.wire {annotations = [
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 1 : i64},
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 2 : i64}]} : !firrtl.uint<8>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @YAMLOutputVectorField() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: module {
// CHECK:        sv.verbatim
// CHECK-SAME:      - name: Foo
// CHECK-SAME:        fields:
// CHECK-SAME:          - name: foo
// CHECK-SAME:            dimensions: [ 1, 2 ]
// CHECK-SAME:            width: 8
// CHECK-SAME:        instances: []

// -----

firrtl.circuit "YAMLOutputInstance" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
     defName = "Foo",
     elements = [
       {class = "sifive.enterprise.grandcentral.AugmentedBundleType",
        defName = "Bar",
        elements = [
          {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
           id = 1 : i64,
           name = "baz"}],
        name = "bar"}],
     id = 0 : i64,
     name = "View"},
    {class = "sifive.enterprise.grandcentral.ExtractGrandCentralAnnotation",
     directory = "gct-dir",
     filename = "bindings.sv"},
    {class = "sifive.enterprise.grandcentral.GrandCentralHierarchyFileAnnotation",
     filename = "gct.yaml"}]} {
  firrtl.module private @View_companion() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.companion",
       defName = "Foo",
       id = 0 : i64,
       name = "View"}]} {}
  firrtl.module private @DUT() attributes {
    annotations = [
      {class = "sifive.enterprise.grandcentral.ViewAnnotation.parent",
       id = 0 : i64,
       name = "view"}
    ]} {
    %a = firrtl.wire {annotations = [
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 1 : i64},
      {class = "sifive.enterprise.grandcentral.AugmentedGroundType",
       id = 2 : i64}]} : !firrtl.uint<8>
    firrtl.instance View_companion @View_companion()
  }
  firrtl.module @YAMLOutputInstance() {
    firrtl.instance dut @DUT()
  }
}

// CHECK-LABEL: module {
// CHECK:        sv.verbatim
// CHECK-SAME:      - name: Foo
// CHECK-SAME:        fields: []
// CHECK-SAME:        instances:
// CHECK-SAME:          - name: bar
// CHECK-SAME:            dimensions: [ ]
// CHECK-SAME:            interface:
// CHECK-SAME:              name: Bar
// CHECK-SAME:              fields:
// CHECK-SAME:                - name: baz
// CHECK-SAME:                  dimensions: [ ]
// CHECK-SAME:                  width: 8
// CHECK-SAME:              instances: []

// -----

firrtl.circuit "NoInterfaces" attributes {
  annotations = [
    {class = "sifive.enterprise.grandcentral.GrandCentralHierarchyFileAnnotation",
     filename = "gct.yaml"}]} {
  firrtl.module @NoInterfaces() {}
}

// CHECK-LABEL: module {
// CHECK:         sv.verbatim
// CHECK-SAME:      []

// -----

firrtl.circuit "Top"  attributes {annotations = [{class = "sifive.enterprise.grandcentral.AugmentedBundleType", defName = "MyInterface", elements = [{class = "sifive.enterprise.grandcentral.AugmentedGroundType", description = "a wire called 'uint'", id = 1 : i64, name = "uint"}, {class = "sifive.enterprise.grandcentral.AugmentedVectorType", description = "a vector called 'vec'", elements = [{class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 2 : i64, name = "vec"}, {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 3 : i64, name = "vec"}], name = "vec"}, {class = "sifive.enterprise.grandcentral.AugmentedGroundType", description = "a wire called 'uint'", id = 4 : i64, name = "old"}], id = 0 : i64, name = "MyView"}]} {
  firrtl.extmodule private @Tap(out clock: !firrtl.clock, out a: !firrtl.uint<1>, in b: !firrtl.uint<1>)
  // CHECK-LABEL: firrtl.module private @MyView_companion
  firrtl.module private @MyView_companion(in %_gen_uint: !firrtl.ref<uint<1>>, in %_gen_vec: !firrtl.ref<uint<1>>, in %_gen_vec_0: !firrtl.ref<uint<1>>) attributes {annotations = [{class = "sifive.enterprise.grandcentral.ViewAnnotation.companion", id = 0 : i64, name = "MyView", type = "companion.companion"}]} {
    %0 = firrtl.ref.resolve %_gen_uint : !firrtl.ref<uint<1>>
    %view_uintrefPort = firrtl.node  %0  {annotations = [{class = "firrtl.transforms.DontTouchAnnotation"}, {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 1 : i64}]} : !firrtl.uint<1>
    %1 = firrtl.ref.resolve %_gen_vec : !firrtl.ref<uint<1>>
    %view_vecrefPort = firrtl.node  %1  {annotations = [{class = "firrtl.transforms.DontTouchAnnotation"}, {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 2 : i64}]} : !firrtl.uint<1>
    %2 = firrtl.ref.resolve %_gen_vec_0 : !firrtl.ref<uint<1>>
    %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
    %view_vecrefPort_0 = firrtl.node  %c1_ui1  {annotations = [{class = "firrtl.transforms.DontTouchAnnotation"}, {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 3 : i64}]} : !firrtl.uint<1>
    %b = firrtl.wire: !firrtl.uint<1>
    %v1 = firrtl.node sym @v1 %b  {annotations = [{class = "firrtl.transforms.DontTouchAnnotation"}, {class = "sifive.enterprise.grandcentral.AugmentedGroundType", id = 4 : i64}]} : !firrtl.uint<1>
    // CHECK:  %0 = sv.interface.instance sym @__MyView_MyInterface__  {name = "MyView"} : !sv.interface<@MyInterface>
    // CHECK: %view_uintrefPort = firrtl.node %1  : !firrtl.uint<1>
    // CHECK: %view_vecrefPort = firrtl.node %2  : !firrtl.uint<1>
    // CHECK: %view_vecrefPort_0 = firrtl.node %c1_ui1 : !firrtl.uint<1>
    // CHECK{LITERAL}: sv.verbatim "assign {{1}}.uint = {{0}};"(%1) : !firrtl.uint<1> {symbols = [#hw.innerNameRef<@MyView_companion::@__MyView_MyInterface__>]}
    // CHECK{LITERAL}: sv.verbatim "assign {{1}}.vec[0] = {{0}};"(%2) : !firrtl.uint<1> {symbols = [#hw.innerNameRef<@MyView_companion::@__MyView_MyInterface__>]}
    // CHECK{LITERAL}: sv.verbatim "assign {{1}}.vec[1] = {{0}};"(%c1_ui1) : !firrtl.uint<1> {symbols = [#hw.innerNameRef<@MyView_companion::@__MyView_MyInterface__>]}
    // CHECK{LITERAL}: sv.verbatim "assign {{0}}.old = {{1}}.{{2}}.{{3}};" {symbols = [#hw.innerNameRef<@MyView_companion::@__MyView_MyInterface__>, @DUT, #hw.innerNameRef<@DUT::@MyView_companion>, #hw.innerNameRef<@MyView_companion::@v1>]}
  }
  firrtl.module private @DUT(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %in_uint: !firrtl.uint<1>, in %in_vec_0: !firrtl.uint<1>, in %in_vec_1: !firrtl.uint<1>, out %out_uint: !firrtl.uint<1>, out %out_vec_0: !firrtl.uint<1>, out %out_vec_1: !firrtl.uint<1>) attributes {annotations = [{class = "sifive.enterprise.grandcentral.ViewAnnotation.parent", id = 0 : i64, name = "MyView"}]} {
    %c1_ui1 = firrtl.constant 1 : !firrtl.uint<1>
    %MyView_companion__gen_uint, %MyView_companion__gen_vec, %MyView_companion__gen_vec_0 = firrtl.instance MyView_companion  @MyView_companion(in _gen_uint: !firrtl.ref<uint<1>>, in _gen_vec: !firrtl.ref<uint<1>>, in _gen_vec_0: !firrtl.ref<uint<1>>)
  }
  firrtl.module @Top(in %clock: !firrtl.clock, in %reset: !firrtl.uint<1>, in %in_uint: !firrtl.uint<1>, in %in_vec_0: !firrtl.uint<1>, in %in_vec_1: !firrtl.uint<1>, out %out_uint: !firrtl.uint<1>, out %out_vec_0: !firrtl.uint<1>, out %out_vec_1: !firrtl.uint<1>) {
    %dut_clock, %dut_reset, %dut_in_uint, %dut_in_vec_0, %dut_in_vec_1, %dut_out_uint, %dut_out_vec_0, %dut_out_vec_1 = firrtl.instance dut  @DUT(in clock: !firrtl.clock, in reset: !firrtl.uint<1>, in in_uint: !firrtl.uint<1>, in in_vec_0: !firrtl.uint<1>, in in_vec_1: !firrtl.uint<1>, out out_uint: !firrtl.uint<1>, out out_vec_0: !firrtl.uint<1>, out out_vec_1: !firrtl.uint<1>)
  }
}
