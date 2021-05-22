# REQUIRES: bindings_python
# RUN: %PYTHON% %s | FileCheck %s

import circt
from circt.design_entry import connect
from circt.dialects import hw

from mlir.ir import *
from mlir.passmanager import PassManager

import sys

with Context() as ctx, Location.unknown():
  circt.register_dialects(ctx)

  i32 = IntegerType.get_signless(32)

  # CHECK: !hw.array<5xi32>
  array_i32 = hw.ArrayType.get(i32, 5)
  print(array_i32)
  # CHECK: i32
  print(array_i32.element_type)

  # CHECK: !hw.struct<foo: i32, bar: !hw.array<5xi32>>
  struct = hw.StructType.get([("foo", i32), ("bar", array_i32)])
  print(struct)

  # CHECK: !hw.struct<baz: i32, qux: !hw.array<5xi32>>
  struct = hw.StructType.get([("baz", i32), ("qux", array_i32)])
  print(struct)

  m = Module.create()
  with InsertionPoint(m.body):
    # CHECK: hw.module @MyWidget(%my_input: i32) -> (%my_output: i32)
    # CHECK:   hw.output %my_input : i32
    op = hw.HWModuleOp(name='MyWidget',
                       input_ports=[('my_input', i32)],
                       output_ports=[('my_output', i32)],
                       body_builder=lambda module, my_input:
                           hw.OutputOp([my_input]))

    # CHECK: hw.module.extern @FancyThing(%input0: i32) -> (%output0: i32)
    extern = hw.HWModuleExternOp(name="FancyThing",
                                 input_ports=[("input0", i32)],
                                 output_ports=[("output0", i32)])

    # CHECK: hw.module @swap(%a: i32, %b: i32) -> (%{{.+}}: i32, %{{.+}}: i32)
    # CHECK:   hw.output %b, %a : i32, i32
    @hw.HWModuleOp.from_py_func(i32, i32)
    def swap(a, b):
      return b, a

    # CHECK: hw.module @top(%a: i32, %b: i32) -> (%{{.+}}: i32, %{{.+}}: i32)
    # CHECK:   %[[a0:.+]], %[[b0:.+]] = hw.instance "" @swap(%a, %b)
    # CHECK:   %[[a1:.+]], %[[b1:.+]] = hw.instance "" @swap(%[[a0]], %[[b0]])
    # CHECK:   hw.output %[[a1:.+]], %[[b1:.+]] : i32, i32
    @hw.HWModuleOp.from_py_func(i32, i32)
    def top(a, b):
      a, b = swap(a, b)
      a, b = swap(a, b)
      return a, b

    one_input = hw.HWModuleOp(
        name="one_input",
        input_ports=[("a", i32)],
        body_builder=lambda m, a: hw.OutputOp([]),
    )
    two_inputs = hw.HWModuleOp(
        name="two_inputs",
        input_ports=[("a", i32), ("b", i32)],
        body_builder=lambda m, a, b: hw.OutputOp([]),
    )
    one_output = hw.HWModuleOp(
        name="one_output",
        output_ports=[("a", i32)],
        body_builder=lambda m: hw.OutputOp(
            [hw.ConstantOp(i32, IntegerAttr.get(i32, 46)).result]),
    )

    # CHECK-LABEL: hw.module @instance_builder_tests
    def instance_builder_body(module):
      # CHECK: %[[INST1_RESULT:.+]] = hw.instance "inst1" @one_output()
      inst1 = one_output.create("inst1")

      # CHECK: hw.instance "inst2" @one_input(%[[INST1_RESULT]])
      inst2 = one_input.create("inst2", {"a": inst1.a})

      # CHECK: hw.instance "inst4" @two_inputs(%[[INST1_RESULT]], %[[INST1_RESULT]])
      inst4 = two_inputs.create("inst4", {"a": inst1.a})
      connect(inst4.b, inst1.a)

      # CHECK: %[[INST5_RESULT:.+]] = hw.instance "inst5" @MyWidget(%[[INST5_RESULT]])
      inst5 = op.create("inst5")
      connect(inst5.my_input, inst5.my_output)

      # CHECK: hw.instance "inst6" {{.*}} {BANKS = 2 : i64}
      one_input.create("inst6", {"a": inst1.a}, parameters={"BANKS": 2})

      hw.OutputOp([])

    instance_builder_tests = hw.HWModuleOp(name="instance_builder_tests",
                                           body_builder=instance_builder_body)

    # CHECK: hw.module @block_args_test(%[[PORT_NAME:.+]]: i32) ->
    # CHECK: hw.output %[[PORT_NAME]]
    hw.HWModuleOp(name="block_args_test",
                  input_ports=[("foo", i32)],
                  output_ports=[("bar", i32)],
                  body_builder=lambda module, foo: hw.OutputOp([foo]))

  print(m)

  # CHECK-LABEL: === Verilog ===
  print("=== Verilog ===")

  pm = PassManager.parse("hw-legalize-names,hw.module(hw-cleanup)")
  pm.run(m)
  # CHECK: module MyWidget
  # CHECK: external module FancyThing
  # CHECK: module swap
  # CHECK: module top
  circt.export_verilog(m, sys.stdout)
