#  Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
#  See https://llvm.org/LICENSE.txt for license information.
#  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

from contextlib import AbstractContextManager


class BackedgeBuilder(AbstractContextManager):

  def __init__(self):
    self.edges = []
    self.builders = {}

  def create(self, type, instance_builder):
    from mlir.ir import Operation

    edge = Operation.create("TemporaryBackedge", [type]).result
    self.edges.append(edge)
    self.builders[repr(edge)] = instance_builder
    return edge

  def remove(self, edge):
    self.edges.remove(edge)
    self.builders.pop(repr(edge))
    edge.owner.erase()

  def __exit__(self, exc_type, exc_value, traceback):
    errors = []
    for edge in self.edges:
      # Build a nice error message about the uninitialized port.
      builder = self.builders[repr(edge)]
      instance = builder.operation
      module = builder.module

      for i in range(len(instance.operands)):
        if instance.operands[i] == edge:
          from mlir.ir import ArrayAttr, StringAttr
          arg_names = ArrayAttr(module.attributes["argNames"])
          port_name = "%" + StringAttr(arg_names[i]).value

      assert port_name, "Could not look up port name for backedge"

      msg = "Port:     " + port_name + "\n"
      msg += "Instance: " + str(instance) + "\n"
      msg += "Module:   " + str(module).split(" {")[0]

      # Clean up the IR and Python references.
      instance.erase()
      self.remove(edge)

      errors.append(msg)

    if errors:
      errors.insert(0, "Uninitialized ports remain in circuit!")
      raise RuntimeError("\n".join(errors))
