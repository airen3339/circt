# RUN: py-split-input-file %s

from pycde import System, Input, Output, module, generator

from pycde.matrix import Matrix
from pycde.dialects import hw
from pycde.pycde_types import types, dim

# Matrix transposition via injected matrix on a ListValue
# Putting this as first test in case users use this file as a reference.
# The majority of tests in this file uses the Matrix directly, but most users
# will probably want to use the Numpy features directly on the ListValue.


@module
class M1:
  in1 = Input(dim(types.i32, 4, 8))
  out = Output(dim(types.i32, 8, 4))

  @generator
  def build(ports):
    ports.out = ports.in1.transpose((1, 0))


m1 = System([M1])
m1.generate()
m1.print()

# -----

# Composing multiple matrix transformations


@module
class M1:
  in1 = Input(dim(types.i32, 4, 8))
  out = Output(dim(types.i32, 2, 16))

  @generator
  def build(ports):
    ports.out = ports.in1.transpose((1, 0)).reshape((16, 2))


m1 = System([M1])
m1.generate()
m1.print()

# -----


@module
class M2:
  in0 = Input(dim(types.i32, 16))
  in1 = Input(types.i32)
  t_c = dim(types.i32, 8, 4)
  c = Output(t_c)

  @generator
  def build(ports):
    # a 32xi32 matrix.
    m = Matrix((32,), dtype=types.i32, name='m2')
    for i in range(16):
      m[i] = ports.in1
    m[16:32] = ports.in0
    m = m.reshape((4, 8))
    ports.c = m.to_circt()


m2 = System([M2])
m2.generate()
m2.print()


# -----
@module
class M1:
  in0 = Input(dim(types.i32, 16))
  in1 = Input(types.i32)
  t_c = dim(types.i32, 16)
  c = Output(t_c)

  @generator
  def build(ports):
    # a 32x32xi1 matrix.
    # A dtype of i32 is fairly expensive wrt. the size of the output IR, but
    # but allows for assigning indiviudal bits.
    m = Matrix((32, 32), dtype=types.i1, name='m1')

    # Assign individual bits to the first 32 bits.
    for i in range(32):
      m[0, i] = hw.ConstantOp(types.i1, 1)

    # Fill the next 15 values with an i32. The Matrix knows how to convert
    # from i32 to <32xi1> to comply with the matrix dtype.
    for i in range(1, 16):
      m[i] = ports.in1

    # Fill the upportmost 16 rows with the input array of in0 : 16xi32
    m[16:32] = ports.in0

    # We don't provide a method of reshaping the matrix wrt. its dtype.
    # that is: 32x32xi1 => 32xi32
    # This has massive overhead in the generated IR, and can be easily
    # achieved by a bitcast.
    ports.c = hw.BitcastOp(M1.t_c, m.to_circt())


m1 = System([M1])
m1.generate()
m1.print()

# -----

# Matrix from value


@module
class M1:
  in1 = Input(dim(types.i32, 10, 10))
  out = Output(dim(types.i32, 10, 10))

  @generator
  def build(ports):
    m = Matrix(from_value=ports.in1, name='m1')
    ports.out = m.to_circt()


m1 = System([M1])
m1.generate()
m1.print()

# -----

# No barrier wire


@module
class M1:
  in1 = Input(dim(types.i32, 10))
  out = Output(dim(types.i32, 10))

  @generator
  def build(ports):
    m = Matrix(from_value=ports.in1, name='m1')
    ports.out = m.to_circt(create_wire=False)


m1 = System([M1])
m1.generate()
m1.print()
