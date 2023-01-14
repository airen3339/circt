# RUN: %PYTHON% %s 2>err.txt | FileCheck %s
# RUN: cat err.txt | FileCheck --check-prefix=ERR %s

from pycde import dim, types
from pycde.circt.ir import Module

# CHECK: [('foo', Type(i1)), ('bar', Type(i13))]
# ERR: i1
st1 = types.struct({"foo": types.i1, "bar": types.i13})
print(st1.fields)
st1.foo.dump()
print()

# ERR: i6
array1 = dim(types.i6)
array1.dump()
print()
# CHECK: i6
print(array1)

# ERR: !hw.array<12xarray<10xi6>>
array2 = dim(6, 10, 12)
array2.dump()
print()
# CHECK: [12][10]i6
print(array2)

# ERR: !hw.typealias<@pycde::@myname1, i8>
int_alias = types.int(8, "myname1")
int_alias.dump()
print()
# CHECK: myname1
print(int_alias)

# ERR: !hw.typealias<@pycde::@myname1, i8>
int_alias = types.int(8, "myname1")
int_alias.dump()
print()

# ERR: !hw.typealias<@pycde::@myname2, i8>
int_alias = types.int(8, "myname2")
int_alias.dump()
print()

# ERR: !hw.typealias<@pycde::@myname3, !hw.array<8xi1>>
array_alias = types.array(types.i1, 8, "myname3")
array_alias.dump()
print()

# ERR: !hw.typealias<@pycde::@myname4, !hw.struct<a: i1, b: i1>>
struct_alias = types.struct({"a": types.i1, "b": types.i1}, "myname4")
struct_alias.dump()
print()

# ERR: !hw.typealias<@pycde::@myname5, !hw.array<8xi1>
dim_alias = dim(1, 8, name="myname5")
dim_alias.dump()
print()

# CHECK: hw.type_scope @pycde
# CHECK: hw.typedecl @myname1 : i8
# CHECK: hw.typedecl @myname2 : i8
# CHECK: hw.typedecl @myname3 : !hw.array<8xi1>
# CHECK: hw.typedecl @myname4 : !hw.struct<a: i1, b: i1>
# CHECK: hw.typedecl @myname5 : !hw.array<8xi1>
# CHECK-NOT: hw.typedecl @myname1
# CHECK-NOT: hw.typedecl @myname2
# CHECK-NOT: hw.typedecl @myname3
# CHECK-NOT: hw.typedecl @myname4
# CHECK-NOT: hw.typedecl @myname5
m = Module.create()
types.declare_types(m)
types.declare_types(m)
print(m)
