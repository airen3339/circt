#rd = {rd_latency=1}
#wr = {wr_latency=1}
#reg_wr = {wr_latency=1}
#reg_rw = {rd_latency=0, wr_latency=1}

hir.func @test at %t(
%a :!hir.memref<16x16x(bank 2)x(bank 2)xf32> ports [#rd,#wr],
%b : i32
){

  %0 = constant 0:index
  %1 = constant 1:index
  %c1_i4 = constant 1:i4
  %c1_f32 = constant 1.0:f32

  %v = hir.load %a[port 0][%c1_i4,%c1_i4,%0,%1]  at %t: !hir.memref<16x16x(bank 2)x(bank 2)xf32> delay 1
  hir.store %v to %a[port 1][%c1_i4,%c1_i4,%0,%0] at %t + 1: !hir.memref<16x16x(bank 2)x(bank 2)xf32> delay 1

  hir.return
}


hir.func @test2 at %t(){
  %0 = constant 0:index
  %1 = constant 1:index
  %c1_i1 = constant 1:i1
  %c1_i2 = constant 1:i2
  %c1_f32 = constant 1.0:f32

  %a = hir.alloca("BRAM_2P") : !hir.memref<(bank 2)x(bank 3)x2x4xi8> ports [#reg_rw,#reg_wr]
  %v = hir.load %a[port 0][%0,%1,%c1_i1,%c1_i2]  at %t: !hir.memref<(bank 2)x(bank 3)x2x4xi8> delay 1
  hir.store %v to %a[port 1][%0,%0,%c1_i1,%c1_i2] at %t + 1: !hir.memref<(bank 2)x(bank 3)x2x4xi8> delay 1
}
