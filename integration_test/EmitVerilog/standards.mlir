// REQUIRES: verilator
// REQUIRES: quartus

// RUN: firtool --lower-to-rtl --verilog %s > %t1.1995.v
// RUN: firtool --lower-to-rtl --verilog %s > %t1.2001.v
// RUN: firtool --lower-to-rtl --verilog %s > %t1.2005.v
// RUN: firtool --lower-to-rtl --verilog %s > %t1.2005.sv
// RUN: firtool --lower-to-rtl --verilog %s > %t1.2009.sv
// RUN: firtool --lower-to-rtl --verilog %s > %t1.2012.sv
// RUN: firtool --lower-to-rtl --verilog %s> %t1.2017.sv

// RUN: verilator --lint-only +1364-1995ext+v %t1.1995.v || true
// RUN: verilator --lint-only +1364-2001ext+v %t1.2001.v || true
// RUN: verilator --lint-only +1364-2005ext+v %t1.2005.v || true
// RUN: verilator --lint-only +1800-2005ext+sv %t1.2005.sv
// RUN: verilator --lint-only +1800-2009ext+sv %t1.2009.sv
// RUN: verilator --lint-only +1800-2012ext+sv %t1.2012.sv
// RUN: verilator --lint-only +1800-2017ext+sv %t1.2017.sv

// RUN: vlog -lint %t1.1995.v -vlog95compat || true
// RUN: vlog -lint %t1.2001.v -vlog01compat || true
// RUN: vlog -lint %t1.2005.v || true
// RUN: vlog -lint -sv -sv05compat %t1.2005.sv
// RUN: vlog -lint -sv -sv09compat %t1.2009.sv
// RUN: vlog -lint -sv -sv12compat %t1.2012.sv
// RUN: vlog -lint -sv -sv17compat %t1.2017.sv

rtl.module @top(%clock : i1, %reset: i1,
                %a: i4, 
                %s: !rtl.struct<foo: i2, bar: i4>,
                %parray: !rtl.array<10xi4>,
                %uarray: !rtl.uarray<16xi8>
                ) -> (%r0: i4, %r1: i4) {
  %0 = comb.or %a, %a : i4
  %1 = comb.and %a, %a : i4

  sv.always posedge %clock, negedge %reset {
  }

  sv.alwaysff(posedge %clock) {
    sv.fwrite "Yo\n"
  }
  
  rtl.output %0, %1 : i4, i4
}
