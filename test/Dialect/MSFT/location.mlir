// RUN: circt-opt %s -verify-diagnostics | circt-opt -verify-diagnostics | FileCheck %s
// RUN: circt-translate %s --export-quartus-tcl | FileCheck %s --check-prefix=TCL

hw.module.extern @Foo()

// CHECK-LABEL: hw.module @leaf
hw.module @leaf() {
  // CHECK: hw.instance "foo" @Foo() -> () {"loc:memBank2" = #msft.switch.inst<@shallow["leaf"]=#msft.physloc<M20K, 8, 19, 1>, @deeper["branch","leaf"]=#msft.physloc<M20K, 15, 9, 3>>} 
  hw.instance "foo" @Foo() -> () {
    "loc:memBank2" = #msft.switch.inst< @shallow["leaf"]=#msft.physloc<M20K, 8, 19, 1>,
                                        @deeper["branch","leaf"]=#msft.physloc<M20K, 15, 9, 3> > }
}

// TCL-LABEL: proc shallow_config
hw.module @shallow() {
  hw.instance "leaf" @leaf() -> ()
  // TCL: set_location_assignment M20K_X8_Y19_N1 -to $parent|leaf|foo|memBank2
}

// TCL-LABEL: proc deeper_config
hw.module @deeper() {
  hw.instance "branch" @shallow() -> ()
  hw.instance "leaf" @leaf() -> ()
  // TCL: set_location_assignment M20K_X15_Y9_N3 -to $parent|branch|leaf|foo|memBank2
}
