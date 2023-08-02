// RUN: circt-opt %s | FileCheck %s

firrtl.circuit "Classes" {
  firrtl.module @Classes() {}

  // CHECK-LABEL: firrtl.class @StringPassThru(in %in_str: !firrtl.string, out %out_str: !firrtl.string) 
  firrtl.class @StringPassThru(in %in_str: !firrtl.string, out %out_str: !firrtl.string) {
    // CHECK: firrtl.propassign %out_str, %in_str : !firrtl.string
    firrtl.propassign %out_str, %in_str : !firrtl.string
  }

  // CHECK-LABEL: firrtl.module @ModuleWithObjectPort(in %in: !firrtl.class<@StringPassThru(in in_str: !firrtl.string, out out_str: !firrtl.string)>) 
  firrtl.module @ModuleWithObjectPort(in %in: !firrtl.class<@StringPassThru(in in_str: !firrtl.string, out out_str: !firrtl.string)>) {}
}
