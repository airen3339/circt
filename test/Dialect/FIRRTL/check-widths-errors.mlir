// RUN: circt-opt --pass-pipeline='firrtl.circuit(firrtl.module(firrtl-check-widths))' --verify-diagnostics --split-input-file %s

firrtl.circuit "Foo" {
  firrtl.module @Foo () {
    // expected-error @+2 {{uninferred width: type '!firrtl.uint'}}
    // expected-note @+1 {{in result of `firrtl.wire`}}
    %0 = firrtl.wire : !firrtl.uint
  }
}

// -----

firrtl.circuit "Foo" {
  firrtl.module @Foo () {
    // expected-error @+2 {{uninferred width: type '!firrtl.vector<uint, 16>'}}
    // expected-note @+1 {{in result of `firrtl.wire`}}
    %1 = firrtl.wire : !firrtl.vector<uint, 16>
  }
}

// -----

firrtl.circuit "Foo" {
  firrtl.module @Foo () {
    // expected-error @+3 {{uninferred width: type '!firrtl.uint'}}
    // expected-note @+2 {{in result of `firrtl.wire`}}
    // expected-note @+1 {{in bundle field `a`}}
    %2 = firrtl.wire : !firrtl.bundle<a: uint>
  }
}

// -----

firrtl.circuit "Foo" {
  firrtl.module @Foo () {
    // expected-error @+5 {{uninferred width: type '!firrtl.flip<uint>'}}
    // expected-note @+4 {{in result of `firrtl.wire`}}
    // expected-note @+3 {{in bundle field `a`}}
    // expected-note @+2 {{in bundle field `b`}}
    // expected-note @+1 {{in bundle field `c`}}
    %3 = firrtl.wire : !firrtl.bundle<a: bundle<b: bundle<c: flip<uint>, d: uint<1>>>>
  }
}
