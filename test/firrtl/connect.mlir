// RUN: circt-opt %s -split-input-file -verify-diagnostics

/// Analog types cannot be connected and must be attached.

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.analog, %b : !firrtl.flip<analog>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<analog>' and source '!firrtl.analog'}}
  firrtl.connect %b, %a : !firrtl.flip<analog>, !firrtl.analog
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.analog, %b : !firrtl.flip<uint<1>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<uint<1>>' and source '!firrtl.analog'}}
  firrtl.connect %b, %a : !firrtl.flip<uint<1>>, !firrtl.analog
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.uint<1>, %b : !firrtl.flip<analog>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<analog>' and source '!firrtl.uint<1>'}}
  firrtl.connect %b, %a : !firrtl.flip<analog>, !firrtl.uint<1>
}

}

/// Reset types can be connected to Reset, UInt<1>, or AsyncReset types.

// Reset source.

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.reset, %b : !firrtl.flip<reset>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<reset>, !firrtl.reset
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.reset, %b : !firrtl.flip<uint<1>>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<uint<1>>, !firrtl.reset
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.reset, %b : !firrtl.flip<asyncreset>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<asyncreset>, !firrtl.reset
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.reset, %b : !firrtl.flip<uint<2>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<uint<2>>' and source '!firrtl.reset'}}
  firrtl.connect %b, %a : !firrtl.flip<uint<2>>, !firrtl.reset
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.reset, %b : !firrtl.flip<sint<1>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<sint<1>>' and source '!firrtl.reset'}}
  firrtl.connect %b, %a : !firrtl.flip<sint<1>>, !firrtl.reset
}

}

// Reset destination.

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.uint<1>, %b : !firrtl.flip<reset>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<reset>, !firrtl.uint<1>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.asyncreset, %b : !firrtl.flip<reset>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<reset>, !firrtl.asyncreset
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.uint<2>, %b : !firrtl.flip<reset>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<reset>' and source '!firrtl.uint<2>'}}
  firrtl.connect %b, %a : !firrtl.flip<reset>, !firrtl.uint<2>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.sint<1>, %b : !firrtl.flip<reset>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<reset>' and source '!firrtl.sint<1>'}}
  firrtl.connect %b, %a : !firrtl.flip<reset>, !firrtl.sint<1>
}

}

/// Ground types can be connected if they are the same ground type.

// UInt<> source.

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.uint<1>, %b : !firrtl.flip<uint<1>>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<uint<1>>, !firrtl.uint<1>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.uint<1>, %b : !firrtl.flip<sint<1>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<sint<1>>' and source '!firrtl.uint<1>'}}
  firrtl.connect %b, %a : !firrtl.flip<sint<1>>, !firrtl.uint<1>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.uint<1>, %b : !firrtl.flip<clock>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<clock>' and source '!firrtl.uint<1>'}}
  firrtl.connect %b, %a : !firrtl.flip<clock>, !firrtl.uint<1>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.uint<1>, %b : !firrtl.flip<asyncreset>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<asyncreset>' and source '!firrtl.uint<1>'}}
  firrtl.connect %b, %a : !firrtl.flip<asyncreset>, !firrtl.uint<1>
}

}

// SInt<> source.

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.sint<1>, %b : !firrtl.flip<sint<1>>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<sint<1>>, !firrtl.sint<1>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.sint<1>, %b : !firrtl.flip<uint<1>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<uint<1>>' and source '!firrtl.sint<1>'}}
  firrtl.connect %b, %a : !firrtl.flip<uint<1>>, !firrtl.sint<1>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.sint<1>, %b : !firrtl.flip<clock>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<clock>' and source '!firrtl.sint<1>'}}
  firrtl.connect %b, %a : !firrtl.flip<clock>, !firrtl.sint<1>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.sint<1>, %b : !firrtl.flip<asyncreset>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<asyncreset>' and source '!firrtl.sint<1>'}}
  firrtl.connect %b, %a : !firrtl.flip<asyncreset>, !firrtl.sint<1>
}

}

// Clock source.

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.clock, %b : !firrtl.flip<clock>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<clock>, !firrtl.clock
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.clock, %b : !firrtl.flip<uint<1>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<uint<1>>' and source '!firrtl.clock'}}
  firrtl.connect %b, %a : !firrtl.flip<uint<1>>, !firrtl.clock
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.clock, %b : !firrtl.flip<sint<1>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<sint<1>>' and source '!firrtl.clock'}}
  firrtl.connect %b, %a : !firrtl.flip<sint<1>>, !firrtl.clock
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.clock, %b : !firrtl.flip<asyncreset>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<asyncreset>' and source '!firrtl.clock'}}
  firrtl.connect %b, %a : !firrtl.flip<asyncreset>, !firrtl.clock
}

}

// AsyncReset source.

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.asyncreset, %b : !firrtl.flip<asyncreset>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<asyncreset>, !firrtl.asyncreset
}

}
// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.asyncreset, %b : !firrtl.flip<uint<1>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<uint<1>>' and source '!firrtl.asyncreset'}}
  firrtl.connect %b, %a : !firrtl.flip<uint<1>>, !firrtl.asyncreset
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.asyncreset, %b : !firrtl.flip<sint<1>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<sint<1>>' and source '!firrtl.asyncreset'}}
  firrtl.connect %b, %a : !firrtl.flip<sint<1>>, !firrtl.asyncreset
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.asyncreset, %b : !firrtl.flip<clock>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<clock>' and source '!firrtl.asyncreset'}}
  firrtl.connect %b, %a : !firrtl.flip<clock>, !firrtl.asyncreset
}

}

/// Vector types can be connected if they have the same size and element type.

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.vector<uint<1>, 3>, %b : !firrtl.flip<vector<uint<1>, 3>>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.flip<vector<uint<1>, 3>>, !firrtl.vector<uint<1>, 3>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.vector<uint<1>, 3>, %b : !firrtl.flip<vector<uint<1>, 2>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<vector<uint<1>, 2>>' and source '!firrtl.vector<uint<1>, 3>'}}
  firrtl.connect %b, %a : !firrtl.flip<vector<uint<1>, 2>>, !firrtl.vector<uint<1>, 3>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.vector<uint<1>, 3>, %b : !firrtl.flip<vector<sint<1>, 3>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<vector<sint<1>, 3>>' and source '!firrtl.vector<uint<1>, 3>'}}
  firrtl.connect %b, %a : !firrtl.flip<vector<sint<1>, 3>>, !firrtl.vector<uint<1>, 3>
}

}

/// Bundle types can be connected if they have the same size, element names, and
/// element types.

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.bundle<f1: uint<1>, f2: flip<sint<1>>>, %b : !firrtl.bundle<f1: flip<uint<1>>, f2: sint<1>>) {
  // CHECK: firrtl.connect %b, %a
  firrtl.connect %b, %a : !firrtl.bundle<f1: flip<uint<1>>, f2: sint<1>>, !firrtl.bundle<f1: uint<1>, f2: flip<sint<1>>>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.bundle<f1: uint<1>>, %b : !firrtl.bundle<f1: flip<uint<1>>, f2: sint<1>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.bundle<f1: flip<uint<1>>, f2: sint<1>>' and source '!firrtl.bundle<f1: uint<1>>'}}
  firrtl.connect %b, %a : !firrtl.bundle<f1: flip<uint<1>>, f2: sint<1>>, !firrtl.bundle<f1: uint<1>>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.bundle<f1: uint<1>>, %b : !firrtl.bundle<f2: flip<uint<1>>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<bundle<f2: uint<1>>>' and source '!firrtl.bundle<f1: uint<1>>'}}
  firrtl.connect %b, %a : !firrtl.bundle<f2: flip<uint<1>>>, !firrtl.bundle<f1: uint<1>>
}

}

// -----

firrtl.circuit "test" {

firrtl.module @test(%a : !firrtl.bundle<f1: uint<1>>, %b : !firrtl.bundle<f1: flip<sint<1>>>) {
  // expected-error @+1 {{type mismatch between destination '!firrtl.flip<bundle<f1: sint<1>>>' and source '!firrtl.bundle<f1: uint<1>>'}}
  firrtl.connect %b, %a : !firrtl.bundle<f1: flip<sint<1>>>, !firrtl.bundle<f1: uint<1>>
}

}
