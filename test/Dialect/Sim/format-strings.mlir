// RUN: circt-opt %s --canonicalize | FileCheck %s

// CHECK-LABEL: hw.module @constant_fold0
hw.module @constant_fold0(in %zeroWitdh: i0, out res: !sim.fstring) {
  %comma = sim.fmt.lit ","
  %semicolon = sim.fmt.lit ";"

  %nocat = sim.fmt.concat ()

  %w0b = sim.fmt.bin %zeroWitdh : i0
  %w0u = sim.fmt.dec %zeroWitdh : i0
  %w0s = sim.fmt.dec signed %zeroWitdh : i0
  %w0h = sim.fmt.hex %zeroWitdh : i0
  %catw0 = sim.fmt.concat (%w0b, %comma, %w0u, %comma, %w0s, %comma, %w0h)

  %cst0_1 = hw.constant 0 : i1
  %w1b0 = sim.fmt.bin %cst0_1 : i1
  %w1u0 = sim.fmt.dec %cst0_1 : i1
  %w1s0 = sim.fmt.dec signed %cst0_1 : i1
  %w1h0 = sim.fmt.hex %cst0_1 : i1
  %catw1_0 = sim.fmt.concat (%w1b0, %comma, %w1u0, %comma, %w1s0, %comma, %w1h0)

  %cst1_1 = hw.constant -1 : i1
  %w1b1 = sim.fmt.bin %cst1_1 : i1
  %w1u1 = sim.fmt.dec %cst1_1 : i1
  %w1s1 = sim.fmt.dec signed %cst1_1 : i1
  %w1h1 = sim.fmt.hex %cst1_1 : i1
  %catw1_1 = sim.fmt.concat (%w1b1, %comma, %w1u1, %comma, %w1s1, %comma, %w1h1)

  %cst3_4 = hw.constant 3 : i4
  %w4b3 = sim.fmt.bin %cst3_4 : i4
  %w4u3 = sim.fmt.dec %cst3_4 : i4
  %w4s3 = sim.fmt.dec signed %cst3_4 : i4
  %w4h3 = sim.fmt.hex %cst3_4 : i4
  %catw4_3 = sim.fmt.concat (%w4b3, %comma, %w4u3, %comma, %w4s3, %comma, %w4h3)

  %cst10_5 = hw.constant 10 : i5
  %w5b10 = sim.fmt.bin %cst10_5 : i5
  %w5u10 = sim.fmt.dec %cst10_5 : i5
  %w5s10 = sim.fmt.dec signed %cst10_5 : i5
  %w5h10 = sim.fmt.hex %cst10_5 : i5
  %catw5_10 = sim.fmt.concat (%w5b10, %comma, %w5u10, %comma, %w5s10, %comma, %w5h10)

  %cst128_8 = hw.constant 128 : i8
  %w8b128 = sim.fmt.bin %cst128_8 : i8
  %w8u128 = sim.fmt.dec %cst128_8 : i8
  %w8s128 = sim.fmt.dec signed %cst128_8 : i8
  %w8h128 = sim.fmt.hex %cst128_8 : i8
  %catw8_128 = sim.fmt.concat (%w8b128, %comma, %w8u128, %comma, %w8s128, %comma, %w8h128, %nocat)

  %cstcafe_22 = hw.constant 0xcafe : i22
  %w22bcafe = sim.fmt.bin %cstcafe_22 : i22
  %w22ucafe = sim.fmt.dec %cstcafe_22 : i22
  %w22scafe = sim.fmt.dec signed %cstcafe_22 : i22
  %w22hcafe = sim.fmt.hex %cstcafe_22 : i22
  %catw22_cafe = sim.fmt.concat (%w22bcafe, %comma, %w22ucafe, %comma, %w22scafe, %comma, %w22hcafe)



  %catout = sim.fmt.concat (%catw0, %semicolon, %catw1_0, %semicolon, %catw1_1, %nocat, %semicolon, %catw4_3, %semicolon, %catw5_10, %semicolon, %catw8_128, %semicolon, %catw22_cafe)
  %catcatout = sim.fmt.concat (%catout)
  hw.output %catcatout : !sim.fstring
}

hw.module @constant_fold1(out res: !sim.fstring) {
  %pre = sim.fmt.lit "42@123B-> "
  %preb = sim.fmt.lit " %b: '"
  %preu = sim.fmt.lit " %u: '"
  %pres = sim.fmt.lit " %d: '"
  %preh = sim.fmt.lit " %x: '"
  %q = sim.fmt.lit "'"

  %cst42_123 = hw.constant 42 : i123
  %w123b42 = sim.fmt.bin %cst42_123 : i123
  %w123u42 = sim.fmt.dec %cst42_123 : i123
  %w123s42 = sim.fmt.dec signed %cst42_123 : i123
  %w123h42 = sim.fmt.hex %cst42_123 : i123
  %res = sim.fmt.concat (%pre, %preb, %w123b42, %q, %preu, %w123u42, %q, %pres, %w123s42, %q, %preh, %w123h42, %q)

  hw.output %res : !sim.fstring
}

hw.module @constant_fold2(in %foo: i1027, out res: !sim.fstring) {
  %space = sim.fmt.lit " "
  %dash = sim.fmt.lit "-"
  %spaceDashSpace = sim.fmt.lit " - "
  %hex = sim.fmt.hex %foo : i1027

  %res = sim.fmt.concat (%spaceDashSpace, %hex, %space, %dash, %space)
  hw.output %res : !sim.fstring
}

hw.module @constant_fold3(in %zeroWitdh: i0, out res: !sim.fstring) {
  %F = hw.constant 70 : i7
  %o = hw.constant 111 : i8
  %cr = hw.constant 13 : i4
  %lf = hw.constant 10 : i5
  %ext = hw.constant 200: i8

  %cF = sim.fmt.char %F : i7
  %co = sim.fmt.char %o : i8
  %ccr = sim.fmt.char %cr : i4
  %clf = sim.fmt.char %lf : i5
  %cext = sim.fmt.char %ext : i8

  %null = sim.fmt.char %zeroWitdh : i0
  
  %foo = sim.fmt.concat (%cF, %co, %co)
  %cat = sim.fmt.concat (%foo, %ccr, %clf, %null, %foo, %null, %cext)
  hw.output %cat : !sim.fstring
}