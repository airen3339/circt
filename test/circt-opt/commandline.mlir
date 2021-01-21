// RUN: circt-opt --help | FileCheck %s --check-prefix=HELP
// RUN: circt-opt --show-dialects | FileCheck %s --check-prefix=DIALECT

// HELP: OVERVIEW: CIRCT modular optimizer driver

// DIALECT: Available Dialects:
// DIALECT-NEXT: affine
// DIALECT-NEXT: esi
// DIALECT-NEXT: firrtl
// DIALECT-NEXT: handshake
// DIALECT-NEXT: llhd
// DIALECT-NEXT: llvm
// DIALECT-NEXT: rtl
// DIALECT-NEXT: staticlogic
// DIALECT-NEXT: std
// DIALECT-NEXT: sv