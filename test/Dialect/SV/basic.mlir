// RUN: circt-opt %s | FileCheck %s
// RUN: circt-opt %s | circt-opt | FileCheck %s

// CHECK-LABEL: rtl.module @test1(%arg0: i1, %arg1: i1, %arg8: i8) {
rtl.module @test1(%arg0: i1, %arg1: i1, %arg8: i8) {

  // This corresponds to this block of system verilog code:
  //    always @(posedge arg0) begin
  //      `ifndef SYNTHESIS
  //         if (`PRINTF_COND_ && arg1) $fwrite(32'h80000002, "Hi\n");
  //      `endif
  //    end // always @(posedge)

  sv.always posedge  %arg0 {
    sv.ifdef.procedural "SYNTHESIS" {
    } else {
      %tmp = sv.verbatim.expr "PRINTF_COND_" : () -> i1
      %tmpx = sv.constantX : i1
      %tmpz = sv.constantZ : i1
      %tmp2 = comb.and %tmp, %tmpx, %tmpz, %arg1 : i1
      sv.if %tmp2 {
        sv.fwrite "Hi\n" 
      }
      sv.if %tmp2 {
        // Test fwrite with operands.
        sv.fwrite "%x"(%tmp2) : i1
      } else {
        sv.fwrite "There\n"
      }
    }
  }

  // CHECK-NEXT: sv.always posedge %arg0 {
  // CHECK-NEXT:   sv.ifdef.procedural "SYNTHESIS" {
  // CHECK-NEXT:   } else {
  // CHECK-NEXT:     %PRINTF_COND_ = sv.verbatim.expr "PRINTF_COND_" : () -> i1
  // CHECK-NEXT:     %x_i1 = sv.constantX : i1
  // CHECK-NEXT:     %z_i1 = sv.constantZ : i1
  // CHECK-NEXT:     %0 = comb.and %PRINTF_COND_, %x_i1, %z_i1, %arg1 : i1
  // CHECK-NEXT:     sv.if %0 {
  // CHECK-NEXT:       sv.fwrite "Hi\0A" 
  // CHECK-NEXT:     }
  // CHECK-NEXT:     sv.if %0 {
  // CHECK-NEXT:       sv.fwrite "%x"(%0) : i1
  // CHECK-NEXT:     } else {
  // CHECK-NEXT:       sv.fwrite "There\0A" 
  // CHECK-NEXT:     }
  // CHECK-NEXT:   }
  // CHECK-NEXT: }

  sv.alwaysff(posedge %arg0) {
    sv.fwrite "Yo\n"
  }

  // CHECK-NEXT: sv.alwaysff(posedge %arg0)  {
  // CHECK-NEXT:   sv.fwrite "Yo\0A"
  // CHECK-NEXT: }

  sv.alwaysff(posedge %arg0) {
    sv.fwrite "Sync Main Block\n"
  } ( syncreset : posedge %arg1) {
    sv.fwrite "Sync Reset Block\n"
  } 

  // CHECK-NEXT: sv.alwaysff(posedge %arg0) {
  // CHECK-NEXT:   sv.fwrite "Sync Main Block\0A"
  // CHECK-NEXT:  }(syncreset : posedge %arg1) {
  // CHECK-NEXT:   sv.fwrite "Sync Reset Block\0A"
  // CHECK-NEXT: } 

  sv.alwaysff (posedge %arg0) {
    sv.fwrite "Async Main Block\n"
  } ( asyncreset : negedge %arg1) {
    sv.fwrite "Async Reset Block\n"
  }

  // CHECK-NEXT: sv.alwaysff(posedge %arg0) {
  // CHECK-NEXT:   sv.fwrite "Async Main Block\0A"
  // CHECK-NEXT:  }(asyncreset : negedge %arg1) {
  // CHECK-NEXT:   sv.fwrite "Async Reset Block\0A"
  // CHECK-NEXT: } 

// Smoke test generic syntax.
  sv.initial {
    "sv.if"(%arg0) ( {
      "sv.yield"() : () -> ()
    }, {
      "sv.yield"() : () -> ()
    }) : (i1) -> ()
  }

  // CHECK-NEXT:     sv.initial {
  // CHECK-NEXT:       sv.if %arg0 {
  // CHECK-NEXT:       } else {
  // CHECK-NEXT:       }
  // CHECK-NEXT:     }

  // CHECK-NEXT: sv.initial { 
  // CHECK-NEXT:   sv.casez %arg8 : i8
  // CHECK-NEXT:   case b0000001x: {
  // CHECK-NEXT:     sv.fwrite "x"
  // CHECK-NEXT:   }
  // CHECK-NEXT:   case b000000x1: {
  // CHECK-NEXT:     sv.fwrite "y"
  // CHECK-NEXT:   }
  // CHECK-NEXT:   default: {
  // CHECK-NEXT:     sv.fwrite "z"
  // CHECK-NEXT:   }
  // CHECK-NEXT: }


  sv.initial {
    sv.casez %arg8 : i8
    case b0000001x: {
      sv.fwrite "x"
      sv.yield
    }
    case b000000x1: {
      sv.fwrite "y"
    }  // implicit yield is ok.
    default: {
      sv.fwrite "z"
      sv.yield
    }
  }

  // CHECK-NEXT: sv.initial {
  // CHECK-NEXT:   sv.casez %arg1 : i1
  // CHECK-NEXT:   case b0: {
  // CHECK-NEXT:     sv.fwrite "zero"
  // CHECK-NEXT:   }
  // CHECK-NEXT:   case b1: {
  // CHECK-NEXT:     sv.fwrite "one"
  // CHECK-NEXT:   }
  // CHECK-NEXT: }
  sv.initial {
    sv.casez %arg1 : i1
    case b0: {
      sv.fwrite "zero"
    }
    case b1: {
      sv.fwrite "one"
    }
  }

  // CHECK-NEXT: rtl.output
  rtl.output
}
