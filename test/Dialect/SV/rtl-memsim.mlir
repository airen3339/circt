// RUN: circt-opt -rtl-memory-sim %s | FileCheck %s

rtl.generator.schema @FIRRTLMem, "FIRRTL_Memory", ["depth", "numReadPorts", "numWritePorts", "numReadWritePorts", "readLatency", "writeLatency", "width", "readUnderWrite"]
rtl.module.generated @FIRRTLMem_1_1_1_16_10_0_1_0, @FIRRTLMem(%ro_clock_0: i1, %ro_en_0: i1, %ro_addr_0: i4, %rw_clock_0: i1, %rw_en_0: i1, %rw_addr_0: i4, %rw_wmode_0: i1, %rw_wmask_0: i1, %rw_wdata_0: i16, %wo_clock_0: i1, %wo_en_0: i1, %wo_addr_0: i4, %wo_mask_0: i1, %wo_data_0: i16) -> (%ro_data_0: i16, %rw_rdata_0: i16) attributes {depth = 10 : i64, numReadPorts = 1 : ui32, numReadWritePorts = 1 : ui32, numWritePorts = 1 : ui32, readLatency = 0 : ui32, readUnderWrite = 0 : ui32, width = 16 : ui32, writeLatency = 1 : ui32}
rtl.module.generated @FIRRTLMem_1_1_1_16_10_2_4_0, @FIRRTLMem(%ro_clock_0: i1, %ro_en_0: i1, %ro_addr_0: i4, %rw_clock_0: i1, %rw_en_0: i1, %rw_addr_0: i4, %rw_wmode_0: i1, %rw_wmask_0: i1, %rw_wdata_0: i16, %wo_clock_0: i1, %wo_en_0: i1, %wo_addr_0: i4, %wo_mask_0: i1, %wo_data_0: i16) -> (%ro_data_0: i16, %rw_rdata_0: i16) attributes {depth = 10 : i64, numReadPorts = 1 : ui32, numReadWritePorts = 1 : ui32, numWritePorts = 1 : ui32, readLatency = 2 : ui32, readUnderWrite = 0 : ui32, width = 16 : ui32, writeLatency = 4 : ui32}

//CHECK-LABEL: @complex
rtl.module @complex(%clock: i1, %reset: i1, %r0en: i1, %mode: i1, %data0: i16) -> (%data1: i16, %data2: i16) {
  %true = rtl.constant true
  %c0_i4 = rtl.constant 0 : i4
  %tmp41.ro_data_0, %tmp41.rw_rdata_0 = rtl.instance "tmp41" @FIRRTLMem_1_1_1_16_10_2_4_0(%clock, %r0en, %c0_i4, %clock, %r0en, %c0_i4, %mode, %true, %data0, %clock, %r0en, %c0_i4, %true, %data0) : (i1, i1, i4, i1, i1, i4, i1, i1, i16, i1, i1, i4, i1, i16) -> (i16, i16)
  rtl.output %tmp41.ro_data_0, %tmp41.rw_rdata_0 : i16, i16
}

//CHECK-LABEL: @simple
rtl.module @simple(%clock: i1, %reset: i1, %r0en: i1, %mode: i1, %data0: i16) -> (%data1: i16, %data2: i16) {
  %true = rtl.constant true
  %c0_i4 = rtl.constant 0 : i4
  %tmp41.ro_data_0, %tmp41.rw_rdata_0 = rtl.instance "tmp41" @FIRRTLMem_1_1_1_16_10_0_1_0(%clock, %r0en, %c0_i4, %clock, %r0en, %c0_i4, %mode, %true, %data0, %clock, %r0en, %c0_i4, %true, %data0) : (i1, i1, i4, i1, i1, i4, i1, i1, i16, i1, i1, i4, i1, i16) -> (i16, i16)
  rtl.output %tmp41.ro_data_0, %tmp41.rw_rdata_0 : i16, i16
}

//CHECK-LABEL: @FIRRTLMem_1_1_1_16_10_0_1_0
//CHECK:       %Memory = sv.reg  : !rtl.inout<uarray<10xi16>>
//CHECK-NEXT:  %[[rslot:.+]] = sv.array_index_inout %Memory[%ro_addr_0]
//CHECK-NEXT:  %[[read:.+]] = sv.read_inout %[[rslot]]
//CHECK-NEXT:  %[[x:.+]] = sv.constantX
//CHECK-NEXT:  %[[readres:.+]] = comb.mux %ro_en_0, %[[read]], %[[x]]
//CHECK-NEXT:  %[[rwtmp:.+]] = sv.wire
//CHECK-NEXT:  %[[rwres:.+]] = sv.read_inout %[[rwtmp]]
//CHECK-NEXT:    sv.alwaysff(posedge %rw_clock_0)  {
//CHECK-NEXT:      %[[rwslot:.+]] = sv.array_index_inout %Memory[%rw_addr_0] 
//CHECK-NEXT:      %false = rtl.constant false
//CHECK-NEXT:      %[[rwrcondpre:.+]] = comb.icmp eq %rw_wmode_0, %false
//CHECK-NEXT:      %[[rwrcond:.+]] = comb.and %rw_en_0, %[[rwrcondpre]]
//CHECK-NEXT:      %[[rwwcondpre:.+]] = comb.and %rw_wmask_0, %rw_wmode_0
//CHECK-NEXT:      %[[rwwcond:.+]] = comb.and %rw_en_0, %[[rwwcondpre]]
//CHECK-NEXT:      %[[x2:.+]] = sv.constantX
//CHECK-NEXT:      sv.passign %[[rwtmp]], %[[x2]]
//CHECK-NEXT:      sv.if %[[rwwcond]]  {
//CHECK-NEXT:        sv.passign %[[rwslot]], %rw_wdata_0
//CHECK-NEXT:      } else  {
//CHECK-NEXT:        sv.if %[[rwrcond]]  {
//CHECK-NEXT:          %[[rwdata:.+]] = sv.read_inout %[[rwslot]]
//CHECK-NEXT:          sv.passign %[[rwtmp]], %[[rwdata]]
//CHECK-NEXT:        }
//CHECK-NEXT:      }
//CHECK-NEXT:    }
//CHECK-NEXT:  sv.alwaysff(posedge %wo_clock_0)  {
//CHECK-NEXT:    %[[wcond:.+]] = comb.and %wo_en_0, %wo_mask_0
//CHECK-NEXT:    sv.if %[[wcond]]  {
//CHECK-NEXT:      %[[wslot:.+]] = sv.array_index_inout %Memory[%wo_addr_0]
//CHECK-NEXT:      sv.passign %[[wslot]], %wo_data_0
//CHECK-NEXT:    }
//CHECK-NEXT:  }
//CHECK-NEXT:  rtl.output %[[readres]], %[[rwres]]

//CHECK-LABEL: @FIRRTLMem_1_1_1_16_10_2_4_0
//COM: This produces a lot of output, we check one field's pipeline
//CHECK:         %Memory = sv.reg  : !rtl.inout<uarray<10xi16>>
//CHECK:         sv.alwaysff(posedge %ro_clock_0)  {
//CHECK-NEXT:      sv.passign %0, %ro_en_0 : i1
//CHECK-NEXT:    }
//CHECK-NEXT:    %1 = sv.read_inout %0 : !rtl.inout<i1>
//CHECK-NEXT:    %2 = sv.reg  : !rtl.inout<i1>
//CHECK-NEXT:    sv.alwaysff(posedge %ro_clock_0)  {
//CHECK-NEXT:      sv.passign %2, %1 : i1
//CHECK-NEXT:    }
//CHECK-NEXT:    %3 = sv.read_inout %2 : !rtl.inout<i1>
//CHECK-NEXT:    %4 = sv.reg  : !rtl.inout<i4>
//CHECK-NEXT:    sv.alwaysff(posedge %ro_clock_0)  {
//CHECK-NEXT:      sv.passign %4, %ro_addr_0 : i4
//CHECK-NEXT:    }
//CHECK-NEXT:    %5 = sv.read_inout %4 : !rtl.inout<i4>
//CHECK-NEXT:    %6 = sv.reg  : !rtl.inout<i4>
//CHECK-NEXT:    sv.alwaysff(posedge %ro_clock_0)  {
//CHECK-NEXT:      sv.passign %6, %5 : i4
//CHECK-NEXT:    }
//CHECK-NEXT:    %7 = sv.read_inout %6 : !rtl.inout<i4>
//CHECK-NEXT:    %8 = sv.array_index_inout %Memory[%7] : !rtl.inout<uarray<10xi16>>, i4
