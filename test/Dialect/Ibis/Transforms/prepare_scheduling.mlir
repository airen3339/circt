// RUN: circt-opt --pass-pipeline="builtin.module(ibis.class(ibis.method.df(ibis-prepare-scheduling)))" \
// RUN:      --allow-unregistered-dialect %s | FileCheck %s

// CHECK:  %[[VAL_3:.*]]:2 = ibis.sblock (%[[VAL_4:.*]] : i32 = %[[VAL_1:.*]], %[[VAL_5:.*]] : i32 = %[[VAL_2:.*]]) -> (i32, i32) {
// CHECK:    %[[VAL_6:.*]], %[[VAL_7:.*]], %[[VAL_8:.*]], %[[VAL_9:.*]] = ibis.pipeline.header
// CHECK:    %[[PL_OUT:.*]]:2, %[[PL_DONE:.*]] = pipeline.unscheduled(%[[INNER_ARG0:.*]] : i32 = %[[VAL_4]], %[[INNER_ARG1:.*]] : i32 = %[[VAL_5]]) stall(%[[VAL_14:.*]] = %[[VAL_9]]) clock(%[[VAL_15:.*]] = %[[VAL_6]]) reset(%[[VAL_16:.*]] = %[[VAL_7]]) go(%[[VAL_17:.*]] = %[[VAL_8]]) -> (out0 : i32, out1 : i32) {
// CHECK:      %[[RES:.*]] = "foo.op1"(%[[INNER_ARG0]], %[[INNER_ARG1]]) : (i32, i32) -> i32
// CHECK:      pipeline.return %[[RES]], %[[INNER_ARG0]] : i32, i32
// CHECK:    }
// CHECK:    ibis.sblock.return %[[PL_OUT]]#0, %[[PL_OUT]]#1 : i32, i32
// CHECK:  }

ibis.class @PrepareScheduling {
  %this = ibis.this @PrepareScheduling
  // A test wherein the returned values are either a value generated by an
  // operation in the pipeline, or a value that's passed through the pipeline.
  // The resulting IR should have all values passing through the newly created
  // pipeline.
  ibis.method.df @foo(%a: i32, %b: i32) -> (i32, i32) {
    %0, %1 = ibis.sblock (%arg0 : i32 = %a, %arg1 : i32 = %b) -> (i32, i32) {
      %4 = "foo.op1"(%arg0, %arg1) : (i32, i32) -> i32
      ibis.sblock.return %4, %arg0 : i32, i32
    }
    ibis.return %0, %1 : i32, i32
  }
}
