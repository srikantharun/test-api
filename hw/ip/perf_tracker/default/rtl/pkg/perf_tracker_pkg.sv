// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Parameters for the perf_tracker.
// Owner: Gua Hao Khov <guahao.khov@axelera.ai>

`ifndef PERF_TRACKER_PKG_SV
`define PERF_TRACKER_PKG_SV

package perf_tracker_pkg;

  parameter int unsigned PERF_DATA_W = 32;
  parameter int unsigned PERF_CNTR_W = 24;

endpackage
`endif  //PERF_TRACKER_PKG_SV

