// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: svs monitor package, defining parameters for the svs monitor.
//
// Authors: Bob Vanhoof, Mohit Gupta
// Owner: Mohit Gupta

`ifndef SVS_MONITOR_PKG_SV
`define SVS_MONITOR_PKG_SV

package svs_monitor_pkg;

    // SVS related parameters
    parameter SVS_SEED = 31415;
    parameter SVS_NB_MONITOR = 30;
    parameter SVS_COUNT_W = 16;
    parameter SVS_TARGET_W = 3;

    typedef logic [SVS_NB_MONITOR-1:0][SVS_COUNT_W-1:0] svs_count_t;

endpackage

`endif  // SVS_MONITOR_PKG_SV
