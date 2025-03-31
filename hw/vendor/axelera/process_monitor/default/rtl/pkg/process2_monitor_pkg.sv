// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: process monitor 2 package, defining parameters for the process monitor 2.
//
// Authors: Bob Vanhoof, Mohit Gupta
// Owner: Mohit Gupta

`ifndef PROCESS2_MONITOR_PKG_SV
`define PROCESS2_MONITOR_PKG_SV

package process2_monitor_pkg;

    // PR1 related parameters
    parameter PR2_SEED = 31415;
    parameter PR2_NB_MONITOR = 43;
    parameter PR2_COUNT_W = 16;
    parameter PR2_TARGET_W = 3;

    typedef logic [PR2_NB_MONITOR-1:0][PR2_COUNT_W-1:0] pr2_count_t;

endpackage

`endif  // PROCESS2_MONITOR_PKG_SV
