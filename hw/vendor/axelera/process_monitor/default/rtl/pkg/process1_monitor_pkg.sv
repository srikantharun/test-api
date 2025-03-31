// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: process monitor 1 package, defining parameters for the process monitor 1.
//
// Authors: Bob Vanhoof, Mohit Gupta
// Owner: Mohit Gupta

`ifndef PROCESS1_MONITOR_PKG_SV
`define PROCESS1_MONITOR_PKG_SV

package process1_monitor_pkg;

    // PR1 related parameters
    parameter PR1_SEED = 31415;
    parameter PR1_NB_MONITOR = 14;
    parameter PR1_COUNT_W = 16;
    parameter PR1_TARGET_W = 3;

    typedef logic [PR1_NB_MONITOR-1:0][PR1_COUNT_W-1:0] pr1_count_t;

endpackage

`endif  // PROCESS1_MONITOR_PKG_SV
