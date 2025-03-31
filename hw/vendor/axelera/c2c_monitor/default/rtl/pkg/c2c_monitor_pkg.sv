// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: C2C monitor package, defining parameters for the c2c_monitor.
//
// Delay numbers are based on TT, 0.85V 25C, nominal CC extracted.
//
// Authors: Bram Rooseleer
// Owner: Bram Rooseleer <bram.rooseleer@axelera.ai>

`ifndef C2C_MONITOR_PKG_SV
`define C2C_MONITOR_PKG_SV

package c2c_monitor_pkg;

  // C2C related parameters
  parameter C2C_COUNT_W = 8;
  parameter C2C_COUNT_0 = 164;
  parameter C2C_COUNT_1 = 200;

endpackage

`endif  // C2C_MONITOR_PKG_SV
