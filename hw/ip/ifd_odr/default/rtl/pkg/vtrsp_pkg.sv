// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: VTRSP package
// Owner: Sander Geursen <sander.geursen@axelera.ai>

package vtrsp_pkg;
  // enum for the connection, connect to row or column for fill or drain
  typedef enum logic {
    ROW    = 1'b0,
    COLUMN = 1'b1
  } vtrsp_fill_drain_connection_e;

  // the command modes:
  typedef enum logic[1:0] {
    bypass_mode = 'd0,
    fp8_mode    = 'd1,
    fp16_mode   = 'd2,
    fp32_mode   = 'd3
  } vtrsp_cmd_mode_e;

endpackage
