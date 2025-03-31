// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: dummy process monitor 2 behavioral model.

module process2_monitor_wrapper
import process2_monitor_pkg::*;
(
  // JTAG
  input   wire                                         tcki,
  input   wire                                         trsti,

  input	  wire                                         i_clk,
  input   wire                                         i_enable,

  input   wire                                         i_ref_clk,

  input   logic                     [PR2_TARGET_W-1:0] i_target,

  input   logic                   [PR2_NB_MONITOR-1:0] i_use_ro,

  output  logic                                        o_valid,
  output  logic [PR2_NB_MONITOR-1:0] [PR2_COUNT_W-1:0] o_count
);

endmodule
