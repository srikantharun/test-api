// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: svs monitor behavioral model.
//
// Authors: Manuel Oliveira


module svs_monitor_wrapper
import svs_monitor_pkg::*;
(
  // JTAG
  input   wire                                         tcki,
  input   wire                                         trsti,

  input	  wire                                         i_clk,
  input   logic                                        i_enable,

  input   wire                                         i_ref_clk,

  input   logic                     [SVS_TARGET_W-1:0] i_target,

  input   logic                   [SVS_NB_MONITOR-1:0] i_use_ro,

  output  logic                                        o_valid,
  output  logic [SVS_NB_MONITOR-1:0] [SVS_COUNT_W-1:0] o_count
);

endmodule
