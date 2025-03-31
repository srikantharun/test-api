// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DFT insertable TDR core
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef PROCESS2_MONITOR_JTAG_TDR_CORE_SV
`define PROCESS2_MONITOR_JTAG_TDR_CORE_SV

module process2_monitor_jtag_tdr_core
  import process2_monitor_pkg::*;
 (
  // JTAG
  input  wire  tcki,
  input  wire  trsti,
  // JTAG TAP
  input  logic seli,
  input  logic sei,
  input  logic cei,
  input  logic uei,
  input  logic tdi,
  output logic tdo,

  output logic                                  o_jtag_mode,
  output logic                                  o_enable,
  output logic               [PR2_TARGET_W-1:0] o_target,
  output logic             [PR2_NB_MONITOR-1:0] o_use_ro,
  input  logic                                  i_valid,
  input  logic [PR2_NB_MONITOR*PR2_COUNT_W-1:0] i_count
);

`ifndef TARGET_DFT
`ifndef TESSENT
always_comb tdo         = '0;
always_comb o_jtag_mode = '0;
always_comb o_enable    = '0;
always_comb o_target    = '0;
always_comb o_use_ro    = '0;
`endif // ! TESSENT
`endif // ! TARGET_DFT

endmodule
`endif  // PROCESS2_MONITOR_JTAG_TDR_CORE_SV
