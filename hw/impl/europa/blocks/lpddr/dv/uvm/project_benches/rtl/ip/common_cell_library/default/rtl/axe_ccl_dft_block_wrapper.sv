// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

/// Placeholder block for DFT insertion, instantiate at physical block top
///
module axe_ccl_dft_block_wrapper #(
  parameter int unsigned N_SCAN_CHAINS = 8
) (
  input  wire  i_ijtag_tck,
  input  wire  i_ijtag_rst_n,
  input  logic i_ijtag_sel,
  input  logic i_ijtag_ue,
  input  logic i_ijtag_se,
  input  logic i_ijtag_ce,
  input  logic i_ijtag_tdi,
  output logic o_ijtag_tdo,

  input  wire  i_test_clk,
  input  logic i_edt_update,
  input  logic i_scan_en,
  input  logic [N_SCAN_CHAINS-1:0] i_scan_in,
  output logic [N_SCAN_CHAINS-1:0] o_scan_out
);

endmodule : axe_ccl_dft_block_wrapper
