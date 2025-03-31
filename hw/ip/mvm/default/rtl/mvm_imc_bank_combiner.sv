// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// mvm_imc_bank_combiner instantiates 2 imc_banks to complete a 32 bits output
///
module mvm_imc_bank_combiner
  import imc_bank_pkg::*;
  import mvm_pkg::*;
  (
  /// Clock, positive edge triggered
  input wire                                                      i_clk,
  /// Asynchronous reset, active low
  input wire                                                      i_rst_n,

  /// Repair interface signals
  input  logic                                                     i_imc_bisr_mux_mode,
  input  logic                                                     i_imc_bisr_shift_en,
  input  logic                                                     i_imc_bisr_ue,
  input  logic                                                     i_imc_bisr_si,
  output logic                                                     o_imc_bisr_mux_mode,
  output logic                                                     o_imc_bisr_shift_en,
  output logic                                                     o_imc_bisr_ue,
  output logic                                                     o_imc_bisr_so,

  /// Weight interface signals
  /// weight write enable bit for this block
  input logic                                                      i_write_enable,
  /// row select address
  input logic                                     [IMC_ROW_PW-1:0] i_write_row,
  /// weight set select for weight writing (should never equal compute_wss when w_en is active)
  input logic                              [IMC_WEIGHT_SET_PW-1:0] i_write_wss,
  /// weight values to be written
  input logic      [1:0][IMC_NB_COLS_PER_BANK-1:0][IMC_DATA_W-1:0] i_write_values,

  /// Compute interface signals
  input  logic                                                     i_compute_enable,
  /// compute input vector of 1 bit elements
  input  logic                                   [IMC_NB_ROWS-1:0] i_compute_inp,
  /// compute weight set select (should never equal write_wss when w_en is active)
  input  logic                             [IMC_WEIGHT_SET_PW-1:0] i_compute_wss,
  /// compute block enable. If all blocks enables are disabled (0) then the imc operation equals zero.
  input  logic                            [IMC_BLOCK_ENABLE_W-1:0] i_compute_block_enable,
  /// determines how weights should be interpreted (00: unsigned, 01: 4 bit signed, 10: 8 bit signed, 11: 16 bit signed)
  input  logic                                               [1:0] i_compute_weight_format,
  /// Partial accumulation result
  output logic [1:0][MVM_IMC_COLS_GROUP-1:0][MVM_IMC_COLS_GROUP_OUT_WD-1:0] o_compute_out
);

  logic [1:0] imc_bisr_mux_mode;
  logic [1:0] imc_bisr_shift_en;
  logic [1:0] imc_bisr_ue;
  logic [1:0] imc_bisr_si;
  logic [1:0] imc_bisr_mux_mode_o;
  logic [1:0] imc_bisr_shift_en_o;
  logic [1:0] imc_bisr_ue_o;
  logic [1:0] imc_bisr_so;

  assign imc_bisr_mux_mode   = {i_imc_bisr_mux_mode, imc_bisr_mux_mode_o[1]};
  assign imc_bisr_shift_en   = {i_imc_bisr_shift_en, imc_bisr_shift_en_o[1]};
  assign imc_bisr_ue         = {i_imc_bisr_ue, imc_bisr_ue_o[1]};
  assign imc_bisr_si         = {i_imc_bisr_si, imc_bisr_so[1]};
  assign o_imc_bisr_mux_mode = imc_bisr_mux_mode_o[0];
  assign o_imc_bisr_shift_en = imc_bisr_shift_en_o[0];
  assign o_imc_bisr_ue       = imc_bisr_ue_o[0];
  assign o_imc_bisr_so       = imc_bisr_so[0];

  for (genvar i = 0; i < 2; i++) begin : g_imc_bank_wrapper
  mvm_imc_bank_wrapper u_mvm_imc_bank_wrapper (
    .i_clk                   (i_clk),
    .i_rst_n                 (i_rst_n),
    .i_imc_bisr_mux_mode     (imc_bisr_mux_mode[i]),
    .i_imc_bisr_shift_en     (imc_bisr_shift_en[i]),
    .i_imc_bisr_ue           (imc_bisr_ue[i]),
    .i_imc_bisr_si           (imc_bisr_si[i]),
    .o_imc_bisr_mux_mode     (imc_bisr_mux_mode_o[i]),
    .o_imc_bisr_shift_en     (imc_bisr_shift_en_o[i]),
    .o_imc_bisr_ue           (imc_bisr_ue_o[i]),
    .o_imc_bisr_so           (imc_bisr_so[i]),
    .i_write_enable          (i_write_enable),
    .i_write_row             (i_write_row),
    .i_write_wss             (i_write_wss),
    .i_write_values          (i_write_values[i]),
    .i_compute_enable        (i_compute_enable),
    .i_compute_inp           (i_compute_inp),
    .i_compute_wss           (i_compute_wss),
    .i_compute_block_enable  (i_compute_block_enable),
    .i_compute_weight_format (i_compute_weight_format),
    .o_compute_out           (o_compute_out[i])
  );
  end

endmodule
