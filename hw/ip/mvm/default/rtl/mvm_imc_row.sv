// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Combinations of imc_banks_acc modules to match the width of a PW.
// Owner: roel uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_IMC_ROW_SV
`define MVM_IMC_ROW_SV

module mvm_imc_row #(
  parameter DATA_W = 8,
  parameter IMC_NB_COLS_PER_BANK = 32,
  parameter IMC_NB_ROWS = 512,
  parameter IMC_NB_WEIGHT_SETS = 4,
  parameter IMC_NB_DELAY_CYCLES = 1,
  parameter IMC_BLOCK_GATING_GRANULARITY = 32,
  parameter MVM_NB_IMC_BANKS_ON_ROW = 2,
  parameter MVM_OUT_DATA_W = 26,
  parameter MVM_IMC_OUT_DATA_W = 17
) (
  input wire i_clk,
  input logic i_rst_n,
  input logic stall,  // stall the mvm operation this includes imc_banks and acc
  // weight related signals
  input  logic [DATA_W-1:0]   w_vec_in   [MVM_NB_IMC_BANKS_ON_ROW*IMC_NB_COLS_PER_BANK-1:0],       // input vector of 64 weights
  input logic [$clog2(IMC_NB_WEIGHT_SETS)-1:0] w_set,  // weight set select for all blocks
  input logic [MVM_NB_IMC_BANKS_ON_ROW-1:0] w_wen,  // individual write enable bits for all blocks (n-hot)
  input logic [8:0] w_row,  // row select address
  input logic c_signed_weights,  // True when weights should be interpreted as signed
  // compute related signals
  input logic [IMC_NB_ROWS-1:0] c_in,  // c_in input vector of 1 bit elements
  input logic [$clog2(
IMC_NB_WEIGHT_SETS
)-1:0] c_wss,  // compute weight set select (should never equal w_set when w_en is active)
  input  logic [IMC_NB_ROWS/IMC_BLOCK_GATING_GRANULARITY-1:0]  c_be [MVM_NB_IMC_BANKS_ON_ROW-1:0],  // compute block enable signals (n-hot for each block)
  input logic c_gc,  // Internal clock gating in the imc banks
  //input  logic                c_en,                           // Compute enable signal, launches a new operation
  // acc related signals
  input logic [2:0] acc_shift_pos,
  input logic [MVM_NB_IMC_BANKS_ON_ROW-1:0] acc_group_enable,
  input logic [MVM_NB_IMC_BANKS_ON_ROW-1:0] acc_output_enable,
  input logic acc_clear,
  input logic acc_signed_weights,
  input logic acc_signed_inputs,
  output logic [MVM_OUT_DATA_W-1:0]         c_out [MVM_NB_IMC_BANKS_ON_ROW*IMC_NB_COLS_PER_BANK-1 :0], // output vectors of all columns from all blocks
  input logic csr_disable_imc_acc_clock_gating_i,
  input logic test_mode
);


  genvar g;
  generate
    for (g = 0; g < MVM_NB_IMC_BANKS_ON_ROW; g++) begin
      logic [DATA_W-1:0] w_vec_in_gated[IMC_NB_COLS_PER_BANK-1:0];
      always_comb begin
        if (w_wen[g]) begin
          w_vec_in_gated = w_vec_in[g*IMC_NB_COLS_PER_BANK+:IMC_NB_COLS_PER_BANK];
        end else w_vec_in_gated = '{default: 0};
      end

      mvm_imc_bank_acc #(
        .DATA_W   (DATA_W),
        .IMC_NB_COLS_PER_BANK  (IMC_NB_COLS_PER_BANK),
        .IMC_NB_ROWS  (IMC_NB_ROWS),
        .IMC_NB_WEIGHT_SETS (IMC_NB_WEIGHT_SETS),
        .IMC_NB_DELAY_CYCLES (IMC_NB_DELAY_CYCLES),
        .IMC_BLOCK_GATING_GRANULARITY (IMC_BLOCK_GATING_GRANULARITY),
        .MVM_OUT_DATA_W (MVM_OUT_DATA_W),
        .MVM_IMC_OUT_DATA_W (MVM_IMC_OUT_DATA_W)
      ) inst_imc_w_acc (
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .stall(stall),
        // Weight related signals
        .w_vec_in(w_vec_in_gated),
        .w_set(w_set),  // weight set select
        .w_wen(w_wen[g]),  // pass on the correct weight write enable bit for this block
        .w_row(w_row),
        .c_signed_weights(c_signed_weights),
        // Compute related input signals
        .c_in(c_in),  // c_in input vector of 1 bit elements
        .c_wss(c_wss),  // compute weight set select (should never equal w_set when w_en is active)
        .c_be(c_be[g]),  // compute block enable signals for this block
        //.c_en           (c_en),                       // Global compute enable for all blocks
        .c_gc(c_gc),

        // acc related signals
        .acc_shift_pos     (acc_shift_pos),
        .acc_group_enable  (acc_group_enable[g]),
        .acc_output_enable (acc_output_enable[g]),
        .acc_clear         (acc_clear),
        .acc_signed_weights(acc_signed_weights),
        .acc_signed_inputs (acc_signed_inputs),

        // Compute output
        .c_out_acc(c_out[g*IMC_NB_COLS_PER_BANK+:IMC_NB_COLS_PER_BANK]),
        .csr_disable_imc_acc_clock_gating_i(csr_disable_imc_acc_clock_gating_i),
        .test_mode(test_mode)
      );
    end
  endgenerate
endmodule
`endif  // MVM_IMC_ROW_SV
