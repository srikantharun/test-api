// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: mvm_imc_bank_acc module that makes it compute inputs signals available as an output again after 1 pipeline reg.
// This enables the creation of pipeline of the compute inputs between serveral mvm_imc_bank_acc modules.
// Owner: roel uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_IMC_BANK_ACC_W_PIPE
`define MVM_IMC_BANK_ACC_W_PIPE

module mvm_imc_bank_acc_w_pipe
  import imc_bank_pkg::*;
  import mvm_pkg::*;
  import imc_bist_pkg::*;
#(
  parameter int unsigned IMC_BANK_ID = 0
) (
  input wire i_clk,
  input wire i_rst_n,

  input  logic i_imc_bist_mode,
  output logic o_imc_bist_mode,

  input  imc_repair_struct_t i_repair_intf,
  output imc_repair_struct_t o_repair_intf,

  // IMC weight write signals
  input logic weight_in_valid_i,
  input imc_weight_struct_t weight_in_data_i,
  output logic weight_in_valid_o,
  output imc_weight_struct_t weight_in_data_o,

  // IMC compute signals
  // Input (before pipelining)
  input logic [1:0] compute_in_valid_i,
  input logic [1:0] compute_in_stall_i,
  input imc_compute_struct_t [1:0] compute_in_data_i,
  // Output (after pipelining)
  output logic [1:0] compute_in_valid_o,
  output logic [1:0] compute_in_stall_o,
  output imc_compute_struct_t [1:0] compute_in_data_o,

  // output vectors of all columns from all blocks
  output logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] compute_out_o,
  output logic compute_out_valid_o,
  output compute_out_ctrl_t compute_out_ctrl_o,

  // IMC static settings
  input logic csr_power_smooth_dummy_ops_i,
  input logic csr_disable_imc_acc_clock_gating_i,
  input logic test_mode_i,
  input logic scan_en,

  // IMC errors
  output logic err_concurrent_exe_prg_on_ws_o
);

  mvm_imc_bank_acc #(
    .IMC_BANK_ID(IMC_BANK_ID)
  ) inst_imc_w_acc (
    .i_clk (i_clk),
    .i_rst_n(i_rst_n),

    .i_repair_intf(i_repair_intf),
    .o_repair_intf(o_repair_intf),

    // IMC weight write signals
    .weight_in_valid_i(weight_in_valid_i),
    .weight_in_data_i (weight_in_data_i),

    // IMC compute signals
    .compute_in_valid_i(compute_in_valid_i),
    .compute_in_stall_i(compute_in_stall_i),
    .compute_in_data_i (compute_in_data_i),

    .compute_out_o(compute_out_o),  // output vectors of all columns from all blocks
    .compute_out_valid_o(compute_out_valid_o),
    .compute_out_ctrl_o(compute_out_ctrl_o),

    // IMC static settings
    .csr_disable_imc_acc_clock_gating_i(csr_disable_imc_acc_clock_gating_i),
    .csr_power_smooth_dummy_ops_i(csr_power_smooth_dummy_ops_i),
    .test_mode_i(test_mode_i), // IMC isolation enable
    .scan_en(scan_en), // Clock gate bypass

    // IMC errors
    .err_concurrent_exe_prg_on_ws_o(err_concurrent_exe_prg_on_ws)
  );

  // Valid/stall pipelining (needs a reset)
  always_ff @(posedge i_clk, negedge i_rst_n) begin : imc_acc_input_valid_pipeline
    if (!i_rst_n) begin
      compute_in_valid_o <= 1'b0;
      compute_in_stall_o <= 1'b0;
      weight_in_valid_o  <= 1'b0;
    end else begin
      compute_in_valid_o <= compute_in_valid_i;
      compute_in_stall_o <= compute_in_stall_i;
      weight_in_valid_o  <= weight_in_valid_i;
    end
  end

  // Data pipelining (does not need a reset)
  always_ff @(posedge i_clk) begin : imc_acc_input_data_pipeline
    // Compute (if compute pipe is inactive ensure wss can't collide)
    if (|compute_in_valid_i) compute_in_data_o <= compute_in_data_i;
    else if (weight_in_valid_i)
      foreach(compute_in_data_o[i]) begin
        compute_in_data_o[i].weight_set <= ~weight_in_data_i.w_set;
      end

    // Weight write
    if (weight_in_valid_i) weight_in_data_o <= weight_in_data_i;
  end

  // IRQ pipelining
  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n) begin
      err_concurrent_exe_prg_on_ws_o <= '0;
    end else if(err_concurrent_exe_prg_on_ws_o ^ err_concurrent_exe_prg_on_ws) begin
      err_concurrent_exe_prg_on_ws_o <= err_concurrent_exe_prg_on_ws;
    end

  // IMC BIST gating logic pipelining
  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n) begin
      o_imc_bist_mode <= 1'b0;
    end else if(o_imc_bist_mode ^ i_imc_bist_mode) begin
      o_imc_bist_mode <= i_imc_bist_mode;
    end

endmodule
`endif  // MVM_IMC_BANK_ACC_W_PIPE
