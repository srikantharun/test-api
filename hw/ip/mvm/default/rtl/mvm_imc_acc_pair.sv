// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: A pair of mvm_imc_acc_w_pipe modules that follow each other in the input pipelining.
// Their output results are muxed locally in this module and presented as the output results of this pair.
// The compute inputs are given to the first mvm_imc_acc_w_pipe element which presents a pipelined version of these inputs for the next elements.
// This elements does the same but presents it's pipelined compute input signals as an output from this module to be used in the next pair.
// Owner: roel uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_IMC_ACC_PAIR
`define MVM_IMC_ACC_PAIR

module mvm_imc_acc_pair
  import imc_bank_pkg::*;
  import mvm_pkg::*;
  import imc_bist_pkg::*;
#(
  parameter int unsigned IMC_PAIR_ID = 0
) (
  input wire i_clk,
  input wire i_rst_n,

  input  imc_repair_struct_t i_repair_intf,
  output imc_repair_struct_t o_repair_intf,

  // IMC weight write signals
  // Input (before pipelining)
  input logic weight_in_valid_i,
  input imc_weight_struct_t   weight_in_data_i,
  // Output (after pipelining twice)
  output logic weight_in_valid_o,
  output imc_weight_struct_t   weight_in_data_o,

  // IMC compute signals
  // Input (before pipelining)
  input logic [1:0] compute_in_valid_i,
  input logic [1:0] compute_in_stall_i,
  input imc_compute_struct_t [1:0] compute_in_data_i,
  // Output (after pipelining twice)
  output logic [1:0] compute_in_valid_o,
  output logic [1:0] compute_in_stall_o,
  output imc_compute_struct_t [1:0] compute_in_data_o,

  // IMC compute output results after MUX/OR-ing based on valid
  // output vectors of all columns from all blocks
  output logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] compute_out_o,
  output logic compute_out_valid_o,
  output compute_out_ctrl_t compute_out_ctrl_o,

  // IMC static settings
  input logic csr_power_smooth_dummy_ops_i,
  input logic csr_disable_imc_acc_clock_gating_i,

  // DFT
  input logic test_mode_i,
  input logic scan_en,

  // IMC errors (or-ed between both banks in pair)
  output logic err_concurrent_exe_prg_on_ws_o,

  // IMC BIST inputs
  input  logic i_imc_bist_mode,
  output logic o_imc_bist_mode,
  input logic imc_bist_expect_strobe_i,
  input imc_bist_pkg::expect_type_e imc_bist_expect_type_i,
  input imc_bist_pkg::compare_bus_t [imc_bist_pkg::NUM_COMPARATORS-1:0] imc_bist_compare_bus_i,

  // IMC BIST outputs
  output logic imc_bist_expect_strobe_o,
  output imc_bist_pkg::expect_type_e imc_bist_expect_type_o,
  output imc_bist_pkg::compare_bus_t [imc_bist_pkg::NUM_COMPARATORS-1:0] imc_bist_compare_bus_o
);

  // IMC compute signals
  logic [1:0] compute_in_valid_a;
  logic [1:0] compute_in_stall_a;
  imc_compute_struct_t [1:0] compute_in_data_a;
  // IMC weight write signals
  logic weight_in_valid_a;
  imc_weight_struct_t   weight_in_data_a;

  // IMC compute output results after MUX/OR-ing based on valid
  logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] compute_out_a, compute_out_b;
  logic compute_out_valid_a, compute_out_valid_b;
  compute_out_ctrl_t compute_out_ctrl_a, compute_out_ctrl_b;
  logic exe_prg_imc_active_a, exe_acc_active_a, exe_prg_imc_active_b, exe_acc_active_b;
  logic err_concurrent_exe_prg_on_ws_a, err_concurrent_exe_prg_on_ws_b;

  logic [IMC_NB_COLS_PER_BANK-1:0][MVM_IMC_OUT_DATA_W-1:0] compute_out_a_noacc;
  logic [IMC_NB_COLS_PER_BANK-1:0][MVM_IMC_OUT_DATA_W-1:0] compute_out_b_noacc;

  logic imc_bist_mode_merged;
  logic imc_bist_mode_i_a, imc_bist_mode_o_a;
  logic imc_bist_mode_i_b, imc_bist_mode_o_b;

  imc_repair_struct_t   repair_intf_i_a, repair_intf_o_a;
  imc_repair_struct_t   repair_intf_i_b, repair_intf_o_b;

  assign imc_bist_mode_i_a = i_imc_bist_mode;
  assign imc_bist_mode_i_b = imc_bist_mode_o_a;
  assign o_imc_bist_mode   = imc_bist_mode_o_b;

  assign repair_intf_i_a = i_repair_intf;
  assign repair_intf_i_b = repair_intf_o_a;
  assign o_repair_intf   = repair_intf_o_b;

  // Mux between output results of this imc_bank_acc pair.
  localparam int unsigned MUX_ID = (IMC_PAIR_ID/2) + (IMC_PAIR_ID%2);
  mvm_dist_mux #(
    .OR_DATA(0), // This is the mux between the pairs, here we do want active gating
                 // of the data signals that should not propagate, not just or-ing the data.
    .OUT_PIPELINE_EN(LOCAL_MUX_PIPELINE_EN[MUX_ID])
  ) inst_mvm_pair_mux (
    .i_clk,
    .i_rst_n,
    .in_0(compute_out_a),
    .in_0_ctrl(compute_out_ctrl_a),
    .in_0_valid(compute_out_valid_a),
    .in_1(compute_out_b),
    .in_1_ctrl(compute_out_ctrl_b),
    .in_1_valid(compute_out_valid_b),
    .out_data(compute_out_o),
    .out_ctrl(compute_out_ctrl_o),
    .out_valid(compute_out_valid_o)
  );

  assign err_concurrent_exe_prg_on_ws_o = err_concurrent_exe_prg_on_ws_a
                                        | err_concurrent_exe_prg_on_ws_b;

  // A imc_bank_acc with pipeline stage on compute input sigals
  mvm_imc_bank_acc_w_pipe #(
    .IMC_BANK_ID(IMC_PAIR_ID)
  ) inst_imc_bank_acc_a (
    .i_clk (i_clk),
    .i_rst_n(i_rst_n),

    .i_imc_bist_mode(imc_bist_mode_i_a),
    .o_imc_bist_mode(imc_bist_mode_o_a),
    .i_repair_intf(repair_intf_i_a),
    .o_repair_intf(repair_intf_o_a),

    // IMC weight write input signals
    .weight_in_valid_i(weight_in_valid_i),
    .weight_in_data_i (weight_in_data_i),
    // IMC weight write input signals pipelined for next bank
    .weight_in_valid_o(weight_in_valid_a),
    .weight_in_data_o (weight_in_data_a),

    // IMC compute input signals
    .compute_in_valid_i(compute_in_valid_i),
    .compute_in_stall_i(compute_in_stall_i),
    .compute_in_data_i (compute_in_data_i),
    // IMC compute input signals pipelined for next bank
    .compute_in_valid_o(compute_in_valid_a),
    .compute_in_stall_o(compute_in_stall_a),
    .compute_in_data_o (compute_in_data_a),

    .compute_out_o(compute_out_a),  // output vectors of all columns from all blocks
    .compute_out_valid_o(compute_out_valid_a),
    .compute_out_ctrl_o(compute_out_ctrl_a),

    // IMC static settings
    .csr_disable_imc_acc_clock_gating_i(csr_disable_imc_acc_clock_gating_i),
    .csr_power_smooth_dummy_ops_i(csr_power_smooth_dummy_ops_i),
    .test_mode_i(test_mode_i),
    .scan_en(scan_en),

    // IMC errors
    .err_concurrent_exe_prg_on_ws_o(err_concurrent_exe_prg_on_ws_a)
  );

  // B imc_bank_acc with pipeline stage on compute input sigals
  mvm_imc_bank_acc_w_pipe #(
    .IMC_BANK_ID(IMC_PAIR_ID + 2)
  ) inst_imc_bank_acc_b (
    .i_clk (i_clk),
    .i_rst_n(i_rst_n),

    .i_imc_bist_mode(imc_bist_mode_i_b),
    .o_imc_bist_mode(imc_bist_mode_o_b),
    .i_repair_intf(repair_intf_i_b),
    .o_repair_intf(repair_intf_o_b),

    // IMC weight write input signals
    .weight_in_valid_i(weight_in_valid_a),
    .weight_in_data_i (weight_in_data_a),
    // IMC weight write input signals pipelined for next pair
    .weight_in_valid_o(weight_in_valid_o),
    .weight_in_data_o (weight_in_data_o),

    // IMC compute input signals
    .compute_in_valid_i(compute_in_valid_a),
    .compute_in_stall_i(compute_in_stall_a),
    .compute_in_data_i (compute_in_data_a),
    // IMC compute input signals pipelined for next pair
    .compute_in_valid_o(compute_in_valid_o),
    .compute_in_stall_o(compute_in_stall_o),
    .compute_in_data_o (compute_in_data_o),

    .compute_out_o(compute_out_b),  // output vectors of all columns from all blocks
    .compute_out_valid_o(compute_out_valid_b),
    .compute_out_ctrl_o(compute_out_ctrl_b),

    // IMC static settings
    .csr_disable_imc_acc_clock_gating_i(csr_disable_imc_acc_clock_gating_i),
    .csr_power_smooth_dummy_ops_i(csr_power_smooth_dummy_ops_i),
    .test_mode_i(test_mode_i),
    .scan_en(scan_en),

    // IMC errors
    .err_concurrent_exe_prg_on_ws_o(err_concurrent_exe_prg_on_ws_b)
  );

  // The first comparator has input delay to compensate for imc bank latency +1
  // for imc output pipeline delay + 1 for accumulator register delay -> +2
  localparam int unsigned CompInputDelay = (IMC_PAIR_ID == 0)
                                         ? (imc_bank_pkg::IMC_NB_DELAY_CYCLES + 2)
                                         : 0;

  always_comb begin
    // IMC BIST bypasses the accumulator so we just clip back the data to 17 bit
    foreach (compute_out_a_noacc[i]) compute_out_a_noacc[i] = compute_out_a[i][MVM_IMC_OUT_DATA_W-1:0];
    foreach (compute_out_b_noacc[i]) compute_out_b_noacc[i] = compute_out_b[i][MVM_IMC_OUT_DATA_W-1:0];
  end

  assign imc_bist_mode_merged = imc_bist_mode_i_a | imc_bist_mode_i_b;

  wire clk_imc_bist_g;
  axe_tcl_clk_gating u_comp_cg (
    .i_clk(i_clk),
    .i_en(imc_bist_mode_merged),
    .i_test_en(scan_en),
    .o_clk(clk_imc_bist_g)
  );

  imc_bist_comp #(
    .PAIR_ID(IMC_PAIR_ID),
    .INPUT_DELAY(CompInputDelay)
  ) i_imc_bist_comp (
    .i_clk  (clk_imc_bist_g),
    .i_rst_n(i_rst_n),

    // <-> GEN
    .expect_strobe_i(imc_bist_expect_strobe_i),
    .expect_type_i  (imc_bist_expect_type_i),
    .compare_bus_i  (imc_bist_compare_bus_i),

    // <-> Left IMC BANK
    .lbank_data_i(compute_out_a_noacc),
    // <-> Right IMC BANK
    .rbank_data_i(compute_out_b_noacc),

    // <-> Next COMP
    .compare_bus_o  (imc_bist_compare_bus_o),
    .expect_strobe_o(imc_bist_expect_strobe_o),
    .expect_type_o  (imc_bist_expect_type_o)
  );

  //synopsys translate_off
`ifdef ASSERTIONS_ON
  // Property check can never be satisfied, but we want assert as soon
  // as err_concurrent_exe_prg_on_ws_o is high
  property dual_valid;
    @(posedge i_clk) disable iff (!i_rst_n)
      not (compute_out_valid_a && compute_out_valid_b) or
      (compute_in_data_i[0].bist_mode || compute_in_data_a[0].bist_mode || compute_in_data_o[0].bist_mode);
  endproperty

  dist_mux_dual_valid :
  assert property (dual_valid)
  else $error("Both valid inputs of a dist , this is not allowed!");
`endif
  //synopsys translate_on

endmodule
`endif  // MVM_IMC_ACC_PAIR
