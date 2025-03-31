// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IMC BIST pattern generator wrapper
// CBIST and MBIST
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef IMC_BIST_AIC_GEN_SV
`define IMC_BIST_AIC_GEN_SV

module imc_bist_gen
  import imc_bist_pkg::bist_type_e;
  import imc_bist_pkg::expect_type_e;
  import imc_bist_pkg::E_IMC_MBIST;
  import imc_bist_pkg::E_IMC_CBIST;
  import mvm_pkg::DATA_W;
  import imc_bank_pkg::IMC_NB_ROWS;
  import imc_bank_pkg::IMC_NB_COLS_PER_BANK;
  import imc_bank_pkg::IMC_ROW_PW;
  import imc_bank_pkg::IMC_WEIGHT_SET_PW;
  import imc_bank_pkg::IMC_BLOCK_ENABLE_W;
(
  input wire i_clk,
  input wire i_rst_n,

  // <-> CTL
  input logic start_pi,
  input logic resume_pi,
  input logic stop_pi,
  input bist_type_e bist_type_i,
  output logic busy_o,

  // <-> IMUX
  output logic write_enable_o,
  output logic [IMC_NB_COLS_PER_BANK-1:0][DATA_W-1:0] write_values_o,
  output logic [IMC_ROW_PW-1:0] write_row_o,
  output logic [IMC_WEIGHT_SET_PW-1:0] write_wss_o,

  // <-> IMUXC
  output logic compute_enable_o,
  output logic [IMC_BLOCK_ENABLE_W-1:0] compute_block_enable_o,
  output logic compute_gate_clock_o,
  output logic compute_signed_weights_o,
  output logic [IMC_NB_ROWS-1:0] compute_inp_o,
  output logic [IMC_WEIGHT_SET_PW-1:0] compute_wss_o,

  // <-> COMP
  output logic expect_strobe_o,
  output expect_type_e expect_type_o
);

  typedef struct packed {
    logic start_p;
    logic resume_p;
    logic stop_p;
  } demux_t;

  typedef struct packed {
    logic busy;
    logic write_enable;
    logic [IMC_ROW_PW-1:0] write_row;
    logic [IMC_WEIGHT_SET_PW-1:0] write_wss;
    logic compute_enable;
    logic [IMC_BLOCK_ENABLE_W-1:0] compute_block_enable;
    logic compute_gate_clock;
    logic compute_signed_weights;
    logic [IMC_NB_ROWS-1:0] compute_inp;
    logic [IMC_WEIGHT_SET_PW-1:0] compute_wss;
    logic expect_strobe;
    expect_type_e expect_type;
  } mux_t;

  logic [1:0] i_cgdemux_clk;
  logic r_mux_sel;
  logic s_in_mux_sel;
  logic s_out_mux_sel;

  demux_t s_demux_in;
  demux_t [1:0] s_demux_int;
  mux_t [1:0] s_mux_int;
  mux_t s_mux_out;

  logic [1:0][IMC_NB_COLS_PER_BANK-1:0][DATA_W-1:0] s_mux_int_write_values;
  logic [IMC_NB_COLS_PER_BANK-1:0][DATA_W-1:0] s_mux_out_write_values;

  assign s_demux_in = '{start_p: start_pi, resume_p: resume_pi, stop_p: stop_pi};

  assign i_cgdemux_clk = {2{i_clk}};

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_mux_sel <= 1'b0;
    else if (start_pi) r_mux_sel <= bist_type_i;

  assign s_in_mux_sel = start_pi ? bist_type_i : r_mux_sel;
  always_comb foreach (s_demux_int[i]) s_demux_int[i] = (s_in_mux_sel == i) ? s_demux_in : '0;

  imc_bist_gen_mbist i_imc_bist_gen_mbist (
    .i_clk  (i_cgdemux_clk[E_IMC_MBIST]),
    .i_rst_n(i_rst_n),

    // <-> CTL
    .start_pi(s_demux_int[E_IMC_MBIST].start_p),
    .resume_pi(s_demux_int[E_IMC_MBIST].resume_p),
    .stop_pi(s_demux_int[E_IMC_MBIST].stop_p),
    .busy_o(s_mux_int[E_IMC_MBIST].busy),

    // <-> IMUX
    .write_enable_o(s_mux_int[E_IMC_MBIST].write_enable),
    .write_values_o(s_mux_int_write_values[E_IMC_MBIST]),
    .write_row_o(s_mux_int[E_IMC_MBIST].write_row),
    .write_wss_o(s_mux_int[E_IMC_MBIST].write_wss),

    // <-> IMUXC
    .compute_enable_o(s_mux_int[E_IMC_MBIST].compute_enable),
    .compute_block_enable_o(s_mux_int[E_IMC_MBIST].compute_block_enable),
    .compute_gate_clock_o(s_mux_int[E_IMC_MBIST].compute_gate_clock),
    .compute_signed_weights_o(s_mux_int[E_IMC_MBIST].compute_signed_weights),
    .compute_inp_o(s_mux_int[E_IMC_MBIST].compute_inp),
    .compute_wss_o(s_mux_int[E_IMC_MBIST].compute_wss),

    // <-> COMP
    .expect_strobe_o(s_mux_int[E_IMC_MBIST].expect_strobe),
    .expect_type_o  (s_mux_int[E_IMC_MBIST].expect_type)
  );

  imc_bist_gen_cbist i_imc_bist_gen_cbist (
    .i_clk  (i_cgdemux_clk[E_IMC_CBIST]),
    .i_rst_n(i_rst_n),

    // <-> CTL
    .start_pi(s_demux_int[E_IMC_CBIST].start_p),
    .resume_pi(s_demux_int[E_IMC_CBIST].resume_p),
    .stop_pi(s_demux_int[E_IMC_CBIST].stop_p),
    .busy_o(s_mux_int[E_IMC_CBIST].busy),

    // <-> IMUX
    .write_enable_o(s_mux_int[E_IMC_CBIST].write_enable),
    .write_values_o(s_mux_int_write_values[E_IMC_CBIST]),
    .write_row_o(s_mux_int[E_IMC_CBIST].write_row),
    .write_wss_o(s_mux_int[E_IMC_CBIST].write_wss),

    // <-> IMUXC
    .compute_enable_o(s_mux_int[E_IMC_CBIST].compute_enable),
    .compute_block_enable_o(s_mux_int[E_IMC_CBIST].compute_block_enable),
    .compute_gate_clock_o(s_mux_int[E_IMC_CBIST].compute_gate_clock),
    .compute_signed_weights_o(s_mux_int[E_IMC_CBIST].compute_signed_weights),
    .compute_inp_o(s_mux_int[E_IMC_CBIST].compute_inp),
    .compute_wss_o(s_mux_int[E_IMC_CBIST].compute_wss),

    // <-> COMP
    .expect_strobe_o(s_mux_int[E_IMC_CBIST].expect_strobe),
    .expect_type_o  (s_mux_int[E_IMC_CBIST].expect_type)
  );

  always_comb
    foreach (s_mux_out_write_values[i])
      s_mux_out_write_values[i] = s_mux_int_write_values[r_mux_sel][i];

  assign s_out_mux_sel = r_mux_sel;
  assign s_mux_out = s_mux_int[s_out_mux_sel];

  assign busy_o = s_mux_out.busy;
  assign write_enable_o = s_mux_out.write_enable;
  assign write_values_o = s_mux_out_write_values;
  assign write_row_o = s_mux_out.write_row;
  assign write_wss_o = s_mux_out.write_wss;
  assign compute_enable_o = s_mux_out.compute_enable;
  assign compute_block_enable_o = s_mux_out.compute_block_enable;
  assign compute_gate_clock_o = s_mux_out.compute_gate_clock;
  assign compute_signed_weights_o = s_mux_out.compute_signed_weights;
  assign compute_inp_o = s_mux_out.compute_inp;
  assign compute_wss_o = s_mux_out.compute_wss;
  assign expect_strobe_o = s_mux_out.expect_strobe;
  assign expect_type_o = s_mux_out.expect_type;

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
`endif  // ASSERTIONS_ON
  //synopsys translate_on

endmodule
`endif  // IMC_BIST_AIC_GEN_SV
