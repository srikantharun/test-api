// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// The par2bser drainer toggles between IFD0 and IFD2 every 8 cycles, starting at IFD2.
// The module is only active when INT16 inputs are enabled, it is passthrough otherwise.
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module mvm_int16_par2bser_drainer
  import mvm_pkg::*;
#(
  parameter int unsigned DATA_W = 8,
  parameter int unsigned PW_LEN = 64,
  parameter int unsigned UIN = 576
) (
  input  wire  i_clk,
  input  wire  i_rst_n,

  input  logic i_enable,

  // Serial Input IFD0 - low byte stream
  input  logic            i_sifd0_cmd_tvalid,
  output logic            o_sifd0_cmd_tready,
  input  imc_acc_dp_cmd_t i_sifd0_cmd_tdata,
  input  logic            i_sifd0_uin_valid,
  input  logic [UIN -1:0] i_sifd0_uin,

  // Serial Input IFD2 - high byte stream
  input  logic            i_sifd2_cmd_tvalid,
  output logic            o_sifd2_cmd_tready,
  input  imc_acc_dp_cmd_t i_sifd2_cmd_tdata,
  input  logic            i_sifd2_uin_valid,
  input  logic [UIN -1:0] i_sifd2_uin,

  // Serial Output IFD0 - serial interleaved highs and lows
  output logic            o_sifd0_cmd_tvalid,
  input  logic            i_sifd0_cmd_tready,
  output imc_acc_dp_cmd_t o_sifd0_cmd_tdata,
  output logic            o_sifd0_uin_valid,
  output logic [UIN -1:0] o_sifd0_uin,

  // Serial Output IFD2 - for passthrough if disabled
  output logic            o_sifd2_cmd_tvalid,
  input  logic            i_sifd2_cmd_tready,
  output imc_acc_dp_cmd_t o_sifd2_cmd_tdata,
  output logic            o_sifd2_uin_valid,
  output logic [UIN -1:0] o_sifd2_uin
);

  imc_acc_dp_cmd_t s_sifd2_cmd_tdata_adj;
  // 16-beat counter, use MSB to pick which input interface is used
  logic [3:0] r_transaction_counter, s_transaction_counter;
  logic mux_selector;

  // Mux selector
  // If 0, use IFD0
  // If 1, use IFD2
  assign mux_selector = ~r_transaction_counter[3];

  always_comb begin : transaction_count_cproc
         if(~i_enable   ) s_transaction_counter = '0;
    else if(mux_selector) s_transaction_counter = r_transaction_counter + (i_sifd2_cmd_tvalid & i_sifd0_cmd_tready);
    else                  s_transaction_counter = r_transaction_counter + (i_sifd0_cmd_tvalid & i_sifd0_cmd_tready);
  end : transaction_count_cproc

  always_ff @(posedge i_clk, negedge i_rst_n)
         if(~i_rst_n ) r_transaction_counter <= '0;
    else if(~i_enable) r_transaction_counter <= '0;
    else if( i_enable) r_transaction_counter <= s_transaction_counter;

  always_comb begin
    s_sifd2_cmd_tdata_adj = i_sifd2_cmd_tdata;
    // Adjust header when reading from IFD2:
    s_sifd2_cmd_tdata_adj.acc_dp_cmd_sig.acc_shift_pos     += 'd8; // adjust shift pos accounting that we are in high byte
    s_sifd2_cmd_tdata_adj.acc_dp_cmd_sig.acc_output_enable  = '0;  // output on low byte only
    s_sifd2_cmd_tdata_adj.out_dp_cmd_sig.tlast              = '0;  // last on low byte only (?)
  end

  always_comb begin : output_cproc
    if(i_enable) begin
      // Serial Input IFD0 - low byte stream (backpressure when selecting IFD2)
      o_sifd0_cmd_tready = mux_selector ? 1'b0 : i_sifd0_cmd_tready;
      // Serial Input IFD2 - high byte stream (backpressure when selecting IFD0)
      o_sifd2_cmd_tready = mux_selector ? i_sifd0_cmd_tready : 1'b0;
      // Serial Output IFD0 - serial interleaved highs and lows
      o_sifd0_cmd_tvalid = mux_selector ? i_sifd2_cmd_tvalid    : i_sifd0_cmd_tvalid ;
      o_sifd0_cmd_tdata  = mux_selector ? s_sifd2_cmd_tdata_adj : i_sifd0_cmd_tdata  ;
      o_sifd0_uin_valid  = mux_selector ? i_sifd2_uin_valid     : i_sifd0_uin_valid  ;
      o_sifd0_uin        = mux_selector ? i_sifd2_uin           : i_sifd0_uin        ;
      // Serial Output IFD2 - for passthrough if disabled
      o_sifd2_cmd_tvalid = 1'b0;
      o_sifd2_cmd_tdata  = s_sifd2_cmd_tdata_adj;
      o_sifd2_uin_valid  = 1'b0;
      o_sifd2_uin        = i_sifd2_uin;
    end else begin
      o_sifd0_cmd_tready = i_sifd0_cmd_tready;
      o_sifd2_cmd_tready = i_sifd2_cmd_tready;
      o_sifd0_cmd_tvalid = i_sifd0_cmd_tvalid;
      o_sifd0_cmd_tdata  = i_sifd0_cmd_tdata;
      o_sifd0_uin_valid  = i_sifd0_uin_valid;
      o_sifd0_uin        = i_sifd0_uin;
      o_sifd2_cmd_tvalid = i_sifd2_cmd_tvalid;
      o_sifd2_cmd_tdata  = i_sifd2_cmd_tdata;
      o_sifd2_uin_valid  = i_sifd2_uin_valid;
      o_sifd2_uin        = i_sifd2_uin;
    end
  end : output_cproc

`ifndef SYNTHESIS
  if (PW_LEN%2) $fatal("PW_LEN must be a multiple of 2");
`endif

endmodule : mvm_int16_par2bser_drainer
