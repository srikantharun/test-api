// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Simple reg stream arbiter with response routing
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module snps_dma_reg_str_bus
#(
  parameter int unsigned OSR = 10, // outstanding requests
  parameter int unsigned REQ_DW = 32,
  parameter int unsigned RESP_DW = 2,
  parameter int unsigned NR_SUBS = 2 // number of subordinates
) (
  input  wire  i_clk,
  input  wire  i_rst_n,

  input  logic [NR_SUBS-1:0]                i_req_vld,
  output logic [NR_SUBS-1:0]                o_req_rdy,
  input  logic [NR_SUBS-1:0] [REQ_DW-1:0]   i_req_data,
  output logic [NR_SUBS-1:0]                o_resp_vld,
  input  logic [NR_SUBS-1:0]                i_resp_rdy,
  output logic [NR_SUBS-1:0] [RESP_DW-1:0]  o_resp_data,

  output logic                              o_req_vld,
  input  logic                              i_req_rdy,
  output logic               [REQ_DW-1:0]   o_req_data,
  input  logic                              i_resp_vld,
  output logic                              o_resp_rdy,
  input  logic               [RESP_DW-1:0]  i_resp_data
);
  logic [$clog2(NR_SUBS)-1:0] arb_wsel;
  logic [$clog2(NR_SUBS)-1:0] arb_rsel;
  logic arb_wrdy, arb_rrdy, arb_rvld;

  // arbiter
  rr_arb_tree #(
    .NumIn(NR_SUBS),
    .DataWidth($bits(o_req_data)),
    .ExtPrio(1'b0), // 0 is round robin, 1 gives priority on rr_i
    .AxiVldRdy(1'b1), // simpler arbiter and normal vld/rdy behavior
    .LockIn(1'b1),
    .FairArb(1'b1)
  ) u_dev2reg_wr_arb (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .flush_i(1'b0),
    .rr_i  ('0),
    .req_i (i_req_vld & arb_wrdy),
    .gnt_o (o_req_rdy),
    .data_i(i_req_data),
    .req_o (o_req_vld),
    .gnt_i (i_req_rdy),
    .data_o(o_req_data),
    .idx_o (arb_wsel)
  );

  // tracking buffer for the response
  cc_stream_buffer #(
    .DEPTH(OSR),
    .DW($clog2(NR_SUBS)),
    .USE_MACRO(0)
  ) u_dev2reg_wr_sel_track (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .wr_vld(o_req_vld & i_req_rdy),
    .wr_data(arb_wsel),
    .wr_rdy(arb_wrdy),
    .rd_rdy(arb_rrdy),
    .rd_data(arb_rsel),
    .rd_vld(arb_rvld)
  );

  always_comb arb_rrdy = i_resp_vld & o_resp_rdy;

  logic [RESP_DW-1:0] resp_data[NR_SUBS];
  logic resp_vld[NR_SUBS];
  logic resp_rdy[NR_SUBS];

  // response mux:
  cc_stream_demux_unpack #(
    .DataWidth(RESP_DW),
    .NumStreams(NR_SUBS),
    .DropOnError(1)
  ) u_resp_demux (
    .i_data(i_resp_data),
    .i_select(arb_rvld ? arb_rsel : '0),
    .i_valid(i_resp_vld),
    .o_ready(o_resp_rdy),
    .o_error(),
    .o_data(resp_data),
    .o_valid(resp_vld),
    .i_ready(resp_rdy)
  );

  always_comb begin
    for (int i=0; i<NR_SUBS; i++) begin
      o_resp_data[i] = resp_data[i];
      o_resp_vld[i]  = resp_vld[i];
      resp_rdy[i]    = i_resp_rdy[i];
    end
  end

endmodule
