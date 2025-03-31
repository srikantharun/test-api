// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp Logger stream arbiter with response tracking and priority selection based on parameter
//              Stream with priority will always go first. Round robin over streams with same priority.
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef TIMESTAMP_LOGGER_STR_ARB_RESP_SV
`define TIMESTAMP_LOGGER_STR_ARB_RESP_SV

module timestamp_logger_str_arb_resp #(
  parameter int unsigned NumOutstanding = 10, // outstanding requests
  parameter int unsigned ReqDw = 32,
  parameter int unsigned RespDw = 2,
  parameter int unsigned NrSubs = 2, // number of subordinates
  parameter type req_data_t = logic[ReqDw-1:0],
  parameter type rsp_data_t = logic[RespDw-1:0],
  parameter logic [$clog2(NrSubs)-1:0] Priority = 0 // which sub has priority
) (
  input  wire                     i_clk,
  input  wire                     i_rst_n,

  input  logic        [NrSubs-1:0] i_req_vld,
  output logic        [NrSubs-1:0] o_req_rdy,
  input  req_data_t   [NrSubs-1:0] i_req_data,
  output logic        [NrSubs-1:0] o_resp_vld,
  input  logic        [NrSubs-1:0] i_resp_rdy,
  output rsp_data_t   [NrSubs-1:0] o_resp_data,

  output logic        o_req_vld,
  input  logic        i_req_rdy,
  output req_data_t   o_req_data,
  input  logic        i_resp_vld,
  output logic        o_resp_rdy,
  input  rsp_data_t   i_resp_data
);
  logic [$clog2(NrSubs)-1:0] arb_track_wsel;
  logic [$clog2(NrSubs)-1:0] arb_track_rsel;
  logic arb_track_wrdy, arb_track_rrdy;
  logic arb_req_vld;

  rsp_data_t resp_data[NrSubs];
  logic resp_vld[NrSubs];
  logic resp_rdy[NrSubs];

  rsp_data_t buf_resp_data;
  logic buf_resp_vld;
  logic buf_resp_rdy;

  always_comb o_req_vld = arb_req_vld & arb_track_wrdy;

  // arbiter
  rr_arb_tree #(
    .NumIn(NrSubs),
    .datatype_t(req_data_t),
    .ExtPrio(1'b1), // 0 is round robin, 1 gives priority on rr_i
    .AxiVldRdy(1'b1), // simpler arbiter and normal vld/rdy behavior
    .LockIn(1'b0),
    .FairArb(1'b1)
  ) u_dev2reg_wr_arb (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .flush_i(1'b0),
    .rr_i  (Priority),
    .req_i (i_req_vld),
    .gnt_o (o_req_rdy),
    .data_i(i_req_data),
    .req_o (arb_req_vld),
    .gnt_i (i_req_rdy & arb_track_wrdy),
    .data_o(o_req_data),
    .idx_o (arb_track_wsel)
  );

  // tracking buffer for the response
  cc_stream_buffer #(
    .DEPTH(NumOutstanding),
    .DW($clog2(NrSubs)),
    .USE_MACRO(0)
  ) u_dev2reg_wr_sel_track (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .wr_vld(arb_req_vld & i_req_rdy),
    .wr_data(arb_track_wsel),
    .wr_rdy(arb_track_wrdy),
    .rd_rdy(arb_track_rrdy),
    .rd_data(arb_track_rsel),
    .rd_vld() // not used
  );

  always_comb arb_track_rrdy = buf_resp_vld & buf_resp_rdy;

  // response mux:
  cc_stream_demux_unpack #(
    .DataWidth(RespDw),
    .NumStreams(NrSubs),
    .DropOnError(1),
    .data_t(rsp_data_t)
  ) u_resp_demux (
    .i_data(buf_resp_data),
    .i_select(buf_resp_vld ? arb_track_rsel : '0),
    .i_valid(buf_resp_vld),
    .o_ready(buf_resp_rdy),
    .o_error(),
    .o_data(resp_data),
    .o_valid(resp_vld),
    .i_ready(resp_rdy)
  );

  // response buffer
  cc_stream_buffer #(
    .DEPTH(NumOutstanding),
    .DW($bits(rsp_data_t)),
    .USE_MACRO(0)
  ) u_resp_buffer (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .wr_vld(i_resp_vld),
    .wr_data(i_resp_data),
    .wr_rdy(o_resp_rdy),
    .rd_rdy(buf_resp_rdy),
    .rd_data(buf_resp_data),
    .rd_vld(buf_resp_vld)
  );

  always_comb begin
    for (int i=0; i<NrSubs; i++) begin
      o_resp_data[i] = resp_data[i];
      o_resp_vld[i]  = resp_vld[i];
      resp_rdy[i]    = i_resp_rdy[i];
    end
  end
endmodule

`endif  // TIMESTAMP_LOGGER_STR_ARB_RESP_SV
