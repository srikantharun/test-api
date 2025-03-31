// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: OSR tracking, only pass through request when response can be absorbed
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module l1_osr_track
  import l1_pkg::*, mmio_pkg::*;
#(
  parameter type mmio_req_t = mmio_pkg::mmio_dmc_full_req_t,
  parameter type mmio_rsp_t = mmio_pkg::mmio_dmc_full_rsp_t,
  parameter uint_t MAX_OSR = 4,
  parameter uint_t MNGR_RSP_ALWAYS_READY = 0
)
(
  // Clock and reset signal
  input  wire                         i_clk,
  input  wire                         i_rst_n,

  output logic                        o_idle_n,

  input  mmio_req_t                   i_mmio_req,
  output mmio_rsp_t                   o_mmio_rsp,

  output mmio_req_t                   o_mmio_req,
  input  mmio_rsp_t                   i_mmio_rsp
);

  localparam uint_t RSP_PAYLOAD_WIDTH = $bits(mmio_rsp_t)-2; // payload is response subtracted by ack and ready

  logic osr_block_req_n;
  logic osr_track_wr_vld;
  logic osr_track_wr_rdy;
  logic osr_track_rd_vld;
  logic osr_track_rd_rdy;

  logic rsp_rd_vld;
  logic rsp_rd_rdy;

  // Idle checking:
  always_comb o_idle_n = osr_track_rd_vld | i_mmio_req.valid;

  // osr tracking
  always_comb osr_block_req_n = osr_track_wr_rdy; // block when osr tracking fifo is full
  always_comb osr_track_wr_vld = i_mmio_req.valid & i_mmio_rsp.ready; // only add tracking entry when other side is ready

    // output req assigns
  always_comb begin
    o_mmio_req.valid = i_mmio_req.valid & osr_block_req_n;
    o_mmio_req.payload = i_mmio_req.payload;
    o_mmio_rsp.ready = osr_block_req_n & i_mmio_rsp.ready;
  end

  // tie response and tracking to input / output and each other:
  always_comb o_mmio_rsp.ack = rsp_rd_vld;
  always_comb rsp_rd_rdy = MNGR_RSP_ALWAYS_READY ? 1'b1: i_mmio_req.rsp_ready;

  logic rsp_rdy_nc;
  if (MNGR_RSP_ALWAYS_READY) always_comb rsp_rdy_nc = i_mmio_req.rsp_ready; //ASO-UNUSED_VARIABLE: in case always ready the rsp_ready is not ues

  always_comb osr_track_rd_rdy = rsp_rd_vld & rsp_rd_rdy;

  if (MNGR_RSP_ALWAYS_READY) begin : g_pipe_rsp_only
    always_comb o_mmio_req.rsp_ready = 1'b1; // never back-pressure response data

    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (i_rst_n == 1'b0) begin
        o_mmio_rsp.payload <= '0;
        rsp_rd_vld <= 1'b0;
      end else begin
        if (i_mmio_rsp.ack | rsp_rd_vld) // flop in the response valid
          rsp_rd_vld <= i_mmio_rsp.ack;
        if (i_mmio_rsp.ack)  // flop in the response data
          o_mmio_rsp.payload <= i_mmio_rsp.payload;
      end
    end
  end else begin : g_osr_track
  // Response path:
  cc_stream_buffer #(
    .DEPTH(MAX_OSR),
    .DW(RSP_PAYLOAD_WIDTH)
  ) u_rsp_fifo (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld(i_mmio_rsp.ack),
    .wr_data(i_mmio_rsp.payload),
    .wr_rdy(o_mmio_req.rsp_ready),
    .rd_vld(rsp_rd_vld),
    .rd_data(o_mmio_rsp.payload),
    .rd_rdy(rsp_rd_rdy)
  );
  end

  // OSR tracking path:
  cc_stream_buffer #(
    .DEPTH(MAX_OSR),
    .DW(1)
  ) u_osr_track_fifo (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld(osr_track_wr_vld),
    .wr_data(1'b0),
    .wr_rdy(osr_track_wr_rdy),
    .rd_vld(osr_track_rd_vld),
    .rd_data(), // ASO-UNUSED_OUTPUT: Only caring about vld and ready
    .rd_rdy(osr_track_rd_rdy)
  );


endmodule
