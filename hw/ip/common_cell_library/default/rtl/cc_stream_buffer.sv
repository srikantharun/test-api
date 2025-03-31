// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: A simple wrapper around the sync_fifo.
// This wrapper converts the interface of the sync_fifo in to a rdy/vld interface
// and it removes unneeded interfaces like the 'almost_empty' 'almost_full'
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CC_STREAM_BUFFER_SV_
`define _CC_STREAM_BUFFER_SV_

module cc_stream_buffer #(
  parameter int unsigned DEPTH           = 32,
  parameter int unsigned DW              = 32,
  parameter int unsigned USE_MACRO       = 0,
  parameter bit          RESET_DATA_FLOP = 1

) (
  input wire  i_clk,
  input logic i_rst_n,

  input  logic              wr_vld,
  input  logic [DW - 1 : 0] wr_data,
  output logic              wr_rdy,

  input  logic              rd_rdy,
  output logic [DW - 1 : 0] rd_data,
  output logic              rd_vld

);

  logic rd_req;
  logic rd_empty;
  logic wr_req;
  logic wr_full;

  // sync fifo will otherwise throw assert (but should support without mask)
  assign wr_req = wr_vld & (~wr_full);
  assign wr_rdy = ~wr_full;
  // sync fifo will otherwise throw assert (but should support without mask)
  assign rd_req = rd_rdy & (~rd_empty);
  assign rd_vld = (~rd_empty);

  sync_fifo #(
    .FIFO_DEPTH(DEPTH),
    .data_t(logic [DW-1:0]),
    .MEM_MACRO_USE(USE_MACRO),
    .MEM_MACRO_TYPE(0),
    .RESET_DATA_FLOP(RESET_DATA_FLOP),
    .ALMOST_EMPTY_THR(0),
    .ALMOST_FULL_THR(1)
  ) i_sync_fifo (

    .i_clk (i_clk),
    .i_rst_n(i_rst_n),

    .rd_req_i(rd_req),
    .rd_data_o(rd_data),
    .empty_o(rd_empty),
    .almost_empty_o(), // ASO-UNUSED_OUTPUT: not used

    .wr_req_i(wr_req),
    .wr_data_i(wr_data),
    .full_o(wr_full),
    .almost_full_o() // ASO-UNUSED_OUTPUT: not used
  );

endmodule

`endif  // _CC_STREAM_BUFFER_SV_
