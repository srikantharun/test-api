// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA FIFO Logic
// Owner: Matt Morris <matt.morris@axelera.ai>

module dma_fifo_logic
#(
    parameter int unsigned FIFO_DEPTH = 8,
    parameter logic        START_FULL = 1'b0
)
(
    input  wire       i_clk,
    input  wire       i_rst_n,

    input  logic      i_push,
    output logic      o_full_n,
    input  logic      i_pop,
    output logic      o_empty_n,
    output logic [$clog2(FIFO_DEPTH):0]   o_free_entries,

    output logic [$clog2(FIFO_DEPTH)-1:0] o_wr_idx,
    output logic [$clog2(FIFO_DEPTH)-1:0] o_rd_idx

);

  typedef logic [$clog2(FIFO_DEPTH):0] ptr_t;
  ptr_t wr_ptr_q;
  ptr_t rd_ptr_q;
  ptr_t fill;

  always_comb fill      = wr_ptr_q - rd_ptr_q;
  always_comb o_free_entries = ptr_t'(FIFO_DEPTH) - fill;
  always_comb o_empty_n = |fill;
  always_comb o_full_n  = !fill[$clog2(FIFO_DEPTH)];

  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    wr_ptr_q <= ptr_t'(START_FULL << $clog2(FIFO_DEPTH));
  end
  else if (i_push && o_full_n) begin
    wr_ptr_q <= wr_ptr_q + ptr_t'(1);
  end

  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    rd_ptr_q <= '0;
  end
  else if (i_pop && o_empty_n) begin
    rd_ptr_q <= rd_ptr_q + ptr_t'(1);
  end

  always_comb o_wr_idx = wr_ptr_q[$clog2(FIFO_DEPTH)-1:0];
  always_comb o_rd_idx = rd_ptr_q[$clog2(FIFO_DEPTH)-1:0];

endmodule
