// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>

module dma_coalesce
  import dma_pkg::*;
#(
    parameter int unsigned UNIT_SIZE = 8,
    parameter int unsigned N_UNITS_IF = 64,
    parameter int unsigned N_UNITS_OUT_IF = N_UNITS_IF,
    parameter int unsigned N_UNITS_BUF = 3*N_UNITS_IF,
    localparam type line_ptr_t = logic [$clog2(N_UNITS_IF)-1:0],
    localparam type line_siz_t = logic [$clog2(N_UNITS_IF):0],
    localparam type buf_idx_t  = logic [$clog2(N_UNITS_BUF)-1:0],
    localparam type buf_siz_t  = logic [$clog2(N_UNITS_BUF):0],
    localparam type out_siz_t  = logic [$clog2(N_UNITS_OUT_IF):0]
)
(
    input  wire                             i_clk,
    input  wire                             i_rst_n,

    input  logic                            i_push_req,
    output logic                            o_push_gnt,
    input  logic [UNIT_SIZE*N_UNITS_IF-1:0] i_push_data,
    input  line_ptr_t                       i_push_offset,
    input  line_ptr_t                       i_push_size,

    input  logic                            i_pull_req,
    input  buf_siz_t                        i_pull_size,
    output logic                            o_pull_gnt,
    output logic [UNIT_SIZE*N_UNITS_OUT_IF-1:0] o_pull_data,
    output buf_siz_t                        o_pull_avail,

    input  logic                            i_drain
);

  typedef logic [UNIT_SIZE-1:0] dma_coalesce_unit_t;


  logic      wr_en;
  line_siz_t wr_size;
  logic      rd_en;
  line_siz_t rd_size;
  line_siz_t data_shift;
  buf_siz_t  data_bytes_q, data_bytes_d;
  buf_siz_t  new_data_start_idx;

  dma_coalesce_unit_t [N_UNITS_BUF-1:0] data_buffer_q, data_buffer_d;
  dma_coalesce_unit_t [N_UNITS_BUF-1:0] data_buffer_shifted, data_buffer_new;

  always_comb wr_en = i_push_req && o_push_gnt;
  always_comb rd_en = i_pull_req && o_pull_gnt;

  always_comb o_push_gnt = (N_UNITS_BUF - data_bytes_q) > N_UNITS_IF;

  always_ff @(posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    data_buffer_q <= '0;
    data_bytes_q    <= '0;
  end
  else begin
    data_bytes_q <= data_bytes_d;
    data_buffer_q <= data_buffer_d;
  end

  always_comb wr_size = i_push_size == 0 ? line_siz_t'(N_UNITS_IF) : i_push_size;
  always_comb rd_size = i_pull_size;// == 0 ? line_siz_t'(N_UNITS_IF) : i_pull_size;

  always_comb data_shift = rd_en ? rd_size : dma_bufline_idx_t'(0);
  always_comb data_bytes_d = i_drain ? '0 : data_bytes_q - data_shift + (wr_en ? wr_size: '0);
  always_comb new_data_start_idx = data_bytes_q - data_shift;

  always_comb begin
    for (int unsigned I=0; I<N_UNITS_BUF; I++ )
      if (data_shift + I >= N_UNITS_BUF)
        data_buffer_shifted[I] = '0;
      else
        data_buffer_shifted[I] = data_buffer_q[I+data_shift];
  end

  always_comb begin
    for (int I=0; I<N_UNITS_BUF; I++ )
      if (I < new_data_start_idx)
        data_buffer_new[I] = '0;
      else if (((I - new_data_start_idx) < wr_size) && wr_en)
        data_buffer_new[I] = i_push_data[(I-new_data_start_idx+i_push_offset)*8+:8];
      else
        data_buffer_new[I] = '0;
  end

  always_comb begin
    for (int unsigned I=0; I<N_UNITS_BUF; I++ )
        data_buffer_d[I] = data_buffer_shifted[I] | data_buffer_new[I];
  end

  always_comb
    for (int I = 0; I < N_UNITS_OUT_IF; I++)
      o_pull_data[I*UNIT_SIZE +: UNIT_SIZE]  = data_buffer_q[I];
  always_comb o_pull_gnt   = (data_bytes_q >= rd_size) && !i_drain;
  always_comb o_pull_avail =  data_bytes_q;

endmodule
