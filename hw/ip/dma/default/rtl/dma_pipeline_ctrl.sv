// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA Pipeline Ctrl
// Owner: Matt Morris <matt.morris@axelera.ai>

module dma_pipeline_ctrl
#(
    parameter type dma_pipedata_t = logic
)
(
    input  wire            i_clk,
    input  wire            i_rst_n,

    input  logic           i_us_mv_req,
    output logic           o_us_mv_gnt,

    output logic           o_ds_mv_req,
    input  logic           i_ds_mv_gnt,

    output logic           o_vld_q,

    input  dma_pipedata_t  i_us_pipe_d,
    input  dma_pipedata_t  i_pipe_d,
    output dma_pipedata_t  o_pipe_q,
    input  logic           i_stall,
    input  logic           i_last,
    output logic           o_update

);

  logic mv;

  always_comb mv = i_ds_mv_gnt && (!o_vld_q || !i_stall) && (o_vld_q || i_us_mv_req);
  always_comb o_us_mv_gnt = !o_vld_q || (i_last && mv);
  always_comb o_update = mv;
  always_comb o_ds_mv_req = o_vld_q && !i_stall;

  always_ff @ (posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      o_vld_q    <= 1'b0;
      o_pipe_q <= '0;
    end
    else if (mv) begin
      o_vld_q    <= (i_last || !o_vld_q) ? i_us_mv_req : 1'b1;
      o_pipe_q <= (i_last || !o_vld_q) ? i_us_pipe_d : i_pipe_d;
    end
  end

endmodule
