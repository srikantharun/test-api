// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA
// Owner: Matt Morris <matt.morris@axelera.ai>


module dma_port_arb
#(
    parameter int unsigned N_REQ = 4
)
(
    input  wire          i_clk,
    input  wire          i_rst_n,

    input  logic [N_REQ-1:0] i_req,
    output logic [N_REQ-1:0] o_gnt,
    input  logic             i_last,

    output logic             o_val,
    output logic [$clog2(N_REQ)-1:0] o_idx,
    input  logic             i_ack
);

  typedef logic [N_REQ-1:0] req_onehot_t;
  typedef logic [$clog2(N_REQ)-1:0] req_idx_t;

  logic [2*N_REQ-1:0] arb_req_full;
  logic [N_REQ-1:0] arb_req_rot;
  req_idx_t arb_sel_idx_d, arb_sel_idx_q;
  req_idx_t arb_sel_idx_inc;
  logic      arb_sel_val_d, arb_sel_val_q, arb_sel_val_n;

  always_comb arb_req_full = {i_req[N_REQ-2:0], i_req};
  always_comb arb_req_rot = req_onehot_t'(arb_req_full >> req_idx_t'(arb_sel_idx_q+1));

  lzc #(.WIDTH(N_REQ),
        .MODE(1'b0))
  u_lzc (
    .in_i (arb_req_rot),
    .cnt_o(arb_sel_idx_inc),
    .empty_o(arb_sel_val_n)
  );

  always_comb arb_sel_val_d = !arb_sel_val_n;
  always_comb arb_sel_idx_d = req_idx_t'(arb_sel_idx_q + arb_sel_idx_inc + 1);

  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    arb_sel_val_q <= 1'b0;
    arb_sel_idx_q <= '0;
  end
  else if (arb_sel_val_d && i_ack & (!arb_sel_idx_q || i_last)) begin
    arb_sel_val_q <= arb_sel_val_d;
    arb_sel_idx_q <= arb_sel_idx_d;
  end

  always_comb o_val = arb_sel_val_d;
  always_comb o_idx = arb_sel_idx_d;
  always_comb o_gnt = req_onehot_t'(arb_sel_val_d && i_ack) << arb_sel_idx_d;

endmodule
