// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token manager token_lines to OCPL
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module token_manager_tok_to_ocpl #(
  // TOP
  parameter int unsigned DevIds = 0,
  parameter int unsigned MaxNrTokens = 0,
  parameter int unsigned NrTokens = 0,
  //// Top mapping producer to device:
  parameter int TopMapProdToDev[MaxNrTokens] = '{default: 0}
)(
  input  wire i_clk,
  input  wire i_rst_n,

  // top info:
  input  logic [token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] i_dev_id,
  input  logic [token_manager_pkg::TOKEN_MANAGER_MAX_VUID:0][token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] i_vuid_to_uid,

  // Top connection via OCPL:
  output logic [7:0]  o_ocpl_m_maddr,
  output logic        o_ocpl_m_mcmd,
  input  logic        i_ocpl_m_scmdaccept,
  output logic [7:0]  o_ocpl_m_mdata,

    // local connections for top:
  input  logic [NrTokens-1:0] i_prod_valid,
  output logic [NrTokens-1:0] o_prod_ready,

  // interrupt:
  output logic o_irq
);

  logic [token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] pp;
  logic [NrTokens-1:0][token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] pc;
  logic [NrTokens-1:0] pc_error;
  logic [token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] pc_rr;
  logic vld_rr;
  logic rdy_rr;

  logic err_d, err_q;

  // Get Physical Producer (dev id of this device)
  always_comb pp = i_dev_id;

  // VUID to UID lookup for the Physical Consumer
  always_comb begin
    for (int d=0; d<NrTokens; d++) begin
      pc[d] = i_vuid_to_uid[TopMapProdToDev[d]];
      pc_error[d] = (i_vuid_to_uid[TopMapProdToDev[d]]==0);
    end
  end

  always_comb err_d = |(pc_error & i_prod_valid);
  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n)
      err_q <= 1'b0;
    else if (err_q != err_d)
      err_q <= err_d;
  end
  always_comb o_irq = err_q;

  // Round robin over all tokens:
  cc_stream_round_robin_arbiter #(
    .data_t(logic[$bits(pc_rr)-1:0]),
    .N_INP(NrTokens),
    .ARBITER("rr")
  ) u_rr (
    .i_clk,
    .i_rst_n,

    .inp_data_i(pc),
    .inp_valid_i(i_prod_valid & ~pc_error),
    .inp_ready_o(o_prod_ready),

    .oup_data_o(pc_rr),
    .oup_valid_o(vld_rr),
    .oup_ready_i(rdy_rr)
  );

  // Stream to OCPL via shielding FIFO:
  cc_stream_buffer #(
    .DEPTH(2),
    .DW(2 * token_manager_pkg::TOKEN_MANAGER_UID_W)
  ) u_fifo (
    .i_clk,
    .i_rst_n,

    .wr_vld(vld_rr),
    .wr_data({pc_rr, pp}),
    .wr_rdy(rdy_rr),

    .rd_rdy(i_ocpl_m_scmdaccept),
    .rd_data({o_ocpl_m_maddr[$bits(pc_rr)-1:0], o_ocpl_m_mdata[$bits(pp)-1:0]}),
    .rd_vld(o_ocpl_m_mcmd)
  );

endmodule
