// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: actual memory block within L2 module
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_MEM_SV
`define L2_MEM_SV

module l2_mem
  import l2_pkg::*;
  import l2_cfg_pkg::*;
  (
  // Clock and reset signals
  input  wire                    i_clk,
  input  wire                    i_rst_n,
  // RAM interface signals
  input  l2_mem_req_t            i_mem_req,
  output logic                   o_mem_rd_ready,
  output logic                   o_mem_wr_ready,
  output l2_mem_rsp_t            o_mem_rsp,

  // SRAM configuration
  input  axe_tcl_sram_pkg::impl_inp_t i_impl,
  output axe_tcl_sram_pkg::impl_oup_t o_impl

);
  // =====================================================
  // Local parameters
  // =====================================================

  // =====================================================
  // Type definition
  // =====================================================

  // =====================================================
  // Signal declarations
  // =====================================================
  axe_tcl_sram_pkg::impl_inp_t  [L2_NUM_BANKS-1:0][L2_NUM_RAMS-1:0][L2_NUM_SRAMS-1:0] cfg_sram_inp;
  axe_tcl_sram_pkg::impl_oup_t  [L2_NUM_BANKS-1:0][L2_NUM_RAMS-1:0][L2_NUM_SRAMS-1:0] cfg_sram_oup;
  l2_bank_req_t                 [L2_NUM_BANKS-1:0]                                    bank_req;
  l2_ram_rsp_t                  [L2_NUM_BANKS-1:0]                                    bank_rsp;

  // =====================================================
  // RTL
  // =====================================================

  axe_tcl_sram_arb_cfg #(
    .NUM_BANKS      (L2_NUM_BANKS),
    .NUM_RAMS       (L2_NUM_RAMS),
    .NUM_SRAMS      (L2_NUM_SRAMS),
    .ARB_CHAIN_ARR  (L2_ARB_CHAIN_ORDER)
  ) u_sram_cfg (
    .i_s(i_impl),
    .o_s(o_impl),
    .o_m(cfg_sram_inp),
    .i_m(cfg_sram_oup)
  );

  l2_xbar u_l2_xbar (
    // Clock and reset signals
    .i_clk           (i_clk),
    .i_rst_n         (i_rst_n),
    // MEM interface signals
    .i_mem_req       (i_mem_req),
    .o_mem_rd_ready  (o_mem_rd_ready),
    .o_mem_wr_ready  (o_mem_wr_ready),
    .o_mem_rsp       (o_mem_rsp),
    // Bank interface signals
    .o_bank_req      (bank_req),
    .i_bank_rsp      (bank_rsp)
  );

  for (genvar bank = 0; bank < L2_NUM_BANKS; bank++) begin : g_bank
  l2_bank u_l2_bank (
    // Clock and reset signals
    .i_clk           (i_clk),
    .i_rst_n         (i_rst_n),
    // RAM interface signals
    .i_bank_req      (bank_req[bank]),
    .o_bank_rsp      (bank_rsp[bank]),
    // Memory configutation pins
    .i_impl          (cfg_sram_inp[bank]),
    .o_impl          (cfg_sram_oup[bank])
  );
  end

endmodule

`endif  // L2_MEM_SV
