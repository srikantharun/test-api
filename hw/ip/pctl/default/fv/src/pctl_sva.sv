// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// SVA of pctl
///

`ifndef PCTL_SVA_SV
`define PCTL_SVA_SV

module pctl_sva #(
      parameter int                                 N_FAST_CLKS       = pctl_ao_csr_reg_pkg::MAX_CLOCKS,
      parameter int                                 N_RESETS          = pctl_ao_csr_reg_pkg::MAX_RESETS,
      parameter int                                 N_MEM_PG          = pctl_ao_csr_reg_pkg::MAX_MEM_GRPS,
      parameter int                                 N_FENCES          = pctl_ao_csr_reg_pkg::MAX_FENCES,
      parameter bit [N_FAST_CLKS-1:0][N_RESETS-1:0] CLKRST_MATRIX     = '1,
      parameter bit [N_FAST_CLKS-1:0]               PLL_CLK_IS_I_CLK  = '0,
      parameter bit [$clog2(N_RESETS)-1:0]          NOC_RST_IDX       = 0,
      parameter bit [$clog2(N_FAST_CLKS+1)-1:0]     SYNC_CLK_IDX      = 0,
      parameter bit                                 AUTO_RESET_REMOVE = 1'b0,
      parameter type                                paddr_t           = logic[15:0],
      parameter type                                pdata_t           = logic[31:0],
      parameter type                                pstrb_t           = logic[3:0]
  )
  (

  input wire                     i_clk,
  input wire                     i_ao_rst_n,
  input wire                     i_global_rst_n,
  input logic                    i_test_mode,

  input wire  [N_FAST_CLKS-1:0]  i_pll_clk,
  input wire  [N_FAST_CLKS-1:0]  o_partition_clk,

  input wire  [N_RESETS-1:0]     o_partition_rst_n,
  input wire                     o_ao_rst_sync_n,

  input logic [N_FENCES-1:0]     o_noc_async_idle_req,
  input logic [N_FENCES-1:0]     i_noc_async_idle_ack,
  input logic [N_FENCES-1:0]     i_noc_async_idle_val,
  input logic [N_FAST_CLKS-1:0]  o_noc_clken,
  input logic                    o_noc_rst_n,

  input logic                    o_int_shutdown_req,
  input logic                    i_int_shutdown_ack,

  input logic [N_MEM_PG-1:0]     o_ret,
  input logic [N_MEM_PG-1:0]     o_pde,
  input logic [N_MEM_PG-1:0]     i_prn,

  input logic                    i_global_sync_async,
  input logic                    o_global_sync,

  //////////////////////////////////////////////
  /// SYS_CFG Bus
  //////////////////////////////////////////////

  input paddr_t                  i_cfg_apb4_s_paddr,
  input pdata_t                  i_cfg_apb4_s_pwdata,
  input logic                    i_cfg_apb4_s_pwrite,
  input logic                    i_cfg_apb4_s_psel,
  input logic                    i_cfg_apb4_s_penable,
  input pstrb_t                  i_cfg_apb4_s_pstrb,
  input logic [3-1:0]            i_cfg_apb4_s_pprot,
  input logic                    o_cfg_apb4_s_pready,
  input pdata_t                  o_cfg_apb4_s_prdata,
  input logic                    o_cfg_apb4_s_pslverr,

  input pctl_ao_csr_reg_pkg::apb_h2d_t o_ao_csr_apb_req,
  input pctl_ao_csr_reg_pkg::apb_d2h_t i_ao_csr_apb_rsp

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

  // =====================================================
  // Bind signals
  // =====================================================

  // =====================================================
  // Properties
  // =====================================================
  property p_paddr_limit;
    @(posedge i_clk) disable iff (~o_ao_rst_sync_n)
    (i_cfg_apb4_s_paddr < 'h1000);
  endproperty
  property p_ignore_strobes;
    @(posedge i_clk) disable iff (~o_ao_rst_sync_n)
    (i_cfg_apb4_s_pstrb ==  pstrb_t'('1));
  endproperty
  // =====================================================
  // Assumes
  // =====================================================
  ap_paddr_limit         : assume property(p_paddr_limit);
  // TODO: @(manuel.oliveira) Check if we want to keep ignoring strobes #1618
  ap_ignore_strobes      : assume property(p_ignore_strobes);
  // =====================================================
  // Assertions
  // =====================================================

  // =====================================================
  // Covers
  // =====================================================

endmodule

`endif // PCTL_SVA_SV
