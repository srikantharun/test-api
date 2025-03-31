
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
module ai_core_p
  import aic_common_pkg::*;
  import aic_ls_pkg::*;
  import dmc_pkg::*;
(
  /// Fast Clock, positive edge triggered
  input   wire i_clk,
  /// Ref Clock, positive edge triggered
  input   wire i_ref_clk,
  /// Asynchronous POR / always On reset, active low
  input   wire i_ao_rst_n,
  /// Asynchronous global reset, active low
  input   wire i_global_rst_n,

  input logic i_inter_core_sync,

  input logic i_thermal_throttle_async,
  input logic i_clock_throttle_async,
  input logic i_aic_throttle_async,
  input logic i_thermal_warning_async,
  input logic i_aic_boost_ack_async,
  output logic o_aic_boost_req_async,

  input logic  [AIC_CID_WIDTH-1:0] i_cid,
  output chip_pkg::chip_ocpl_token_addr_t o_tok_prod_ocpl_m_maddr,
  output logic       o_tok_prod_ocpl_m_mcmd,
  input  logic       i_tok_prod_ocpl_m_scmdaccept,
  output chip_pkg::chip_ocpl_token_data_t o_tok_prod_ocpl_m_mdata,
  input  chip_pkg::chip_ocpl_token_addr_t i_tok_cons_ocpl_s_maddr,
  input  logic       i_tok_cons_ocpl_s_mcmd,
  output logic       o_tok_cons_ocpl_s_scmdaccept,
  input  chip_pkg::chip_ocpl_token_data_t i_tok_cons_ocpl_s_mdata,
  output logic  o_irq,
  input  logic i_msip_async,
  input  logic i_mtip_async,
  input  logic i_debug_int_async,
  input  logic i_resethaltreq_async,
  output logic o_stoptime_async,
  output logic o_hart_unavail_async,
  output logic o_hart_under_reset_async,
  inout  wire io_ibias_ts,
  inout  wire io_vsense_ts,
  output logic  [15:0] o_aic_obs,
  input  logic  [4:0] i_reserved,
  output logic  [4:0] o_reserved,
  output logic  [39:0] o_noc_ht_axi_m_awaddr,
  output logic  [8:0] o_noc_ht_axi_m_awid,
  output logic  [7:0] o_noc_ht_axi_m_awlen,
  output logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_awsize,
  output logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_awburst,
  output logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_awcache,
  output logic  [AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_awprot,
  output logic   o_noc_ht_axi_m_awlock,
  output logic   o_noc_ht_axi_m_awvalid,
  input logic   i_noc_ht_axi_m_awready,
  output logic  [511:0] o_noc_ht_axi_m_wdata,
  output logic  [63:0] o_noc_ht_axi_m_wstrb,
  output logic   o_noc_ht_axi_m_wlast,
  output logic   o_noc_ht_axi_m_wvalid,
  input logic   i_noc_ht_axi_m_wready,
  input logic   i_noc_ht_axi_m_bvalid,
  input logic  [8:0] i_noc_ht_axi_m_bid,
  input logic  [AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_bresp,
  output logic   o_noc_ht_axi_m_bready,
  output logic  [39:0] o_noc_ht_axi_m_araddr,
  output logic  [8:0] o_noc_ht_axi_m_arid,
  output logic  [7:0] o_noc_ht_axi_m_arlen,
  output logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_arsize,
  output logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_arburst,
  output logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_arcache,
  output logic  [AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_arprot,
  output logic   o_noc_ht_axi_m_arlock,
  output logic   o_noc_ht_axi_m_arvalid,
  input logic   i_noc_ht_axi_m_arready,
  input logic   i_noc_ht_axi_m_rvalid,
  input logic   i_noc_ht_axi_m_rlast,
  input logic  [8:0] i_noc_ht_axi_m_rid,
  input logic  [511:0] i_noc_ht_axi_m_rdata,
  input logic  [AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_rresp,
  output logic   o_noc_ht_axi_m_rready,
  output logic  [39:0] o_noc_lt_axi_m_awaddr,
  output logic  [8:0] o_noc_lt_axi_m_awid,
  output logic  [7:0] o_noc_lt_axi_m_awlen,
  output logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_awsize,
  output logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_awburst,
  output logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_awcache,
  output logic  [AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_awprot,
  output logic   o_noc_lt_axi_m_awlock,
  output logic   o_noc_lt_axi_m_awvalid,
  input logic   i_noc_lt_axi_m_awready,
  output logic  [63:0] o_noc_lt_axi_m_wdata,
  output logic  [7:0] o_noc_lt_axi_m_wstrb,
  output logic   o_noc_lt_axi_m_wlast,
  output logic   o_noc_lt_axi_m_wvalid,
  input logic   i_noc_lt_axi_m_wready,
  input logic   i_noc_lt_axi_m_bvalid,
  input logic  [8:0] i_noc_lt_axi_m_bid,
  input logic  [AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_bresp,
  output logic   o_noc_lt_axi_m_bready,
  output logic  [39:0] o_noc_lt_axi_m_araddr,
  output logic  [8:0] o_noc_lt_axi_m_arid,
  output logic  [7:0] o_noc_lt_axi_m_arlen,
  output logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_arsize,
  output logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_arburst,
  output logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_arcache,
  output logic  [AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_arprot,
  output logic   o_noc_lt_axi_m_arlock,
  output logic   o_noc_lt_axi_m_arvalid,
  input logic   i_noc_lt_axi_m_arready,
  input logic   i_noc_lt_axi_m_rvalid,
  input logic   i_noc_lt_axi_m_rlast,
  input logic  [8:0] i_noc_lt_axi_m_rid,
  input logic  [63:0] i_noc_lt_axi_m_rdata,
  input logic  [AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_rresp,
  output logic   o_noc_lt_axi_m_rready,
  input logic  [39:0] i_noc_lt_axi_s_awaddr,
  input logic  [5:0] i_noc_lt_axi_s_awid,
  input logic  [7:0] i_noc_lt_axi_s_awlen,
  input logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_awsize,
  input logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_awburst,
  input logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_awcache,
  input logic  [AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_awprot,
  input logic   i_noc_lt_axi_s_awlock,
  input logic   i_noc_lt_axi_s_awvalid,
  output logic   o_noc_lt_axi_s_awready,
  input logic  [63:0] i_noc_lt_axi_s_wdata,
  input logic  [7:0] i_noc_lt_axi_s_wstrb,
  input logic   i_noc_lt_axi_s_wlast,
  input logic   i_noc_lt_axi_s_wvalid,
  output logic   o_noc_lt_axi_s_wready,
  output logic   o_noc_lt_axi_s_bvalid,
  output logic  [5:0] o_noc_lt_axi_s_bid,
  output logic  [AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_bresp,
  input logic   i_noc_lt_axi_s_bready,
  input logic  [39:0] i_noc_lt_axi_s_araddr,
  input logic  [5:0] i_noc_lt_axi_s_arid,
  input logic  [7:0] i_noc_lt_axi_s_arlen,
  input logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_arsize,
  input logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_arburst,
  input logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_arcache,
  input logic  [AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_arprot,
  input logic   i_noc_lt_axi_s_arlock,
  input logic   i_noc_lt_axi_s_arvalid,
  output logic   o_noc_lt_axi_s_arready,
  output logic   o_noc_lt_axi_s_rvalid,
  output logic   o_noc_lt_axi_s_rlast,
  output logic  [5:0] o_noc_lt_axi_s_rid,
  output logic  [63:0] o_noc_lt_axi_s_rdata,
  output logic  [AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_rresp,
  input logic   i_noc_lt_axi_s_rready,


  // APB
  input  chip_pkg::chip_syscfg_addr_t     i_cfg_apb4_s_paddr,
  input  chip_pkg::chip_apb_syscfg_data_t i_cfg_apb4_s_pwdata,
  input  logic                            i_cfg_apb4_s_pwrite,
  input  logic                            i_cfg_apb4_s_psel,
  input  logic                            i_cfg_apb4_s_penable,
  input  chip_pkg::chip_apb_syscfg_strb_t i_cfg_apb4_s_pstrb,
  input  logic          [3-1:0]           i_cfg_apb4_s_pprot,
  output logic                            o_cfg_apb4_s_pready,
  output chip_pkg::chip_apb_syscfg_data_t o_cfg_apb4_s_prdata,
  output logic                            o_cfg_apb4_s_pslverr,

  output logic                  o_noc_async_idle_req,
  input  logic                  i_noc_async_idle_ack,
  input  logic                  i_noc_async_idle_val,
  output logic                  o_noc_clken,
  output logic                  o_noc_rst_n,

  output logic                  o_noc_ocpl_tok_async_idle_req,
  input  logic                  i_noc_ocpl_tok_async_idle_ack,
  input  logic                  i_noc_ocpl_tok_async_idle_val,


  input wire  tck,
  input wire  trst,
  input logic tms,
  input logic tdi,
  output logic tdo_en,
  output logic tdo,

  input logic test_mode,

  input wire  ssn_bus_clk,
  input logic [24 -1: 0] ssn_bus_data_in,
  output logic [24 -1: 0] ssn_bus_data_out,
  input wire  bisr_clk,
  input wire  bisr_reset,
  input logic  bisr_shift_en,
  input logic  bisr_si,
  output logic  bisr_so,
  // aic_mid-specific IMC repair chain
  input wire  imc_bisr_clk,
  input wire  imc_bisr_reset,
  input logic  imc_bisr_shift_en,
  input logic  imc_bisr_si,
  output logic  imc_bisr_so

);

  wire ai_core_clk;
  wire ai_core_rst_n;
  wire ao_rst_sync_n;

  logic sram_ret, sram_pde, sram_prn;

  logic mvm_throttle;

  pctl_ao_csr_reg_pkg::apb_h2d_t    ao_csr_apb_req;
  pctl_ao_csr_reg_pkg::apb_d2h_t    ao_csr_apb_rsp;

  ai_core_cfg_csr_reg_pkg::ai_core_cfg_csr_reg2hw_t    ai_core_cfg_reg2hw;
  ai_core_cfg_csr_reg_pkg::ai_core_cfg_csr_hw2reg_t    ai_core_cfg_hw2reg;
  // --------------------------------------------------------------
  // RTL
  // --------------------------------------------------------------

  ///// PCTL:
  pctl #(
    .N_FAST_CLKS(1),
    .N_RESETS   (1),
    .N_MEM_PG   (1),
    .N_FENCES   (2),
    .N_THROTTLE_PINS(3),
    .CLKRST_MATRIX(1'b1),
    .PLL_CLK_IS_I_CLK(1'b0),
    .AUTO_RESET_REMOVE(1'b0),
    .paddr_t    (chip_pkg::chip_syscfg_addr_t),
    .pdata_t    (chip_pkg::chip_apb_syscfg_data_t),
    .pstrb_t    (chip_pkg::chip_apb_syscfg_strb_t)
  ) u_pctl (
    // Input clocks and resets
    .i_clk(i_ref_clk),
    .i_ao_rst_n,
    .i_global_rst_n,
    .i_test_mode         (test_mode),
    // Output clocks and resets
    .i_pll_clk           (i_clk),
    .o_partition_clk     (ai_core_clk),
    .o_partition_rst_n   (ai_core_rst_n),
    .o_ao_rst_sync_n     (ao_rst_sync_n),
    // Isolation interface
    .o_noc_async_idle_req({o_noc_ocpl_tok_async_idle_req, o_noc_async_idle_req}),
    .i_noc_async_idle_ack({i_noc_ocpl_tok_async_idle_ack, i_noc_async_idle_ack}),
    .i_noc_async_idle_val({i_noc_ocpl_tok_async_idle_val, i_noc_async_idle_val}),
    .o_noc_clken,
    .o_noc_rst_n,
    .o_int_shutdown_req(),
    .i_int_shutdown_ack(1'b1),
    // Memory pwr:
    .o_ret(sram_ret),
    .o_pde(sram_pde),
    .i_prn(sram_prn),
    // core sync:
    .i_global_sync_async(i_inter_core_sync),
    .o_global_sync(inter_core_sync),

    .i_throttle({mvm_throttle_async, i_thermal_throttle_async, i_clock_throttle_async}),

    // SYS_CFG Bus
    .i_cfg_apb4_s_paddr,
    .i_cfg_apb4_s_pwdata,
    .i_cfg_apb4_s_pwrite,
    .i_cfg_apb4_s_psel,
    .i_cfg_apb4_s_penable,
    .i_cfg_apb4_s_pstrb,
    .i_cfg_apb4_s_pprot,
    .o_cfg_apb4_s_pready,
    .o_cfg_apb4_s_prdata,
    .o_cfg_apb4_s_pslverr,
    // External APB interface
    .o_ao_csr_apb_req    (ao_csr_apb_req),
    .i_ao_csr_apb_rsp    (ao_csr_apb_rsp)
  );

  // AI Core AO CSR:
  ai_core_cfg_csr_reg_top u_ai_core_cfg_ao_csr (
    .clk_i    (i_ref_clk),
    .rst_ni   (ao_rst_sync_n),
    .apb_i    (ao_csr_apb_req),
    .apb_o    (ao_csr_apb_rsp),
    // To HW
    .reg2hw   (ai_core_cfg_reg2hw),
    .hw2reg   (ai_core_cfg_hw2reg),
    // Config
    .devmode_i(1'b1)
  );

  // synchronizers:
    // IMC bist status
  logic imc_bist_busy_async;
  logic imc_bist_done_async;
  logic imc_bist_pass_async;
  axe_tcl_seq_sync #(.SyncStages(3)) u_sync_bist_busy (
    .i_clk(i_ref_clk), // should be same as AO CSR
    .i_rst_n(ao_rst_sync_n),
    .i_d(imc_bist_busy_async),
    .o_q(ai_core_cfg_hw2reg.imc_bist_status.imc_bist_busy)
  );
  axe_tcl_seq_sync #(.SyncStages(3)) u_sync_bist_done (
    .i_clk(i_ref_clk), // should be same as AO CSR
    .i_rst_n(ao_rst_sync_n),
    .i_d(imc_bist_done_async),
    .o_q(ai_core_cfg_hw2reg.imc_bist_status.imc_bist_done)
  );
  axe_tcl_seq_sync #(.SyncStages(3)) u_sync_bist_pass (
    .i_clk(i_ref_clk), // should be same as AO CSR
    .i_rst_n(ao_rst_sync_n),
    .i_d(imc_bist_pass_async),
    .o_q(ai_core_cfg_hw2reg.imc_bist_status.imc_bist_pass)
  );

  // tie irq to 0, not used
  always_comb o_irq = '0;

  ai_core u_ai_core (

  .i_clk(ai_core_clk),
  .i_rst_n(ai_core_rst_n),
  .i_ref_clk(i_ref_clk),
  .i_c2c_clk(i_clk),
  .i_ref_rst_n(ao_rst_sync_n),
  .i_cid(i_cid),
  .i_test_mode(test_mode),
  .i_reset_vector({ai_core_cfg_reg2hw.reset_vector_msb,ai_core_cfg_reg2hw.reset_vector_lsb}),
  .i_inter_core_sync(inter_core_sync),
  .i_thermal_throttle_async,
  .i_aic_throttle_async,
  .i_thermal_warning_async,
  .i_aic_boost_ack_async,
  .o_aic_boost_req_async,
  .o_mvm_throttle_async(mvm_throttle_async),
  .o_imc_bist_busy_async(imc_bist_busy_async),
  .o_imc_bist_done_async(imc_bist_done_async),
  .o_imc_bist_pass_async(imc_bist_pass_async),
  .o_tok_prod_ocpl_m_maddr(o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd(o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept(i_tok_prod_ocpl_m_scmdaccept),
  .o_tok_prod_ocpl_m_mdata(o_tok_prod_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_maddr(i_tok_cons_ocpl_s_maddr),
  .i_tok_cons_ocpl_s_mcmd(i_tok_cons_ocpl_s_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept(o_tok_cons_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_mdata(i_tok_cons_ocpl_s_mdata),
  .o_irq(/*open*/),
  .i_msip_async(i_msip_async),
  .i_mtip_async(i_mtip_async),
  .i_debug_int_async(i_debug_int_async),
  .i_resethaltreq_async(i_resethaltreq_async),
  .o_hart_unavail_async(o_hart_unavail_async),
  .o_hart_under_reset_async(o_hart_under_reset_async),
  .o_stoptime_async(o_stoptime_async),
  .io_ibias_ts(io_ibias_ts),
  .io_vsense_ts(io_vsense_ts),
  .o_aic_obs(o_aic_obs),
  .i_reserved(i_reserved),
  .o_reserved(o_reserved),
  .o_noc_ht_axi_m_awaddr(o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid(o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen(o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize(o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst(o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache(o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot(o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock(o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_awvalid(o_noc_ht_axi_m_awvalid),
  .i_noc_ht_axi_m_awready(i_noc_ht_axi_m_awready),
  .o_noc_ht_axi_m_wdata(o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_wstrb(o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wlast(o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wvalid(o_noc_ht_axi_m_wvalid),
  .i_noc_ht_axi_m_wready(i_noc_ht_axi_m_wready),
  .i_noc_ht_axi_m_bvalid(i_noc_ht_axi_m_bvalid),
  .i_noc_ht_axi_m_bid(i_noc_ht_axi_m_bid),
  .i_noc_ht_axi_m_bresp(i_noc_ht_axi_m_bresp),
  .o_noc_ht_axi_m_bready(o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_araddr(o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid(o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen(o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize(o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst(o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache(o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot(o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock(o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_arvalid(o_noc_ht_axi_m_arvalid),
  .i_noc_ht_axi_m_arready(i_noc_ht_axi_m_arready),
  .i_noc_ht_axi_m_rvalid(i_noc_ht_axi_m_rvalid),
  .i_noc_ht_axi_m_rlast(i_noc_ht_axi_m_rlast),
  .i_noc_ht_axi_m_rid(i_noc_ht_axi_m_rid),
  .i_noc_ht_axi_m_rdata(i_noc_ht_axi_m_rdata),
  .i_noc_ht_axi_m_rresp(i_noc_ht_axi_m_rresp),
  .o_noc_ht_axi_m_rready(o_noc_ht_axi_m_rready),
  .o_noc_lt_axi_m_awaddr(o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid(o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen(o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize(o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst(o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache(o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot(o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock(o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_awvalid(o_noc_lt_axi_m_awvalid),
  .i_noc_lt_axi_m_awready(i_noc_lt_axi_m_awready),
  .o_noc_lt_axi_m_wdata(o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_wstrb(o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wlast(o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wvalid(o_noc_lt_axi_m_wvalid),
  .i_noc_lt_axi_m_wready(i_noc_lt_axi_m_wready),
  .i_noc_lt_axi_m_bvalid(i_noc_lt_axi_m_bvalid),
  .i_noc_lt_axi_m_bid(i_noc_lt_axi_m_bid),
  .i_noc_lt_axi_m_bresp(i_noc_lt_axi_m_bresp),
  .o_noc_lt_axi_m_bready(o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_araddr(o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid(o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen(o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize(o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst(o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache(o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot(o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock(o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_arvalid(o_noc_lt_axi_m_arvalid),
  .i_noc_lt_axi_m_arready(i_noc_lt_axi_m_arready),
  .i_noc_lt_axi_m_rvalid(i_noc_lt_axi_m_rvalid),
  .i_noc_lt_axi_m_rlast(i_noc_lt_axi_m_rlast),
  .i_noc_lt_axi_m_rid(i_noc_lt_axi_m_rid),
  .i_noc_lt_axi_m_rdata(i_noc_lt_axi_m_rdata),
  .i_noc_lt_axi_m_rresp(i_noc_lt_axi_m_rresp),
  .o_noc_lt_axi_m_rready(o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_s_awaddr(i_noc_lt_axi_s_awaddr),
  .i_noc_lt_axi_s_awid(i_noc_lt_axi_s_awid),
  .i_noc_lt_axi_s_awlen(i_noc_lt_axi_s_awlen),
  .i_noc_lt_axi_s_awsize(i_noc_lt_axi_s_awsize),
  .i_noc_lt_axi_s_awburst(i_noc_lt_axi_s_awburst),
  .i_noc_lt_axi_s_awcache(i_noc_lt_axi_s_awcache),
  .i_noc_lt_axi_s_awprot(i_noc_lt_axi_s_awprot),
  .i_noc_lt_axi_s_awlock(i_noc_lt_axi_s_awlock),
  .i_noc_lt_axi_s_awvalid(i_noc_lt_axi_s_awvalid),
  .o_noc_lt_axi_s_awready(o_noc_lt_axi_s_awready),
  .i_noc_lt_axi_s_wdata(i_noc_lt_axi_s_wdata),
  .i_noc_lt_axi_s_wstrb(i_noc_lt_axi_s_wstrb),
  .i_noc_lt_axi_s_wlast(i_noc_lt_axi_s_wlast),
  .i_noc_lt_axi_s_wvalid(i_noc_lt_axi_s_wvalid),
  .o_noc_lt_axi_s_wready(o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid(o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid(o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp(o_noc_lt_axi_s_bresp),
  .i_noc_lt_axi_s_bready(i_noc_lt_axi_s_bready),
  .i_noc_lt_axi_s_araddr(i_noc_lt_axi_s_araddr),
  .i_noc_lt_axi_s_arid(i_noc_lt_axi_s_arid),
  .i_noc_lt_axi_s_arlen(i_noc_lt_axi_s_arlen),
  .i_noc_lt_axi_s_arsize(i_noc_lt_axi_s_arsize),
  .i_noc_lt_axi_s_arburst(i_noc_lt_axi_s_arburst),
  .i_noc_lt_axi_s_arcache(i_noc_lt_axi_s_arcache),
  .i_noc_lt_axi_s_arprot(i_noc_lt_axi_s_arprot),
  .i_noc_lt_axi_s_arlock(i_noc_lt_axi_s_arlock),
  .i_noc_lt_axi_s_arvalid(i_noc_lt_axi_s_arvalid),
  .o_noc_lt_axi_s_arready(o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid(o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast(o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid(o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata(o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp(o_noc_lt_axi_s_rresp),
  .i_noc_lt_axi_s_rready(i_noc_lt_axi_s_rready),
  .i_sram_mcs('0), // Should not be used anymore
  .i_sram_mcsw('0), // Should not be used anymore
  .i_sram_ret(sram_ret),
  .i_sram_pde(sram_pde),
  .i_sram_adme('0), // Should not be used anymore
  .o_sram_prn(sram_prn),
  .scan_en(1'b0)
  );


endmodule
