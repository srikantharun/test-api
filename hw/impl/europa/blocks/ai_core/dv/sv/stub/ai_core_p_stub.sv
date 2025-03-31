
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//

module ai_core_p_stub
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

  assign o_aic_boost_req_async = 1'b0;
  assign o_tok_prod_ocpl_m_maddr = '0;
  assign o_tok_prod_ocpl_m_mcmd = 1'b0;
  assign o_tok_prod_ocpl_m_mdata = '0;
  assign o_tok_cons_ocpl_s_scmdaccept = 1'b0;
  assign o_irq = 1'b0;
  assign o_stoptime_async = 1'b0;
  assign o_hart_unavail_async = 1'b0;
  assign o_hart_under_reset_async = 1'b0;
  assign o_aic_obs = {15+1{1'b0}};
  assign o_reserved = {4+1{1'b0}};
  assign o_noc_ht_axi_m_awaddr = {39+1{1'b0}};
  assign o_noc_ht_axi_m_awid = {8+1{1'b0}};
  assign o_noc_ht_axi_m_awlen = {7+1{1'b0}};
  assign o_noc_ht_axi_m_awsize = {AIC_HT_AXI_SIZE_WIDTH-1+1{1'b0}};
  assign o_noc_ht_axi_m_awburst = {AIC_HT_AXI_BURST_TYPE_WIDTH-1+1{1'b0}};
  assign o_noc_ht_axi_m_awcache = {AIC_HT_AXI_CACHE_WIDTH-1+1{1'b0}};
  assign o_noc_ht_axi_m_awprot = {AIC_HT_AXI_PROT_WIDTH-1+1{1'b0}};
  assign o_noc_ht_axi_m_awlock = 1'b0;
  assign o_noc_ht_axi_m_awvalid = 1'b0;
  assign o_noc_ht_axi_m_wdata = {511+1{1'b0}};
  assign o_noc_ht_axi_m_wstrb = {63+1{1'b0}};
  assign o_noc_ht_axi_m_wlast = 1'b0;
  assign o_noc_ht_axi_m_wvalid = 1'b0;
  assign o_noc_ht_axi_m_bready = 1'b1;
  assign o_noc_ht_axi_m_araddr = {39+1{1'b0}};
  assign o_noc_ht_axi_m_arid = {8+1{1'b0}};
  assign o_noc_ht_axi_m_arlen = {7+1{1'b0}};
  assign o_noc_ht_axi_m_arsize = {AIC_HT_AXI_SIZE_WIDTH-1+1{1'b0}};
  assign o_noc_ht_axi_m_arburst = {AIC_HT_AXI_BURST_TYPE_WIDTH-1+1{1'b0}};
  assign o_noc_ht_axi_m_arcache = {AIC_HT_AXI_CACHE_WIDTH-1+1{1'b0}};
  assign o_noc_ht_axi_m_arprot = {AIC_HT_AXI_PROT_WIDTH-1+1{1'b0}};
  assign o_noc_ht_axi_m_arlock = 1'b0;
  assign o_noc_ht_axi_m_arvalid = 1'b0;
  assign o_noc_ht_axi_m_rready = 1'b1;
  assign o_noc_lt_axi_m_awaddr = {39+1{1'b0}};
  assign o_noc_lt_axi_m_awid = {8+1{1'b0}};
  assign o_noc_lt_axi_m_awlen = {7+1{1'b0}};
  assign o_noc_lt_axi_m_awsize = {AIC_LT_AXI_SIZE_WIDTH-1+1{1'b0}};
  assign o_noc_lt_axi_m_awburst = {AIC_LT_AXI_BURST_TYPE_WIDTH-1+1{1'b0}};
  assign o_noc_lt_axi_m_awcache = {AIC_LT_AXI_CACHE_WIDTH-1+1{1'b0}};
  assign o_noc_lt_axi_m_awprot = {AIC_LT_AXI_PROT_WIDTH-1+1{1'b0}};
  assign o_noc_lt_axi_m_awlock = 1'b0;
  assign o_noc_lt_axi_m_awvalid = 1'b0;
  assign o_noc_lt_axi_m_wdata = {63+1{1'b0}};
  assign o_noc_lt_axi_m_wstrb = {7+1{1'b0}};
  assign o_noc_lt_axi_m_wlast = 1'b0;
  assign o_noc_lt_axi_m_wvalid = 1'b0;
  assign o_noc_lt_axi_m_bready = 1'b1;
  assign o_noc_lt_axi_m_araddr = {39+1{1'b0}};
  assign o_noc_lt_axi_m_arid = {8+1{1'b0}};
  assign o_noc_lt_axi_m_arlen = {7+1{1'b0}};
  assign o_noc_lt_axi_m_arsize = {AIC_LT_AXI_SIZE_WIDTH-1+1{1'b0}};
  assign o_noc_lt_axi_m_arburst = {AIC_LT_AXI_BURST_TYPE_WIDTH-1+1{1'b0}};
  assign o_noc_lt_axi_m_arcache = {AIC_LT_AXI_CACHE_WIDTH-1+1{1'b0}};
  assign o_noc_lt_axi_m_arprot = {AIC_LT_AXI_PROT_WIDTH-1+1{1'b0}};
  assign o_noc_lt_axi_m_arlock = 1'b0;
  assign o_noc_lt_axi_m_arvalid = 1'b0;
  assign o_noc_lt_axi_m_rready = 1'b1;
  assign o_noc_lt_axi_s_awready = 1'b1;
  assign o_noc_lt_axi_s_wready = 1'b1;
  assign o_noc_lt_axi_s_bvalid = 1'b0;
  assign o_noc_lt_axi_s_bid = {5+1{1'b0}};
  assign o_noc_lt_axi_s_bresp = {AIC_LT_AXI_RESP_WIDTH-1+1{1'b0}};
  assign o_noc_lt_axi_s_arready = 1'b1;
  assign o_noc_lt_axi_s_rvalid = 1'b0;
  assign o_noc_lt_axi_s_rlast = 1'b0;
  assign o_noc_lt_axi_s_rid = {5+1{1'b0}};
  assign o_noc_lt_axi_s_rdata = {63+1{1'b0}};
  assign o_noc_lt_axi_s_rresp = {AIC_LT_AXI_RESP_WIDTH-1+1{1'b0}};
  assign o_cfg_apb4_s_pready = 1'b1;
  assign o_cfg_apb4_s_prdata = '0;
  assign o_cfg_apb4_s_pslverr = 1'b0;
  assign o_noc_async_idle_req = 1'b0;
  assign o_noc_clken = 1'b0;
  assign o_noc_rst_n = 1'b0;
  assign o_noc_ocpl_tok_async_idle_req = 1'b0;
  assign tdo_en = 1'b0;
  assign tdo = 1'b0;
  assign bisr_so = 1'b0;

endmodule
