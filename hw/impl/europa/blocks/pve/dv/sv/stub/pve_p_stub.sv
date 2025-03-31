// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// Video Pre / Post Processor
///

module pve_p_stub
  import axi_pkg::*;
  import chip_pkg::*;
  import axe_tcl_sram_pkg::*;
  import pve_pkg::*;
  import svs_monitor_pkg::*;
(
  // Fast Clock, positive edge triggered
  input  wire i_clk,
  // Ref Clock, positive edge triggered
  input  wire i_ref_clk,
  // Asynchronous POR / always On reset, active low
  input  wire i_ao_rst_n,
  // Asynchronous global reset, active low
  input  wire i_global_rst_n,

  // TMS & DLM
  input  logic i_clock_throttle,
  input  logic i_thermal_throttle,

  // NoC isolation interface
  output logic o_noc_async_idle_req,
  input  logic i_noc_async_idle_ack,
  input  logic i_noc_async_idle_val,
  output logic o_noc_clken,
  output logic o_noc_rst_n,

  // PVE ID
  input  pve_hart_base_t i_hart_base,

  // Debug
  input  logic [PVE_N_CPU-1:0] i_debug_req,
  input  logic [PVE_N_CPU-1:0] i_debug_rst_halt_req,

  // Hart status
  output logic [PVE_N_CPU-1:0] o_hart_unavail,
  output logic [PVE_N_CPU-1:0] o_hart_under_reset,

  //////////////////////////////////////////////
  /// SYS_CFG Bus
  //////////////////////////////////////////////

  input  chip_syscfg_addr_t     i_cfg_apb4_s_paddr,
  input  chip_apb_syscfg_data_t i_cfg_apb4_s_pwdata,
  input  logic                  i_cfg_apb4_s_pwrite,
  input  logic                  i_cfg_apb4_s_psel,
  input  logic                  i_cfg_apb4_s_penable,
  input  chip_apb_syscfg_strb_t i_cfg_apb4_s_pstrb,
  input  logic [3-1:0]          i_cfg_apb4_s_pprot,
  output logic                  o_cfg_apb4_s_pready,
  output chip_apb_syscfg_data_t o_cfg_apb4_s_prdata,
  output logic                  o_cfg_apb4_s_pslverr,

  /////////////////////////////////////////////
  // CTRL OUT AXI : AXI Narrow Master Interface
  /////////////////////////////////////////////

  // CTRL OUT AXI : Write Address Channel
  output logic                  o_ctrlo_axi_m_awvalid,
  output pve_lt_axi_m_id_t      o_ctrlo_axi_m_awid,
  output chip_axi_addr_t        o_ctrlo_axi_m_awaddr,
  output axi_len_t              o_ctrlo_axi_m_awlen,
  output axi_size_t             o_ctrlo_axi_m_awsize,
  output axi_burst_t            o_ctrlo_axi_m_awburst,
  output logic                  o_ctrlo_axi_m_awlock,
  output axi_cache_t            o_ctrlo_axi_m_awcache,
  output axi_prot_t             o_ctrlo_axi_m_awprot,
  output axi_qos_t              o_ctrlo_axi_m_awqos,
  output axi_region_t           o_ctrlo_axi_m_awregion,
  output chip_axi_lt_awuser_t   o_ctrlo_axi_m_awuser,
  input  logic                  i_ctrlo_axi_m_awready,

  // CTRL OUT AXI : Write Data Channel
  output logic                  o_ctrlo_axi_m_wvalid,
  output chip_axi_lt_data_t     o_ctrlo_axi_m_wdata,
  output chip_axi_lt_wstrb_t    o_ctrlo_axi_m_wstrb,
  output logic                  o_ctrlo_axi_m_wlast,
  output chip_axi_lt_wuser_t    o_ctrlo_axi_m_wuser,
  input  logic                  i_ctrlo_axi_m_wready,

  // CTRL OUT AXI : Write Response Channel
  input  logic                  i_ctrlo_axi_m_bvalid,
  input  pve_lt_axi_m_id_t      i_ctrlo_axi_m_bid,
  input  axi_resp_t             i_ctrlo_axi_m_bresp,
  input  chip_axi_lt_buser_t    i_ctrlo_axi_m_buser,
  output logic                  o_ctrlo_axi_m_bready,

  // CTRL OUT AXI : Read Address Channel
  output logic                  o_ctrlo_axi_m_arvalid,
  output pve_lt_axi_m_id_t      o_ctrlo_axi_m_arid,
  output chip_axi_addr_t        o_ctrlo_axi_m_araddr,
  output axi_len_t              o_ctrlo_axi_m_arlen,
  output axi_size_t             o_ctrlo_axi_m_arsize,
  output axi_burst_t            o_ctrlo_axi_m_arburst,
  output logic                  o_ctrlo_axi_m_arlock,
  output axi_cache_t            o_ctrlo_axi_m_arcache,
  output axi_prot_t             o_ctrlo_axi_m_arprot,
  output axi_qos_t              o_ctrlo_axi_m_arqos,
  output axi_region_t           o_ctrlo_axi_m_arregion,
  output chip_axi_lt_aruser_t   o_ctrlo_axi_m_aruser,
  input  logic                  i_ctrlo_axi_m_arready,

  // CTRL OUT AXI : Read Data / Response Channel
  input  logic                  i_ctrlo_axi_m_rvalid,
  input  pve_lt_axi_m_id_t      i_ctrlo_axi_m_rid,
  input  chip_axi_lt_data_t     i_ctrlo_axi_m_rdata,
  input  axi_resp_t             i_ctrlo_axi_m_rresp,
  input  logic                  i_ctrlo_axi_m_rlast,
  input  chip_axi_lt_ruser_t    i_ctrlo_axi_m_ruser,
  output logic                  o_ctrlo_axi_m_rready,

  ///////////////////////////////////////////
  // CTRL IN AXI : AXI Narrow Slave Interface
  ///////////////////////////////////////////

  // CTRL IN AXI : Write Address Channel
  input  logic                  i_ctrli_axi_s_awvalid,
  input  pve_lt_axi_s_id_t      i_ctrli_axi_s_awid,
  input  chip_axi_addr_t        i_ctrli_axi_s_awaddr,
  input  axi_len_t              i_ctrli_axi_s_awlen,
  input  axi_size_t             i_ctrli_axi_s_awsize,
  input  axi_burst_t            i_ctrli_axi_s_awburst,
  input  logic                  i_ctrli_axi_s_awlock,
  input  axi_cache_t            i_ctrli_axi_s_awcache,
  input  axi_prot_t             i_ctrli_axi_s_awprot,
  input  axi_qos_t              i_ctrli_axi_s_awqos,
  input  axi_region_t           i_ctrli_axi_s_awregion,
  input  chip_axi_lt_awuser_t   i_ctrli_axi_s_awuser,
  output logic                  o_ctrli_axi_s_awready,

  // CTRL IN AXI : Write Data Channel
  input  logic                  i_ctrli_axi_s_wvalid,
  input  chip_axi_lt_data_t     i_ctrli_axi_s_wdata,
  input  chip_axi_lt_wstrb_t    i_ctrli_axi_s_wstrb,
  input  logic                  i_ctrli_axi_s_wlast,
  input  chip_axi_lt_wuser_t    i_ctrli_axi_s_wuser,
  output logic                  o_ctrli_axi_s_wready,

  // CTRL IN AXI : Write Response Channel
  output logic                  o_ctrli_axi_s_bvalid,
  output pve_lt_axi_s_id_t      o_ctrli_axi_s_bid,
  output axi_resp_t             o_ctrli_axi_s_bresp,
  output chip_axi_lt_buser_t    o_ctrli_axi_s_buser,
  input  logic                  i_ctrli_axi_s_bready,

  // CTRL IN AXI : Read Address Channel
  input  logic                  i_ctrli_axi_s_arvalid,
  input  pve_lt_axi_s_id_t      i_ctrli_axi_s_arid,
  input  chip_axi_addr_t        i_ctrli_axi_s_araddr,
  input  axi_len_t              i_ctrli_axi_s_arlen,
  input  axi_size_t             i_ctrli_axi_s_arsize,
  input  axi_burst_t            i_ctrli_axi_s_arburst,
  input  logic                  i_ctrli_axi_s_arlock,
  input  axi_cache_t            i_ctrli_axi_s_arcache,
  input  axi_prot_t             i_ctrli_axi_s_arprot,
  input  axi_qos_t              i_ctrli_axi_s_arqos,
  input  axi_region_t           i_ctrli_axi_s_arregion,
  input  chip_axi_lt_aruser_t   i_ctrli_axi_s_aruser,
  output logic                  o_ctrli_axi_s_arready,

  // DMA AXI : Read Data / Response Channel
  output logic                  o_ctrli_axi_s_rvalid,
  output pve_lt_axi_s_id_t      o_ctrli_axi_s_rid,
  output chip_axi_lt_data_t     o_ctrli_axi_s_rdata,
  output axi_resp_t             o_ctrli_axi_s_rresp,
  output logic                  o_ctrli_axi_s_rlast,
  output chip_axi_lt_ruser_t    o_ctrli_axi_s_ruser,
  input  logic                  i_ctrli_axi_s_rready,

  //////////////////////////////////////
  // DMA AXI : AXI WIDE Master Interface
  //////////////////////////////////////

  // DMA AXI : Write Address Channel
  output logic                  o_dma_axi_m_awvalid,
  output pve_ht_axi_m_id_t      o_dma_axi_m_awid,
  output chip_axi_addr_t        o_dma_axi_m_awaddr,
  output axi_len_t              o_dma_axi_m_awlen,
  output axi_size_t             o_dma_axi_m_awsize,
  output axi_burst_t            o_dma_axi_m_awburst,
  output logic                  o_dma_axi_m_awlock,
  output axi_cache_t            o_dma_axi_m_awcache,
  output axi_prot_t             o_dma_axi_m_awprot,
  output axi_qos_t              o_dma_axi_m_awqos,
  output axi_region_t           o_dma_axi_m_awregion,
  output chip_axi_ht_awuser_t   o_dma_axi_m_awuser,
  input  logic                  i_dma_axi_m_awready,

  // DMA AXI : Write Data Channel
  output logic                  o_dma_axi_m_wvalid,
  output chip_axi_ht_data_t     o_dma_axi_m_wdata,
  output chip_axi_ht_wstrb_t    o_dma_axi_m_wstrb,
  output logic                  o_dma_axi_m_wlast,
  output chip_axi_ht_wuser_t    o_dma_axi_m_wuser,
  input  logic                  i_dma_axi_m_wready,

  // DMA AXI : Write Response Channel
  input  logic                  i_dma_axi_m_bvalid,
  input  pve_ht_axi_m_id_t      i_dma_axi_m_bid,
  input  axi_resp_t             i_dma_axi_m_bresp,
  input  chip_axi_ht_buser_t    i_dma_axi_m_buser,
  output logic                  o_dma_axi_m_bready,

  // DMA AXI : Read Address Channel
  output logic                  o_dma_axi_m_arvalid,
  output pve_ht_axi_m_id_t      o_dma_axi_m_arid,
  output chip_axi_addr_t        o_dma_axi_m_araddr,
  output axi_len_t              o_dma_axi_m_arlen,
  output axi_size_t             o_dma_axi_m_arsize,
  output axi_burst_t            o_dma_axi_m_arburst,
  output logic                  o_dma_axi_m_arlock,
  output axi_cache_t            o_dma_axi_m_arcache,
  output axi_prot_t             o_dma_axi_m_arprot,
  output axi_qos_t              o_dma_axi_m_arqos,
  output axi_region_t           o_dma_axi_m_arregion,
  output chip_axi_ht_aruser_t   o_dma_axi_m_aruser,
  input  logic                  i_dma_axi_m_arready,

  // DMA AXI : Read Data / Response Channel
  input  logic                  i_dma_axi_m_rvalid,
  input  pve_ht_axi_m_id_t      i_dma_axi_m_rid,
  input  chip_axi_ht_data_t     i_dma_axi_m_rdata,
  input  axi_resp_t             i_dma_axi_m_rresp,
  input  logic                  i_dma_axi_m_rlast,
  input  chip_axi_ht_ruser_t    i_dma_axi_m_ruser,
  output logic                  o_dma_axi_m_rready,

  /////////////////////////////////////////////
  // DFT
  /////////////////////////////////////////////

  // JTAG
  input  wire   tck,
  input  wire   trst,
  input  logic  tms,
  input  logic  tdi,
  output logic  tdo_en,
  output logic  tdo,

  // SCAN
  input  logic  test_mode,
  input  wire   ssn_bus_clk,
  input  logic [25-1: 0] ssn_bus_data_in,
  output logic [25-1: 0] ssn_bus_data_out,

  // BIST
  input  wire                   bisr_clk,
  input  wire                   bisr_reset,
  input  logic                  bisr_shift_en,
  input  logic                  bisr_si,
  output logic                  bisr_so,

  /////////////////////////////////////////////////////////////////////////
  // PVT Sensor Analog signals from Probe to Socket Management
  /////////////////////////////////////////////////////////////////////////
  inout  wire                   io_ibias_ts,
  inout  wire                   io_vsense_ts
);

  assign o_noc_async_idle_req = 1'b0;
  assign o_noc_clken = 1'b0;
  assign o_noc_rst_n = 1'b0;
  assign o_hart_unavail = {PVE_N_CPU-1+1{1'b0}};
  assign o_hart_under_reset = {PVE_N_CPU-1+1{1'b0}};
  assign o_cfg_apb4_s_pready = 1'b1;
  assign o_cfg_apb4_s_prdata = '0;
  assign o_cfg_apb4_s_pslverr = 1'b0;
  assign o_ctrlo_axi_m_awvalid = 1'b0;
  assign o_ctrlo_axi_m_awid = '0;
  assign o_ctrlo_axi_m_awaddr = '0;
  assign o_ctrlo_axi_m_awlen = '0;
  assign o_ctrlo_axi_m_awsize = '0;
  assign o_ctrlo_axi_m_awburst = '0;
  assign o_ctrlo_axi_m_awlock = 1'b0;
  assign o_ctrlo_axi_m_awcache = '0;
  assign o_ctrlo_axi_m_awprot = '0;
  assign o_ctrlo_axi_m_awqos = '0;
  assign o_ctrlo_axi_m_awregion = '0;
  assign o_ctrlo_axi_m_awuser = '0;
  assign o_ctrlo_axi_m_wvalid = 1'b0;
  assign o_ctrlo_axi_m_wdata = '0;
  assign o_ctrlo_axi_m_wstrb = '0;
  assign o_ctrlo_axi_m_wlast = 1'b0;
  assign o_ctrlo_axi_m_wuser = '0;
  assign o_ctrlo_axi_m_bready = 1'b1;
  assign o_ctrlo_axi_m_arvalid = 1'b0;
  assign o_ctrlo_axi_m_arid = '0;
  assign o_ctrlo_axi_m_araddr = '0;
  assign o_ctrlo_axi_m_arlen = '0;
  assign o_ctrlo_axi_m_arsize = '0;
  assign o_ctrlo_axi_m_arburst = '0;
  assign o_ctrlo_axi_m_arlock = 1'b0;
  assign o_ctrlo_axi_m_arcache = '0;
  assign o_ctrlo_axi_m_arprot = '0;
  assign o_ctrlo_axi_m_arqos = '0;
  assign o_ctrlo_axi_m_arregion = '0;
  assign o_ctrlo_axi_m_aruser = '0;
  assign o_ctrlo_axi_m_rready = 1'b1;
  assign o_ctrli_axi_s_awready = 1'b1;
  assign o_ctrli_axi_s_wready = 1'b1;
  assign o_ctrli_axi_s_bvalid = 1'b1;
  assign o_ctrli_axi_s_bid = '0;
  assign o_ctrli_axi_s_bresp = '0;
  assign o_ctrli_axi_s_buser = '0;
  assign o_ctrli_axi_s_arready = 1'b1;
  assign o_ctrli_axi_s_rvalid = 1'b0;
  assign o_ctrli_axi_s_rid = '0;
  assign o_ctrli_axi_s_rdata = '0;
  assign o_ctrli_axi_s_rresp = '0;
  assign o_ctrli_axi_s_rlast = 1'b0;
  assign o_ctrli_axi_s_ruser = '0;
  assign o_dma_axi_m_awvalid = 1'b0;
  assign o_dma_axi_m_awid = '0;
  assign o_dma_axi_m_awaddr = '0;
  assign o_dma_axi_m_awlen = '0;
  assign o_dma_axi_m_awsize = '0;
  assign o_dma_axi_m_awburst = '0;
  assign o_dma_axi_m_awlock = 1'b0;
  assign o_dma_axi_m_awcache = '0;
  assign o_dma_axi_m_awprot = '0;
  assign o_dma_axi_m_awqos = '0;
  assign o_dma_axi_m_awregion = '0;
  assign o_dma_axi_m_awuser = '0;
  assign o_dma_axi_m_wvalid = 1'b0;
  assign o_dma_axi_m_wdata = '0;
  assign o_dma_axi_m_wstrb = '0;
  assign o_dma_axi_m_wlast = 1'b0;
  assign o_dma_axi_m_wuser = '0;
  assign o_dma_axi_m_bready = 1'b1;
  assign o_dma_axi_m_arvalid = 1'b0;
  assign o_dma_axi_m_arid = '0;
  assign o_dma_axi_m_araddr = '0;
  assign o_dma_axi_m_arlen = '0;
  assign o_dma_axi_m_arsize = '0;
  assign o_dma_axi_m_arburst = '0;
  assign o_dma_axi_m_arlock = 1'b0;
  assign o_dma_axi_m_arcache = '0;
  assign o_dma_axi_m_arprot = '0;
  assign o_dma_axi_m_arqos = '0;
  assign o_dma_axi_m_arregion = '0;
  assign o_dma_axi_m_aruser = '0;
  assign o_dma_axi_m_rready = 1'b1;
  assign tdo_en = 1'b0;
  assign tdo = 1'b0;
  assign bisr_so = 1'b0;

endmodule
