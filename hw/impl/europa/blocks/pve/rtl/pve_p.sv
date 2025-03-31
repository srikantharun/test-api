// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// Video Pre / Post Processor
///
module pve_p
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
  /////////////////////////////////////////////
  // Signals
  /////////////////////////////////////////////

  // Internal Clocks and Resets
  wire pve_clk;
  wire pve_rst_n;

  // AO CSR
  logic                             ao_csr_apb_rst_n;
  pctl_ao_csr_reg_pkg::apb_h2d_t    ao_csr_apb_req;
  pctl_ao_csr_reg_pkg::apb_d2h_t    ao_csr_apb_rsp;
  pve_csr_reg_pkg::pve_csr_reg2hw_t pve_reg2hw;
  pve_csr_reg_pkg::pve_csr_hw2reg_t pve_hw2reg;

  // SVS Monitor
  svs_monitor_pkg::svs_count_t svs_count;
  logic                        svs_valid;
  // Process1 monitor
  process1_monitor_pkg::pr1_count_t p1_count;
  logic                             p1_valid;
  // Process2 monitor
  process2_monitor_pkg::pr2_count_t p2_count;
  logic                             p2_valid;

  // PVE CPUs boot address
  logic             clk_en           [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic             clk_en_sync      [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic             clk_en_sync_q    [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic             clk_en_sync_q2   [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic             clk_en_sync_q3   [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  chip_axi_addr_t   boot_addr        [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic [1:0][47:0] memreg_csr       [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic [1:0]       memreg_csr_update[PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];

  // Pipe reg intermediate signals
  logic debug_req_inp            [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic debug_req_inp_q          [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic debug_req_inp_q2         [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic debug_req_inp_q3         [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic debug_rst_halt_req_inp   [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic debug_rst_halt_req_inp_q [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic debug_rst_halt_req_inp_q2[PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic debug_rst_halt_req_inp_q3[PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic debug_stop_time          [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic hart_unavail_oup         [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic hart_unavail_oup_q       [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic hart_unavail_oup_q2      [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic hart_unavail_oup_q3      [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic hart_under_reset_oup     [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic hart_under_reset_oup_q   [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic hart_under_reset_oup_q2  [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic hart_under_reset_oup_q3  [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic int_shutdown_req;

  // CTRL_OUT pipe intermediate signals
  // AW
  logic               spreg_ctrlo_o_axi_m_awvalid;
  pve_lt_axi_m_id_t   spreg_ctrlo_o_axi_m_awid;
  chip_axi_addr_t     spreg_ctrlo_o_axi_m_awaddr;
  axi_len_t           spreg_ctrlo_o_axi_m_awlen;
  axi_size_t          spreg_ctrlo_o_axi_m_awsize;
  axi_burst_t         spreg_ctrlo_o_axi_m_awburst;
  logic               spreg_ctrlo_o_axi_m_awlock;
  axi_cache_t         spreg_ctrlo_o_axi_m_awcache;
  axi_prot_t          spreg_ctrlo_o_axi_m_awprot;
  logic               spreg_ctrlo_i_axi_m_awready;
  // W
  logic               spreg_ctrlo_o_axi_m_wvalid;
  chip_axi_lt_data_t  spreg_ctrlo_o_axi_m_wdata;
  chip_axi_lt_wstrb_t spreg_ctrlo_o_axi_m_wstrb;
  logic               spreg_ctrlo_o_axi_m_wlast;
  logic               spreg_ctrlo_i_axi_m_wready;
  // B
  logic               spreg_ctrlo_i_axi_m_bvalid;
  pve_lt_axi_m_id_t   spreg_ctrlo_i_axi_m_bid;
  axi_resp_t          spreg_ctrlo_i_axi_m_bresp;
  logic               spreg_ctrlo_o_axi_m_bready;
  // AR
  logic               spreg_ctrlo_o_axi_m_arvalid;
  pve_lt_axi_m_id_t   spreg_ctrlo_o_axi_m_arid;
  chip_axi_addr_t     spreg_ctrlo_o_axi_m_araddr;
  axi_len_t           spreg_ctrlo_o_axi_m_arlen;
  axi_size_t          spreg_ctrlo_o_axi_m_arsize;
  axi_burst_t         spreg_ctrlo_o_axi_m_arburst;
  logic               spreg_ctrlo_o_axi_m_arlock;
  axi_cache_t         spreg_ctrlo_o_axi_m_arcache;
  axi_prot_t          spreg_ctrlo_o_axi_m_arprot;
  logic               spreg_ctrlo_i_axi_m_arready;
  // R
  logic               spreg_ctrlo_i_axi_m_rvalid;
  pve_lt_axi_m_id_t   spreg_ctrlo_i_axi_m_rid;
  chip_axi_lt_data_t  spreg_ctrlo_i_axi_m_rdata;
  axi_resp_t          spreg_ctrlo_i_axi_m_rresp;
  logic               spreg_ctrlo_i_axi_m_rlast;
  logic               spreg_ctrlo_o_axi_m_rready;

  // CTRL_IN pipe intermediate signals
  // AW
  logic               spreg_ctrli_i_axi_s_awvalid;
  pve_lt_axi_s_id_t   spreg_ctrli_i_axi_s_awid;
  chip_axi_addr_t     spreg_ctrli_i_axi_s_awaddr;
  axi_len_t           spreg_ctrli_i_axi_s_awlen;
  axi_size_t          spreg_ctrli_i_axi_s_awsize;
  axi_burst_t         spreg_ctrli_i_axi_s_awburst;
  logic               spreg_ctrli_i_axi_s_awlock;
  axi_cache_t         spreg_ctrli_i_axi_s_awcache;
  axi_prot_t          spreg_ctrli_i_axi_s_awprot;
  logic               spreg_ctrli_o_axi_s_awready;
  // W
  logic               spreg_ctrli_i_axi_s_wvalid;
  chip_axi_lt_data_t  spreg_ctrli_i_axi_s_wdata;
  chip_axi_lt_wstrb_t spreg_ctrli_i_axi_s_wstrb;
  logic               spreg_ctrli_i_axi_s_wlast;
  logic               spreg_ctrli_o_axi_s_wready;
  // B
  logic               spreg_ctrli_o_axi_s_bvalid;
  pve_lt_axi_s_id_t   spreg_ctrli_o_axi_s_bid;
  axi_resp_t          spreg_ctrli_o_axi_s_bresp;
  logic               spreg_ctrli_i_axi_s_bready;
  // AR
  logic               spreg_ctrli_i_axi_s_arvalid;
  pve_lt_axi_s_id_t   spreg_ctrli_i_axi_s_arid;
  chip_axi_addr_t     spreg_ctrli_i_axi_s_araddr;
  axi_len_t           spreg_ctrli_i_axi_s_arlen;
  axi_size_t          spreg_ctrli_i_axi_s_arsize;
  axi_burst_t         spreg_ctrli_i_axi_s_arburst;
  logic               spreg_ctrli_i_axi_s_arlock;
  axi_cache_t         spreg_ctrli_i_axi_s_arcache;
  axi_prot_t          spreg_ctrli_i_axi_s_arprot;
  logic               spreg_ctrli_o_axi_s_arready;
  // R
  logic               spreg_ctrli_o_axi_s_rvalid;
  pve_lt_axi_s_id_t   spreg_ctrli_o_axi_s_rid;
  chip_axi_lt_data_t  spreg_ctrli_o_axi_s_rdata;
  axi_resp_t          spreg_ctrli_o_axi_s_rresp;
  logic               spreg_ctrli_o_axi_s_rlast;
  logic               spreg_ctrli_i_axi_s_rready;

  // DMA_OUT pipe intermediate signals
  // AW
  logic               spreg_dma_o_axi_m_awvalid;
  pve_ht_axi_m_id_t   spreg_dma_o_axi_m_awid;
  chip_axi_addr_t     spreg_dma_o_axi_m_awaddr;
  axi_len_t           spreg_dma_o_axi_m_awlen;
  axi_size_t          spreg_dma_o_axi_m_awsize;
  axi_burst_t         spreg_dma_o_axi_m_awburst;
  logic               spreg_dma_o_axi_m_awlock;
  axi_cache_t         spreg_dma_o_axi_m_awcache;
  axi_prot_t          spreg_dma_o_axi_m_awprot;
  logic               spreg_dma_i_axi_m_awready;
  // W
  logic               spreg_dma_o_axi_m_wvalid;
  chip_axi_ht_data_t  spreg_dma_o_axi_m_wdata;
  chip_axi_ht_wstrb_t spreg_dma_o_axi_m_wstrb;
  logic               spreg_dma_o_axi_m_wlast;
  logic               spreg_dma_i_axi_m_wready;
  // B
  logic               spreg_dma_i_axi_m_bvalid;
  pve_ht_axi_m_id_t   spreg_dma_i_axi_m_bid;
  axi_resp_t          spreg_dma_i_axi_m_bresp;
  logic               spreg_dma_o_axi_m_bready;
  // AR
  logic               spreg_dma_o_axi_m_arvalid;
  pve_ht_axi_m_id_t   spreg_dma_o_axi_m_arid;
  chip_axi_addr_t     spreg_dma_o_axi_m_araddr;
  axi_len_t           spreg_dma_o_axi_m_arlen;
  axi_size_t          spreg_dma_o_axi_m_arsize;
  axi_burst_t         spreg_dma_o_axi_m_arburst;
  logic               spreg_dma_o_axi_m_arlock;
  axi_cache_t         spreg_dma_o_axi_m_arcache;
  axi_prot_t          spreg_dma_o_axi_m_arprot;
  logic               spreg_dma_i_axi_m_arready;
  // R
  logic               spreg_dma_i_axi_m_rvalid;
  pve_ht_axi_m_id_t   spreg_dma_i_axi_m_rid;
  chip_axi_ht_data_t  spreg_dma_i_axi_m_rdata;
  axi_resp_t          spreg_dma_i_axi_m_rresp;
  logic               spreg_dma_i_axi_m_rlast;
  logic               spreg_dma_o_axi_m_rready;

  // SRAM control signals
  logic ret;
  logic pde;
  logic scan_en;
  logic prn;

  pctl #(
    .N_FAST_CLKS          (1),
    .N_RESETS             (1),
    .N_MEM_PG             (1),
    .N_FENCES             (1),
    .N_THROTTLE_PINS      (2),
    .CLKRST_MATRIX        ('1),
    .PLL_CLK_IS_I_CLK     ('0),
    .NOC_RST_IDX          (0),
    .SYNC_CLK_IDX         (0),
    .AUTO_RESET_REMOVE    (1'b0),
    .paddr_t              (chip_syscfg_addr_t),
    .pdata_t              (chip_apb_syscfg_data_t),
    .pstrb_t              (chip_apb_syscfg_strb_t)
  ) u_pctl (
    // Input clocks and resets
    .i_clk                (i_ref_clk),
    .i_ao_rst_n,
    .i_global_rst_n,
    .i_test_mode          (test_mode),
    // Output clocks and resets
    .i_pll_clk            (i_clk),
    .o_partition_clk      (pve_clk),
    .o_partition_rst_n    (pve_rst_n),
    .o_ao_rst_sync_n      (ao_csr_apb_rst_n),
    // Isolation interface
    .o_noc_async_idle_req,
    .i_noc_async_idle_ack,
    .i_noc_async_idle_val,
    .o_noc_clken,
    .o_noc_rst_n,
    // IRQs
    .o_int_shutdown_req   (int_shutdown_req),
    .i_int_shutdown_ack   (1'b0),
    // SRAM configuration
    .o_ret                (ret),
    .o_pde                (pde),
    .i_prn                (prn),
    // Sync interface
    .i_global_sync_async  (1'b0),   // Not needed
    .o_global_sync        (),       // ASO-UNUSED_OUTPUT: pve doesn't use sync interface
    // Throttle inputs
    .i_throttle           ({i_thermal_throttle, i_clock_throttle}),
    /////////////////////////////////////////////
    // SYS_CFG Bus
    /////////////////////////////////////////////
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
    .o_ao_csr_apb_req     (ao_csr_apb_req),
    .i_ao_csr_apb_rsp     (ao_csr_apb_rsp)
  );

  // AO CSR
  pve_csr_reg_top u_pve_ao_csr (
    .clk_i    (i_ref_clk),
    .rst_ni   (ao_csr_apb_rst_n),
    .apb_i    (ao_csr_apb_req),
    .apb_o    (ao_csr_apb_rsp),
    .reg2hw   (pve_reg2hw),
    .hw2reg   (pve_hw2reg),
    .devmode_i(1'b1)
  );

  // PVT sensor
  pvt_probe_wrapper u_pvt_probe (
    .io_ibias_ts,
    .io_vsense_ts
  );

  // Process1 monitor
  always_comb foreach(pve_hw2reg.p1_counters[counter])
    pve_hw2reg.p1_counters[counter] = '{
      de: p1_valid,
      d:  p1_count[counter]
  };
  process1_monitor_wrapper u_p1_monitor (
    .tcki     (tck),
    .trsti    (trst),
    .i_clk,
    .i_enable (pve_reg2hw.p1_control.enable),
    .i_ref_clk,
    .i_target (pve_reg2hw.p1_control.target),
    .i_use_ro (pve_reg2hw.p1_ro_select),
    .o_valid  (p1_valid),
    .o_count  (p1_count)
  );

  // Process2 monitor
  always_comb foreach(pve_hw2reg.p2_counters[counter])
    pve_hw2reg.p2_counters[counter] = '{
      de: p2_valid,
      d:  p2_count[counter]
  };
  process2_monitor_wrapper u_p2_monitor (
    .tcki     (tck),
    .trsti    (trst),
    .i_clk,
    .i_enable (pve_reg2hw.p2_control.enable),
    .i_ref_clk,
    .i_target (pve_reg2hw.p2_control.target),
    .i_use_ro (pve_reg2hw.p2_ro_select),
    .o_valid  (p2_valid),
    .o_count  (p2_count)
  );

  // SVS Monitor
  always_comb foreach(pve_hw2reg.svs_counters[counter])
    pve_hw2reg.svs_counters[counter] = '{
      de: svs_valid,
      d:  svs_count[counter]
  };
  svs_monitor_wrapper u_svs_monitor (
    .tcki     (tck),
    .trsti    (trst),
    .i_clk,
    .i_enable (pve_reg2hw.svs_control.enable),
    .i_ref_clk,
    .i_target (pve_reg2hw.svs_control.target),
    .i_use_ro (pve_reg2hw.svs_ro_select),
    .o_valid  (svs_valid),
    .o_count  (svs_count)
  );

  /////////////////////////////////////////////
  // PVE and pipes
  /////////////////////////////////////////////

  for (genvar I = 0; I < PVE_N_CLUSTERS; I++) begin: g_io0
    for (genvar J = 0; J < PVE_CLUSTER_N_CPU; J++) begin: g_io1

      // AO CSRs
      always_comb clk_en[I][J]    = pve_reg2hw.clk_en[I*PVE_CLUSTER_N_CPU+J];
      always_comb boot_addr[I][J] = {pve_reg2hw.boot_addr_msb[I*PVE_CLUSTER_N_CPU+J],
                                     pve_reg2hw.boot_addr_lsb[I*PVE_CLUSTER_N_CPU+J]};
      always_comb memreg_csr_update[I][J][0] = pve_reg2hw.memreg0_msb[I*PVE_CLUSTER_N_CPU+J].addr.qe |
                                               pve_reg2hw.memreg0_lsb[I*PVE_CLUSTER_N_CPU+J].qe;
      always_comb memreg_csr_update[I][J][1] = pve_reg2hw.memreg1_msb[I*PVE_CLUSTER_N_CPU+J].addr.qe |
                                               pve_reg2hw.memreg1_lsb[I*PVE_CLUSTER_N_CPU+J].qe;
      always_ff @(posedge i_ref_clk or negedge ao_csr_apb_rst_n) begin
        if (!ao_csr_apb_rst_n) begin
          memreg_csr[I][J][0][47] <= 1'b0;
        end else if (memreg_csr_update[I][J][0]) begin
          memreg_csr[I][J][0][47] <= 1'b1;
        end
      end
      always_ff @(posedge i_ref_clk or negedge ao_csr_apb_rst_n) begin
        if (!ao_csr_apb_rst_n) begin
          memreg_csr[I][J][1][47] <= 1'b0;
        end else if (memreg_csr_update[I][J][1]) begin
          memreg_csr[I][J][1][47] <= 1'b1;
        end
      end
      always_ff @(posedge i_ref_clk or negedge ao_csr_apb_rst_n) begin
        if (!ao_csr_apb_rst_n) begin
          memreg_csr[I][J][0][46:0] <= '0;
          memreg_csr[I][J][1][46:0] <= '0;
        end else begin
          memreg_csr[I][J][0][46:0] <= {pve_reg2hw.memreg0_msb[I*PVE_CLUSTER_N_CPU+J].tcdm.q,
                                        pve_reg2hw.memreg0_msb[I*PVE_CLUSTER_N_CPU+J].size.q,
                                        pve_reg2hw.memreg0_msb[I*PVE_CLUSTER_N_CPU+J].addr.q,
                                        pve_reg2hw.memreg0_lsb[I*PVE_CLUSTER_N_CPU+J].q};
          memreg_csr[I][J][1][46:0] <= {pve_reg2hw.memreg1_msb[I*PVE_CLUSTER_N_CPU+J].tcdm.q,
                                        pve_reg2hw.memreg1_msb[I*PVE_CLUSTER_N_CPU+J].size.q,
                                        pve_reg2hw.memreg1_msb[I*PVE_CLUSTER_N_CPU+J].addr.q,
                                        pve_reg2hw.memreg1_lsb[I*PVE_CLUSTER_N_CPU+J].q};
        end
      end
      always_comb pve_hw2reg.debug_stop_time[I*PVE_CLUSTER_N_CPU+J] = debug_stop_time[I][J];

      // Sync clk_en to pve_clk
      axe_tcl_seq_sync #(
        .SyncStages(PVE_SYNC_STAGES),
        .ResetValue(0)
      ) u_clk_en_sync (
        .i_clk   (pve_clk),
        .i_rst_n (pve_rst_n),
        .i_d     (clk_en[I][J]),
        .o_q     (clk_en_sync[I][J])
      );

      // Debug and hart status pipes
      always_ff @(posedge pve_clk or negedge pve_rst_n) begin
        if (!pve_rst_n) begin
          debug_req_inp[I][J]                       <= 1'b0;
          debug_req_inp_q[I][J]                     <= 1'b0;
          debug_req_inp_q2[I][J]                    <= 1'b0;
          debug_req_inp_q3[I][J]                    <= 1'b0;
          debug_rst_halt_req_inp[I][J]              <= 1'b0;
          debug_rst_halt_req_inp_q[I][J]            <= 1'b0;
          debug_rst_halt_req_inp_q2[I][J]           <= 1'b0;
          debug_rst_halt_req_inp_q3[I][J]           <= 1'b0;
          hart_unavail_oup_q[I][J]                  <= 1'b0;
          hart_unavail_oup_q2[I][J]                 <= 1'b0;
          hart_unavail_oup_q3[I][J]                 <= 1'b0;
          o_hart_unavail[I*PVE_CLUSTER_N_CPU+J]     <= 1'b0;
          hart_under_reset_oup_q[I][J]              <= 1'b0;
          hart_under_reset_oup_q2[I][J]             <= 1'b0;
          hart_under_reset_oup_q3[I][J]             <= 1'b0;
          o_hart_under_reset[I*PVE_CLUSTER_N_CPU+J] <= 1'b0;
        end else begin
          debug_req_inp[I][J]                       <= i_debug_req[I*PVE_CLUSTER_N_CPU+J];
          debug_req_inp_q[I][J]                     <= debug_req_inp[I][J];
          debug_req_inp_q2[I][J]                    <= debug_req_inp_q[I][J];
          debug_req_inp_q3[I][J]                    <= debug_req_inp_q2[I][J];
          debug_rst_halt_req_inp[I][J]              <= i_debug_rst_halt_req[I*PVE_CLUSTER_N_CPU+J];
          debug_rst_halt_req_inp_q[I][J]            <= debug_rst_halt_req_inp[I][J];
          debug_rst_halt_req_inp_q2[I][J]           <= debug_rst_halt_req_inp_q[I][J];
          debug_rst_halt_req_inp_q3[I][J]           <= debug_rst_halt_req_inp_q2[I][J];
          hart_unavail_oup_q[I][J]                  <= hart_unavail_oup[I][J];
          hart_unavail_oup_q2[I][J]                 <= hart_unavail_oup_q[I][J];
          hart_unavail_oup_q3[I][J]                 <= hart_unavail_oup_q2[I][J];
          o_hart_unavail[I*PVE_CLUSTER_N_CPU+J]     <= hart_unavail_oup_q3[I][J];
          hart_under_reset_oup_q[I][J]              <= hart_under_reset_oup[I][J];
          hart_under_reset_oup_q2[I][J]             <= hart_under_reset_oup_q[I][J];
          hart_under_reset_oup_q3[I][J]             <= hart_under_reset_oup_q2[I][J];
          o_hart_under_reset[I*PVE_CLUSTER_N_CPU+J] <= hart_under_reset_oup_q3[I][J];
        end
      end
    end
  end

  // clk_en and int_shutdown pipes
  always_ff @(posedge pve_clk or negedge pve_rst_n) begin
    if (!pve_rst_n) begin
      clk_en_sync_q  <= '{default: '0};
      clk_en_sync_q2 <= '{default: '0};
      clk_en_sync_q3 <= '{default: '0};
    end else begin
      clk_en_sync_q  <= clk_en_sync;
      clk_en_sync_q2 <= clk_en_sync_q;
      clk_en_sync_q3 <= clk_en_sync_q2;
    end
  end

  // CTRL_OUT pipe
  axe_axi_multicut_flat #(
    .NumCuts       (1                   ), // Number of cuts.
    .AxiIdWidth    (PVE_LT_M_ID_W       ), // AXI ID Width
    .AxiAddrWidth  (CHIP_AXI_ADDR_W     ), // AXI Address Width
    .AxiDataWidth  (CHIP_AXI_LT_DATA_W  ), // AXI Data Width
    .AxiAwUserWidth(CHIP_AXI_LT_AWUSER_W), // AXI AW User Width
    .AxiWUserWidth (CHIP_AXI_LT_WUSER_W ), // AXI  W User Width
    .AxiBUserWidth (CHIP_AXI_LT_BUSER_W ), // AXI  B User Width
    .AxiArUserWidth(CHIP_AXI_LT_ARUSER_W), // AXI AR User Width
    .AxiRUserWidth (CHIP_AXI_LT_RUSER_W )  // AXI  R User Width
  ) u_ctrl_out_cut (
    .i_clk            (pve_clk  ),
    .i_rst_n          (pve_rst_n),
    // Subordinate side
    // AW
    .i_axi_s_aw_valid (spreg_ctrlo_o_axi_m_awvalid),
    .i_axi_s_aw_id    (spreg_ctrlo_o_axi_m_awid   ),
    .i_axi_s_aw_addr  (spreg_ctrlo_o_axi_m_awaddr ),
    .i_axi_s_aw_len   (spreg_ctrlo_o_axi_m_awlen  ),
    .i_axi_s_aw_size  (spreg_ctrlo_o_axi_m_awsize ),
    .i_axi_s_aw_burst (spreg_ctrlo_o_axi_m_awburst),
    .i_axi_s_aw_lock  (spreg_ctrlo_o_axi_m_awlock ),
    .i_axi_s_aw_cache (spreg_ctrlo_o_axi_m_awcache),
    .i_axi_s_aw_prot  (spreg_ctrlo_o_axi_m_awprot ),
    .i_axi_s_aw_qos   (axi_qos_t'('0)             ), // Not needed
    .i_axi_s_aw_region(axi_region_t'('0)          ), // Not needed
    .i_axi_s_aw_user  (chip_axi_lt_awuser_t'('0)  ), // Not needed
    .o_axi_s_aw_ready (spreg_ctrlo_i_axi_m_awready),
    // W
    .i_axi_s_w_valid  (spreg_ctrlo_o_axi_m_wvalid ),
    .i_axi_s_w_data   (spreg_ctrlo_o_axi_m_wdata  ),
    .i_axi_s_w_strb   (spreg_ctrlo_o_axi_m_wstrb  ),
    .i_axi_s_w_last   (spreg_ctrlo_o_axi_m_wlast  ),
    .i_axi_s_w_user   (chip_axi_lt_wuser_t'('0)   ), // Not needed
    .o_axi_s_w_ready  (spreg_ctrlo_i_axi_m_wready ),
    // B
    .o_axi_s_b_valid  (spreg_ctrlo_i_axi_m_bvalid ),
    .o_axi_s_b_id     (spreg_ctrlo_i_axi_m_bid    ),
    .o_axi_s_b_resp   (spreg_ctrlo_i_axi_m_bresp  ),
    .o_axi_s_b_user   (                           ), // ASO-UNUSED_OUTPUT: pve doesn't use buser
    .i_axi_s_b_ready  (spreg_ctrlo_o_axi_m_bready ),
    // AR
    .i_axi_s_ar_valid (spreg_ctrlo_o_axi_m_arvalid),
    .i_axi_s_ar_id    (spreg_ctrlo_o_axi_m_arid   ),
    .i_axi_s_ar_addr  (spreg_ctrlo_o_axi_m_araddr ),
    .i_axi_s_ar_len   (spreg_ctrlo_o_axi_m_arlen  ),
    .i_axi_s_ar_size  (spreg_ctrlo_o_axi_m_arsize ),
    .i_axi_s_ar_burst (spreg_ctrlo_o_axi_m_arburst),
    .i_axi_s_ar_lock  (spreg_ctrlo_o_axi_m_arlock ),
    .i_axi_s_ar_cache (spreg_ctrlo_o_axi_m_arcache),
    .i_axi_s_ar_prot  (spreg_ctrlo_o_axi_m_arprot ),
    .i_axi_s_ar_qos   (axi_qos_t'('0)             ), // Not needed
    .i_axi_s_ar_region(axi_region_t'('0)          ), // Not needed
    .i_axi_s_ar_user  (chip_axi_lt_aruser_t'('0)  ), // Not needed
    .o_axi_s_ar_ready (spreg_ctrlo_i_axi_m_arready),
    // R
    .o_axi_s_r_valid  (spreg_ctrlo_i_axi_m_rvalid ),
    .o_axi_s_r_id     (spreg_ctrlo_i_axi_m_rid    ),
    .o_axi_s_r_data   (spreg_ctrlo_i_axi_m_rdata  ),
    .o_axi_s_r_resp   (spreg_ctrlo_i_axi_m_rresp  ),
    .o_axi_s_r_last   (spreg_ctrlo_i_axi_m_rlast  ),
    .o_axi_s_r_user   (                           ), // ASO-UNUSED_OUTPUT: pve doesn't use ruser
    .i_axi_s_r_ready  (spreg_ctrlo_o_axi_m_rready ),
    // Manager side
    // AW
    .o_axi_m_aw_valid (o_ctrlo_axi_m_awvalid ),
    .o_axi_m_aw_id    (o_ctrlo_axi_m_awid    ),
    .o_axi_m_aw_addr  (o_ctrlo_axi_m_awaddr  ),
    .o_axi_m_aw_len   (o_ctrlo_axi_m_awlen   ),
    .o_axi_m_aw_size  (o_ctrlo_axi_m_awsize  ),
    .o_axi_m_aw_burst (o_ctrlo_axi_m_awburst ),
    .o_axi_m_aw_lock  (o_ctrlo_axi_m_awlock  ),
    .o_axi_m_aw_cache (o_ctrlo_axi_m_awcache ),
    .o_axi_m_aw_prot  (o_ctrlo_axi_m_awprot  ),
    .o_axi_m_aw_qos   (o_ctrlo_axi_m_awqos   ),
    .o_axi_m_aw_region(o_ctrlo_axi_m_awregion),
    .o_axi_m_aw_user  (o_ctrlo_axi_m_awuser  ),
    .i_axi_m_aw_ready (i_ctrlo_axi_m_awready ),
    // W
    .o_axi_m_w_valid  (o_ctrlo_axi_m_wvalid  ),
    .o_axi_m_w_data   (o_ctrlo_axi_m_wdata   ),
    .o_axi_m_w_strb   (o_ctrlo_axi_m_wstrb   ),
    .o_axi_m_w_last   (o_ctrlo_axi_m_wlast   ),
    .o_axi_m_w_user   (o_ctrlo_axi_m_wuser   ),
    .i_axi_m_w_ready  (i_ctrlo_axi_m_wready  ),
    // B
    .i_axi_m_b_valid  (i_ctrlo_axi_m_bvalid  ),
    .i_axi_m_b_id     (i_ctrlo_axi_m_bid     ),
    .i_axi_m_b_resp   (i_ctrlo_axi_m_bresp   ),
    .i_axi_m_b_user   (i_ctrlo_axi_m_buser   ),
    .o_axi_m_b_ready  (o_ctrlo_axi_m_bready  ),
    // AR
    .o_axi_m_ar_valid (o_ctrlo_axi_m_arvalid ),
    .o_axi_m_ar_id    (o_ctrlo_axi_m_arid    ),
    .o_axi_m_ar_addr  (o_ctrlo_axi_m_araddr  ),
    .o_axi_m_ar_len   (o_ctrlo_axi_m_arlen   ),
    .o_axi_m_ar_size  (o_ctrlo_axi_m_arsize  ),
    .o_axi_m_ar_burst (o_ctrlo_axi_m_arburst ),
    .o_axi_m_ar_lock  (o_ctrlo_axi_m_arlock  ),
    .o_axi_m_ar_cache (o_ctrlo_axi_m_arcache ),
    .o_axi_m_ar_prot  (o_ctrlo_axi_m_arprot  ),
    .o_axi_m_ar_qos   (o_ctrlo_axi_m_arqos   ),
    .o_axi_m_ar_region(o_ctrlo_axi_m_arregion),
    .o_axi_m_ar_user  (o_ctrlo_axi_m_aruser  ),
    .i_axi_m_ar_ready (i_ctrlo_axi_m_arready ),
    // R
    .i_axi_m_r_valid  (i_ctrlo_axi_m_rvalid  ),
    .i_axi_m_r_id     (i_ctrlo_axi_m_rid     ),
    .i_axi_m_r_data   (i_ctrlo_axi_m_rdata   ),
    .i_axi_m_r_resp   (i_ctrlo_axi_m_rresp   ),
    .i_axi_m_r_last   (i_ctrlo_axi_m_rlast   ),
    .i_axi_m_r_user   (i_ctrlo_axi_m_ruser   ),
    .o_axi_m_r_ready  (o_ctrlo_axi_m_rready  )
  );

  // CTRL_IN pipe
  axe_axi_multicut_flat #(
    .NumCuts       (1                   ), // Number of cuts.
    .AxiIdWidth    (PVE_LT_S_ID_W       ), // AXI ID Width
    .AxiAddrWidth  (CHIP_AXI_ADDR_W     ), // AXI Address Width
    .AxiDataWidth  (CHIP_AXI_LT_DATA_W  ), // AXI Data Width
    .AxiAwUserWidth(CHIP_AXI_LT_AWUSER_W), // AXI AW User Width
    .AxiWUserWidth (CHIP_AXI_LT_WUSER_W ), // AXI  W User Width
    .AxiBUserWidth (CHIP_AXI_LT_BUSER_W ), // AXI  B User Width
    .AxiArUserWidth(CHIP_AXI_LT_ARUSER_W), // AXI AR User Width
    .AxiRUserWidth (CHIP_AXI_LT_RUSER_W )  // AXI  R User Width
  ) u_ctrl_in_cut (
    .i_clk             (pve_clk  ),
    .i_rst_n           (pve_rst_n),
    // Subordinate side
    // AW
    .i_axi_s_aw_valid  (i_ctrli_axi_s_awvalid ),
    .i_axi_s_aw_id     (i_ctrli_axi_s_awid    ),
    .i_axi_s_aw_addr   (i_ctrli_axi_s_awaddr  ),
    .i_axi_s_aw_len    (i_ctrli_axi_s_awlen   ),
    .i_axi_s_aw_size   (i_ctrli_axi_s_awsize  ),
    .i_axi_s_aw_burst  (i_ctrli_axi_s_awburst ),
    .i_axi_s_aw_lock   (i_ctrli_axi_s_awlock  ),
    .i_axi_s_aw_cache  (i_ctrli_axi_s_awcache ),
    .i_axi_s_aw_prot   (i_ctrli_axi_s_awprot  ),
    .i_axi_s_aw_qos    (i_ctrli_axi_s_awqos   ),
    .i_axi_s_aw_region (i_ctrli_axi_s_awregion),
    .i_axi_s_aw_user   (i_ctrli_axi_s_awuser  ),
    .o_axi_s_aw_ready  (o_ctrli_axi_s_awready ),
    // W
    .i_axi_s_w_valid   (i_ctrli_axi_s_wvalid  ),
    .i_axi_s_w_data    (i_ctrli_axi_s_wdata   ),
    .i_axi_s_w_strb    (i_ctrli_axi_s_wstrb   ),
    .i_axi_s_w_last    (i_ctrli_axi_s_wlast   ),
    .i_axi_s_w_user    (i_ctrli_axi_s_wuser   ),
    .o_axi_s_w_ready   (o_ctrli_axi_s_wready  ),
    // B
    .o_axi_s_b_valid   (o_ctrli_axi_s_bvalid  ),
    .o_axi_s_b_id      (o_ctrli_axi_s_bid     ),
    .o_axi_s_b_resp    (o_ctrli_axi_s_bresp   ),
    .o_axi_s_b_user    (o_ctrli_axi_s_buser   ),
    .i_axi_s_b_ready   (i_ctrli_axi_s_bready  ),
    // AR
    .i_axi_s_ar_valid  (i_ctrli_axi_s_arvalid ),
    .i_axi_s_ar_id     (i_ctrli_axi_s_arid    ),
    .i_axi_s_ar_addr   (i_ctrli_axi_s_araddr  ),
    .i_axi_s_ar_len    (i_ctrli_axi_s_arlen   ),
    .i_axi_s_ar_size   (i_ctrli_axi_s_arsize  ),
    .i_axi_s_ar_burst  (i_ctrli_axi_s_arburst ),
    .i_axi_s_ar_lock   (i_ctrli_axi_s_arlock  ),
    .i_axi_s_ar_cache  (i_ctrli_axi_s_arcache ),
    .i_axi_s_ar_prot   (i_ctrli_axi_s_arprot  ),
    .i_axi_s_ar_qos    (i_ctrli_axi_s_arqos   ),
    .i_axi_s_ar_region (i_ctrli_axi_s_arregion),
    .i_axi_s_ar_user   (i_ctrli_axi_s_aruser  ),
    .o_axi_s_ar_ready  (o_ctrli_axi_s_arready ),
    // R
    .o_axi_s_r_valid   (o_ctrli_axi_s_rvalid  ),
    .o_axi_s_r_id      (o_ctrli_axi_s_rid     ),
    .o_axi_s_r_data    (o_ctrli_axi_s_rdata   ),
    .o_axi_s_r_resp    (o_ctrli_axi_s_rresp   ),
    .o_axi_s_r_last    (o_ctrli_axi_s_rlast   ),
    .o_axi_s_r_user    (o_ctrli_axi_s_ruser   ),
    .i_axi_s_r_ready   (i_ctrli_axi_s_rready  ),
    // Manager side
    // AW
    .o_axi_m_aw_valid   (spreg_ctrli_i_axi_s_awvalid),
    .o_axi_m_aw_id      (spreg_ctrli_i_axi_s_awid   ),
    .o_axi_m_aw_addr    (spreg_ctrli_i_axi_s_awaddr ),
    .o_axi_m_aw_len     (spreg_ctrli_i_axi_s_awlen  ),
    .o_axi_m_aw_size    (spreg_ctrli_i_axi_s_awsize ),
    .o_axi_m_aw_burst   (spreg_ctrli_i_axi_s_awburst),
    .o_axi_m_aw_lock    (spreg_ctrli_i_axi_s_awlock ),
    .o_axi_m_aw_cache   (spreg_ctrli_i_axi_s_awcache),
    .o_axi_m_aw_prot    (spreg_ctrli_i_axi_s_awprot ),
    .o_axi_m_aw_qos     (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use awqos
    .o_axi_m_aw_region  (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use awregion
    .o_axi_m_aw_user    (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use awuser
    .i_axi_m_aw_ready   (spreg_ctrli_o_axi_s_awready),
    // W
    .o_axi_m_w_valid    (spreg_ctrli_i_axi_s_wvalid ),
    .o_axi_m_w_data     (spreg_ctrli_i_axi_s_wdata  ),
    .o_axi_m_w_strb     (spreg_ctrli_i_axi_s_wstrb  ),
    .o_axi_m_w_last     (spreg_ctrli_i_axi_s_wlast  ),
    .o_axi_m_w_user     (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use wuser
    .i_axi_m_w_ready    (spreg_ctrli_o_axi_s_wready ),
    // B
    .i_axi_m_b_valid    (spreg_ctrli_o_axi_s_bvalid ),
    .i_axi_m_b_id       (spreg_ctrli_o_axi_s_bid    ),
    .i_axi_m_b_resp     (spreg_ctrli_o_axi_s_bresp  ),
    .i_axi_m_b_user     (chip_axi_lt_buser_t'('0)   ), // Not needed
    .o_axi_m_b_ready    (spreg_ctrli_i_axi_s_bready ),
    // AR
    .o_axi_m_ar_valid   (spreg_ctrli_i_axi_s_arvalid),
    .o_axi_m_ar_id      (spreg_ctrli_i_axi_s_arid   ),
    .o_axi_m_ar_addr    (spreg_ctrli_i_axi_s_araddr ),
    .o_axi_m_ar_len     (spreg_ctrli_i_axi_s_arlen  ),
    .o_axi_m_ar_size    (spreg_ctrli_i_axi_s_arsize ),
    .o_axi_m_ar_burst   (spreg_ctrli_i_axi_s_arburst),
    .o_axi_m_ar_lock    (spreg_ctrli_i_axi_s_arlock ),
    .o_axi_m_ar_cache   (spreg_ctrli_i_axi_s_arcache),
    .o_axi_m_ar_prot    (spreg_ctrli_i_axi_s_arprot ),
    .o_axi_m_ar_qos     (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use arqos
    .o_axi_m_ar_region  (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use arregion
    .o_axi_m_ar_user    (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use aruser
    .i_axi_m_ar_ready   (spreg_ctrli_o_axi_s_arready),
    // R
    .i_axi_m_r_valid    (spreg_ctrli_o_axi_s_rvalid ),
    .i_axi_m_r_id       (spreg_ctrli_o_axi_s_rid    ),
    .i_axi_m_r_data     (spreg_ctrli_o_axi_s_rdata  ),
    .i_axi_m_r_resp     (spreg_ctrli_o_axi_s_rresp  ),
    .i_axi_m_r_last     (spreg_ctrli_o_axi_s_rlast  ),
    .i_axi_m_r_user     (chip_axi_lt_ruser_t'('0)   ), // Not needed
    .o_axi_m_r_ready    (spreg_ctrli_i_axi_s_rready )
  );

  // DMA_OUT pipe
  axe_axi_multicut_flat #(
    .NumCuts       (1                   ), // Number of cuts.
    .AxiIdWidth    (PVE_HT_M_ID_W       ), // AXI ID Width
    .AxiAddrWidth  (CHIP_AXI_ADDR_W     ), // AXI Address Width
    .AxiDataWidth  (CHIP_AXI_HT_DATA_W  ), // AXI Data Width
    .AxiAwUserWidth(CHIP_AXI_HT_AWUSER_W), // AXI AW User Width
    .AxiWUserWidth (CHIP_AXI_HT_WUSER_W ), // AXI  W User Width
    .AxiBUserWidth (CHIP_AXI_HT_BUSER_W ), // AXI  B User Width
    .AxiArUserWidth(CHIP_AXI_HT_ARUSER_W), // AXI AR User Width
    .AxiRUserWidth (CHIP_AXI_HT_RUSER_W )  // AXI  R User Width
  ) u_dma_cut (
    .i_clk            (pve_clk  ),
    .i_rst_n          (pve_rst_n),
    // Subordinate side
    // AW
    .i_axi_s_aw_valid (spreg_dma_o_axi_m_awvalid),
    .i_axi_s_aw_id    (spreg_dma_o_axi_m_awid   ),
    .i_axi_s_aw_addr  (spreg_dma_o_axi_m_awaddr ),
    .i_axi_s_aw_len   (spreg_dma_o_axi_m_awlen  ),
    .i_axi_s_aw_size  (spreg_dma_o_axi_m_awsize ),
    .i_axi_s_aw_burst (spreg_dma_o_axi_m_awburst),
    .i_axi_s_aw_lock  (spreg_dma_o_axi_m_awlock ),
    .i_axi_s_aw_cache (spreg_dma_o_axi_m_awcache),
    .i_axi_s_aw_prot  (spreg_dma_o_axi_m_awprot ),
    .i_axi_s_aw_qos   (axi_qos_t'('0)           ), // Not needed
    .i_axi_s_aw_region(axi_region_t'('0)        ), // Not needed
    .i_axi_s_aw_user  (chip_axi_ht_awuser_t'('0)), // Not needed
    .o_axi_s_aw_ready (spreg_dma_i_axi_m_awready),
    // W
    .i_axi_s_w_valid  (spreg_dma_o_axi_m_wvalid ),
    .i_axi_s_w_data   (spreg_dma_o_axi_m_wdata  ),
    .i_axi_s_w_strb   (spreg_dma_o_axi_m_wstrb  ),
    .i_axi_s_w_last   (spreg_dma_o_axi_m_wlast  ),
    .i_axi_s_w_user   (chip_axi_ht_wuser_t'('0) ), // Not needed
    .o_axi_s_w_ready  (spreg_dma_i_axi_m_wready ),
    // B
    .o_axi_s_b_valid  (spreg_dma_i_axi_m_bvalid ),
    .o_axi_s_b_id     (spreg_dma_i_axi_m_bid    ),
    .o_axi_s_b_resp   (spreg_dma_i_axi_m_bresp  ),
    .o_axi_s_b_user   (                         ), // ASO-UNUSED_OUTPUT: pve doesn't use buser
    .i_axi_s_b_ready  (spreg_dma_o_axi_m_bready ),
    // AR
    .i_axi_s_ar_valid (spreg_dma_o_axi_m_arvalid),
    .i_axi_s_ar_id    (spreg_dma_o_axi_m_arid   ),
    .i_axi_s_ar_addr  (spreg_dma_o_axi_m_araddr ),
    .i_axi_s_ar_len   (spreg_dma_o_axi_m_arlen  ),
    .i_axi_s_ar_size  (spreg_dma_o_axi_m_arsize ),
    .i_axi_s_ar_burst (spreg_dma_o_axi_m_arburst),
    .i_axi_s_ar_lock  (spreg_dma_o_axi_m_arlock ),
    .i_axi_s_ar_cache (spreg_dma_o_axi_m_arcache),
    .i_axi_s_ar_prot  (spreg_dma_o_axi_m_arprot ),
    .i_axi_s_ar_qos   (axi_qos_t'('0)           ), // Not needed
    .i_axi_s_ar_region(axi_region_t'('0)        ), // Not needed
    .i_axi_s_ar_user  (chip_axi_ht_aruser_t'('0)), // Not needed
    .o_axi_s_ar_ready (spreg_dma_i_axi_m_arready),
    // R
    .o_axi_s_r_valid  (spreg_dma_i_axi_m_rvalid ),
    .o_axi_s_r_id     (spreg_dma_i_axi_m_rid    ),
    .o_axi_s_r_data   (spreg_dma_i_axi_m_rdata  ),
    .o_axi_s_r_resp   (spreg_dma_i_axi_m_rresp  ),
    .o_axi_s_r_last   (spreg_dma_i_axi_m_rlast  ),
    .o_axi_s_r_user   (                         ), // ASO-UNUSED_OUTPUT: pve doesn't use ruser
    .i_axi_s_r_ready  (spreg_dma_o_axi_m_rready ),
    // Manager side
    // AW
    .o_axi_m_aw_valid (o_dma_axi_m_awvalid ),
    .o_axi_m_aw_id    (o_dma_axi_m_awid    ),
    .o_axi_m_aw_addr  (o_dma_axi_m_awaddr  ),
    .o_axi_m_aw_len   (o_dma_axi_m_awlen   ),
    .o_axi_m_aw_size  (o_dma_axi_m_awsize  ),
    .o_axi_m_aw_burst (o_dma_axi_m_awburst ),
    .o_axi_m_aw_lock  (o_dma_axi_m_awlock  ),
    .o_axi_m_aw_cache (o_dma_axi_m_awcache ),
    .o_axi_m_aw_prot  (o_dma_axi_m_awprot  ),
    .o_axi_m_aw_qos   (o_dma_axi_m_awqos   ),
    .o_axi_m_aw_region(o_dma_axi_m_awregion),
    .o_axi_m_aw_user  (o_dma_axi_m_awuser  ),
    .i_axi_m_aw_ready (i_dma_axi_m_awready ),
    // W
    .o_axi_m_w_valid  (o_dma_axi_m_wvalid  ),
    .o_axi_m_w_data   (o_dma_axi_m_wdata   ),
    .o_axi_m_w_strb   (o_dma_axi_m_wstrb   ),
    .o_axi_m_w_last   (o_dma_axi_m_wlast   ),
    .o_axi_m_w_user   (o_dma_axi_m_wuser   ),
    .i_axi_m_w_ready  (i_dma_axi_m_wready  ),
    // B
    .i_axi_m_b_valid  (i_dma_axi_m_bvalid  ),
    .i_axi_m_b_id     (i_dma_axi_m_bid     ),
    .i_axi_m_b_resp   (i_dma_axi_m_bresp   ),
    .i_axi_m_b_user   (i_dma_axi_m_buser   ),
    .o_axi_m_b_ready  (o_dma_axi_m_bready  ),
    // AR
    .o_axi_m_ar_valid (o_dma_axi_m_arvalid ),
    .o_axi_m_ar_id    (o_dma_axi_m_arid    ),
    .o_axi_m_ar_addr  (o_dma_axi_m_araddr  ),
    .o_axi_m_ar_len   (o_dma_axi_m_arlen   ),
    .o_axi_m_ar_size  (o_dma_axi_m_arsize  ),
    .o_axi_m_ar_burst (o_dma_axi_m_arburst ),
    .o_axi_m_ar_lock  (o_dma_axi_m_arlock  ),
    .o_axi_m_ar_cache (o_dma_axi_m_arcache ),
    .o_axi_m_ar_prot  (o_dma_axi_m_arprot  ),
    .o_axi_m_ar_qos   (o_dma_axi_m_arqos   ),
    .o_axi_m_ar_region(o_dma_axi_m_arregion),
    .o_axi_m_ar_user  (o_dma_axi_m_aruser  ),
    .i_axi_m_ar_ready (i_dma_axi_m_arready ),
    // R
    .i_axi_m_r_valid  (i_dma_axi_m_rvalid  ),
    .i_axi_m_r_id     (i_dma_axi_m_rid     ),
    .i_axi_m_r_data   (i_dma_axi_m_rdata   ),
    .i_axi_m_r_resp   (i_dma_axi_m_rresp   ),
    .i_axi_m_r_last   (i_dma_axi_m_rlast   ),
    .i_axi_m_r_user   (i_dma_axi_m_ruser   ),
    .o_axi_m_r_ready  (o_dma_axi_m_rready  )
  );

  pve u_pve (
    // Clock, positive edge triggered
    .i_clk                (pve_clk),
    // Asynchronous reset, active low
    .i_rst_n              (pve_rst_n),

    // Config
    .i_clk_en             (clk_en_sync_q3),
    .i_hart_base,
    .i_boot_addr          (boot_addr     ),
    .i_memreg_csr         (memreg_csr    ),

    // Interrupt input
    .i_int_shutdown_req   (int_shutdown_req),

    // Debug
    .i_debug_req          (debug_req_inp_q3         ),
    .i_debug_rst_halt_req (debug_rst_halt_req_inp_q3),
    .o_debug_stop_time    (debug_stop_time          ),

    // Hart status
    .o_hart_is_wfi        (                    ),  // ASO-UNUSED_OUTPUT: pve doesn't use o_hart_is_wfi from CVA6V cores
    .o_hart_unavail       (hart_unavail_oup    ),
    .o_hart_under_reset   (hart_under_reset_oup),

    /////////////////////////////////////////////
    // CTRL OUT AXI : AXI Narrow Master Interface
    /////////////////////////////////////////////

    // CTRL OUT AXI : Write Address Channel
    .o_ctrlo_axi_m_awvalid(spreg_ctrlo_o_axi_m_awvalid),
    .o_ctrlo_axi_m_awid   (spreg_ctrlo_o_axi_m_awid   ),
    .o_ctrlo_axi_m_awaddr (spreg_ctrlo_o_axi_m_awaddr ),
    .o_ctrlo_axi_m_awlen  (spreg_ctrlo_o_axi_m_awlen  ),
    .o_ctrlo_axi_m_awsize (spreg_ctrlo_o_axi_m_awsize ),
    .o_ctrlo_axi_m_awburst(spreg_ctrlo_o_axi_m_awburst),
    .o_ctrlo_axi_m_awlock (spreg_ctrlo_o_axi_m_awlock ),
    .o_ctrlo_axi_m_awcache(spreg_ctrlo_o_axi_m_awcache),
    .o_ctrlo_axi_m_awprot (spreg_ctrlo_o_axi_m_awprot ),
    .i_ctrlo_axi_m_awready(spreg_ctrlo_i_axi_m_awready),

    // CTRL OUT AXI : Write Data Channel
    .o_ctrlo_axi_m_wvalid (spreg_ctrlo_o_axi_m_wvalid ),
    .o_ctrlo_axi_m_wdata  (spreg_ctrlo_o_axi_m_wdata  ),
    .o_ctrlo_axi_m_wstrb  (spreg_ctrlo_o_axi_m_wstrb  ),
    .o_ctrlo_axi_m_wlast  (spreg_ctrlo_o_axi_m_wlast  ),
    .i_ctrlo_axi_m_wready (spreg_ctrlo_i_axi_m_wready ),

    // CTRL OUT AXI : Write Response Channel
    .i_ctrlo_axi_m_bvalid (spreg_ctrlo_i_axi_m_bvalid ),
    .i_ctrlo_axi_m_bid    (spreg_ctrlo_i_axi_m_bid    ),
    .i_ctrlo_axi_m_bresp  (spreg_ctrlo_i_axi_m_bresp  ),
    .o_ctrlo_axi_m_bready (spreg_ctrlo_o_axi_m_bready ),

    // CTRL OUT AXI : Read Address Channel
    .o_ctrlo_axi_m_arvalid(spreg_ctrlo_o_axi_m_arvalid),
    .o_ctrlo_axi_m_arid   (spreg_ctrlo_o_axi_m_arid   ),
    .o_ctrlo_axi_m_araddr (spreg_ctrlo_o_axi_m_araddr ),
    .o_ctrlo_axi_m_arlen  (spreg_ctrlo_o_axi_m_arlen  ),
    .o_ctrlo_axi_m_arsize (spreg_ctrlo_o_axi_m_arsize ),
    .o_ctrlo_axi_m_arburst(spreg_ctrlo_o_axi_m_arburst),
    .o_ctrlo_axi_m_arlock (spreg_ctrlo_o_axi_m_arlock ),
    .o_ctrlo_axi_m_arcache(spreg_ctrlo_o_axi_m_arcache),
    .o_ctrlo_axi_m_arprot (spreg_ctrlo_o_axi_m_arprot ),
    .i_ctrlo_axi_m_arready(spreg_ctrlo_i_axi_m_arready),

    // CTRL OUT AXI : Read Data / Response Channel
    .i_ctrlo_axi_m_rvalid (spreg_ctrlo_i_axi_m_rvalid ),
    .i_ctrlo_axi_m_rid    (spreg_ctrlo_i_axi_m_rid    ),
    .i_ctrlo_axi_m_rdata  (spreg_ctrlo_i_axi_m_rdata  ),
    .i_ctrlo_axi_m_rresp  (spreg_ctrlo_i_axi_m_rresp  ),
    .i_ctrlo_axi_m_rlast  (spreg_ctrlo_i_axi_m_rlast  ),
    .o_ctrlo_axi_m_rready (spreg_ctrlo_o_axi_m_rready ),

    /////////////////////////////////////////////
    // CTRL IN AXI : AXI Narrow Slave Interface
    /////////////////////////////////////////////

    // CTRL IN AXI : Write Address Channel
    .i_ctrli_axi_s_awvalid(spreg_ctrli_i_axi_s_awvalid),
    .i_ctrli_axi_s_awid   (spreg_ctrli_i_axi_s_awid   ),
    .i_ctrli_axi_s_awaddr (spreg_ctrli_i_axi_s_awaddr ),
    .i_ctrli_axi_s_awlen  (spreg_ctrli_i_axi_s_awlen  ),
    .i_ctrli_axi_s_awsize (spreg_ctrli_i_axi_s_awsize ),
    .i_ctrli_axi_s_awburst(spreg_ctrli_i_axi_s_awburst),
    .i_ctrli_axi_s_awlock (spreg_ctrli_i_axi_s_awlock ),
    .i_ctrli_axi_s_awcache(spreg_ctrli_i_axi_s_awcache),
    .i_ctrli_axi_s_awprot (spreg_ctrli_i_axi_s_awprot ),
    .o_ctrli_axi_s_awready(spreg_ctrli_o_axi_s_awready),

    // CTRL IN AXI : Write Data Channel
    .i_ctrli_axi_s_wdata  (spreg_ctrli_i_axi_s_wdata  ),
    .i_ctrli_axi_s_wstrb  (spreg_ctrli_i_axi_s_wstrb  ),
    .i_ctrli_axi_s_wvalid (spreg_ctrli_i_axi_s_wvalid ),
    .i_ctrli_axi_s_wlast  (spreg_ctrli_i_axi_s_wlast  ),
    .o_ctrli_axi_s_wready (spreg_ctrli_o_axi_s_wready ),

    // CTRL IN AXI : Write Response Channel
    .o_ctrli_axi_s_bvalid (spreg_ctrli_o_axi_s_bvalid ),
    .o_ctrli_axi_s_bid    (spreg_ctrli_o_axi_s_bid    ),
    .o_ctrli_axi_s_bresp  (spreg_ctrli_o_axi_s_bresp  ),
    .i_ctrli_axi_s_bready (spreg_ctrli_i_axi_s_bready ),

    // CTRL IN AXI : Read Address Channel
    .i_ctrli_axi_s_arvalid(spreg_ctrli_i_axi_s_arvalid),
    .i_ctrli_axi_s_arid   (spreg_ctrli_i_axi_s_arid   ),
    .i_ctrli_axi_s_araddr (spreg_ctrli_i_axi_s_araddr ),
    .i_ctrli_axi_s_arlen  (spreg_ctrli_i_axi_s_arlen  ),
    .i_ctrli_axi_s_arsize (spreg_ctrli_i_axi_s_arsize ),
    .i_ctrli_axi_s_arburst(spreg_ctrli_i_axi_s_arburst),
    .i_ctrli_axi_s_arlock (spreg_ctrli_i_axi_s_arlock ),
    .i_ctrli_axi_s_arcache(spreg_ctrli_i_axi_s_arcache),
    .i_ctrli_axi_s_arprot (spreg_ctrli_i_axi_s_arprot ),
    .o_ctrli_axi_s_arready(spreg_ctrli_o_axi_s_arready),

    // DMA AXI : Read Data / Response Channel
    .o_ctrli_axi_s_rvalid (spreg_ctrli_o_axi_s_rvalid ),
    .o_ctrli_axi_s_rid    (spreg_ctrli_o_axi_s_rid    ),
    .o_ctrli_axi_s_rdata  (spreg_ctrli_o_axi_s_rdata  ),
    .o_ctrli_axi_s_rresp  (spreg_ctrli_o_axi_s_rresp  ),
    .o_ctrli_axi_s_rlast  (spreg_ctrli_o_axi_s_rlast  ),
    .i_ctrli_axi_s_rready (spreg_ctrli_i_axi_s_rready ),

    /////////////////////////////////////////////
    // DMA AXI : AXI WIDE Master Interface
    /////////////////////////////////////////////

    // DMA AXI : Write Address Channel
    .o_dma_axi_m_awvalid  (spreg_dma_o_axi_m_awvalid),
    .o_dma_axi_m_awid     (spreg_dma_o_axi_m_awid   ),
    .o_dma_axi_m_awaddr   (spreg_dma_o_axi_m_awaddr ),
    .o_dma_axi_m_awlen    (spreg_dma_o_axi_m_awlen  ),
    .o_dma_axi_m_awsize   (spreg_dma_o_axi_m_awsize ),
    .o_dma_axi_m_awburst  (spreg_dma_o_axi_m_awburst),
    .o_dma_axi_m_awlock   (spreg_dma_o_axi_m_awlock ),
    .o_dma_axi_m_awcache  (spreg_dma_o_axi_m_awcache),
    .o_dma_axi_m_awprot   (spreg_dma_o_axi_m_awprot ),
    .i_dma_axi_m_awready  (spreg_dma_i_axi_m_awready),

    // DMA AXI : Write Data Channel
    .o_dma_axi_m_wvalid   (spreg_dma_o_axi_m_wvalid ),
    .o_dma_axi_m_wdata    (spreg_dma_o_axi_m_wdata  ),
    .o_dma_axi_m_wstrb    (spreg_dma_o_axi_m_wstrb  ),
    .o_dma_axi_m_wlast    (spreg_dma_o_axi_m_wlast  ),
    .i_dma_axi_m_wready   (spreg_dma_i_axi_m_wready ),

    // DMA AXI : Write Response Channel
    .i_dma_axi_m_bvalid   (spreg_dma_i_axi_m_bvalid ),
    .i_dma_axi_m_bid      (spreg_dma_i_axi_m_bid    ),
    .i_dma_axi_m_bresp    (spreg_dma_i_axi_m_bresp  ),
    .o_dma_axi_m_bready   (spreg_dma_o_axi_m_bready ),

    // DMA AXI : Read Address Channel
    .o_dma_axi_m_arvalid  (spreg_dma_o_axi_m_arvalid),
    .o_dma_axi_m_arid     (spreg_dma_o_axi_m_arid   ),
    .o_dma_axi_m_araddr   (spreg_dma_o_axi_m_araddr ),
    .o_dma_axi_m_arlen    (spreg_dma_o_axi_m_arlen  ),
    .o_dma_axi_m_arsize   (spreg_dma_o_axi_m_arsize ),
    .o_dma_axi_m_arburst  (spreg_dma_o_axi_m_arburst),
    .o_dma_axi_m_arlock   (spreg_dma_o_axi_m_arlock ),
    .o_dma_axi_m_arcache  (spreg_dma_o_axi_m_arcache),
    .o_dma_axi_m_arprot   (spreg_dma_o_axi_m_arprot ),
    .i_dma_axi_m_arready  (spreg_dma_i_axi_m_arready),

    // DMA AXI : Read Data / Response Channel
    .i_dma_axi_m_rvalid   (spreg_dma_i_axi_m_rvalid ),
    .i_dma_axi_m_rid      (spreg_dma_i_axi_m_rid    ),
    .i_dma_axi_m_rdata    (spreg_dma_i_axi_m_rdata  ),
    .i_dma_axi_m_rresp    (spreg_dma_i_axi_m_rresp  ),
    .i_dma_axi_m_rlast    (spreg_dma_i_axi_m_rlast  ),
    .o_dma_axi_m_rready   (spreg_dma_o_axi_m_rready ),

    // SRAM configuration
    .i_mem_impl           (axe_tcl_sram_pkg::impl_inp_t'{
                           default: '0,
                           mcs    : axe_tcl_pkg::MCS,
                           mcsw   : axe_tcl_pkg::MCSW,
                           ret    : ret,
                           pde    : pde,
                           se     : scan_en,
                           adme   : axe_tcl_pkg::ADME
                           }),
    .o_mem_impl           (prn)
  );

endmodule
