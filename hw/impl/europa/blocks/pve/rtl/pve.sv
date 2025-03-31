// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// Video Pre / Post Processor
///
module pve
  import axi_pkg::*;
  import chip_pkg::*;
  import axe_tcl_sram_pkg::*;
  import pve_pkg::*;
  import pve_cva6v_pkg::*;
  import pve_l1_pkg::*;
(
  // Clock, positive edge triggered
  input  wire i_clk,
  // Asynchronous reset, active low
  input  wire i_rst_n,

  // Config
  input  logic             i_clk_en    [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU],
  input  pve_hart_base_t   i_hart_base,
  input  chip_axi_addr_t   i_boot_addr [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU],
  input  logic [1:0][47:0] i_memreg_csr[PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU],

  // Interrupt inputs
  input  logic i_int_shutdown_req,

  // Debug
  input  logic i_debug_req         [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU],
  input  logic i_debug_rst_halt_req[PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU],
  output logic o_debug_stop_time   [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU],

  // Hart statu
  output logic o_hart_is_wfi       [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU],
  output logic o_hart_unavail      [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU],
  output logic o_hart_under_reset  [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU],

  /////////////////////////////////////////////
  // CTRL OUT AXI : AXI Narrow Master Interface
  /////////////////////////////////////////////

  // CTRL OUT AXI : Write Address Channel
  output logic                o_ctrlo_axi_m_awvalid,
  output pve_lt_axi_m_id_t    o_ctrlo_axi_m_awid,
  output chip_axi_addr_t      o_ctrlo_axi_m_awaddr,
  output axi_len_t            o_ctrlo_axi_m_awlen,
  output axi_size_t           o_ctrlo_axi_m_awsize,
  output axi_burst_t          o_ctrlo_axi_m_awburst,
  output logic                o_ctrlo_axi_m_awlock,
  output axi_cache_t          o_ctrlo_axi_m_awcache,
  output axi_prot_t           o_ctrlo_axi_m_awprot,
  input  logic                i_ctrlo_axi_m_awready,

  // CTRL OUT AXI : Write Data Channel
  output logic                o_ctrlo_axi_m_wvalid,
  output chip_axi_lt_data_t   o_ctrlo_axi_m_wdata,
  output chip_axi_lt_wstrb_t  o_ctrlo_axi_m_wstrb,
  output logic                o_ctrlo_axi_m_wlast,
  input  logic                i_ctrlo_axi_m_wready,

  // CTRL OUT AXI : Write Response Channel
  input  logic                i_ctrlo_axi_m_bvalid,
  input  pve_lt_axi_m_id_t    i_ctrlo_axi_m_bid,
  input  axi_resp_t           i_ctrlo_axi_m_bresp,
  output logic                o_ctrlo_axi_m_bready,

  // CTRL OUT AXI : Read Address Channel
  output logic                o_ctrlo_axi_m_arvalid,
  output pve_lt_axi_m_id_t    o_ctrlo_axi_m_arid,
  output chip_axi_addr_t      o_ctrlo_axi_m_araddr,
  output axi_len_t            o_ctrlo_axi_m_arlen,
  output axi_size_t           o_ctrlo_axi_m_arsize,
  output axi_burst_t          o_ctrlo_axi_m_arburst,
  output logic                o_ctrlo_axi_m_arlock,
  output axi_cache_t          o_ctrlo_axi_m_arcache,
  output axi_prot_t           o_ctrlo_axi_m_arprot,
  input  logic                i_ctrlo_axi_m_arready,

  // CTRL OUT AXI : Read Data / Response Channel
  input  logic                i_ctrlo_axi_m_rvalid,
  input  pve_lt_axi_m_id_t    i_ctrlo_axi_m_rid,
  input  chip_axi_lt_data_t   i_ctrlo_axi_m_rdata,
  input  axi_resp_t           i_ctrlo_axi_m_rresp,
  input  logic                i_ctrlo_axi_m_rlast,
  output logic                o_ctrlo_axi_m_rready,

  ///////////////////////////////////////////
  // CTRL IN AXI : AXI Narrow Slave Interface
  ///////////////////////////////////////////

  // CTRL IN AXI : Write Address Channel
  input  logic                i_ctrli_axi_s_awvalid,
  input  pve_lt_axi_s_id_t    i_ctrli_axi_s_awid,
  input  chip_axi_addr_t      i_ctrli_axi_s_awaddr,
  input  axi_len_t            i_ctrli_axi_s_awlen,
  input  axi_size_t           i_ctrli_axi_s_awsize,
  input  axi_burst_t          i_ctrli_axi_s_awburst,
  input  logic                i_ctrli_axi_s_awlock,
  input  axi_cache_t          i_ctrli_axi_s_awcache,
  input  axi_prot_t           i_ctrli_axi_s_awprot,
  output logic                o_ctrli_axi_s_awready,

  // CTRL IN AXI : Write Data Channel
  input  logic                i_ctrli_axi_s_wvalid,
  input  chip_axi_lt_data_t   i_ctrli_axi_s_wdata,
  input  chip_axi_lt_wstrb_t  i_ctrli_axi_s_wstrb,
  input  logic                i_ctrli_axi_s_wlast,
  output logic                o_ctrli_axi_s_wready,

  // CTRL IN AXI : Write Response Channel
  output logic                o_ctrli_axi_s_bvalid,
  output pve_lt_axi_s_id_t    o_ctrli_axi_s_bid,
  output axi_resp_t           o_ctrli_axi_s_bresp,
  input  logic                i_ctrli_axi_s_bready,

  // CTRL IN AXI : Read Address Channel
  input  logic                i_ctrli_axi_s_arvalid,
  input  pve_lt_axi_s_id_t    i_ctrli_axi_s_arid,
  input  chip_axi_addr_t      i_ctrli_axi_s_araddr,
  input  axi_len_t            i_ctrli_axi_s_arlen,
  input  axi_size_t           i_ctrli_axi_s_arsize,
  input  axi_burst_t          i_ctrli_axi_s_arburst,
  input  logic                i_ctrli_axi_s_arlock,
  input  axi_cache_t          i_ctrli_axi_s_arcache,
  input  axi_prot_t           i_ctrli_axi_s_arprot,
  output logic                o_ctrli_axi_s_arready,

  // DMA AXI : Read Data / Response Channel
  output logic                o_ctrli_axi_s_rvalid,
  output pve_lt_axi_s_id_t    o_ctrli_axi_s_rid,
  output chip_axi_lt_data_t   o_ctrli_axi_s_rdata,
  output axi_resp_t           o_ctrli_axi_s_rresp,
  output logic                o_ctrli_axi_s_rlast,
  input  logic                i_ctrli_axi_s_rready,

  //////////////////////////////////////
  // DMA AXI : AXI WIDE Master Interface
  //////////////////////////////////////

  // DMA AXI : Write Address Channel
  output logic                o_dma_axi_m_awvalid,
  output pve_ht_axi_m_id_t    o_dma_axi_m_awid,
  output chip_axi_addr_t      o_dma_axi_m_awaddr,
  output axi_len_t            o_dma_axi_m_awlen,
  output axi_size_t           o_dma_axi_m_awsize,
  output axi_burst_t          o_dma_axi_m_awburst,
  output logic                o_dma_axi_m_awlock,
  output axi_cache_t          o_dma_axi_m_awcache,
  output axi_prot_t           o_dma_axi_m_awprot,
  input  logic                i_dma_axi_m_awready,

  // DMA AXI : Write Data Channel
  output logic                o_dma_axi_m_wvalid,
  output chip_axi_ht_data_t   o_dma_axi_m_wdata,
  output chip_axi_ht_wstrb_t  o_dma_axi_m_wstrb,
  output logic                o_dma_axi_m_wlast,
  input  logic                i_dma_axi_m_wready,

  // DMA AXI : Write Response Channel
  input  logic                i_dma_axi_m_bvalid,
  input  pve_ht_axi_m_id_t    i_dma_axi_m_bid,
  input  axi_resp_t           i_dma_axi_m_bresp,
  output logic                o_dma_axi_m_bready,

  // DMA AXI : Read Address Channel
  output logic                o_dma_axi_m_arvalid,
  output pve_ht_axi_m_id_t    o_dma_axi_m_arid,
  output chip_axi_addr_t      o_dma_axi_m_araddr,
  output axi_len_t            o_dma_axi_m_arlen,
  output axi_size_t           o_dma_axi_m_arsize,
  output axi_burst_t          o_dma_axi_m_arburst,
  output logic                o_dma_axi_m_arlock,
  output axi_cache_t          o_dma_axi_m_arcache,
  output axi_prot_t           o_dma_axi_m_arprot,
  input  logic                i_dma_axi_m_arready,

  // DMA AXI : Read Data / Response Channel
  input  logic                i_dma_axi_m_rvalid,
  input  pve_ht_axi_m_id_t    i_dma_axi_m_rid,
  input  chip_axi_ht_data_t   i_dma_axi_m_rdata,
  input  axi_resp_t           i_dma_axi_m_rresp,
  input  logic                i_dma_axi_m_rlast,
  output logic                o_dma_axi_m_rready,

  // SRAM configuration
  input  impl_inp_t           i_mem_impl,
  output impl_oup_t           o_mem_impl
);

  chip_axi_addr_t pve_base_addr;

  // FABRIC PORTS
  logic                 lt_axi_s_awvalid[PVE_FABRIC_N_LT_S_EXT_PORTS];
  pve_lt_axi_s_id_t     lt_axi_s_awid   [PVE_FABRIC_N_LT_S_EXT_PORTS];
  chip_axi_addr_t       lt_axi_s_awaddr [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_len_t             lt_axi_s_awlen  [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_size_e            lt_axi_s_awsize [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_burst_e           lt_axi_s_awburst[PVE_FABRIC_N_LT_S_EXT_PORTS];
  logic                 lt_axi_s_awlock [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_cache_e           lt_axi_s_awcache[PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_prot_t            lt_axi_s_awprot [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_atop_t            lt_axi_s_awatop [PVE_FABRIC_N_LT_S_EXT_PORTS];
  logic                 lt_axi_s_awready[PVE_FABRIC_N_LT_S_EXT_PORTS];

  logic                 lt_axi_s_wvalid [PVE_FABRIC_N_LT_S_EXT_PORTS];
  chip_axi_lt_data_t    lt_axi_s_wdata  [PVE_FABRIC_N_LT_S_EXT_PORTS];
  chip_axi_lt_wstrb_t   lt_axi_s_wstrb  [PVE_FABRIC_N_LT_S_EXT_PORTS];
  logic                 lt_axi_s_wlast  [PVE_FABRIC_N_LT_S_EXT_PORTS];
  logic                 lt_axi_s_wready [PVE_FABRIC_N_LT_S_EXT_PORTS];

  logic                 lt_axi_s_bvalid [PVE_FABRIC_N_LT_S_EXT_PORTS];
  pve_lt_axi_s_id_t     lt_axi_s_bid    [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_resp_e            lt_axi_s_bresp  [PVE_FABRIC_N_LT_S_EXT_PORTS];
  logic                 lt_axi_s_bready [PVE_FABRIC_N_LT_S_EXT_PORTS];

  logic                 lt_axi_s_arvalid[PVE_FABRIC_N_LT_S_EXT_PORTS];
  pve_lt_axi_s_id_t     lt_axi_s_arid   [PVE_FABRIC_N_LT_S_EXT_PORTS];
  chip_axi_addr_t       lt_axi_s_araddr [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_len_t             lt_axi_s_arlen  [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_size_e            lt_axi_s_arsize [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_burst_e           lt_axi_s_arburst[PVE_FABRIC_N_LT_S_EXT_PORTS];
  logic                 lt_axi_s_arlock [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_cache_e           lt_axi_s_arcache[PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_prot_t            lt_axi_s_arprot [PVE_FABRIC_N_LT_S_EXT_PORTS];
  logic                 lt_axi_s_arready[PVE_FABRIC_N_LT_S_EXT_PORTS];

  logic                 lt_axi_s_rvalid [PVE_FABRIC_N_LT_S_EXT_PORTS];
  pve_lt_axi_s_id_t     lt_axi_s_rid    [PVE_FABRIC_N_LT_S_EXT_PORTS];
  chip_axi_lt_data_t    lt_axi_s_rdata  [PVE_FABRIC_N_LT_S_EXT_PORTS];
  axi_resp_e            lt_axi_s_rresp  [PVE_FABRIC_N_LT_S_EXT_PORTS];
  logic                 lt_axi_s_rlast  [PVE_FABRIC_N_LT_S_EXT_PORTS];
  logic                 lt_axi_s_rready [PVE_FABRIC_N_LT_S_EXT_PORTS];

  logic                 lt_axi_m_awvalid[PVE_FABRIC_N_LT_M_EXT_PORTS];
  pve_lt_axi_m_id_t     lt_axi_m_awid   [PVE_FABRIC_N_LT_M_EXT_PORTS];
  chip_axi_addr_t       lt_axi_m_awaddr [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_len_t             lt_axi_m_awlen  [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_size_e            lt_axi_m_awsize [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_burst_e           lt_axi_m_awburst[PVE_FABRIC_N_LT_M_EXT_PORTS];
  logic                 lt_axi_m_awlock [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_cache_e           lt_axi_m_awcache[PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_prot_t            lt_axi_m_awprot [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_atop_t            lt_axi_m_awatop [PVE_FABRIC_N_LT_M_EXT_PORTS];
  logic                 lt_axi_m_awready[PVE_FABRIC_N_LT_M_EXT_PORTS];

  logic                 lt_axi_m_wvalid [PVE_FABRIC_N_LT_M_EXT_PORTS];
  chip_axi_lt_data_t    lt_axi_m_wdata  [PVE_FABRIC_N_LT_M_EXT_PORTS];
  chip_axi_lt_wstrb_t   lt_axi_m_wstrb  [PVE_FABRIC_N_LT_M_EXT_PORTS];
  logic                 lt_axi_m_wlast  [PVE_FABRIC_N_LT_M_EXT_PORTS];
  logic                 lt_axi_m_wready [PVE_FABRIC_N_LT_M_EXT_PORTS];

  logic                 lt_axi_m_bvalid [PVE_FABRIC_N_LT_M_EXT_PORTS];
  pve_lt_axi_m_id_t     lt_axi_m_bid    [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_resp_e            lt_axi_m_bresp  [PVE_FABRIC_N_LT_M_EXT_PORTS];
  logic                 lt_axi_m_bready [PVE_FABRIC_N_LT_M_EXT_PORTS];

  logic                 lt_axi_m_arvalid[PVE_FABRIC_N_LT_M_EXT_PORTS];
  pve_lt_axi_m_id_t     lt_axi_m_arid   [PVE_FABRIC_N_LT_M_EXT_PORTS];
  chip_axi_addr_t       lt_axi_m_araddr [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_len_t             lt_axi_m_arlen  [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_size_e            lt_axi_m_arsize [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_burst_e           lt_axi_m_arburst[PVE_FABRIC_N_LT_M_EXT_PORTS];
  logic                 lt_axi_m_arlock [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_cache_e           lt_axi_m_arcache[PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_prot_t            lt_axi_m_arprot [PVE_FABRIC_N_LT_M_EXT_PORTS];
  logic                 lt_axi_m_arready[PVE_FABRIC_N_LT_M_EXT_PORTS];

  logic                 lt_axi_m_rvalid [PVE_FABRIC_N_LT_M_EXT_PORTS];
  pve_lt_axi_m_id_t     lt_axi_m_rid    [PVE_FABRIC_N_LT_M_EXT_PORTS];
  chip_axi_lt_data_t    lt_axi_m_rdata  [PVE_FABRIC_N_LT_M_EXT_PORTS];
  axi_resp_e            lt_axi_m_rresp  [PVE_FABRIC_N_LT_M_EXT_PORTS];
  logic                 lt_axi_m_rlast  [PVE_FABRIC_N_LT_M_EXT_PORTS];
  logic                 lt_axi_m_rready [PVE_FABRIC_N_LT_M_EXT_PORTS];

  logic                 ht_axi_s_awvalid[PVE_FABRIC_N_HT_S_EXT_PORTS];
  pve_ht_axi_s_id_t     ht_axi_s_awid   [PVE_FABRIC_N_HT_S_EXT_PORTS];
  chip_axi_addr_t       ht_axi_s_awaddr [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_len_t             ht_axi_s_awlen  [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_size_e            ht_axi_s_awsize [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_burst_e           ht_axi_s_awburst[PVE_FABRIC_N_HT_S_EXT_PORTS];
  logic                 ht_axi_s_awlock [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_cache_e           ht_axi_s_awcache[PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_prot_t            ht_axi_s_awprot [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_atop_t            ht_axi_s_awatop [PVE_FABRIC_N_HT_S_EXT_PORTS];
  logic                 ht_axi_s_awready[PVE_FABRIC_N_HT_S_EXT_PORTS];

  logic                 ht_axi_s_wvalid [PVE_FABRIC_N_HT_S_EXT_PORTS];
  chip_axi_ht_data_t    ht_axi_s_wdata  [PVE_FABRIC_N_HT_S_EXT_PORTS];
  chip_axi_ht_wstrb_t   ht_axi_s_wstrb  [PVE_FABRIC_N_HT_S_EXT_PORTS];
  logic                 ht_axi_s_wlast  [PVE_FABRIC_N_HT_S_EXT_PORTS];
  logic                 ht_axi_s_wready [PVE_FABRIC_N_HT_S_EXT_PORTS];

  logic                 ht_axi_s_bvalid [PVE_FABRIC_N_HT_S_EXT_PORTS];
  pve_ht_axi_s_id_t     ht_axi_s_bid    [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_resp_e            ht_axi_s_bresp  [PVE_FABRIC_N_HT_S_EXT_PORTS];
  logic                 ht_axi_s_bready [PVE_FABRIC_N_HT_S_EXT_PORTS];

  logic                 ht_axi_s_arvalid[PVE_FABRIC_N_HT_S_EXT_PORTS];
  pve_ht_axi_s_id_t     ht_axi_s_arid   [PVE_FABRIC_N_HT_S_EXT_PORTS];
  chip_axi_addr_t       ht_axi_s_araddr [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_len_t             ht_axi_s_arlen  [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_size_e            ht_axi_s_arsize [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_burst_e           ht_axi_s_arburst[PVE_FABRIC_N_HT_S_EXT_PORTS];
  logic                 ht_axi_s_arlock [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_cache_e           ht_axi_s_arcache[PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_prot_t            ht_axi_s_arprot [PVE_FABRIC_N_HT_S_EXT_PORTS];
  logic                 ht_axi_s_arready[PVE_FABRIC_N_HT_S_EXT_PORTS];

  logic                 ht_axi_s_rvalid [PVE_FABRIC_N_HT_S_EXT_PORTS];
  pve_ht_axi_s_id_t     ht_axi_s_rid    [PVE_FABRIC_N_HT_S_EXT_PORTS];
  chip_axi_ht_data_t    ht_axi_s_rdata  [PVE_FABRIC_N_HT_S_EXT_PORTS];
  axi_resp_e            ht_axi_s_rresp  [PVE_FABRIC_N_HT_S_EXT_PORTS];
  logic                 ht_axi_s_rlast  [PVE_FABRIC_N_HT_S_EXT_PORTS];
  logic                 ht_axi_s_rready [PVE_FABRIC_N_HT_S_EXT_PORTS];

  logic                 ht_axi_m_awvalid[PVE_FABRIC_N_HT_M_EXT_PORTS];
  pve_ht_axi_m_id_t     ht_axi_m_awid   [PVE_FABRIC_N_HT_M_EXT_PORTS];
  chip_axi_addr_t       ht_axi_m_awaddr [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_len_t             ht_axi_m_awlen  [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_size_e            ht_axi_m_awsize [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_burst_e           ht_axi_m_awburst[PVE_FABRIC_N_HT_M_EXT_PORTS];
  logic                 ht_axi_m_awlock [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_cache_e           ht_axi_m_awcache[PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_prot_t            ht_axi_m_awprot [PVE_FABRIC_N_HT_M_EXT_PORTS];
  logic                 ht_axi_m_awready[PVE_FABRIC_N_HT_M_EXT_PORTS];

  logic                 ht_axi_m_wvalid [PVE_FABRIC_N_HT_M_EXT_PORTS];
  chip_axi_ht_data_t    ht_axi_m_wdata  [PVE_FABRIC_N_HT_M_EXT_PORTS];
  chip_axi_ht_wstrb_t   ht_axi_m_wstrb  [PVE_FABRIC_N_HT_M_EXT_PORTS];
  logic                 ht_axi_m_wlast  [PVE_FABRIC_N_HT_M_EXT_PORTS];
  logic                 ht_axi_m_wready [PVE_FABRIC_N_HT_M_EXT_PORTS];

  logic                 ht_axi_m_arvalid[PVE_FABRIC_N_HT_M_EXT_PORTS];
  pve_ht_axi_m_id_t     ht_axi_m_arid   [PVE_FABRIC_N_HT_M_EXT_PORTS];
  chip_axi_addr_t       ht_axi_m_araddr [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_len_t             ht_axi_m_arlen  [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_size_e            ht_axi_m_arsize [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_burst_e           ht_axi_m_arburst[PVE_FABRIC_N_HT_M_EXT_PORTS];
  logic                 ht_axi_m_arlock [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_cache_e           ht_axi_m_arcache[PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_prot_t            ht_axi_m_arprot [PVE_FABRIC_N_HT_M_EXT_PORTS];
  logic                 ht_axi_m_arready[PVE_FABRIC_N_HT_M_EXT_PORTS];

  logic                 ht_axi_m_bvalid [PVE_FABRIC_N_HT_M_EXT_PORTS];
  pve_ht_axi_m_id_t     ht_axi_m_bid    [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_resp_e            ht_axi_m_bresp  [PVE_FABRIC_N_HT_M_EXT_PORTS];
  logic                 ht_axi_m_bready [PVE_FABRIC_N_HT_M_EXT_PORTS];

  logic                 ht_axi_m_rvalid [PVE_FABRIC_N_HT_M_EXT_PORTS];
  pve_ht_axi_m_id_t     ht_axi_m_rid    [PVE_FABRIC_N_HT_M_EXT_PORTS];
  chip_axi_ht_data_t    ht_axi_m_rdata  [PVE_FABRIC_N_HT_M_EXT_PORTS];
  axi_resp_e            ht_axi_m_rresp  [PVE_FABRIC_N_HT_M_EXT_PORTS];
  logic                 ht_axi_m_rlast  [PVE_FABRIC_N_HT_M_EXT_PORTS];
  logic                 ht_axi_m_rready [PVE_FABRIC_N_HT_M_EXT_PORTS];

  impl_inp_t [PVE_N_DMA:0] sram_impl_inp;
  impl_oup_t [PVE_N_DMA:0] sram_impl_oup;

  axe_tcl_sram_cfg #(
    .NUM_SRAMS(PVE_N_DMA + 1)
  ) u_sram_cfg (
    .i_s(i_mem_impl),
    .o_s(o_mem_impl),
    .o_m(sram_impl_inp),
    .i_m(sram_impl_oup)
  );

  always_comb pve_base_addr = (i_hart_base == PVE0_HART_BASE) ? PVE0_BASE_ADDR :
                              (i_hart_base == PVE1_HART_BASE) ? PVE1_BASE_ADDR : '1;

  // FABRIC HOOKUP TO TOP LEVEL PINS

  ///////////////////////////////
  // CTRL OUT AXI : AXI Narrow Master Interface
  ///////////////////////////////

  pve_lt_m_aw_t     lt_axi_m_aw;
  pve_lt_w_t        lt_axi_m_w;
  pve_lt_m_b_t      lt_axi_m_b;
  pve_lt_m_ar_t     lt_axi_m_ar;
  pve_lt_m_r_t      lt_axi_m_r;
  pve_lt_m_aw_t     ctrlo_axi_m_aw;
  pve_lt_w_t        ctrlo_axi_m_w;
  pve_lt_m_b_t      ctrlo_axi_m_b;
  pve_lt_m_ar_t     ctrlo_axi_m_ar;
  pve_lt_m_r_t      ctrlo_axi_m_r;

  always_comb lt_axi_m_aw = '{ id    : lt_axi_m_awid   [PVE_LT_M_PRTIDX_EXT],
                               addr  : lt_axi_m_awaddr [PVE_LT_M_PRTIDX_EXT],
                               len   : lt_axi_m_awlen  [PVE_LT_M_PRTIDX_EXT],
                               size  : lt_axi_m_awsize [PVE_LT_M_PRTIDX_EXT],
                               burst : lt_axi_m_awburst[PVE_LT_M_PRTIDX_EXT],
                               lock  : lt_axi_m_awlock [PVE_LT_M_PRTIDX_EXT],
                               cache : lt_axi_m_awcache[PVE_LT_M_PRTIDX_EXT],
                               prot  : lt_axi_m_awprot [PVE_LT_M_PRTIDX_EXT],
                               atop  : lt_axi_m_awatop [PVE_LT_M_PRTIDX_EXT] };
  always_comb lt_axi_m_w  = '{ data  : lt_axi_m_wdata  [PVE_LT_M_PRTIDX_EXT],
                               strb  : lt_axi_m_wstrb  [PVE_LT_M_PRTIDX_EXT],
                               last  : lt_axi_m_wlast  [PVE_LT_M_PRTIDX_EXT] };
  always_comb lt_axi_m_bid  [PVE_LT_M_PRTIDX_EXT] = lt_axi_m_b.id;
  always_comb lt_axi_m_bresp[PVE_LT_M_PRTIDX_EXT] = lt_axi_m_b.resp;
  always_comb lt_axi_m_ar = '{ id    : lt_axi_m_arid   [PVE_LT_M_PRTIDX_EXT],
                               addr  : lt_axi_m_araddr [PVE_LT_M_PRTIDX_EXT],
                               len   : lt_axi_m_arlen  [PVE_LT_M_PRTIDX_EXT],
                               size  : lt_axi_m_arsize [PVE_LT_M_PRTIDX_EXT],
                               burst : lt_axi_m_arburst[PVE_LT_M_PRTIDX_EXT],
                               lock  : lt_axi_m_arlock [PVE_LT_M_PRTIDX_EXT],
                               cache : lt_axi_m_arcache[PVE_LT_M_PRTIDX_EXT],
                               prot  : lt_axi_m_arprot [PVE_LT_M_PRTIDX_EXT] };
  always_comb lt_axi_m_rid  [PVE_LT_M_PRTIDX_EXT] = lt_axi_m_r.id;
  always_comb lt_axi_m_rdata[PVE_LT_M_PRTIDX_EXT] = lt_axi_m_r.data;
  always_comb lt_axi_m_rresp[PVE_LT_M_PRTIDX_EXT] = lt_axi_m_r.resp;
  always_comb lt_axi_m_rlast[PVE_LT_M_PRTIDX_EXT] = lt_axi_m_r.last;

  axe_axi_riscv_amos #(
    // ID width of both subordinate and manager port
    .AxiIdWidth          ( PVE_LT_M_ID_W ),
    // Address width of both subordinate and manager port
    .AxiAddrWidth        ( CHIP_AXI_ADDR_W ),
    // Address width of both subordinate and manager port
    .AxiDataWidth        ( CHIP_AXI_LT_DATA_W ),
    /// Maximum number of AXI write transactions outstanding at the same time
    .AxiMaxWriteTxns     ( 8 ),
    /// Word width of the widest RISC-V processor that can issue requests to this module.
    /// 32 for RV32; 64 for RV64, where both 32-bit (.W suffix) and 64-bit (.D suffix) AMOs are
    /// supported if `aw_strb` is set correctly.
    .RiscvWordWidth      ( 64 ),

    .axi_aw_t           ( pve_lt_m_aw_t     ),
    .axi_w_t            ( pve_lt_w_t        ),
    .axi_b_t            ( pve_lt_m_b_t      ),
    .axi_ar_t           ( pve_lt_m_ar_t     ),
    .axi_r_t            ( pve_lt_m_r_t      )
  ) u_amo_adapter (
    // Clock and reset signals
    .i_clk,
    .i_rst_n,
    // Subordinate port
    .i_axi_s_aw      ( lt_axi_m_aw                           ),
    .i_axi_s_aw_valid( lt_axi_m_awvalid[PVE_LT_M_PRTIDX_EXT] ),
    .o_axi_s_aw_ready( lt_axi_m_awready[PVE_LT_M_PRTIDX_EXT] ),
    .i_axi_s_w       ( lt_axi_m_w                            ),
    .i_axi_s_w_valid ( lt_axi_m_wvalid [PVE_LT_M_PRTIDX_EXT] ),
    .o_axi_s_w_ready ( lt_axi_m_wready [PVE_LT_M_PRTIDX_EXT] ),
    .o_axi_s_b       ( lt_axi_m_b                            ),
    .o_axi_s_b_valid ( lt_axi_m_bvalid [PVE_LT_M_PRTIDX_EXT] ),
    .i_axi_s_b_ready ( lt_axi_m_bready [PVE_LT_M_PRTIDX_EXT] ),
    .i_axi_s_ar      ( lt_axi_m_ar                           ),
    .i_axi_s_ar_valid( lt_axi_m_arvalid[PVE_LT_M_PRTIDX_EXT] ),
    .o_axi_s_ar_ready( lt_axi_m_arready[PVE_LT_M_PRTIDX_EXT] ),
    .o_axi_s_r       ( lt_axi_m_r                            ),
    .o_axi_s_r_valid ( lt_axi_m_rvalid [PVE_LT_M_PRTIDX_EXT] ),
    .i_axi_s_r_ready ( lt_axi_m_rready [PVE_LT_M_PRTIDX_EXT] ),
    // Manager port
    .o_axi_m_aw      ( ctrlo_axi_m_aw        ),
    .o_axi_m_aw_valid( o_ctrlo_axi_m_awvalid ),
    .i_axi_m_aw_ready( i_ctrlo_axi_m_awready ),
    .o_axi_m_w       ( ctrlo_axi_m_w         ),
    .o_axi_m_w_valid ( o_ctrlo_axi_m_wvalid  ),
    .i_axi_m_w_ready ( i_ctrlo_axi_m_wready  ),
    .i_axi_m_b       ( ctrlo_axi_m_b         ),
    .i_axi_m_b_valid ( i_ctrlo_axi_m_bvalid  ),
    .o_axi_m_b_ready ( o_ctrlo_axi_m_bready  ),
    .o_axi_m_ar      ( ctrlo_axi_m_ar        ),
    .o_axi_m_ar_valid( o_ctrlo_axi_m_arvalid ),
    .i_axi_m_ar_ready( i_ctrlo_axi_m_arready ),
    .i_axi_m_r       ( ctrlo_axi_m_r         ),
    .i_axi_m_r_valid ( i_ctrlo_axi_m_rvalid  ),
    .o_axi_m_r_ready ( o_ctrlo_axi_m_rready  )
  );

  // CTRL OUT AXI : Write Address Channel
  always_comb o_ctrlo_axi_m_awid    = ctrlo_axi_m_aw.id;
  always_comb o_ctrlo_axi_m_awaddr  = ctrlo_axi_m_aw.addr;
  always_comb o_ctrlo_axi_m_awlen   = ctrlo_axi_m_aw.len;
  always_comb o_ctrlo_axi_m_awsize  = axi_size_t'(ctrlo_axi_m_aw.size);
  always_comb o_ctrlo_axi_m_awburst = axi_burst_t'(ctrlo_axi_m_aw.burst);
  always_comb o_ctrlo_axi_m_awlock  = ctrlo_axi_m_aw.lock;
  always_comb o_ctrlo_axi_m_awcache = axi_cache_t'(ctrlo_axi_m_aw.cache);
  always_comb o_ctrlo_axi_m_awprot  = ctrlo_axi_m_aw.prot;

  // CTRL OUT AXI : Write Data Channel
  always_comb o_ctrlo_axi_m_wdata   = ctrlo_axi_m_w.data;
  always_comb o_ctrlo_axi_m_wstrb   = ctrlo_axi_m_w.strb;
  always_comb o_ctrlo_axi_m_wlast   = ctrlo_axi_m_w.last;

  // CTRL OUT AXI : Write Response Channel
  always_comb ctrlo_axi_m_b         = '{ id   : i_ctrlo_axi_m_bid,
                                         resp : axi_resp_e'(i_ctrlo_axi_m_bresp) };

  // CTRL OUT AXI : Read Address Channel
  always_comb o_ctrlo_axi_m_arid    = ctrlo_axi_m_ar.id;
  always_comb o_ctrlo_axi_m_araddr  = ctrlo_axi_m_ar.addr;
  always_comb o_ctrlo_axi_m_arlen   = ctrlo_axi_m_ar.len;
  always_comb o_ctrlo_axi_m_arsize  = axi_size_t'(ctrlo_axi_m_ar.size);
  always_comb o_ctrlo_axi_m_arburst = axi_burst_t'(ctrlo_axi_m_ar.burst);
  always_comb o_ctrlo_axi_m_arlock  = ctrlo_axi_m_ar.lock;
  always_comb o_ctrlo_axi_m_arcache = axi_cache_t'(ctrlo_axi_m_ar.cache);
  always_comb o_ctrlo_axi_m_arprot  = ctrlo_axi_m_ar.prot;

  // CTRL OUT AXI : Read Data / Response Channel
  always_comb ctrlo_axi_m_r         = '{ id   : i_ctrlo_axi_m_rid,
                                         data : i_ctrlo_axi_m_rdata,
                                         resp : axi_resp_e'(i_ctrlo_axi_m_rresp),
                                         last : i_ctrlo_axi_m_rlast };

  ///////////////////////////////
  // CTRL IN AXI : AXI Narrow Slave Interface
  ///////////////////////////////
  logic lt_axi_s_aw_ok;
  logic lt_axi_s_ar_ok;

  // CTRL IN AXI : Write Address Channel
  always_comb lt_axi_s_aw_ok                        = (i_ctrli_axi_s_awaddr[CHIP_AXI_ADDR_W-1:PVE_AXI_ADDR_W] ==
                                                       pve_base_addr[CHIP_AXI_ADDR_W-1:PVE_AXI_ADDR_W]) ? 1'b1 : 1'b0;
  always_comb lt_axi_s_awvalid[PVE_LT_S_PRTIDX_EXT] = i_ctrli_axi_s_awvalid & lt_axi_s_aw_ok;
  always_comb lt_axi_s_awaddr[PVE_LT_S_PRTIDX_EXT]  = i_ctrli_axi_s_awaddr;
  always_comb lt_axi_s_awid[PVE_LT_S_PRTIDX_EXT]    = i_ctrli_axi_s_awid;
  always_comb lt_axi_s_awlen[PVE_LT_S_PRTIDX_EXT]   = i_ctrli_axi_s_awlen;
  always_comb lt_axi_s_awsize[PVE_LT_S_PRTIDX_EXT]  = axi_size_e'(i_ctrli_axi_s_awsize);
  always_comb lt_axi_s_awburst[PVE_LT_S_PRTIDX_EXT] = axi_burst_e'(i_ctrli_axi_s_awburst);
  always_comb lt_axi_s_awlock[PVE_LT_S_PRTIDX_EXT]  = i_ctrli_axi_s_awlock;
  always_comb lt_axi_s_awcache[PVE_LT_S_PRTIDX_EXT] = axi_cache_e'(i_ctrli_axi_s_awcache);
  always_comb lt_axi_s_awprot[PVE_LT_S_PRTIDX_EXT]  = i_ctrli_axi_s_awprot;
  always_comb lt_axi_s_awatop[PVE_LT_S_PRTIDX_EXT]  = '0;
  always_comb o_ctrli_axi_s_awready                 = lt_axi_s_awready[PVE_LT_S_PRTIDX_EXT];

  // CTRL IN AXI : Write Data Channel
  always_comb lt_axi_s_wvalid[PVE_LT_S_PRTIDX_EXT]  = i_ctrli_axi_s_wvalid;
  always_comb lt_axi_s_wdata[PVE_LT_S_PRTIDX_EXT]   = i_ctrli_axi_s_wdata;
  always_comb lt_axi_s_wstrb[PVE_LT_S_PRTIDX_EXT]   = i_ctrli_axi_s_wstrb;
  always_comb lt_axi_s_wlast[PVE_LT_S_PRTIDX_EXT]   = i_ctrli_axi_s_wlast;
  always_comb o_ctrli_axi_s_wready                  = lt_axi_s_wready[PVE_LT_S_PRTIDX_EXT];

  // CTRL IN AXI : Write Response Channel
  always_comb o_ctrli_axi_s_bvalid                  = lt_axi_s_bvalid[PVE_LT_S_PRTIDX_EXT];
  always_comb o_ctrli_axi_s_bid                     = lt_axi_s_bid[PVE_LT_S_PRTIDX_EXT];
  always_comb o_ctrli_axi_s_bresp                   = axi_resp_t'(lt_axi_s_bresp[PVE_LT_S_PRTIDX_EXT]);
  always_comb lt_axi_s_bready[PVE_LT_S_PRTIDX_EXT]  = i_ctrli_axi_s_bready;

  // CTRL IN AXI : Read Address Channel
  always_comb lt_axi_s_ar_ok                        = (i_ctrli_axi_s_araddr[CHIP_AXI_ADDR_W-1:PVE_AXI_ADDR_W] ==
                                                       pve_base_addr[CHIP_AXI_ADDR_W-1:PVE_AXI_ADDR_W]) ? 1'b1 : 1'b0;
  always_comb lt_axi_s_arvalid[PVE_LT_S_PRTIDX_EXT] = i_ctrli_axi_s_arvalid & lt_axi_s_ar_ok;
  always_comb lt_axi_s_araddr[PVE_LT_S_PRTIDX_EXT]  = i_ctrli_axi_s_araddr;
  always_comb lt_axi_s_arid[PVE_LT_S_PRTIDX_EXT]    = i_ctrli_axi_s_arid;
  always_comb lt_axi_s_arlen[PVE_LT_S_PRTIDX_EXT]   = i_ctrli_axi_s_arlen;
  always_comb lt_axi_s_arsize[PVE_LT_S_PRTIDX_EXT]  = axi_size_e'(i_ctrli_axi_s_arsize);
  always_comb lt_axi_s_arburst[PVE_LT_S_PRTIDX_EXT] = axi_burst_e'(i_ctrli_axi_s_arburst);
  always_comb lt_axi_s_arlock[PVE_LT_S_PRTIDX_EXT]  = i_ctrli_axi_s_arlock;
  always_comb lt_axi_s_arcache[PVE_LT_S_PRTIDX_EXT] = axi_cache_e'(i_ctrli_axi_s_arcache);
  always_comb lt_axi_s_arprot[PVE_LT_S_PRTIDX_EXT]  = i_ctrli_axi_s_arprot;
  always_comb o_ctrli_axi_s_arready                 = lt_axi_s_arready[PVE_LT_S_PRTIDX_EXT];

  // DMA AXI : Read Data / Response Channel
  always_comb o_ctrli_axi_s_rvalid                  = lt_axi_s_rvalid[PVE_LT_S_PRTIDX_EXT];
  always_comb o_ctrli_axi_s_rid                     = lt_axi_s_rid[PVE_LT_S_PRTIDX_EXT];
  always_comb o_ctrli_axi_s_rdata                   = lt_axi_s_rdata[PVE_LT_S_PRTIDX_EXT];
  always_comb o_ctrli_axi_s_rresp                   = axi_resp_t'(lt_axi_s_rresp[PVE_LT_S_PRTIDX_EXT]);
  always_comb o_ctrli_axi_s_rlast                   = lt_axi_s_rlast[PVE_LT_S_PRTIDX_EXT];
  always_comb lt_axi_s_rready[PVE_LT_S_PRTIDX_EXT]  = i_ctrli_axi_s_rready;

  //////////////////////////////////////
  // DMA AXI : AXI WIDE Master Interface
  //////////////////////////////////////

  // DMA AXI : Write Address Channel
  always_comb o_dma_axi_m_awvalid                   = ht_axi_m_awvalid[PVE_HT_M_PRTIDX_EXT];
  always_comb ht_axi_m_awready[PVE_HT_M_PRTIDX_EXT] = i_dma_axi_m_awready;
  always_comb o_dma_axi_m_awaddr                    = ht_axi_m_awaddr[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_awid                      = ht_axi_m_awid[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_awlen                     = ht_axi_m_awlen[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_awsize                    = axi_size_t'(ht_axi_m_awsize[PVE_HT_M_PRTIDX_EXT]);
  always_comb o_dma_axi_m_awburst                   = axi_burst_t'(ht_axi_m_awburst[PVE_HT_M_PRTIDX_EXT]);
  always_comb o_dma_axi_m_awlock                    = ht_axi_m_awlock[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_awcache                   = axi_cache_t'(ht_axi_m_awcache[PVE_HT_M_PRTIDX_EXT]);
  always_comb o_dma_axi_m_awprot                    = ht_axi_m_awprot[PVE_HT_M_PRTIDX_EXT];

  // DMA AXI : Write Data Channel
  always_comb o_dma_axi_m_wvalid                    = ht_axi_m_wvalid[PVE_HT_M_PRTIDX_EXT];
  always_comb ht_axi_m_wready[PVE_HT_M_PRTIDX_EXT]  = i_dma_axi_m_wready;
  always_comb o_dma_axi_m_wdata                     = ht_axi_m_wdata[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_wstrb                     = ht_axi_m_wstrb[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_wlast                     = ht_axi_m_wlast[PVE_HT_M_PRTIDX_EXT];

  // DMA AXI : Write Response Channel
  always_comb ht_axi_m_bvalid[PVE_HT_M_PRTIDX_EXT]  = i_dma_axi_m_bvalid;
  always_comb o_dma_axi_m_bready                    = ht_axi_m_bready[PVE_HT_M_PRTIDX_EXT];
  always_comb ht_axi_m_bid[PVE_HT_M_PRTIDX_EXT]     = i_dma_axi_m_bid;
  always_comb ht_axi_m_bresp[PVE_HT_M_PRTIDX_EXT]   = axi_resp_e'(i_dma_axi_m_bresp);

  // DMA AXI : Read Address Channel
  always_comb o_dma_axi_m_arvalid                   = ht_axi_m_arvalid[PVE_HT_M_PRTIDX_EXT];
  always_comb ht_axi_m_arready[PVE_HT_M_PRTIDX_EXT] = i_dma_axi_m_arready;
  always_comb o_dma_axi_m_araddr                    = ht_axi_m_araddr[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_arid                      = ht_axi_m_arid[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_arlen                     = ht_axi_m_arlen[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_arsize                    = axi_size_t'(ht_axi_m_arsize[PVE_HT_M_PRTIDX_EXT]);
  always_comb o_dma_axi_m_arburst                   = axi_burst_t'(ht_axi_m_arburst[PVE_HT_M_PRTIDX_EXT]);
  always_comb o_dma_axi_m_arlock                    = ht_axi_m_arlock[PVE_HT_M_PRTIDX_EXT];
  always_comb o_dma_axi_m_arcache                   = axi_cache_t'(ht_axi_m_arcache[PVE_HT_M_PRTIDX_EXT]);
  always_comb o_dma_axi_m_arprot                    = ht_axi_m_arprot[PVE_HT_M_PRTIDX_EXT];

  // DMA AXI : Read Data / Response Channel
  always_comb ht_axi_m_rvalid[PVE_HT_M_PRTIDX_EXT]  = i_dma_axi_m_rvalid;
  always_comb o_dma_axi_m_rready                    = ht_axi_m_rready[PVE_HT_M_PRTIDX_EXT];
  always_comb ht_axi_m_rid[PVE_HT_M_PRTIDX_EXT]     = i_dma_axi_m_rid;
  always_comb ht_axi_m_rdata[PVE_HT_M_PRTIDX_EXT]   = i_dma_axi_m_rdata;
  always_comb ht_axi_m_rresp[PVE_HT_M_PRTIDX_EXT]   = axi_resp_e'(i_dma_axi_m_rresp);
  always_comb ht_axi_m_rlast[PVE_HT_M_PRTIDX_EXT]   = i_dma_axi_m_rlast;

  // FABRIC
  pve_fabric u_fabric (
    .i_clk,
    .i_rst_n,

    // Config
    .i_base_addr ( pve_base_addr ),

    // LT INTERFACES

    // Subordinates
    // AW
    .i_lt_axi_s_awvalid   ( lt_axi_s_awvalid  ),
    .i_lt_axi_s_awid      ( lt_axi_s_awid     ),
    .i_lt_axi_s_awaddr    ( lt_axi_s_awaddr   ),
    .i_lt_axi_s_awlen     ( lt_axi_s_awlen    ),
    .i_lt_axi_s_awsize    ( lt_axi_s_awsize   ),
    .i_lt_axi_s_awburst   ( lt_axi_s_awburst  ),
    .i_lt_axi_s_awlock    ( lt_axi_s_awlock   ),
    .i_lt_axi_s_awcache   ( lt_axi_s_awcache  ),
    .i_lt_axi_s_awprot    ( lt_axi_s_awprot   ),
    .i_lt_axi_s_awatop    ( lt_axi_s_awatop   ),
    .o_lt_axi_s_awready   ( lt_axi_s_awready  ),
    // W
    .i_lt_axi_s_wvalid    ( lt_axi_s_wvalid   ),
    .i_lt_axi_s_wdata     ( lt_axi_s_wdata    ),
    .i_lt_axi_s_wstrb     ( lt_axi_s_wstrb    ),
    .i_lt_axi_s_wlast     ( lt_axi_s_wlast    ),
    .o_lt_axi_s_wready    ( lt_axi_s_wready   ),
    // B
    .o_lt_axi_s_bvalid    ( lt_axi_s_bvalid   ),
    .o_lt_axi_s_bid       ( lt_axi_s_bid      ),
    .o_lt_axi_s_bresp     ( lt_axi_s_bresp    ),
    .i_lt_axi_s_bready    ( lt_axi_s_bready   ),
    // AR
    .i_lt_axi_s_arvalid   ( lt_axi_s_arvalid  ),
    .i_lt_axi_s_arid      ( lt_axi_s_arid     ),
    .i_lt_axi_s_araddr    ( lt_axi_s_araddr   ),
    .i_lt_axi_s_arlen     ( lt_axi_s_arlen    ),
    .i_lt_axi_s_arsize    ( lt_axi_s_arsize   ),
    .i_lt_axi_s_arburst   ( lt_axi_s_arburst  ),
    .i_lt_axi_s_arlock    ( lt_axi_s_arlock   ),
    .i_lt_axi_s_arcache   ( lt_axi_s_arcache  ),
    .i_lt_axi_s_arprot    ( lt_axi_s_arprot   ),
    .o_lt_axi_s_arready   ( lt_axi_s_arready  ),
    // R
    .o_lt_axi_s_rvalid    ( lt_axi_s_rvalid   ),
    .o_lt_axi_s_rid       ( lt_axi_s_rid      ),
    .o_lt_axi_s_rdata     ( lt_axi_s_rdata    ),
    .o_lt_axi_s_rresp     ( lt_axi_s_rresp    ),
    .o_lt_axi_s_rlast     ( lt_axi_s_rlast    ),
    .i_lt_axi_s_rready    ( lt_axi_s_rready   ),

    // Managers
    // AW
    .o_lt_axi_m_awvalid   ( lt_axi_m_awvalid  ),
    .o_lt_axi_m_awid      ( lt_axi_m_awid     ),
    .o_lt_axi_m_awaddr    ( lt_axi_m_awaddr   ),
    .o_lt_axi_m_awlen     ( lt_axi_m_awlen    ),
    .o_lt_axi_m_awsize    ( lt_axi_m_awsize   ),
    .o_lt_axi_m_awburst   ( lt_axi_m_awburst  ),
    .o_lt_axi_m_awlock    ( lt_axi_m_awlock   ),
    .o_lt_axi_m_awcache   ( lt_axi_m_awcache  ),
    .o_lt_axi_m_awprot    ( lt_axi_m_awprot   ),
    .o_lt_axi_m_awatop    ( lt_axi_m_awatop   ),
    .i_lt_axi_m_awready   ( lt_axi_m_awready  ),
    // W
    .o_lt_axi_m_wvalid    ( lt_axi_m_wvalid   ),
    .o_lt_axi_m_wdata     ( lt_axi_m_wdata    ),
    .o_lt_axi_m_wstrb     ( lt_axi_m_wstrb    ),
    .o_lt_axi_m_wlast     ( lt_axi_m_wlast    ),
    .i_lt_axi_m_wready    ( lt_axi_m_wready   ),
    // B
    .i_lt_axi_m_bvalid    ( lt_axi_m_bvalid   ),
    .i_lt_axi_m_bid       ( lt_axi_m_bid      ),
    .i_lt_axi_m_bresp     ( lt_axi_m_bresp    ),
    .o_lt_axi_m_bready    ( lt_axi_m_bready   ),
    // AR
    .o_lt_axi_m_arvalid   ( lt_axi_m_arvalid  ),
    .o_lt_axi_m_arid      ( lt_axi_m_arid     ),
    .o_lt_axi_m_araddr    ( lt_axi_m_araddr   ),
    .o_lt_axi_m_arlen     ( lt_axi_m_arlen    ),
    .o_lt_axi_m_arsize    ( lt_axi_m_arsize   ),
    .o_lt_axi_m_arburst   ( lt_axi_m_arburst  ),
    .o_lt_axi_m_arlock    ( lt_axi_m_arlock   ),
    .o_lt_axi_m_arcache   ( lt_axi_m_arcache  ),
    .o_lt_axi_m_arprot    ( lt_axi_m_arprot   ),
    .i_lt_axi_m_arready   ( lt_axi_m_arready  ),
    // R
    .i_lt_axi_m_rvalid    ( lt_axi_m_rvalid   ),
    .i_lt_axi_m_rid       ( lt_axi_m_rid      ),
    .i_lt_axi_m_rdata     ( lt_axi_m_rdata    ),
    .i_lt_axi_m_rresp     ( lt_axi_m_rresp    ),
    .i_lt_axi_m_rlast     ( lt_axi_m_rlast    ),
    .o_lt_axi_m_rready    ( lt_axi_m_rready   ),

    // HT INTERFACES

    // Subordinates
    // AW
    .i_ht_axi_s_awvalid   ( ht_axi_s_awvalid  ),
    .i_ht_axi_s_awid      ( ht_axi_s_awid     ),
    .i_ht_axi_s_awaddr    ( ht_axi_s_awaddr   ),
    .i_ht_axi_s_awlen     ( ht_axi_s_awlen    ),
    .i_ht_axi_s_awsize    ( ht_axi_s_awsize   ),
    .i_ht_axi_s_awburst   ( ht_axi_s_awburst  ),
    .i_ht_axi_s_awlock    ( ht_axi_s_awlock   ),
    .i_ht_axi_s_awcache   ( ht_axi_s_awcache  ),
    .i_ht_axi_s_awprot    ( ht_axi_s_awprot   ),
    .i_ht_axi_s_awatop    ( '{default:'0}     ),
    .o_ht_axi_s_awready   ( ht_axi_s_awready  ),
    // W
    .i_ht_axi_s_wvalid    ( ht_axi_s_wvalid   ),
    .i_ht_axi_s_wdata     ( ht_axi_s_wdata    ),
    .i_ht_axi_s_wstrb     ( ht_axi_s_wstrb    ),
    .i_ht_axi_s_wlast     ( ht_axi_s_wlast    ),
    .o_ht_axi_s_wready    ( ht_axi_s_wready   ),
    // B
    .o_ht_axi_s_bvalid    ( ht_axi_s_bvalid   ),
    .o_ht_axi_s_bid       ( ht_axi_s_bid      ),
    .o_ht_axi_s_bresp     ( ht_axi_s_bresp    ),
    .i_ht_axi_s_bready    ( ht_axi_s_bready   ),
    // AR
    .i_ht_axi_s_arvalid   ( ht_axi_s_arvalid  ),
    .i_ht_axi_s_arid      ( ht_axi_s_arid     ),
    .i_ht_axi_s_araddr    ( ht_axi_s_araddr   ),
    .i_ht_axi_s_arlen     ( ht_axi_s_arlen    ),
    .i_ht_axi_s_arsize    ( ht_axi_s_arsize   ),
    .i_ht_axi_s_arburst   ( ht_axi_s_arburst  ),
    .i_ht_axi_s_arlock    ( ht_axi_s_arlock   ),
    .i_ht_axi_s_arcache   ( ht_axi_s_arcache  ),
    .i_ht_axi_s_arprot    ( ht_axi_s_arprot   ),
    .o_ht_axi_s_arready   ( ht_axi_s_arready  ),
    // R
    .o_ht_axi_s_rvalid    ( ht_axi_s_rvalid   ),
    .o_ht_axi_s_rid       ( ht_axi_s_rid      ),
    .o_ht_axi_s_rdata     ( ht_axi_s_rdata    ),
    .o_ht_axi_s_rresp     ( ht_axi_s_rresp    ),
    .o_ht_axi_s_rlast     ( ht_axi_s_rlast    ),
    .i_ht_axi_s_rready    ( ht_axi_s_rready   ),

    // Managers
    // AW
    .o_ht_axi_m_awvalid   ( ht_axi_m_awvalid  ),
    .o_ht_axi_m_awid      ( ht_axi_m_awid     ),
    .o_ht_axi_m_awaddr    ( ht_axi_m_awaddr   ),
    .o_ht_axi_m_awlen     ( ht_axi_m_awlen    ),
    .o_ht_axi_m_awsize    ( ht_axi_m_awsize   ),
    .o_ht_axi_m_awburst   ( ht_axi_m_awburst  ),
    .o_ht_axi_m_awlock    ( ht_axi_m_awlock   ),
    .o_ht_axi_m_awcache   ( ht_axi_m_awcache  ),
    .o_ht_axi_m_awprot    ( ht_axi_m_awprot   ),
    .i_ht_axi_m_awready   ( ht_axi_m_awready  ),
    // W
    .o_ht_axi_m_wvalid    ( ht_axi_m_wvalid   ),
    .o_ht_axi_m_wdata     ( ht_axi_m_wdata    ),
    .o_ht_axi_m_wstrb     ( ht_axi_m_wstrb    ),
    .o_ht_axi_m_wlast     ( ht_axi_m_wlast    ),
    .i_ht_axi_m_wready    ( ht_axi_m_wready   ),
    // B
    .i_ht_axi_m_bvalid    ( ht_axi_m_bvalid   ),
    .i_ht_axi_m_bid       ( ht_axi_m_bid      ),
    .i_ht_axi_m_bresp     ( ht_axi_m_bresp    ),
    .o_ht_axi_m_bready    ( ht_axi_m_bready   ),
    // AR
    .o_ht_axi_m_arvalid   ( ht_axi_m_arvalid  ),
    .o_ht_axi_m_arid      ( ht_axi_m_arid     ),
    .o_ht_axi_m_araddr    ( ht_axi_m_araddr   ),
    .o_ht_axi_m_arlen     ( ht_axi_m_arlen    ),
    .o_ht_axi_m_arsize    ( ht_axi_m_arsize   ),
    .o_ht_axi_m_arburst   ( ht_axi_m_arburst  ),
    .o_ht_axi_m_arlock    ( ht_axi_m_arlock   ),
    .o_ht_axi_m_arcache   ( ht_axi_m_arcache  ),
    .o_ht_axi_m_arprot    ( ht_axi_m_arprot   ),
    .i_ht_axi_m_arready   ( ht_axi_m_arready  ),
    // R
    .i_ht_axi_m_rvalid    ( ht_axi_m_rvalid   ),
    .i_ht_axi_m_rid       ( ht_axi_m_rid      ),
    .i_ht_axi_m_rdata     ( ht_axi_m_rdata    ),
    .i_ht_axi_m_rresp     ( ht_axi_m_rresp    ),
    .i_ht_axi_m_rlast     ( ht_axi_m_rlast    ),
    .o_ht_axi_m_rready    ( ht_axi_m_rready   )
  );

  // CLUSTERs
  pve_hart_base_t          hart_id           [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  pve_cva6v_memreg_addr_t  memreg_addr       [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  pve_cva6v_memreg_size_t  memreg_size       [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  pve_cva6v_memreg_tcdm_t  memreg_tcdm       [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic                    ipi               [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  logic                    irq               [PVE_N_CLUSTERS];
  logic                    irq_q             [PVE_N_CLUSTERS];
  logic                    irq_q2            [PVE_N_CLUSTERS];
  logic                    time_irq          [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];
  pve_cva6v_platf_irq_t    dma_combined_int;
  logic                    debug_stop_time   [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU];

  perf_cntr_fu_status_t    [PVE_N_CPU-1:0] perf_cntr_fu_status;
  perf_cntr_fu_status_t    [PVE_N_CPU-1:0] perf_cntr_fu_status_q;
  perf_cntr_fu_status_t    [PVE_N_CPU-1:0] perf_cntr_fu_status_q2;
  perf_cntr_fu_status_t    [PVE_N_CPU-1:0] perf_cntr_fu_status_q3;
  logic                    [PVE_N_CPU-1:0] perf_cntr_dispatch_queue_full;
  logic                    [PVE_N_CPU-1:0] perf_cntr_dispatch_queue_full_q;
  logic                    [PVE_N_CPU-1:0] perf_cntr_dispatch_queue_full_q2;
  logic                    [PVE_N_CPU-1:0] perf_cntr_dispatch_queue_full_q3;
  logic                    [PVE_N_CPU-1:0] perf_cntr_dispatch_queue_empty;
  logic                    [PVE_N_CPU-1:0] perf_cntr_dispatch_queue_empty_q;
  logic                    [PVE_N_CPU-1:0] perf_cntr_dispatch_queue_empty_q2;
  logic                    [PVE_N_CPU-1:0] perf_cntr_dispatch_queue_empty_q3;
  logic                    [PVE_N_CPU-1:0] perf_cntr_commit_queue_full;
  logic                    [PVE_N_CPU-1:0] perf_cntr_commit_queue_full_q;
  logic                    [PVE_N_CPU-1:0] perf_cntr_commit_queue_full_q2;
  logic                    [PVE_N_CPU-1:0] perf_cntr_commit_queue_full_q3;
  logic                    [PVE_N_CPU-1:0] perf_cntr_commit_queue_empty;
  logic                    [PVE_N_CPU-1:0] perf_cntr_commit_queue_empty_q;
  logic                    [PVE_N_CPU-1:0] perf_cntr_commit_queue_empty_q2;
  logic                    [PVE_N_CPU-1:0] perf_cntr_commit_queue_empty_q3;
  pve_cva6v_event_addr_t   [PVE_N_CPU-1:0] perf_event_addr;
  pve_cva6v_event_addr_t   [PVE_N_CPU-1:0] perf_event_addr_q;
  pve_cva6v_event_addr_t   [PVE_N_CPU-1:0] perf_event_addr_q2;
  pve_cva6v_event_addr_t   [PVE_N_CPU-1:0] perf_event_addr_q3;
  pve_cva6v_event_deltas_t [PVE_N_CPU-1:0] perf_event_deltas;
  pve_cva6v_event_deltas_t [PVE_N_CPU-1:0] perf_event_deltas_q;
  pve_cva6v_event_deltas_t [PVE_N_CPU-1:0] perf_event_deltas_q2;
  pve_cva6v_event_deltas_t [PVE_N_CPU-1:0] perf_event_deltas_q3;

  pve_l1_base_addr_t       l1_base_address     [PVE_N_CLUSTERS];
  chip_axi_addr_t          l1_base_address_full[PVE_N_CLUSTERS];
  chip_axi_addr_t          memreg_addr_mux     [PVE_N_CLUSTERS][PVE_CLUSTER_N_CPU][2];

  localparam logic [PAddrSizeWidth-1:0] MEMREG_WIDTH = $clog2(PVE_TGT_CL0L1_MMAP_SIZE / 2);
  for (genvar I = 0; I < PVE_N_CLUSTERS; I++) begin: g_cluster
    localparam int CVA6V_NUM_CUTS = (I == 1 || I == 2) ? 2 : 3;
    localparam int L1_NUM_CUTS = (I == 1 || I == 2) ? 1 : 3;
    always_comb l1_base_address_full[I] = pve_base_addr + PVE_TGT_CL0L1_MMAP_BASE + I*PVE_TGT_CL0L1_MMAP_SIZE;
    always_comb l1_base_address[I] = l1_base_address_full[I][CHIP_AXI_ADDR_W-1-:pve_l1_pkg::PVE_L1_BASE_ADDR_W];
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) begin
        irq[I]    <= 1'b0;
        irq_q[I]  <= 1'b0;
        irq_q2[I] <= 1'b0;
      end else begin
        irq[I]    <= i_int_shutdown_req;
        irq_q[I]  <= irq[I];
        irq_q2[I] <= irq_q[I];
      end
    end
    for (genvar J = 0; J < PVE_CLUSTER_N_CPU; J++) begin: g_cpus
      // boot all PVE cores from start of SPM
      always_comb hart_id[I][J]   = i_hart_base + I*PVE_CLUSTER_N_CPU + J;
      always_comb memreg_addr_mux[I][J][0] = (i_memreg_csr[I][J][0][47]) ? i_memreg_csr[I][J][0][39:0] : l1_base_address_full[I] + PVE_TGT_CL0L1_MMAP_SIZE / 2;
      always_comb memreg_addr_mux[I][J][1] = (i_memreg_csr[I][J][1][47]) ? i_memreg_csr[I][J][1][39:0] : l1_base_address_full[I];
      always_comb memreg_addr[I][J] = pve_cva6v_memreg_addr_t'({memreg_addr_mux[I][J][1], memreg_addr_mux[I][J][0]});
      always_comb memreg_size[I][J] = pve_cva6v_memreg_size_t'({i_memreg_csr[I][J][1][45:40], i_memreg_csr[I][J][0][45:40]});
      always_comb memreg_tcdm[I][J] = pve_cva6v_memreg_tcdm_t'({i_memreg_csr[I][J][1][46], i_memreg_csr[I][J][0][46]});
    end

    pve_cluster #(
      .CVA6V_NUM_CUTS(CVA6V_NUM_CUTS),
      .L1_NUM_CUTS   (L1_NUM_CUTS   )
    ) u_cluster (
      .i_clk,
      .i_rst_n,
      .i_clk_en                        ( i_clk_en[I]             ),

      // Config
      .i_boot_addr                     ( i_boot_addr[I]          ),
      .i_hart_id                       ( hart_id[I]              ),
      // Memory regions
      .i_memreg_addr                   ( memreg_addr[I]          ),
      .i_memreg_size                   ( memreg_size[I]          ),
      .i_memreg_tcdm                   ( memreg_tcdm[I]          ),

      // Interrupt inputs
      .i_int_shutdown_req              ( irq_q2[I]               ), // connected to PCTL in the wrapper
      .i_ipi                           ( ipi[I]                  ), // CLINT
      .i_time_irq                      ( time_irq[I]             ), // CLINT
      .i_platform_irq                  ( {dma_combined_int, dma_combined_int} ), // DMA
      // Debug
      .i_debug_req                     ( i_debug_req[I]          ), // top
      .i_debug_rst_halt_req            ( i_debug_rst_halt_req[I] ), // top
      .o_debug_stop_time               ( debug_stop_time[I]      ), // unconnected
      // Hart status
      .o_hart_is_wfi                   ( o_hart_is_wfi[I]        ), // not used atm, exposed in _p
      .o_hart_unavail                  ( o_hart_unavail[I]       ), // top
      .o_hart_under_reset              ( o_hart_under_reset[I]   ), // top

      // Memory side, AXI Manager
      // AW
      .o_cpu_axi_m_awvalid             ( lt_axi_s_awvalid[PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_awid                ( lt_axi_s_awid   [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_awaddr              ( lt_axi_s_awaddr [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_awlen               ( lt_axi_s_awlen  [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_awsize              ( lt_axi_s_awsize [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_awburst             ( lt_axi_s_awburst[PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_awlock              ( lt_axi_s_awlock [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_awcache             ( lt_axi_s_awcache[PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_awprot              ( lt_axi_s_awprot [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_awatop              ( lt_axi_s_awatop [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .i_cpu_axi_m_awready             ( lt_axi_s_awready[PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      // W
      .o_cpu_axi_m_wvalid              ( lt_axi_s_wvalid [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_wdata               ( lt_axi_s_wdata  [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_wstrb               ( lt_axi_s_wstrb  [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_wlast               ( lt_axi_s_wlast  [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .i_cpu_axi_m_wready              ( lt_axi_s_wready [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      // B
      .i_cpu_axi_m_bvalid              ( lt_axi_s_bvalid [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .i_cpu_axi_m_bid                 ( lt_axi_s_bid    [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .i_cpu_axi_m_bresp               ( lt_axi_s_bresp  [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_bready              ( lt_axi_s_bready [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      // AR
      .o_cpu_axi_m_arvalid             ( lt_axi_s_arvalid[PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_arid                ( lt_axi_s_arid   [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_araddr              ( lt_axi_s_araddr [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_arlen               ( lt_axi_s_arlen  [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_arsize              ( lt_axi_s_arsize [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_arburst             ( lt_axi_s_arburst[PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_arlock              ( lt_axi_s_arlock [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_arcache             ( lt_axi_s_arcache[PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_arprot              ( lt_axi_s_arprot [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .i_cpu_axi_m_arready             ( lt_axi_s_arready[PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      // R
      .i_cpu_axi_m_rvalid              ( lt_axi_s_rvalid [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .i_cpu_axi_m_rid                 ( lt_axi_s_rid    [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .i_cpu_axi_m_rdata               ( lt_axi_s_rdata  [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .i_cpu_axi_m_rresp               ( lt_axi_s_rresp  [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .i_cpu_axi_m_rlast               ( lt_axi_s_rlast  [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),
      .o_cpu_axi_m_rready              ( lt_axi_s_rready [PVE_LT_S_PRTIDX_CL0CPU0 + PVE_CLUSTER_N_CPU * I +: PVE_CLUSTER_N_CPU] ),

      // Raptor performance counter signals
      .o_perf_cntr_fu_status           ( perf_cntr_fu_status           [I*PVE_CLUSTER_N_CPU+:PVE_CLUSTER_N_CPU] ),
      .o_perf_cntr_dispatch_queue_full ( perf_cntr_dispatch_queue_full [I*PVE_CLUSTER_N_CPU+:PVE_CLUSTER_N_CPU] ),
      .o_perf_cntr_dispatch_queue_empty( perf_cntr_dispatch_queue_empty[I*PVE_CLUSTER_N_CPU+:PVE_CLUSTER_N_CPU] ),
      .o_perf_cntr_commit_queue_full   ( perf_cntr_commit_queue_full   [I*PVE_CLUSTER_N_CPU+:PVE_CLUSTER_N_CPU] ),
      .o_perf_cntr_commit_queue_empty  ( perf_cntr_commit_queue_empty  [I*PVE_CLUSTER_N_CPU+:PVE_CLUSTER_N_CPU] ),
      // CVA6V performance event signals
      .o_perf_event_addr               ( perf_event_addr               [I*PVE_CLUSTER_N_CPU+:PVE_CLUSTER_N_CPU] ),
      .o_perf_event_deltas             ( perf_event_deltas             [I*PVE_CLUSTER_N_CPU+:PVE_CLUSTER_N_CPU] ),

      // AXI write address channel
      .i_l1_axi_s_awvalid              ( ht_axi_m_awvalid[PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_awid                 ( ht_axi_m_awid   [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_awaddr               ( ht_axi_m_awaddr [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_awlen                ( ht_axi_m_awlen  [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_awsize               ( ht_axi_m_awsize [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_awburst              ( ht_axi_m_awburst[PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .o_l1_axi_s_awready              ( ht_axi_m_awready[PVE_HT_M_PRTIDX_CL0L1 + I] ),
      // AXI write data channel
      .i_l1_axi_s_wvalid               ( ht_axi_m_wvalid [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_wdata                ( ht_axi_m_wdata  [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_wstrb                ( ht_axi_m_wstrb  [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_wlast                ( ht_axi_m_wlast  [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .o_l1_axi_s_wready               ( ht_axi_m_wready [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      // AXI write response channel
      .o_l1_axi_s_bvalid               ( ht_axi_m_bvalid [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .o_l1_axi_s_bid                  ( ht_axi_m_bid    [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .o_l1_axi_s_bresp                ( ht_axi_m_bresp  [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_bready               ( ht_axi_m_bready [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      // AXI read address channel
      .i_l1_axi_s_arvalid              ( ht_axi_m_arvalid[PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_arid                 ( ht_axi_m_arid   [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_araddr               ( ht_axi_m_araddr [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_arlen                ( ht_axi_m_arlen  [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_arsize               ( ht_axi_m_arsize [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_arburst              ( ht_axi_m_arburst[PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .o_l1_axi_s_arready              ( ht_axi_m_arready[PVE_HT_M_PRTIDX_CL0L1 + I] ),
      // AXI read data/response channel
      .o_l1_axi_s_rvalid               ( ht_axi_m_rvalid [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .o_l1_axi_s_rid                  ( ht_axi_m_rid    [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .o_l1_axi_s_rdata                ( ht_axi_m_rdata  [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .o_l1_axi_s_rresp                ( ht_axi_m_rresp  [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .o_l1_axi_s_rlast                ( ht_axi_m_rlast  [PVE_HT_M_PRTIDX_CL0L1 + I] ),
      .i_l1_axi_s_rready               ( ht_axi_m_rready [PVE_HT_M_PRTIDX_CL0L1 + I] ),

      // Configuration control
      .i_l1_base_address               ( l1_base_address [I] )
    );
  end: g_cluster

  logic [PVE_N_DMA_CHNLS-1:0] dma_int  [PVE_N_DMA];
  logic [PVE_N_DMA_CHNLS-1:0] dma_int_q[PVE_N_DMA];
  logic [0:0] dummy_i_tok_prod_rdy[PVE_N_DMA_CHNLS] = '{default:1};
  logic [0:0] dummy_i_tok_cons_vld[PVE_N_DMA_CHNLS] = '{default:0};

  logic                 dma_conf_axi_awvalid[PVE_N_DMA];
  pve_lt_axi_m_id_t     dma_conf_axi_awid   [PVE_N_DMA];
  dma_conf_addr_t       dma_conf_axi_awaddr [PVE_N_DMA];
  axi_len_t             dma_conf_axi_awlen  [PVE_N_DMA];
  axi_size_e            dma_conf_axi_awsize [PVE_N_DMA];
  axi_burst_e           dma_conf_axi_awburst[PVE_N_DMA];
  logic                 dma_conf_axi_awlock [PVE_N_DMA];
  axi_cache_e           dma_conf_axi_awcache[PVE_N_DMA];
  axi_prot_t            dma_conf_axi_awprot [PVE_N_DMA];
  logic                 dma_conf_axi_awready[PVE_N_DMA];

  logic                 dma_conf_axi_wvalid [PVE_N_DMA];
  chip_axi_lt_data_t    dma_conf_axi_wdata  [PVE_N_DMA];
  chip_axi_lt_wstrb_t   dma_conf_axi_wstrb  [PVE_N_DMA];
  logic                 dma_conf_axi_wlast  [PVE_N_DMA];
  logic                 dma_conf_axi_wready [PVE_N_DMA];

  logic                 dma_conf_axi_bvalid [PVE_N_DMA];
  pve_lt_axi_m_id_t     dma_conf_axi_bid    [PVE_N_DMA];
  axi_resp_e            dma_conf_axi_bresp  [PVE_N_DMA];
  logic                 dma_conf_axi_bready [PVE_N_DMA];

  logic                 dma_conf_axi_arvalid[PVE_N_DMA];
  pve_lt_axi_m_id_t     dma_conf_axi_arid   [PVE_N_DMA];
  dma_conf_addr_t       dma_conf_axi_araddr [PVE_N_DMA];
  axi_len_t             dma_conf_axi_arlen  [PVE_N_DMA];
  axi_size_e            dma_conf_axi_arsize [PVE_N_DMA];
  axi_burst_e           dma_conf_axi_arburst[PVE_N_DMA];
  logic                 dma_conf_axi_arlock [PVE_N_DMA];
  axi_cache_e           dma_conf_axi_arcache[PVE_N_DMA];
  axi_prot_t            dma_conf_axi_arprot [PVE_N_DMA];
  logic                 dma_conf_axi_arready[PVE_N_DMA];

  logic                 dma_conf_axi_rvalid [PVE_N_DMA];
  pve_lt_axi_m_id_t     dma_conf_axi_rid    [PVE_N_DMA];
  chip_axi_lt_data_t    dma_conf_axi_rdata  [PVE_N_DMA];
  axi_resp_e            dma_conf_axi_rresp  [PVE_N_DMA];
  logic                 dma_conf_axi_rlast  [PVE_N_DMA];
  logic                 dma_conf_axi_rready [PVE_N_DMA];

  pve_axi_multistage_spill_reg #(
    .NUM_STAGES_AW(0                  ),
    .NUM_STAGES_W (0                  ),
    .NUM_STAGES_B (0                  ),
    .NUM_STAGES_AR(0                  ),
    .NUM_STAGES_R (0                  ),
    .axi_addr_t   (dma_conf_addr_t    ),
    .axi_id_t     (pve_lt_axi_m_id_t  ),
    .axi_data_t   (chip_axi_lt_data_t ),
    .axi_strb_t   (chip_axi_lt_wstrb_t)
  ) u_dma1_spill_reg (
    .i_clk,
    .i_rst_n,
    // Subordinate side
    // AXI write address channel
    .i_axi_s_awvalid(lt_axi_m_awvalid[PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_awid   (lt_axi_m_awid   [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_awaddr (lt_axi_m_awaddr [PVE_LT_M_PRTIDX_DMA0 + 1][PVE_TGT_DMA_MMAP_W-1:0]),
    .i_axi_s_awlen  (lt_axi_m_awlen  [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_awsize (lt_axi_m_awsize [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_awburst(lt_axi_m_awburst[PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_awlock (lt_axi_m_awlock [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_awcache(lt_axi_m_awcache[PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_awprot (lt_axi_m_awprot [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_awatop ('0                                        ),
    .o_axi_s_awready(lt_axi_m_awready[PVE_LT_M_PRTIDX_DMA0 + 1]),
    // AXI write data channel
    .i_axi_s_wvalid (lt_axi_m_wvalid [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_wdata  (lt_axi_m_wdata  [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_wstrb  (lt_axi_m_wstrb  [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_wlast  (lt_axi_m_wlast  [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .o_axi_s_wready (lt_axi_m_wready [PVE_LT_M_PRTIDX_DMA0 + 1]),
    // AXI write response channel
    .o_axi_s_bvalid (lt_axi_m_bvalid [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .o_axi_s_bid    (lt_axi_m_bid    [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .o_axi_s_bresp  (lt_axi_m_bresp  [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_bready (lt_axi_m_bready [PVE_LT_M_PRTIDX_DMA0 + 1]),
    // AXI read address channel
    .i_axi_s_arvalid(lt_axi_m_arvalid[PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_arid   (lt_axi_m_arid   [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_araddr (lt_axi_m_araddr [PVE_LT_M_PRTIDX_DMA0 + 1][PVE_TGT_DMA_MMAP_W-1:0]),
    .i_axi_s_arlen  (lt_axi_m_arlen  [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_arsize (lt_axi_m_arsize [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_arburst(lt_axi_m_arburst[PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_arlock (lt_axi_m_arlock [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_arcache(lt_axi_m_arcache[PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_arprot (lt_axi_m_arprot [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .o_axi_s_arready(lt_axi_m_arready[PVE_LT_M_PRTIDX_DMA0 + 1]),
    // AXI read data/response channel
    .o_axi_s_rvalid (lt_axi_m_rvalid [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .o_axi_s_rid    (lt_axi_m_rid    [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .o_axi_s_rdata  (lt_axi_m_rdata  [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .o_axi_s_rresp  (lt_axi_m_rresp  [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .o_axi_s_rlast  (lt_axi_m_rlast  [PVE_LT_M_PRTIDX_DMA0 + 1]),
    .i_axi_s_rready (lt_axi_m_rready [PVE_LT_M_PRTIDX_DMA0 + 1]),
    // Manager Ports
    // AXI write address channel
    .o_axi_m_awvalid(dma_conf_axi_awvalid[1] ),
    .o_axi_m_awid   (dma_conf_axi_awid   [1] ),
    .o_axi_m_awaddr (dma_conf_axi_awaddr [1] ),
    .o_axi_m_awlen  (dma_conf_axi_awlen  [1] ),
    .o_axi_m_awsize (dma_conf_axi_awsize [1] ),
    .o_axi_m_awburst(dma_conf_axi_awburst[1] ),
    .o_axi_m_awlock (dma_conf_axi_awlock [1] ),
    .o_axi_m_awcache(dma_conf_axi_awcache[1] ),
    .o_axi_m_awprot (dma_conf_axi_awprot [1] ),
    .o_axi_m_awatop (                        ), // ASO-UNUSED_OUTPUT: dma doesn't use AWTOP
    .i_axi_m_awready(dma_conf_axi_awready[1] ),
    // AXI write data channel
    .o_axi_m_wvalid (dma_conf_axi_wvalid [1] ),
    .o_axi_m_wdata  (dma_conf_axi_wdata  [1] ),
    .o_axi_m_wstrb  (dma_conf_axi_wstrb  [1] ),
    .o_axi_m_wlast  (dma_conf_axi_wlast  [1] ),
    .i_axi_m_wready (dma_conf_axi_wready [1] ),
    // AXI write response channel
    .i_axi_m_bvalid (dma_conf_axi_bvalid [1] ),
    .i_axi_m_bid    (dma_conf_axi_bid    [1] ),
    .i_axi_m_bresp  (dma_conf_axi_bresp  [1] ),
    .o_axi_m_bready (dma_conf_axi_bready [1] ),
    // AXI read address channel
    .o_axi_m_arvalid(dma_conf_axi_arvalid[1]),
    .o_axi_m_arid   (dma_conf_axi_arid   [1]),
    .o_axi_m_araddr (dma_conf_axi_araddr [1]),
    .o_axi_m_arlen  (dma_conf_axi_arlen  [1]),
    .o_axi_m_arsize (dma_conf_axi_arsize [1]),
    .o_axi_m_arburst(dma_conf_axi_arburst[1]),
    .o_axi_m_arlock (dma_conf_axi_arlock [1]),
    .o_axi_m_arcache(dma_conf_axi_arcache[1]),
    .o_axi_m_arprot (dma_conf_axi_arprot [1]),
    .i_axi_m_arready(dma_conf_axi_arready[1]),
    // AXI read data/response channel
    .i_axi_m_rvalid (dma_conf_axi_rvalid [1]),
    .i_axi_m_rid    (dma_conf_axi_rid    [1]),
    .i_axi_m_rdata  (dma_conf_axi_rdata  [1]),
    .i_axi_m_rresp  (dma_conf_axi_rresp  [1]),
    .i_axi_m_rlast  (dma_conf_axi_rlast  [1]),
    .o_axi_m_rready (dma_conf_axi_rready [1])
  );
  always_comb dma_conf_axi_awvalid[0] = lt_axi_m_awvalid[PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_awid   [0] = lt_axi_m_awid   [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_awaddr [0] = lt_axi_m_awaddr [PVE_LT_M_PRTIDX_DMA0][PVE_TGT_DMA_MMAP_W-1:0];
  always_comb dma_conf_axi_awlen  [0] = lt_axi_m_awlen  [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_awsize [0] = lt_axi_m_awsize [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_awburst[0] = lt_axi_m_awburst[PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_awlock [0] = lt_axi_m_awlock [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_awcache[0] = lt_axi_m_awcache[PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_awprot [0] = lt_axi_m_awprot [PVE_LT_M_PRTIDX_DMA0];
  always_comb lt_axi_m_awready[PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_awready[0];

  always_comb dma_conf_axi_wvalid [0] = lt_axi_m_wvalid [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_wdata  [0] = lt_axi_m_wdata  [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_wstrb  [0] = lt_axi_m_wstrb  [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_wlast  [0] = lt_axi_m_wlast  [PVE_LT_M_PRTIDX_DMA0];
  always_comb lt_axi_m_wready [PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_wready [0];

  always_comb lt_axi_m_bvalid [PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_bvalid [0];
  always_comb lt_axi_m_bid    [PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_bid    [0];
  always_comb lt_axi_m_bresp  [PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_bresp  [0];
  always_comb dma_conf_axi_bready [0] = lt_axi_m_bready [PVE_LT_M_PRTIDX_DMA0];

  always_comb dma_conf_axi_arvalid[0] = lt_axi_m_arvalid[PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_arid   [0] = lt_axi_m_arid   [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_araddr [0] = lt_axi_m_araddr [PVE_LT_M_PRTIDX_DMA0][PVE_TGT_DMA_MMAP_W-1:0];
  always_comb dma_conf_axi_arlen  [0] = lt_axi_m_arlen  [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_arsize [0] = lt_axi_m_arsize [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_arburst[0] = lt_axi_m_arburst[PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_arlock [0] = lt_axi_m_arlock [PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_arcache[0] = lt_axi_m_arcache[PVE_LT_M_PRTIDX_DMA0];
  always_comb dma_conf_axi_arprot [0] = lt_axi_m_arprot [PVE_LT_M_PRTIDX_DMA0];
  always_comb lt_axi_m_arready[PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_arready[0];

  always_comb lt_axi_m_rvalid [PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_rvalid [0];
  always_comb lt_axi_m_rid    [PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_rid    [0];
  always_comb lt_axi_m_rdata  [PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_rdata  [0];
  always_comb lt_axi_m_rresp  [PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_rresp  [0];
  always_comb lt_axi_m_rlast  [PVE_LT_M_PRTIDX_DMA0] = dma_conf_axi_rlast  [0];
  always_comb dma_conf_axi_rready [0] = lt_axi_m_rready [PVE_LT_M_PRTIDX_DMA0];

  // DMAs
  for (genvar I = 0; I < PVE_N_DMA; I++) begin: g_dma
    dma #(
      .NUM_PORTS            ( PVE_N_DMA_PORTS    ),
      .NUM_CHNLS            ( PVE_N_DMA_CHNLS    ),
      .DMA_N_BUF_IDXS       ( 256                ),
      .DMA_N_IMPL_BUF_IDXS  ( 256                ),
      .NR_TOK_PROD          ( 1                  ),
      .NR_TOK_CONS          ( 1                  ),
      .NR_TOP_TOK_PROD      ( 0                  ),
      .NR_TOP_TOK_CONS      ( 0                  ),
      .dma_axi_s_data_t     ( chip_axi_lt_data_t ),
      .dma_axi_s_addr_t     ( dma_conf_addr_t    ),
      .dma_axi_s_id_t       ( pve_lt_axi_m_id_t  ),
      .dma_axi_m_data_t     ( chip_axi_ht_data_t ),
      .dma_axi_m_addr_t     ( chip_axi_addr_t    ),
      .dma_axi_m_id_t       ( pve_ht_axi_s_id_t  )
    ) u_dma (
      // Clock and reset signals
      .i_clk,
      .i_rst_n,
      // Control
      .o_int          ( dma_int[I]           ),
      .o_tok_prod_vld (                      ), // ASO-UNUSED_OUTPUT: pve doesn't use tokens
      .i_tok_prod_rdy ( dummy_i_tok_prod_rdy ),
      .i_tok_cons_vld ( dummy_i_tok_cons_vld ),
      .o_tok_cons_rdy (                      ), // ASO-UNUSED_OUTPUT: pve doesn't use tokens
      .o_ts_start     (                      ), // ASO-UNUSED_OUTPUT: pve doesn't use ts_start
      .o_ts_end       (                      ), // ASO-UNUSED_OUTPUT: pve doesn't use ts_end
      .o_acd_sync     (                      ), // ASO-UNUSED_OUTPUT: pve doesn't use acd_sync
      .o_obs          (                      ), // ASO-UNUSED_OUTPUT: pve doesn't use observation signals
      // AXI 4 Configuration Interface
      // AXI write address channel
      .i_axi_s_awvalid( dma_conf_axi_awvalid[I] ),
      .i_axi_s_awaddr ( dma_conf_axi_awaddr [I] ),
      .i_axi_s_awid   ( dma_conf_axi_awid   [I] ),
      .i_axi_s_awlen  ( dma_conf_axi_awlen  [I] ),
      .i_axi_s_awsize ( dma_conf_axi_awsize [I] ),
      .i_axi_s_awburst( dma_conf_axi_awburst[I] ),
      .i_axi_s_awlock ( dma_conf_axi_awlock [I] ),
      .i_axi_s_awcache( dma_conf_axi_awcache[I] ),
      .i_axi_s_awprot ( dma_conf_axi_awprot [I] ),
      .o_axi_s_awready( dma_conf_axi_awready[I] ),
      // AXI write data channel
      .i_axi_s_wvalid ( dma_conf_axi_wvalid [I] ),
      .i_axi_s_wlast  ( dma_conf_axi_wlast  [I] ),
      .i_axi_s_wdata  ( dma_conf_axi_wdata  [I] ),
      .i_axi_s_wstrb  ( dma_conf_axi_wstrb  [I] ),
      .o_axi_s_wready ( dma_conf_axi_wready [I] ),
      // AXI write response channel
      .o_axi_s_bvalid ( dma_conf_axi_bvalid [I] ),
      .o_axi_s_bid    ( dma_conf_axi_bid    [I] ),
      .o_axi_s_bresp  ( dma_conf_axi_bresp  [I] ),
      .i_axi_s_bready ( dma_conf_axi_bready [I] ),
      // AXI read address channel
      .i_axi_s_arvalid( dma_conf_axi_arvalid[I] ),
      .i_axi_s_araddr ( dma_conf_axi_araddr [I] ),
      .i_axi_s_arid   ( dma_conf_axi_arid   [I] ),
      .i_axi_s_arlen  ( dma_conf_axi_arlen  [I] ),
      .i_axi_s_arsize ( dma_conf_axi_arsize [I] ),
      .i_axi_s_arburst( dma_conf_axi_arburst[I] ),
      .i_axi_s_arlock ( dma_conf_axi_arlock [I] ),
      .i_axi_s_arcache( dma_conf_axi_arcache[I] ),
      .i_axi_s_arprot ( dma_conf_axi_arprot [I] ),
      .o_axi_s_arready( dma_conf_axi_arready[I] ),
      // AXI read data/response channel
      .o_axi_s_rvalid ( dma_conf_axi_rvalid [I] ),
      .o_axi_s_rlast  ( dma_conf_axi_rlast  [I] ),
      .o_axi_s_rid    ( dma_conf_axi_rid    [I] ),
      .o_axi_s_rdata  ( dma_conf_axi_rdata  [I] ),
      .o_axi_s_rresp  ( dma_conf_axi_rresp  [I] ),
      .i_axi_s_rready ( dma_conf_axi_rready [I] ),
      // AXI 4 Data Ports
      // AXI write address channel
      .o_axi_m_awvalid( ht_axi_s_awvalid[PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_awaddr ( ht_axi_s_awaddr [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_awid   ( ht_axi_s_awid   [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_awlen  ( ht_axi_s_awlen  [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_awsize ( ht_axi_s_awsize [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_awburst( ht_axi_s_awburst[PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_awlock ( ht_axi_s_awlock [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_awcache( ht_axi_s_awcache[PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_awprot ( ht_axi_s_awprot [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .i_axi_m_awready( ht_axi_s_awready[PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      // AXI write data channel
      .o_axi_m_wvalid ( ht_axi_s_wvalid [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_wlast  ( ht_axi_s_wlast  [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_wdata  ( ht_axi_s_wdata  [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_wstrb  ( ht_axi_s_wstrb  [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .i_axi_m_wready ( ht_axi_s_wready [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      // AXI write response channel
      .i_axi_m_bvalid ( ht_axi_s_bvalid [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .i_axi_m_bid    ( ht_axi_s_bid    [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .i_axi_m_bresp  ( ht_axi_s_bresp  [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_bready ( ht_axi_s_bready [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      // AXI read address channel
      .o_axi_m_arvalid( ht_axi_s_arvalid[PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_araddr ( ht_axi_s_araddr [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_arid   ( ht_axi_s_arid   [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_arlen  ( ht_axi_s_arlen  [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_arsize ( ht_axi_s_arsize [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_arburst( ht_axi_s_arburst[PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_arlock ( ht_axi_s_arlock [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_arcache( ht_axi_s_arcache[PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_arprot ( ht_axi_s_arprot [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .i_axi_m_arready( ht_axi_s_arready[PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      // AXI read data/response channel
      .i_axi_m_rvalid ( ht_axi_s_rvalid [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .i_axi_m_rlast  ( ht_axi_s_rlast  [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .i_axi_m_rid    ( ht_axi_s_rid    [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .i_axi_m_rdata  ( ht_axi_s_rdata  [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .i_axi_m_rresp  ( ht_axi_s_rresp  [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      .o_axi_m_rready ( ht_axi_s_rready [PVE_HT_S_PRTIDX_DMA0PRT0 + PVE_N_DMA_PORTS * I +: PVE_N_DMA_PORTS] ),
      // SRAM Sidebands
      .i_impl         ( sram_impl_inp   [I] ),
      .o_impl         ( sram_impl_oup   [I] )
    );
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) begin
        dma_int_q[I]                                         <= '0;
        dma_combined_int[I*PVE_N_DMA_CHNLS+:PVE_N_DMA_CHNLS] <= '0;
      end else begin
        dma_int_q[I]                                         <= dma_int[I];
        dma_combined_int[I*PVE_N_DMA_CHNLS+:PVE_N_DMA_CHNLS] <= dma_int_q[I];
      end
    end
  end: g_dma

  // SPM
  // Memory math:
  //  = Using 2k deep memory, with 8 Bytes per line = 16KiB per SRAM
  //  - To reach 256KiB we need 256/16 = 16 SRAM instances
  //  - Total number of instances = NB_BANKS * NB_SUB_BANKS * NB_MINI_BANKS * NB_SRAMS_PER_MINI_BANK
  spm #(
    .SPM_MEM_SIZE_KB      ( 256 ),
    .SPM_MEM_MACRO_DEPTH_K( 2   ),

    .SPM_NB_BANKS              ( 2 ),
    .SPM_NB_SUB_BANKS          ( 2 ),
    .SPM_NB_MINI_BANKS         ( 2 ),
    .SPM_NB_SRAMS_PER_MINI_BANK( 2 ),
    .SPM_NB_REQ_PIPELINE       ( 1 ),
    .SPM_NB_RSP_PIPELINE       ( 1 ),

    .ECC_PROTECTION_EN         ( 1 ),
    .EN_ATOMIC_SUPPORT         ( 1 ),
    .spm_axi_data_t   ( chip_axi_lt_data_t  ),
    .spm_axi_addr_t   ( spm_addr_t          ),
    .spm_axi_strb_t   ( chip_axi_lt_wstrb_t ),
    .spm_axi_len_t    ( axi_len_t           ),
    .spm_axi_id_t     ( pve_lt_axi_m_id_t   ),
    .spm_axi_size_t   ( axi_size_e          ),
    .spm_axi_burst_t  ( axi_burst_e         ),
    .spm_axi_cache_t  ( axi_cache_e         ),
    .spm_axi_prot_t   ( axi_prot_t          )
  ) u_spm (
    // Clock and reset signals
    .i_clk,
    .i_rst_n,
    // AXI write address channel
    .i_axi_s_awvalid           ( lt_axi_m_awvalid  [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_awaddr            ( lt_axi_m_awaddr   [PVE_LT_M_PRTIDX_SPM][PVE_TGT_SPM_MMAP_W-1:0] ),
    .i_axi_s_awid              ( lt_axi_m_awid     [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_awlen             ( lt_axi_m_awlen    [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_awsize            ( lt_axi_m_awsize   [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_awburst           ( lt_axi_m_awburst  [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_awlock            ( lt_axi_m_awlock   [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_awcache           ( lt_axi_m_awcache  [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_awprot            ( lt_axi_m_awprot   [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_awatop            ( lt_axi_m_awatop   [PVE_LT_M_PRTIDX_SPM] ),
    .o_axi_s_awready           ( lt_axi_m_awready  [PVE_LT_M_PRTIDX_SPM] ),
    // AXI write data channel
    .i_axi_s_wvalid            ( lt_axi_m_wvalid   [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_wlast             ( lt_axi_m_wlast    [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_wdata             ( lt_axi_m_wdata    [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_wstrb             ( lt_axi_m_wstrb    [PVE_LT_M_PRTIDX_SPM] ),
    .o_axi_s_wready            ( lt_axi_m_wready   [PVE_LT_M_PRTIDX_SPM] ),
    // AXI write response channel
    .o_axi_s_bvalid            ( lt_axi_m_bvalid   [PVE_LT_M_PRTIDX_SPM] ),
    .o_axi_s_bid               ( lt_axi_m_bid      [PVE_LT_M_PRTIDX_SPM] ),
    .o_axi_s_bresp             ( lt_axi_m_bresp    [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_bready            ( lt_axi_m_bready   [PVE_LT_M_PRTIDX_SPM] ),
    // AXI read address channel
    .i_axi_s_arvalid           ( lt_axi_m_arvalid  [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_araddr            ( lt_axi_m_araddr   [PVE_LT_M_PRTIDX_SPM][PVE_TGT_SPM_MMAP_W-1:0] ),
    .i_axi_s_arid              ( lt_axi_m_arid     [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_arlen             ( lt_axi_m_arlen    [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_arsize            ( lt_axi_m_arsize   [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_arburst           ( lt_axi_m_arburst  [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_arlock            ( lt_axi_m_arlock   [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_arcache           ( lt_axi_m_arcache  [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_arprot            ( lt_axi_m_arprot   [PVE_LT_M_PRTIDX_SPM] ),
    .o_axi_s_arready           ( lt_axi_m_arready  [PVE_LT_M_PRTIDX_SPM] ),
    // AXI read data/response channel
    .o_axi_s_rvalid            ( lt_axi_m_rvalid   [PVE_LT_M_PRTIDX_SPM] ),
    .o_axi_s_rlast             ( lt_axi_m_rlast    [PVE_LT_M_PRTIDX_SPM] ),
    .o_axi_s_rid               ( lt_axi_m_rid      [PVE_LT_M_PRTIDX_SPM] ),
    .o_axi_s_rdata             ( lt_axi_m_rdata    [PVE_LT_M_PRTIDX_SPM] ),
    .o_axi_s_rresp             ( lt_axi_m_rresp    [PVE_LT_M_PRTIDX_SPM] ),
    .i_axi_s_rready            ( lt_axi_m_rready   [PVE_LT_M_PRTIDX_SPM] ),

    .i_scp_ecc_disable         ( '0                                      ),
    .o_scp_error_status        (                                         ), // ASO-UNUSED_OUTPUT: pve doesn't use scp_error_status
    .o_irq                     (                                         ), // ASO-UNUSED_OUTPUT: pve doesn't use SPM error irq
    .o_spm_obs                 (                                         ), // ASO-UNUSED_OUTPUT: pve doesn't use SPM internal observation signals
    .i_impl                    ( sram_impl_inp[PVE_N_DMA]                ),
    .o_impl                    ( sram_impl_oup[PVE_N_DMA]                )
  );

  // CLINT
  clint_lt_req_t clint_axi_req;
  clint_lt_rsp_t clint_axi_resp;
  logic [PVE_N_CPU-1:0] clint_timer_irq;
  logic [PVE_N_CPU-1:0] clint_timer_irq_q;
  logic [PVE_N_CPU-1:0] clint_timer_irq_q2;
  logic [PVE_N_CPU-1:0] clint_timer_irq_q3;
  logic [PVE_N_CPU-1:0] clint_ipi;
  logic [PVE_N_CPU-1:0] clint_ipi_q;
  logic [PVE_N_CPU-1:0] clint_ipi_q2;
  logic [PVE_N_CPU-1:0] clint_ipi_q3;

  // Request
  always_comb clint_axi_req.aw_valid  = lt_axi_m_awvalid[PVE_LT_M_PRTIDX_CLINT];
  always_comb clint_axi_req.aw.id     = lt_axi_m_awid   [PVE_LT_M_PRTIDX_CLINT];
  always_comb clint_axi_req.aw.addr   = lt_axi_m_awaddr [PVE_LT_M_PRTIDX_CLINT];
  always_comb clint_axi_req.aw.len    = lt_axi_m_awlen  [PVE_LT_M_PRTIDX_CLINT];

  always_comb clint_axi_req.w_valid   = lt_axi_m_wvalid [PVE_LT_M_PRTIDX_CLINT];
  always_comb clint_axi_req.w.data    = lt_axi_m_wdata  [PVE_LT_M_PRTIDX_CLINT];
  always_comb clint_axi_req.w.strb    = lt_axi_m_wstrb  [PVE_LT_M_PRTIDX_CLINT];
  always_comb clint_axi_req.w.last    = lt_axi_m_wlast  [PVE_LT_M_PRTIDX_CLINT];

  always_comb clint_axi_req.b_ready   = lt_axi_m_bready [PVE_LT_M_PRTIDX_CLINT];

  always_comb clint_axi_req.ar_valid  = lt_axi_m_arvalid[PVE_LT_M_PRTIDX_CLINT];
  always_comb clint_axi_req.ar.id     = lt_axi_m_arid   [PVE_LT_M_PRTIDX_CLINT];
  always_comb clint_axi_req.ar.addr   = lt_axi_m_araddr [PVE_LT_M_PRTIDX_CLINT];
  always_comb clint_axi_req.ar.len    = lt_axi_m_arlen  [PVE_LT_M_PRTIDX_CLINT];

  always_comb clint_axi_req.r_ready   = lt_axi_m_rready [PVE_LT_M_PRTIDX_CLINT];

  // Response
  always_comb lt_axi_m_awready[PVE_LT_M_PRTIDX_CLINT] = clint_axi_resp.aw_ready;
  always_comb lt_axi_m_arready[PVE_LT_M_PRTIDX_CLINT] = clint_axi_resp.ar_ready;

  always_comb lt_axi_m_wready [PVE_LT_M_PRTIDX_CLINT] = clint_axi_resp.w_ready;

  always_comb lt_axi_m_bvalid [PVE_LT_M_PRTIDX_CLINT] = clint_axi_resp.b_valid;
  always_comb lt_axi_m_bid    [PVE_LT_M_PRTIDX_CLINT] = clint_axi_resp.b.id;
  always_comb lt_axi_m_bresp  [PVE_LT_M_PRTIDX_CLINT] = axi_resp_e'(clint_axi_resp.b.resp);

  always_comb lt_axi_m_rvalid [PVE_LT_M_PRTIDX_CLINT] = clint_axi_resp.r_valid;
  always_comb lt_axi_m_rid    [PVE_LT_M_PRTIDX_CLINT] = clint_axi_resp.r.id;
  always_comb lt_axi_m_rdata  [PVE_LT_M_PRTIDX_CLINT] = clint_axi_resp.r.data;
  always_comb lt_axi_m_rresp  [PVE_LT_M_PRTIDX_CLINT] = axi_resp_e'(clint_axi_resp.r.resp);
  always_comb lt_axi_m_rlast  [PVE_LT_M_PRTIDX_CLINT] = clint_axi_resp.r.last;

  gc_clint #(
    .AxiAddrWidth(CHIP_AXI_ADDR_W   ),
    .AxiDataWidth(CHIP_AXI_LT_DATA_W),
    .AxiIdWidth  (PVE_LT_M_ID_W     ),
    .NrHarts     (PVE_N_CPU         ), // Number of cores therefore also the number of timecmp registers and timer interrupts
    .axi_req_t   (clint_lt_req_t    ),
    .axi_resp_t  (clint_lt_rsp_t    )
  ) u_clint (
    .clk_i      (i_clk          ),
    .rst_ni     (i_rst_n        ),
    .axi_req_i  (clint_axi_req  ),
    .axi_resp_o (clint_axi_resp ),
    .timer_irq_o(clint_timer_irq),     // Timer interrupts
    .ipi_o      (clint_ipi      )      // software interrupt (a.k.a inter-process-interrupt)
  );
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      clint_ipi_q        <= '0;
      clint_ipi_q2       <= '0;
      clint_ipi_q3       <= '0;
      clint_timer_irq_q  <= '0;
      clint_timer_irq_q2 <= '0;
      clint_timer_irq_q3 <= '0;
    end else begin
      clint_ipi_q        <= clint_ipi;
      clint_ipi_q2       <= clint_ipi_q;
      clint_ipi_q3       <= clint_ipi_q2;
      clint_timer_irq_q  <= clint_timer_irq;
      clint_timer_irq_q2 <= clint_timer_irq_q;
      clint_timer_irq_q3 <= clint_timer_irq_q2;
    end
  end
  for (genvar I = 0; I < PVE_N_CLUSTERS; I++) begin: g_clint0
    for (genvar J = 0; J < PVE_CLUSTER_N_CPU; J++) begin: g_clint1
      always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
          ipi[I][J]      <= 1'b0;
          time_irq[I][J] <= 1'b0;
        end else begin
          ipi[I][J]      <= clint_ipi_q3      [I*PVE_CLUSTER_N_CPU+J];
          time_irq[I][J] <= clint_timer_irq_q3[I*PVE_CLUSTER_N_CPU+J];
        end
      end
    end
  end

  // PERF COUNTERS
  perfc_lt_req_t perfc_axi_req;
  perfc_lt_rsp_t perfc_axi_resp;

  // AXI request and response
  pve_axi_multistage_spill_reg #(
    .NUM_STAGES_AW(1                  ),
    .NUM_STAGES_W (1                  ),
    .NUM_STAGES_B (1                  ),
    .NUM_STAGES_AR(1                  ),
    .NUM_STAGES_R (1                  ),
    .axi_addr_t   (chip_axi_addr_t    ),
    .axi_id_t     (pve_lt_axi_m_id_t  ),
    .axi_data_t   (chip_axi_lt_data_t ),
    .axi_strb_t   (chip_axi_lt_wstrb_t)
  ) u_perfc_spill_reg (
    .i_clk,
    .i_rst_n,
    // Subordinate side
    // AXI write address channel
    .i_axi_s_awvalid(lt_axi_m_awvalid[PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_awid   (lt_axi_m_awid   [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_awaddr (lt_axi_m_awaddr [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_awlen  (lt_axi_m_awlen  [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_awsize (lt_axi_m_awsize [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_awburst(lt_axi_m_awburst[PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_awlock (lt_axi_m_awlock [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_awcache(lt_axi_m_awcache[PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_awprot (lt_axi_m_awprot [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_awatop (lt_axi_m_awatop [PVE_LT_M_PRTIDX_PERFC]),
    .o_axi_s_awready(lt_axi_m_awready[PVE_LT_M_PRTIDX_PERFC]),
    // AXI write data channel
    .i_axi_s_wvalid (lt_axi_m_wvalid [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_wdata  (lt_axi_m_wdata  [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_wstrb  (lt_axi_m_wstrb  [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_wlast  (lt_axi_m_wlast  [PVE_LT_M_PRTIDX_PERFC]),
    .o_axi_s_wready (lt_axi_m_wready [PVE_LT_M_PRTIDX_PERFC]),
    // AXI write response channel
    .o_axi_s_bvalid (lt_axi_m_bvalid [PVE_LT_M_PRTIDX_PERFC]),
    .o_axi_s_bid    (lt_axi_m_bid    [PVE_LT_M_PRTIDX_PERFC]),
    .o_axi_s_bresp  (lt_axi_m_bresp  [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_bready (lt_axi_m_bready [PVE_LT_M_PRTIDX_PERFC]),
    // AXI read address channel
    .i_axi_s_arvalid(lt_axi_m_arvalid[PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_arid   (lt_axi_m_arid   [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_araddr (lt_axi_m_araddr [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_arlen  (lt_axi_m_arlen  [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_arsize (lt_axi_m_arsize [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_arburst(lt_axi_m_arburst[PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_arlock (lt_axi_m_arlock [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_arcache(lt_axi_m_arcache[PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_arprot (lt_axi_m_arprot [PVE_LT_M_PRTIDX_PERFC]),
    .o_axi_s_arready(lt_axi_m_arready[PVE_LT_M_PRTIDX_PERFC]),
    // AXI read data/response channel
    .o_axi_s_rvalid (lt_axi_m_rvalid [PVE_LT_M_PRTIDX_PERFC]),
    .o_axi_s_rid    (lt_axi_m_rid    [PVE_LT_M_PRTIDX_PERFC]),
    .o_axi_s_rdata  (lt_axi_m_rdata  [PVE_LT_M_PRTIDX_PERFC]),
    .o_axi_s_rresp  (lt_axi_m_rresp  [PVE_LT_M_PRTIDX_PERFC]),
    .o_axi_s_rlast  (lt_axi_m_rlast  [PVE_LT_M_PRTIDX_PERFC]),
    .i_axi_s_rready (lt_axi_m_rready [PVE_LT_M_PRTIDX_PERFC]),
    // Manager Ports
    // AXI write address channel
    .o_axi_m_awvalid(perfc_axi_req.aw_valid ),
    .o_axi_m_awid   (perfc_axi_req.aw.id    ),
    .o_axi_m_awaddr (perfc_axi_req.aw.addr  ),
    .o_axi_m_awlen  (perfc_axi_req.aw.len   ),
    .o_axi_m_awsize (perfc_axi_req.aw.size  ),
    .o_axi_m_awburst(perfc_axi_req.aw.burst ),
    .o_axi_m_awlock (perfc_axi_req.aw.lock  ),
    .o_axi_m_awcache(perfc_axi_req.aw.cache ),
    .o_axi_m_awprot (perfc_axi_req.aw.prot  ),
    .o_axi_m_awatop (perfc_axi_req.aw.atop  ),
    .i_axi_m_awready(perfc_axi_resp.aw_ready),
    // AXI write data channel
    .o_axi_m_wvalid (perfc_axi_req.w_valid  ),
    .o_axi_m_wdata  (perfc_axi_req.w.data   ),
    .o_axi_m_wstrb  (perfc_axi_req.w.strb   ),
    .o_axi_m_wlast  (perfc_axi_req.w.last   ),
    .i_axi_m_wready (perfc_axi_resp.w_ready ),
    // AXI write response channel
    .i_axi_m_bvalid (perfc_axi_resp.b_valid ),
    .i_axi_m_bid    (perfc_axi_resp.b.id    ),
    .i_axi_m_bresp  (perfc_axi_resp.b.resp  ),
    .o_axi_m_bready (perfc_axi_req.b_ready  ),
    // AXI read address channel
    .o_axi_m_arvalid(perfc_axi_req.ar_valid ),
    .o_axi_m_arid   (perfc_axi_req.ar.id    ),
    .o_axi_m_araddr (perfc_axi_req.ar.addr  ),
    .o_axi_m_arlen  (perfc_axi_req.ar.len   ),
    .o_axi_m_arsize (perfc_axi_req.ar.size  ),
    .o_axi_m_arburst(perfc_axi_req.ar.burst ),
    .o_axi_m_arlock (perfc_axi_req.ar.lock  ),
    .o_axi_m_arcache(perfc_axi_req.ar.cache ),
    .o_axi_m_arprot (perfc_axi_req.ar.prot  ),
    .i_axi_m_arready(perfc_axi_resp.ar_ready),
    // AXI read data/response channel
    .i_axi_m_rvalid (perfc_axi_resp.r_valid ),
    .i_axi_m_rid    (perfc_axi_resp.r.id    ),
    .i_axi_m_rdata  (perfc_axi_resp.r.data  ),
    .i_axi_m_rresp  (perfc_axi_resp.r.resp  ),
    .i_axi_m_rlast  (perfc_axi_resp.r.last  ),
    .o_axi_m_rready (perfc_axi_req.r_ready  )
  );

  always_comb perfc_axi_req.aw.qos    = '0;
  always_comb perfc_axi_req.aw.region = '0;
  always_comb perfc_axi_req.aw.user   = '0;

  always_comb perfc_axi_req.w.user    = '0;

  always_comb perfc_axi_req.ar.qos    = '0;
  always_comb perfc_axi_req.ar.region = '0;
  always_comb perfc_axi_req.ar.user   = '0;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      perf_cntr_fu_status_q             <= '0;
      perf_cntr_fu_status_q2            <= '0;
      perf_cntr_dispatch_queue_full_q   <= '0;
      perf_cntr_dispatch_queue_full_q2  <= '0;
      perf_cntr_dispatch_queue_empty_q  <= '0;
      perf_cntr_dispatch_queue_empty_q2 <= '0;
      perf_cntr_commit_queue_full_q     <= '0;
      perf_cntr_commit_queue_full_q2    <= '0;
      perf_cntr_commit_queue_empty_q    <= '0;
      perf_cntr_commit_queue_empty_q2   <= '0;
      perf_event_addr_q                 <= '0;
      perf_event_addr_q2                <= '0;
      perf_event_deltas_q               <= '0;
      perf_event_deltas_q2              <= '0;
    end else begin
      perf_cntr_fu_status_q             <= perf_cntr_fu_status;
      perf_cntr_fu_status_q2            <= perf_cntr_fu_status_q;
      perf_cntr_dispatch_queue_full_q   <= perf_cntr_dispatch_queue_full;
      perf_cntr_dispatch_queue_full_q2  <= perf_cntr_dispatch_queue_full_q;
      perf_cntr_dispatch_queue_empty_q  <= perf_cntr_dispatch_queue_empty;
      perf_cntr_dispatch_queue_empty_q2 <= perf_cntr_dispatch_queue_empty_q;
      perf_cntr_commit_queue_full_q     <= perf_cntr_commit_queue_full;
      perf_cntr_commit_queue_full_q2    <= perf_cntr_commit_queue_full_q;
      perf_cntr_commit_queue_empty_q    <= perf_cntr_commit_queue_empty;
      perf_cntr_commit_queue_empty_q2   <= perf_cntr_commit_queue_empty_q;
      perf_event_addr_q                 <= perf_event_addr;
      perf_event_addr_q2                <= perf_event_addr_q;
      perf_event_deltas_q               <= perf_event_deltas;
      perf_event_deltas_q2              <= perf_event_deltas_q;
    end
  end

  for (genvar I = 0; I < PVE_N_CPU; I++) begin: g_ncpu
    if (I < 2 || I >= 6) begin: g_core03_sel
      always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
          perf_cntr_fu_status_q3[I]            <= '0;
          perf_cntr_dispatch_queue_full_q3[I]  <= 1'b0;
          perf_cntr_dispatch_queue_empty_q3[I] <= 1'b0;
          perf_cntr_commit_queue_full_q3[I]    <= 1'b0;
          perf_cntr_commit_queue_empty_q3[I]   <= 1'b0;
          perf_event_addr_q3[I]                <= '0;
          perf_event_deltas_q3[I]              <= '0;
        end else begin
          perf_cntr_fu_status_q3[I]            <= perf_cntr_fu_status_q2[I];
          perf_cntr_dispatch_queue_full_q3[I]  <= perf_cntr_dispatch_queue_full_q2[I];
          perf_cntr_dispatch_queue_empty_q3[I] <= perf_cntr_dispatch_queue_empty_q2[I];
          perf_cntr_commit_queue_full_q3[I]    <= perf_cntr_commit_queue_full_q2[I];
          perf_cntr_commit_queue_empty_q3[I]   <= perf_cntr_commit_queue_empty_q2[I];
          perf_event_addr_q3[I]                <= perf_event_addr_q2[I];
          perf_event_deltas_q3[I]              <= perf_event_deltas_q2[I];
        end
      end
    end else begin: g_core12_sel
      always_comb perf_cntr_fu_status_q3[I]            = perf_cntr_fu_status_q2[I];
      always_comb perf_cntr_dispatch_queue_full_q3[I]  = perf_cntr_dispatch_queue_full_q2[I];
      always_comb perf_cntr_dispatch_queue_empty_q3[I] = perf_cntr_dispatch_queue_empty_q2[I];
      always_comb perf_cntr_commit_queue_full_q3[I]    = perf_cntr_commit_queue_full_q2[I];
      always_comb perf_cntr_commit_queue_empty_q3[I]   = perf_cntr_commit_queue_empty_q2[I];
      always_comb perf_event_addr_q3[I]                = perf_event_addr_q2[I];
      always_comb perf_event_deltas_q3[I]              = perf_event_deltas_q2[I];
    end
  end
  cva6v_perf_counters_top #(
    .NrHarts       (PVE_N_CPU                    ), // Number of cores
    .EventCount    (cva6v_pve_pkg::PerfEventCount),
    .CntrWidth     (32                           ),
    .AxiAddrWidth  (CHIP_AXI_ADDR_W              ),
    .AxiDataWidth  (CHIP_AXI_LT_DATA_W           ),
    .AxiIdWidth    (PVE_LT_M_ID_W                ),
    .AxiUserWidth  (1                            ),
    .axi_req_t     (perfc_lt_req_t               ),
    .axi_rsp_t     (perfc_lt_rsp_t               ),
    .cva6v_config_t(cva6v_pkg::cva6v_config_t    ),
    .CVA6VConfig   (cva6v_pve_pkg::CVA6VConfig   ),
    .L1Latency     (10                           )
  ) u_perf_counters (
    .clk_i                       (i_clk                            ),
    .rst_ni                      (i_rst_n                          ),
    .axi_req_i                   (perfc_axi_req                    ),
    .axi_rsp_o                   (perfc_axi_resp                   ),
    .trace_fu_status_i           (perf_cntr_fu_status_q3           ),
    .trace_dispatch_queue_full_i (perf_cntr_dispatch_queue_full_q3 ),
    .trace_dispatch_queue_empty_i(perf_cntr_dispatch_queue_empty_q3),
    .trace_commit_queue_full_i   (perf_cntr_commit_queue_full_q3   ),
    .trace_commit_queue_empty_i  (perf_cntr_commit_queue_empty_q3  ),
    .trace_instr_entry_addr_i    (perf_event_addr_q3               ),
    .trace_instr_event_delta_i   (perf_event_deltas_q3             )
  );

endmodule
