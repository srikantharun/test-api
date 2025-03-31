// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>
//        Matt Morris <matt.morris@axelera.ai>

// PVE Fabric

module pve_fabric
  import chip_pkg::*;
  import axi_pkg::*;
  import pve_pkg::*;
(
  input  wire i_clk,
  input  wire i_rst_n,

  // Config
  input chip_axi_addr_t i_base_addr,

  // LT INTERFACES

  // Subordinates
  // AW
  input  logic               i_lt_axi_s_awvalid [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  pve_lt_axi_s_id_t   i_lt_axi_s_awid    [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  chip_axi_addr_t     i_lt_axi_s_awaddr  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_len_t           i_lt_axi_s_awlen   [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_size_e          i_lt_axi_s_awsize  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_burst_e         i_lt_axi_s_awburst [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  logic               i_lt_axi_s_awlock  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_cache_e         i_lt_axi_s_awcache [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_prot_t          i_lt_axi_s_awprot  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_atop_t          i_lt_axi_s_awatop  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  output logic               o_lt_axi_s_awready [PVE_FABRIC_N_LT_S_EXT_PORTS],
  // W
  input  logic               i_lt_axi_s_wvalid  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  chip_axi_lt_data_t  i_lt_axi_s_wdata   [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  chip_axi_lt_wstrb_t i_lt_axi_s_wstrb   [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  logic               i_lt_axi_s_wlast   [PVE_FABRIC_N_LT_S_EXT_PORTS],
  output logic               o_lt_axi_s_wready  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  // B
  output logic               o_lt_axi_s_bvalid  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  output pve_lt_axi_s_id_t   o_lt_axi_s_bid     [PVE_FABRIC_N_LT_S_EXT_PORTS],
  output axi_resp_e          o_lt_axi_s_bresp   [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  logic               i_lt_axi_s_bready  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  // AR
  input  logic               i_lt_axi_s_arvalid [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  pve_lt_axi_s_id_t   i_lt_axi_s_arid    [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  chip_axi_addr_t     i_lt_axi_s_araddr  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_len_t           i_lt_axi_s_arlen   [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_size_e          i_lt_axi_s_arsize  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_burst_e         i_lt_axi_s_arburst [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  logic               i_lt_axi_s_arlock  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_cache_e         i_lt_axi_s_arcache [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  axi_prot_t          i_lt_axi_s_arprot  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  output logic               o_lt_axi_s_arready [PVE_FABRIC_N_LT_S_EXT_PORTS],
  // R
  output logic               o_lt_axi_s_rvalid  [PVE_FABRIC_N_LT_S_EXT_PORTS],
  output pve_lt_axi_s_id_t   o_lt_axi_s_rid     [PVE_FABRIC_N_LT_S_EXT_PORTS],
  output chip_axi_lt_data_t  o_lt_axi_s_rdata   [PVE_FABRIC_N_LT_S_EXT_PORTS],
  output axi_resp_e          o_lt_axi_s_rresp   [PVE_FABRIC_N_LT_S_EXT_PORTS],
  output logic               o_lt_axi_s_rlast   [PVE_FABRIC_N_LT_S_EXT_PORTS],
  input  logic               i_lt_axi_s_rready  [PVE_FABRIC_N_LT_S_EXT_PORTS],

  // Managers
  // AW
  output logic               o_lt_axi_m_awvalid [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output pve_lt_axi_m_id_t   o_lt_axi_m_awid    [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output chip_axi_addr_t     o_lt_axi_m_awaddr  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_len_t           o_lt_axi_m_awlen   [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_size_e          o_lt_axi_m_awsize  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_burst_e         o_lt_axi_m_awburst [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output logic               o_lt_axi_m_awlock  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_cache_e         o_lt_axi_m_awcache [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_prot_t          o_lt_axi_m_awprot  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_atop_t          o_lt_axi_m_awatop  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  input  logic               i_lt_axi_m_awready [PVE_FABRIC_N_LT_M_EXT_PORTS],
  // W
  output logic               o_lt_axi_m_wvalid  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output chip_axi_lt_data_t  o_lt_axi_m_wdata   [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output chip_axi_lt_wstrb_t o_lt_axi_m_wstrb   [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output logic               o_lt_axi_m_wlast   [PVE_FABRIC_N_LT_M_EXT_PORTS],
  input  logic               i_lt_axi_m_wready  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  // B
  input  logic               i_lt_axi_m_bvalid  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  input  pve_lt_axi_m_id_t   i_lt_axi_m_bid     [PVE_FABRIC_N_LT_M_EXT_PORTS],
  input  axi_resp_e          i_lt_axi_m_bresp   [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output logic               o_lt_axi_m_bready  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  // AR
  output logic               o_lt_axi_m_arvalid [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output pve_lt_axi_m_id_t   o_lt_axi_m_arid    [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output chip_axi_addr_t     o_lt_axi_m_araddr  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_len_t           o_lt_axi_m_arlen   [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_size_e          o_lt_axi_m_arsize  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_burst_e         o_lt_axi_m_arburst [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output logic               o_lt_axi_m_arlock  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_cache_e         o_lt_axi_m_arcache [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output axi_prot_t          o_lt_axi_m_arprot  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  input  logic               i_lt_axi_m_arready [PVE_FABRIC_N_LT_M_EXT_PORTS],
  // R
  input  logic               i_lt_axi_m_rvalid  [PVE_FABRIC_N_LT_M_EXT_PORTS],
  input  pve_lt_axi_m_id_t   i_lt_axi_m_rid     [PVE_FABRIC_N_LT_M_EXT_PORTS],
  input  chip_axi_lt_data_t  i_lt_axi_m_rdata   [PVE_FABRIC_N_LT_M_EXT_PORTS],
  input  axi_resp_e          i_lt_axi_m_rresp   [PVE_FABRIC_N_LT_M_EXT_PORTS],
  input  logic               i_lt_axi_m_rlast   [PVE_FABRIC_N_LT_M_EXT_PORTS],
  output logic               o_lt_axi_m_rready  [PVE_FABRIC_N_LT_M_EXT_PORTS],

  // HT INTERFACES

  // Subordinates
  // AW
  input  logic               i_ht_axi_s_awvalid [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  pve_ht_axi_s_id_t   i_ht_axi_s_awid    [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  chip_axi_addr_t     i_ht_axi_s_awaddr  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_len_t           i_ht_axi_s_awlen   [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_size_e          i_ht_axi_s_awsize  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_burst_e         i_ht_axi_s_awburst [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  logic               i_ht_axi_s_awlock  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_cache_e         i_ht_axi_s_awcache [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_prot_t          i_ht_axi_s_awprot  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_atop_t          i_ht_axi_s_awatop  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  output logic               o_ht_axi_s_awready [PVE_FABRIC_N_HT_S_EXT_PORTS],
  // W
  input  logic               i_ht_axi_s_wvalid  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  chip_axi_ht_data_t  i_ht_axi_s_wdata   [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  chip_axi_ht_wstrb_t i_ht_axi_s_wstrb   [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  logic               i_ht_axi_s_wlast   [PVE_FABRIC_N_HT_S_EXT_PORTS],
  output logic               o_ht_axi_s_wready  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  // B
  output logic               o_ht_axi_s_bvalid  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  output pve_ht_axi_s_id_t   o_ht_axi_s_bid     [PVE_FABRIC_N_HT_S_EXT_PORTS],
  output axi_resp_e          o_ht_axi_s_bresp   [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  logic               i_ht_axi_s_bready  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  // AR
  input  logic               i_ht_axi_s_arvalid [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  pve_ht_axi_s_id_t   i_ht_axi_s_arid    [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  chip_axi_addr_t     i_ht_axi_s_araddr  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_len_t           i_ht_axi_s_arlen   [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_size_e          i_ht_axi_s_arsize  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_burst_e         i_ht_axi_s_arburst [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  logic               i_ht_axi_s_arlock  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_cache_e         i_ht_axi_s_arcache [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  axi_prot_t          i_ht_axi_s_arprot  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  output logic               o_ht_axi_s_arready [PVE_FABRIC_N_HT_S_EXT_PORTS],
  // R
  output logic               o_ht_axi_s_rvalid  [PVE_FABRIC_N_HT_S_EXT_PORTS],
  output pve_ht_axi_s_id_t   o_ht_axi_s_rid     [PVE_FABRIC_N_HT_S_EXT_PORTS],
  output chip_axi_ht_data_t  o_ht_axi_s_rdata   [PVE_FABRIC_N_HT_S_EXT_PORTS],
  output axi_resp_e          o_ht_axi_s_rresp   [PVE_FABRIC_N_HT_S_EXT_PORTS],
  output logic               o_ht_axi_s_rlast   [PVE_FABRIC_N_HT_S_EXT_PORTS],
  input  logic               i_ht_axi_s_rready  [PVE_FABRIC_N_HT_S_EXT_PORTS],

  // Managers
  // AW
  output logic               o_ht_axi_m_awvalid [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output pve_ht_axi_m_id_t   o_ht_axi_m_awid    [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output chip_axi_addr_t     o_ht_axi_m_awaddr  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_len_t           o_ht_axi_m_awlen   [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_size_e          o_ht_axi_m_awsize  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_burst_e         o_ht_axi_m_awburst [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output logic               o_ht_axi_m_awlock  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_cache_e         o_ht_axi_m_awcache [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_prot_t          o_ht_axi_m_awprot  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  input  logic               i_ht_axi_m_awready [PVE_FABRIC_N_HT_M_EXT_PORTS],
  // W
  output logic               o_ht_axi_m_wvalid  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output chip_axi_ht_data_t  o_ht_axi_m_wdata   [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output chip_axi_ht_wstrb_t o_ht_axi_m_wstrb   [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output logic               o_ht_axi_m_wlast   [PVE_FABRIC_N_HT_M_EXT_PORTS],
  input  logic               i_ht_axi_m_wready  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  // B
  input  logic               i_ht_axi_m_bvalid  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  input  pve_ht_axi_m_id_t   i_ht_axi_m_bid     [PVE_FABRIC_N_HT_M_EXT_PORTS],
  input  axi_resp_e          i_ht_axi_m_bresp   [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output logic               o_ht_axi_m_bready  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  // AR
  output logic               o_ht_axi_m_arvalid [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output pve_ht_axi_m_id_t   o_ht_axi_m_arid    [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output chip_axi_addr_t     o_ht_axi_m_araddr  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_len_t           o_ht_axi_m_arlen   [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_size_e          o_ht_axi_m_arsize  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_burst_e         o_ht_axi_m_arburst [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output logic               o_ht_axi_m_arlock  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_cache_e         o_ht_axi_m_arcache [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output axi_prot_t          o_ht_axi_m_arprot  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  input  logic               i_ht_axi_m_arready [PVE_FABRIC_N_HT_M_EXT_PORTS],
  // R
  input  logic               i_ht_axi_m_rvalid  [PVE_FABRIC_N_HT_M_EXT_PORTS],
  input  pve_ht_axi_m_id_t   i_ht_axi_m_rid     [PVE_FABRIC_N_HT_M_EXT_PORTS],
  input  chip_axi_ht_data_t  i_ht_axi_m_rdata   [PVE_FABRIC_N_HT_M_EXT_PORTS],
  input  axi_resp_e          i_ht_axi_m_rresp   [PVE_FABRIC_N_HT_M_EXT_PORTS],
  input  logic               i_ht_axi_m_rlast   [PVE_FABRIC_N_HT_M_EXT_PORTS],
  output logic               o_ht_axi_m_rready  [PVE_FABRIC_N_HT_M_EXT_PORTS]
);

  logic pve_s_lt_awvalid[PVE_FABRIC_N_LT_S_PORTS];
  logic pve_s_lt_awready[PVE_FABRIC_N_LT_S_PORTS];
  logic pve_s_lt_wvalid [PVE_FABRIC_N_LT_S_PORTS];
  logic pve_s_lt_wready [PVE_FABRIC_N_LT_S_PORTS];
  logic pve_s_lt_bvalid [PVE_FABRIC_N_LT_S_PORTS];
  logic pve_s_lt_bready [PVE_FABRIC_N_LT_S_PORTS];
  logic pve_s_lt_arvalid[PVE_FABRIC_N_LT_S_PORTS];
  logic pve_s_lt_arready[PVE_FABRIC_N_LT_S_PORTS];
  logic pve_s_lt_rvalid [PVE_FABRIC_N_LT_S_PORTS];
  logic pve_s_lt_rready [PVE_FABRIC_N_LT_S_PORTS];

  pve_lt_s_aw_t pve_s_lt_aw[PVE_FABRIC_N_LT_S_PORTS];
  pve_lt_w_t    pve_s_lt_w [PVE_FABRIC_N_LT_S_PORTS];
  pve_lt_s_b_t  pve_s_lt_b [PVE_FABRIC_N_LT_S_PORTS];
  pve_lt_s_ar_t pve_s_lt_ar[PVE_FABRIC_N_LT_S_PORTS];
  pve_lt_s_r_t  pve_s_lt_r [PVE_FABRIC_N_LT_S_PORTS];

  logic pve_m_lt_awvalid[PVE_FABRIC_N_LT_M_PORTS];
  logic pve_m_lt_awready[PVE_FABRIC_N_LT_M_PORTS];
  logic pve_m_lt_wvalid [PVE_FABRIC_N_LT_M_PORTS];
  logic pve_m_lt_wready [PVE_FABRIC_N_LT_M_PORTS];
  logic pve_m_lt_bvalid [PVE_FABRIC_N_LT_M_PORTS];
  logic pve_m_lt_bready [PVE_FABRIC_N_LT_M_PORTS];
  logic pve_m_lt_arvalid[PVE_FABRIC_N_LT_M_PORTS];
  logic pve_m_lt_arready[PVE_FABRIC_N_LT_M_PORTS];
  logic pve_m_lt_rvalid [PVE_FABRIC_N_LT_M_PORTS];
  logic pve_m_lt_rready [PVE_FABRIC_N_LT_M_PORTS];

  pve_lt_m_aw_t pve_m_lt_aw[PVE_FABRIC_N_LT_M_PORTS];
  pve_lt_w_t    pve_m_lt_w [PVE_FABRIC_N_LT_M_PORTS];
  pve_lt_m_b_t  pve_m_lt_b [PVE_FABRIC_N_LT_M_PORTS];
  pve_lt_m_ar_t pve_m_lt_ar[PVE_FABRIC_N_LT_M_PORTS];
  pve_lt_m_r_t  pve_m_lt_r [PVE_FABRIC_N_LT_M_PORTS];

  logic pve_s_ht_awvalid[PVE_FABRIC_N_HT_S_PORTS];
  logic pve_s_ht_awready[PVE_FABRIC_N_HT_S_PORTS];
  logic pve_s_ht_wvalid [PVE_FABRIC_N_HT_S_PORTS];
  logic pve_s_ht_wready [PVE_FABRIC_N_HT_S_PORTS];
  logic pve_s_ht_bvalid [PVE_FABRIC_N_HT_S_PORTS];
  logic pve_s_ht_bready [PVE_FABRIC_N_HT_S_PORTS];
  logic pve_s_ht_arvalid[PVE_FABRIC_N_HT_S_PORTS];
  logic pve_s_ht_arready[PVE_FABRIC_N_HT_S_PORTS];
  logic pve_s_ht_rvalid [PVE_FABRIC_N_HT_S_PORTS];
  logic pve_s_ht_rready [PVE_FABRIC_N_HT_S_PORTS];

  pve_ht_s_aw_t pve_s_ht_aw[PVE_FABRIC_N_HT_S_PORTS];
  pve_ht_w_t    pve_s_ht_w [PVE_FABRIC_N_HT_S_PORTS];
  pve_ht_s_b_t  pve_s_ht_b [PVE_FABRIC_N_HT_S_PORTS];
  pve_ht_s_ar_t pve_s_ht_ar[PVE_FABRIC_N_HT_S_PORTS];
  pve_ht_s_r_t  pve_s_ht_r [PVE_FABRIC_N_HT_S_PORTS];

  logic pve_m_ht_awvalid[PVE_FABRIC_N_HT_M_PORTS];
  logic pve_m_ht_awready[PVE_FABRIC_N_HT_M_PORTS];
  logic pve_m_ht_wvalid [PVE_FABRIC_N_HT_M_PORTS];
  logic pve_m_ht_wready [PVE_FABRIC_N_HT_M_PORTS];
  logic pve_m_ht_bvalid [PVE_FABRIC_N_HT_M_PORTS];
  logic pve_m_ht_bready [PVE_FABRIC_N_HT_M_PORTS];
  logic pve_m_ht_arvalid[PVE_FABRIC_N_HT_M_PORTS];
  logic pve_m_ht_arready[PVE_FABRIC_N_HT_M_PORTS];
  logic pve_m_ht_rvalid [PVE_FABRIC_N_HT_M_PORTS];
  logic pve_m_ht_rready [PVE_FABRIC_N_HT_M_PORTS];

  pve_ht_m_aw_t pve_m_ht_aw[PVE_FABRIC_N_HT_M_PORTS];
  pve_ht_w_t    pve_m_ht_w [PVE_FABRIC_N_HT_M_PORTS];
  pve_ht_m_b_t  pve_m_ht_b [PVE_FABRIC_N_HT_M_PORTS];
  pve_ht_m_ar_t pve_m_ht_ar[PVE_FABRIC_N_HT_M_PORTS];
  pve_ht_m_r_t  pve_m_ht_r [PVE_FABRIC_N_HT_M_PORTS];

  ///////////////////////////////////////////////////////////////
  //                                                           //
  //  LT XBAR                                                  //
  //  =======                                                  //
  //                                                           //
  ///////////////////////////////////////////////////////////////

  for (genvar I = 0; I < PVE_FABRIC_N_LT_S_EXT_PORTS; I++) begin: g_lt_s_mapping
    always_comb pve_s_lt_aw[I] = '{ id    : i_lt_axi_s_awid[I],
                                    addr  : i_lt_axi_s_awaddr[I],
                                    len   : i_lt_axi_s_awlen[I],
                                    size  : i_lt_axi_s_awsize[I],
                                    burst : i_lt_axi_s_awburst[I],
                                    lock  : i_lt_axi_s_awlock[I],
                                    cache : i_lt_axi_s_awcache[I],
                                    prot  : i_lt_axi_s_awprot[I],
                                    atop  : i_lt_axi_s_awatop[I] };

    always_comb pve_s_lt_w[I]  = '{ data  : i_lt_axi_s_wdata[I],
                                    strb  : i_lt_axi_s_wstrb[I],
                                    last  : i_lt_axi_s_wlast[I] };

    always_comb o_lt_axi_s_bid[I]    = pve_s_lt_b[I].id;
    always_comb o_lt_axi_s_bresp[I]  = pve_s_lt_b[I].resp;

    always_comb pve_s_lt_ar[I] = '{ id    : i_lt_axi_s_arid[I],
                                    addr  : i_lt_axi_s_araddr[I],
                                    len   : i_lt_axi_s_arlen[I],
                                    size  : i_lt_axi_s_arsize[I],
                                    burst : i_lt_axi_s_arburst[I],
                                    lock  : i_lt_axi_s_arlock[I],
                                    cache : i_lt_axi_s_arcache[I],
                                    prot  : i_lt_axi_s_arprot[I] };

    always_comb o_lt_axi_s_rid[I]    = pve_s_lt_r[I].id;
    always_comb o_lt_axi_s_rdata[I]  = pve_s_lt_r[I].data;
    always_comb o_lt_axi_s_rresp[I]  = pve_s_lt_r[I].resp;
    always_comb o_lt_axi_s_rlast[I]  = pve_s_lt_r[I].last;

    always_comb pve_s_lt_awvalid[I]   = i_lt_axi_s_awvalid[I];
    always_comb o_lt_axi_s_awready[I] = pve_s_lt_awready[I];
    always_comb pve_s_lt_wvalid[I]    = i_lt_axi_s_wvalid[I];
    always_comb o_lt_axi_s_wready[I]  = pve_s_lt_wready[I];
    always_comb o_lt_axi_s_bvalid[I]  = pve_s_lt_bvalid[I];
    always_comb pve_s_lt_bready[I]    = i_lt_axi_s_bready[I];
    always_comb pve_s_lt_arvalid[I]   = i_lt_axi_s_arvalid[I];
    always_comb o_lt_axi_s_arready[I] = pve_s_lt_arready[I];
    always_comb o_lt_axi_s_rvalid[I]  = pve_s_lt_rvalid[I];
    always_comb pve_s_lt_rready[I]    = i_lt_axi_s_rready[I];
  end: g_lt_s_mapping

  for (genvar I = 0; I < PVE_FABRIC_N_LT_M_EXT_PORTS; I++) begin: g_lt_m_mapping
    always_comb o_lt_axi_m_awid[I]     = pve_m_lt_aw[I].id;
    always_comb o_lt_axi_m_awaddr[I]   = pve_m_lt_aw[I].addr;
    always_comb o_lt_axi_m_awlen[I]    = pve_m_lt_aw[I].len;
    always_comb o_lt_axi_m_awsize[I]   = pve_m_lt_aw[I].size;
    always_comb o_lt_axi_m_awburst[I]  = pve_m_lt_aw[I].burst;
    always_comb o_lt_axi_m_awlock[I]   = pve_m_lt_aw[I].lock;
    always_comb o_lt_axi_m_awcache[I]  = pve_m_lt_aw[I].cache;
    always_comb o_lt_axi_m_awprot[I]   = pve_m_lt_aw[I].prot;
    always_comb o_lt_axi_m_awatop[I]   = pve_m_lt_aw[I].atop;

    always_comb o_lt_axi_m_wdata[I]    = pve_m_lt_w[I].data;
    always_comb o_lt_axi_m_wstrb[I]    = pve_m_lt_w[I].strb;
    always_comb o_lt_axi_m_wlast[I]    = pve_m_lt_w[I].last;

    always_comb pve_m_lt_b[I] = '{ id   : i_lt_axi_m_bid[I],
                                   resp : i_lt_axi_m_bresp[I] };

    always_comb o_lt_axi_m_arid[I]     = pve_m_lt_ar[I].id;
    always_comb o_lt_axi_m_araddr[I]   = pve_m_lt_ar[I].addr;
    always_comb o_lt_axi_m_arlen[I]    = pve_m_lt_ar[I].len;
    always_comb o_lt_axi_m_arsize[I]   = pve_m_lt_ar[I].size;
    always_comb o_lt_axi_m_arburst[I]  = pve_m_lt_ar[I].burst;
    always_comb o_lt_axi_m_arlock[I]   = pve_m_lt_ar[I].lock;
    always_comb o_lt_axi_m_arcache[I]  = pve_m_lt_ar[I].cache;
    always_comb o_lt_axi_m_arprot[I]   = pve_m_lt_ar[I].prot;

    always_comb pve_m_lt_r[I] = '{ id   : i_lt_axi_m_rid[I],
                                   data : i_lt_axi_m_rdata[I],
                                   resp : i_lt_axi_m_rresp[I],
                                   last : i_lt_axi_m_rlast[I] };

    always_comb o_lt_axi_m_awvalid[I] = pve_m_lt_awvalid[I];
    always_comb pve_m_lt_awready[I]   = i_lt_axi_m_awready[I];
    always_comb o_lt_axi_m_wvalid[I]  = pve_m_lt_wvalid[I];
    always_comb pve_m_lt_wready[I]    = i_lt_axi_m_wready[I];
    always_comb o_lt_axi_m_arvalid[I] = pve_m_lt_arvalid[I];
    always_comb pve_m_lt_arready[I]   = i_lt_axi_m_arready[I];
    always_comb o_lt_axi_m_bready[I]  = pve_m_lt_bready[I];
    always_comb pve_m_lt_bvalid[I]    = i_lt_axi_m_bvalid[I];
    always_comb o_lt_axi_m_rready[I]  = pve_m_lt_rready[I];
    always_comb pve_m_lt_rvalid[I]    = i_lt_axi_m_rvalid[I];
  end: g_lt_m_mapping

  pve_lt_xbar_rule_t lt_addr_rules [PVE_FABRIC_N_LT_M_PORTS];
  always_comb lt_addr_rules[0] = '{ index      : PVE_LT_M_PRTIDX_DMA0,
                                    addr_start : i_base_addr + PVE_TGT_DMA0_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_DMA0_MMAP_TOP };
  always_comb lt_addr_rules[1] = '{ index      : PVE_LT_M_PRTIDX_DMA1,
                                    addr_start : i_base_addr + PVE_TGT_DMA1_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_DMA1_MMAP_TOP };
  always_comb lt_addr_rules[2] = '{ index      : PVE_LT_M_PRTIDX_CLINT,
                                    addr_start : i_base_addr + PVE_TGT_CLINT_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_CLINT_MMAP_TOP };
  always_comb lt_addr_rules[3] = '{ index      : PVE_LT_M_PRTIDX_PERFC,
                                    addr_start : i_base_addr + PVE_TGT_PERFC_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_PERFC_MMAP_TOP };
  always_comb lt_addr_rules[4] = '{ index      : PVE_LT_M_PRTIDX_SPM,
                                    addr_start : i_base_addr + PVE_TGT_SPM_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_SPM_MMAP_TOP };
  always_comb lt_addr_rules[5] = '{ index      : PVE_LT_M_PRTIDX_INTHT,
                                    addr_start : i_base_addr + PVE_TGT_CL0L1_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_CL3L1_MMAP_TOP };
  always_comb lt_addr_rules[6] = '{ index      : PVE_LT_M_PRTIDX_EXT,
                                    addr_start : '0,
                                    addr_end   : '1 };

  logic default_m_port_en[PVE_FABRIC_N_LT_S_PORTS] = '{default : 1'b1};
  logic [$clog2(PVE_FABRIC_N_LT_M_PORTS)-1:0] default_m_port[PVE_FABRIC_N_LT_S_PORTS] = '{default : PVE_LT_S_PRTIDX_EXT};

  axe_axi_xbar #(
    // The number of subordinate ports
    .NumSubPorts    ( PVE_FABRIC_N_LT_S_PORTS ),
    // The number of manager ports
    .NumManPorts    ( PVE_FABRIC_N_LT_M_PORTS ),
    // The maximum number of outstanding transactions on each subordinate port per ID
    .MaxSubTxn      ( 32 ),
    // The maximum number of outstanding write transactions on each manager port
    .MaxManTxn      ( 32 ),
    // The Fifos in the design are configured in fall-through mode
    .FallThrough    ( 1'b0 ),
    // The latency mode of the ports, inserts spill registers at the ports
    .LatencyMode    ( axi_xbar_pkg::CUT_ALL_PORTS ),
    // The amount of pipeline stages in the middle of the cross, between the demux and muxes
    .LatencyCross   ( 0 ),
    // Axi Id width of the subordinate ports, the submodules require that
    // The ID width increses and is calculated by: `SubAxiIdWidth + $clog2(NumSubPorts)`
    // See `axe_axi_mux`
    .SubAxiIdWidth  ( PVE_LT_S_ID_W ),
    // Indicate that the incoming IDs are unique for each transaction, this causes the demux to be simpler
    .UniqueIds      ( 1'b0 ),
    // The actual slice width of a transaction ID that determines the uniques of an ID.
    // This directly translates to the amount of counters instanziated:
    // `(2**AxiIdUsedWidth) * NumSubPorts`
    // Note: This parameter might change in the future.
    .AxiIdUsedWidth ( 2 ),
    // The address with of the AXI structs
    .AxiAddrWidth   ( CHIP_AXI_ADDR_W ),
    // The number of address rules
    .NumAddrRules   ( PVE_FABRIC_N_LT_M_PORTS ),
    // Support atomic operations from AXI5 (ATOPS)
    .SupportAtops   ( 1'b1 ),
    // Define the connectivity between subordinates and manager ports
    .Connectivity   ( PVE_LT_CONNECTIVITY ),
    // Address rule type for the address decoders from `common_cells:addr_decode`.
    // Example types are provided in `axi_pkg`.
    // Required struct fields:
    // ```
    // typedef struct packed {
    //   int m_select_t index;
    //   axi_addr_t     addr_start;
    //   axi_addr_t     addr_end;
    // } addr_rule_t;
    // ```
    .addr_rule_t    ( pve_lt_xbar_rule_t ),
    // Subordinate AW channel type
    .axi_s_aw_t     ( pve_lt_s_aw_t ),
    // Manager AW channel type
    .axi_m_aw_t     ( pve_lt_m_aw_t ),
    // Subordinate *AND* Manager W channel type
    .axi_w_t        ( pve_lt_w_t ),
    // Subordinate B channel type
    .axi_s_b_t      ( pve_lt_s_b_t ),
    // Manager B channel type
    .axi_m_b_t      ( pve_lt_m_b_t ),
    // Subordinate AR channel type
    .axi_s_ar_t     ( pve_lt_s_ar_t ),
    // Manager AR channel type
    .axi_m_ar_t     ( pve_lt_m_ar_t ),
    // Subordinate R channel type
    .axi_s_r_t      ( pve_lt_s_r_t ),
    // Manager R channel type
    .axi_m_r_t      ( pve_lt_m_r_t )
  ) u_lt_xbar (
    // Clock, positive edge triggered.
    .i_clk,
    // Asynchronous reset, active low.
    .i_rst_n,

    // Subordinate Port
    .i_axi_s_aw      ( pve_s_lt_aw       ),
    .i_axi_s_aw_valid( pve_s_lt_awvalid  ),
    .o_axi_s_aw_ready( pve_s_lt_awready  ),
    .i_axi_s_w       ( pve_s_lt_w        ),
    .i_axi_s_w_valid ( pve_s_lt_wvalid   ),
    .o_axi_s_w_ready ( pve_s_lt_wready   ),
    .o_axi_s_b       ( pve_s_lt_b        ),
    .o_axi_s_b_valid ( pve_s_lt_bvalid   ),
    .i_axi_s_b_ready ( pve_s_lt_bready   ),
    .i_axi_s_ar      ( pve_s_lt_ar       ),
    .i_axi_s_ar_valid( pve_s_lt_arvalid  ),
    .o_axi_s_ar_ready( pve_s_lt_arready  ),
    .o_axi_s_r       ( pve_s_lt_r        ),
    .o_axi_s_r_valid ( pve_s_lt_rvalid   ),
    .i_axi_s_r_ready ( pve_s_lt_rready   ),

    // Manager Port
    .o_axi_m_aw      ( pve_m_lt_aw      ),
    .o_axi_m_aw_valid( pve_m_lt_awvalid ),
    .i_axi_m_aw_ready( pve_m_lt_awready ),
    .o_axi_m_w       ( pve_m_lt_w       ),
    .o_axi_m_w_valid ( pve_m_lt_wvalid  ),
    .i_axi_m_w_ready ( pve_m_lt_wready  ),
    .i_axi_m_b       ( pve_m_lt_b       ),
    .i_axi_m_b_valid ( pve_m_lt_bvalid  ),
    .o_axi_m_b_ready ( pve_m_lt_bready  ),
    .o_axi_m_ar      ( pve_m_lt_ar      ),
    .o_axi_m_ar_valid( pve_m_lt_arvalid ),
    .i_axi_m_ar_ready( pve_m_lt_arready ),
    .i_axi_m_r       ( pve_m_lt_r       ),
    .i_axi_m_r_valid ( pve_m_lt_rvalid  ),
    .o_axi_m_r_ready ( pve_m_lt_rready  ),

    // The address map, replicated on all subordinate ports
    .i_addr_map          ( lt_addr_rules ),
    // Enable default routing on decode errors
    .i_default_m_port_en ( default_m_port_en ),
    // Default routing mapping per subordinate port
    .i_default_m_port    ( default_m_port )
  );

  ///////////////////////////////////////////////////////////////
  //                                                           //
  //  LT2HT ATOP FILTER + DW CONVERSION                        //
  //                                                           //
  ///////////////////////////////////////////////////////////////
  logic pve_lt2ht_awvalid;
  logic pve_lt2ht_awready;
  logic pve_lt2ht_wvalid;
  logic pve_lt2ht_wready;
  logic pve_lt2ht_bvalid;
  logic pve_lt2ht_bready;
  logic pve_lt2ht_arvalid;
  logic pve_lt2ht_arready;
  logic pve_lt2ht_rvalid;
  logic pve_lt2ht_rready;

  pve_lt_m_aw_t pve_lt2ht_aw;
  pve_lt_w_t    pve_lt2ht_w;
  pve_lt_m_b_t  pve_lt2ht_b;
  pve_lt_m_ar_t pve_lt2ht_ar;
  pve_lt_m_r_t  pve_lt2ht_r;

  axe_axi_atop_filter #(
    .AxiIdWidth     ( PVE_LT_M_ID_W     ),
    .AxiMaxWriteTxns( 1                 ),
    .axi_aw_t       ( pve_lt_m_aw_t     ),
    .axi_w_t        ( pve_lt_w_t        ),
    .axi_b_t        ( pve_lt_m_b_t      ),
    .axi_ar_t       ( pve_lt_m_ar_t     ),
    .axi_r_t        ( pve_lt_m_r_t      )
  ) u_lt2ht_atop_filter (
    // Clock and reset signals
    .i_clk,
    .i_rst_n,
    // Subordinate port
    .i_axi_s_aw        ( pve_m_lt_aw     [PVE_LT_M_PRTIDX_INTHT] ),
    .i_axi_s_aw_valid  ( pve_m_lt_awvalid[PVE_LT_M_PRTIDX_INTHT] ),
    .o_axi_s_aw_ready  ( pve_m_lt_awready[PVE_LT_M_PRTIDX_INTHT] ),
    .i_axi_s_w         ( pve_m_lt_w      [PVE_LT_M_PRTIDX_INTHT] ),
    .i_axi_s_w_valid   ( pve_m_lt_wvalid [PVE_LT_M_PRTIDX_INTHT] ),
    .o_axi_s_w_ready   ( pve_m_lt_wready [PVE_LT_M_PRTIDX_INTHT] ),
    .o_axi_s_b         ( pve_m_lt_b      [PVE_LT_M_PRTIDX_INTHT] ),
    .o_axi_s_b_valid   ( pve_m_lt_bvalid [PVE_LT_M_PRTIDX_INTHT] ),
    .i_axi_s_b_ready   ( pve_m_lt_bready [PVE_LT_M_PRTIDX_INTHT] ),
    .i_axi_s_ar        ( pve_m_lt_ar     [PVE_LT_M_PRTIDX_INTHT] ),
    .i_axi_s_ar_valid  ( pve_m_lt_arvalid[PVE_LT_M_PRTIDX_INTHT] ),
    .o_axi_s_ar_ready  ( pve_m_lt_arready[PVE_LT_M_PRTIDX_INTHT] ),
    .o_axi_s_r         ( pve_m_lt_r      [PVE_LT_M_PRTIDX_INTHT] ),
    .o_axi_s_r_valid   ( pve_m_lt_rvalid [PVE_LT_M_PRTIDX_INTHT] ),
    .i_axi_s_r_ready   ( pve_m_lt_rready [PVE_LT_M_PRTIDX_INTHT] ),
    // Manager port
    .o_axi_m_aw        ( pve_lt2ht_aw      ),
    .o_axi_m_aw_valid  ( pve_lt2ht_awvalid ),
    .i_axi_m_aw_ready  ( pve_lt2ht_awready ),
    .o_axi_m_w         ( pve_lt2ht_w       ),
    .o_axi_m_w_valid   ( pve_lt2ht_wvalid  ),
    .i_axi_m_w_ready   ( pve_lt2ht_wready  ),
    .i_axi_m_b         ( pve_lt2ht_b       ),
    .i_axi_m_b_valid   ( pve_lt2ht_bvalid  ),
    .o_axi_m_b_ready   ( pve_lt2ht_bready  ),
    .o_axi_m_ar        ( pve_lt2ht_ar      ),
    .o_axi_m_ar_valid  ( pve_lt2ht_arvalid ),
    .i_axi_m_ar_ready  ( pve_lt2ht_arready ),
    .i_axi_m_r         ( pve_lt2ht_r       ),
    .i_axi_m_r_valid   ( pve_lt2ht_rvalid  ),
    .o_axi_m_r_ready   ( pve_lt2ht_rready  )
  );

  axe_axi_dw_converter #(
    // ID width of both subordinate and manager port
    .AxiIdWidth          ( PVE_HT_S_ID_W ),
    // Address width of both subordinate and manager port
    .AxiAddrWidth        ( CHIP_AXI_ADDR_W ),
    // Datawidth of the subordinate port
    .AxiSubPortDataWidth ( CHIP_AXI_LT_DATA_W ),
    // Datawidth of the manager port
    .AxiManPortDataWidth ( CHIP_AXI_HT_DATA_W ),
    // The number of parallel outstanding reads the converteer can do at a given time.
    .AxiMaxReads         ( 4 ),

    .axi_aw_t            ( pve_ht_s_aw_t ),
    .axi_s_w_t           ( pve_lt_w_t    ),
    .axi_m_w_t           ( pve_ht_w_t    ),
    .axi_b_t             ( pve_lt_m_b_t  ),
    .axi_ar_t            ( pve_lt_m_ar_t ),
    .axi_s_r_t           ( pve_lt_m_r_t  ),
    .axi_m_r_t           ( pve_ht_s_r_t  )
  ) u_lt2ht_dw_conv (
    // Clock, positive edge triggered
    .i_clk,
    // doc async
    // Asynchronous reset, active low
    .i_rst_n,
    // doc sync i_clk

    //////////////////////
    // Subordinate Port //
    //////////////////////
    .i_axi_s_aw        ( pve_lt2ht_aw      ),
    .i_axi_s_aw_valid  ( pve_lt2ht_awvalid ),
    .o_axi_s_aw_ready  ( pve_lt2ht_awready ),
    .i_axi_s_w         ( pve_lt2ht_w       ),
    .i_axi_s_w_valid   ( pve_lt2ht_wvalid  ),
    .o_axi_s_w_ready   ( pve_lt2ht_wready  ),
    .o_axi_s_b         ( pve_lt2ht_b       ),
    .o_axi_s_b_valid   ( pve_lt2ht_bvalid  ),
    .i_axi_s_b_ready   ( pve_lt2ht_bready  ),
    .i_axi_s_ar        ( pve_lt2ht_ar      ),
    .i_axi_s_ar_valid  ( pve_lt2ht_arvalid ),
    .o_axi_s_ar_ready  ( pve_lt2ht_arready ),
    .o_axi_s_r         ( pve_lt2ht_r       ),
    .o_axi_s_r_valid   ( pve_lt2ht_rvalid  ),
    .i_axi_s_r_ready   ( pve_lt2ht_rready  ),

    //////////////////
    // Manager port //
    //////////////////
    .o_axi_m_aw        ( pve_s_ht_aw     [PVE_HT_S_PRTIDX_INTLT] ),
    .o_axi_m_aw_valid  ( pve_s_ht_awvalid[PVE_HT_S_PRTIDX_INTLT] ),
    .i_axi_m_aw_ready  ( pve_s_ht_awready[PVE_HT_S_PRTIDX_INTLT] ),
    .o_axi_m_w         ( pve_s_ht_w      [PVE_HT_S_PRTIDX_INTLT] ),
    .o_axi_m_w_valid   ( pve_s_ht_wvalid [PVE_HT_S_PRTIDX_INTLT] ),
    .i_axi_m_w_ready   ( pve_s_ht_wready [PVE_HT_S_PRTIDX_INTLT] ),
    .i_axi_m_b         ( pve_s_ht_b      [PVE_HT_S_PRTIDX_INTLT] ),
    .i_axi_m_b_valid   ( pve_s_ht_bvalid [PVE_HT_S_PRTIDX_INTLT] ),
    .o_axi_m_b_ready   ( pve_s_ht_bready [PVE_HT_S_PRTIDX_INTLT] ),
    .o_axi_m_ar        ( pve_s_ht_ar     [PVE_HT_S_PRTIDX_INTLT] ),
    .o_axi_m_ar_valid  ( pve_s_ht_arvalid[PVE_HT_S_PRTIDX_INTLT] ),
    .i_axi_m_ar_ready  ( pve_s_ht_arready[PVE_HT_S_PRTIDX_INTLT] ),
    .i_axi_m_r         ( pve_s_ht_r      [PVE_HT_S_PRTIDX_INTLT] ),
    .i_axi_m_r_valid   ( pve_s_ht_rvalid [PVE_HT_S_PRTIDX_INTLT] ),
    .o_axi_m_r_ready   ( pve_s_ht_rready [PVE_HT_S_PRTIDX_INTLT] )
  );

  ///////////////////////////////////////////////////////////////
  //                                                           //
  //  HT2LT ID WIDTH + DW CONVERSION                           //
  //                                                           //
  ///////////////////////////////////////////////////////////////
  logic pve_ht2lt_awvalid;
  logic pve_ht2lt_awready;
  logic pve_ht2lt_wvalid;
  logic pve_ht2lt_wready;
  logic pve_ht2lt_bvalid;
  logic pve_ht2lt_bready;
  logic pve_ht2lt_arvalid;
  logic pve_ht2lt_arready;
  logic pve_ht2lt_rvalid;
  logic pve_ht2lt_rready;

  pve_lt_s_aw_t      pve_ht2lt_aw;
  pve_ht_w_t         pve_ht2lt_w;
  pve_lt_s_b_t       pve_ht2lt_b;
  pve_lt_s_ar_t      pve_ht2lt_ar;
  pve_ht_m_ltid_r_t  pve_ht2lt_r;

  axe_axi_id_remap #(
    .SubAxiIdWidth( PVE_HT_M_ID_W     ),
    .SubMaxUniqIds( 2**PVE_LT_S_ID_W  ),
    .MaxTxnsPerId ( 64                ),
    .ManAxiIdWidth( PVE_LT_S_ID_W     ),
    .axi_s_aw_t   ( pve_ht_m_aw_t     ),
    .axi_s_w_t    ( pve_ht_w_t        ),
    .axi_s_b_t    ( pve_ht_m_b_t      ),
    .axi_s_ar_t   ( pve_ht_m_ar_t     ),
    .axi_s_r_t    ( pve_ht_m_r_t      ),
    .axi_m_aw_t   ( pve_lt_s_aw_t     ),
    .axi_m_w_t    ( pve_ht_w_t        ),
    .axi_m_b_t    ( pve_lt_s_b_t      ),
    .axi_m_ar_t   ( pve_lt_s_ar_t     ),
    .axi_m_r_t    ( pve_ht_m_ltid_r_t )
  ) u_ht2lt_id_remap (
    // Clock and reset signals
    .i_clk,
    .i_rst_n,
    // Subordinate port
    .i_axi_s_aw        ( pve_m_ht_aw     [PVE_HT_M_PRTIDX_INTLT] ),
    .i_axi_s_aw_valid  ( pve_m_ht_arvalid[PVE_HT_M_PRTIDX_INTLT] ),
    .o_axi_s_aw_ready  ( pve_m_ht_awready[PVE_HT_M_PRTIDX_INTLT] ),
    .i_axi_s_w         ( pve_m_ht_w      [PVE_HT_M_PRTIDX_INTLT] ),
    .i_axi_s_w_valid   ( pve_m_ht_wvalid [PVE_HT_M_PRTIDX_INTLT] ),
    .o_axi_s_w_ready   ( pve_m_ht_wready [PVE_HT_M_PRTIDX_INTLT] ),
    .o_axi_s_b         ( pve_m_ht_b      [PVE_HT_M_PRTIDX_INTLT] ),
    .o_axi_s_b_valid   ( pve_m_ht_bvalid [PVE_HT_M_PRTIDX_INTLT] ),
    .i_axi_s_b_ready   ( pve_m_ht_bready [PVE_HT_M_PRTIDX_INTLT] ),
    .i_axi_s_ar        ( pve_m_ht_ar     [PVE_HT_M_PRTIDX_INTLT] ),
    .i_axi_s_ar_valid  ( pve_m_ht_arvalid[PVE_HT_M_PRTIDX_INTLT] ),
    .o_axi_s_ar_ready  ( pve_m_ht_arready[PVE_HT_M_PRTIDX_INTLT] ),
    .o_axi_s_r         ( pve_m_ht_r      [PVE_HT_M_PRTIDX_INTLT] ),
    .o_axi_s_r_valid   ( pve_m_ht_rvalid [PVE_HT_M_PRTIDX_INTLT] ),
    .i_axi_s_r_ready   ( pve_m_ht_rready [PVE_HT_M_PRTIDX_INTLT] ),
    // Manager port
    .o_axi_m_aw        ( pve_ht2lt_aw      ),
    .o_axi_m_aw_valid  ( pve_ht2lt_awvalid ),
    .i_axi_m_aw_ready  ( pve_ht2lt_awready ),
    .o_axi_m_w         ( pve_ht2lt_w       ),
    .o_axi_m_w_valid   ( pve_ht2lt_wvalid  ),
    .i_axi_m_w_ready   ( pve_ht2lt_wready  ),
    .i_axi_m_b         ( pve_ht2lt_b       ),
    .i_axi_m_b_valid   ( pve_ht2lt_bvalid  ),
    .o_axi_m_b_ready   ( pve_ht2lt_bready  ),
    .o_axi_m_ar        ( pve_ht2lt_ar      ),
    .o_axi_m_ar_valid  ( pve_ht2lt_arvalid ),
    .i_axi_m_ar_ready  ( pve_ht2lt_arready ),
    .i_axi_m_r         ( pve_ht2lt_r       ),
    .i_axi_m_r_valid   ( pve_ht2lt_rvalid  ),
    .o_axi_m_r_ready   ( pve_ht2lt_rready  )
  );

  axe_axi_dw_converter #(
    // ID width of both subordinate and manager port
    .AxiIdWidth          ( PVE_LT_S_ID_W ),
    // Address width of both subordinate and manager port
    .AxiAddrWidth        ( CHIP_AXI_ADDR_W ),
    // Datawidth of the subordinate port
    .AxiSubPortDataWidth ( CHIP_AXI_HT_DATA_W ),
    // Datawidth of the manager port
    .AxiManPortDataWidth ( CHIP_AXI_LT_DATA_W ),
    // The number of parallel outstanding reads the converteer can do at a given time.
    .AxiMaxReads         ( 4 ),

    .axi_aw_t            ( pve_lt_s_aw_t     ),
    .axi_s_w_t           ( pve_ht_w_t        ),
    .axi_m_w_t           ( pve_lt_w_t        ),
    .axi_b_t             ( pve_lt_s_b_t      ),
    .axi_ar_t            ( pve_lt_s_ar_t     ),
    .axi_s_r_t           ( pve_ht_m_ltid_r_t ),
    .axi_m_r_t           ( pve_lt_s_r_t      )
  ) u_ht2lt_dw_conv (
    // Clock, positive edge triggered
    .i_clk,
    // doc async
    // Asynchronous reset, active low
    .i_rst_n,
    // doc sync i_clk

    //////////////////////
    // Subordinate Port //
    //////////////////////
    .i_axi_s_aw        ( pve_ht2lt_aw      ),
    .i_axi_s_aw_valid  ( pve_ht2lt_awvalid ),
    .o_axi_s_aw_ready  ( pve_ht2lt_awready ),
    .i_axi_s_w         ( pve_ht2lt_w       ),
    .i_axi_s_w_valid   ( pve_ht2lt_wvalid  ),
    .o_axi_s_w_ready   ( pve_ht2lt_wready  ),
    .o_axi_s_b         ( pve_ht2lt_b       ),
    .o_axi_s_b_valid   ( pve_ht2lt_bvalid  ),
    .i_axi_s_b_ready   ( pve_ht2lt_bready  ),
    .i_axi_s_ar        ( pve_ht2lt_ar      ),
    .i_axi_s_ar_valid  ( pve_ht2lt_arvalid ),
    .o_axi_s_ar_ready  ( pve_ht2lt_arready ),
    .o_axi_s_r         ( pve_ht2lt_r       ),
    .o_axi_s_r_valid   ( pve_ht2lt_rvalid  ),
    .i_axi_s_r_ready   ( pve_ht2lt_rready  ),

    //////////////////
    // Manager port //
    //////////////////
    .o_axi_m_aw        ( pve_s_lt_aw     [PVE_LT_S_PRTIDX_INTHT] ),
    .o_axi_m_aw_valid  ( pve_s_lt_awvalid[PVE_LT_S_PRTIDX_INTHT] ),
    .i_axi_m_aw_ready  ( pve_s_lt_awready[PVE_LT_S_PRTIDX_INTHT] ),
    .o_axi_m_w         ( pve_s_lt_w      [PVE_LT_S_PRTIDX_INTHT] ),
    .o_axi_m_w_valid   ( pve_s_lt_wvalid [PVE_LT_S_PRTIDX_INTHT] ),
    .i_axi_m_w_ready   ( pve_s_lt_wready [PVE_LT_S_PRTIDX_INTHT] ),
    .i_axi_m_b         ( pve_s_lt_b      [PVE_LT_S_PRTIDX_INTHT] ),
    .i_axi_m_b_valid   ( pve_s_lt_bvalid [PVE_LT_S_PRTIDX_INTHT] ),
    .o_axi_m_b_ready   ( pve_s_lt_bready [PVE_LT_S_PRTIDX_INTHT] ),
    .o_axi_m_ar        ( pve_s_lt_ar     [PVE_LT_S_PRTIDX_INTHT] ),
    .o_axi_m_ar_valid  ( pve_s_lt_arvalid[PVE_LT_S_PRTIDX_INTHT] ),
    .i_axi_m_ar_ready  ( pve_s_lt_arready[PVE_LT_S_PRTIDX_INTHT] ),
    .i_axi_m_r         ( pve_s_lt_r      [PVE_LT_S_PRTIDX_INTHT] ),
    .i_axi_m_r_valid   ( pve_s_lt_rvalid [PVE_LT_S_PRTIDX_INTHT] ),
    .o_axi_m_r_ready   ( pve_s_lt_rready [PVE_LT_S_PRTIDX_INTHT] )
  );

  ///////////////////////////////////////////////////////////////
  //                                                           //
  //  HT XBAR                                                  //
  //                                                           //
  ///////////////////////////////////////////////////////////////

  for (genvar I = 0; I < PVE_FABRIC_N_HT_S_EXT_PORTS; I++) begin: g_ht_s_mapping
    always_comb pve_s_ht_aw[I] = '{ id    : i_ht_axi_s_awid[I],
                                    addr  : i_ht_axi_s_awaddr[I],
                                    len   : i_ht_axi_s_awlen[I],
                                    size  : i_ht_axi_s_awsize[I],
                                    burst : i_ht_axi_s_awburst[I],
                                    lock  : i_ht_axi_s_awlock[I],
                                    cache : i_ht_axi_s_awcache[I],
                                    prot  : i_ht_axi_s_awprot[I],
                                    atop  : i_ht_axi_s_awatop[I] };

    always_comb pve_s_ht_w[I]  = '{ data  : i_ht_axi_s_wdata[I],
                                    strb  : i_ht_axi_s_wstrb[I],
                                    last  : i_ht_axi_s_wlast[I]};

    always_comb o_ht_axi_s_bid[I]    = pve_s_ht_b[I].id;
    always_comb o_ht_axi_s_bresp[I]  = pve_s_ht_b[I].resp;

    always_comb pve_s_ht_ar[I] = '{ id    : i_ht_axi_s_arid[I],
                                    addr  : i_ht_axi_s_araddr[I],
                                    len   : i_ht_axi_s_arlen[I],
                                    size  : i_ht_axi_s_arsize[I],
                                    burst : i_ht_axi_s_arburst[I],
                                    lock  : i_ht_axi_s_arlock[I],
                                    cache : i_ht_axi_s_arcache[I],
                                    prot  : i_ht_axi_s_arprot[I] };

    always_comb o_ht_axi_s_rid[I]     = pve_s_ht_r[I].id;
    always_comb o_ht_axi_s_rdata[I]   = pve_s_ht_r[I].data;
    always_comb o_ht_axi_s_rresp[I]   = pve_s_ht_r[I].resp;
    always_comb o_ht_axi_s_rlast[I]   = pve_s_ht_r[I].last;

    always_comb pve_s_ht_awvalid[I]   = i_ht_axi_s_awvalid[I];
    always_comb o_ht_axi_s_awready[I] = pve_s_ht_awready[I];
    always_comb pve_s_ht_wvalid[I]    = i_ht_axi_s_wvalid[I];
    always_comb o_ht_axi_s_wready[I]  = pve_s_ht_wready[I];
    always_comb o_ht_axi_s_bvalid[I]  = pve_s_ht_bvalid[I];
    always_comb pve_s_ht_bready[I]    = i_ht_axi_s_bready[I];
    always_comb pve_s_ht_arvalid[I]   = i_ht_axi_s_arvalid[I];
    always_comb o_ht_axi_s_arready[I] = pve_s_ht_arready[I];
    always_comb o_ht_axi_s_rvalid[I]  = pve_s_ht_rvalid[I];
    always_comb pve_s_ht_rready[I]    = i_ht_axi_s_rready[I];
  end: g_ht_s_mapping

  for (genvar I = 0; I < PVE_FABRIC_N_HT_M_EXT_PORTS; I++) begin: g_ht_m_mapping
    always_comb o_ht_axi_m_awid[I]    = pve_m_ht_aw[I].id;
    always_comb o_ht_axi_m_awaddr[I]  = pve_m_ht_aw[I].addr;
    always_comb o_ht_axi_m_awlen[I]   = pve_m_ht_aw[I].len;
    always_comb o_ht_axi_m_awsize[I]  = pve_m_ht_aw[I].size;
    always_comb o_ht_axi_m_awburst[I] = pve_m_ht_aw[I].burst;
    always_comb o_ht_axi_m_awlock[I]  = pve_m_ht_aw[I].lock;
    always_comb o_ht_axi_m_awcache[I] = pve_m_ht_aw[I].cache;
    always_comb o_ht_axi_m_awprot[I]  = pve_m_ht_aw[I].prot;

    always_comb o_ht_axi_m_wdata[I]   = pve_m_ht_w[I].data;
    always_comb o_ht_axi_m_wstrb[I]   = pve_m_ht_w[I].strb;
    always_comb o_ht_axi_m_wlast[I]   = pve_m_ht_w[I].last;

    always_comb pve_m_ht_b[I] = '{ id  : i_ht_axi_m_bid[I],
                                  resp : i_ht_axi_m_bresp[I] };

    always_comb o_ht_axi_m_arid[I]    = pve_m_ht_ar[I].id;
    always_comb o_ht_axi_m_araddr[I]  = pve_m_ht_ar[I].addr;
    always_comb o_ht_axi_m_arlen[I]   = pve_m_ht_ar[I].len;
    always_comb o_ht_axi_m_arsize[I]  = pve_m_ht_ar[I].size;
    always_comb o_ht_axi_m_arburst[I] = pve_m_ht_ar[I].burst;
    always_comb o_ht_axi_m_arlock[I]  = pve_m_ht_ar[I].lock;
    always_comb o_ht_axi_m_arcache[I] = pve_m_ht_ar[I].cache;
    always_comb o_ht_axi_m_arprot[I]  = pve_m_ht_ar[I].prot;

    always_comb pve_m_ht_r[I] = '{ id  : i_ht_axi_m_rid[I],
                                  data : i_ht_axi_m_rdata[I],
                                  resp : i_ht_axi_m_rresp[I],
                                  last : i_ht_axi_m_rlast[I] };

    always_comb o_ht_axi_m_awvalid[I] = pve_m_ht_awvalid[I];
    always_comb pve_m_ht_awready[I]   = i_ht_axi_m_awready[I];
    always_comb o_ht_axi_m_wvalid[I]  = pve_m_ht_wvalid[I];
    always_comb pve_m_ht_wready[I]    = i_ht_axi_m_wready[I];
    always_comb o_ht_axi_m_arvalid[I] = pve_m_ht_arvalid[I];
    always_comb pve_m_ht_arready[I]   = i_ht_axi_m_arready[I];
    always_comb o_ht_axi_m_bready[I]  = pve_m_ht_bready[I];
    always_comb pve_m_ht_bvalid[I]    = i_ht_axi_m_bvalid[I];
    always_comb o_ht_axi_m_rready[I]  = pve_m_ht_rready[I];
    always_comb pve_m_ht_rvalid[I]    = i_ht_axi_m_rvalid[I];

  end: g_ht_m_mapping

  pve_ht_xbar_rule_t ht_addr_rules [PVE_FABRIC_N_HT_M_PORTS];
  always_comb ht_addr_rules[0] = '{ index      : PVE_HT_M_PRTIDX_CL0L1,
                                    addr_start : i_base_addr + PVE_TGT_CL0L1_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_CL0L1_MMAP_TOP };
  always_comb ht_addr_rules[1] = '{ index      : PVE_HT_M_PRTIDX_CL1L1,
                                    addr_start : i_base_addr + PVE_TGT_CL1L1_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_CL1L1_MMAP_TOP };
  always_comb ht_addr_rules[2] = '{ index      : PVE_HT_M_PRTIDX_CL2L1,
                                    addr_start : i_base_addr + PVE_TGT_CL2L1_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_CL2L1_MMAP_TOP };
  always_comb ht_addr_rules[3] = '{ index      : PVE_HT_M_PRTIDX_CL3L1,
                                    addr_start : i_base_addr + PVE_TGT_CL3L1_MMAP_BASE,
                                    addr_end   : i_base_addr + PVE_TGT_CL3L1_MMAP_TOP };
  // FIXME: Fix those rules such that they are not equivalent.
  always_comb ht_addr_rules[4] = '{ index      : PVE_HT_M_PRTIDX_EXT,
                                    addr_start : '0,
                                    addr_end   : '1 };
  always_comb ht_addr_rules[5] = '{ index      : PVE_HT_M_PRTIDX_INTLT,
                                    addr_start : '0,
                                    addr_end   : '1 };

  axe_axi_xbar #(
    // The number of subordinate ports
    .NumSubPorts        ( PVE_FABRIC_N_HT_S_PORTS ),
    // The number of manager ports
    .NumManPorts        ( PVE_FABRIC_N_HT_M_PORTS ),
    // The maximum number of outstanding transactions on each subordinate port per ID
    .MaxSubTxn          ( 256 ),
    // The maximum number of outstanding write transactions on each manager port
    .MaxManTxn          ( 256 ),
    // The Fifos in the design are configured in fall-through mode
    .FallThrough        ( 1'b0 ),
    // The latency mode of the ports, inserts spill registers at the ports
    .LatencyMode        ( axi_xbar_pkg::CUT_ALL_PORTS ),
    // The amount of pipeline stages in the middle of the cross, between the demux and muxes
    .LatencyCross       ( 0 ),
    // Axi Id width of the subordinate ports, the submodules require that
    // The ID width increses and is calculated by: `SubAxiIdWidth + $clog2(NumSubPorts)`
    // See `axe_axi_mux`
    .SubAxiIdWidth      ( PVE_HT_S_ID_W ),
    // Indicate that the incoming IDs are unique for each transaction, this causes the demux to be simpler
    .UniqueIds          ( 1'b0 ),
    // The actual slice width of a transaction ID that determines the uniques of an ID.
    // This directly translates to the amount of counters instanziated:
    // `(2**AxiIdUsedWidth) * NumSubPorts`
    // Note: This parameter might change in the future.
    .AxiIdUsedWidth     ( 2 ),
    // The address with of the AXI structs
    .AxiAddrWidth       ( CHIP_AXI_ADDR_W ),
    // The number of address rules
    .NumAddrRules       ( PVE_FABRIC_N_HT_M_PORTS ),
    // Support atomic operations from AXI5 (ATOPS)
    .SupportAtops       ( 1'b1 ),
    // Define the connectivity between subordinates and manager ports
    .Connectivity       ( PVE_HT_CONNECTIVITY ),
    // Address rule type for the address decoders from `common_cells:addr_decode`.
    // Example types are provided in `axi_pkg`.
    // Required struct fields:
    // ```
    // typedef struct packed {
    //   int m_select_t index;
    //   axi_addr_t     addr_start;
    //   axi_addr_t     addr_end;
    // } addr_rule_t;
    // ```
    .addr_rule_t      ( pve_ht_xbar_rule_t ),
    // Subordinate AW channel type
    .axi_s_aw_t       ( pve_ht_s_aw_t ),
    // Manager AW channel type
    .axi_m_aw_t       ( pve_ht_m_aw_t ),
    // Subordinate *AND* Manager W channel type
    .axi_w_t          ( pve_ht_w_t ),
    // Subordinate B channel type
    .axi_s_b_t        ( pve_ht_s_b_t ),
    // Manager B channel type
    .axi_m_b_t        ( pve_ht_m_b_t ),
    // Subordinate AR channel type
    .axi_s_ar_t       ( pve_ht_s_ar_t ),
    // Manager AR channel type
    .axi_m_ar_t       ( pve_ht_m_ar_t ),
    // Subordinate R channel type
    .axi_s_r_t        ( pve_ht_s_r_t ),
    // Manager R channel type
    .axi_m_r_t        ( pve_ht_m_r_t )
  )  u_ht_xbar (
    // Clock, positive edge triggered.
    .i_clk,
    // Asynchronous reset, active low.
    .i_rst_n,

    // Subordinate Port
    .i_axi_s_aw      ( pve_s_ht_aw      ),
    .i_axi_s_aw_valid( pve_s_ht_awvalid ),
    .o_axi_s_aw_ready( pve_s_ht_awready ),
    .i_axi_s_w       ( pve_s_ht_w       ),
    .i_axi_s_w_valid ( pve_s_ht_wvalid  ),
    .o_axi_s_w_ready ( pve_s_ht_wready  ),
    .o_axi_s_b       ( pve_s_ht_b       ),
    .o_axi_s_b_valid ( pve_s_ht_bvalid  ),
    .i_axi_s_b_ready ( pve_s_ht_bready  ),
    .i_axi_s_ar      ( pve_s_ht_ar      ),
    .i_axi_s_ar_valid( pve_s_ht_arvalid ),
    .o_axi_s_ar_ready( pve_s_ht_arready ),
    .o_axi_s_r       ( pve_s_ht_r       ),
    .o_axi_s_r_valid ( pve_s_ht_rvalid  ),
    .i_axi_s_r_ready ( pve_s_ht_rready  ),

    // Manager Port
    .o_axi_m_aw      ( pve_m_ht_aw      ),
    .o_axi_m_aw_valid( pve_m_ht_awvalid ),
    .i_axi_m_aw_ready( pve_m_ht_awready ),
    .o_axi_m_w       ( pve_m_ht_w       ),
    .o_axi_m_w_valid ( pve_m_ht_wvalid  ),
    .i_axi_m_w_ready ( pve_m_ht_wready  ),
    .i_axi_m_b       ( pve_m_ht_b       ),
    .i_axi_m_b_valid ( pve_m_ht_bvalid  ),
    .o_axi_m_b_ready ( pve_m_ht_bready  ),
    .o_axi_m_ar      ( pve_m_ht_ar      ),
    .o_axi_m_ar_valid( pve_m_ht_arvalid ),
    .i_axi_m_ar_ready( pve_m_ht_arready ),
    .i_axi_m_r       ( pve_m_ht_r       ),
    .i_axi_m_r_valid ( pve_m_ht_rvalid  ),
    .o_axi_m_r_ready ( pve_m_ht_rready  ),

    // The address map, replicated on all subordinate ports
    .i_addr_map          ( ht_addr_rules ),
    // Enable default routing on decode errors
    .i_default_m_port_en ( '{default:'0} ),
    // Default routing mapping per subordinate port
    .i_default_m_port    ( '{default:'0} )
  );

endmodule
