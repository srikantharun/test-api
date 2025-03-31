// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// PCIe partition wrapper

module pcie_p
  import chip_pkg::*;
  import axi_pkg::*;
  import pcie_pkg::*;
(
  // Global Clock and Reset Signals
  // Ref Clock, positive edge triggered
  input  wire                         i_ref_clk,
  // Asynchronous POR / always On reset, active low
  input  wire                         i_ao_rst_n,
  // Asynchronous global reset, active low
  input  wire                         i_global_rst_n,

  // NoC Control Signals
  output logic                        o_noc_async_idle_init_mt_axi_req,
  output logic                        o_noc_async_idle_targ_mt_axi_req,
  output logic                        o_noc_async_idle_targ_cfg_dbi_axi_req,
  output logic                        o_noc_async_idle_targ_cfg_apb_req,
  input  logic                        i_noc_async_idle_init_mt_axi_ack,
  input  logic                        i_noc_async_idle_targ_mt_axi_ack,
  input  logic                        i_noc_async_idle_targ_cfg_dbi_axi_ack,
  input  logic                        i_noc_async_idle_targ_cfg_apb_ack,
  input  logic                        i_noc_async_idle_init_mt_axi_val,
  input  logic                        i_noc_async_idle_targ_mt_axi_val,
  input  logic                        i_noc_async_idle_targ_cfg_dbi_axi_val,
  input  logic                        i_noc_async_idle_targ_cfg_apb_val,
  output logic                        o_noc_init_mt_axi_clken,
  output logic                        o_noc_targ_mt_axi_clken,
  output logic                        o_noc_targ_cfg_dbi_axi_clken,
  output logic                        o_noc_targ_cfg_apb_clken,

  // PCIe Auxilary Clock
  input  wire                         i_pcie_aux_clk,

  // AXI Clock and Reset Signals
  input  wire                         i_pcie_init_mt_axi_clk,
  input  wire                         i_pcie_targ_mt_axi_clk,
  input  wire                         i_pcie_targ_cfg_dbi_axi_clk,
  output wire                         o_pcie_init_mt_axi_rst_n,
  output wire                         o_pcie_targ_mt_axi_rst_n,
  output wire                         o_pcie_targ_cfg_dbi_axi_rst_n,

  // APB Clock
  input  wire                         i_pcie_targ_cfg_apb_clk,
  output wire                         o_pcie_targ_cfg_apb_rst_n,

  // PHY Alternative Clock
  input  wire                         i_ref_alt_clk_p,

  // PHY Pads
  inout  wire                         io_pcie_resref,
  input  wire                         i_ref_pad_clk_p,
  input  wire                         i_ref_pad_clk_m,
  input  logic                        i_pcie_rxm_00,
  input  logic                        i_pcie_rxm_01,
  input  logic                        i_pcie_rxm_02,
  input  logic                        i_pcie_rxm_03,
  input  logic                        i_pcie_rxp_00,
  input  logic                        i_pcie_rxp_01,
  input  logic                        i_pcie_rxp_02,
  input  logic                        i_pcie_rxp_03,
  output logic                        o_pcie_txm_00,
  output logic                        o_pcie_txm_01,
  output logic                        o_pcie_txm_02,
  output logic                        o_pcie_txm_03,
  output logic                        o_pcie_txp_00,
  output logic                        o_pcie_txp_01,
  output logic                        o_pcie_txp_02,
  output logic                        o_pcie_txp_03,

  // AXI M Interface Signals
  // AW
  output logic                        o_pcie_init_mt_axi_awvalid,
  output pcie_init_mt_axi_id_t        o_pcie_init_mt_axi_awid,
  output chip_axi_addr_t              o_pcie_init_mt_axi_awaddr,
  output axi_len_t                    o_pcie_init_mt_axi_awlen,
  output axi_size_t                   o_pcie_init_mt_axi_awsize,
  output axi_burst_t                  o_pcie_init_mt_axi_awburst,
  output logic                        o_pcie_init_mt_axi_awlock,
  output axi_cache_t                  o_pcie_init_mt_axi_awcache,
  output axi_prot_t                   o_pcie_init_mt_axi_awprot,
  output axi_qos_t                    o_pcie_init_mt_axi_awqos,
  output axi_region_t                 o_pcie_init_mt_axi_awregion,
  output chip_axi_mt_awuser_t         o_pcie_init_mt_axi_awuser,
  input  logic                        i_pcie_init_mt_axi_awready,
  // W
  output logic                        o_pcie_init_mt_axi_wvalid,
  output pcie_init_mt_axi_data_t      o_pcie_init_mt_axi_wdata,
  output pcie_init_mt_axi_strb_t      o_pcie_init_mt_axi_wstrb,
  output logic                        o_pcie_init_mt_axi_wlast,
  output chip_axi_mt_wuser_t          o_pcie_init_mt_axi_wuser,
  input  logic                        i_pcie_init_mt_axi_wready,
  // B
  input  logic                        i_pcie_init_mt_axi_bvalid,
  input  pcie_init_mt_axi_id_t        i_pcie_init_mt_axi_bid,
  input  axi_resp_t                   i_pcie_init_mt_axi_bresp,
  input  chip_axi_mt_buser_t          i_pcie_init_mt_axi_buser,
  output logic                        o_pcie_init_mt_axi_bready,
  // AR
  output logic                        o_pcie_init_mt_axi_arvalid,
  output pcie_init_mt_axi_id_t        o_pcie_init_mt_axi_arid,
  output chip_axi_addr_t              o_pcie_init_mt_axi_araddr,
  output axi_len_t                    o_pcie_init_mt_axi_arlen,
  output axi_size_t                   o_pcie_init_mt_axi_arsize,
  output axi_burst_t                  o_pcie_init_mt_axi_arburst,
  output logic                        o_pcie_init_mt_axi_arlock,
  output axi_cache_t                  o_pcie_init_mt_axi_arcache,
  output axi_prot_t                   o_pcie_init_mt_axi_arprot,
  output axi_qos_t                    o_pcie_init_mt_axi_arqos,
  output axi_region_t                 o_pcie_init_mt_axi_arregion,
  output chip_axi_mt_aruser_t         o_pcie_init_mt_axi_aruser,
  input  logic                        i_pcie_init_mt_axi_arready,
  // R
  input  logic                        i_pcie_init_mt_axi_rvalid,
  input  pcie_init_mt_axi_id_t        i_pcie_init_mt_axi_rid,
  input  pcie_init_mt_axi_data_t      i_pcie_init_mt_axi_rdata,
  input  axi_resp_t                   i_pcie_init_mt_axi_rresp,
  input  logic                        i_pcie_init_mt_axi_rlast,
  input  chip_axi_mt_ruser_t          i_pcie_init_mt_axi_ruser,
  output logic                        o_pcie_init_mt_axi_rready,
  
  // AXI S Interface Signals
  // AW
  input  logic                        i_pcie_targ_mt_axi_awvalid,
  input  pcie_targ_mt_axi_id_t        i_pcie_targ_mt_axi_awid,
  input  chip_axi_addr_t              i_pcie_targ_mt_axi_awaddr,
  input  axi_len_t                    i_pcie_targ_mt_axi_awlen,
  input  axi_size_t                   i_pcie_targ_mt_axi_awsize,
  input  axi_burst_t                  i_pcie_targ_mt_axi_awburst,
  input  logic                        i_pcie_targ_mt_axi_awlock,
  input  axi_cache_t                  i_pcie_targ_mt_axi_awcache,
  input  axi_prot_t                   i_pcie_targ_mt_axi_awprot,
  input  axi_qos_t                    i_pcie_targ_mt_axi_awqos,
  input  axi_region_t                 i_pcie_targ_mt_axi_awregion,
  input  chip_axi_mt_awuser_t         i_pcie_targ_mt_axi_awuser,
  output logic                        o_pcie_targ_mt_axi_awready,
  // W
  input  logic                        i_pcie_targ_mt_axi_wvalid,
  input  pcie_targ_mt_axi_data_t      i_pcie_targ_mt_axi_wdata,
  input  pcie_targ_mt_axi_strb_t      i_pcie_targ_mt_axi_wstrb,
  input  logic                        i_pcie_targ_mt_axi_wlast,
  input  chip_axi_mt_wuser_t          i_pcie_targ_mt_axi_wuser,
  output logic                        o_pcie_targ_mt_axi_wready,
  // B
  output logic                        o_pcie_targ_mt_axi_bvalid,
  output pcie_targ_mt_axi_id_t        o_pcie_targ_mt_axi_bid,
  output axi_resp_t                   o_pcie_targ_mt_axi_bresp,
  output chip_axi_mt_buser_t          o_pcie_targ_mt_axi_buser,
  input  logic                        i_pcie_targ_mt_axi_bready,
  // AR
  input  logic                        i_pcie_targ_mt_axi_arvalid,
  input  pcie_targ_mt_axi_id_t        i_pcie_targ_mt_axi_arid,
  input  chip_axi_addr_t              i_pcie_targ_mt_axi_araddr,
  input  axi_len_t                    i_pcie_targ_mt_axi_arlen,
  input  axi_size_t                   i_pcie_targ_mt_axi_arsize,
  input  axi_burst_t                  i_pcie_targ_mt_axi_arburst,
  input  logic                        i_pcie_targ_mt_axi_arlock,
  input  axi_cache_t                  i_pcie_targ_mt_axi_arcache,
  input  axi_prot_t                   i_pcie_targ_mt_axi_arprot,
  input  axi_qos_t                    i_pcie_targ_mt_axi_arqos,
  input  axi_region_t                 i_pcie_targ_mt_axi_arregion,
  input  chip_axi_mt_aruser_t         i_pcie_targ_mt_axi_aruser,
  output logic                        o_pcie_targ_mt_axi_arready,
  // R
  output logic                        o_pcie_targ_mt_axi_rvalid,
  output pcie_targ_mt_axi_id_t        o_pcie_targ_mt_axi_rid,
  output pcie_targ_mt_axi_data_t      o_pcie_targ_mt_axi_rdata,
  output axi_resp_t                   o_pcie_targ_mt_axi_rresp,
  output logic                        o_pcie_targ_mt_axi_rlast,
  output chip_axi_mt_ruser_t          o_pcie_targ_mt_axi_ruser,
  input  logic                        i_pcie_targ_mt_axi_rready,

  // AXI S DBI Interface Signals
  // AW
  input  logic                        i_pcie_targ_cfg_dbi_axi_awvalid,
  input  pcie_targ_cfg_dbi_axi_id_t   i_pcie_targ_cfg_dbi_axi_awid,
  input  chip_axi_addr_t              i_pcie_targ_cfg_dbi_axi_awaddr,
  input  axi_len_t                    i_pcie_targ_cfg_dbi_axi_awlen,
  input  axi_size_t                   i_pcie_targ_cfg_dbi_axi_awsize,
  input  axi_burst_t                  i_pcie_targ_cfg_dbi_axi_awburst,
  input  logic                        i_pcie_targ_cfg_dbi_axi_awlock,
  input  axi_cache_t                  i_pcie_targ_cfg_dbi_axi_awcache,
  input  axi_prot_t                   i_pcie_targ_cfg_dbi_axi_awprot,
  input  axi_qos_t                    i_pcie_targ_cfg_dbi_axi_awqos,
  input  axi_region_t                 i_pcie_targ_cfg_dbi_axi_awregion,
  input  chip_axi_lt_awuser_t         i_pcie_targ_cfg_dbi_axi_awuser,
  output logic                        o_pcie_targ_cfg_dbi_axi_awready,
  // W
  input  logic                        i_pcie_targ_cfg_dbi_axi_wvalid,
  input  pcie_targ_cfg_dbi_axi_data_t i_pcie_targ_cfg_dbi_axi_wdata,
  input  pcie_targ_cfg_dbi_axi_strb_t i_pcie_targ_cfg_dbi_axi_wstrb,
  input  logic                        i_pcie_targ_cfg_dbi_axi_wlast,
  input  chip_axi_lt_wuser_t          i_pcie_targ_cfg_dbi_axi_wuser,
  output logic                        o_pcie_targ_cfg_dbi_axi_wready,
  // B
  output logic                        o_pcie_targ_cfg_dbi_axi_bvalid,
  output pcie_targ_cfg_dbi_axi_id_t   o_pcie_targ_cfg_dbi_axi_bid,
  output axi_resp_t                   o_pcie_targ_cfg_dbi_axi_bresp,
  output chip_axi_lt_buser_t          o_pcie_targ_cfg_dbi_axi_buser,
  input  logic                        i_pcie_targ_cfg_dbi_axi_bready,
  // AR
  input  logic                        i_pcie_targ_cfg_dbi_axi_arvalid,
  input  pcie_targ_cfg_dbi_axi_id_t   i_pcie_targ_cfg_dbi_axi_arid,
  input  chip_axi_addr_t              i_pcie_targ_cfg_dbi_axi_araddr,
  input  axi_len_t                    i_pcie_targ_cfg_dbi_axi_arlen,
  input  axi_size_t                   i_pcie_targ_cfg_dbi_axi_arsize,
  input  axi_burst_t                  i_pcie_targ_cfg_dbi_axi_arburst,
  input  logic                        i_pcie_targ_cfg_dbi_axi_arlock,
  input  axi_cache_t                  i_pcie_targ_cfg_dbi_axi_arcache,
  input  axi_prot_t                   i_pcie_targ_cfg_dbi_axi_arprot,
  input  axi_qos_t                    i_pcie_targ_cfg_dbi_axi_arqos,
  input  axi_region_t                 i_pcie_targ_cfg_dbi_axi_arregion,
  input  chip_axi_lt_aruser_t         i_pcie_targ_cfg_dbi_axi_aruser,
  output logic                        o_pcie_targ_cfg_dbi_axi_arready,
  // R
  output logic                        o_pcie_targ_cfg_dbi_axi_rvalid,
  output pcie_targ_cfg_dbi_axi_id_t   o_pcie_targ_cfg_dbi_axi_rid,
  output pcie_targ_cfg_dbi_axi_data_t o_pcie_targ_cfg_dbi_axi_rdata,
  output axi_resp_t                   o_pcie_targ_cfg_dbi_axi_rresp,
  output logic                        o_pcie_targ_cfg_dbi_axi_rlast,
  output chip_axi_lt_ruser_t          o_pcie_targ_cfg_dbi_axi_ruser,
  input  logic                        i_pcie_targ_cfg_dbi_axi_rready,

  // APB Config Interface Signals
  input  pcie_targ_cfg_apb3_addr_t    i_pcie_targ_cfg_apb_paddr,
  input  pcie_targ_cfg_apb3_data_t    i_pcie_targ_cfg_apb_pwdata,
  input  logic                        i_pcie_targ_cfg_apb_pwrite,
  input  logic                        i_pcie_targ_cfg_apb_psel,
  input  logic                        i_pcie_targ_cfg_apb_penable,
  input  pcie_targ_cfg_apb3_strb_t    i_pcie_targ_cfg_apb_pstrb,
  input  logic [2:0]                  i_pcie_targ_cfg_apb_pprot,
  output logic                        o_pcie_targ_cfg_apb_pready,
  output pcie_targ_cfg_apb3_data_t    o_pcie_targ_cfg_apb_prdata,
  output logic                        o_pcie_targ_cfg_apb_pslverr,

  // APB SysConfig Interface Signals
  input  chip_syscfg_addr_t           i_pcie_targ_syscfg_apb_paddr,
  input  chip_apb_syscfg_data_t       i_pcie_targ_syscfg_apb_pwdata,
  input  logic                        i_pcie_targ_syscfg_apb_pwrite,
  input  logic                        i_pcie_targ_syscfg_apb_psel,
  input  logic                        i_pcie_targ_syscfg_apb_penable,
  input  chip_apb_syscfg_strb_t       i_pcie_targ_syscfg_apb_pstrb,
  input  logic [2:0]                  i_pcie_targ_syscfg_apb_pprot,
  output logic                        o_pcie_targ_syscfg_apb_pready,
  output chip_apb_syscfg_data_t       o_pcie_targ_syscfg_apb_prdata,
  output logic                        o_pcie_targ_syscfg_apb_pslverr,

  // Interrupts
  output logic                        o_pcie_int,

  // Observability signals for PCIe
  output logic [15:0]                 o_pcie_obs,

  /////////////////////////////////////////////
  // DFT
  /////////////////////////////////////////////

  // JTAG
  input  wire                         tck,
  input  wire                         trst,
  input  logic                        tms,
  input  logic                        tdi,
  output logic                        tdo_en,
  output logic                        tdo,

  // SCAN
  input  wire                         ssn_bus_clk,
  input  logic  [               24:0] ssn_bus_data_in,
  output logic  [               24:0] ssn_bus_data_out,
  
  // BIST
  input  wire                         bisr_clk,
  input  wire                         bisr_reset,
  input  logic                        bisr_shift_en,
  input  logic                        bisr_si,
  output logic                        bisr_so
);

  // AO CSR
  pctl_ao_csr_reg_pkg::apb_h2d_t      ao_csr_apb_req;
  pctl_ao_csr_reg_pkg::apb_d2h_t      ao_csr_apb_rsp;
  logic                               ao_csr_apb_rst_n;
  pcie_csr_reg_pkg::pcie_csr_reg2hw_t pcie_reg2hw;
  pcie_csr_reg_pkg::pcie_csr_hw2reg_t pcie_hw2reg;

  // Internal Clocks and Resets
  wire aux_clk;
  wire power_up_rst_n;
  wire pcie_perst_n_inp;
  wire phy_fw_clk;                 // 300MHz clock derived from i_pcie_init_mt_axi_clk
  wire pcie_init_mt_axi_aclk;
  wire mstr_aclk;
  wire pcie_targ_mt_axi_aclk;
  wire slv_aclk;
  wire pcie_targ_cfg_dbi_axi_aclk;
  wire dbi_aclk;
  wire apb_pclk;
  wire pcie_core_clk_oup;
  wire pcie_core_clk_div2;
  wire pcie_core_clk_div4;
  wire pcie_core_clk_div8;
  wire pcie_muxd_aux_clk_oup;
  wire pcie_muxd_aux_clk_div2;
  wire pcie_muxd_aux_clk_div4;
  wire pcie_muxd_aux_clk_div8;
  wire pcie_core_rst_n_oup;
  wire pcie_pwr_rst_n_oup;

  // Power Management intermediate signals
  logic pcie_clkreq_in_n;
  logic pcie_local_ref_clk_req_n;

  // Debug Outputs intermediate signals
  logic [15:0] pcie_dbg_signal;
  logic [ 1:0] pcie_phy0_dtb_out;

  //////////////////////////////////
  // AXI intermediate signals
  //////////////////////////////////

  // AXI M Interface
  // AW channel
  logic                   spreg_o_axi_m_awvalid;
  pcie_init_mt_axi_id_t   spreg_o_axi_m_awid;
  logic [63:0]            spreg_o_axi_m_awaddr;
  axi_len_t               spreg_o_axi_m_awlen;
  axi_size_t              spreg_o_axi_m_awsize;
  axi_burst_t             spreg_o_axi_m_awburst;
  logic                   spreg_o_axi_m_awlock;
  axi_cache_t             spreg_o_axi_m_awcache;
  axi_prot_t              spreg_o_axi_m_awprot;
  axi_qos_t               spreg_o_axi_m_awqos;
  logic                   spreg_i_axi_m_awready;
  // W channel
  logic                   spreg_o_axi_m_wvalid;
  pcie_init_mt_axi_data_t spreg_o_axi_m_wdata;
  pcie_init_mt_axi_strb_t spreg_o_axi_m_wstrb;
  logic                   spreg_o_axi_m_wlast;
  logic                   spreg_i_axi_m_wready;
  // B channel
  logic                   spreg_i_axi_m_bvalid;
  pcie_init_mt_axi_id_t   spreg_i_axi_m_bid;
  axi_resp_t              spreg_i_axi_m_bresp;
  logic                   spreg_o_axi_m_bready;
  // AR channel
  logic                   spreg_o_axi_m_arvalid;
  pcie_init_mt_axi_id_t   spreg_o_axi_m_arid;
  logic [63:0]            spreg_o_axi_m_araddr;
  axi_len_t               spreg_o_axi_m_arlen;
  axi_size_t              spreg_o_axi_m_arsize;
  axi_burst_t             spreg_o_axi_m_arburst;
  logic                   spreg_o_axi_m_arlock;
  axi_cache_t             spreg_o_axi_m_arcache;
  axi_prot_t              spreg_o_axi_m_arprot;
  axi_qos_t               spreg_o_axi_m_arqos;
  logic                   spreg_i_axi_m_arready;
  // R channel
  logic                   spreg_i_axi_m_rvalid;
  pcie_init_mt_axi_id_t   spreg_i_axi_m_rid;
  pcie_init_mt_axi_data_t spreg_i_axi_m_rdata;
  axi_resp_t              spreg_i_axi_m_rresp;
  logic                   spreg_i_axi_m_rlast;
  logic                   spreg_o_axi_m_rready;
     
  // AXI S Interface     
  // AW channel     
  logic                   spreg_i_axi_s_awvalid;
  pcie_targ_mt_axi_id_t   spreg_i_axi_s_awid;
  chip_axi_addr_t         spreg_i_axi_s_awaddr;
  axi_len_t               spreg_i_axi_s_awlen;
  axi_size_t              spreg_i_axi_s_awsize;
  axi_burst_t             spreg_i_axi_s_awburst;
  logic                   spreg_i_axi_s_awlock;
  axi_cache_t             spreg_i_axi_s_awcache;
  axi_prot_t              spreg_i_axi_s_awprot;
  axi_qos_t               spreg_i_axi_s_awqos;
  logic                   spreg_o_axi_s_awready;
  // W channel
  logic                   spreg_i_axi_s_wvalid;
  pcie_targ_mt_axi_data_t spreg_i_axi_s_wdata;
  pcie_targ_mt_axi_strb_t spreg_i_axi_s_wstrb;
  logic                   spreg_i_axi_s_wlast;
  logic                   spreg_o_axi_s_wready;
  // B channel
  logic                   spreg_o_axi_s_bvalid;
  pcie_targ_mt_axi_id_t   spreg_o_axi_s_bid;
  axi_resp_t              spreg_o_axi_s_bresp;
  logic                   spreg_i_axi_s_bready;
  // AR channel
  logic                   spreg_i_axi_s_arvalid;
  pcie_targ_mt_axi_id_t   spreg_i_axi_s_arid;
  chip_axi_addr_t         spreg_i_axi_s_araddr;
  axi_len_t               spreg_i_axi_s_arlen;
  axi_size_t              spreg_i_axi_s_arsize;
  axi_burst_t             spreg_i_axi_s_arburst;
  logic                   spreg_i_axi_s_arlock;
  axi_cache_t             spreg_i_axi_s_arcache;
  axi_prot_t              spreg_i_axi_s_arprot;
  axi_qos_t               spreg_i_axi_s_arqos;
  logic                   spreg_o_axi_s_arready;
  // R channel
  logic                   spreg_o_axi_s_rvalid;
  pcie_targ_mt_axi_id_t   spreg_o_axi_s_rid;
  pcie_targ_mt_axi_data_t spreg_o_axi_s_rdata;
  axi_resp_t              spreg_o_axi_s_rresp;
  logic                   spreg_o_axi_s_rlast;
  logic                   spreg_i_axi_s_rready;

  // DBI AXI S Interface
  // AW channel
  logic                        spreg_i_dbi_awvalid;
  pcie_targ_cfg_dbi_axi_id_t   spreg_i_dbi_awid;
  chip_axi_addr_t              spreg_i_dbi_awaddr;
  axi_len_t                    spreg_i_dbi_awlen;
  axi_size_t                   spreg_i_dbi_awsize;
  axi_burst_t                  spreg_i_dbi_awburst;
  logic                        spreg_i_dbi_awlock;
  axi_cache_t                  spreg_i_dbi_awcache;
  axi_prot_t                   spreg_i_dbi_awprot;
  axi_qos_t                    spreg_i_dbi_awqos;
  logic                        spreg_o_dbi_awready;
  // W channel
  logic                        spreg_i_dbi_wvalid;
  pcie_targ_cfg_dbi_axi_data_t spreg_i_dbi_wdata;
  pcie_targ_cfg_dbi_axi_strb_t spreg_i_dbi_wstrb;
  logic                        spreg_i_dbi_wlast;
  logic                        spreg_o_dbi_wready;
  // B channel
  logic                        spreg_o_dbi_bvalid;
  pcie_targ_cfg_dbi_axi_id_t   spreg_o_dbi_bid;
  axi_resp_t                   spreg_o_dbi_bresp;
  logic                        spreg_i_dbi_bready;
  // AR channel
  logic                        spreg_i_dbi_arvalid;
  pcie_targ_cfg_dbi_axi_id_t   spreg_i_dbi_arid;
  chip_axi_addr_t              spreg_i_dbi_araddr;
  axi_len_t                    spreg_i_dbi_arlen;
  axi_size_t                   spreg_i_dbi_arsize;
  axi_burst_t                  spreg_i_dbi_arburst;
  logic                        spreg_i_dbi_arlock;
  axi_cache_t                  spreg_i_dbi_arcache;
  axi_prot_t                   spreg_i_dbi_arprot;
  axi_qos_t                    spreg_i_dbi_arqos;
  logic                        spreg_o_dbi_arready;
  // R channel
  logic                        spreg_o_dbi_rvalid;
  pcie_targ_cfg_dbi_axi_id_t   spreg_o_dbi_rid;
  pcie_targ_cfg_dbi_axi_data_t spreg_o_dbi_rdata;
  axi_resp_t                   spreg_o_dbi_rresp;
  logic                        spreg_o_dbi_rlast;
  logic                        spreg_i_dbi_rready;
  
  //////////////////////////////////
  // DFT intermediate signals
  //////////////////////////////////

  // SRAM Control Signals
  logic ret;
  logic pde;
  logic scan_en = 1'b0;
  logic prn;

  // Scan clocks
  wire phy0_mplla_word_fr_clk; // 1000MHz clock from PHY PLL
  wire pcie_scan_clk_500;      // 500MHz clock derived from phy0_mplla_word_fr_clk

  // Main Test Enable
  logic test_mode = 1'b0;

  // PCIe Controller Scan Signals
  logic mac_scan_mode;
  logic mac_scan_rst_n;
  logic mac_scan_shift;
  logic mac_scan_shift_cg;
  wire  mac_scan_coreclk;

  // PHY Test Control signals
  logic tap_phy0_ref_use_pad;
  logic tap_phy0_reset;
  logic ate_test_mode;
  logic phy_test_burnin;
  logic phy_test_powerdown;
  logic phy_test_stop_clk_en;
  logic phy_test_tx_ref_clk_en;
  logic phy0_test_flyover_en;

  // PHY Boundary Scan Port Signals
  logic       phy_bs_acmode;
  logic       phy_bs_actest;
  logic       phy_bs_cdr;
  logic       phy_bs_ce;
  logic       phy_bs_rx_bigswing;
  logic       phy_bs_rx_init;
  logic [4:0] phy_bs_rx_level;
  logic       phy_bs_sdr;
  logic       phy_bs_tdi;
  logic       phy_bs_tdo;
  logic       phy_bs_tx_lowswing;
  logic       phy_bs_udr;

  // PHY PCS Scan Interface
  wire  pcs_scan_clk;
  logic pcs_scan_clk_sel;
  logic pcs_scan_mode;
  wire  pcs_scan_pclk;
  wire  pcs_scan_pcs_clk;
  wire  pcs_scan_pma_clk;
  logic pcs_scan_rst;
  logic pcs_scan_shift;
  logic pcs_scan_shift_cg;
  
  // PHY Scan Interface
  logic phy0_scan_mode;
  wire  phy0_scan_clk;
  logic phy0_scan_clk_sel;
  logic phy0_scan_cr_clk;
  wire  phy0_scan_mpll_dword_clk;
  wire  phy0_scan_mpll_qword_clk;
  wire  phy0_scan_rx_dword_clk;
  wire  phy0_scan_occ_clk;
  wire  phy0_scan_ref_clk;
  logic phy0_scan_set_rst;
  logic phy0_scan_shift;
  logic phy0_scan_shift_cg;
  logic phy0_scan_pma_occ_en;
  
  logic [PHY_SCAN_CR-1:0]         phy0_scan_cr_in;
  logic [PHY_SCAN_CR-1:0]         phy0_scan_cr_out;
  logic [PHY_SCAN_MPLL_DWORD-1:0] phy0_scan_mpll_dword_in;
  logic [PHY_SCAN_MPLL_DWORD-1:0] phy0_scan_mpll_dword_out;
  logic [PHY_SCAN_MPLL_QWORD-1:0] phy0_scan_mpll_qword_in;
  logic [PHY_SCAN_MPLL_QWORD-1:0] phy0_scan_mpll_qword_out;
  logic [PHY_SCAN_RX_DWORD-1:0]   phy0_scan_rx_dword_in;
  logic [PHY_SCAN_RX_DWORD-1:0]   phy0_scan_rx_dword_out;
  logic [PHY_SCAN_OCC-1:0]        phy0_scan_occ_in;
  logic [PHY_SCAN_OCC-1:0]        phy0_scan_occ_out;
  logic [PHY_SCAN_REF-1:0]        phy0_scan_ref_in;
  logic [PHY_SCAN_REF-1:0]        phy0_scan_ref_out;
  
  logic [              1:0] phy0_scan_apb0_in;
  logic [              1:0] phy0_scan_apb0_out;
  logic                     phy0_scan_apb1_in;
  logic                     phy0_scan_apb1_out;
  logic                     phy0_scan_fw_in;
  logic                     phy0_scan_fw_out;
  logic [PHY_SCAN_JTAG-1:0] phy0_scan_jtag_in;
  logic [PHY_SCAN_JTAG-1:0] phy0_scan_jtag_out;

  pctl #(
    .N_FAST_CLKS          (N_FAST_CLKS),
    .N_RESETS             (1),
    .N_MEM_PG             (1),
    .N_FENCES             (N_FENCES),
    .N_THROTTLE_PINS      (0),
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
    .i_pll_clk            ({i_pcie_init_mt_axi_clk, i_pcie_targ_mt_axi_clk, i_pcie_targ_cfg_dbi_axi_clk}),
    .o_partition_clk      ({pcie_init_mt_axi_aclk, pcie_targ_mt_axi_aclk, pcie_targ_cfg_dbi_axi_aclk}),
    .o_partition_rst_n    (power_up_rst_n),
    .o_ao_rst_sync_n      (ao_csr_apb_rst_n),
    // Isolation interface
    .o_noc_async_idle_req ({o_noc_async_idle_init_mt_axi_req, o_noc_async_idle_targ_mt_axi_req, o_noc_async_idle_targ_cfg_dbi_axi_req, o_noc_async_idle_targ_cfg_apb_req}),
    .i_noc_async_idle_ack ({i_noc_async_idle_init_mt_axi_ack, i_noc_async_idle_targ_mt_axi_ack, i_noc_async_idle_targ_cfg_dbi_axi_ack, i_noc_async_idle_targ_cfg_apb_ack}),
    .i_noc_async_idle_val ({i_noc_async_idle_init_mt_axi_val, i_noc_async_idle_targ_mt_axi_val, i_noc_async_idle_targ_cfg_dbi_axi_val, i_noc_async_idle_targ_cfg_apb_val}),
    .o_noc_clken          ({o_noc_init_mt_axi_clken, o_noc_targ_mt_axi_clken, o_noc_targ_cfg_dbi_axi_clken, o_noc_targ_cfg_apb_clken}),
    .o_noc_rst_n          (),                    // ASO-UNUSED_OUTPUT: pcie doesn't use noc_rst_n, but uses internaly generated resets for each fence instead
    // IRQs
    .o_int_shutdown_req   (),                    // ASO-UNUSED_OUTPUT: pcie doesn't use shutdown irq
    .i_int_shutdown_ack   (1'b0),                // Not needed
    // SRAM configuration
    .o_ret                (ret),
    .o_pde                (pde),
    .i_prn                (prn),
    // Sync interface
    .i_global_sync_async  (1'b0),                // Not needed
    .o_global_sync        (),                    // ASO-UNUSED_OUTPUT: pcie doesn't use sync interface
    // Throttle inputs
    .i_throttle           (1'b0),
    /////////////////////////////////////////////
    // SYS_CFG Bus
    /////////////////////////////////////////////
    .i_cfg_apb4_s_paddr   (i_pcie_targ_syscfg_apb_paddr  ),
    .i_cfg_apb4_s_pwdata  (i_pcie_targ_syscfg_apb_pwdata ),
    .i_cfg_apb4_s_pwrite  (i_pcie_targ_syscfg_apb_pwrite ),
    .i_cfg_apb4_s_psel    (i_pcie_targ_syscfg_apb_psel   ),
    .i_cfg_apb4_s_penable (i_pcie_targ_syscfg_apb_penable),
    .i_cfg_apb4_s_pstrb   (i_pcie_targ_syscfg_apb_pstrb  ),
    .i_cfg_apb4_s_pprot   (i_pcie_targ_syscfg_apb_pprot  ),
    .o_cfg_apb4_s_pready  (o_pcie_targ_syscfg_apb_pready ),
    .o_cfg_apb4_s_prdata  (o_pcie_targ_syscfg_apb_prdata ),
    .o_cfg_apb4_s_pslverr (o_pcie_targ_syscfg_apb_pslverr),
    // External APB interface
    .o_ao_csr_apb_req     (ao_csr_apb_req),
    .i_ao_csr_apb_rsp     (ao_csr_apb_rsp)
  );

  // AO CSR
  pcie_csr_reg_top u_pcie_ao_csr (
    .clk_i    (i_ref_clk),
    .rst_ni   (ao_csr_apb_rst_n),
    .apb_i    (ao_csr_apb_req),
    .apb_o    (ao_csr_apb_rsp),
    .reg2hw   (pcie_reg2hw),
    .hw2reg   (pcie_hw2reg),
    .devmode_i(1'b1)
  );

  assign pcie_perst_n_inp = i_ao_rst_n & pcie_reg2hw.perst_n;
  assign o_pcie_targ_cfg_apb_rst_n = power_up_rst_n & pcie_perst_n_inp;

  // AO CSR Syncronization
  axe_tcl_seq_sync #(
    .SyncStages(PCIE_SYNC_STAGES),
    .ResetValue(1)
  ) u_clkreq_in_n_sync (
    .i_clk   (pcie_muxd_aux_clk_oup),
    .i_rst_n (pcie_pwr_rst_n_oup),
    .i_d     (pcie_reg2hw.clkreq_control),
    .o_q     (pcie_clkreq_in_n)
  );
  axe_tcl_seq_sync #(
    .SyncStages(PCIE_SYNC_STAGES),
    .ResetValue(1)
  ) u_local_ref_clk_req_n_sync (
    .i_clk   (i_ref_clk),
    .i_rst_n (i_ao_rst_n),
    .i_d     (pcie_local_ref_clk_req_n),
    .o_q     (pcie_hw2reg.local_refclk_req_status.d)
  );
  axe_tcl_seq_sync #(
    .SyncStages(PCIE_SYNC_STAGES),
    .ResetValue(1)
  ) u_core_rst_n_sync (
    .i_clk   (i_ref_clk),
    .i_rst_n (i_ao_rst_n),
    .i_d     (pcie_core_rst_n_oup),
    .o_q     (pcie_hw2reg.rst_status.o_core_rst_n.d)
  );
  axe_tcl_seq_sync #(
    .SyncStages(PCIE_SYNC_STAGES),
    .ResetValue(1)
  ) u_pwr_rst_n_sync (
    .i_clk   (i_ref_clk),
    .i_rst_n (i_ao_rst_n),
    .i_d     (pcie_pwr_rst_n_oup),
    .o_q     (pcie_hw2reg.rst_status.o_pwr_rst_n.d)
  );
  axe_tcl_seq_sync #(
    .SyncStages(PCIE_SYNC_STAGES),
    .ResetValue(1)
  ) u_mstr_aresetn_sync (
    .i_clk   (i_ref_clk),
    .i_rst_n (i_ao_rst_n),
    .i_d     (o_pcie_init_mt_axi_rst_n),
    .o_q     (pcie_hw2reg.rst_status.o_mstr_aresetn.d)
  );
  axe_tcl_seq_sync #(
    .SyncStages(PCIE_SYNC_STAGES),
    .ResetValue(1)
  ) u_slv_aresetn_sync (
    .i_clk   (i_ref_clk),
    .i_rst_n (i_ao_rst_n),
    .i_d     (o_pcie_targ_mt_axi_rst_n),
    .o_q     (pcie_hw2reg.rst_status.o_slv_aresetn.d)
  );
  axe_tcl_seq_sync #(
    .SyncStages(PCIE_SYNC_STAGES),
    .ResetValue(1)
  ) u_dbi_aresetn_sync (
    .i_clk   (i_ref_clk),
    .i_rst_n (i_ao_rst_n),
    .i_d     (o_pcie_targ_cfg_dbi_axi_rst_n),
    .o_q     (pcie_hw2reg.rst_status.o_dbi_aresetn.d)
  );

  // Observation mux and clock output dividers
    axe_ccl_clk_div_by_2 u_pcie_core_clk_d2 (
    .i_clk       ( pcie_core_clk_oup          ),
    .i_rst_n     ( i_ao_rst_n                 ), // Always on reset
    .i_test_mode ( 1'b0                       ),
    .i_enable    ( 1'b1                       ),
    .o_clk       ( pcie_core_clk_div2         )
  );
  axe_ccl_clk_div_by_2 u_pcie_core_clk_d4 (
    .i_clk       ( pcie_core_clk_div2         ),
    .i_rst_n     ( i_ao_rst_n                 ), // Always on reset
    .i_test_mode ( 1'b0                       ),
    .i_enable    ( 1'b1                       ),
    .o_clk       ( pcie_core_clk_div4         )
  );
  axe_ccl_clk_div_by_2 u_pcie_core_clk_d8 (
    .i_clk       ( pcie_core_clk_div4         ),
    .i_rst_n     ( i_ao_rst_n                 ), // Always on reset
    .i_test_mode ( 1'b0                       ),
    .i_enable    ( 1'b1                       ),
    .o_clk       ( pcie_core_clk_div8         )
  );
  axe_ccl_clk_div_by_2 u_pcie_muxd_aux_clk_d2 (
    .i_clk       ( pcie_muxd_aux_clk_oup      ),
    .i_rst_n     ( i_ao_rst_n                 ), // Always on reset
    .i_test_mode ( 1'b0                       ),
    .i_enable    ( 1'b1                       ),
    .o_clk       ( pcie_muxd_aux_clk_div2     )
  );
  axe_ccl_clk_div_by_2 u_pcie_muxd_aux_clk_d4 (
    .i_clk       ( pcie_muxd_aux_clk_div2     ),
    .i_rst_n     ( i_ao_rst_n                 ), // Always on reset
    .i_test_mode ( 1'b0                       ),
    .i_enable    ( 1'b1                       ),
    .o_clk       ( pcie_muxd_aux_clk_div4     )
  );
  axe_ccl_clk_div_by_2 u_pcie_muxd_aux_clk_d8 (
    .i_clk       ( pcie_muxd_aux_clk_div4     ),
    .i_rst_n     ( i_ao_rst_n                 ), // Always on reset
    .i_test_mode ( 1'b0                       ),
    .i_enable    ( 1'b1                       ),
    .o_clk       ( pcie_muxd_aux_clk_div8     )
  );
  assign o_pcie_obs = (pcie_reg2hw.obs_control == "2'b00") ? pcie_dbg_signal :
                      (pcie_reg2hw.obs_control == "2'b01") ? {14'b0, pcie_phy0_dtb_out} :
                      (pcie_reg2hw.obs_control == "2'b10") ? {12'b0, pcie_core_clk_div8, pcie_muxd_aux_clk_div8, 
                                                              pcie_core_rst_n_oup, pcie_pwr_rst_n_oup} : 16'b0;

  // Scal clock dividers
  axe_ccl_clk_div_by_2 u_pcie_fast_axi_clk_d2 (
    .i_clk       ( pcie_init_mt_axi_aclk      ),
    .i_rst_n     ( i_ao_rst_n                 ), // Always on reset
    .i_test_mode ( 1'b0                       ),
    .i_enable    ( 1'b1                       ),
    .o_clk       ( phy_fw_clk                 )
  );
  axe_ccl_clk_div_by_2 u_phy0_mplla_word_fr_clk_d2 (
    .i_clk       ( phy0_mplla_word_fr_clk     ),
    .i_rst_n     ( i_ao_rst_n                 ), // Always on reset
    .i_test_mode ( 1'b0                       ),
    .i_enable    ( test_mode                  ),
    .o_clk       ( pcie_scan_clk_500          )
  );

  // Clock buffers to create clock definitions for generate subsystem clocks
  axe_tcl_clk_buffer u_aux_clk_buf (
    .i_clk (i_pcie_aux_clk),
    .o_clk (aux_clk)
  );
  axe_tcl_clk_buffer u_mstr_aclk_buf (
    .i_clk (pcie_init_mt_axi_aclk),
    .o_clk (mstr_aclk)
  );
  axe_tcl_clk_buffer u_slv_aclk_buf (
    .i_clk (pcie_targ_mt_axi_aclk),
    .o_clk (slv_aclk)
  );
  axe_tcl_clk_buffer u_dbi_aclk_buf (
    .i_clk (pcie_targ_cfg_dbi_axi_aclk),
    .o_clk (dbi_aclk)
  );
  axe_tcl_clk_buffer u_apb_pclk_buf (
    .i_clk (i_pcie_targ_cfg_apb_clk),
    .o_clk (apb_pclk)
  );

  assign pcs_scan_clk             = i_ref_alt_clk_p;
  assign pcs_scan_pclk            = phy0_mplla_word_fr_clk;
  assign pcs_scan_pcs_clk         = phy0_mplla_word_fr_clk;
  assign pcs_scan_pma_clk         = phy0_mplla_word_fr_clk;
  assign phy0_scan_clk            = i_ref_alt_clk_p;
  assign phy0_scan_cr_clk         = i_ref_alt_clk_p;
  assign phy0_scan_mpll_dword_clk = phy0_mplla_word_fr_clk;
  assign phy0_scan_mpll_qword_clk = pcie_scan_clk_500;
  assign phy0_scan_rx_dword_clk   = phy0_mplla_word_fr_clk;
  assign phy0_scan_occ_clk        = i_ref_alt_clk_p;
  assign phy0_scan_ref_clk        = i_ref_alt_clk_p;
  assign mac_scan_coreclk         = pcie_scan_clk_500;

  axe_axi_multicut_flat #(
    .NumCuts       (1                      ), // Number of cuts.
    .AxiIdWidth    (PCIE_INIT_MT_AXI_ID_W  ), // AXI ID Width
    .AxiAddrWidth  (CHIP_AXI_ADDR_W        ), // AXI Address Width
    .AxiDataWidth  (PCIE_INIT_MT_AXI_DATA_W), // AXI Data Width
    .AxiAwUserWidth(CHIP_AXI_MT_AWUSER_W   ), // AXI AW User Width
    .AxiWUserWidth (CHIP_AXI_MT_WUSER_W    ), // AXI  W User Width
    .AxiBUserWidth (CHIP_AXI_MT_BUSER_W    ), // AXI  B User Width
    .AxiArUserWidth(CHIP_AXI_MT_ARUSER_W   ), // AXI AR User Width
    .AxiRUserWidth (CHIP_AXI_MT_RUSER_W    )  // AXI  R User Width
  ) u_axi_m_cut (
    .i_clk             (pcie_init_mt_axi_aclk   ),
    .i_rst_n           (o_pcie_init_mt_axi_rst_n),
    //////////////////////
    // Subordinate Port //
    //////////////////////
    // AW
    .i_axi_s_aw_valid  (spreg_o_axi_m_awvalid    ),
    .i_axi_s_aw_id     (spreg_o_axi_m_awid       ),
    .i_axi_s_aw_addr   (spreg_o_axi_m_awaddr[CHIP_AXI_ADDR_W-1:0]),
    .i_axi_s_aw_len    (spreg_o_axi_m_awlen      ),
    .i_axi_s_aw_size   (spreg_o_axi_m_awsize     ),
    .i_axi_s_aw_burst  (spreg_o_axi_m_awburst    ),
    .i_axi_s_aw_lock   (spreg_o_axi_m_awlock     ),
    .i_axi_s_aw_cache  (spreg_o_axi_m_awcache    ),
    .i_axi_s_aw_prot   (spreg_o_axi_m_awprot     ),
    .i_axi_s_aw_qos    (spreg_o_axi_m_awqos      ),
    .i_axi_s_aw_region (axi_region_t'('0)        ), // Not needed
    .i_axi_s_aw_user   (chip_axi_mt_awuser_t'('0)), // Not needed
    .o_axi_s_aw_ready  (spreg_i_axi_m_awready    ),
    // W
    .i_axi_s_w_valid   (spreg_o_axi_m_wvalid     ),
    .i_axi_s_w_data    (spreg_o_axi_m_wdata      ),
    .i_axi_s_w_strb    (spreg_o_axi_m_wstrb      ),
    .i_axi_s_w_last    (spreg_o_axi_m_wlast      ),
    .i_axi_s_w_user    (chip_axi_mt_wuser_t'('0) ), // Not needed
    .o_axi_s_w_ready   (spreg_i_axi_m_wready     ),
    // B
    .o_axi_s_b_valid   (spreg_i_axi_m_bvalid     ),
    .o_axi_s_b_id      (spreg_i_axi_m_bid        ),
    .o_axi_s_b_resp    (spreg_i_axi_m_bresp      ),
    .o_axi_s_b_user    (                         ), // ASO-UNUSED_OUTPUT: pcie doesn't use buser
    .i_axi_s_b_ready   (spreg_o_axi_m_bready     ),
    // AR
    .i_axi_s_ar_valid  (spreg_o_axi_m_arvalid    ),
    .i_axi_s_ar_id     (spreg_o_axi_m_arid       ),
    .i_axi_s_ar_addr   (spreg_o_axi_m_araddr[CHIP_AXI_ADDR_W-1:0]),
    .i_axi_s_ar_len    (spreg_o_axi_m_arlen      ),
    .i_axi_s_ar_size   (spreg_o_axi_m_arsize     ),
    .i_axi_s_ar_burst  (spreg_o_axi_m_arburst    ),
    .i_axi_s_ar_lock   (spreg_o_axi_m_arlock     ),
    .i_axi_s_ar_cache  (spreg_o_axi_m_arcache    ),
    .i_axi_s_ar_prot   (spreg_o_axi_m_arprot     ),
    .i_axi_s_ar_qos    (spreg_o_axi_m_arqos      ),
    .i_axi_s_ar_region (axi_region_t'('0)        ), // Not needed
    .i_axi_s_ar_user   (chip_axi_mt_awuser_t'('0)), // Not needed
    .o_axi_s_ar_ready  (spreg_i_axi_m_arready    ),
    // R
    .o_axi_s_r_valid   (spreg_i_axi_m_rvalid     ),
    .o_axi_s_r_id      (spreg_i_axi_m_rid        ),
    .o_axi_s_r_data    (spreg_i_axi_m_rdata      ),
    .o_axi_s_r_resp    (spreg_i_axi_m_rresp      ),
    .o_axi_s_r_last    (spreg_i_axi_m_rlast      ),
    .o_axi_s_r_user    (                         ), // ASO-UNUSED_OUTPUT: pcie doesn't use ruser
    .i_axi_s_r_ready   (spreg_o_axi_m_rready     ),
    /////////////////////
    // Management Port //
    /////////////////////
    // AW
    .o_axi_m_aw_valid   (o_pcie_init_mt_axi_awvalid ),
    .o_axi_m_aw_id      (o_pcie_init_mt_axi_awid    ),
    .o_axi_m_aw_addr    (o_pcie_init_mt_axi_awaddr  ),
    .o_axi_m_aw_len     (o_pcie_init_mt_axi_awlen   ),
    .o_axi_m_aw_size    (o_pcie_init_mt_axi_awsize  ),
    .o_axi_m_aw_burst   (o_pcie_init_mt_axi_awburst ),
    .o_axi_m_aw_lock    (o_pcie_init_mt_axi_awlock  ),
    .o_axi_m_aw_cache   (o_pcie_init_mt_axi_awcache ),
    .o_axi_m_aw_prot    (o_pcie_init_mt_axi_awprot  ),
    .o_axi_m_aw_qos     (o_pcie_init_mt_axi_awqos   ),
    .o_axi_m_aw_region  (o_pcie_init_mt_axi_awregion),
    .o_axi_m_aw_user    (o_pcie_init_mt_axi_awuser  ),
    .i_axi_m_aw_ready   (i_pcie_init_mt_axi_awready ),
    // W
    .o_axi_m_w_valid    (o_pcie_init_mt_axi_wvalid  ),
    .o_axi_m_w_data     (o_pcie_init_mt_axi_wdata   ),
    .o_axi_m_w_strb     (o_pcie_init_mt_axi_wstrb   ),
    .o_axi_m_w_last     (o_pcie_init_mt_axi_wlast   ),
    .o_axi_m_w_user     (o_pcie_init_mt_axi_wuser   ),
    .i_axi_m_w_ready    (i_pcie_init_mt_axi_wready  ),
    // B
    .i_axi_m_b_valid    (i_pcie_init_mt_axi_bvalid  ),
    .i_axi_m_b_id       (i_pcie_init_mt_axi_bid     ),
    .i_axi_m_b_resp     (i_pcie_init_mt_axi_bresp   ),
    .i_axi_m_b_user     (i_pcie_init_mt_axi_buser   ),
    .o_axi_m_b_ready    (o_pcie_init_mt_axi_bready  ),
    // AR
    .o_axi_m_ar_valid   (o_pcie_init_mt_axi_arvalid ),
    .o_axi_m_ar_id      (o_pcie_init_mt_axi_arid    ),
    .o_axi_m_ar_addr    (o_pcie_init_mt_axi_araddr  ),
    .o_axi_m_ar_len     (o_pcie_init_mt_axi_arlen   ),
    .o_axi_m_ar_size    (o_pcie_init_mt_axi_arsize  ),
    .o_axi_m_ar_burst   (o_pcie_init_mt_axi_arburst ),
    .o_axi_m_ar_lock    (o_pcie_init_mt_axi_arlock  ),
    .o_axi_m_ar_cache   (o_pcie_init_mt_axi_arcache ),
    .o_axi_m_ar_prot    (o_pcie_init_mt_axi_arprot  ),
    .o_axi_m_ar_qos     (o_pcie_init_mt_axi_arqos   ),
    .o_axi_m_ar_region  (o_pcie_init_mt_axi_arregion),
    .o_axi_m_ar_user    (o_pcie_init_mt_axi_aruser  ),
    .i_axi_m_ar_ready   (i_pcie_init_mt_axi_arready ),
    // R
    .i_axi_m_r_valid    (i_pcie_init_mt_axi_rvalid  ),
    .i_axi_m_r_id       (i_pcie_init_mt_axi_rid     ),
    .i_axi_m_r_data     (i_pcie_init_mt_axi_rdata   ),
    .i_axi_m_r_resp     (i_pcie_init_mt_axi_rresp   ),
    .i_axi_m_r_last     (i_pcie_init_mt_axi_rlast   ),
    .i_axi_m_r_user     (i_pcie_init_mt_axi_ruser   ),
    .o_axi_m_r_ready    (o_pcie_init_mt_axi_rready  )
  );

  axe_axi_multicut_flat #(
    .NumCuts       (1                      ), // Number of cuts.
    .AxiIdWidth    (PCIE_TARG_MT_AXI_ID_W  ), // AXI ID Width
    .AxiAddrWidth  (CHIP_AXI_ADDR_W        ), // AXI Address Width
    .AxiDataWidth  (PCIE_TARG_MT_AXI_DATA_W), // AXI Data Width
    .AxiAwUserWidth(CHIP_AXI_MT_AWUSER_W   ), // AXI AW User Width
    .AxiWUserWidth (CHIP_AXI_MT_WUSER_W    ), // AXI  W User Width
    .AxiBUserWidth (CHIP_AXI_MT_BUSER_W    ), // AXI  B User Width
    .AxiArUserWidth(CHIP_AXI_MT_ARUSER_W   ), // AXI AR User Width
    .AxiRUserWidth (CHIP_AXI_MT_RUSER_W    )  // AXI  R User Width
  ) u_axi_s_cut (
    .i_clk             (pcie_targ_mt_axi_aclk   ),
    .i_rst_n           (o_pcie_targ_mt_axi_rst_n),
    //////////////////////
    // Subordinate Port //
    //////////////////////
    // AW
    .i_axi_s_aw_valid  (i_pcie_targ_mt_axi_awvalid ),
    .i_axi_s_aw_id     (i_pcie_targ_mt_axi_awid    ),
    .i_axi_s_aw_addr   (i_pcie_targ_mt_axi_awaddr  ),
    .i_axi_s_aw_len    (i_pcie_targ_mt_axi_awlen   ),
    .i_axi_s_aw_size   (i_pcie_targ_mt_axi_awsize  ),
    .i_axi_s_aw_burst  (i_pcie_targ_mt_axi_awburst ),
    .i_axi_s_aw_lock   (i_pcie_targ_mt_axi_awlock  ),
    .i_axi_s_aw_cache  (i_pcie_targ_mt_axi_awcache ),
    .i_axi_s_aw_prot   (i_pcie_targ_mt_axi_awprot  ),
    .i_axi_s_aw_qos    (i_pcie_targ_mt_axi_awqos   ),
    .i_axi_s_aw_region (i_pcie_targ_mt_axi_awregion),
    .i_axi_s_aw_user   (i_pcie_targ_mt_axi_awuser  ),
    .o_axi_s_aw_ready  (o_pcie_targ_mt_axi_awready ),
    // W
    .i_axi_s_w_valid   (i_pcie_targ_mt_axi_wvalid  ),
    .i_axi_s_w_data    (i_pcie_targ_mt_axi_wdata   ),
    .i_axi_s_w_strb    (i_pcie_targ_mt_axi_wstrb   ),
    .i_axi_s_w_last    (i_pcie_targ_mt_axi_wlast   ),
    .i_axi_s_w_user    (i_pcie_targ_mt_axi_wuser   ),
    .o_axi_s_w_ready   (o_pcie_targ_mt_axi_wready  ),
    // B
    .o_axi_s_b_valid   (o_pcie_targ_mt_axi_bvalid  ),
    .o_axi_s_b_id      (o_pcie_targ_mt_axi_bid     ),
    .o_axi_s_b_resp    (o_pcie_targ_mt_axi_bresp   ),
    .o_axi_s_b_user    (o_pcie_targ_mt_axi_buser   ),
    .i_axi_s_b_ready   (i_pcie_targ_mt_axi_bready  ),
    // AR
    .i_axi_s_ar_valid  (i_pcie_targ_mt_axi_arvalid ),
    .i_axi_s_ar_id     (i_pcie_targ_mt_axi_arid    ),
    .i_axi_s_ar_addr   (i_pcie_targ_mt_axi_araddr  ),
    .i_axi_s_ar_len    (i_pcie_targ_mt_axi_arlen   ),
    .i_axi_s_ar_size   (i_pcie_targ_mt_axi_arsize  ),
    .i_axi_s_ar_burst  (i_pcie_targ_mt_axi_arburst ),
    .i_axi_s_ar_lock   (i_pcie_targ_mt_axi_arlock  ),
    .i_axi_s_ar_cache  (i_pcie_targ_mt_axi_arcache ),
    .i_axi_s_ar_prot   (i_pcie_targ_mt_axi_arprot  ),
    .i_axi_s_ar_qos    (i_pcie_targ_mt_axi_arqos   ),
    .i_axi_s_ar_region (i_pcie_targ_mt_axi_arregion),
    .i_axi_s_ar_user   (i_pcie_targ_mt_axi_aruser  ),
    .o_axi_s_ar_ready  (o_pcie_targ_mt_axi_arready ),
    // R
    .o_axi_s_r_valid   (o_pcie_targ_mt_axi_rvalid  ),
    .o_axi_s_r_id      (o_pcie_targ_mt_axi_rid     ),
    .o_axi_s_r_data    (o_pcie_targ_mt_axi_rdata   ),
    .o_axi_s_r_resp    (o_pcie_targ_mt_axi_rresp   ),
    .o_axi_s_r_last    (o_pcie_targ_mt_axi_rlast   ),
    .o_axi_s_r_user    (o_pcie_targ_mt_axi_ruser   ),
    .i_axi_s_r_ready   (i_pcie_targ_mt_axi_rready  ),
    /////////////////////
    // Management Port //
    /////////////////////
    // AW
    .o_axi_m_aw_valid   (spreg_i_axi_s_awvalid   ),
    .o_axi_m_aw_id      (spreg_i_axi_s_awid      ),
    .o_axi_m_aw_addr    (spreg_i_axi_s_awaddr    ),
    .o_axi_m_aw_len     (spreg_i_axi_s_awlen     ),
    .o_axi_m_aw_size    (spreg_i_axi_s_awsize    ),
    .o_axi_m_aw_burst   (spreg_i_axi_s_awburst   ),
    .o_axi_m_aw_lock    (spreg_i_axi_s_awlock    ),
    .o_axi_m_aw_cache   (spreg_i_axi_s_awcache   ),
    .o_axi_m_aw_prot    (spreg_i_axi_s_awprot    ),
    .o_axi_m_aw_qos     (spreg_i_axi_s_awqos     ),
    .o_axi_m_aw_region  (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use awregion
    .o_axi_m_aw_user    (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use awuser
    .i_axi_m_aw_ready   (spreg_o_axi_s_awready   ),
    // W
    .o_axi_m_w_valid    (spreg_i_axi_s_wvalid    ),
    .o_axi_m_w_data     (spreg_i_axi_s_wdata     ),
    .o_axi_m_w_strb     (spreg_i_axi_s_wstrb     ),
    .o_axi_m_w_last     (spreg_i_axi_s_wlast     ),
    .o_axi_m_w_user     (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use wuser
    .i_axi_m_w_ready    (spreg_o_axi_s_wready    ),
    // B
    .i_axi_m_b_valid    (spreg_o_axi_s_bvalid    ),
    .i_axi_m_b_id       (spreg_o_axi_s_bid       ),
    .i_axi_m_b_resp     (spreg_o_axi_s_bresp     ),
    .i_axi_m_b_user     (chip_axi_mt_buser_t'('0)), // Not needed
    .o_axi_m_b_ready    (spreg_i_axi_s_bready    ),
    // AR
    .o_axi_m_ar_valid   (spreg_i_axi_s_arvalid   ),
    .o_axi_m_ar_id      (spreg_i_axi_s_arid      ),
    .o_axi_m_ar_addr    (spreg_i_axi_s_araddr    ),
    .o_axi_m_ar_len     (spreg_i_axi_s_arlen     ),
    .o_axi_m_ar_size    (spreg_i_axi_s_arsize    ),
    .o_axi_m_ar_burst   (spreg_i_axi_s_arburst   ),
    .o_axi_m_ar_lock    (spreg_i_axi_s_arlock    ),
    .o_axi_m_ar_cache   (spreg_i_axi_s_arcache   ),
    .o_axi_m_ar_prot    (spreg_i_axi_s_arprot    ),
    .o_axi_m_ar_qos     (spreg_i_axi_s_arqos     ),
    .o_axi_m_ar_region  (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use arregion
    .o_axi_m_ar_user    (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use aruser
    .i_axi_m_ar_ready   (spreg_o_axi_s_arready   ),
    // R
    .i_axi_m_r_valid    (spreg_o_axi_s_rvalid    ),
    .i_axi_m_r_id       (spreg_o_axi_s_rid       ),
    .i_axi_m_r_data     (spreg_o_axi_s_rdata     ),
    .i_axi_m_r_resp     (spreg_o_axi_s_rresp     ),
    .i_axi_m_r_last     (spreg_o_axi_s_rlast     ),
    .i_axi_m_r_user     (chip_axi_mt_ruser_t'('0)), // Not needed
    .o_axi_m_r_ready    (spreg_i_axi_s_rready    )
  );

  axe_axi_multicut_flat #(
    .NumCuts       (1                           ), // Number of cuts.
    .AxiIdWidth    (PCIE_TARG_CFG_DBI_AXI_ID_W  ), // AXI ID Width
    .AxiAddrWidth  (CHIP_AXI_ADDR_W             ), // AXI Address Width
    .AxiDataWidth  (PCIE_TARG_CFG_DBI_AXI_DATA_W), // AXI Data Width
    .AxiAwUserWidth(CHIP_AXI_LT_AWUSER_W        ), // AXI AW User Width
    .AxiWUserWidth (CHIP_AXI_LT_WUSER_W         ), // AXI  W User Width
    .AxiBUserWidth (CHIP_AXI_LT_BUSER_W         ), // AXI  B User Width
    .AxiArUserWidth(CHIP_AXI_LT_ARUSER_W        ), // AXI AR User Width
    .AxiRUserWidth (CHIP_AXI_LT_RUSER_W         )  // AXI  R User Width
  ) u_dbi_cut (
    .i_clk             (pcie_targ_cfg_dbi_axi_aclk   ),
    .i_rst_n           (o_pcie_targ_cfg_dbi_axi_rst_n),
    //////////////////////
    // Subordinate Port //
    //////////////////////
    // AW
    .i_axi_s_aw_valid  (i_pcie_targ_cfg_dbi_axi_awvalid ),
    .i_axi_s_aw_id     (i_pcie_targ_cfg_dbi_axi_awid    ),
    .i_axi_s_aw_addr   (i_pcie_targ_cfg_dbi_axi_awaddr  ),
    .i_axi_s_aw_len    (i_pcie_targ_cfg_dbi_axi_awlen   ),
    .i_axi_s_aw_size   (i_pcie_targ_cfg_dbi_axi_awsize  ),
    .i_axi_s_aw_burst  (i_pcie_targ_cfg_dbi_axi_awburst ),
    .i_axi_s_aw_lock   (i_pcie_targ_cfg_dbi_axi_awlock  ),
    .i_axi_s_aw_cache  (i_pcie_targ_cfg_dbi_axi_awcache ),
    .i_axi_s_aw_prot   (i_pcie_targ_cfg_dbi_axi_awprot  ),
    .i_axi_s_aw_qos    (i_pcie_targ_cfg_dbi_axi_awqos   ),
    .i_axi_s_aw_region (i_pcie_targ_cfg_dbi_axi_awregion),
    .i_axi_s_aw_user   (i_pcie_targ_cfg_dbi_axi_awuser  ),
    .o_axi_s_aw_ready  (o_pcie_targ_cfg_dbi_axi_awready ),
    // W
    .i_axi_s_w_valid   (i_pcie_targ_cfg_dbi_axi_wvalid  ),
    .i_axi_s_w_data    (i_pcie_targ_cfg_dbi_axi_wdata   ),
    .i_axi_s_w_strb    (i_pcie_targ_cfg_dbi_axi_wstrb   ),
    .i_axi_s_w_last    (i_pcie_targ_cfg_dbi_axi_wlast   ),
    .i_axi_s_w_user    (i_pcie_targ_cfg_dbi_axi_wuser   ),
    .o_axi_s_w_ready   (o_pcie_targ_cfg_dbi_axi_wready  ),
    // B
    .o_axi_s_b_valid   (o_pcie_targ_cfg_dbi_axi_bvalid  ),
    .o_axi_s_b_id      (o_pcie_targ_cfg_dbi_axi_bid     ),
    .o_axi_s_b_resp    (o_pcie_targ_cfg_dbi_axi_bresp   ),
    .o_axi_s_b_user    (o_pcie_targ_cfg_dbi_axi_buser   ),
    .i_axi_s_b_ready   (i_pcie_targ_cfg_dbi_axi_bready  ),
    // AR
    .i_axi_s_ar_valid  (i_pcie_targ_cfg_dbi_axi_arvalid ),
    .i_axi_s_ar_id     (i_pcie_targ_cfg_dbi_axi_arid    ),
    .i_axi_s_ar_addr   (i_pcie_targ_cfg_dbi_axi_araddr  ),
    .i_axi_s_ar_len    (i_pcie_targ_cfg_dbi_axi_arlen   ),
    .i_axi_s_ar_size   (i_pcie_targ_cfg_dbi_axi_arsize  ),
    .i_axi_s_ar_burst  (i_pcie_targ_cfg_dbi_axi_arburst ),
    .i_axi_s_ar_lock   (i_pcie_targ_cfg_dbi_axi_arlock  ),
    .i_axi_s_ar_cache  (i_pcie_targ_cfg_dbi_axi_arcache ),
    .i_axi_s_ar_prot   (i_pcie_targ_cfg_dbi_axi_arprot  ),
    .i_axi_s_ar_qos    (i_pcie_targ_cfg_dbi_axi_arqos   ),
    .i_axi_s_ar_region (i_pcie_targ_cfg_dbi_axi_arregion),
    .i_axi_s_ar_user   (i_pcie_targ_cfg_dbi_axi_aruser  ),
    .o_axi_s_ar_ready  (o_pcie_targ_cfg_dbi_axi_arready ),
    // R
    .o_axi_s_r_valid   (o_pcie_targ_cfg_dbi_axi_rvalid  ),
    .o_axi_s_r_id      (o_pcie_targ_cfg_dbi_axi_rid     ),
    .o_axi_s_r_data    (o_pcie_targ_cfg_dbi_axi_rdata   ),
    .o_axi_s_r_resp    (o_pcie_targ_cfg_dbi_axi_rresp   ),
    .o_axi_s_r_last    (o_pcie_targ_cfg_dbi_axi_rlast   ),
    .o_axi_s_r_user    (o_pcie_targ_cfg_dbi_axi_ruser   ),
    .i_axi_s_r_ready   (i_pcie_targ_cfg_dbi_axi_rready  ),
    /////////////////////
    // Management Port //
    /////////////////////
    // AW
    .o_axi_m_aw_valid   (spreg_i_dbi_awvalid     ),
    .o_axi_m_aw_id      (spreg_i_dbi_awid        ),
    .o_axi_m_aw_addr    (spreg_i_dbi_awaddr      ),
    .o_axi_m_aw_len     (spreg_i_dbi_awlen       ),
    .o_axi_m_aw_size    (spreg_i_dbi_awsize      ),
    .o_axi_m_aw_burst   (spreg_i_dbi_awburst     ),
    .o_axi_m_aw_lock    (spreg_i_dbi_awlock      ),
    .o_axi_m_aw_cache   (spreg_i_dbi_awcache     ),
    .o_axi_m_aw_prot    (spreg_i_dbi_awprot      ),
    .o_axi_m_aw_qos     (spreg_i_dbi_awqos       ),
    .o_axi_m_aw_region  (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use awregion
    .o_axi_m_aw_user    (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use awuser
    .i_axi_m_aw_ready   (spreg_o_dbi_awready     ),
    // W
    .o_axi_m_w_valid    (spreg_i_dbi_wvalid      ),
    .o_axi_m_w_data     (spreg_i_dbi_wdata       ),
    .o_axi_m_w_strb     (spreg_i_dbi_wstrb       ),
    .o_axi_m_w_last     (spreg_i_dbi_wlast       ),
    .o_axi_m_w_user     (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use wuser
    .i_axi_m_w_ready    (spreg_o_dbi_wready      ),
    // B
    .i_axi_m_b_valid    (spreg_o_dbi_bvalid      ),
    .i_axi_m_b_id       (spreg_o_dbi_bid         ),
    .i_axi_m_b_resp     (spreg_o_dbi_bresp       ),
    .i_axi_m_b_user     (chip_axi_lt_buser_t'('0)), // Not needed
    .o_axi_m_b_ready    (spreg_i_dbi_bready      ),
    // AR
    .o_axi_m_ar_valid   (spreg_i_dbi_arvalid     ),
    .o_axi_m_ar_id      (spreg_i_dbi_arid        ),
    .o_axi_m_ar_addr    (spreg_i_dbi_araddr      ),
    .o_axi_m_ar_len     (spreg_i_dbi_arlen       ),
    .o_axi_m_ar_size    (spreg_i_dbi_arsize      ),
    .o_axi_m_ar_burst   (spreg_i_dbi_arburst     ),
    .o_axi_m_ar_lock    (spreg_i_dbi_arlock      ),
    .o_axi_m_ar_cache   (spreg_i_dbi_arcache     ),
    .o_axi_m_ar_prot    (spreg_i_dbi_arprot      ),
    .o_axi_m_ar_qos     (spreg_i_dbi_arqos       ),
    .o_axi_m_ar_region  (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use arregion
    .o_axi_m_ar_user    (                        ), // ASO-UNUSED_OUTPUT: pcie doesn't use aruser
    .i_axi_m_ar_ready   (spreg_o_dbi_arready     ),
    // R
    .i_axi_m_r_valid    (spreg_o_dbi_rvalid      ),
    .i_axi_m_r_id       (spreg_o_dbi_rid         ),
    .i_axi_m_r_data     (spreg_o_dbi_rdata       ),
    .i_axi_m_r_resp     (spreg_o_dbi_rresp       ),
    .i_axi_m_r_last     (spreg_o_dbi_rlast       ),
    .i_axi_m_r_user     (chip_axi_lt_ruser_t'('0)), // Not needed
    .o_axi_m_r_ready    (spreg_i_dbi_rready      )
  );

  DWC_pcie_subsystem u_pcie_subsys (
    // Clock and Reset Signals
    .aux_clk                            (aux_clk                      ),
    .o_core_clk                         (pcie_core_clk_oup            ),
    .o_muxd_aux_clk                     (pcie_muxd_aux_clk_oup        ),
    .local_ref_clk_req_n                (pcie_local_ref_clk_req_n     ),
    .clkreq_in_n                        (pcie_clkreq_in_n             ),
    .power_up_rst_n                     (power_up_rst_n               ),
    .perst_n                            (pcie_perst_n_inp             ),
    .o_core_rst_n                       (pcie_core_rst_n_oup          ),
    .o_pwr_rst_n                        (pcie_pwr_rst_n_oup           ),
    .phy_fw_clk                         (phy_fw_clk                   ),

    // AXI Clock and Reset Signals
    .mstr_aclk                          (mstr_aclk                    ),
    .o_mstr_aresetn                     (o_pcie_init_mt_axi_rst_n     ),
    .slv_aclk                           (slv_aclk                     ),
    .o_slv_aresetn                      (o_pcie_targ_mt_axi_rst_n     ),
    .dbi_aclk                           (dbi_aclk                     ),
    .o_dbi_aresetn                      (o_pcie_targ_cfg_dbi_axi_rst_n),

    // APB Clock Interface Signals
    .apb_pclk                           (apb_pclk                     ),
    .apb_presetn                        (i_global_rst_n               ),
    
    // On-Chip Reference Clock Inputs
    .ref_alt_clk_p                      (i_ref_alt_clk_p),

    // PHY Pads
    .resref                             (io_pcie_resref ),
    .ref_pad_clk_p                      (i_ref_pad_clk_p),
    .ref_pad_clk_m                      (i_ref_pad_clk_m),
    .rxp                                ({i_pcie_rxp_03, i_pcie_rxp_02, i_pcie_rxp_01, i_pcie_rxp_00}),
    .rxm                                ({i_pcie_rxm_03, i_pcie_rxm_02, i_pcie_rxm_01, i_pcie_rxm_00}),
    .txp                                ({o_pcie_txp_03, o_pcie_txp_02, o_pcie_txp_01, o_pcie_txp_00}),
    .txm                                ({o_pcie_txm_03, o_pcie_txm_02, o_pcie_txm_01, o_pcie_txm_00}),

    // AXI M Interface Signals
	  // AW
	  .mstr_awvalid                       (spreg_o_axi_m_awvalid ),
	  .mstr_awid                          (spreg_o_axi_m_awid    ),
    .mstr_awaddr                        (spreg_o_axi_m_awaddr  ),
    .mstr_awlen                         (spreg_o_axi_m_awlen   ),
    .mstr_awsize                        (spreg_o_axi_m_awsize  ),
    .mstr_awburst                       (spreg_o_axi_m_awburst ),
    .mstr_awlock                        (spreg_o_axi_m_awlock  ),
    .mstr_awcache                       (spreg_o_axi_m_awcache ),
    .mstr_awprot                        (spreg_o_axi_m_awprot  ),
	  .mstr_awqos                         (spreg_o_axi_m_awqos   ),
    .mstr_awready                       (spreg_i_axi_m_awready ),
    .mstr_awmisc_info                   (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_awmisc_info_last_dcmp_tlp     (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_awmisc_info_hdr_34dw          (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_awmisc_info_dma               (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_awmisc_info_ep                (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_awmisc_info_nw                (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_awmisc_info_ats               (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    // W
    .mstr_wvalid                        (spreg_o_axi_m_wvalid  ),
    .mstr_wdata                         (spreg_o_axi_m_wdata   ),
    .mstr_wstrb                         (spreg_o_axi_m_wstrb   ),
    .mstr_wlast                         (spreg_o_axi_m_wlast   ),
    .mstr_wready                        (spreg_i_axi_m_wready  ),
    // B
	  .mstr_bvalid                        (spreg_i_axi_m_bvalid  ),
    .mstr_bid                           (spreg_i_axi_m_bid     ),
    .mstr_bresp                         (spreg_i_axi_m_bresp   ),
	  .mstr_bready                        (spreg_o_axi_m_bready  ),
    .mstr_bmisc_info_cpl_stat           ('0                    ), // Not needed
    // AR
	  .mstr_arvalid                       (spreg_o_axi_m_arvalid ),
    .mstr_arid                          (spreg_o_axi_m_arid    ),
    .mstr_araddr                        (spreg_o_axi_m_araddr  ),
    .mstr_arlen                         (spreg_o_axi_m_arlen   ),
    .mstr_arsize                        (spreg_o_axi_m_arsize  ),
    .mstr_arburst                       (spreg_o_axi_m_arburst ),
    .mstr_arlock                        (spreg_o_axi_m_arlock  ),
    .mstr_arcache                       (spreg_o_axi_m_arcache ),
    .mstr_arprot                        (spreg_o_axi_m_arprot  ),
	  .mstr_arqos                         (spreg_o_axi_m_arqos   ),
	  .mstr_arready                       (spreg_i_axi_m_arready ),
    .mstr_armisc_info                   (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_armisc_info_last_dcmp_tlp     (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_armisc_info_dma               (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_armisc_info_zeroread          (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_armisc_info_nw                (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    .mstr_armisc_info_ats               (                      ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
	  // R
    .mstr_rvalid                        (spreg_i_axi_m_rvalid  ),
	  .mstr_rid                           (spreg_i_axi_m_rid     ),
    .mstr_rlast                         (spreg_i_axi_m_rlast   ),
    .mstr_rdata                         (spreg_i_axi_m_rdata   ),
    .mstr_rresp                         (spreg_i_axi_m_rresp   ),
	  .mstr_rready                        (spreg_o_axi_m_rready  ),
    .mstr_rmisc_info                    ('0                    ), // Not needed
    .mstr_rmisc_info_cpl_stat           ('0                    ), // Not needed
	
    // AXI S Interface Signals
	  // AW
	  .slv_awvalid                        (spreg_i_axi_s_awvalid),
    .slv_awid                           (spreg_i_axi_s_awid   ),
    .slv_awaddr                         ({{64-CHIP_AXI_ADDR_W{1'b0}}, spreg_i_axi_s_awaddr}),
    .slv_awlen                          (spreg_i_axi_s_awlen  ),
    .slv_awsize                         (spreg_i_axi_s_awsize ),
    .slv_awburst                        (spreg_i_axi_s_awburst),
    .slv_awlock                         (spreg_i_axi_s_awlock ),
    .slv_awcache                        (spreg_i_axi_s_awcache),
    .slv_awprot                         (spreg_i_axi_s_awprot ),
	  .slv_awqos                          (spreg_i_axi_s_awqos  ),
    .slv_awready                        (spreg_o_axi_s_awready),
    .slv_awmisc_info                    ('0                   ), // Not needed
    .slv_awmisc_info_hdr_34dw           ('0                   ), // Not needed
    .slv_awmisc_info_p_tag              ('0                   ), // Not needed
    .slv_awmisc_info_atu_bypass         ('0                   ), // Not needed
    .slv_awmisc_info_nw                 ('0                   ), // Not needed
    .slv_awmisc_info_ats                ('0                   ), // Not needed
    // W
	  .slv_wvalid                         (spreg_i_axi_s_wvalid ),
	  .slv_wdata                          (spreg_i_axi_s_wdata  ),
    .slv_wstrb                          (spreg_i_axi_s_wstrb  ),
    .slv_wlast                          (spreg_i_axi_s_wlast  ),
	  .slv_wready                         (spreg_o_axi_s_wready ),
    .slv_wmisc_info_ep                  ('0                   ), // Not needed
    .slv_wmisc_info_silentDrop          ('0                   ), // Not needed
	  // B
	  .slv_bvalid                         (spreg_o_axi_s_bvalid ),
    .slv_bid                            (spreg_o_axi_s_bid    ),
    .slv_bresp                          (spreg_o_axi_s_bresp  ),
    .slv_bready                         (spreg_i_axi_s_bready ),
    .slv_bmisc_info                     (                     ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
	  // AR
	  .slv_arvalid                        (spreg_i_axi_s_arvalid),
    .slv_arid                           (spreg_i_axi_s_arid   ),
    .slv_araddr                         ({{64-CHIP_AXI_ADDR_W{1'b0}}, spreg_i_axi_s_araddr}),
    .slv_arlen                          (spreg_i_axi_s_arlen  ),
    .slv_arsize                         (spreg_i_axi_s_arsize ),
    .slv_arburst                        (spreg_i_axi_s_arburst),
    .slv_arlock                         (spreg_i_axi_s_arlock ),
    .slv_arcache                        (spreg_i_axi_s_arcache),
    .slv_arprot                         (spreg_i_axi_s_arprot ),
	  .slv_arqos                          (spreg_i_axi_s_arqos  ),
	  .slv_arready                        (spreg_o_axi_s_arready),
    .slv_armisc_info                    ('0                   ), // Not needed
    .slv_armisc_info_atu_bypass         ('0                   ), // Not needed
    .slv_armisc_info_nw                 ('0                   ), // Not needed
    .slv_armisc_info_ats                ('0                   ), // Not needed
	  // R
	  .slv_rvalid                         (spreg_o_axi_s_rvalid ),
    .slv_rid                            (spreg_o_axi_s_rid    ),
    .slv_rdata                          (spreg_o_axi_s_rdata  ),
    .slv_rresp                          (spreg_o_axi_s_rresp  ),
    .slv_rlast                          (spreg_o_axi_s_rlast  ),
	  .slv_rready                         (spreg_i_axi_s_rready ),
    .slv_rmisc_info                     (                     ), // ASO-UNUSED_OUTPUT: pcie doesn't use misc_info interface
    
    // AXI S DBI Interface Signals
	  // AW
	  .dbi_awvalid                        (spreg_i_dbi_awvalid),
    .dbi_awid                           (spreg_i_dbi_awid   ),
    .dbi_awaddr                         (spreg_i_dbi_awaddr[31:0]),
    .dbi_awlen                          (spreg_i_dbi_awlen  ),
    .dbi_awsize                         (spreg_i_dbi_awsize ),
    .dbi_awburst                        (spreg_i_dbi_awburst),
    .dbi_awlock                         (spreg_i_dbi_awlock ),
    .dbi_awcache                        (spreg_i_dbi_awcache),
    .dbi_awprot                         (spreg_i_dbi_awprot ),
	  .dbi_awqos                          (spreg_i_dbi_awqos  ),
    .dbi_awready                        (spreg_o_dbi_awready),
	  // W
	  .dbi_wvalid                         (spreg_i_dbi_wvalid ),
    .dbi_wdata                          (spreg_i_dbi_wdata  ),
    .dbi_wstrb                          (spreg_i_dbi_wstrb  ),
    .dbi_wlast                          (spreg_i_dbi_wlast  ),
	  .dbi_wready                         (spreg_o_dbi_wready ),
	  // B
	  .dbi_bvalid                         (spreg_o_dbi_bvalid ),
    .dbi_bid                            (spreg_o_dbi_bid    ),
    .dbi_bresp                          (spreg_o_dbi_bresp  ),
    .dbi_bready                         (spreg_i_dbi_bready ),
	  // AR
    .dbi_arvalid                        (spreg_i_dbi_arvalid),
    .dbi_arid                           (spreg_i_dbi_arid   ),
    .dbi_araddr                         (spreg_i_dbi_araddr[31:0]),
    .dbi_arlen                          (spreg_i_dbi_arlen  ),
    .dbi_arsize                         (spreg_i_dbi_arsize ),
    .dbi_arburst                        (spreg_i_dbi_arburst),
    .dbi_arlock                         (spreg_i_dbi_arlock ),
    .dbi_arcache                        (spreg_i_dbi_arcache),
    .dbi_arprot                         (spreg_i_dbi_arprot ),
	  .dbi_arqos                          (spreg_i_dbi_arqos  ),
    .dbi_arready                        (spreg_o_dbi_arready),
	  // R
	  .dbi_rvalid                         (spreg_o_dbi_rvalid ),
    .dbi_rid                            (spreg_o_dbi_rid    ),
    .dbi_rdata                          (spreg_o_dbi_rdata  ),
    .dbi_rresp                          (spreg_o_dbi_rresp  ),
    .dbi_rlast                          (spreg_o_dbi_rlast  ),
	  .dbi_rready                         (spreg_i_dbi_rready ),

    // APB Config Interface Signals
    .apbslv_psel                        (i_pcie_targ_cfg_apb_psel   ),
    .apbslv_penable                     (i_pcie_targ_cfg_apb_penable),
    .apbslv_paddr                       ({{32-PCIE_TARG_CFG_APB3_ADDR_W{1'b0}}, i_pcie_targ_cfg_apb_paddr}),
    .apbslv_pwrite                      (i_pcie_targ_cfg_apb_pwrite ),
    .apbslv_pstrb                       (i_pcie_targ_cfg_apb_pstrb  ),
    .apbslv_pwdata                      (i_pcie_targ_cfg_apb_pwdata ),
    .apbslv_pready                      (o_pcie_targ_cfg_apb_pready ),
    .apbslv_pslverr                     (o_pcie_targ_cfg_apb_pslverr),
    .apbslv_prdata                      (o_pcie_targ_cfg_apb_prdata ),
    .apbslv_active                      (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use active signal

    // MSI interface
    .msi_int                            (pcie_reg2hw.msi_int        ),
    // Misc Interrupt Signal
    .sys_int                            (pcie_reg2hw.sys_int        ),
    .pcie_int                           (o_pcie_int                 ),

    .smlh_req_rst_not                   (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use smlh_req_rst_not signal

    // Debug Signals
    .pcie_dbg_signal                    (pcie_dbg_signal            ),

    // FLR interface
    .wake                               (                           ), // ASO-UNUSED_OUTPUT: pcie doesn't use wake signal

    // PHY APB/CR select
    .phy_apb0_if_sel                    (1'b1                       ), // jtag tdr can override

    .phy0_dtb_out                       (pcie_phy0_dtb_out          ),

    // General Scan Signals 
    .snps_scan_in             ('0),
    .snps_scan_out            (),

    // PCIe Controller Scan Signals
    .mac_scan_mode            (1'b0),
    .mac_scan_rst_n           (i_global_rst_n),
    .mac_scan_shift           (1'b0),
    .mac_scan_shift_cg        (1'b0),
    .mac_scan_coreclk         (mac_scan_coreclk),

    // PHY Test Control Signals
    .tap_phy0_ref_use_pad     (1'b0),
    .tap_phy0_reset           (1'b0),
    .ate_test_mode            (1'b0),
    .phy_test_burnin          (1'b0),
    .phy_test_powerdown       (1'b0),
    .phy_test_stop_clk_en     (1'b0),
    .phy_test_tx_ref_clk_en   (1'b0),
    .phy0_test_flyover_en     (1'b0),


    // PHY Boundary Scan Port Signals
    .phy_bs_acmode            (1'b0),
    .phy_bs_actest            (1'b0),
    .phy_bs_cdr               (1'b0),
    .phy_bs_ce                (1'b0),
    .phy_bs_rx_bigswing       (1'b0),
    .phy_bs_rx_init           (1'b0),
    .phy_bs_rx_level          ('0),
    .phy_bs_sdr               (1'b0),
    .phy_bs_tdi               (1'b0),
    .phy_bs_tdo               (),
    .phy_bs_tx_lowswing       (1'b0),
    .phy_bs_udr               (1'b0),

    // PHY JTAG Port
    .phy0_jtag_tck            (tck),
    .phy0_jtag_tdi            (tdi),
    .phy0_jtag_tdo            (tdo),
    .phy0_jtag_tdo_en         (tdo_en),
    .phy0_jtag_tms            (tms),
    .phy0_jtag_trst_n         (trst),

    // PHY PCS Scan Interface
    .pcs_scan_clk             (pcs_scan_clk),
    .pcs_scan_clk_sel         (1'b0),
    .pcs_scan_mode            (1'b0),
    .pcs_scan_pclk            (pcs_scan_pclk),
    .pcs_scan_pcs_clk         (pcs_scan_pcs_clk),
    .pcs_scan_pma_clk         (pcs_scan_pma_clk),
    .pcs_scan_rst             (~i_global_rst_n),
    .pcs_scan_shift           (1'b0),
    .pcs_scan_shift_cg        (1'b0),

    // PHY Scan Interface
    .phy0_scan_mode           (1'b0),
    .phy0_scan_clk            (phy0_scan_clk),
    .phy0_scan_clk_sel        (1'b0),
    .phy0_scan_cr_clk         (phy0_scan_cr_clk),
    .phy0_scan_mpll_dword_clk (phy0_scan_mpll_dword_clk ),
    .phy0_scan_mpll_qword_clk (phy0_scan_mpll_qword_clk ),
    .phy0_scan_rx_dword_clk   (phy0_scan_rx_dword_clk   ),
    .phy0_scan_occ_clk        (phy0_scan_occ_clk        ),
    .phy0_scan_ref_clk        (phy0_scan_ref_clk        ),
    .phy0_scan_set_rst        (~i_global_rst_n),
    .phy0_scan_shift          (1'b0),
    .phy0_scan_shift_cg       (1'b0),
    .phy0_scan_pma_occ_en     (1'b0),

    .phy0_scan_cr_in          ('0),
    .phy0_scan_cr_out         (),
    .phy0_scan_mpll_dword_in  ('0),
    .phy0_scan_mpll_dword_out (),
    .phy0_scan_mpll_qword_in  ('0),
    .phy0_scan_mpll_qword_out (),
    .phy0_scan_rx_dword_in    ('0),
    .phy0_scan_rx_dword_out   (),
    .phy0_scan_occ_in         ('0),
    .phy0_scan_occ_out        (),
    .phy0_scan_ref_in         ('0),
    .phy0_scan_ref_out        (),

    .phy0_scan_apb0_in        (2'b0),
    .phy0_scan_apb0_out       (),
    .phy0_scan_apb1_in        (1'b0),
    .phy0_scan_apb1_out       (),
    .phy0_scan_fw_in          (1'b0),
    .phy0_scan_fw_out         (),
    .phy0_scan_jtag_in        ('0),
    .phy0_scan_jtag_out       ()
  );

endmodule
