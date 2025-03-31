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

  assign o_noc_async_idle_init_mt_axi_req = 1'b0;
  assign o_noc_async_idle_targ_mt_axi_req = 1'b0;
  assign o_noc_async_idle_targ_cfg_dbi_axi_req = 1'b0;
  assign o_noc_async_idle_targ_cfg_apb_req = 1'b0;
  assign o_noc_init_mt_axi_clken = 1'b0;
  assign o_noc_targ_mt_axi_clken = 1'b0;
  assign o_noc_targ_cfg_dbi_axi_clken = 1'b0;
  assign o_noc_targ_cfg_apb_clken = 1'b0;
  assign o_pcie_init_mt_axi_rst_n = 1'b0;
  assign o_pcie_targ_mt_axi_rst_n = 1'b0;
  assign o_pcie_targ_cfg_dbi_axi_rst_n = 1'b0;
  assign o_pcie_targ_cfg_apb_rst_n = 1'b0;
  assign o_pcie_txm_00 = 1'b0;
  assign o_pcie_txm_01 = 1'b0;
  assign o_pcie_txm_02 = 1'b0;
  assign o_pcie_txm_03 = 1'b0;
  assign o_pcie_txp_00 = 1'b0;
  assign o_pcie_txp_01 = 1'b0;
  assign o_pcie_txp_02 = 1'b0;
  assign o_pcie_txp_03 = 1'b0;
  assign o_pcie_init_mt_axi_awvalid = 1'b0;
  assign o_pcie_init_mt_axi_awid = '0;
  assign o_pcie_init_mt_axi_awaddr = '0;
  assign o_pcie_init_mt_axi_awlen = '0;
  assign o_pcie_init_mt_axi_awsize = '0;
  assign o_pcie_init_mt_axi_awburst = '0;
  assign o_pcie_init_mt_axi_awlock = 1'b0;
  assign o_pcie_init_mt_axi_awcache = '0;
  assign o_pcie_init_mt_axi_awprot = '0;
  assign o_pcie_init_mt_axi_awqos = '0;
  assign o_pcie_init_mt_axi_awregion = '0;
  assign o_pcie_init_mt_axi_awuser = '0;
  assign o_pcie_init_mt_axi_wvalid = 1'b0;
  assign o_pcie_init_mt_axi_wdata = '0;
  assign o_pcie_init_mt_axi_wstrb = '0;
  assign o_pcie_init_mt_axi_wlast = 1'b0;
  assign o_pcie_init_mt_axi_wuser = '0;
  assign o_pcie_init_mt_axi_bready = 1'b1;
  assign o_pcie_init_mt_axi_arvalid = 1'b0;
  assign o_pcie_init_mt_axi_arid = '0;
  assign o_pcie_init_mt_axi_araddr = '0;
  assign o_pcie_init_mt_axi_arlen = '0;
  assign o_pcie_init_mt_axi_arsize = '0;
  assign o_pcie_init_mt_axi_arburst = '0;
  assign o_pcie_init_mt_axi_arlock = 1'b0;
  assign o_pcie_init_mt_axi_arcache = '0;
  assign o_pcie_init_mt_axi_arprot = '0;
  assign o_pcie_init_mt_axi_arqos = '0;
  assign o_pcie_init_mt_axi_arregion = '0;
  assign o_pcie_init_mt_axi_aruser = '0;
  assign o_pcie_init_mt_axi_rready = 1'b1;
  assign o_pcie_targ_mt_axi_awready = 1'b1;
  assign o_pcie_targ_mt_axi_wready = 1'b1;
  assign o_pcie_targ_mt_axi_bvalid = 1'b0;
  assign o_pcie_targ_mt_axi_bid = '0;
  assign o_pcie_targ_mt_axi_bresp = '0;
  assign o_pcie_targ_mt_axi_buser = '0;
  assign o_pcie_targ_mt_axi_arready = 1'b1;
  assign o_pcie_targ_mt_axi_rvalid = 1'b0;
  assign o_pcie_targ_mt_axi_rid = '0;
  assign o_pcie_targ_mt_axi_rdata = '0;
  assign o_pcie_targ_mt_axi_rresp = '0;
  assign o_pcie_targ_mt_axi_rlast = 1'b0;
  assign o_pcie_targ_mt_axi_ruser = '0;
  assign o_pcie_targ_cfg_dbi_axi_awready = 1'b1;
  assign o_pcie_targ_cfg_dbi_axi_wready = 1'b1;
  assign o_pcie_targ_cfg_dbi_axi_bvalid = 1'b0;
  assign o_pcie_targ_cfg_dbi_axi_bid = '0;
  assign o_pcie_targ_cfg_dbi_axi_bresp = '0;
  assign o_pcie_targ_cfg_dbi_axi_buser = '0;
  assign o_pcie_targ_cfg_dbi_axi_arready = 1'b1;
  assign o_pcie_targ_cfg_dbi_axi_rvalid = 1'b0;
  assign o_pcie_targ_cfg_dbi_axi_rid = '0;
  assign o_pcie_targ_cfg_dbi_axi_rdata = '0;
  assign o_pcie_targ_cfg_dbi_axi_rresp = '0;
  assign o_pcie_targ_cfg_dbi_axi_rlast = 1'b0;
  assign o_pcie_targ_cfg_dbi_axi_ruser = '0;
  assign o_pcie_targ_cfg_apb_pready = 1'b1;
  assign o_pcie_targ_cfg_apb_prdata = '0;
  assign o_pcie_targ_cfg_apb_pslverr = 1'b0;
  assign o_pcie_targ_syscfg_apb_pready = 1'b1;
  assign o_pcie_targ_syscfg_apb_prdata = '0;
  assign o_pcie_targ_syscfg_apb_pslverr = 1'b0;
  assign o_pcie_int = 1'b0;
  assign o_pcie_obs = {15+1{1'b0}};
  assign tdo_en = 1'b0;
  assign tdo = 1'b0;
  assign ssn_bus_data_out = {24+1{1'b0}};
  assign bisr_so = 1'b0;

endmodule
