// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// Implementation of L2 Europa
///

module l2_p_stub
    import chip_pkg::*;
    import axi_pkg::*;
    import l2_p_pkg::*;
  (
    /// Fast Clock, positive edge triggered
    input   wire                  i_clk,
    /// APB Clock, positive edge triggered
    input   wire                  i_ref_clk,
    /// Asynchronous POR / always On reset, active low
    input   wire                  i_ao_rst_n,
    /// Asynchronous global reset, active low
    input   wire                  i_global_rst_n,
    /// Synchronous NoC reset, active low
    output  wire                  o_noc_rst_n,

    /// Isolation interface
    output logic                  o_noc_async_idle_req,
    input  logic                  i_noc_async_idle_ack,
    input  logic                  i_noc_async_idle_val,
    output logic                  o_noc_clken,

    // AXI Interface
    // AW channel
    input  chip_axi_addr_t        i_ht_axi_s_awaddr,
    input  l2_targ_ht_axi_id_t    i_ht_axi_s_awid,
    input  axi_len_t              i_ht_axi_s_awlen,
    input  axi_size_t             i_ht_axi_s_awsize,
    input  axi_burst_t            i_ht_axi_s_awburst,
    input  axi_cache_t            i_ht_axi_s_awcache,
    input  axi_prot_t             i_ht_axi_s_awprot,
    input  logic                  i_ht_axi_s_awlock,
    input  axi_qos_t              i_ht_axi_s_awqos,
    input  axi_region_t           i_ht_axi_s_awregion,
    input  chip_axi_ht_awuser_t   i_ht_axi_s_awuser,
    input  logic                  i_ht_axi_s_awvalid,
    output logic                  o_ht_axi_s_awready,
    // W channel
    input  chip_axi_ht_data_t     i_ht_axi_s_wdata,
    input  chip_axi_ht_wstrb_t    i_ht_axi_s_wstrb,
    input  logic                  i_ht_axi_s_wlast,
    input  chip_axi_ht_wuser_t    i_ht_axi_s_wuser,
    input  logic                  i_ht_axi_s_wvalid,
    output logic                  o_ht_axi_s_wready,
    // B channel
    output logic                  o_ht_axi_s_bvalid,
    output l2_targ_ht_axi_id_t    o_ht_axi_s_bid,
    output chip_axi_ht_buser_t    o_ht_axi_s_buser,
    output axi_resp_t             o_ht_axi_s_bresp,
    input  logic                  i_ht_axi_s_bready,
    // AR channel
    input  chip_axi_addr_t        i_ht_axi_s_araddr,
    input  l2_targ_ht_axi_id_t    i_ht_axi_s_arid,
    input  axi_len_t              i_ht_axi_s_arlen,
    input  axi_size_t             i_ht_axi_s_arsize,
    input  axi_burst_t            i_ht_axi_s_arburst,
    input  axi_cache_t            i_ht_axi_s_arcache,
    input  axi_prot_t             i_ht_axi_s_arprot,
    input  axi_qos_t              i_ht_axi_s_arqos,
    input  axi_region_t           i_ht_axi_s_arregion,
    input  chip_axi_ht_aruser_t   i_ht_axi_s_aruser,
    input  logic                  i_ht_axi_s_arlock,
    input  logic                  i_ht_axi_s_arvalid,
    output logic                  o_ht_axi_s_arready,
    // R channel
    output logic                  o_ht_axi_s_rvalid,
    output logic                  o_ht_axi_s_rlast,
    output l2_targ_ht_axi_id_t    o_ht_axi_s_rid,
    output chip_axi_ht_data_t     o_ht_axi_s_rdata,
    output chip_axi_ht_ruser_t    o_ht_axi_s_ruser,
    output axi_resp_t             o_ht_axi_s_rresp,
    input  logic                  i_ht_axi_s_rready,
    // APB
    input  chip_syscfg_addr_t     i_cfg_apb4_s_paddr,
    input  chip_apb_syscfg_data_t i_cfg_apb4_s_pwdata,
    input  logic                  i_cfg_apb4_s_pwrite,
    input  logic                  i_cfg_apb4_s_psel,
    input  logic                  i_cfg_apb4_s_penable,
    input  chip_apb_syscfg_strb_t i_cfg_apb4_s_pstrb,
    input  logic          [3-1:0] i_cfg_apb4_s_pprot,
    output logic                  o_cfg_apb4_s_pready,
    output chip_apb_syscfg_data_t o_cfg_apb4_s_prdata,
    output logic                  o_cfg_apb4_s_pslverr,
    // JTAG
    input  wire                   tck,
    input  wire                   trst,
    input  logic                  tms,
    input  logic                  tdi,
    output logic                  tdo_en,
    output logic                  tdo,
    // DFT
    input  wire                   test_clk,
    input  logic                  test_mode,
    input  logic                  edt_update,
    input  logic                  scan_en,
    input  logic [           7:0] scan_in,
    output logic [           7:0] scan_out,
    // BIST
    input  wire                   bisr_clk,
    input  wire                   bisr_reset,
    input  logic                  bisr_shift_en,
    input  logic                  bisr_si,
    output logic                  bisr_so
  );

  assign o_noc_rst_n = 1'b0;
  assign o_noc_async_idle_req = 1'b0;
  assign o_noc_clken = 1'b0;
  assign o_ht_axi_s_awready = 1'b1;
  assign o_ht_axi_s_wready = 1'b1;
  assign o_ht_axi_s_bvalid = 1'b0;
  assign o_ht_axi_s_bid = '0;
  assign o_ht_axi_s_buser = '0;
  assign o_ht_axi_s_bresp = '0;
  assign o_ht_axi_s_arready = 1'b1;
  assign o_ht_axi_s_rvalid = 1'b0;
  assign o_ht_axi_s_rlast = 1'b0;
  assign o_ht_axi_s_rid = '0;
  assign o_ht_axi_s_rdata = '0;
  assign o_ht_axi_s_ruser = '0;
  assign o_ht_axi_s_rresp = '0;
  assign o_cfg_apb4_s_pready = 1'b1;
  assign o_cfg_apb4_s_prdata = '0;
  assign o_cfg_apb4_s_pslverr = 1'b0;
  assign tdo_en = 1'b0;
  assign tdo = 1'b0;
  assign scan_out = {7+1{1'b0}};

endmodule
