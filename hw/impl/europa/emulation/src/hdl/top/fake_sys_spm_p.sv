// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
module sys_spm_p
  import sys_spm_pkg::*;
(
  // Fast Clock, positive edge triggered
  input   wire   i_clk,
  // APB Clock, positive edge triggered
  input   wire   i_ref_clk,
  // Asynchronous POR / always On reset, active low
  input   wire   i_ao_rst_n,
  // Asynchronous global reset, active low
  input   wire   i_global_rst_n,
  // Synchronous NoC reset, active low
  output  wire   o_noc_rst_n,

  /// Isolation interface
  output logic o_noc_async_idle_req,
  input  logic i_noc_async_idle_ack,
  input  logic i_noc_async_idle_val,
  output logic o_noc_clken,

  // AXI Interface
  // - AW Channel
  input  chip_pkg::chip_axi_addr_t        i_lt_axi_s_awaddr,
  input  sys_spm_targ_lt_axi_id_t         i_lt_axi_s_awid,
  input  axi_pkg::axi_len_t               i_lt_axi_s_awlen,
  input  axi_pkg::axi_size_t              i_lt_axi_s_awsize,
  input  axi_pkg::axi_burst_t             i_lt_axi_s_awburst,
  input  axi_pkg::axi_cache_t             i_lt_axi_s_awcache,
  input  axi_pkg::axi_prot_t              i_lt_axi_s_awprot,
  input  logic                            i_lt_axi_s_awlock,
  input  axi_pkg::axi_qos_t               i_lt_axi_s_awqos,
  input  axi_pkg::axi_region_t            i_lt_axi_s_awregion,
  input  chip_pkg::chip_axi_lt_awuser_t   i_lt_axi_s_awuser,
  input  logic                            i_lt_axi_s_awvalid,
  output logic                            o_lt_axi_s_awready,
  // - W Channel
  input chip_pkg::chip_axi_lt_data_t      i_lt_axi_s_wdata,
  input chip_pkg::chip_axi_lt_wstrb_t     i_lt_axi_s_wstrb,
  input logic                             i_lt_axi_s_wlast,
  input chip_pkg::chip_axi_lt_wuser_t     i_lt_axi_s_wuser,
  input logic                             i_lt_axi_s_wvalid,
  output logic                            o_lt_axi_s_wready,
  // - B Channel
  output logic                            o_lt_axi_s_bvalid,
  output sys_spm_targ_lt_axi_id_t         o_lt_axi_s_bid,
  output chip_pkg::chip_axi_lt_buser_t    o_lt_axi_s_buser,
  output axi_pkg::axi_resp_t              o_lt_axi_s_bresp,
  input  logic                            i_lt_axi_s_bready,
  // - AR Channel
  input  chip_pkg::chip_axi_addr_t        i_lt_axi_s_araddr,
  input  sys_spm_targ_lt_axi_id_t         i_lt_axi_s_arid,
  input  axi_pkg::axi_len_t               i_lt_axi_s_arlen,
  input  axi_pkg::axi_size_t              i_lt_axi_s_arsize,
  input  axi_pkg::axi_burst_t             i_lt_axi_s_arburst,
  input  axi_pkg::axi_cache_t             i_lt_axi_s_arcache,
  input  axi_pkg::axi_prot_t              i_lt_axi_s_arprot,
  input  axi_pkg::axi_qos_t               i_lt_axi_s_arqos,
  input  axi_pkg::axi_region_t            i_lt_axi_s_arregion,
  input  chip_pkg::chip_axi_lt_aruser_t   i_lt_axi_s_aruser,
  input  logic                            i_lt_axi_s_arlock,
  input  logic                            i_lt_axi_s_arvalid,
  output logic                            o_lt_axi_s_arready,
  // - R Channel
  output logic                            o_lt_axi_s_rvalid,
  output logic                            o_lt_axi_s_rlast,
  output sys_spm_targ_lt_axi_id_t         o_lt_axi_s_rid,
  output chip_pkg::chip_axi_lt_data_t     o_lt_axi_s_rdata,
  output chip_pkg::chip_axi_lt_ruser_t    o_lt_axi_s_ruser,
  output axi_pkg::axi_resp_t              o_lt_axi_s_rresp,
  input  logic                            i_lt_axi_s_rready,
  // APB Interface
  input  chip_pkg::chip_syscfg_addr_t     i_cfg_apb4_s_paddr,
  input  chip_pkg::chip_apb_syscfg_data_t i_cfg_apb4_s_pwdata,
  input  logic                            i_cfg_apb4_s_pwrite,
  input  logic                            i_cfg_apb4_s_psel,
  input  logic                            i_cfg_apb4_s_penable,
  input  chip_pkg::chip_apb_syscfg_strb_t i_cfg_apb4_s_pstrb,
  input  logic  [3-1:0]                   i_cfg_apb4_s_pprot,
  output logic                            o_cfg_apb4_s_pready,
  output chip_pkg::chip_apb_syscfg_data_t o_cfg_apb4_s_prdata,
  output logic                            o_cfg_apb4_s_pslverr,
  // Error IRQ signal
  output logic o_irq,
  // Observation port
  output logic [15:0] o_sysspm_obs,

  // DFT signals
  input  wire        tck,
  input  wire        trst,
  input  logic       tms,
  input  logic       tdi,
  output logic       tdo_en,
  output logic       tdo,

  input  wire        test_clk,
  input  logic       test_mode,
  input  logic       edt_update,
  input  logic       scan_en,
  input  logic [7:0] scan_in,
  output logic [7:0] scan_out,

  input  wire        bisr_clk,
  input  wire        bisr_reset,
  input  logic       bisr_shift_en,
  input  logic       bisr_si,
  output logic       bisr_so
);

  dv_axi_ram #(
      .ADDR_WIDTH(40),
      .DATA_WIDTH(64),
      .ID_WIDTH  (4)
  ) i_dv_axi_ram (
      .clk          (i_clk),
      .rst          (!i_global_rst_n),
      .s_axi_awid   (i_lt_axi_s_awid),
      .s_axi_awaddr (i_lt_axi_s_awaddr & 'hffffff),
      .s_axi_awlen  (i_lt_axi_s_awlen),
      .s_axi_awsize (i_lt_axi_s_awsize),
      .s_axi_awburst(i_lt_axi_s_awburst),
      .s_axi_awlock (i_lt_axi_s_awlock),
      .s_axi_awcache(i_lt_axi_s_awcache),
      .s_axi_awprot (i_lt_axi_s_awprot),
      .s_axi_awvalid(i_lt_axi_s_awvalid),
      .s_axi_awready(o_lt_axi_s_awready),
      .s_axi_wdata  (i_lt_axi_s_wdata),
      .s_axi_wstrb  (i_lt_axi_s_wstrb),
      .s_axi_wlast  (i_lt_axi_s_wlast),
      .s_axi_wvalid (i_lt_axi_s_wvalid),
      .s_axi_wready (o_lt_axi_s_wready),
      .s_axi_bid    (o_lt_axi_s_bid),
      .s_axi_bresp  (o_lt_axi_s_bresp),
      .s_axi_bvalid (o_lt_axi_s_bvalid),
      .s_axi_bready (i_lt_axi_s_bready),
      .s_axi_arid   (i_lt_axi_s_arid),
      .s_axi_araddr (i_lt_axi_s_araddr & 'hffffff),
      .s_axi_arlen  (i_lt_axi_s_arlen),
      .s_axi_arsize (i_lt_axi_s_arsize),
      .s_axi_arburst(i_lt_axi_s_arburst),
      .s_axi_arlock (i_lt_axi_s_arlock),
      .s_axi_arcache(i_lt_axi_s_arcache),
      .s_axi_arprot (i_lt_axi_s_arprot),
      .s_axi_arvalid(i_lt_axi_s_arvalid),
      .s_axi_arready(o_lt_axi_s_arready),
      .s_axi_rid    (o_lt_axi_s_rid),
      .s_axi_rdata  (o_lt_axi_s_rdata),
      .s_axi_rresp  (o_lt_axi_s_rresp),
      .s_axi_rlast  (o_lt_axi_s_rlast),
      .s_axi_rvalid (o_lt_axi_s_rvalid),
      .s_axi_rready (i_lt_axi_s_rready)
  );

  assign o_lt_axi_s_buser = '0;
  assign o_lt_axi_s_ruser = '0;
  assign o_cfg_apb4_s_pready = '0;
  assign o_cfg_apb4_s_prdata = '0;
  assign o_cfg_apb4_s_pslverr = '0;
  assign o_irq = '0;
  assign o_sysspm_obs = '0;
  assign ijtag_so = '0;
  assign scan_out = '0;
  assign bisr_so = '0;

  assign o_noc_rst_n = i_global_rst_n;
  assign o_noc_async_idle_req = 0;
  assign o_noc_clken = 1;

endmodule
