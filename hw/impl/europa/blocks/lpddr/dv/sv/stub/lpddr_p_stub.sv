
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//


module lpddr_p_stub
  import chip_pkg::*;
  import axi_pkg::*;
  import lpddr_pkg::*;
  (
  // Clocks
  input  wire   i_ao_clk,
  input  wire   i_lpddr_clk,

  //-------------------------------
  // Partition Controller Interface
  //-------------------------------
  input  wire                         i_ao_rst_n          ,
  input  wire                         i_global_rst_n      ,
  output wire                         o_ao_rst_sync_n     ,
  output logic          [1:0]         o_noc_async_idle_req, // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  input  logic          [1:0]         i_noc_async_idle_ack, // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  input  logic          [1:0]         i_noc_async_idle_val, // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  output logic                        o_noc_clken         ,
  output wire                         o_noc_rst_n         ,

  //-------------------------------
  // AXI4 lpddr_axi
  //-------------------------------
  input  logic [39:0]  i_lpddr_axi_m_araddr  ,
  input  logic [1:0]   i_lpddr_axi_m_arburst ,
  input  logic [3:0]   i_lpddr_axi_m_arcache ,
  input  logic [7:0]   i_lpddr_axi_m_arid    ,
  input  logic [7:0]   i_lpddr_axi_m_arlen   ,
  input  logic i_lpddr_axi_m_arlock  ,
  input  logic [2:0]   i_lpddr_axi_m_arprot  ,
  input  logic [3:0]   i_lpddr_axi_m_arqos   ,
  input  logic [3:0]   i_lpddr_axi_m_arregion,
  input  logic         i_lpddr_axi_m_aruser  ,
  input  logic [2:0]   i_lpddr_axi_m_arsize  ,
  input  logic i_lpddr_axi_m_arvalid ,
  input  logic i_lpddr_axi_m_rready  ,
  input  logic [39:0]  i_lpddr_axi_m_awaddr  ,
  input  logic [1:0]   i_lpddr_axi_m_awburst ,
  input  logic [3:0]   i_lpddr_axi_m_awcache ,
  input  logic [7:0]   i_lpddr_axi_m_awid    ,
  input  logic [7:0]   i_lpddr_axi_m_awlen   ,
  input  logic i_lpddr_axi_m_awlock  ,
  input  logic [2:0]   i_lpddr_axi_m_awprot  ,
  input  logic [3:0]   i_lpddr_axi_m_awqos   ,
  input  logic [3:0]   i_lpddr_axi_m_awregion,
  input  logic         i_lpddr_axi_m_awuser  ,
  input  logic [2:0]   i_lpddr_axi_m_awsize  ,
  input  logic i_lpddr_axi_m_awvalid ,
  input  logic [255:0] i_lpddr_axi_m_wdata   ,
  input  logic i_lpddr_axi_m_wlast   ,
  input  logic [31:0]  i_lpddr_axi_m_wstrb   ,
  input  logic i_lpddr_axi_m_wvalid  ,
  input  logic i_lpddr_axi_m_wuser  ,
  input  logic i_lpddr_axi_m_bready  ,
  output logic o_lpddr_axi_m_arready,
  output logic [255:0] o_lpddr_axi_m_rdata  ,
  output logic [7:0]   o_lpddr_axi_m_rid    ,
  output logic o_lpddr_axi_m_rlast  ,
  output logic o_lpddr_axi_m_ruser ,
  output logic [1:0]   o_lpddr_axi_m_rresp  ,
  output logic o_lpddr_axi_m_rvalid ,
  output logic o_lpddr_axi_m_awready,
  output logic o_lpddr_axi_m_wready ,
  output logic [7:0]   o_lpddr_axi_m_bid    ,
  output logic [1:0]   o_lpddr_axi_m_bresp  ,
  output logic o_lpddr_axi_m_bvalid ,
  output logic o_lpddr_axi_m_buser ,

  //-------------------------------
  // APB4 lpddr_cfg_apb (sync to i_lpddr_clk)
  //-------------------------------
  input  logic [31:0] i_lpddr_cfg_apb4_s_paddr,
  input  logic        i_lpddr_cfg_apb4_s_penable,
  input  logic [2:0]  i_lpddr_cfg_apb4_s_pprot,
  input  logic        i_lpddr_cfg_apb4_s_psel,
  input  logic [3:0]  i_lpddr_cfg_apb4_s_pstrb,
  input  logic [31:0] i_lpddr_cfg_apb4_s_pwdata,
  input  logic        i_lpddr_cfg_apb4_s_pwrite,
  output logic [31:0] o_lpddr_cfg_apb4_s_prdata,
  output logic        o_lpddr_cfg_apb4_s_pready,
  output logic        o_lpddr_cfg_apb4_s_pslverr,
  //-------------------------------
  // APB4 lpddr_syscfg_apb (sync to i_ao_clk)
  //-------------------------------
  input  chip_syscfg_addr_t           i_lpddr_syscfg_apb4_s_paddr  ,
  input  chip_apb_syscfg_data_t       i_lpddr_syscfg_apb4_s_pwdata ,
  input  logic                        i_lpddr_syscfg_apb4_s_pwrite ,
  input  logic                        i_lpddr_syscfg_apb4_s_psel   ,
  input  logic                        i_lpddr_syscfg_apb4_s_penable,
  input  chip_apb_syscfg_strb_t       i_lpddr_syscfg_apb4_s_pstrb  ,
  input  logic                  [2:0] i_lpddr_syscfg_apb4_s_pprot  ,
  output logic                        o_lpddr_syscfg_apb4_s_pready ,
  output chip_apb_syscfg_data_t       o_lpddr_syscfg_apb4_s_prdata ,
  output logic                        o_lpddr_syscfg_apb4_s_pslverr,

  // CTRL Interrupts
  output logic  o_ctrl_sbr_done_intr,
  output logic  o_ctrl_derate_temp_limit_intr,
  output logic  o_ctrl_ecc_ap_err_intr,
  output logic  o_ctrl_ecc_corrected_err_intr,
  output logic  o_ctrl_ecc_uncorrected_err_intr,
  output logic  o_ctrl_rd_linkecc_corr_err_intr,
  output logic  o_ctrl_rd_linkecc_uncorr_err_intr,

  // PHY interrupts
  output logic  o_phy_pie_prog_err_intr,
  output logic  o_phy_ecc_err_intr,
  output logic  o_phy_rdfptrchk_err_intr,
  output logic  o_phy_pie_parity_err_intr,
  output logic  o_phy_acsm_parity_err_intr,
  output logic  o_phy_trng_fail_intr,
  output logic  o_phy_init_cmplt_intr,
  output logic  o_phy_trng_cmplt_intr,

  //-------------------------------
  // DFT Interface add by axelera
  //-------------------------------
  input wire  tck,
  input wire  trst,
  input logic tms,
  input logic tdi,
  output logic tdo_en,
  output logic tdo,

  input wire  ssn_bus_clk,
  input logic [24 -1: 0] ssn_bus_data_in,
  output logic [24 -1: 0] ssn_bus_data_out,

  input wire  bisr_clk,
  input wire  bisr_reset,
  input logic  bisr_shift_en,
  input logic  bisr_si,
  output logic  bisr_so,

  // Observability signals for lpddr
  output logic [15:0] o_lpddr_obs,

  //-----------
  // PHY Bump signals
  //-----------
  output wire  BP_MEMRESET_L,
  inout wire [19:0] BP_A,
  inout wire  BP_ATO,
  inout wire  BP_ATO_PLL,
  inout wire [12:0] BP_B0_D,
  inout wire [12:0] BP_B1_D,
  inout wire [12:0] BP_B2_D,
  inout wire [12:0] BP_B3_D,
  inout wire  BP_CK0_C,
  inout wire  BP_CK0_T,
  inout wire  BP_CK1_C,
  inout wire  BP_CK1_T,
  inout wire  BP_ZN
);

  assign o_ao_rst_sync_n = i_ao_rst_n;
  assign o_noc_async_idle_req = 2'b00;
  assign o_noc_clken = 1'b1;
  assign o_noc_rst_n = i_ao_rst_n;
  assign o_lpddr_axi_m_ruser = 1'b0;
  assign o_lpddr_axi_m_buser = 1'b0;
  assign o_lpddr_cfg_apb4_s_pready = 1'b0;
  assign o_lpddr_cfg_apb4_s_pslverr = 1'b0;
  assign o_lpddr_syscfg_apb4_s_pready = 1'b0;
  assign o_lpddr_syscfg_apb4_s_prdata = 1'b0;
  assign o_lpddr_syscfg_apb4_s_pslverr = 1'b0;
  assign o_ctrl_sbr_done_intr = 1'b0;
  assign o_ctrl_derate_temp_limit_intr = 1'b0;
  assign o_ctrl_ecc_ap_err_intr = 1'b0;
  assign o_ctrl_ecc_corrected_err_intr = 1'b0;
  assign o_ctrl_ecc_uncorrected_err_intr = 1'b0;
  assign o_ctrl_rd_linkecc_corr_err_intr = 1'b0;
  assign o_ctrl_rd_linkecc_uncorr_err_intr = 1'b0;
  assign o_phy_pie_prog_err_intr = 1'b0;
  assign o_phy_ecc_err_intr = 1'b0;
  assign o_phy_rdfptrchk_err_intr = 1'b0;
  assign o_phy_pie_parity_err_intr = 1'b0;
  assign o_phy_acsm_parity_err_intr = 1'b0;
  assign o_phy_trng_fail_intr = 1'b0;
  assign o_phy_init_cmplt_intr = 1'b0;
  assign o_phy_trng_cmplt_intr = 1'b0;
  assign tdo_en = 1'b0;
  assign tdo = 1'b0;
  assign bisr_so = 1'b0;
  assign BP_MEMRESET_L = 1'b0;

  dv_axi_ram #(
      .ADDR_WIDTH(33),
      .DATA_WIDTH(256),
      .ID_WIDTH  (8),
      .MEM_TOTAL_BYTE_SIZE(8<<30)
  ) i_fake_lpddr (
      .clk          (i_lpddr_clk),
      .rst          (!i_global_rst_n),
      .s_axi_awid   (i_lpddr_axi_m_awid),
      .s_axi_awaddr (i_lpddr_axi_m_awaddr[32:0]),
      .s_axi_awlen  (i_lpddr_axi_m_awlen),
      .s_axi_awsize (i_lpddr_axi_m_awsize),
      .s_axi_awburst(i_lpddr_axi_m_awburst),
      .s_axi_awlock (i_lpddr_axi_m_awlock),
      .s_axi_awcache(i_lpddr_axi_m_awcache),
      .s_axi_awprot (i_lpddr_axi_m_awprot),
      .s_axi_awvalid(i_lpddr_axi_m_awvalid),
      .s_axi_awready(o_lpddr_axi_m_awready),
      .s_axi_wdata  (i_lpddr_axi_m_wdata),
      .s_axi_wstrb  (i_lpddr_axi_m_wstrb),
      .s_axi_wlast  (i_lpddr_axi_m_wlast),
      .s_axi_wvalid (i_lpddr_axi_m_wvalid),
      .s_axi_wready (o_lpddr_axi_m_wready),
      .s_axi_bid    (o_lpddr_axi_m_bid),
      .s_axi_bresp  (o_lpddr_axi_m_bresp),
      .s_axi_bvalid (o_lpddr_axi_m_bvalid),
      .s_axi_bready (i_lpddr_axi_m_bready),
      .s_axi_arid   (i_lpddr_axi_m_arid),
      .s_axi_araddr (i_lpddr_axi_m_araddr[32:0]),
      .s_axi_arlen  (i_lpddr_axi_m_arlen),
      .s_axi_arsize (i_lpddr_axi_m_arsize),
      .s_axi_arburst(i_lpddr_axi_m_arburst),
      .s_axi_arlock (i_lpddr_axi_m_arlock),
      .s_axi_arcache(i_lpddr_axi_m_arcache),
      .s_axi_arprot (i_lpddr_axi_m_arprot),
      .s_axi_arvalid(i_lpddr_axi_m_arvalid),
      .s_axi_arready(o_lpddr_axi_m_arready),
      .s_axi_rid    (o_lpddr_axi_m_rid),
      .s_axi_rdata  (o_lpddr_axi_m_rdata),
      .s_axi_rresp  (o_lpddr_axi_m_rresp),
      .s_axi_rlast  (o_lpddr_axi_m_rlast),
      .s_axi_rvalid (o_lpddr_axi_m_rvalid),
      .s_axi_rready (i_lpddr_axi_m_rready)
  );

endmodule
