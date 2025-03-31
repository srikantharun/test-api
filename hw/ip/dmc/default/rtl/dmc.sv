// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>

/// DMC (DataMovementCluster) contains all IFD's ODR's and AXI2MMIO of AI Core.
/// It's also used for pass through of busses accross the AI Core

module dmc
  import dmc_pkg::*, mmio_pkg::*, aic_common_pkg::*;
# (
  parameter int DMC_REGION_SLAVE_ID[DMC_NR_REGIONS] = {
    m_ifdw_idx, m_ifdw_idx, m_ifdw_idx,
    m_ifd0_idx, m_ifd0_idx, m_ifd0_idx,
    m_ifd1_idx, m_ifd1_idx, m_ifd1_idx,
    m_ifd2_idx, m_ifd2_idx, m_ifd2_idx,
    m_odr_idx,  m_odr_idx,  m_odr_idx,
    d_ifd0_idx, d_ifd0_idx, d_ifd0_idx,
    d_ifd1_idx, d_ifd1_idx, d_ifd1_idx,
    d_odr_idx,  d_odr_idx,  d_odr_idx
  },
  parameter longint DMC_REGION_ST_ADDR[DMC_NR_REGIONS] = {
    64'h0_0000, 64'h0_1000, 64'h0_8000,
    64'h1_0000, 64'h1_1000, 64'h1_8000,
    64'h2_0000, 64'h2_1000, 64'h2_8000,
    64'h3_0000, 64'h3_1000, 64'h3_8000,
    64'h4_0000, 64'h4_1000, 64'h4_8000,
    64'h5_0000, 64'h5_1000, 64'h5_8000,
    64'h6_0000, 64'h6_1000, 64'h6_8000,
    64'h7_0000, 64'h7_1000, 64'h7_8000
  },
  parameter longint DMC_REGION_END_ADDR[DMC_NR_REGIONS] = {
    64'h0_0fff, 64'h0_1fff, 64'h0_ffff,
    64'h1_0fff, 64'h1_1fff, 64'h1_ffff,
    64'h2_0fff, 64'h2_1fff, 64'h2_ffff,
    64'h3_0fff, 64'h3_1fff, 64'h3_ffff,
    64'h4_0fff, 64'h4_1fff, 64'h4_ffff,
    64'h5_0fff, 64'h5_1fff, 64'h5_ffff,
    64'h6_0fff, 64'h6_1fff, 64'h6_ffff,
    64'h7_0fff, 64'h7_1fff, 64'h7_ffff
  },

  // IFD/ODR dev regions:
  parameter aic_region_t DMC_DEV_REGION_ST_ADDR[DMC_NR_AXI_DEVS] = {
    aic_region_t'{'h0_0000, 'h0_1000, 'h0_8000},
    aic_region_t'{'h1_0000, 'h1_1000, 'h1_8000},
    aic_region_t'{'h2_0000, 'h2_1000, 'h2_8000},
    aic_region_t'{'h3_0000, 'h3_1000, 'h3_8000},
    aic_region_t'{'h4_0000, 'h4_1000, 'h4_8000},
    aic_region_t'{'h5_0000, 'h5_1000, 'h5_8000},
    aic_region_t'{'h6_0000, 'h6_1000, 'h6_8000},
    aic_region_t'{'h7_0000, 'h7_1000, 'h7_8000}
  },
  parameter aic_region_t DMC_DEV_REGION_END_ADDR[DMC_NR_AXI_DEVS] = {
    aic_region_t'{'h0_0fff, 'h0_1fff, 'h0_ffff},
    aic_region_t'{'h1_0fff, 'h1_1fff, 'h1_ffff},
    aic_region_t'{'h2_0fff, 'h2_1fff, 'h2_ffff},
    aic_region_t'{'h3_0fff, 'h3_1fff, 'h3_ffff},
    aic_region_t'{'h4_0fff, 'h4_1fff, 'h4_ffff},
    aic_region_t'{'h5_0fff, 'h5_1fff, 'h5_ffff},
    aic_region_t'{'h6_0fff, 'h6_1fff, 'h6_ffff},
    aic_region_t'{'h7_0fff, 'h7_1fff, 'h7_ffff}
  },
  parameter logic [AIC_HT_AXI_ADDR_WIDTH-1:0] L1_ST_ADDR = '0,
  parameter logic [AIC_HT_AXI_ADDR_WIDTH-1:0] L1_END_ADDR = '0
) (
  /// Clock, positive edge triggered
  input wire i_clk,
  /// Asynchronous reset, active low
  input wire i_rst_n,

  input logic i_scan_en,

  output logic [DMC_IRQ_W-1:0] o_irq,

  // axi streams:
    // IFD:
  output logic [DMC_NR_IFDS-1:0] o_dmc_ip_axis_m_tvalid,
  input  logic [DMC_NR_IFDS-1:0] i_dmc_ip_axis_m_tready,
  output logic [DMC_NR_IFDS-1:0][AIC_PWORD_WIDTH-1:0] o_dmc_ip_axis_m_tdata,
  output logic [DMC_NR_IFDS-1:0] o_dmc_ip_axis_m_tlast,
    // ODR:
  input  logic [DMC_NR_ODRS-1:0] i_ip_dmc_axis_s_tvalid,
  output logic [DMC_NR_ODRS-1:0] o_ip_dmc_axis_s_tready,
  input  logic [DMC_NR_ODRS-1:0][AIC_PWORD_WIDTH-1:0] i_ip_dmc_axis_s_tdata,
  input  logic [DMC_NR_ODRS-1:0] i_ip_dmc_axis_s_tlast,

  // MMIO L1:
    // DMC -> L1 read only (IFD + A2M)
  output mmio_pkg::mmio_dmc_ro_req_t [DMC_NR_IFDS:0] o_mmio_rd_m_req,
  input  mmio_pkg::mmio_dmc_ro_rsp_t [DMC_NR_IFDS:0] i_mmio_rd_m_rsp,
    // DMC -> L1 write only (ODR + A2M)
  output mmio_pkg::mmio_dmc_wo_req_t [DMC_NR_ODRS:0] o_mmio_wr_m_req,
  input  mmio_pkg::mmio_dmc_wo_rsp_t [DMC_NR_ODRS:0] i_mmio_wr_m_rsp,

  /////////////// Token ////////////
  output logic [DMC_NR_IFDS_ODRS-1:0][DMC_TOKENS_PROD-1:0] o_dev_prod_vld,
  input  logic [DMC_NR_IFDS_ODRS-1:0][DMC_TOKENS_PROD-1:0] i_dev_prod_rdy,
  input  logic [DMC_NR_IFDS_ODRS-1:0][DMC_TOKENS_CONS-1:0] i_dev_cons_vld,
  output logic [DMC_NR_IFDS_ODRS-1:0][DMC_TOKENS_CONS-1:0] o_dev_cons_rdy,

  ///// Timestamp:
  output logic [DMC_NR_IFDS_ODRS-1:0] o_ts_start,
  output logic [DMC_NR_IFDS_ODRS-1:0] o_ts_end,
  ///// ACD sync:
  output logic [DMC_NR_IFDS_ODRS-1:0] o_acd_sync,

  // A2M:
  //------------------------------------------------------
  // AXI write address channel
  input  logic                                   i_hp_axi_s_awvalid,
  input  logic [      AIC_HT_AXI_ADDR_WIDTH-1:0] i_hp_axi_s_awaddr,
  input  logic [      AIC_HT_AXI_S_ID_WIDTH-1:0] i_hp_axi_s_awid,
  input  logic [       AIC_HT_AXI_LEN_WIDTH-1:0] i_hp_axi_s_awlen,
  input  logic [      AIC_HT_AXI_SIZE_WIDTH-1:0] i_hp_axi_s_awsize,
  input  logic [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] i_hp_axi_s_awburst,
  input  logic [     AIC_HT_AXI_CACHE_WIDTH-1:0] i_hp_axi_s_awcache, // ASO-UNUSED_INPUT: not used
  input  logic [      AIC_HT_AXI_PROT_WIDTH-1:0] i_hp_axi_s_awprot, // ASO-UNUSED_INPUT: not used
  input  logic                                   i_hp_axi_s_awlock, // ASO-UNUSED_INPUT: not used
  output logic                                   o_hp_axi_s_awready,
  // AXI write data channel
  input  logic                                   i_hp_axi_s_wvalid,
  input  logic                                   i_hp_axi_s_wlast,
  input  logic [     AIC_HT_AXI_WSTRB_WIDTH-1:0] i_hp_axi_s_wstrb,
  input  logic [      AIC_HT_AXI_DATA_WIDTH-1:0] i_hp_axi_s_wdata,
  output logic                                   o_hp_axi_s_wready,
  // AXI write response channel
  output logic                                   o_hp_axi_s_bvalid,
  output logic [      AIC_HT_AXI_S_ID_WIDTH-1:0] o_hp_axi_s_bid,
  output logic [      AIC_HT_AXI_RESP_WIDTH-1:0] o_hp_axi_s_bresp,
  input  logic                                   i_hp_axi_s_bready,
  // AXI read address channel
  input  logic                                   i_hp_axi_s_arvalid,
  input  logic [      AIC_HT_AXI_ADDR_WIDTH-1:0] i_hp_axi_s_araddr,
  input  logic [      AIC_HT_AXI_S_ID_WIDTH-1:0] i_hp_axi_s_arid,
  input  logic [       AIC_HT_AXI_LEN_WIDTH-1:0] i_hp_axi_s_arlen,
  input  logic [      AIC_HT_AXI_SIZE_WIDTH-1:0] i_hp_axi_s_arsize,
  input  logic [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] i_hp_axi_s_arburst,
  input  logic [     AIC_HT_AXI_CACHE_WIDTH-1:0] i_hp_axi_s_arcache, // ASO-UNUSED_INPUT: not used
  input  logic [      AIC_HT_AXI_PROT_WIDTH-1:0] i_hp_axi_s_arprot, // ASO-UNUSED_INPUT: not used
  input  logic                                   i_hp_axi_s_arlock, // ASO-UNUSED_INPUT: not used
  output logic                                   o_hp_axi_s_arready,
  // AXI read data/response channel
  output logic                                   o_hp_axi_s_rvalid,
  output logic                                   o_hp_axi_s_rlast,
  output logic [      AIC_HT_AXI_S_ID_WIDTH-1:0] o_hp_axi_s_rid,
  output logic [      AIC_HT_AXI_DATA_WIDTH-1:0] o_hp_axi_s_rdata,
  output logic [      AIC_HT_AXI_RESP_WIDTH-1:0] o_hp_axi_s_rresp,
  input  logic                                   i_hp_axi_s_rready,


  // CFG:
  //------------------------------------------------------
  // AXI write address channel
  input  logic                                   i_cfg_axi_s_awvalid,
  input  logic [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] i_cfg_axi_s_awaddr,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_awid,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_awlen,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_awsize,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_awburst,
  output logic                                   o_cfg_axi_s_awready,
  // AXI write data channel
  input  logic                                   i_cfg_axi_s_wvalid,
  input  logic                                   i_cfg_axi_s_wlast,
  input  logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] i_cfg_axi_s_wstrb,
  input  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_cfg_axi_s_wdata,
  output logic                                   o_cfg_axi_s_wready,
  // AXI write response channel
  output logic                                   o_cfg_axi_s_bvalid,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_bid,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_bresp,
  input  logic                                   i_cfg_axi_s_bready,
  // AXI read address channel
  input  logic                                   i_cfg_axi_s_arvalid,
  input  logic [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] i_cfg_axi_s_araddr,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_arid,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_arlen,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_arsize,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_arburst,
  output logic                                   o_cfg_axi_s_arready,
  // AXI read data/response channel
  output logic                                   o_cfg_axi_s_rvalid,
  output logic                                   o_cfg_axi_s_rlast,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_rid,
  output logic [      AIC_LT_AXI_DATA_WIDTH-1:0] o_cfg_axi_s_rdata,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_rresp,
  input  logic                                   i_cfg_axi_s_rready,

  // Sidebands:
  input logic [AIC_CID_WIDTH-1:0]   i_cid,
  output aic_common_pkg::aic_dev_obs_t [DMC_NR_IFDS_ODRS-1:0] o_dmc_obs,

  // Instruction memory SRAM sideband signals
  input  axe_tcl_sram_pkg::impl_inp_t i_sram_impl,
  output axe_tcl_sram_pkg::impl_oup_t o_sram_impl
);

  axe_tcl_sram_pkg::impl_inp_t [DMC_NR_IFDS_ODRS-1:0] inst_sram_impl_inp;
  axe_tcl_sram_pkg::impl_oup_t [DMC_NR_IFDS_ODRS-1:0] inst_sram_impl_oup;

  // AXI bus:
  ///// AXI slaves:
  // Write Address Channel
  logic [DMC_NR_AXI_DEVS-1:0][AIC_LT_AXI_S_ID_WIDTH-1:0] awid_s;
  logic [DMC_NR_AXI_DEVS-1:0][AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] awaddr_s;
  logic [DMC_NR_AXI_DEVS-1:0][AIC_LT_AXI_LEN_WIDTH-1:0] awlen_s;
  logic [DMC_NR_AXI_DEVS-1:0][2:0] awsize_s;
  logic [DMC_NR_AXI_DEVS-1:0][1:0] awburst_s;
  logic [DMC_NR_AXI_DEVS-1:0]awvalid_s;
  logic [DMC_NR_AXI_DEVS-1:0]awready_s;
  // Read Address Channel
  logic [DMC_NR_AXI_DEVS-1:0][AIC_LT_AXI_S_ID_WIDTH-1:0] arid_s;
  logic [DMC_NR_AXI_DEVS-1:0][AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] araddr_s;
  logic [DMC_NR_AXI_DEVS-1:0][AIC_HT_AXI_LEN_WIDTH-1:0] arlen_s;
  logic [DMC_NR_AXI_DEVS-1:0][2:0] arsize_s;
  logic [DMC_NR_AXI_DEVS-1:0][1:0] arburst_s;
  logic [DMC_NR_AXI_DEVS-1:0]arvalid_s;
  logic [DMC_NR_AXI_DEVS-1:0]arready_s;
  // Write  Data Channel
  logic [DMC_NR_AXI_DEVS-1:0][AIC_LT_AXI_DATA_WIDTH-1:0] wdata_s;
  logic [AIC_LT_AXI_DATA_WIDTH_B-1:0][DMC_NR_AXI_DEVS-1:0] wstrb_s;
  logic [DMC_NR_AXI_DEVS-1:0]wlast_s;
  logic [DMC_NR_AXI_DEVS-1:0]wvalid_s;
  logic [DMC_NR_AXI_DEVS-1:0]wready_s;
  // Read Data Channel
  logic [DMC_NR_AXI_DEVS-1:0][AIC_LT_AXI_S_ID_WIDTH-1:0] rid_s;
  logic [DMC_NR_AXI_DEVS-1:0][AIC_LT_AXI_DATA_WIDTH-1:0] rdata_s;
  logic [DMC_NR_AXI_DEVS-1:0][1:0] rresp_s;
  logic [DMC_NR_AXI_DEVS-1:0]rlast_s;
  logic [DMC_NR_AXI_DEVS-1:0]rvalid_s;
  logic [DMC_NR_AXI_DEVS-1:0]rready_s;
  // Write Response Channel
  logic [DMC_NR_AXI_DEVS-1:0][AIC_LT_AXI_S_ID_WIDTH-1:0] bid_s;
  logic [DMC_NR_AXI_DEVS-1:0][1:0] bresp_s;
  logic [DMC_NR_AXI_DEVS-1:0]bvalid_s;
  logic [DMC_NR_AXI_DEVS-1:0]bready_s;

  ///////////////////////////////////
  logic [$clog2(DMC_NR_AXI_DEVS+1)-1:0] bus_sel_rd;
  logic [$clog2(DMC_NR_AXI_DEVS+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(DMC_NR_AXI_DEVS),
    .NR_REGIONS(DMC_NR_REGIONS),
    .REGION_ST_ADDR(DMC_REGION_ST_ADDR),
    .REGION_END_ADDR(DMC_REGION_END_ADDR),
    .REGION_SLAVE_ID(DMC_REGION_SLAVE_ID)
  ) u_ext_decode_wr (
    .addr_in(i_cfg_axi_s_awaddr),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(DMC_NR_AXI_DEVS),
    .NR_REGIONS(DMC_NR_REGIONS),
    .REGION_ST_ADDR(DMC_REGION_ST_ADDR),
    .REGION_END_ADDR(DMC_REGION_END_ADDR),
    .REGION_SLAVE_ID(DMC_REGION_SLAVE_ID)
  ) u_ext_decode_rd (
    .addr_in(i_cfg_axi_s_araddr),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  // AXI bus:
  simple_axi_demux #(
    .NR_MASTERS(DMC_NR_AXI_DEVS),
    .IDW(AIC_LT_AXI_S_ID_WIDTH),
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DW(AIC_LT_AXI_DATA_WIDTH),
    .BW(AIC_LT_AXI_LEN_WIDTH),
    .SL_WREQ_SHIELD(2),
    .SL_RREQ_SHIELD(2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR(10),
    .EXT_SEL(1)
  ) u_bus (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),

    // IP -> DMC:
    // write address channel:
    .s_awvalid(i_cfg_axi_s_awvalid),
    .s_awaddr(i_cfg_axi_s_awaddr),
    .s_awid(i_cfg_axi_s_awid),
    .s_awlen(i_cfg_axi_s_awlen),
    .s_awsize(i_cfg_axi_s_awsize),
    .s_awburst(i_cfg_axi_s_awburst),
    .s_awlock('0),
    .s_awcache('0),
    .s_awprot('0),
    .s_awready(o_cfg_axi_s_awready),

    // write data channel:
    .s_wvalid(i_cfg_axi_s_wvalid),
    .s_wdata(i_cfg_axi_s_wdata),
    .s_wstrb(i_cfg_axi_s_wstrb),
    .s_wlast(i_cfg_axi_s_wlast),
    .s_wready(o_cfg_axi_s_wready),

    // write response channel:
    .s_bvalid(o_cfg_axi_s_bvalid),
    .s_bid(o_cfg_axi_s_bid),
    .s_bresp(o_cfg_axi_s_bresp),
    .s_bready(i_cfg_axi_s_bready),

    // read address channel:
    .s_arvalid(i_cfg_axi_s_arvalid),
    .s_araddr(i_cfg_axi_s_araddr),
    .s_arid(i_cfg_axi_s_arid),
    .s_arlen(i_cfg_axi_s_arlen),
    .s_arsize(i_cfg_axi_s_arsize),
    .s_arburst(i_cfg_axi_s_arburst),
    .s_arlock('0),
    .s_arcache('0),
    .s_arprot('0),
    .s_arready(o_cfg_axi_s_arready),

    // read response channel:
    .s_rvalid(o_cfg_axi_s_rvalid),
    .s_rid(o_cfg_axi_s_rid),
    .s_rdata(o_cfg_axi_s_rdata),
    .s_rresp(o_cfg_axi_s_rresp),
    .s_rlast(o_cfg_axi_s_rlast),
    .s_rready(i_cfg_axi_s_rready),

    // DMC -> devs:
    // write address channel:
    .m_awvalid(awvalid_s),
    .m_awaddr(awaddr_s),
    .m_awid(awid_s),
    .m_awlen(awlen_s),
    .m_awsize(awsize_s),
    .m_awburst(awburst_s),
    .m_awlock(), // ASO-UNUSED_OUTPUT: not used
    .m_awcache(), // ASO-UNUSED_OUTPUT: not used
    .m_awprot(), // ASO-UNUSED_OUTPUT: not used
    .m_awready(awready_s),

    // write data channel:
    .m_wvalid(wvalid_s),
    .m_wdata (wdata_s),
    .m_wstrb (wstrb_s),
    .m_wlast (wlast_s),
    .m_wready(wready_s),

    // write response channel:
    .m_bvalid(bvalid_s),
    .m_bid(bid_s),
    .m_bresp(bresp_s),
    .m_bready(bready_s),

    // read address channel:
    .m_arvalid(arvalid_s),
    .m_araddr(araddr_s),
    .m_arid(arid_s),
    .m_arlen(arlen_s),
    .m_arsize(arsize_s),
    .m_arburst(arburst_s),
    .m_arlock(), // ASO-UNUSED_OUTPUT: not used
    .m_arcache(), // ASO-UNUSED_OUTPUT: not used
    .m_arprot(), // ASO-UNUSED_OUTPUT: not used
    .m_arready(arready_s),

    // read response channel:
    .m_rvalid(rvalid_s),
    .m_rid(rid_s),
    .m_rdata(rdata_s),
    .m_rresp(rresp_s),
    .m_rlast(rlast_s),
    .m_rready(rready_s)
  );

  axe_tcl_sram_cfg #(
    .NUM_SRAMS(DMC_NR_IFDS_ODRS)
  ) u_sram_cfg (
    .i_s(i_sram_impl),
    .o_s(o_sram_impl),
    .o_m(inst_sram_impl_inp),
    .i_m(inst_sram_impl_oup)
  );


  ////////////////////////////
  // IFD's:
  for (genvar dev=0; unsigned'(dev)<DMC_NR_IFDS; dev++) begin : g_ifd
    ifd #(
      .IDW(AIC_LT_AXI_S_ID_WIDTH),
      .AW(AIC_HT_AXI_ADDR_WIDTH),
      .AXI_AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
      .AXI_DW(AIC_LT_AXI_DATA_WIDTH),
      .DW(AIC_PWORD_I8_WIDTH),
      .BW(AIC_LT_AXI_LEN_WIDTH),
      .L1_LAT(DMC_MAX_L1_LATENCY),
      .L1_ST_ADDR(L1_ST_ADDR[ifd_odr_pkg::IFD_ODR_DP_AW-1:0]),
      .L1_END_ADDR(L1_END_ADDR[ifd_odr_pkg::IFD_ODR_DP_AW-1:0]),

      .HAS_VTRSP(DMC_DEV_HAS_VTRSP[dev]),

      .NR_TOK_PROD(DMC_TOKENS_PROD),
      .NR_TOK_CONS(DMC_TOKENS_CONS),
      .MAX_OUTST_CMDS(DMC_IFD_MAX_OUTST_CMDS),
      .CMD_FIFO_DEPTH(DMC_IFD_CMD_FIFO_DEPTH),
      .CMD_FIFO_WIDTH(DMC_IFD_CMD_FIFO_WIDTH),
      .DEFMEM_DEPTH(DMC_IFD_DM_DEPTH),
      .HAS_DECOMP(DMC_DEV_HAS_DECOMP[dev]),
      .REGION_ST_ADDR(DMC_DEV_REGION_ST_ADDR[dev]),
      .REGION_END_ADDR(DMC_DEV_REGION_END_ADDR[dev])
    ) u_ifd (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    .scan_en(i_scan_en),
    .irq(o_irq[dev]),

    ///// AXI slave:
    .awid(awid_s[dev]),
    .awaddr(awaddr_s[dev]),
    .awlen(awlen_s[dev]),
    .awsize(awsize_s[dev]),
    .awburst(awburst_s[dev]),
    .awvalid(awvalid_s[dev]),
    .awready(awready_s[dev]),

    .arid(arid_s[dev]),
    .araddr(araddr_s[dev]),
    .arlen(arlen_s[dev]),
    .arsize(arsize_s[dev]),
    .arburst(arburst_s[dev]),
    .arvalid(arvalid_s[dev]),
    .arready(arready_s[dev]),

    .wdata (wdata_s[dev]),
    .wstrb (wstrb_s[dev]),
    .wlast (wlast_s[dev]),
    .wvalid(wvalid_s[dev]),
    .wready(wready_s[dev]),

    .rid(rid_s[dev]),
    .rdata(rdata_s[dev]),
    .rresp(rresp_s[dev]),
    .rlast(rlast_s[dev]),
    .rvalid(rvalid_s[dev]),
    .rready(rready_s[dev]),

    .bid(bid_s[dev]),
    .bresp(bresp_s[dev]),
    .bvalid(bvalid_s[dev]),
    .bready(bready_s[dev]),

    ///// Tokens:
    .tok_prod_vld(o_dev_prod_vld[dev]),
    .tok_prod_rdy(i_dev_prod_rdy[dev]),
    .tok_cons_vld(i_dev_cons_vld[dev]),
    .tok_cons_rdy(o_dev_cons_rdy[dev]),

    ///// Timestamp:
    .o_ts_start(o_ts_start[dev]),
    .o_ts_end(o_ts_end[dev]),
    ///// ACD sync:
    .o_acd_sync(o_acd_sync[dev]),

    ///// MMIO:
    .mm_req(o_mmio_rd_m_req[dev]),
    .mm_rsp(i_mmio_rd_m_rsp[dev]),

    ///// AXIS:
    .axis_m_valid(o_dmc_ip_axis_m_tvalid[dev]),
    .axis_m_ready(i_dmc_ip_axis_m_tready[dev]),
    .axis_m_data (o_dmc_ip_axis_m_tdata[dev]),
    .axis_m_last (o_dmc_ip_axis_m_tlast[dev]),

    ///// Observation
    .obs(o_dmc_obs[dev]),

    ///// Block Identification
    .cid     (i_cid[AIC_CID_SUB_W-1:0]),
    .block_id(DMC_BLOCK_ID[dev]),

    .i_sram_impl(inst_sram_impl_inp[dev]),
    .o_sram_impl(inst_sram_impl_oup[dev])
  );
  end

  ////////////////////////////
  // ODR's:
  for (genvar dev=DMC_NR_IFDS; unsigned'(dev)<DMC_NR_IFDS+DMC_NR_ODRS; dev++) begin : g_odr
    odr #(
    .IDW(AIC_LT_AXI_S_ID_WIDTH),
    .AW(AIC_HT_AXI_ADDR_WIDTH),
    .AXI_AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .AXI_DW(AIC_LT_AXI_DATA_WIDTH),
    .DW(AIC_PWORD_I8_WIDTH),
    .BW(AIC_LT_AXI_LEN_WIDTH),
    .L1_LAT(DMC_MAX_L1_LATENCY),
    .L1_ST_ADDR(L1_ST_ADDR[ifd_odr_pkg::IFD_ODR_DP_AW-1:0]),
    .L1_END_ADDR(L1_END_ADDR[ifd_odr_pkg::IFD_ODR_DP_AW-1:0]),

    .HAS_VTRSP(DMC_DEV_HAS_VTRSP[dev]),

    .NR_TOK_PROD(DMC_TOKENS_PROD),
    .NR_TOK_CONS(DMC_TOKENS_CONS),
    .MAX_OUTST_CMDS(DMC_ODR_MAX_OUTST_CMDS),
    .CMD_FIFO_DEPTH(DMC_ODR_CMD_FIFO_DEPTH),
    .CMD_FIFO_WIDTH(DMC_ODR_CMD_FIFO_WIDTH),
    .DEFMEM_DEPTH(DMC_ODR_DM_DEPTH),
    .REGION_ST_ADDR(DMC_DEV_REGION_ST_ADDR[dev]),
    .REGION_END_ADDR(DMC_DEV_REGION_END_ADDR[dev])
    ) u_odr (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    .scan_en(i_scan_en),
    .irq(o_irq[dev]),

    ///// AXI slave:
    .awid(awid_s[dev]),
    .awaddr(awaddr_s[dev]),
    .awlen(awlen_s[dev]),
    .awsize(awsize_s[dev]),
    .awburst(awburst_s[dev]),
    .awvalid(awvalid_s[dev]),
    .awready(awready_s[dev]),

    .arid(arid_s[dev]),
    .araddr(araddr_s[dev]),
    .arlen(arlen_s[dev]),
    .arsize(arsize_s[dev]),
    .arburst(arburst_s[dev]),
    .arvalid(arvalid_s[dev]),
    .arready(arready_s[dev]),

    .wdata (wdata_s[dev]),
    .wstrb (wstrb_s[dev]),
    .wlast (wlast_s[dev]),
    .wvalid(wvalid_s[dev]),
    .wready(wready_s[dev]),

    .rid(rid_s[dev]),
    .rdata(rdata_s[dev]),
    .rresp(rresp_s[dev]),
    .rlast(rlast_s[dev]),
    .rvalid(rvalid_s[dev]),
    .rready(rready_s[dev]),

    .bid(bid_s[dev]),
    .bresp(bresp_s[dev]),
    .bvalid(bvalid_s[dev]),
    .bready(bready_s[dev]),

    ///// Tokens:
    .tok_prod_vld(o_dev_prod_vld[dev]),
    .tok_prod_rdy(i_dev_prod_rdy[dev]),
    .tok_cons_vld(i_dev_cons_vld[dev]),
    .tok_cons_rdy(o_dev_cons_rdy[dev]),

    ///// Timestamp:
    .o_ts_start(o_ts_start[dev]),
    .o_ts_end(o_ts_end[dev]),
    ///// ACD sync:
    .o_acd_sync(o_acd_sync[dev]),

    ///// MMIO:
    .mm_req(o_mmio_wr_m_req[dev - DMC_NR_IFDS]),
    .mm_rsp(i_mmio_wr_m_rsp[dev - DMC_NR_IFDS]),

    ///// AXIS:
    .axis_s_valid(i_ip_dmc_axis_s_tvalid[dev - DMC_NR_IFDS]),
    .axis_s_ready(o_ip_dmc_axis_s_tready[dev - DMC_NR_IFDS]),
    .axis_s_data (i_ip_dmc_axis_s_tdata[dev - DMC_NR_IFDS]),
    .axis_s_last (i_ip_dmc_axis_s_tlast[dev - DMC_NR_IFDS]),

    ///// Observation
    .obs(o_dmc_obs[dev]),

    ///// Block Identification
    .cid     (i_cid[AIC_CID_SUB_W-1:0]),
    .block_id(DMC_BLOCK_ID[dev]),

    .i_sram_impl(inst_sram_impl_inp[dev]),
    .o_sram_impl(inst_sram_impl_oup[dev])
  );
  end

  ////////////////////////////
  // AXI2MMIO:
  logic [DMC_L1_BASE_ADDR_WIDTH-1:0] l1_base_address;
  localparam int unsigned L1BaseAddrZeroMsbW = DMC_L1_BASE_ADDR_WIDTH - unsigned'((AIC_CID_LSB-AIC_VA_BASE_LSB) + AIC_CID_SUB_W);
  always_comb l1_base_address = {(L1BaseAddrZeroMsbW)'(0), // set upper msb's to zero
                                  i_cid[AIC_CID_SUB_W-1:0], // CID (dynamic part)
                                  L1_ST_ADDR[AIC_CID_LSB-1:AIC_VA_BASE_LSB] // rest of static part of L1
                                };
  axi2mmio_bridge #(
    .AXI_S_ID_WIDTH(AIC_HT_AXI_S_ID_WIDTH),
    .AXI_ADDR_WIDTH(AIC_HT_AXI_ADDR_WIDTH),
    .AXI_WSTRB_WIDTH(AIC_HT_AXI_WSTRB_WIDTH),
    .AXI_DATA_WIDTH(AIC_HT_AXI_DATA_WIDTH),
    .MEM_BASE_ADDRESS_WIDTH(DMC_L1_BASE_ADDR_WIDTH),
    .MAX_MEM_LATENCY(DMC_MAX_L1_LATENCY)
  ) u_a2m (
    // Clock and reset signals
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    .i_axi_s_awvalid(i_hp_axi_s_awvalid),
    .i_axi_s_awaddr(i_hp_axi_s_awaddr),
    .i_axi_s_awid(i_hp_axi_s_awid),
    .i_axi_s_awlen(i_hp_axi_s_awlen),
    .i_axi_s_awsize(i_hp_axi_s_awsize),
    .i_axi_s_awburst(i_hp_axi_s_awburst),
    .o_axi_s_awready(o_hp_axi_s_awready),

    .i_axi_s_wvalid(i_hp_axi_s_wvalid),
    .i_axi_s_wlast(i_hp_axi_s_wlast),
    .i_axi_s_wstrb(i_hp_axi_s_wstrb),
    .i_axi_s_wdata(i_hp_axi_s_wdata),
    .o_axi_s_wready(o_hp_axi_s_wready),

    .o_axi_s_bvalid(o_hp_axi_s_bvalid),
    .o_axi_s_bid(o_hp_axi_s_bid),
    .o_axi_s_bresp(o_hp_axi_s_bresp),
    .i_axi_s_bready(i_hp_axi_s_bready),

    .i_axi_s_arvalid(i_hp_axi_s_arvalid),
    .i_axi_s_araddr(i_hp_axi_s_araddr),
    .i_axi_s_arid(i_hp_axi_s_arid),
    .i_axi_s_arlen(i_hp_axi_s_arlen),
    .i_axi_s_arsize(i_hp_axi_s_arsize),
    .i_axi_s_arburst(i_hp_axi_s_arburst),
    .o_axi_s_arready(o_hp_axi_s_arready),

    .o_axi_s_rvalid(o_hp_axi_s_rvalid),
    .o_axi_s_rlast(o_hp_axi_s_rlast),
    .o_axi_s_rid(o_hp_axi_s_rid),
    .o_axi_s_rdata(o_hp_axi_s_rdata),
    .o_axi_s_rresp(o_hp_axi_s_rresp),
    .i_axi_s_rready(i_hp_axi_s_rready),

    .o_mmio_s_wr_req(o_mmio_wr_m_req[DMC_NR_ODRS]),
    .i_mmio_s_wr_rsp(i_mmio_wr_m_rsp[DMC_NR_ODRS]),

    .o_mmio_s_rd_req(o_mmio_rd_m_req[DMC_NR_IFDS]),
    .i_mmio_s_rd_rsp(i_mmio_rd_m_rsp[DMC_NR_IFDS]),

    .i_mem_base_address(l1_base_address)
  );
endmodule
