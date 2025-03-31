// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Europa block for DWPU, IAU DPU
///
module aic_did
  import aic_common_pkg::*;
  import token_mgr_mapping_aic_pkg::*;
(
  /// Clock, positive edge triggered
  input wire  i_clk,
  /// Asynchronous reset, active low
  // doc async
  input wire  i_rst_n,
  // doc sync i_clk

  ////////////////////
  // Observability ///
  ////////////////////

  /// Observability of DWPU
  output logic [AIC_DEV_OBS_DW-1:0] o_dwpu_obs,
  /// Observability of IAU
  output logic [AIC_DEV_OBS_DW-1:0]  o_iau_obs,
  /// Observability of DPU
  output logic [AIC_DEV_OBS_DW-1:0]  o_dpu_obs,

  ///// Timestamp:
  output logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] o_ts_start,
  output logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] o_ts_end,
  ///// ACD sync:
  output logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] o_acd_sync,

  ////////////////////////////////
  /// Interrupts and identifier //
  ////////////////////////////////
  output logic [              2:0]   o_irq,

  input  logic [AIC_CID_WIDTH-1:0]   i_cid,

  //////////////////////////////////
  // Tokens of the ai_core subips //
  //////////////////////////////////

  output logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0]  o_dwpu_tok_prod_vld,
  input  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0]  i_dwpu_tok_prod_rdy,
  input  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0]  i_dwpu_tok_cons_vld,
  output logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0]  o_dwpu_tok_cons_rdy,

  output logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] o_iau_tok_prod_vld,
  input  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_iau_tok_prod_rdy,
  input  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_iau_tok_cons_vld,
  output logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] o_iau_tok_cons_rdy,

  output logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] o_dpu_tok_prod_vld,
  input  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_dpu_tok_prod_rdy,
  input  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_dpu_tok_cons_vld,
  output logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] o_dpu_tok_cons_rdy,

  //////////////////
  // AXI LT NOC S //
  //////////////////
  // AXI write address channel
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_awid,
  input  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_awaddr,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_awlen,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_awsize,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_awburst,
  input  logic                                   i_cfg_axi_s_awvalid,
  output logic                                   o_cfg_axi_s_awready,
  // AXI write data channel
  input  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_cfg_axi_s_wdata,
  input  logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] i_cfg_axi_s_wstrb,
  input  logic                                   i_cfg_axi_s_wlast,
  input  logic                                   i_cfg_axi_s_wvalid,
  output logic                                   o_cfg_axi_s_wready,
  // AXI write response channel
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_bid,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_bresp,
  output logic                                   o_cfg_axi_s_bvalid,
  input  logic                                   i_cfg_axi_s_bready,
  // AXI read address channel
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_arid,
  input  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_araddr,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_arlen,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_arsize,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_arburst,
  input  logic                                   i_cfg_axi_s_arvalid,
  output logic                                   o_cfg_axi_s_arready,
  // AXI read data/response channel
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_rid,
  output logic [      AIC_LT_AXI_DATA_WIDTH-1:0] o_cfg_axi_s_rdata,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_rresp,
  output logic                                   o_cfg_axi_s_rlast,
  output logic                                   o_cfg_axi_s_rvalid,
  input  logic                                   i_cfg_axi_s_rready,

  ////////////////
  // AXI Stream //
  ////////////////

  // IFD0 -> DWPU AXI stream
  input  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_ifd0_axis_s_tdata,
  input  logic                                     i_ifd0_axis_s_tlast,
  input  logic                                     i_ifd0_axis_s_tvalid,
  output logic                                     o_ifd0_axis_s_tready,

  // IFD1 -> DPU AXI stream
  input  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_ifd1_axis_s_tdata,
  input  logic                                     i_ifd1_axis_s_tlast,
  input  logic                                     i_ifd1_axis_s_tvalid,
  output logic                                     o_ifd1_axis_s_tready,

  // DPU -> ODR AXI stream
  output logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] o_odr_axis_m_tdata,
  output logic                                     o_odr_axis_m_tlast,
  output logic                                     o_odr_axis_m_tvalid,
  input  logic                                     i_odr_axis_m_tready,

  ////////////////////////////////
  // SRAM configuration signals //
  ////////////////////////////////
  /// Margin adjustment control selection
  input  logic [1:0] i_sram_mcs,
  /// Margin adjustment control selection write
  input  logic       i_sram_mcsw,
  /// Retention mode enable input pin (power gating)
  input  logic       i_sram_ret,
  /// Power down enable, active high (power gating)
  input  logic       i_sram_pde,
  /// Scan enable, active high
  input  logic       i_sram_se,
  /// Margin adjustment for access disturbance margin enhancement (Vmin Feature Control Pins)
  input  logic [2:0] i_sram_adme,
  /// Power up ready negative
  output logic       o_sram_prn
);

  logic [AIC_CID_SUB_W-1:0] cid;
  always_comb cid = i_cid[AIC_CID_SUB_W-1:0];

  /////////////////////////////////
  // SRAM implementation signals //
  /////////////////////////////////
  axe_tcl_sram_pkg::impl_inp_t sram_impl_inp_aic_did;
  axe_tcl_sram_pkg::impl_oup_t sram_impl_oup_aic_did;

  axe_tcl_sram_pkg::impl_inp_t sram_impl_inp_dwpu;
  axe_tcl_sram_pkg::impl_oup_t sram_impl_oup_dwpu;

  axe_tcl_sram_pkg::impl_inp_t sram_impl_inp_dpu;
  axe_tcl_sram_pkg::impl_oup_t sram_impl_oup_dpu;

  always_comb sram_impl_inp_aic_did = axe_tcl_sram_pkg::impl_inp_t'{
    mcs:     i_sram_mcs,
    mcsw:    i_sram_mcsw,
    ret:     i_sram_ret,
    pde:     i_sram_pde,
    se:      i_sram_se,
    adme:    i_sram_adme,
    default: '0
  };
  always_comb o_sram_prn = sram_impl_oup_aic_did.prn;

  axe_tcl_sram_cfg #(
    .NUM_SRAMS (2)
  ) u_sram_cfg_impl (
    .i_s(sram_impl_inp_aic_did),
    .o_s(sram_impl_oup_aic_did),
    .o_m({sram_impl_inp_dpu, sram_impl_inp_dwpu}),
    .i_m({sram_impl_oup_dpu, sram_impl_oup_dwpu})
  );

  ///////////////////////////////////////////////
  // Additional pipelines to ease output paths //
  ///////////////////////////////////////////////
  logic [AIC_DEV_OBS_DW-1:0] dwpu_obs;
  logic [AIC_DEV_OBS_DW-1:0] iau_obs;
  logic [AIC_DEV_OBS_DW-1:0] dpu_obs;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] ts_start;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] ts_end;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] acd_sync;
  logic [2:0] irq;

  logic dwpu_obs_update;
  logic iau_obs_update;
  logic dpu_obs_update;
  logic ts_start_update;
  logic ts_end_update;
  logic acd_sync_update;
  logic irq_update;

  always_comb dwpu_obs_update = o_dwpu_obs != dwpu_obs;
  always_comb iau_obs_update  = o_iau_obs  != iau_obs;
  always_comb dpu_obs_update  = o_dpu_obs  != dpu_obs;
  always_comb ts_start_update = o_ts_start != ts_start;
  always_comb ts_end_update   = o_ts_end   != ts_end;
  always_comb acd_sync_update = o_acd_sync != acd_sync;
  always_comb irq_update      = o_irq      != irq;

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      o_dwpu_obs <= '0;
      o_iau_obs  <= '0;
      o_dpu_obs  <= '0;
      o_ts_start <= '0;
      o_ts_end   <= '0;
      o_acd_sync <= '0;
      o_irq      <= '0;
    end else begin
      if (dwpu_obs_update) o_dwpu_obs <= dwpu_obs;
      if (iau_obs_update)  o_iau_obs  <= iau_obs;
      if (dpu_obs_update)  o_dpu_obs  <= dpu_obs;
      if (ts_start_update) o_ts_start <= ts_start;
      if (ts_end_update)   o_ts_end   <= ts_end;
      if (acd_sync_update) o_acd_sync <= acd_sync;
      if (irq_update)      o_irq      <= irq;
    end
  end

  ///////////////////////////////////
  // AXI Demux                     //
  // With instantiation sanitation //
  ///////////////////////////////////

  aic_did_pkg::axi_id_t   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_awid;
  aic_did_pkg::axi_addr_t [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_awaddr;
  axi_pkg::axi_len_t      [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_awlen;
  axi_pkg::axi_size_t     [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_awsize;
  axi_pkg::axi_burst_t    [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_awburst;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_awvalid;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_awready;

  aic_did_pkg::axi_data_t [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_wdata;
  aic_did_pkg::axi_strb_t [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_wstrb;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_wlast;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_wvalid;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_wready;

  aic_did_pkg::axi_id_t   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_bid;
  axi_pkg::axi_resp_t     [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_bresp;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_bvalid;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_bready;

  aic_did_pkg::axi_id_t   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_arid;
  aic_did_pkg::axi_addr_t [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_araddr;
  axi_pkg::axi_len_t      [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_arlen;
  axi_pkg::axi_size_t     [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_arsize;
  axi_pkg::axi_burst_t    [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_arburst;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_arvalid;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_arready;

  aic_did_pkg::axi_id_t   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_rid;
  aic_did_pkg::axi_data_t [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_rdata;
  axi_pkg::axi_resp_t     [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_rresp;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_rlast;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_rvalid;
  logic                   [aic_did_pkg::NUM_AXI_ENDPOINTS-1:0] cfg_axi_s_rready;

  if ($bits(i_cfg_axi_s_awid)    != $bits(cfg_axi_s_awid[0]))    $fatal(1, "Problem on 'cfg_axi_s_awid' width");
  // if ($bits(i_cfg_axi_s_awaddr)  != $bits(cfg_axi_s_awaddr[0]))  $fatal(1, "Problem on 'cfg_axi_s_awaddr' width");
  if ($bits(i_cfg_axi_s_awlen)   != $bits(cfg_axi_s_awlen[0]))   $fatal(1, "Problem on 'cfg_axi_s_awlen' width");
  if ($bits(i_cfg_axi_s_awsize)  != $bits(cfg_axi_s_awsize[0]))  $fatal(1, "Problem on 'cfg_axi_s_awsize' width");
  if ($bits(i_cfg_axi_s_awburst) != $bits(cfg_axi_s_awburst[0])) $fatal(1, "Problem on 'cfg_axi_s_awburst' width");
  if ($bits(i_cfg_axi_s_awvalid) != $bits(cfg_axi_s_awvalid[0])) $fatal(1, "Problem on 'cfg_axi_s_awvalid' width");
  if ($bits(o_cfg_axi_s_awready) != $bits(cfg_axi_s_awready[0])) $fatal(1, "Problem on 'cfg_axi_s_awready' width");

  if ($bits(i_cfg_axi_s_wdata)   != $bits(cfg_axi_s_wdata[0]))   $fatal(1, "Problem on 'cfg_axi_s_wdata' width");
  if ($bits(i_cfg_axi_s_wstrb)   != $bits(cfg_axi_s_wstrb[0]))   $fatal(1, "Problem on 'cfg_axi_s_wstrb' width");
  if ($bits(i_cfg_axi_s_wlast)   != $bits(cfg_axi_s_wlast[0]))   $fatal(1, "Problem on 'cfg_axi_s_wlast' width");
  if ($bits(i_cfg_axi_s_wvalid)  != $bits(cfg_axi_s_wvalid[0]))  $fatal(1, "Problem on 'cfg_axi_s_wvalid' width");
  if ($bits(o_cfg_axi_s_wready)  != $bits(cfg_axi_s_wready[0]))  $fatal(1, "Problem on 'cfg_axi_s_wready' width");

  if ($bits(o_cfg_axi_s_bid)     != $bits(cfg_axi_s_bid[0]))     $fatal(1, "Problem on 'cfg_axi_s_bid' width");
  if ($bits(o_cfg_axi_s_bresp)   != $bits(cfg_axi_s_bresp[0]))   $fatal(1, "Problem on 'cfg_axi_s_bresp' width");
  if ($bits(o_cfg_axi_s_bvalid)  != $bits(cfg_axi_s_bvalid[0]))  $fatal(1, "Problem on 'cfg_axi_s_bvalid' width");
  if ($bits(i_cfg_axi_s_bready)  != $bits(cfg_axi_s_bready[0]))  $fatal(1, "Problem on 'cfg_axi_s_bready' width");

  if ($bits(i_cfg_axi_s_arid)    != $bits(cfg_axi_s_arid[0]))    $fatal(1, "Problem on 'cfg_axi_s_arid' width");
  // if ($bits(i_cfg_axi_s_araddr)  != $bits(cfg_axi_s_araddr[0]))  $fatal(1, "Problem on 'cfg_axi_s_araddr' width");
  if ($bits(i_cfg_axi_s_arlen)   != $bits(cfg_axi_s_arlen[0]))   $fatal(1, "Problem on 'cfg_axi_s_arlen' width");
  if ($bits(i_cfg_axi_s_arsize)  != $bits(cfg_axi_s_arsize[0]))  $fatal(1, "Problem on 'cfg_axi_s_arsize' width");
  if ($bits(i_cfg_axi_s_arburst) != $bits(cfg_axi_s_arburst[0])) $fatal(1, "Problem on 'cfg_axi_s_arburst' width");
  if ($bits(i_cfg_axi_s_arvalid) != $bits(cfg_axi_s_arvalid[0])) $fatal(1, "Problem on 'cfg_axi_s_arvalid' width");
  if ($bits(o_cfg_axi_s_arready) != $bits(cfg_axi_s_arready[0])) $fatal(1, "Problem on 'cfg_axi_s_arready' width");

  if ($bits(o_cfg_axi_s_rid)     != $bits(cfg_axi_s_rid[0]))     $fatal(1, "Problem on 'cfg_axi_s_rid' width");
  if ($bits(o_cfg_axi_s_rdata)   != $bits(cfg_axi_s_rdata[0]))   $fatal(1, "Problem on 'cfg_axi_s_rdata' width");
  if ($bits(o_cfg_axi_s_rresp)   != $bits(cfg_axi_s_rresp[0]))   $fatal(1, "Problem on 'cfg_axi_s_rresp' width");
  if ($bits(o_cfg_axi_s_rlast)   != $bits(cfg_axi_s_rlast[0]))   $fatal(1, "Problem on 'cfg_axi_s_rlast' width");
  if ($bits(o_cfg_axi_s_rvalid)  != $bits(cfg_axi_s_rvalid[0]))  $fatal(1, "Problem on 'cfg_axi_s_rvalid' width");
  if ($bits(i_cfg_axi_s_rready)  != $bits(cfg_axi_s_rready[0]))  $fatal(1, "Problem on 'cfg_axi_s_rready' width");


  /////////////
  logic [$clog2(aic_did_pkg::NUM_AXI_ENDPOINTS+1)-1:0] bus_sel_rd;
  logic [$clog2(aic_did_pkg::NUM_AXI_ENDPOINTS+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(aic_did_pkg::NUM_AXI_ENDPOINTS),
    .NR_REGIONS(aic_did_pkg::DID_NR_REGIONS),
    .REGION_ST_ADDR(aic_did_pkg::DID_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_did_pkg::DID_REGION_END_ADDR),
    .REGION_SLAVE_ID(aic_did_pkg::DID_REGION_SLAVE_ID)
  ) u_ext_decode_wr (
    .addr_in(AIC_LT_AXI_LOCAL_ADDR_WIDTH'(i_cfg_axi_s_awaddr)),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(aic_did_pkg::NUM_AXI_ENDPOINTS),
    .NR_REGIONS(aic_did_pkg::DID_NR_REGIONS),
    .REGION_ST_ADDR(aic_did_pkg::DID_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_did_pkg::DID_REGION_END_ADDR),
    .REGION_SLAVE_ID(aic_did_pkg::DID_REGION_SLAVE_ID)
  ) u_ext_decode_rd (
    .addr_in(AIC_LT_AXI_LOCAL_ADDR_WIDTH'(i_cfg_axi_s_araddr)),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  // AXI Demux
  simple_axi_demux #(
    .NR_MASTERS     (aic_did_pkg::NUM_AXI_ENDPOINTS),
    .IDW            (AIC_LT_AXI_S_ID_WIDTH),
    .AW             (AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DW             (AIC_LT_AXI_DATA_WIDTH),
    .BW             (axi_pkg::AXI_LEN_WIDTH),
    .SL_WREQ_SHIELD (2),
    .SL_RREQ_SHIELD (2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR            (8),
    .EXT_SEL(1)
  ) u_axi_demux (
    .i_clk,
    .i_rst_n,
    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),
    .s_awid   (i_cfg_axi_s_awid),
    .s_awaddr (AIC_LT_AXI_LOCAL_ADDR_WIDTH'(i_cfg_axi_s_awaddr)),
    .s_awlen  (i_cfg_axi_s_awlen),
    .s_awsize (i_cfg_axi_s_awsize),
    .s_awburst(i_cfg_axi_s_awburst),
    .s_awlock ('0), // Not supported by endpoints
    .s_awcache('0), // Not supported by endpoints
    .s_awprot ('0), // Not supported by endpoints
    .s_awvalid(i_cfg_axi_s_awvalid),
    .s_awready(o_cfg_axi_s_awready),
    .s_arid   (i_cfg_axi_s_arid),
    .s_araddr (AIC_LT_AXI_LOCAL_ADDR_WIDTH'(i_cfg_axi_s_araddr)),
    .s_arlen  (i_cfg_axi_s_arlen),
    .s_arsize (i_cfg_axi_s_arsize),
    .s_arburst(i_cfg_axi_s_arburst),
    .s_arlock ('0), // Not supported by endpoints
    .s_arcache('0), // Not supported by endpoints
    .s_arprot ('0), // Not supported by endpoints
    .s_arvalid(i_cfg_axi_s_arvalid),
    .s_arready(o_cfg_axi_s_arready),
    .s_wdata  (i_cfg_axi_s_wdata),
    .s_wstrb  (i_cfg_axi_s_wstrb),
    .s_wlast  (i_cfg_axi_s_wlast),
    .s_wvalid (i_cfg_axi_s_wvalid),
    .s_wready (o_cfg_axi_s_wready),
    .s_rid    (o_cfg_axi_s_rid),
    .s_rdata  (o_cfg_axi_s_rdata),
    .s_rresp  (o_cfg_axi_s_rresp),
    .s_rlast  (o_cfg_axi_s_rlast),
    .s_rvalid (o_cfg_axi_s_rvalid),
    .s_rready (i_cfg_axi_s_rready),
    .s_bid    (o_cfg_axi_s_bid),
    .s_bresp  (o_cfg_axi_s_bresp),
    .s_bvalid (o_cfg_axi_s_bvalid),
    .s_bready (i_cfg_axi_s_bready),
    .m_awid   (cfg_axi_s_awid),
    .m_awaddr (cfg_axi_s_awaddr),
    .m_awlen  (cfg_axi_s_awlen),
    .m_awsize (cfg_axi_s_awsize),
    .m_awburst(cfg_axi_s_awburst),
    .m_awlock (/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awcache(/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awprot (/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awvalid(cfg_axi_s_awvalid),
    .m_awready(cfg_axi_s_awready),
    .m_arid   (cfg_axi_s_arid),
    .m_araddr (cfg_axi_s_araddr),
    .m_arlen  (cfg_axi_s_arlen),
    .m_arsize (cfg_axi_s_arsize),
    .m_arburst(cfg_axi_s_arburst),
    .m_arlock (/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arcache(/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arprot (/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arvalid(cfg_axi_s_arvalid),
    .m_arready(cfg_axi_s_arready),
    .m_wdata  (cfg_axi_s_wdata),
    .m_wstrb  (cfg_axi_s_wstrb),
    .m_wlast  (cfg_axi_s_wlast),
    .m_wvalid (cfg_axi_s_wvalid),
    .m_wready (cfg_axi_s_wready),
    .m_rid    (cfg_axi_s_rid),
    .m_rdata  (cfg_axi_s_rdata),
    .m_rresp  (cfg_axi_s_rresp),
    .m_rlast  (cfg_axi_s_rlast),
    .m_rvalid (cfg_axi_s_rvalid),
    .m_rready (cfg_axi_s_rready),
    .m_bid    (cfg_axi_s_bid),
    .m_bresp  (cfg_axi_s_bresp),
    .m_bvalid (cfg_axi_s_bvalid),
    .m_bready (cfg_axi_s_bready)
  );

  //////////
  // DWPU //
  //////////
  logic [AIC_PWORD_I26_AXIS_TDATA_WIDTH-1:0] dwpu_axis_m_tdata;
  logic                                      dwpu_axis_m_tlast;
  logic                                      dwpu_axis_m_tvalid;
  logic                                      dwpu_axis_m_tready;

  dwpu #(
    .AxiIdWidth      (AIC_LT_AXI_S_ID_WIDTH),
    .AxiAddrWidth    (AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .AxiDataWidth    (AIC_LT_AXI_DATA_WIDTH),
    .AxiStrbWidth    (AIC_LT_AXI_WSTRB_WIDTH),
    .NumTokenProd    (TOK_MGR_D_DWPU_NR_TOK_PROD),
    .NumTokenCons    (TOK_MGR_D_DWPU_NR_TOK_CONS),
    .InpAxisDataWidth(AIC_PWORD_I8_AXIS_TDATA_WIDTH),
    .OupAxisDataWidth(AIC_PWORD_I26_AXIS_TDATA_WIDTH),
    .ObserveWidth    (AIC_DEV_OBS_DW),
    .CIdWidth        (AIC_CID_SUB_W),
    .BlockIdWidth    (AIC_BLOCK_ID_WIDTH),
    .sram_impl_inp_t (axe_tcl_sram_pkg::impl_inp_t),
    .sram_impl_oup_t (axe_tcl_sram_pkg::impl_oup_t),
    .REGION_ST_ADDR(aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_END_ADDR)
  ) u_dwpu (
    .i_clk,
    .i_rst_n,
    .i_test_mode     (i_sram_se),
    .i_axi_s_aw_id   (cfg_axi_s_awid[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_aw_addr (cfg_axi_s_awaddr[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_aw_len  (cfg_axi_s_awlen[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_aw_size (cfg_axi_s_awsize[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_aw_burst(cfg_axi_s_awburst[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_aw_valid(cfg_axi_s_awvalid[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_aw_ready(cfg_axi_s_awready[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_w_data  (cfg_axi_s_wdata[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_w_strb  (cfg_axi_s_wstrb[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_w_last  (cfg_axi_s_wlast[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_w_valid (cfg_axi_s_wvalid[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_w_ready (cfg_axi_s_wready[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_b_id    (cfg_axi_s_bid[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_b_resp  (cfg_axi_s_bresp[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_b_valid (cfg_axi_s_bvalid[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_b_ready (cfg_axi_s_bready[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_ar_id   (cfg_axi_s_arid[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_ar_addr (cfg_axi_s_araddr[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_ar_len  (cfg_axi_s_arlen[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_ar_size (cfg_axi_s_arsize[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_ar_burst(cfg_axi_s_arburst[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_ar_valid(cfg_axi_s_arvalid[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_ar_ready(cfg_axi_s_arready[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_r_id    (cfg_axi_s_rid[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_r_data  (cfg_axi_s_rdata[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_r_resp  (cfg_axi_s_rresp[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_r_last  (cfg_axi_s_rlast[aic_did_pkg::EndPointDwpu]),
    .o_axi_s_r_valid (cfg_axi_s_rvalid[aic_did_pkg::EndPointDwpu]),
    .i_axi_s_r_ready (cfg_axi_s_rready[aic_did_pkg::EndPointDwpu]),
    .o_tok_prod_valid(o_dwpu_tok_prod_vld),
    .i_tok_prod_ready(i_dwpu_tok_prod_rdy),
    .i_tok_cons_valid(i_dwpu_tok_cons_vld),
    .o_tok_cons_ready(o_dwpu_tok_cons_rdy),
    .i_axis_s_tdata  (i_ifd0_axis_s_tdata),
    .i_axis_s_tlast  (i_ifd0_axis_s_tlast),
    .i_axis_s_tvalid (i_ifd0_axis_s_tvalid),
    .o_axis_s_tready (o_ifd0_axis_s_tready),
    .o_axis_m_tdata  (dwpu_axis_m_tdata),
    .o_axis_m_tlast  (dwpu_axis_m_tlast),
    .o_axis_m_tvalid (dwpu_axis_m_tvalid),
    .i_axis_m_tready (dwpu_axis_m_tready),
    .o_irq           (irq[aic_did_pkg::EndPointDwpu]),
    .o_obs           (dwpu_obs),
    .o_ts_start      (ts_start[aic_did_pkg::EndPointDwpu]),
    .o_ts_end        (ts_end[aic_did_pkg::EndPointDwpu]),
    .o_acd_sync      (acd_sync[aic_did_pkg::EndPointDwpu]),
    .i_cid           (cid),
    .i_block_id            (AIC_BLOCK_ID_WIDTH'(AIC_BLOCK_ID_D_DWPU)),
    .i_dp_cmd_gen_sram_impl(sram_impl_inp_dwpu),
    .o_dp_cmd_gen_sram_impl(sram_impl_oup_dwpu)
  );

  /////////
  // IAU //
  /////////
  logic [AIC_PWORD_I26_AXIS_TDATA_WIDTH-1:0] iau_axis_s_tdata;
  logic                                      iau_axis_s_tlast;
  logic                                      iau_axis_s_tvalid;
  logic                                      iau_axis_s_tready;

  cc_stream_spill_reg #(
    .data_t(logic[AIC_PWORD_I26_AXIS_TDATA_WIDTH:0]),
    .Bypass(aic_did_pkg::DwpuIauSpillRegBypass)
  ) u_dwpu_iau_axis_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({dwpu_axis_m_tlast, dwpu_axis_m_tdata}),
    .i_valid(dwpu_axis_m_tvalid),
    .o_ready(dwpu_axis_m_tready),
    .o_data ({iau_axis_s_tlast,  iau_axis_s_tdata}),
    .o_valid(iau_axis_s_tvalid),
    .i_ready(iau_axis_s_tready)
  );

  logic [AIC_PWORD_I32_AXIS_TDATA_WIDTH-1:0] iau_axis_m_tdata;
  logic                                      iau_axis_m_tlast;
  logic                                      iau_axis_m_tvalid;
  logic                                      iau_axis_m_tready;

  iau #(
    .REGION_ST_ADDR(aic_addr_map_pkg::AIC_LOC_D_IAU_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_addr_map_pkg::AIC_LOC_D_IAU_REGION_END_ADDR)
  ) u_iau (
    .i_clk,
    .i_rst_n,
    .i_axi_s_awid      (cfg_axi_s_awid[aic_did_pkg::EndPointIau]),
    .i_axi_s_awaddr    (cfg_axi_s_awaddr[aic_did_pkg::EndPointIau]),
    .i_axi_s_awlen     (cfg_axi_s_awlen[aic_did_pkg::EndPointIau]),
    .i_axi_s_awsize    (cfg_axi_s_awsize[aic_did_pkg::EndPointIau]),
    .i_axi_s_awburst   (cfg_axi_s_awburst[aic_did_pkg::EndPointIau]),
    .i_axi_s_awvalid   (cfg_axi_s_awvalid[aic_did_pkg::EndPointIau]),
    .o_axi_s_awready   (cfg_axi_s_awready[aic_did_pkg::EndPointIau]),
    .i_axi_s_wdata     (cfg_axi_s_wdata[aic_did_pkg::EndPointIau]),
    .i_axi_s_wstrb     (cfg_axi_s_wstrb[aic_did_pkg::EndPointIau]),
    .i_axi_s_wlast     (cfg_axi_s_wlast[aic_did_pkg::EndPointIau]),
    .i_axi_s_wvalid    (cfg_axi_s_wvalid[aic_did_pkg::EndPointIau]),
    .o_axi_s_wready    (cfg_axi_s_wready[aic_did_pkg::EndPointIau]),
    .o_axi_s_bid       (cfg_axi_s_bid[aic_did_pkg::EndPointIau]),
    .o_axi_s_bresp     (cfg_axi_s_bresp[aic_did_pkg::EndPointIau]),
    .o_axi_s_bvalid    (cfg_axi_s_bvalid[aic_did_pkg::EndPointIau]),
    .i_axi_s_bready    (cfg_axi_s_bready[aic_did_pkg::EndPointIau]),
    .i_axi_s_arid      (cfg_axi_s_arid[aic_did_pkg::EndPointIau]),
    .i_axi_s_araddr    (cfg_axi_s_araddr[aic_did_pkg::EndPointIau]),
    .i_axi_s_arlen     (cfg_axi_s_arlen[aic_did_pkg::EndPointIau]),
    .i_axi_s_arsize    (cfg_axi_s_arsize[aic_did_pkg::EndPointIau]),
    .i_axi_s_arburst   (cfg_axi_s_arburst[aic_did_pkg::EndPointIau]),
    .i_axi_s_arvalid   (cfg_axi_s_arvalid[aic_did_pkg::EndPointIau]),
    .o_axi_s_arready   (cfg_axi_s_arready[aic_did_pkg::EndPointIau]),
    .o_axi_s_rid       (cfg_axi_s_rid[aic_did_pkg::EndPointIau]),
    .o_axi_s_rdata     (cfg_axi_s_rdata[aic_did_pkg::EndPointIau]),
    .o_axi_s_rresp     (cfg_axi_s_rresp[aic_did_pkg::EndPointIau]),
    .o_axi_s_rlast     (cfg_axi_s_rlast[aic_did_pkg::EndPointIau]),
    .o_axi_s_rvalid    (cfg_axi_s_rvalid[aic_did_pkg::EndPointIau]),
    .i_axi_s_rready    (cfg_axi_s_rready[aic_did_pkg::EndPointIau]),

    .o_iau_tok_prod_vld(o_iau_tok_prod_vld),
    .i_iau_tok_prod_rdy(i_iau_tok_prod_rdy),
    .i_iau_tok_cons_vld(i_iau_tok_cons_vld),
    .o_iau_tok_cons_rdy(o_iau_tok_cons_rdy),

    .i_axis_s_tdata    (iau_axis_s_tdata),
    .i_axis_s_tlast    (iau_axis_s_tlast),
    .i_axis_s_tvalid   (iau_axis_s_tvalid),
    .o_axis_s_tready   (iau_axis_s_tready),

    .o_axis_m_tdata    (iau_axis_m_tdata),
    .o_axis_m_tlast    (iau_axis_m_tlast),
    .o_axis_m_tvalid   (iau_axis_m_tvalid),
    .i_axis_m_tready   (iau_axis_m_tready),

    .o_irq             (irq[aic_did_pkg::EndPointIau]),
    .o_obs             (iau_obs),
    .o_ts_start        (ts_start[aic_did_pkg::EndPointIau]),
    .o_ts_end          (ts_end[aic_did_pkg::EndPointIau]),
    .o_acd_sync        (acd_sync[aic_did_pkg::EndPointIau]),
    .i_cid             (cid),
    .i_block_id        (AIC_BLOCK_ID_WIDTH'(AIC_BLOCK_ID_D_IAU)),
    .i_scan_en         (i_sram_se)
  );

  /////////
  // DPU //
  /////////
  logic [AIC_PWORD_I32_AXIS_TDATA_WIDTH-1:0] dpu_axis_s_tdata;
  logic                                      dpu_axis_s_tlast;
  logic                                      dpu_axis_s_tvalid;
  logic                                      dpu_axis_s_tready;

  cc_stream_fifo #(
    .Depth      (aic_did_pkg::IauDpuFifoDepth),
    .data_t     (logic[AIC_PWORD_I32_AXIS_TDATA_WIDTH:0]),
    .FallThrough(1'b0)
  ) u_iau_dpu_axis_fifo (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({iau_axis_m_tlast, iau_axis_m_tdata}),
    .i_valid(iau_axis_m_tvalid),
    .o_ready(iau_axis_m_tready),
    .o_data ({dpu_axis_s_tlast, dpu_axis_s_tdata}),
    .o_valid(dpu_axis_s_tvalid),
    .i_ready(dpu_axis_s_tready),
    .o_usage(/*open*/), // ASO-UNUSED_OUTPUT : No observability needed
    .o_full (/*open*/), // ASO-UNUSED_OUTPUT : No observability needed
    .o_empty(/*open*/)  // ASO-UNUSED_OUTPUT : No observability needed
  );

  dpu #(
    .REGION_ST_ADDR(aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_END_ADDR)
  ) u_dpu (
    .i_clk,
    .i_rst_n,
    .i_dpu_cfg_axi_s_awid   (cfg_axi_s_awid[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_awaddr (cfg_axi_s_awaddr[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_awlen  (cfg_axi_s_awlen[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_awsize (cfg_axi_s_awsize[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_awburst(cfg_axi_s_awburst[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_awvalid(cfg_axi_s_awvalid[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_awready(cfg_axi_s_awready[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_wdata  (cfg_axi_s_wdata[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_wstrb  (cfg_axi_s_wstrb[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_wlast  (cfg_axi_s_wlast[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_wvalid (cfg_axi_s_wvalid[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_wready (cfg_axi_s_wready[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_bid    (cfg_axi_s_bid[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_bresp  (cfg_axi_s_bresp[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_bvalid (cfg_axi_s_bvalid[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_bready (cfg_axi_s_bready[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_arid   (cfg_axi_s_arid[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_araddr (cfg_axi_s_araddr[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_arlen  (cfg_axi_s_arlen[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_arsize (cfg_axi_s_arsize[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_arburst(cfg_axi_s_arburst[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_arvalid(cfg_axi_s_arvalid[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_arready(cfg_axi_s_arready[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_rid    (cfg_axi_s_rid[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_rdata  (cfg_axi_s_rdata[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_rresp  (cfg_axi_s_rresp[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_rlast  (cfg_axi_s_rlast[aic_did_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_rvalid (cfg_axi_s_rvalid[aic_did_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_rready (cfg_axi_s_rready[aic_did_pkg::EndPointDpu]),
    .o_dpu_tok_prod_vld     (o_dpu_tok_prod_vld),
    .i_dpu_tok_prod_rdy     (i_dpu_tok_prod_rdy),
    .i_dpu_tok_cons_vld     (i_dpu_tok_cons_vld),
    .o_dpu_tok_cons_rdy     (o_dpu_tok_cons_rdy),
    .i_dpu_iau_axis_s_data  (dpu_axis_s_tdata),
    .i_dpu_iau_axis_s_last  (dpu_axis_s_tlast),
    .i_dpu_iau_axis_s_valid (dpu_axis_s_tvalid),
    .o_dpu_iau_axis_s_ready (dpu_axis_s_tready),
    .i_dpu_ifd1_axis_s_data (i_ifd1_axis_s_tdata),
    .i_dpu_ifd1_axis_s_last (i_ifd1_axis_s_tlast),
    .i_dpu_ifd1_axis_s_valid(i_ifd1_axis_s_tvalid),
    .o_dpu_ifd1_axis_s_ready(o_ifd1_axis_s_tready),
    .o_dpu_odr_axis_m_data  (o_odr_axis_m_tdata),
    .o_dpu_odr_axis_m_last  (o_odr_axis_m_tlast),
    .o_dpu_odr_axis_m_valid (o_odr_axis_m_tvalid),
    .i_dpu_odr_axis_m_ready (i_odr_axis_m_tready),
    .o_irq                  (irq[aic_did_pkg::EndPointDpu]),
    .o_obs                  (dpu_obs),
    .o_ts_start             (ts_start[aic_did_pkg::EndPointDpu]),
    .o_ts_end               (ts_end[aic_did_pkg::EndPointDpu]),
    .o_acd_sync             (acd_sync[aic_did_pkg::EndPointDpu]),
    .i_cid                  (cid),
    .i_block_id             (AIC_BLOCK_ID_WIDTH'(AIC_BLOCK_ID_D_DPU)),
    .i_sram_impl            (sram_impl_inp_dpu),
    .o_sram_impl            (sram_impl_oup_dpu)
  );
endmodule
