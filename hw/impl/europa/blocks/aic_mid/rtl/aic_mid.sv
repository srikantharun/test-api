// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// MVM DPU, containing MVM, IAU, DPU
///
module aic_mid
  import aic_common_pkg::*, token_mgr_mapping_aic_pkg::*, aic_mid_pkg::*;
(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Asynchronous reset, active low
  input  wire i_rst_n,
  /// Ref clock, positive edge triggered
  input  wire i_ref_clk,
  /// Ref asynchronous reset, active low
  input  wire i_ref_rst_n,
  /// Clock, positive edge triggered and non-divided
  input  wire i_c2c_clk,

  input logic i_test_mode,
  output logic o_imc_bist_fast_clk_en,

  //--------------------------------------------------
  // Obervability
  //--------------------------------------------------
  output  logic [AIC_DEV_OBS_DW-1:0] o_mvm_exe_obs,
  output  logic [AIC_DEV_OBS_DW-1:0] o_mvm_prg_obs,
  output  logic [AIC_DEV_OBS_DW-1:0] o_m_iau_obs,
  output  logic [AIC_DEV_OBS_DW-1:0] o_m_dpu_obs,
  output  logic [AIC_TU_OBS_DW-1 :0] o_tu_obs,

  // Throttle
  input   logic i_aic_throttle_async,
  input   logic i_thermal_throttle_async,
  output  logic o_mvm_throttle_async,
  output  logic o_aic_boost_req_async,
  input   logic i_aic_boost_ack_async,

  // PVT Probe
  inout  wire io_ibias_ts,
  inout  wire io_vsense_ts,

  ///// Timestamp:
  output logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] o_ts_start,
  output logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] o_ts_end,
  ///// ACD sync:
  output logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] o_acd_sync,

  //--------------------------------------------------
  // IRQ ai_core subips
  //--------------------------------------------------
  output logic [aic_mid_pkg::NUM_IRQS-1:0] o_irq,

  //--------------------------------------------------
  // Tokens ai_core subips
  //--------------------------------------------------
    // MVM EXE
  output logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] o_mvm_exe_tok_prod_vld,
  input  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] i_mvm_exe_tok_prod_rdy,
  input  logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] i_mvm_exe_tok_cons_vld,
  output logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] o_mvm_exe_tok_cons_rdy,
    // MVM PRG
  output logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] o_mvm_prg_tok_prod_vld,
  input  logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] i_mvm_prg_tok_prod_rdy,
  input  logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] i_mvm_prg_tok_cons_vld,
  output logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] o_mvm_prg_tok_cons_rdy,
    // M_IAU
  output logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] o_m_iau_tok_prod_vld,
  input  logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] i_m_iau_tok_prod_rdy,
  input  logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] i_m_iau_tok_cons_vld,
  output logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] o_m_iau_tok_cons_rdy,
    // M_DPU
  output logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] o_m_dpu_tok_prod_vld,
  input  logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] i_m_dpu_tok_prod_rdy,
  input  logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] i_m_dpu_tok_cons_vld,
  output logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] o_m_dpu_tok_cons_rdy,

  //--------------------------------------------------
  // AXI LT NOC S
  //--------------------------------------------------
  // AXI write address channel
  input  logic                                   i_cfg_s_awvalid,
  input  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_s_awaddr,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_s_awid,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_s_awlen,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_s_awsize,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_s_awburst,
  output logic                                   o_cfg_s_awready,
  // AXI write data channel
  input  logic                                   i_cfg_s_wvalid,
  input  logic                                   i_cfg_s_wlast,
  input  logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] i_cfg_s_wstrb,
  input  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_cfg_s_wdata,
  output logic                                   o_cfg_s_wready,
  // AXI write response channel
  output logic                                   o_cfg_s_bvalid,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_s_bid,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_s_bresp,
  input  logic                                   i_cfg_s_bready,
  // AXI read address channel
  input  logic                                   i_cfg_s_arvalid,
  input  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_s_araddr,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_s_arid,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_s_arlen,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_s_arsize,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_s_arburst,
  output logic                                   o_cfg_s_arready,
  // AXI read data/response channel
  output logic                                   o_cfg_s_rvalid,
  output logic                                   o_cfg_s_rlast,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_s_rid,
  output logic [      AIC_LT_AXI_DATA_WIDTH-1:0] o_cfg_s_rdata,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_s_rresp,
  input  logic                                   i_cfg_s_rready,

  //--------------------------------------------------
  // AXI-S
  //--------------------------------------------------
    // M IFDW
  input  logic                        i_m_ifdw_axis_s_tvalid,
  output logic                        o_m_ifdw_axis_s_tready,
  input  logic [AIC_PWORD_WIDTH-1:0]  i_m_ifdw_axis_s_tdata,
  input  logic                        i_m_ifdw_axis_s_tlast,
    // M IFD0
  input  logic                        i_m_ifd0_axis_s_tvalid,
  output logic                        o_m_ifd0_axis_s_tready,
  input  logic [AIC_PWORD_WIDTH-1:0]  i_m_ifd0_axis_s_tdata,
  input  logic                        i_m_ifd0_axis_s_tlast,
    // M IFD1
  input  logic                        i_m_ifd1_axis_s_tvalid,
  output logic                        o_m_ifd1_axis_s_tready,
  input  logic [AIC_PWORD_WIDTH-1:0]  i_m_ifd1_axis_s_tdata,
  input  logic                        i_m_ifd1_axis_s_tlast,
    // M IFD2
  input  logic                        i_m_ifd2_axis_s_tvalid,
  output logic                        o_m_ifd2_axis_s_tready,
  input  logic [AIC_PWORD_WIDTH-1:0]  i_m_ifd2_axis_s_tdata,
  input  logic                        i_m_ifd2_axis_s_tlast,
    // M ODR
  output logic                        o_m_odr_axis_m_tvalid,
  input  logic                        i_m_odr_axis_m_tready,
  output logic [AIC_PWORD_WIDTH-1:0]  o_m_odr_axis_m_tdata,
  output logic                        o_m_odr_axis_m_tlast,

  input logic [AIC_CID_WIDTH-1:0]     i_cid,

  // IMC BIST
  output logic o_imc_bist_busy,
  output logic o_imc_bist_done,
  output logic o_imc_bist_pass,

  //--------------------------------------------------
  //SRAM config signals
  //--------------------------------------------------
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
  output logic       o_sram_prn,

  input  wire        ijtag_tck,
  input  wire        ijtag_resetn,
  input  logic       ijtag_sel,
  input  logic       ijtag_ue,
  input  logic       ijtag_se,
  input  logic       ijtag_ce,
  input  logic       ijtag_si,
  output logic       ijtag_so
);
  // ----------------------------------------------------------
  // Signals
  // ----------------------------------------------------------
  axe_tcl_sram_pkg::impl_inp_t mem_impl_inp;
  axe_tcl_sram_pkg::impl_oup_t mem_impl_oup;

  logic [AIC_CID_SUB_W-1:0]    cid;

  // AXI write address channel
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_awvalid;
  aic_mid_pkg::axi_ext_addr_t [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_awaddr;
  aic_mid_pkg::axi_id_t       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_awid;
  axi_pkg::axi_len_t          [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_awlen;
  axi_pkg::axi_size_t         [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_awsize;
  axi_pkg::axi_burst_t        [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_awburst;
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_awready;
  // AXI write data channel
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_wvalid;
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_wlast;
  aic_mid_pkg::axi_strb_t     [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_wstrb;
  aic_mid_pkg::axi_data_t     [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_wdata;
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_wready;
  // AXI write response channel
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_bvalid;
  aic_mid_pkg::axi_id_t       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_bid;
  axi_pkg::axi_resp_t         [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_bresp;
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_bready;
  // AXI read address channel
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_arvalid;
  aic_mid_pkg::axi_ext_addr_t [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_araddr;
  aic_mid_pkg::axi_id_t       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_arid;
  axi_pkg::axi_len_t          [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_arlen;
  axi_pkg::axi_size_t         [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_arsize;
  axi_pkg::axi_burst_t        [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_arburst;
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_arready;
  // AXI read data/response channel
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_rvalid;
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_rlast;
  aic_mid_pkg::axi_id_t       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_rid;
  aic_mid_pkg::axi_data_t     [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_rdata;
  axi_pkg::axi_resp_t         [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_rresp;
  logic                       [aic_mid_pkg::NUM_AXI_ENDPOINTS-1:0] demux_rready;
  // Synced signals
  logic                       aic_throttle;
  logic                       thermal_throttle;
  logic                       aic_boost_ack;

  // AXIS
  logic                                      mvm_axis_m_tvalid;
  logic                                      mvm_axis_m_tready;
  logic [AIC_PWORD_I26_AXIS_TDATA_WIDTH-1:0] mvm_axis_m_tdata;
  logic                                      mvm_axis_m_tlast;

  logic                                      iau_axis_s_tvalid;
  logic                                      iau_axis_s_tready;
  logic [AIC_PWORD_I26_AXIS_TDATA_WIDTH-1:0] iau_axis_s_tdata;
  logic                                      iau_axis_s_tlast;

  logic                                      iau_axis_m_tvalid;
  logic                                      iau_axis_m_tready;
  logic [AIC_PWORD_I32_AXIS_TDATA_WIDTH-1:0] iau_axis_m_tdata;
  logic                                      iau_axis_m_tlast;

  logic                                      dpu_axis_s_tvalid;
  logic                                      dpu_axis_s_tready;
  logic [AIC_PWORD_I32_AXIS_TDATA_WIDTH-1:0] dpu_axis_s_tdata;
  logic                                      dpu_axis_s_tlast;

  // CSR
  imc_bist_pkg::aic_csr_hw2reg_t                      aic_mvm_bist_csr_hw2reg;
  aic_csr_mid_part_reg_pkg::aic_csr_mid_part_reg2hw_t aic_csr_reg2hw;
  aic_csr_mid_part_reg_pkg::aic_csr_mid_part_hw2reg_t aic_csr_hw2reg;
  aic_csr_mid_part_reg_pkg::axi_a_ch_h2d_t            aic_csr_axi_aw_i;
  logic                                               aic_csr_axi_awready;
  aic_csr_mid_part_reg_pkg::axi_a_ch_h2d_t            aic_csr_axi_ar_i;
  logic                                               aic_csr_axi_arready;
  aic_csr_mid_part_reg_pkg::axi_w_ch_h2d_t            aic_csr_axi_w_i;
  logic                                               aic_csr_axi_wready;
  aic_csr_mid_part_reg_pkg::axi_b_ch_d2h_t            aic_csr_axi_b_o;
  logic                                               aic_csr_axi_bready;
  aic_csr_mid_part_reg_pkg::axi_r_ch_d2h_t            aic_csr_axi_r_o;
  logic                                               aic_csr_axi_rready;

  // SVS Monitor
  logic [svs_monitor_pkg::SVS_NB_MONITOR-1:0][svs_monitor_pkg::SVS_COUNT_W-1:0] svs_core_count;
  logic                                                                         svs_core_valid;
  logic [svs_monitor_pkg::SVS_NB_MONITOR-1:0][svs_monitor_pkg::SVS_COUNT_W-1:0] svs_imc_count;
  logic                                                                         svs_imc_valid;
  // Process1 monitor
  logic [process1_monitor_pkg::PR1_NB_MONITOR-1:0][process1_monitor_pkg::PR1_COUNT_W-1:0] p1_count;
  logic                                                                                   p1_valid;
  // Process2 monitor
  logic [process2_monitor_pkg::PR2_NB_MONITOR-1:0][process2_monitor_pkg::PR2_COUNT_W-1:0] p2_count;
  logic                                                                                   p2_valid;
  // C2C
  logic                                     axis_imc_valid;
  c2c_monitor_wrapper_pkg::c2c_data_width_t axis_imc_data;
  logic                                     axis_core_valid;
  c2c_monitor_wrapper_pkg::c2c_data_width_t axis_core_data;

  // Ramp up
  mvm_ramp_up_ctrl_pkg::ramp_up_ctrl_t ramp_budget_ctrl;

  // Utilisation limit
  util_data_t util_limit;
  logic       util_limit_en;
  util_data_t avg_util;

  // NOP injection stream
  nop_inj_rate_t nop_inj_rate;
  logic          nop_inj_rate_en;

  // ----------------------------------------------------------
  // RTL
  // ----------------------------------------------------------
  axe_tcl_seq_sync #(
    .SyncStages(3)
  ) u_sync_aic_throttle (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_d(i_aic_throttle_async),
    .o_q(aic_throttle)
  );
  axe_tcl_seq_sync #(
    .SyncStages(3)
  ) u_sync_thermal_throttle (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_d(i_thermal_throttle_async),
    .o_q(thermal_throttle)
  );
  axe_tcl_seq_sync #(
    .SyncStages(3)
  ) u_sync_aic_boost_ack (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_d(i_aic_boost_ack_async),
    .o_q(aic_boost_ack)
  );

  always_comb cid = i_cid[AIC_CID_SUB_W-1:0];
  always_comb begin
    mem_impl_inp.mcs = i_sram_mcs;
    mem_impl_inp.mcsw = i_sram_mcsw;
    mem_impl_inp.ret = i_sram_ret;
    mem_impl_inp.pde = i_sram_pde;
    mem_impl_inp.se = i_sram_se;
    mem_impl_inp.adme = i_sram_adme;
    o_sram_prn = mem_impl_oup.prn;
  end

  /////////////
  logic [$clog2(aic_mid_pkg::NUM_AXI_ENDPOINTS+1)-1:0] bus_sel_rd;
  logic [$clog2(aic_mid_pkg::NUM_AXI_ENDPOINTS+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(aic_mid_pkg::NUM_AXI_ENDPOINTS),
    .NR_REGIONS(aic_mid_pkg::MID_NR_REGIONS),
    .REGION_ST_ADDR(aic_mid_pkg::MID_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_mid_pkg::MID_REGION_END_ADDR),
    .REGION_SLAVE_ID(aic_mid_pkg::MID_REGION_SLAVE_ID)
  ) u_ext_decode_wr (
    .addr_in(i_cfg_s_awaddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(aic_mid_pkg::NUM_AXI_ENDPOINTS),
    .NR_REGIONS(aic_mid_pkg::MID_NR_REGIONS),
    .REGION_ST_ADDR(aic_mid_pkg::MID_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_mid_pkg::MID_REGION_END_ADDR),
    .REGION_SLAVE_ID(aic_mid_pkg::MID_REGION_SLAVE_ID)
  ) u_ext_decode_rd (
    .addr_in(i_cfg_s_araddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  // AXI Demux
  simple_axi_demux #(
    .NR_MASTERS     (aic_mid_pkg::NUM_AXI_ENDPOINTS),
    .IDW            (AIC_LT_AXI_S_ID_WIDTH),
    .AW             (AIC_LT_AXI_ADDR_WIDTH),
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
    ///// AXI slave:
    // Write Address Channel
    .s_awid   (i_cfg_s_awid   ),
    .s_awaddr (i_cfg_s_awaddr ),
    .s_awlen  (i_cfg_s_awlen  ),
    .s_awsize (i_cfg_s_awsize ),
    .s_awburst(i_cfg_s_awburst),
    .s_awlock ( '0            ),
    .s_awprot ( '0            ),
    .s_awcache( '0            ),
    .s_awvalid(i_cfg_s_awvalid),
    .s_awready(o_cfg_s_awready),
    // Read Address Channel
    .s_arid   (i_cfg_s_arid   ),
    .s_araddr (i_cfg_s_araddr ),
    .s_arlen  (i_cfg_s_arlen  ),
    .s_arsize (i_cfg_s_arsize ),
    .s_arburst(i_cfg_s_arburst),
    .s_arlock ( '0            ),
    .s_arprot ( '0            ),
    .s_arcache( '0            ),
    .s_arvalid(i_cfg_s_arvalid),
    .s_arready(o_cfg_s_arready),
    // Write  Data Channel
    .s_wdata  (i_cfg_s_wdata  ),
    .s_wstrb  (i_cfg_s_wstrb  ),
    .s_wlast  (i_cfg_s_wlast  ),
    .s_wvalid (i_cfg_s_wvalid ),
    .s_wready (o_cfg_s_wready ),
    // Read Data Channel
    .s_rid    (o_cfg_s_rid    ),
    .s_rdata  (o_cfg_s_rdata  ),
    .s_rresp  (o_cfg_s_rresp  ),
    .s_rlast  (o_cfg_s_rlast  ),
    .s_rvalid (o_cfg_s_rvalid ),
    .s_rready (i_cfg_s_rready ),
    // Write Response Channel
    .s_bid    (o_cfg_s_bid    ),
    .s_bresp  (o_cfg_s_bresp  ),
    .s_bvalid (o_cfg_s_bvalid ),
    .s_bready (i_cfg_s_bready ),
    ///// AXI Master:
    // Write Address Channel
    .m_awid   (demux_awid     ),
    .m_awlen  (demux_awlen    ),
    .m_awaddr (demux_awaddr   ),
    .m_awsize (demux_awsize   ),
    .m_awburst(demux_awburst  ),
    .m_awlock (/*    NC     */),// ASO-UNUSED_OUTPUT: Field not used by MID
    .m_awprot (/*    NC     */),// ASO-UNUSED_OUTPUT: Field not used by MID
    .m_awcache(/*    NC     */),// ASO-UNUSED_OUTPUT: Field not used by MID
    .m_awvalid(demux_awvalid  ),
    .m_awready(demux_awready  ),
    // Read Address Chann
    .m_arid   (demux_arid     ),
    .m_arlen  (demux_arlen    ),
    .m_araddr (demux_araddr   ),
    .m_arsize (demux_arsize   ),
    .m_arburst(demux_arburst  ),
    .m_arlock (/*    NC     */),// ASO-UNUSED_OUTPUT: Field not used by MID
    .m_arprot (/*    NC     */),// ASO-UNUSED_OUTPUT: Field not used by MID
    .m_arcache(/*    NC     */),// ASO-UNUSED_OUTPUT: Field not used by MID
    .m_arvalid(demux_arvalid  ),
    .m_arready(demux_arready  ),
    // Read Resp Channel
    .m_rid    (demux_rid      ),
    .m_rdata  (demux_rdata    ),
    .m_rresp  (demux_rresp    ),
    .m_rlast  (demux_rlast    ),
    .m_rvalid (demux_rvalid   ),
    .m_rready (demux_rready   ),
    // Write  Data Channel
    .m_wdata  (demux_wdata    ),
    .m_wstrb  (demux_wstrb    ),
    .m_wlast  (demux_wlast    ),
    .m_wvalid (demux_wvalid   ),
    .m_wready (demux_wready   ),
    // Write Resp Channel
    .m_bid    (demux_bid      ),
    .m_bresp  (demux_bresp    ),
    .m_bvalid (demux_bvalid   ),
    .m_bready (demux_bready   )
  );

  always_comb ramp_budget_ctrl = '{
    budget_cost_base   : aic_csr_reg2hw.mvm_ramp_up_cfg.budget_cost_base,
    budget_cost_per_col: aic_csr_reg2hw.mvm_ramp_up_cfg.budget_cost_per_col,
    budget_cost_per_row: aic_csr_reg2hw.mvm_ramp_up_cfg.budget_cost_per_row,
    budget_cost_per_rc : aic_csr_reg2hw.mvm_ramp_up_cfg.budget_cost_per_rc,
    budget_increment   : aic_csr_reg2hw.mvm_ramp_up_cfg.budget_increment,
    budget_clip        : aic_csr_reg2hw.mvm_ramp_up_cfg.budget_clip
  };
  mvm #(
    .REGION_ST_ADDR(aic_addr_map_pkg::AIC_LOC_M_MVM_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_addr_map_pkg::AIC_LOC_M_MVM_REGION_END_ADDR),
    .util_data_t(util_data_t),
    .nop_inj_rate_t(nop_inj_rate_t)
  ) u_mvm (
    .i_clk,
    .i_rst_n,
    .i_jtag_tck                 (ijtag_tck),
    .jtag_i_rst_n               (ijtag_resetn),
    // AXI write address channel
    .i_ai_core_mvm_axi_s_awvalid(demux_awvalid[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_awaddr (aic_mid_pkg::axi_addr_t'(demux_awaddr[aic_mid_pkg::EndPointMvm])),
    .i_ai_core_mvm_axi_s_awid   (demux_awid[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_awlen  (demux_awlen[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_awsize (demux_awsize[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_awburst(demux_awburst[aic_mid_pkg::EndPointMvm]),
    .o_ai_core_mvm_axi_s_awready(demux_awready[aic_mid_pkg::EndPointMvm]),
    // AXI write data channel
    .i_ai_core_mvm_axi_s_wvalid (demux_wvalid[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_wlast  (demux_wlast[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_wstrb  (demux_wstrb[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_wdata  (demux_wdata[aic_mid_pkg::EndPointMvm]),
    .o_ai_core_mvm_axi_s_wready (demux_wready[aic_mid_pkg::EndPointMvm]),
    // AXI write response channel
    .o_ai_core_mvm_axi_s_bvalid (demux_bvalid[aic_mid_pkg::EndPointMvm]),
    .o_ai_core_mvm_axi_s_bid    (demux_bid[aic_mid_pkg::EndPointMvm]),
    .o_ai_core_mvm_axi_s_bresp  (demux_bresp[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_bready (demux_bready[aic_mid_pkg::EndPointMvm]),
    // AXI read address channel
    .i_ai_core_mvm_axi_s_arvalid(demux_arvalid[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_araddr (aic_mid_pkg::axi_addr_t'(demux_araddr[aic_mid_pkg::EndPointMvm])),
    .i_ai_core_mvm_axi_s_arid   (demux_arid[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_arlen  (demux_arlen[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_arsize (demux_arsize[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_arburst(demux_arburst[aic_mid_pkg::EndPointMvm]),
    .o_ai_core_mvm_axi_s_arready(demux_arready[aic_mid_pkg::EndPointMvm]),
    // AXI read data/response channel
    .o_ai_core_mvm_axi_s_rvalid (demux_rvalid[aic_mid_pkg::EndPointMvm]),
    .o_ai_core_mvm_axi_s_rlast  (demux_rlast[aic_mid_pkg::EndPointMvm]),
    .o_ai_core_mvm_axi_s_rid    (demux_rid[aic_mid_pkg::EndPointMvm]),
    .o_ai_core_mvm_axi_s_rdata  (demux_rdata[aic_mid_pkg::EndPointMvm]),
    .o_ai_core_mvm_axi_s_rresp  (demux_rresp[aic_mid_pkg::EndPointMvm]),
    .i_ai_core_mvm_axi_s_rready (demux_rready[aic_mid_pkg::EndPointMvm]),
    // Token EXE
    .o_ai_core_mvm_exe_tok_prod_vld(o_mvm_exe_tok_prod_vld),
    .i_ai_core_mvm_exe_tok_prod_rdy(i_mvm_exe_tok_prod_rdy),
    .i_ai_core_mvm_exe_tok_cons_vld(i_mvm_exe_tok_cons_vld),
    .o_ai_core_mvm_exe_tok_cons_rdy(o_mvm_exe_tok_cons_rdy),
    // Token PRG
    .o_ai_core_mvm_prg_tok_prod_vld(o_mvm_prg_tok_prod_vld),
    .i_ai_core_mvm_prg_tok_prod_rdy(i_mvm_prg_tok_prod_rdy),
    .i_ai_core_mvm_prg_tok_cons_vld(i_mvm_prg_tok_cons_vld),
    .o_ai_core_mvm_prg_tok_cons_rdy(o_mvm_prg_tok_cons_rdy),
    // IFD0 AXI stream
    .i_mvm_ifd0_axis_s_tvalid (i_m_ifd0_axis_s_tvalid),
    .i_mvm_ifd0_axis_s_tdata  (i_m_ifd0_axis_s_tdata),
    .i_mvm_ifd0_axis_s_tlast  (i_m_ifd0_axis_s_tlast),
    .o_mvm_ifd0_axis_s_tready (o_m_ifd0_axis_s_tready),
    // IFD2 AXI stream
    .i_mvm_ifd2_axis_s_tvalid (i_m_ifd2_axis_s_tvalid),
    .i_mvm_ifd2_axis_s_tdata  (i_m_ifd2_axis_s_tdata),
    .i_mvm_ifd2_axis_s_tlast  (i_m_ifd2_axis_s_tlast),
    .o_mvm_ifd2_axis_s_tready (o_m_ifd2_axis_s_tready),
    // IFDW AXI stream
    .i_mvm_ifdw_axis_s_tvalid (i_m_ifdw_axis_s_tvalid),
    .i_mvm_ifdw_axis_s_tdata  (i_m_ifdw_axis_s_tdata),
    .i_mvm_ifdw_axis_s_tlast  (i_m_ifdw_axis_s_tlast),
    .o_mvm_ifdw_axis_s_tready (o_m_ifdw_axis_s_tready),
    // IAU AXI stream
    .o_mvm_iau_axis_m_tvalid  (mvm_axis_m_tvalid),
    .o_mvm_iau_axis_m_tdata   (mvm_axis_m_tdata),
    .o_mvm_iau_axis_m_tlast   (mvm_axis_m_tlast),
    .i_mvm_iau_axis_m_tready  (mvm_axis_m_tready),
    // UTIL limit
    .i_mvm_util_average_nominator    (aic_csr_reg2hw.mvm_avg_util_cfg.filter_nominator),
    .i_mvm_util_col_upscaling_factor (aic_csr_reg2hw.mvm_avg_util_cfg.col_upscaling_factor),
    .i_mvm_util_row_upscaling_factor (aic_csr_reg2hw.mvm_avg_util_cfg.row_upscaling_factor),

    .i_mvm_util_limit_value    (util_limit),
    .i_mvm_util_limit_enable   (util_limit_en),
    .o_mvm_util_average        (avg_util),

    .i_mvm_nop_inj_rate_value  (nop_inj_rate),
    .i_mvm_nop_inj_rate_enable (nop_inj_rate_en),

    // IRQ
    .o_irq                 (o_irq[aic_mid_pkg::Mvm_irq]),
    // DFT signals
    .i_test_mode,
    .o_imc_bist_fast_clk_en,
    // Observation signals
    .o_ai_core_mvm_exe_obs    (o_mvm_exe_obs),
    .o_ai_core_mvm_prg_obs    (o_mvm_prg_obs),
    ///// Timestamp:
    .o_ts_start_mvm_exe(o_ts_start[aic_mid_pkg::EndPointTSMvmExe]),
    .o_ts_start_mvm_prg(o_ts_start[aic_mid_pkg::EndPointTSMvmPrg]),
    .o_ts_end_mvm_exe(o_ts_end[aic_mid_pkg::EndPointTSMvmExe]),
    .o_ts_end_mvm_prg(o_ts_end[aic_mid_pkg::EndPointTSMvmPrg]),
    ///// ACD sync:
    .o_acd_sync_mvm_exe(o_acd_sync[aic_mid_pkg::EndPointTSMvmExe]),
    .o_acd_sync_mvm_prg(o_acd_sync[aic_mid_pkg::EndPointTSMvmPrg]),
    //// Block Identification
    .i_cid                    (cid),
    .i_block_id               (AIC_BLOCK_ID_WIDTH'(AIC_BLOCK_ID_M_MVM)),
    // JTAG
    .i_jtag_sel               ('0),
    .i_jtag_se                ('0),
    .i_jtag_ce                ('0),
    .i_jtag_ue                ('0),
    .i_jtag_td                ('0),
    .o_jtag_td                (),
    // AIC CSR
    .i_aic_bist_csr_reg2hw    (imc_bist_pkg::aic_csr_reg2hw_t'{
      imc_bist_cmd: aic_csr_reg2hw.imc_bist_cmd,
      imc_bist_cfg: aic_csr_reg2hw.imc_bist_cfg,
      imc_bist_status: aic_csr_reg2hw.imc_bist_status
    }),
    .o_aic_bist_csr_hw2reg    (aic_mvm_bist_csr_hw2reg),
    // IMC BIST
    .o_imc_bist_busy,
    .o_imc_bist_done,
    .o_imc_bist_pass,
    .i_scan_en                (i_sram_se),
    // Ramp up control
    .i_ramp_budget_ctrl       (ramp_budget_ctrl)
  );

  always_comb aic_csr_hw2reg.imc_bist_status = aic_mvm_bist_csr_hw2reg.imc_bist_status;
  always_comb aic_csr_hw2reg.imc_bist_cmd = aic_mvm_bist_csr_hw2reg.imc_bist_cmd;

  cc_stream_spill_reg #(
    .data_t(logic[AIC_PWORD_I26_AXIS_TDATA_WIDTH:0]),
    .Bypass(aic_mid_pkg::MvmIauSpillRegBypass)
  ) u_mvm_iau_axis_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({mvm_axis_m_tlast, mvm_axis_m_tdata}),
    .i_valid(mvm_axis_m_tvalid),
    .o_ready(mvm_axis_m_tready),
    .o_data ({iau_axis_s_tlast,  iau_axis_s_tdata}),
    .o_valid(iau_axis_s_tvalid),
    .i_ready(iau_axis_s_tready)
  );

  iau #(
    .REGION_ST_ADDR(aic_addr_map_pkg::AIC_LOC_M_IAU_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_addr_map_pkg::AIC_LOC_M_IAU_REGION_END_ADDR)
  ) u_iau (
    .i_clk,
    .i_rst_n,
    //// AXI subordinate
    // Write Address Channel
    .i_axi_s_awid   (demux_awid[aic_mid_pkg::EndPointIau]),
    .i_axi_s_awaddr (aic_mid_pkg::axi_addr_t'(demux_awaddr[aic_mid_pkg::EndPointIau])),
    .i_axi_s_awlen  (demux_awlen[aic_mid_pkg::EndPointIau]),
    .i_axi_s_awsize (demux_awsize[aic_mid_pkg::EndPointIau]),
    .i_axi_s_awburst(demux_awburst[aic_mid_pkg::EndPointIau]),
    .i_axi_s_awvalid(demux_awvalid[aic_mid_pkg::EndPointIau]),
    .o_axi_s_awready(demux_awready[aic_mid_pkg::EndPointIau]),
    // Read Address Channel
    .i_axi_s_arid   (demux_arid[aic_mid_pkg::EndPointIau]),
    .i_axi_s_araddr (aic_mid_pkg::axi_addr_t'(demux_araddr[aic_mid_pkg::EndPointIau])),
    .i_axi_s_arlen  (demux_arlen[aic_mid_pkg::EndPointIau]),
    .i_axi_s_arsize (demux_arsize[aic_mid_pkg::EndPointIau]),
    .i_axi_s_arburst(demux_arburst[aic_mid_pkg::EndPointIau]),
    .i_axi_s_arvalid(demux_arvalid[aic_mid_pkg::EndPointIau]),
    .o_axi_s_arready(demux_arready[aic_mid_pkg::EndPointIau]),
    // Write  Data Channel
    .i_axi_s_wdata  (demux_wdata[aic_mid_pkg::EndPointIau]),
    .i_axi_s_wstrb  (demux_wstrb[aic_mid_pkg::EndPointIau]),
    .i_axi_s_wlast  (demux_wlast[aic_mid_pkg::EndPointIau]),
    .i_axi_s_wvalid (demux_wvalid[aic_mid_pkg::EndPointIau]),
    .o_axi_s_wready (demux_wready[aic_mid_pkg::EndPointIau]),
    // Read Data Channel
    .o_axi_s_rid    (demux_rid[aic_mid_pkg::EndPointIau]),
    .o_axi_s_rdata  (demux_rdata[aic_mid_pkg::EndPointIau]),
    .o_axi_s_rresp  (demux_rresp[aic_mid_pkg::EndPointIau]),
    .o_axi_s_rlast  (demux_rlast[aic_mid_pkg::EndPointIau]),
    .o_axi_s_rvalid (demux_rvalid[aic_mid_pkg::EndPointIau]),
    .i_axi_s_rready (demux_rready[aic_mid_pkg::EndPointIau]),
    // Write Response Channel
    .o_axi_s_bid    (demux_bid[aic_mid_pkg::EndPointIau]),
    .o_axi_s_bresp  (demux_bresp[aic_mid_pkg::EndPointIau]),
    .o_axi_s_bvalid (demux_bvalid[aic_mid_pkg::EndPointIau]),
    .i_axi_s_bready (demux_bready[aic_mid_pkg::EndPointIau]),
    //// Token System
    .o_iau_tok_prod_vld(o_m_iau_tok_prod_vld),
    .i_iau_tok_prod_rdy(i_m_iau_tok_prod_rdy),
    .i_iau_tok_cons_vld(i_m_iau_tok_cons_vld),
    .o_iau_tok_cons_rdy(o_m_iau_tok_cons_rdy),
    //// AXIS subordinate
    .i_axis_s_tvalid (iau_axis_s_tvalid),
    .i_axis_s_tdata  (iau_axis_s_tdata),
    .i_axis_s_tlast  (iau_axis_s_tlast),
    .o_axis_s_tready (iau_axis_s_tready),
    //// AXIS manager
    .o_axis_m_tvalid (iau_axis_m_tvalid),
    .o_axis_m_tdata  (iau_axis_m_tdata),
    .o_axis_m_tlast  (iau_axis_m_tlast),
    .i_axis_m_tready (iau_axis_m_tready),
    //// IRQ
    .o_irq           (o_irq[aic_mid_pkg::Iau_irq]),
    //// Observation
    .o_obs           (o_m_iau_obs),
    ///// Timestamp:
    .o_ts_start      (o_ts_start[aic_mid_pkg::EndPointTSIau]),
    .o_ts_end        (o_ts_end[aic_mid_pkg::EndPointTSIau]),
    ///// ACD sync:
    .o_acd_sync      (o_acd_sync[aic_mid_pkg::EndPointTSIau]),
    //// Block Identification
    .i_cid           (cid),
    .i_block_id      (AIC_BLOCK_ID_WIDTH'(AIC_BLOCK_ID_M_IAU)),
    .i_scan_en       (i_sram_se)
  );

  cc_stream_fifo #(
    .Depth      (aic_mid_pkg::IauDpuFifoDepth),
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
    .o_usage(/*     NC       */),// ASO-UNUSED_OUTPUT: Field not used by MID
    .o_full (/*     NC       */),// ASO-UNUSED_OUTPUT: Field not used by MID
    .o_empty(/*     NC       */)// ASO-UNUSED_OUTPUT: Field not used by MID
  );

  dpu #(
    .REGION_ST_ADDR(aic_addr_map_pkg::AIC_LOC_M_DPU_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_addr_map_pkg::AIC_LOC_M_DPU_REGION_END_ADDR)
  ) u_dpu (
    .i_clk,
    .i_rst_n,
    //--------------------------------------------------
    // AXI4 slave config port
    //--------------------------------------------------
    // AXI S read address channel
    .i_dpu_cfg_axi_s_araddr (aic_mid_pkg::axi_addr_t'(demux_araddr[aic_mid_pkg::EndPointDpu])),
    .i_dpu_cfg_axi_s_arburst(demux_arburst[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_arid   (demux_arid[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_arlen  (demux_arlen[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_arsize (demux_arsize[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_arvalid(demux_arvalid[aic_mid_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_arready(demux_arready[aic_mid_pkg::EndPointDpu]),
    // AXI S write address channel
    .i_dpu_cfg_axi_s_awaddr (aic_mid_pkg::axi_addr_t'(demux_awaddr[aic_mid_pkg::EndPointDpu])),
    .i_dpu_cfg_axi_s_awburst(demux_awburst[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_awid   (demux_awid[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_awlen  (demux_awlen[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_awsize (demux_awsize[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_awvalid(demux_awvalid[aic_mid_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_awready(demux_awready[aic_mid_pkg::EndPointDpu]),
    // AXI S write response channel
    .o_dpu_cfg_axi_s_bid    (demux_bid[aic_mid_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_bresp  (demux_bresp[aic_mid_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_bvalid (demux_bvalid[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_bready (demux_bready[aic_mid_pkg::EndPointDpu]),
    // AXI S read data/response channel
    .o_dpu_cfg_axi_s_rdata  (demux_rdata[aic_mid_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_rid    (demux_rid[aic_mid_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_rlast  (demux_rlast[aic_mid_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_rresp  (demux_rresp[aic_mid_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_rvalid (demux_rvalid[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_rready (demux_rready[aic_mid_pkg::EndPointDpu]),
    // AXI S write data channel
    .i_dpu_cfg_axi_s_wdata  (demux_wdata[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_wlast  (demux_wlast[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_wstrb  (demux_wstrb[aic_mid_pkg::EndPointDpu]),
    .i_dpu_cfg_axi_s_wvalid (demux_wvalid[aic_mid_pkg::EndPointDpu]),
    .o_dpu_cfg_axi_s_wready (demux_wready[aic_mid_pkg::EndPointDpu]),
    // Tokens
    .o_dpu_tok_prod_vld     (o_m_dpu_tok_prod_vld),
    .i_dpu_tok_prod_rdy     (i_m_dpu_tok_prod_rdy),
    .i_dpu_tok_cons_vld     (i_m_dpu_tok_cons_vld),
    .o_dpu_tok_cons_rdy     (o_m_dpu_tok_cons_rdy),
    // IAU AXI stream
    .i_dpu_iau_axis_s_data  (dpu_axis_s_tdata),
    .i_dpu_iau_axis_s_last  (dpu_axis_s_tlast),
    .i_dpu_iau_axis_s_valid (dpu_axis_s_tvalid),
    .o_dpu_iau_axis_s_ready (dpu_axis_s_tready),
    // IFD1 AXI stream
    .i_dpu_ifd1_axis_s_data (i_m_ifd1_axis_s_tdata),
    .i_dpu_ifd1_axis_s_last (i_m_ifd1_axis_s_tlast),
    .i_dpu_ifd1_axis_s_valid(i_m_ifd1_axis_s_tvalid),
    .o_dpu_ifd1_axis_s_ready(o_m_ifd1_axis_s_tready),
    // ODR AXI stream
    .o_dpu_odr_axis_m_data  (o_m_odr_axis_m_tdata),
    .o_dpu_odr_axis_m_last  (o_m_odr_axis_m_tlast),
    .o_dpu_odr_axis_m_valid (o_m_odr_axis_m_tvalid),
    .i_dpu_odr_axis_m_ready (i_m_odr_axis_m_tready),
    // IRQ
    .o_irq                  (o_irq[aic_mid_pkg::Dpu_irq]),
    // Observation
    .o_obs                  (o_m_dpu_obs),
    ///// Timestamp:
    .o_ts_start             (o_ts_start[aic_mid_pkg::EndPointTSDpu]),
    .o_ts_end               (o_ts_end[aic_mid_pkg::EndPointTSDpu]),
    ///// ACD sync:
    .o_acd_sync             (o_acd_sync[aic_mid_pkg::EndPointTSDpu]),
    // Block identification
    .i_cid                  (cid),
    .i_block_id             (AIC_BLOCK_ID_WIDTH'(AIC_BLOCK_ID_M_DPU)),
    // Instruction memory SRAM sideband signals
    .i_sram_impl            (mem_impl_inp),
    .o_sram_impl            (mem_impl_oup)
  );

  always_comb aic_csr_axi_aw_i.addr  = demux_awaddr[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_aw_i.id    = demux_awid[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_aw_i.len   = demux_awlen[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_aw_i.size  = demux_awsize[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_aw_i.burst = demux_awburst[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_aw_i.valid = demux_awvalid[aic_mid_pkg::EndPointCSR];
  always_comb demux_awready[aic_mid_pkg::EndPointCSR] = aic_csr_axi_awready;

  always_comb aic_csr_axi_ar_i.addr  = demux_araddr[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_ar_i.id    = demux_arid[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_ar_i.len   = demux_arlen[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_ar_i.size  = demux_arsize[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_ar_i.burst = demux_arburst[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_ar_i.valid = demux_arvalid[aic_mid_pkg::EndPointCSR];
  always_comb demux_arready[aic_mid_pkg::EndPointCSR] = aic_csr_axi_arready;

  always_comb aic_csr_axi_w_i.data  = demux_wdata[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_w_i.strb  = demux_wstrb[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_w_i.last  = demux_wlast[aic_mid_pkg::EndPointCSR];
  always_comb aic_csr_axi_w_i.valid = demux_wvalid[aic_mid_pkg::EndPointCSR];
  always_comb demux_wready[aic_mid_pkg::EndPointCSR] = aic_csr_axi_wready;

  always_comb demux_bvalid[aic_mid_pkg::EndPointCSR] = aic_csr_axi_b_o.valid;
  always_comb demux_bid[aic_mid_pkg::EndPointCSR]    = aic_csr_axi_b_o.id;
  always_comb demux_bresp[aic_mid_pkg::EndPointCSR]  = aic_csr_axi_b_o.resp;
  always_comb aic_csr_axi_bready    = demux_bready[aic_mid_pkg::EndPointCSR];

  always_comb demux_rvalid[aic_mid_pkg::EndPointCSR] = aic_csr_axi_r_o.valid;
  always_comb demux_rid[aic_mid_pkg::EndPointCSR]    = aic_csr_axi_r_o.id;
  always_comb demux_rdata[aic_mid_pkg::EndPointCSR]  = aic_csr_axi_r_o.data;
  always_comb demux_rlast[aic_mid_pkg::EndPointCSR]  = aic_csr_axi_r_o.last;
  always_comb demux_rresp[aic_mid_pkg::EndPointCSR]  = aic_csr_axi_r_o.resp;
  always_comb aic_csr_axi_rready    = demux_rready[aic_mid_pkg::EndPointCSR];

  // AIC CSR
  aic_csr_mid_part_reg_top u_aic_csr (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    // APB interface
    .axi_aw_i   (aic_csr_axi_aw_i),
    .axi_awready(aic_csr_axi_awready),
    .axi_ar_i   (aic_csr_axi_ar_i),
    .axi_arready(aic_csr_axi_arready),
    .axi_w_i    (aic_csr_axi_w_i),
    .axi_wready (aic_csr_axi_wready),
    .axi_b_o    (aic_csr_axi_b_o),
    .axi_bready (aic_csr_axi_bready),
    .axi_r_o    (aic_csr_axi_r_o),
    .axi_rready (aic_csr_axi_rready),
    // REG2HW bundle
    .reg2hw     (aic_csr_reg2hw),
    .hw2reg     (aic_csr_hw2reg),
    // Config
    .devmode_i  (1'b1)
  );

  // PVT probe:
  pvt_probe_wrapper u_pvt_probe (
    .io_ibias_ts (io_ibias_ts),
    .io_vsense_ts(io_vsense_ts)
  );

  // Process1 monitor
  always_comb foreach(aic_csr_hw2reg.p1_counters[counter])
    aic_csr_hw2reg.p1_counters[counter] = '{
      de: p1_valid,
      d:  p1_count[counter]
  };

  process1_monitor_wrapper u_p1_monitor (
    .tcki     (ijtag_tck),
    .trsti    (ijtag_resetn),
    .i_clk,
    .i_enable (aic_csr_reg2hw.p1_control.enable),
    .i_ref_clk,
    .i_target (aic_csr_reg2hw.p1_control.target),
    .i_use_ro (aic_csr_reg2hw.p1_ro_select),
    .o_valid  (p1_valid),
    .o_count  (p1_count)
  );

  // Process2 monitor
  always_comb foreach(aic_csr_hw2reg.p2_counters[counter])
    aic_csr_hw2reg.p2_counters[counter] = '{
      de: p2_valid,
      d:  p2_count[counter]
  };

  process2_monitor_wrapper u_p2_monitor (
    .tcki     (ijtag_tck),
    .trsti    (ijtag_resetn),
    .i_clk,
    .i_enable (aic_csr_reg2hw.p2_control.enable),
    .i_ref_clk,
    .i_target (aic_csr_reg2hw.p2_control.target),
    .i_use_ro (aic_csr_reg2hw.p2_ro_select),
    .o_valid  (p2_valid),
    .o_count  (p2_count)
  );

  // SVS Core Monitor
  always_comb foreach(aic_csr_hw2reg.svs_core_counters[counter])
    aic_csr_hw2reg.svs_core_counters[counter] = '{
      de: svs_core_valid,
      d:  svs_core_count[counter]
  };

  svs_monitor_wrapper u_svs_core_monitor (
    .tcki     (ijtag_tck),
    .trsti    (ijtag_resetn),
    .i_clk,
    .i_enable (aic_csr_reg2hw.svs_core_control.enable),
    .i_ref_clk,
    .i_target (aic_csr_reg2hw.svs_core_control.target),
    .i_use_ro (aic_csr_reg2hw.svs_core_ro_select),
    .o_valid  (svs_core_valid),
    .o_count  (svs_core_count)
  );

  // SVS IMC Monitor
  always_comb foreach(aic_csr_hw2reg.svs_imc_counters[counter])
    aic_csr_hw2reg.svs_imc_counters[counter] = '{
      de: svs_imc_valid,
      d:  svs_imc_count[counter]
  };

  svs_monitor_wrapper u_svs_imc_monitor (
    .tcki     (ijtag_tck),
    .trsti    (ijtag_resetn),
    .i_clk,
    .i_enable (aic_csr_reg2hw.svs_imc_control.enable),
    .i_ref_clk,
    .i_target (aic_csr_reg2hw.svs_imc_control.target),
    .i_use_ro (aic_csr_reg2hw.svs_imc_ro_select),
    .o_valid  (svs_imc_valid),
    .o_count  (svs_imc_count)
  );

  c2c_monitor_wrapper_pkg::c2c_cfg_t c2c_imc_cfg;

  always_comb c2c_imc_cfg = '{
    vote     : c2c_monitor_wrapper_pkg::c2c_vote_opt_e'(aic_csr_reg2hw.c2c_imc_control.voting_cfg),
    scale    : aic_csr_reg2hw.c2c_imc_control.scale,
    constants: aic_csr_reg2hw.c2c_imc_constants
  };

  c2c_monitor_wrapper u_c2c_imc (
    .i_pll_clk   (i_c2c_clk),
    .i_test_mode (i_sram_se),
    .i_clk,
    .i_rst_n,
    .i_enable    (aic_csr_reg2hw.c2c_imc_control.enable),
    .i_cfg       (c2c_imc_cfg),
    .o_axis_valid(axis_imc_valid),
    .o_axis_data (axis_imc_data)
  );

  always_comb aic_csr_hw2reg.c2c_imc_margin = '{
    de: axis_imc_valid,
    d : axis_imc_data
  };

  c2c_monitor_wrapper_pkg::c2c_cfg_t c2c_core_cfg;

  always_comb c2c_core_cfg = '{
    vote     : c2c_monitor_wrapper_pkg::c2c_vote_opt_e'(aic_csr_reg2hw.c2c_core_control.voting_cfg),
    scale    : aic_csr_reg2hw.c2c_core_control.scale,
    constants: aic_csr_reg2hw.c2c_core_constants
  };

  c2c_monitor_wrapper u_c2c_core (
    .i_pll_clk   (i_c2c_clk),
    .i_test_mode (i_sram_se),
    .i_clk,
    .i_rst_n,
    .i_enable    (aic_csr_reg2hw.c2c_core_control.enable),
    .i_cfg       (c2c_core_cfg),
    .o_axis_valid(axis_core_valid),
    .o_axis_data (axis_core_data)
  );

  always_comb aic_csr_hw2reg.c2c_core_margin = '{
    de: axis_core_valid,
    d : axis_core_data
  };

  c2c_monitor_wrapper_pkg::c2c_data_width_t [1:0] imc_cfg_obs_on_th;
  c2c_monitor_wrapper_pkg::c2c_data_width_t [1:0] imc_cfg_obs_off_th;
  logic                                     [1:0] imc_cfg_obs_polarity;
  logic                                     [1:0] imc_cfg_obs_enable;
  logic                                     [1:0] imc_cfg_obs_sw_force;

  always_comb imc_cfg_obs_on_th[ULTRA_FAST_IDX]    = aic_csr_reg2hw.imc_c2c_observation_cfg.ultra_fast_on_th;
  always_comb imc_cfg_obs_off_th[ULTRA_FAST_IDX]   = aic_csr_reg2hw.imc_c2c_observation_cfg.ultra_fast_off_th;
  always_comb imc_cfg_obs_polarity[ULTRA_FAST_IDX] = aic_csr_reg2hw.imc_c2c_observation_cfg.ultra_fast_polarity;
  always_comb imc_cfg_obs_enable[ULTRA_FAST_IDX]   = aic_csr_reg2hw.imc_c2c_observation_cfg.ultra_fast_enable;
  always_comb imc_cfg_obs_sw_force[ULTRA_FAST_IDX] = aic_csr_reg2hw.imc_c2c_observation_cfg.ultra_fast_sw_overwrite;

  always_comb imc_cfg_obs_on_th[FAST_IDX]    = aic_csr_reg2hw.imc_c2c_observation_cfg.fast_on_th;
  always_comb imc_cfg_obs_off_th[FAST_IDX]   = aic_csr_reg2hw.imc_c2c_observation_cfg.fast_off_th;
  always_comb imc_cfg_obs_polarity[FAST_IDX] = aic_csr_reg2hw.imc_c2c_observation_cfg.fast_polarity;
  always_comb imc_cfg_obs_enable[FAST_IDX]   = aic_csr_reg2hw.imc_c2c_observation_cfg.fast_enable;
  always_comb imc_cfg_obs_sw_force[FAST_IDX] = aic_csr_reg2hw.imc_c2c_observation_cfg.fast_sw_overwrite;

  c2c_monitor_wrapper_pkg::c2c_data_width_t [1:0] core_cfg_obs_on_th;
  c2c_monitor_wrapper_pkg::c2c_data_width_t [1:0] core_cfg_obs_off_th;
  logic                                     [1:0] core_cfg_obs_polarity;
  logic                                     [1:0] core_cfg_obs_enable;
  logic                                     [1:0] core_cfg_obs_sw_force;

  always_comb core_cfg_obs_on_th[ULTRA_FAST_IDX]    = aic_csr_reg2hw.core_c2c_observation_cfg.ultra_fast_on_th;
  always_comb core_cfg_obs_off_th[ULTRA_FAST_IDX]   = aic_csr_reg2hw.core_c2c_observation_cfg.ultra_fast_off_th;
  always_comb core_cfg_obs_polarity[ULTRA_FAST_IDX] = aic_csr_reg2hw.core_c2c_observation_cfg.ultra_fast_polarity;
  always_comb core_cfg_obs_enable[ULTRA_FAST_IDX]   = aic_csr_reg2hw.core_c2c_observation_cfg.ultra_fast_enable;
  always_comb core_cfg_obs_sw_force[ULTRA_FAST_IDX] = aic_csr_reg2hw.core_c2c_observation_cfg.ultra_fast_sw_overwrite;

  always_comb core_cfg_obs_on_th[FAST_IDX]    = aic_csr_reg2hw.core_c2c_observation_cfg.fast_on_th;
  always_comb core_cfg_obs_off_th[FAST_IDX]   = aic_csr_reg2hw.core_c2c_observation_cfg.fast_off_th;
  always_comb core_cfg_obs_polarity[FAST_IDX] = aic_csr_reg2hw.core_c2c_observation_cfg.fast_polarity;
  always_comb core_cfg_obs_enable[FAST_IDX]   = aic_csr_reg2hw.core_c2c_observation_cfg.fast_enable;
  always_comb core_cfg_obs_sw_force[FAST_IDX] = aic_csr_reg2hw.core_c2c_observation_cfg.fast_sw_overwrite;

  logic [1:0][1:0] obs_throttle_cfg;

  always_comb obs_throttle_cfg[FAST_IDX][CORE_IDX] = aic_csr_reg2hw.obs_throttle_cfg.core_fast_enable;
  always_comb obs_throttle_cfg[ULTRA_FAST_IDX][CORE_IDX] = aic_csr_reg2hw.obs_throttle_cfg.core_ultra_fast_enable;
  always_comb obs_throttle_cfg[FAST_IDX][IMC_IDX] = aic_csr_reg2hw.obs_throttle_cfg.imc_fast_enable;
  always_comb obs_throttle_cfg[ULTRA_FAST_IDX][IMC_IDX] = aic_csr_reg2hw.obs_throttle_cfg.imc_ultra_fast_enable;

  inj_nop_rate_cfg_t nop_inj_tu_cfg;

  always_comb nop_inj_tu_cfg = '{
    static_settings    : aic_csr_reg2hw.nop_injection_rate_cfg,
    throttle_value     : aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_ULTRA_FAST_IDX].throttle_limit << NOP_INJ_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_FAST_IDX].throttle_limit << NOP_INJ_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_AIC_IDX].throttle_limit << NOP_INJ_AIC_IDX,
    throttle_mode      : aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_ULTRA_FAST_IDX].mode << NOP_INJ_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_FAST_IDX].mode << NOP_INJ_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_AIC_IDX].mode << NOP_INJ_AIC_IDX,
    throttle_en        : aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_ULTRA_FAST_IDX].throttle_en << NOP_INJ_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_FAST_IDX].throttle_en << NOP_INJ_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_AIC_IDX].throttle_en << NOP_INJ_AIC_IDX,
    sw_overwrite       : aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_ULTRA_FAST_IDX].sw_throttle_en << NOP_INJ_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_FAST_IDX].sw_throttle_en << NOP_INJ_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_AIC_IDX].sw_throttle_en << NOP_INJ_AIC_IDX,
    throttle_incr_time : aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_ULTRA_FAST_IDX].soft_throttle_incr_time << NOP_INJ_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_FAST_IDX].soft_throttle_incr_time << NOP_INJ_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_AIC_IDX].soft_throttle_incr_time << NOP_INJ_AIC_IDX,
    throttle_decr_time : aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_ULTRA_FAST_IDX].soft_throttle_decr_time << NOP_INJ_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_FAST_IDX].soft_throttle_decr_time << NOP_INJ_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_AIC_IDX].soft_throttle_decr_time << NOP_INJ_AIC_IDX,
    throttle_prescale  : aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_ULTRA_FAST_IDX].soft_throttle_prescale << NOP_INJ_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_FAST_IDX].soft_throttle_prescale << NOP_INJ_FAST_IDX
                       | aic_csr_reg2hw.nop_injection_throttle_cfg[NOP_INJ_AIC_IDX].soft_throttle_prescale << NOP_INJ_AIC_IDX
  };

  util_cfg_t util_tu_cfg;

  always_comb util_tu_cfg = '{
    throttle_value     : aic_csr_reg2hw.util_throttle_cfg[UTIL_ULTRA_FAST_IDX].throttle_limit << UTIL_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_FAST_IDX].throttle_limit << UTIL_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_AIC_IDX].throttle_limit << UTIL_AIC_IDX,
    throttle_mode      : aic_csr_reg2hw.util_throttle_cfg[UTIL_ULTRA_FAST_IDX].mode << UTIL_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_FAST_IDX].mode << UTIL_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_AIC_IDX].mode << UTIL_AIC_IDX,
    throttle_en        : aic_csr_reg2hw.util_throttle_cfg[UTIL_ULTRA_FAST_IDX].throttle_en << UTIL_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_FAST_IDX].throttle_en << UTIL_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_AIC_IDX].throttle_en << UTIL_AIC_IDX,
    sw_overwrite       : aic_csr_reg2hw.util_throttle_cfg[UTIL_ULTRA_FAST_IDX].sw_throttle_en << UTIL_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_FAST_IDX].sw_throttle_en << UTIL_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_AIC_IDX].sw_throttle_en << UTIL_AIC_IDX,
    throttle_incr_time : aic_csr_reg2hw.util_throttle_cfg[UTIL_ULTRA_FAST_IDX].soft_throttle_incr_time << UTIL_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_FAST_IDX].soft_throttle_incr_time << UTIL_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_AIC_IDX].soft_throttle_incr_time << UTIL_AIC_IDX,
    throttle_decr_time : aic_csr_reg2hw.util_throttle_cfg[UTIL_ULTRA_FAST_IDX].soft_throttle_decr_time << UTIL_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_FAST_IDX].soft_throttle_decr_time << UTIL_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_AIC_IDX].soft_throttle_decr_time << UTIL_AIC_IDX,
    throttle_prescale  : aic_csr_reg2hw.util_throttle_cfg[UTIL_ULTRA_FAST_IDX].soft_throttle_prescale << UTIL_ULTRA_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_FAST_IDX].soft_throttle_prescale << UTIL_FAST_IDX
                       | aic_csr_reg2hw.util_throttle_cfg[UTIL_AIC_IDX].soft_throttle_prescale << UTIL_AIC_IDX
  };

  logic [1:0][1:0] irq_warning_cfg;
  logic warning_irq;

  always_comb irq_warning_cfg[ULTRA_FAST_IDX][IMC_IDX]  = aic_csr_reg2hw.irq_throttle_cfg.warning_imc_c2c_ultra_fast;
  always_comb irq_warning_cfg[ULTRA_FAST_IDX][CORE_IDX] = aic_csr_reg2hw.irq_throttle_cfg.warning_core_c2c_ultra_fast;
  always_comb irq_warning_cfg[FAST_IDX][IMC_IDX]        = aic_csr_reg2hw.irq_throttle_cfg.warning_imc_c2c_fast;
  always_comb irq_warning_cfg[FAST_IDX][CORE_IDX]       = aic_csr_reg2hw.irq_throttle_cfg.warning_core_c2c_fast;

  logic [1:0][1:0] irq_critical_cfg;
  logic critical_irq;

  always_comb irq_critical_cfg[ULTRA_FAST_IDX][IMC_IDX]  = aic_csr_reg2hw.irq_throttle_cfg.critical_imc_c2c_ultra_fast;
  always_comb irq_critical_cfg[ULTRA_FAST_IDX][CORE_IDX] = aic_csr_reg2hw.irq_throttle_cfg.critical_core_c2c_ultra_fast;
  always_comb irq_critical_cfg[FAST_IDX][IMC_IDX]        = aic_csr_reg2hw.irq_throttle_cfg.critical_imc_c2c_fast;
  always_comb irq_critical_cfg[FAST_IDX][CORE_IDX]       = aic_csr_reg2hw.irq_throttle_cfg.critical_core_c2c_fast;

  logic [3:0] cfg_disengage_boost;

  always_comb cfg_disengage_boost[THROTTLE_DISENGAGE_AIC_IDX]        = aic_csr_reg2hw.boost_requester_cfg.aic_disengage;
  always_comb cfg_disengage_boost[THROTTLE_DISENGAGE_THERMAL_IDX]    = aic_csr_reg2hw.boost_requester_cfg.thermal_disengage;
  always_comb cfg_disengage_boost[THROTTLE_DISENGAGE_FAST_IDX]       = aic_csr_reg2hw.boost_requester_cfg.fast_disengage;
  always_comb cfg_disengage_boost[THROTTLE_DISENGAGE_ULTRA_FAST_IDX] = aic_csr_reg2hw.boost_requester_cfg.ultra_fast_disengage;

  logic [1:0][1:0] obs_cfg_error;
  logic boost_cfg_error;

  aic_mid_throttle_unit #(
      .c2c_data_t (c2c_monitor_wrapper_pkg::c2c_data_width_t)
    ) u_throttle_unit (
      .i_clk,
      .i_rst_n,

      .i_axis_c2c_imc_valid    (axis_imc_valid),
      .i_axis_c2c_imc_data     (axis_imc_data),

      .i_imc_cfg_obs_on_th     (imc_cfg_obs_on_th),
      .i_imc_cfg_obs_off_th    (imc_cfg_obs_off_th),
      .i_imc_cfg_obs_polarity  (imc_cfg_obs_polarity),
      .i_imc_cfg_obs_enable    (imc_cfg_obs_enable),
      .i_imc_cfg_obs_sw_force  (imc_cfg_obs_sw_force),
      .i_imc_cfg_obs_clean_max (aic_csr_reg2hw.monitor_min_max_value.max_imc_c2c_margin.re),
      .i_imc_cfg_obs_clean_min (aic_csr_reg2hw.monitor_min_max_value.min_imc_c2c_margin.re),
      .o_imc_cfg_obs_max_value (aic_csr_hw2reg.monitor_min_max_value.max_imc_c2c_margin),
      .o_imc_cfg_obs_min_value (aic_csr_hw2reg.monitor_min_max_value.min_imc_c2c_margin),

      .i_axis_c2c_core_valid   (axis_core_valid),
      .i_axis_c2c_core_data    (axis_core_data),

      .i_core_cfg_obs_on_th    (core_cfg_obs_on_th),
      .i_core_cfg_obs_off_th   (core_cfg_obs_off_th),
      .i_core_cfg_obs_polarity (core_cfg_obs_polarity),
      .i_core_cfg_obs_enable   (core_cfg_obs_enable),
      .i_core_cfg_obs_sw_force (core_cfg_obs_sw_force),
      .i_core_cfg_obs_clean_max(aic_csr_reg2hw.monitor_min_max_value.max_core_c2c_margin.re),
      .i_core_cfg_obs_clean_min(aic_csr_reg2hw.monitor_min_max_value.min_core_c2c_margin.re),
      .o_core_cfg_obs_max_value(aic_csr_hw2reg.monitor_min_max_value.max_core_c2c_margin),
      .o_core_cfg_obs_min_value(aic_csr_hw2reg.monitor_min_max_value.min_core_c2c_margin),

      .o_error                 (obs_cfg_error),
      .i_obs_throttle_cfg      (obs_throttle_cfg),

      .i_thermal_throttle      (thermal_throttle),
      .i_aic_throttle          (aic_throttle),
      .o_mvm_throttle          (o_mvm_throttle_async),

      .i_nop_inj_tu_cfg        (nop_inj_tu_cfg),
      .o_nop_inj_rate          (nop_inj_rate),
      .o_nop_inj_valid         (nop_inj_rate_en),

      .i_util_tu_cfg           (util_tu_cfg),
      .o_util_limit            (util_limit),
      .o_util_limit_en         (util_limit_en),
      .i_avg_util              (avg_util),

      .o_util_min              (aic_csr_hw2reg.monitor_min_max_value.min_avg_util),
      .o_util_max              (aic_csr_hw2reg.monitor_min_max_value.max_avg_util),
      .i_clean_util_min        (aic_csr_reg2hw.monitor_min_max_value.min_avg_util.re),
      .i_clean_util_max        (aic_csr_reg2hw.monitor_min_max_value.max_avg_util.re),

      .i_enable_boost_req      (aic_csr_reg2hw.boost_requester_cfg.enable),
      .i_req_boost_on_th       (aic_csr_reg2hw.boost_requester_cfg.on_th),
      .i_req_boost_off_th      (aic_csr_reg2hw.boost_requester_cfg.off_th),
      .i_boost_ack             (aic_boost_ack),
      .i_normal_util_limit     (aic_csr_reg2hw.boost_requester_cfg.normal_max_util),
      .i_boost_util_limit      (aic_csr_reg2hw.boost_requester_cfg.boost_max_util),
      .o_polarity_err_cfg      (boost_cfg_error),
      .o_boost_req             (o_aic_boost_req_async),

      .i_cfg_disengage_boost   (cfg_disengage_boost),

      .i_irq_warning_cfg       (irq_warning_cfg),
      .i_irq_critical_cfg      (irq_critical_cfg),
      .o_warning_irq           (warning_irq),
      .o_critical_irq          (critical_irq)
    );

  tu_obs_union_t tu_obs;

  always_comb tu_obs.as_struct = '{
    sampled_avg_util:  avg_util,
    util_limit:        util_limit,
    util_limit_en:     util_limit_en
  };

  always_comb o_tu_obs = '0; // TODO: The OBS interface requires updates - meeting scheduled with Arch team to close this

  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.boost_req_error.d           = 1'b1;
  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.imc_ultra_fast_obs_error.d  = 1'b1;
  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.imc_fast_obs_error.d        = 1'b1;
  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.core_ultra_fast_obs_error.d = 1'b1;
  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.core_fast_obs_error.d       = 1'b1;

  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.boost_req_error.de           = boost_cfg_error;
  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.imc_ultra_fast_obs_error.de  = obs_cfg_error[IMC_IDX][ULTRA_FAST_IDX];
  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.imc_fast_obs_error.de        = obs_cfg_error[IMC_IDX][FAST_IDX];
  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.core_ultra_fast_obs_error.de = obs_cfg_error[CORE_IDX][ULTRA_FAST_IDX];
  always_comb aic_csr_hw2reg.throttle_cfg_error_irq_status.core_fast_obs_error.de       = obs_cfg_error[CORE_IDX][FAST_IDX];

  always_comb o_irq[aic_mid_pkg::MID_irq] = |(aic_csr_reg2hw.throttle_cfg_error_irq_enable & aic_csr_hw2reg.throttle_cfg_error_irq_status);

  always_comb o_irq[aic_mid_pkg::TU_warning_irq]  = warning_irq;
  always_comb o_irq[aic_mid_pkg::TU_critical_irq] = critical_irq;

endmodule
