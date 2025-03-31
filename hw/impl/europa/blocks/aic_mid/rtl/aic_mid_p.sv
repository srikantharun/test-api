// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// Partition of aic_mid
///
module aic_mid_p
  import aic_common_pkg::*, token_mgr_mapping_aic_pkg::*;
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
  input   logic i_aic_boost_ack_async,
  output  logic o_aic_boost_req_async,

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
    /// Margin adjustment for access disturbance margin enhancement (Vmin Feature Control Pins)
  input  logic [2:0] i_sram_adme,
    /// Power up ready negative
  output logic       o_sram_prn,

  //--------------------------------------------------
  // DFT
  //--------------------------------------------------
  input  wire         ijtag_tck,
  input  wire         ijtag_reset,
  input  logic        ijtag_sel,
  input  logic        ijtag_ue,
  input  logic        ijtag_se,
  input  logic        ijtag_ce,
  input  logic        ijtag_si,
  output logic        ijtag_so,

  input  wire         bisr_clk,
  input  wire         bisr_reset,
  input  logic        bisr_shift_en,
  input  logic        bisr_si,
  output logic        bisr_so,

  // IMC repair chain (aic_mid specific)
  input  wire         imc_bisr_clk,
  input  wire         imc_bisr_reset,
  input  logic        imc_bisr_shift_en,
  input  logic        imc_bisr_si,
  output logic        imc_bisr_so,

  input  wire         test_clk,
  input  logic        test_mode,
  input  logic        edt_update,
  input  logic        scan_en,
  input  logic [11:0] scan_in,
  output logic [11:0] scan_out

);
  //--------------------------------------------------
  // AXI-S
  //--------------------------------------------------
  // IFDW
  logic                        ifdw_axis_s_tvalid;
  logic                        ifdw_axis_s_tready;
  logic [AIC_PWORD_WIDTH-1:0]  ifdw_axis_s_tdata;
  logic                        ifdw_axis_s_tlast;
  // IFD0
  logic                        ifd0_axis_s_tvalid;
  logic                        ifd0_axis_s_tready;
  logic [AIC_PWORD_WIDTH-1:0]  ifd0_axis_s_tdata;
  logic                        ifd0_axis_s_tlast;
  // IFD1
  logic                        ifd1_axis_s_tvalid;
  logic                        ifd1_axis_s_tready;
  logic [AIC_PWORD_WIDTH-1:0]  ifd1_axis_s_tdata;
  logic                        ifd1_axis_s_tlast;
  // M IFD2
  logic                        ifd2_axis_s_tvalid;
  logic                        ifd2_axis_s_tready;
  logic [AIC_PWORD_WIDTH-1:0]  ifd2_axis_s_tdata;
  logic                        ifd2_axis_s_tlast;
  // M ODR
  logic                        odr_axis_m_tvalid;
  logic                        odr_axis_m_tready;
  logic [AIC_PWORD_WIDTH-1:0]  odr_axis_m_tdata;
  logic                        odr_axis_m_tlast;
  //--------------------------------------------------
  // Sideband
  //--------------------------------------------------
  logic s_imc_bist_busy;
  logic s_imc_bist_done;
  logic s_imc_bist_pass;
  logic [aic_mid_pkg::NUM_IRQS-1:0] s_irq;
  logic [AIC_TU_OBS_DW-1 :0] s_tu_obs;

  cc_stream_spill_reg #(
    .data_t(logic[AIC_PWORD_WIDTH:0]),
    .Bypass(1'b0)
  ) u_ifdw_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({i_m_ifdw_axis_s_tlast, i_m_ifdw_axis_s_tdata}),
    .i_valid(i_m_ifdw_axis_s_tvalid),
    .o_ready(o_m_ifdw_axis_s_tready),
    .o_data ({ifdw_axis_s_tlast,  ifdw_axis_s_tdata}),
    .o_valid(ifdw_axis_s_tvalid),
    .i_ready(ifdw_axis_s_tready)
  );

  cc_stream_spill_reg #(
    .data_t(logic[AIC_PWORD_WIDTH:0]),
    .Bypass(1'b0),
    .CutFirst(1'b1)
  ) u_ifd0_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({i_m_ifd0_axis_s_tlast, i_m_ifd0_axis_s_tdata}),
    .i_valid(i_m_ifd0_axis_s_tvalid),
    .o_ready(o_m_ifd0_axis_s_tready),
    .o_data ({ifd0_axis_s_tlast,  ifd0_axis_s_tdata}),
    .o_valid(ifd0_axis_s_tvalid),
    .i_ready(ifd0_axis_s_tready)
  );

  cc_stream_spill_reg #(
    .data_t(logic[AIC_PWORD_WIDTH:0]),
    .Bypass(1'b0),
    .CutFirst(1'b1)
  ) u_ifd1_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({i_m_ifd1_axis_s_tlast, i_m_ifd1_axis_s_tdata}),
    .i_valid(i_m_ifd1_axis_s_tvalid),
    .o_ready(o_m_ifd1_axis_s_tready),
    .o_data ({ifd1_axis_s_tlast,  ifd1_axis_s_tdata}),
    .o_valid(ifd1_axis_s_tvalid),
    .i_ready(ifd1_axis_s_tready)
  );

  cc_stream_spill_reg #(
    .data_t(logic[AIC_PWORD_WIDTH:0]),
    .Bypass(1'b0)
  ) u_ifd2_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({i_m_ifd2_axis_s_tlast, i_m_ifd2_axis_s_tdata}),
    .i_valid(i_m_ifd2_axis_s_tvalid),
    .o_ready(o_m_ifd2_axis_s_tready),
    .o_data ({ifd2_axis_s_tlast,  ifd2_axis_s_tdata}),
    .o_valid(ifd2_axis_s_tvalid),
    .i_ready(ifd2_axis_s_tready)
  );

  cc_stream_spill_reg #(
    .data_t(logic[AIC_PWORD_WIDTH:0]),
    .Bypass(1'b0)
  ) u_odr_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({odr_axis_m_tlast,  odr_axis_m_tdata}),
    .i_valid(odr_axis_m_tvalid),
    .o_ready(odr_axis_m_tready),
    .o_data ({o_m_odr_axis_m_tlast, o_m_odr_axis_m_tdata}),
    .o_valid(o_m_odr_axis_m_tvalid),
    .i_ready(i_m_odr_axis_m_tready)
  );

  // ----------------------------------------------------------
  // MVM IAU DPU
  // ----------------------------------------------------------
  aic_mid u_aic_mid (
    .i_clk,
    .i_rst_n,
    .i_ref_clk,
    .i_ref_rst_n,
    .i_c2c_clk,

    .i_test_mode(test_mode),
    .o_imc_bist_fast_clk_en,

    .o_mvm_exe_obs,
    .o_mvm_prg_obs,
    .o_m_iau_obs,
    .o_m_dpu_obs,
    .o_tu_obs(s_tu_obs),

    .i_aic_throttle_async,
    .i_thermal_throttle_async,
    .o_mvm_throttle_async,
    .o_aic_boost_req_async,
    .i_aic_boost_ack_async,

    .io_ibias_ts,
    .io_vsense_ts,

    .o_ts_start,
    .o_ts_end,
    .o_acd_sync,

    .o_irq(s_irq),

    .o_mvm_exe_tok_prod_vld,
    .i_mvm_exe_tok_prod_rdy,
    .i_mvm_exe_tok_cons_vld,
    .o_mvm_exe_tok_cons_rdy,

    .o_mvm_prg_tok_prod_vld,
    .i_mvm_prg_tok_prod_rdy,
    .i_mvm_prg_tok_cons_vld,
    .o_mvm_prg_tok_cons_rdy,

    .o_m_iau_tok_prod_vld,
    .i_m_iau_tok_prod_rdy,
    .i_m_iau_tok_cons_vld,
    .o_m_iau_tok_cons_rdy,

    .o_m_dpu_tok_prod_vld,
    .i_m_dpu_tok_prod_rdy,
    .i_m_dpu_tok_cons_vld,
    .o_m_dpu_tok_cons_rdy,

    .i_cfg_s_awvalid,
    .i_cfg_s_awaddr,
    .i_cfg_s_awid,
    .i_cfg_s_awlen,
    .i_cfg_s_awsize,
    .i_cfg_s_awburst,
    .o_cfg_s_awready,

    .i_cfg_s_wvalid,
    .i_cfg_s_wlast,
    .i_cfg_s_wstrb,
    .i_cfg_s_wdata,
    .o_cfg_s_wready,

    .o_cfg_s_bvalid,
    .o_cfg_s_bid,
    .o_cfg_s_bresp,
    .i_cfg_s_bready,

    .i_cfg_s_arvalid,
    .i_cfg_s_araddr,
    .i_cfg_s_arid,
    .i_cfg_s_arlen,
    .i_cfg_s_arsize,
    .i_cfg_s_arburst,
    .o_cfg_s_arready,

    .o_cfg_s_rvalid,
    .o_cfg_s_rlast,
    .o_cfg_s_rid,
    .o_cfg_s_rdata,
    .o_cfg_s_rresp,
    .i_cfg_s_rready,

    .i_m_ifdw_axis_s_tvalid (ifdw_axis_s_tvalid),
    .o_m_ifdw_axis_s_tready (ifdw_axis_s_tready),
    .i_m_ifdw_axis_s_tdata  (ifdw_axis_s_tdata),
    .i_m_ifdw_axis_s_tlast  (ifdw_axis_s_tlast),

    .i_m_ifd0_axis_s_tvalid (ifd0_axis_s_tvalid),
    .o_m_ifd0_axis_s_tready (ifd0_axis_s_tready),
    .i_m_ifd0_axis_s_tdata  (ifd0_axis_s_tdata),
    .i_m_ifd0_axis_s_tlast  (ifd0_axis_s_tlast),

    .i_m_ifd1_axis_s_tvalid (ifd1_axis_s_tvalid),
    .o_m_ifd1_axis_s_tready (ifd1_axis_s_tready),
    .i_m_ifd1_axis_s_tdata  (ifd1_axis_s_tdata),
    .i_m_ifd1_axis_s_tlast  (ifd1_axis_s_tlast),

    .i_m_ifd2_axis_s_tvalid (ifd2_axis_s_tvalid),
    .o_m_ifd2_axis_s_tready (ifd2_axis_s_tready),
    .i_m_ifd2_axis_s_tdata  (ifd2_axis_s_tdata),
    .i_m_ifd2_axis_s_tlast  (ifd2_axis_s_tlast),

    .o_m_odr_axis_m_tvalid  (odr_axis_m_tvalid),
    .i_m_odr_axis_m_tready  (odr_axis_m_tready),
    .o_m_odr_axis_m_tdata   (odr_axis_m_tdata),
    .o_m_odr_axis_m_tlast   (odr_axis_m_tlast),

    .i_cid,

    .o_imc_bist_busy(s_imc_bist_busy),
    .o_imc_bist_done(s_imc_bist_done),
    .o_imc_bist_pass(s_imc_bist_pass),

    .i_sram_mcs,
    .i_sram_mcsw,
    .i_sram_ret,
    .i_sram_pde,
    .i_sram_se(scan_en),
    .i_sram_adme,
    .o_sram_prn,

    .ijtag_tck,
    .ijtag_resetn(ijtag_reset),
    .ijtag_sel('0),
    .ijtag_ue('0),
    .ijtag_se('0),
    .ijtag_ce('0),
    .ijtag_si('0),
    .ijtag_so()
  );

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n) begin
      o_imc_bist_busy <= '0;
      o_imc_bist_done <= '0;
      o_imc_bist_pass <= '0;
      o_irq           <= '0;
      o_tu_obs        <= '0;
    end else begin
      if(o_imc_bist_busy ^ s_imc_bist_busy) o_imc_bist_busy <= s_imc_bist_busy;
      if(o_imc_bist_done ^ s_imc_bist_done) o_imc_bist_done <= s_imc_bist_done;
      if(o_imc_bist_pass ^ s_imc_bist_pass) o_imc_bist_pass <= s_imc_bist_pass;
      if(o_irq ^ s_irq) o_irq <= s_irq;
      if(o_tu_obs ^ s_tu_obs) o_tu_obs <= s_tu_obs;
    end

endmodule
