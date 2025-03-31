// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>

/// Description: DMC L1 impl combines DMC and L1 into one impl
/// to be decided if it will also contain a seperate axi cfg input/output for MVM feedthrough

module aic_ls
  import aic_common_pkg::*, dmc_pkg::*, token_mgr_mapping_aic_pkg::*, aic_ls_pkg::*;
(
  input  wire i_clk,
  input  wire i_rst_n,

  input  logic i_scan_en,

  output logic [DMC_IRQ_W-1:0] o_dmc_irq,

  // axi streams:
    // IFD:
    // M IFD0
  output logic                        o_m_ifd0_axis_m_tvalid,
  input  logic                        i_m_ifd0_axis_m_tready,
  output logic [AIC_PWORD_WIDTH-1:0]  o_m_ifd0_axis_m_tdata,
  output logic                        o_m_ifd0_axis_m_tlast,
    // M IFD1
  output logic                        o_m_ifd1_axis_m_tvalid,
  input  logic                        i_m_ifd1_axis_m_tready,
  output logic [AIC_PWORD_WIDTH-1:0]  o_m_ifd1_axis_m_tdata,
  output logic                        o_m_ifd1_axis_m_tlast,
    // M IFD2
  output logic                        o_m_ifd2_axis_m_tvalid,
  input  logic                        i_m_ifd2_axis_m_tready,
  output logic [AIC_PWORD_WIDTH-1:0]  o_m_ifd2_axis_m_tdata,
  output logic                        o_m_ifd2_axis_m_tlast,
    // M IFDW
  output logic                        o_m_ifdw_axis_m_tvalid,
  input  logic                        i_m_ifdw_axis_m_tready,
  output logic [AIC_PWORD_WIDTH-1:0]  o_m_ifdw_axis_m_tdata,
  output logic                        o_m_ifdw_axis_m_tlast,
    // D IFD0
  output logic                        o_d_ifd0_axis_m_tvalid,
  input  logic                        i_d_ifd0_axis_m_tready,
  output logic [AIC_PWORD_WIDTH-1:0]  o_d_ifd0_axis_m_tdata,
  output logic                        o_d_ifd0_axis_m_tlast,
    // D IFD1
  output logic                        o_d_ifd1_axis_m_tvalid,
  input  logic                        i_d_ifd1_axis_m_tready,
  output logic [AIC_PWORD_WIDTH-1:0]  o_d_ifd1_axis_m_tdata,
  output logic                        o_d_ifd1_axis_m_tlast,
    // ODR:
    // M ODR
  input  logic                        i_m_odr_axis_s_tvalid,
  output logic                        o_m_odr_axis_s_tready,
  input  logic [AIC_PWORD_WIDTH-1:0]  i_m_odr_axis_s_tdata,
  input  logic                        i_m_odr_axis_s_tlast,
    // D ODR:
  input  logic                        i_d_odr_axis_s_tvalid,
  output logic                        o_d_odr_axis_s_tready,
  input  logic [AIC_PWORD_WIDTH-1:0]  i_d_odr_axis_s_tdata,
  input  logic                        i_d_odr_axis_s_tlast,

  // RVV input
    // 0
  input  logic                                           i_rvv_0_req_valid,
  output logic                                           o_rvv_0_req_ready,
  input  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_0_req_addr,
  input  logic                                           i_rvv_0_req_we,
  input  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_0_req_be,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_0_req_wdata,
  output logic                                           o_rvv_0_res_valid,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_0_res_rdata,
  output logic                                           o_rvv_0_res_err,
    // 0
  input  logic                                           i_rvv_1_req_valid,
  output logic                                           o_rvv_1_req_ready,
  input  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_1_req_addr,
  input  logic                                           i_rvv_1_req_we,
  input  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_1_req_be,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_1_req_wdata,
  output logic                                           o_rvv_1_res_valid,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_1_res_rdata,
  output logic                                           o_rvv_1_res_err,
    // 2
  input  logic                                           i_rvv_2_req_valid,
  output logic                                           o_rvv_2_req_ready,
  input  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_2_req_addr,
  input  logic                                           i_rvv_2_req_we,
  input  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_2_req_be,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_2_req_wdata,
  output logic                                           o_rvv_2_res_valid,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_2_res_rdata,
  output logic                                           o_rvv_2_res_err,
    // 3
  input  logic                                           i_rvv_3_req_valid,
  output logic                                           o_rvv_3_req_ready,
  input  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_3_req_addr,
  input  logic                                           i_rvv_3_req_we,
  input  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_3_req_be,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_3_req_wdata,
  output logic                                           o_rvv_3_res_valid,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_3_res_rdata,
  output logic                                           o_rvv_3_res_err,
    // 4
  input  logic                                           i_rvv_4_req_valid,
  output logic                                           o_rvv_4_req_ready,
  input  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_4_req_addr,
  input  logic                                           i_rvv_4_req_we,
  input  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_4_req_be,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_4_req_wdata,
  output logic                                           o_rvv_4_res_valid,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_4_res_rdata,
  output logic                                           o_rvv_4_res_err,
    // 5
  input  logic                                           i_rvv_5_req_valid,
  output logic                                           o_rvv_5_req_ready,
  input  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_5_req_addr,
  input  logic                                           i_rvv_5_req_we,
  input  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_5_req_be,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_5_req_wdata,
  output logic                                           o_rvv_5_res_valid,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_5_res_rdata,
  output logic                                           o_rvv_5_res_err,
    // 6
  input  logic                                           i_rvv_6_req_valid,
  output logic                                           o_rvv_6_req_ready,
  input  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_6_req_addr,
  input  logic                                           i_rvv_6_req_we,
  input  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_6_req_be,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_6_req_wdata,
  output logic                                           o_rvv_6_res_valid,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_6_res_rdata,
  output logic                                           o_rvv_6_res_err,
    // 7
  input  logic                                           i_rvv_7_req_valid,
  output logic                                           o_rvv_7_req_ready,
  input  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_7_req_addr,
  input  logic                                           i_rvv_7_req_we,
  input  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_7_req_be,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_7_req_wdata,
  output logic                                           o_rvv_7_res_valid,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_7_res_rdata,
  output logic                                           o_rvv_7_res_err,

  /////////////// Token ////////////
    // IFD:
    // M IFD0
  output logic [DMC_TOKENS_PROD-1:0] o_m_ifd0_tok_prod_vld,
  input  logic [DMC_TOKENS_PROD-1:0] i_m_ifd0_tok_prod_rdy,
  input  logic [DMC_TOKENS_CONS-1:0] i_m_ifd0_tok_cons_vld,
  output logic [DMC_TOKENS_CONS-1:0] o_m_ifd0_tok_cons_rdy,
    // M IFD1
  output logic [DMC_TOKENS_PROD-1:0] o_m_ifd1_tok_prod_vld,
  input  logic [DMC_TOKENS_PROD-1:0] i_m_ifd1_tok_prod_rdy,
  input  logic [DMC_TOKENS_CONS-1:0] i_m_ifd1_tok_cons_vld,
  output logic [DMC_TOKENS_CONS-1:0] o_m_ifd1_tok_cons_rdy,
    // M IFD2
  output logic [DMC_TOKENS_PROD-1:0] o_m_ifd2_tok_prod_vld,
  input  logic [DMC_TOKENS_PROD-1:0] i_m_ifd2_tok_prod_rdy,
  input  logic [DMC_TOKENS_CONS-1:0] i_m_ifd2_tok_cons_vld,
  output logic [DMC_TOKENS_CONS-1:0] o_m_ifd2_tok_cons_rdy,
    // M IFDW
  output logic [DMC_TOKENS_PROD-1:0] o_m_ifdw_tok_prod_vld,
  input  logic [DMC_TOKENS_PROD-1:0] i_m_ifdw_tok_prod_rdy,
  input  logic [DMC_TOKENS_CONS-1:0] i_m_ifdw_tok_cons_vld,
  output logic [DMC_TOKENS_CONS-1:0] o_m_ifdw_tok_cons_rdy,
    // D IFD0
  output logic [DMC_TOKENS_PROD-1:0] o_d_ifd0_tok_prod_vld,
  input  logic [DMC_TOKENS_PROD-1:0] i_d_ifd0_tok_prod_rdy,
  input  logic [DMC_TOKENS_CONS-1:0] i_d_ifd0_tok_cons_vld,
  output logic [DMC_TOKENS_CONS-1:0] o_d_ifd0_tok_cons_rdy,
    // D IFD1
  output logic [DMC_TOKENS_PROD-1:0] o_d_ifd1_tok_prod_vld,
  input  logic [DMC_TOKENS_PROD-1:0] i_d_ifd1_tok_prod_rdy,
  input  logic [DMC_TOKENS_CONS-1:0] i_d_ifd1_tok_cons_vld,
  output logic [DMC_TOKENS_CONS-1:0] o_d_ifd1_tok_cons_rdy,
    // ODR:
    // M ODR
  output logic [DMC_TOKENS_PROD-1:0] o_m_odr_tok_prod_vld,
  input  logic [DMC_TOKENS_PROD-1:0] i_m_odr_tok_prod_rdy,
  input  logic [DMC_TOKENS_CONS-1:0] i_m_odr_tok_cons_vld,
  output logic [DMC_TOKENS_CONS-1:0] o_m_odr_tok_cons_rdy,
    // D ODR:
  output logic [DMC_TOKENS_PROD-1:0] o_d_odr_tok_prod_vld,
  input  logic [DMC_TOKENS_PROD-1:0] i_d_odr_tok_prod_rdy,
  input  logic [DMC_TOKENS_CONS-1:0] i_d_odr_tok_cons_vld,
  output logic [DMC_TOKENS_CONS-1:0] o_d_odr_tok_cons_rdy,

  ///// Timestamp:
  output logic [DMC_NR_IFDS_ODRS-1:0] o_dmc_ts_start,
  output logic [DMC_NR_IFDS_ODRS-1:0] o_dmc_ts_end,
  ///// ACD sync:
  output logic [DMC_NR_IFDS_ODRS-1:0] o_dmc_acd_sync,

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
  input  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_awaddr,
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
  input  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_araddr,
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
  input logic  [AIC_CID_WIDTH-1:0]               i_cid,
  output logic [AIC_DMC_OBS_DW-1:0]              o_dmc_obs,

  ////////////////////////////////////////////////
  //////// MID feedthrough
  /////////////// Token ////////////
  //// MVM EXE:
    // MID2LS:
  input  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] i_mid_mvm_exe_tok_prod_vld,
  output logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] o_mid_mvm_exe_tok_prod_rdy,
  output logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] o_mid_mvm_exe_tok_cons_vld,
  input  logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] i_mid_mvm_exe_tok_cons_rdy,
    // LS2AIC:
  output logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] o_mid_mvm_exe_tok_prod_vld,
  input  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] i_mid_mvm_exe_tok_prod_rdy,
  input  logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] i_mid_mvm_exe_tok_cons_vld,
  output logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] o_mid_mvm_exe_tok_cons_rdy,
  //// MVM PRG:
    // MID2LS:
  input  logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] i_mid_mvm_prg_tok_prod_vld,
  output logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] o_mid_mvm_prg_tok_prod_rdy,
  output logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] o_mid_mvm_prg_tok_cons_vld,
  input  logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] i_mid_mvm_prg_tok_cons_rdy,
    // LS2AIC:
  output logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] o_mid_mvm_prg_tok_prod_vld,
  input  logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] i_mid_mvm_prg_tok_prod_rdy,
  input  logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] i_mid_mvm_prg_tok_cons_vld,
  output logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] o_mid_mvm_prg_tok_cons_rdy,
  //// IAU:
    // MID2LS:
  input  logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] i_mid_iau_tok_prod_vld,
  output logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] o_mid_iau_tok_prod_rdy,
  output logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] o_mid_iau_tok_cons_vld,
  input  logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] i_mid_iau_tok_cons_rdy,
    // LS2AIC:
  output logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] o_mid_iau_tok_prod_vld,
  input  logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] i_mid_iau_tok_prod_rdy,
  input  logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] i_mid_iau_tok_cons_vld,
  output logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] o_mid_iau_tok_cons_rdy,
  //// DPU:
    // MID2LS:
  input  logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] i_mid_dpu_tok_prod_vld,
  output logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] o_mid_dpu_tok_prod_rdy,
  output logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] o_mid_dpu_tok_cons_vld,
  input  logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] i_mid_dpu_tok_cons_rdy,
    // LS2AIC:
  output logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] o_mid_dpu_tok_prod_vld,
  input  logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] i_mid_dpu_tok_prod_rdy,
  input  logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] i_mid_dpu_tok_cons_vld,
  output logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] o_mid_dpu_tok_cons_rdy,

  /////////////// IRQ ////////////
  input  logic [aic_mid_pkg::NUM_IRQS-1:0] i_mid_irq,
  output logic [aic_mid_pkg::NUM_IRQS-1:0] o_mid_irq,

  /////////////// OBS ////////////
    // MID2LS:
  input  logic [AIC_DEV_OBS_DW-1:0]  i_mid_mvm_exe_obs,
  input  logic [AIC_DEV_OBS_DW-1:0]  i_mid_mvm_prg_obs,
  input  logic [AIC_DEV_OBS_DW-1:0]  i_mid_iau_obs,
  input  logic [AIC_DEV_OBS_DW-1:0]  i_mid_dpu_obs,
  input  logic [AIC_TU_OBS_DW-1:0]   i_mid_tu_obs,
    // LS2AIC:
  output logic [AIC_DEV_OBS_DW-1:0]  o_mid_mvm_exe_obs,
  output logic [AIC_DEV_OBS_DW-1:0]  o_mid_mvm_prg_obs,
  output logic [AIC_DEV_OBS_DW-1:0]  o_mid_iau_obs,
  output logic [AIC_DEV_OBS_DW-1:0]  o_mid_dpu_obs,
  output logic [AIC_TU_OBS_DW-1:0]   o_mid_tu_obs,

  /////////////// Timestamp & ACD sync ////////////
    // MID2LS:
  input  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] i_mid_ts_start,
  input  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] i_mid_ts_end,
  input  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] i_mid_acd_sync,
    // LS2AIC:
  output logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] o_mid_ts_start,
  output logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] o_mid_ts_end,
  output logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] o_mid_acd_sync,

  ////////////////////////////////////////////////
  //////// DID feedthrough
  /////////////// Token ////////////
  //// DWPU:
    // MID2LS:
  input  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_did_dwpu_tok_prod_vld,
  output logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] o_did_dwpu_tok_prod_rdy,
  output logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] o_did_dwpu_tok_cons_vld,
  input  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] i_did_dwpu_tok_cons_rdy,
    // LS2AIC:
  output logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] o_did_dwpu_tok_prod_vld,
  input  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_did_dwpu_tok_prod_rdy,
  input  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] i_did_dwpu_tok_cons_vld,
  output logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] o_did_dwpu_tok_cons_rdy,
  //// IAU:
    // MID2LS:
  input  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_did_iau_tok_prod_vld,
  output logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] o_did_iau_tok_prod_rdy,
  output logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] o_did_iau_tok_cons_vld,
  input  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_did_iau_tok_cons_rdy,
    // LS2AIC:
  output logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] o_did_iau_tok_prod_vld,
  input  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_did_iau_tok_prod_rdy,
  input  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_did_iau_tok_cons_vld,
  output logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] o_did_iau_tok_cons_rdy,
  //// DPU:
    // MID2LS:
  input  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_did_dpu_tok_prod_vld,
  output logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] o_did_dpu_tok_prod_rdy,
  output logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] o_did_dpu_tok_cons_vld,
  input  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_did_dpu_tok_cons_rdy,
    // LS2AIC:
  output logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] o_did_dpu_tok_prod_vld,
  input  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_did_dpu_tok_prod_rdy,
  input  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_did_dpu_tok_cons_vld,
  output logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] o_did_dpu_tok_cons_rdy,

  /////////////// IRQ ////////////
  input  logic [2:0] i_did_irq,
  output logic [2:0] o_did_irq,

  /////////////// OBS ////////////
    // DID2LS:
  input  logic [AIC_DEV_OBS_DW-1:0] i_did_dwpu_obs,
  input  logic [AIC_DEV_OBS_DW-1:0] i_did_iau_obs,
  input  logic [AIC_DEV_OBS_DW-1:0] i_did_dpu_obs,
    // LS2AIC:
  output logic [AIC_DEV_OBS_DW-1:0] o_did_dwpu_obs,
  output logic [AIC_DEV_OBS_DW-1:0] o_did_iau_obs,
  output logic [AIC_DEV_OBS_DW-1:0] o_did_dpu_obs,

  /////////////// Timestamp & ACD sync ////////////
    // DID2LS:
  input  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] i_did_ts_start,
  input  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] i_did_ts_end,
  input  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] i_did_acd_sync,
    // LS2AIC:
  output logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] o_did_ts_start,
  output logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] o_did_ts_end,
  output logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] o_did_acd_sync,


  //------------------------------------------------------
  // AXI write address channel
  output logic                                   o_mid_cfg_axi_m_awvalid,
  output logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] o_mid_cfg_axi_m_awaddr,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_mid_cfg_axi_m_awid,
  output logic [       AIC_LT_AXI_LEN_WIDTH-1:0] o_mid_cfg_axi_m_awlen,
  output logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] o_mid_cfg_axi_m_awsize,
  output logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_mid_cfg_axi_m_awburst,
  input  logic                                   i_mid_cfg_axi_m_awready,
  // AXI write data channel
  output logic                                   o_mid_cfg_axi_m_wvalid,
  output logic                                   o_mid_cfg_axi_m_wlast,
  output logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] o_mid_cfg_axi_m_wstrb,
  output logic [      AIC_LT_AXI_DATA_WIDTH-1:0] o_mid_cfg_axi_m_wdata,
  input  logic                                   i_mid_cfg_axi_m_wready,
  // AXI write response channel
  input  logic                                   i_mid_cfg_axi_m_bvalid,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_mid_cfg_axi_m_bid,
  input  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] i_mid_cfg_axi_m_bresp,
  output logic                                   o_mid_cfg_axi_m_bready,
  // AXI read address channel
  output logic                                   o_mid_cfg_axi_m_arvalid,
  output logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] o_mid_cfg_axi_m_araddr,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_mid_cfg_axi_m_arid,
  output logic [       AIC_LT_AXI_LEN_WIDTH-1:0] o_mid_cfg_axi_m_arlen,
  output logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] o_mid_cfg_axi_m_arsize,
  output logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_mid_cfg_axi_m_arburst,
  input  logic                                   i_mid_cfg_axi_m_arready,
  // AXI read data/response channel
  input  logic                                   i_mid_cfg_axi_m_rvalid,
  input  logic                                   i_mid_cfg_axi_m_rlast,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_mid_cfg_axi_m_rid,
  input  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_mid_cfg_axi_m_rdata,
  input  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] i_mid_cfg_axi_m_rresp,
  output logic                                   o_mid_cfg_axi_m_rready,


    // CFG to DID:
  //------------------------------------------------------
  // AXI write address channel
  output logic                                   o_did_cfg_axi_m_awvalid,
  output logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] o_did_cfg_axi_m_awaddr,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_did_cfg_axi_m_awid,
  output logic [       AIC_LT_AXI_LEN_WIDTH-1:0] o_did_cfg_axi_m_awlen,
  output logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] o_did_cfg_axi_m_awsize,
  output logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_did_cfg_axi_m_awburst,
  input  logic                                   i_did_cfg_axi_m_awready,
  // AXI write data channel
  output logic                                   o_did_cfg_axi_m_wvalid,
  output logic                                   o_did_cfg_axi_m_wlast,
  output logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] o_did_cfg_axi_m_wstrb,
  output logic [      AIC_LT_AXI_DATA_WIDTH-1:0] o_did_cfg_axi_m_wdata,
  input  logic                                   i_did_cfg_axi_m_wready,
  // AXI write response channel
  input  logic                                   i_did_cfg_axi_m_bvalid,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_did_cfg_axi_m_bid,
  input  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] i_did_cfg_axi_m_bresp,
  output logic                                   o_did_cfg_axi_m_bready,
  // AXI read address channel
  output logic                                   o_did_cfg_axi_m_arvalid,
  output logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] o_did_cfg_axi_m_araddr,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_did_cfg_axi_m_arid,
  output logic [       AIC_LT_AXI_LEN_WIDTH-1:0] o_did_cfg_axi_m_arlen,
  output logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] o_did_cfg_axi_m_arsize,
  output logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_did_cfg_axi_m_arburst,
  input  logic                                   i_did_cfg_axi_m_arready,
  // AXI read data/response channel
  input  logic                                   i_did_cfg_axi_m_rvalid,
  input  logic                                   i_did_cfg_axi_m_rlast,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_did_cfg_axi_m_rid,
  input  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_did_cfg_axi_m_rdata,
  input  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] i_did_cfg_axi_m_rresp,
  output logic                                   o_did_cfg_axi_m_rready,

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

  //--------------------------------------------------
  //RF config signals
  //--------------------------------------------------
    /// Margin adjustment control selection
  input  logic [1:0] i_rf_mcs,
    /// Margin adjustment control selection write
  input  logic       i_rf_mcsw,
    /// Retention mode enable input pin (power gating)
  input  logic       i_rf_ret,
    /// Power down enable, active high (power gating)
  input  logic       i_rf_pde,
    /// Scan enable, active high
  input  logic       i_rf_se,
    /// Margin adjustment for access disturbance margin enhancement (Vmin Feature Control Pins)
  input  logic [2:0] i_rf_adme,
    /// Power up ready negative
  output logic       o_rf_prn
);

  axe_tcl_sram_pkg::impl_inp_t mem_impl_inp;
  axe_tcl_sram_pkg::impl_oup_t mem_impl_oup;

  axe_tcl_sram_pkg::impl_inp_t rf_impl_inp;
  axe_tcl_sram_pkg::impl_oup_t rf_impl_oup;

  always_comb begin
    mem_impl_inp.mcs = i_sram_mcs;
    mem_impl_inp.mcsw = i_sram_mcsw;
    mem_impl_inp.ret = i_sram_ret;
    mem_impl_inp.pde = i_sram_pde;
    mem_impl_inp.se = i_sram_se;
    mem_impl_inp.adme = i_sram_adme;
    o_sram_prn = mem_impl_oup.prn;
    // rf:
    rf_impl_inp.mcs = i_rf_mcs;
    rf_impl_inp.mcsw = i_rf_mcsw;
    rf_impl_inp.ret = i_rf_ret;
    rf_impl_inp.pde = i_rf_pde;
    rf_impl_inp.se = i_rf_se;
    rf_impl_inp.adme = i_rf_adme;
    o_rf_prn = rf_impl_oup.prn;
  end
  //////////////////////////////////////////////////////////////
  ////// Signals
    // AXI
  logic                                   dmc_cfg_axi_awvalid;
  logic [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] dmc_cfg_axi_awaddr;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] dmc_cfg_axi_awid;
  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] dmc_cfg_axi_awlen;
  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] dmc_cfg_axi_awsize;
  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] dmc_cfg_axi_awburst;
  logic                                   dmc_cfg_axi_awready;
  // AXI write data channel
  logic                                   dmc_cfg_axi_wvalid;
  logic                                   dmc_cfg_axi_wlast;
  logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] dmc_cfg_axi_wstrb;
  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] dmc_cfg_axi_wdata;
  logic                                   dmc_cfg_axi_wready;
  // AXI write response channel
  logic                                   dmc_cfg_axi_bvalid;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] dmc_cfg_axi_bid;
  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] dmc_cfg_axi_bresp;
  logic                                   dmc_cfg_axi_bready;
  // AXI read address channel
  logic                                   dmc_cfg_axi_arvalid;
  logic [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] dmc_cfg_axi_araddr;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] dmc_cfg_axi_arid;
  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] dmc_cfg_axi_arlen;
  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] dmc_cfg_axi_arsize;
  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] dmc_cfg_axi_arburst;
  logic                                   dmc_cfg_axi_arready;
  // AXI read data/response channel
  logic                                   dmc_cfg_axi_rvalid;
  logic                                   dmc_cfg_axi_rlast;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] dmc_cfg_axi_rid;
  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] dmc_cfg_axi_rdata;
  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] dmc_cfg_axi_rresp;
  logic                                   dmc_cfg_axi_rready;

    // axi streams:
      // IFD:
  logic [dmc_pkg::DMC_NR_IFDS-1:0] ifd_axis_tvalid;
  logic [dmc_pkg::DMC_NR_IFDS-1:0] ifd_axis_tready;
  logic [dmc_pkg::DMC_NR_IFDS-1:0][AIC_PWORD_WIDTH-1:0] ifd_axis_tdata;
  logic [dmc_pkg::DMC_NR_IFDS-1:0] ifd_axis_tlast;
      // ODR:
  logic [dmc_pkg::DMC_NR_ODRS-1:0] odr_axis_tvalid;
  logic [dmc_pkg::DMC_NR_ODRS-1:0] odr_axis_tready;
  logic [dmc_pkg::DMC_NR_ODRS-1:0][AIC_PWORD_WIDTH-1:0] odr_axis_tdata;
  logic [dmc_pkg::DMC_NR_ODRS-1:0] odr_axis_tlast;

    // Token:
  logic [DMC_NR_IFDS_ODRS-1:0][DMC_TOKENS_PROD-1:0] dmc_tok_prod_vld;
  logic [DMC_NR_IFDS_ODRS-1:0][DMC_TOKENS_PROD-1:0] dmc_tok_prod_rdy;
  logic [DMC_NR_IFDS_ODRS-1:0][DMC_TOKENS_CONS-1:0] dmc_tok_cons_vld;
  logic [DMC_NR_IFDS_ODRS-1:0][DMC_TOKENS_CONS-1:0] dmc_tok_cons_rdy;

    // MMIO:
      // DMC:
  mmio_pkg::mmio_dmc_ro_req_t [dmc_pkg::DMC_NR_IFDS:0] dmc_mmio_rd_req;
  mmio_pkg::mmio_dmc_ro_rsp_t [dmc_pkg::DMC_NR_IFDS:0] dmc_mmio_rd_rsp;
  mmio_pkg::mmio_dmc_wo_req_t [dmc_pkg::DMC_NR_ODRS:0] dmc_mmio_wr_req;
  mmio_pkg::mmio_dmc_wo_rsp_t [dmc_pkg::DMC_NR_ODRS:0] dmc_mmio_wr_rsp;
      // RVV:
  mmio_pkg::mmio_rvv_req_t [l1_pkg::DEFAULT_L1_NUM_RVV_REQUESTS-1:0] rvv_mmio_req;
  mmio_pkg::mmio_rvv_rsp_t [l1_pkg::DEFAULT_L1_NUM_RVV_REQUESTS-1:0] rvv_mmio_rsp;

    // OBS:
  aic_common_pkg::aic_dev_obs_t [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] dmc_obs;
  aic_common_pkg::dmc_obs_t                                     dmc_ip_obs;

  //////////////////////////////////////////////////////////////
  ////// specific assignments:
  always_comb begin
    // M_IFD0:
    o_m_ifd0_axis_m_tvalid      = ifd_axis_tvalid[m_ifd0_idx];
    ifd_axis_tready[m_ifd0_idx] = i_m_ifd0_axis_m_tready;
    o_m_ifd0_axis_m_tdata       = ifd_axis_tdata[m_ifd0_idx];
    o_m_ifd0_axis_m_tlast       = ifd_axis_tlast[m_ifd0_idx];
    dmc_ip_obs.m_ifd0_obs       = dmc_obs[m_ifd0_idx];
    o_m_ifd0_tok_prod_vld       = dmc_tok_prod_vld[m_ifd0_idx];
    dmc_tok_prod_rdy[m_ifd0_idx]= i_m_ifd0_tok_prod_rdy;
    dmc_tok_cons_vld[m_ifd0_idx]= i_m_ifd0_tok_cons_vld;
    o_m_ifd0_tok_cons_rdy       = dmc_tok_cons_rdy[m_ifd0_idx];
    // M_IFD1:
    o_m_ifd1_axis_m_tvalid      = ifd_axis_tvalid[m_ifd1_idx];
    ifd_axis_tready[m_ifd1_idx] = i_m_ifd1_axis_m_tready;
    o_m_ifd1_axis_m_tdata       = ifd_axis_tdata[m_ifd1_idx];
    o_m_ifd1_axis_m_tlast       = ifd_axis_tlast[m_ifd1_idx];
    dmc_ip_obs.m_ifd1_obs       = dmc_obs[m_ifd1_idx];
    o_m_ifd1_tok_prod_vld       = dmc_tok_prod_vld[m_ifd1_idx];
    dmc_tok_prod_rdy[m_ifd1_idx]= i_m_ifd1_tok_prod_rdy;
    dmc_tok_cons_vld[m_ifd1_idx]= i_m_ifd1_tok_cons_vld;
    o_m_ifd1_tok_cons_rdy       = dmc_tok_cons_rdy[m_ifd1_idx];
    // M_IFD2:
    o_m_ifd2_axis_m_tvalid      = ifd_axis_tvalid[m_ifd2_idx];
    ifd_axis_tready[m_ifd2_idx] = i_m_ifd2_axis_m_tready;
    o_m_ifd2_axis_m_tdata       = ifd_axis_tdata[m_ifd2_idx];
    o_m_ifd2_axis_m_tlast       = ifd_axis_tlast[m_ifd2_idx];
    dmc_ip_obs.m_ifd2_obs       = dmc_obs[m_ifd2_idx];
    o_m_ifd2_tok_prod_vld       = dmc_tok_prod_vld[m_ifd2_idx];
    dmc_tok_prod_rdy[m_ifd2_idx]= i_m_ifd2_tok_prod_rdy;
    dmc_tok_cons_vld[m_ifd2_idx]= i_m_ifd2_tok_cons_vld;
    o_m_ifd2_tok_cons_rdy       = dmc_tok_cons_rdy[m_ifd2_idx];
    // M_IFDW:
    o_m_ifdw_axis_m_tvalid      = ifd_axis_tvalid[m_ifdw_idx];
    ifd_axis_tready[m_ifdw_idx] = i_m_ifdw_axis_m_tready;
    o_m_ifdw_axis_m_tdata       = ifd_axis_tdata[m_ifdw_idx];
    o_m_ifdw_axis_m_tlast       = ifd_axis_tlast[m_ifdw_idx];
    dmc_ip_obs.m_ifdw_obs       = dmc_obs[m_ifdw_idx];
    o_m_ifdw_tok_prod_vld       = dmc_tok_prod_vld[m_ifdw_idx];
    dmc_tok_prod_rdy[m_ifdw_idx]= i_m_ifdw_tok_prod_rdy;
    dmc_tok_cons_vld[m_ifdw_idx]= i_m_ifdw_tok_cons_vld;
    o_m_ifdw_tok_cons_rdy       = dmc_tok_cons_rdy[m_ifdw_idx];
    // D_IFD0:
    o_d_ifd0_axis_m_tvalid      = ifd_axis_tvalid[d_ifd0_idx];
    ifd_axis_tready[d_ifd0_idx] = i_d_ifd0_axis_m_tready;
    o_d_ifd0_axis_m_tdata       = ifd_axis_tdata[d_ifd0_idx];
    o_d_ifd0_axis_m_tlast       = ifd_axis_tlast[d_ifd0_idx];
    dmc_ip_obs.d_ifd0_obs       = dmc_obs[d_ifd0_idx];
    o_d_ifd0_tok_prod_vld       = dmc_tok_prod_vld[d_ifd0_idx];
    dmc_tok_prod_rdy[d_ifd0_idx]= i_d_ifd0_tok_prod_rdy;
    dmc_tok_cons_vld[d_ifd0_idx]= i_d_ifd0_tok_cons_vld;
    o_d_ifd0_tok_cons_rdy       = dmc_tok_cons_rdy[d_ifd0_idx];
    // D_IFD1:
    o_d_ifd1_axis_m_tvalid      = ifd_axis_tvalid[d_ifd1_idx];
    ifd_axis_tready[d_ifd1_idx] = i_d_ifd1_axis_m_tready;
    o_d_ifd1_axis_m_tdata       = ifd_axis_tdata[d_ifd1_idx];
    o_d_ifd1_axis_m_tlast       = ifd_axis_tlast[d_ifd1_idx];
    dmc_ip_obs.d_ifd1_obs       = dmc_obs[d_ifd1_idx];
    o_d_ifd1_tok_prod_vld       = dmc_tok_prod_vld[d_ifd1_idx];
    dmc_tok_prod_rdy[d_ifd1_idx]= i_d_ifd1_tok_prod_rdy;
    dmc_tok_cons_vld[d_ifd1_idx]= i_d_ifd1_tok_cons_vld;
    o_d_ifd1_tok_cons_rdy       = dmc_tok_cons_rdy[d_ifd1_idx];
    // M_ODR:
    odr_axis_tvalid[m_odr_idx-DMC_NR_IFDS]  = i_m_odr_axis_s_tvalid;
    o_m_odr_axis_s_tready                   = odr_axis_tready[m_odr_idx-DMC_NR_IFDS];
    odr_axis_tdata[m_odr_idx-DMC_NR_IFDS]   = i_m_odr_axis_s_tdata;
    odr_axis_tlast[m_odr_idx-DMC_NR_IFDS]   = i_m_odr_axis_s_tlast;
    dmc_ip_obs.m_odr_obs                    = dmc_obs[m_odr_idx];
    o_m_odr_tok_prod_vld                    = dmc_tok_prod_vld[m_odr_idx];
    dmc_tok_prod_rdy[m_odr_idx]             = i_m_odr_tok_prod_rdy;
    dmc_tok_cons_vld[m_odr_idx]             = i_m_odr_tok_cons_vld;
    o_m_odr_tok_cons_rdy                    = dmc_tok_cons_rdy[m_odr_idx];
    // D_ODR:
    odr_axis_tvalid[d_odr_idx-DMC_NR_IFDS]  = i_d_odr_axis_s_tvalid;
    o_d_odr_axis_s_tready                   = odr_axis_tready[d_odr_idx-DMC_NR_IFDS];
    odr_axis_tdata[d_odr_idx-DMC_NR_IFDS]   = i_d_odr_axis_s_tdata;
    odr_axis_tlast[d_odr_idx-DMC_NR_IFDS]   = i_d_odr_axis_s_tlast;
    dmc_ip_obs.d_odr_obs                    = dmc_obs[d_odr_idx];
    o_d_odr_tok_prod_vld                    = dmc_tok_prod_vld[d_odr_idx];
    dmc_tok_prod_rdy[d_odr_idx]             = i_d_odr_tok_prod_rdy;
    dmc_tok_cons_vld[d_odr_idx]             = i_d_odr_tok_cons_vld;
    o_d_odr_tok_cons_rdy                    = dmc_tok_cons_rdy[d_odr_idx];
  end
  always_comb o_dmc_obs                     = dmc_ip_obs;

  // RVV
  always_comb begin
    // 0
    rvv_mmio_req[0].valid         = i_rvv_0_req_valid;
    o_rvv_0_req_ready             = rvv_mmio_rsp[0].ready;
    rvv_mmio_req[0].payload.addr  = i_rvv_0_req_addr[mmio_pkg::MMIO_RVV_ADDR_WIDTH-1:0];
    rvv_mmio_req[0].payload.we    = i_rvv_0_req_we;
    rvv_mmio_req[0].payload.wbe   = i_rvv_0_req_be;
    rvv_mmio_req[0].payload.data  = i_rvv_0_req_wdata;
    rvv_mmio_req[0].rsp_ready     = 1'b1;
    o_rvv_0_res_valid             = rvv_mmio_rsp[0].ack;
    o_rvv_0_res_rdata             = rvv_mmio_rsp[0].payload.data;
    o_rvv_0_res_err               = rvv_mmio_rsp[0].payload.error;
    // 1
    rvv_mmio_req[1].valid         = i_rvv_1_req_valid;
    o_rvv_1_req_ready             = rvv_mmio_rsp[1].ready;
    rvv_mmio_req[1].payload.addr  = i_rvv_1_req_addr[mmio_pkg::MMIO_RVV_ADDR_WIDTH-1:0];
    rvv_mmio_req[1].payload.we    = i_rvv_1_req_we;
    rvv_mmio_req[1].payload.wbe   = i_rvv_1_req_be;
    rvv_mmio_req[1].payload.data  = i_rvv_1_req_wdata;
    rvv_mmio_req[1].rsp_ready     = 1'b1;
    o_rvv_1_res_valid             = rvv_mmio_rsp[1].ack;
    o_rvv_1_res_rdata             = rvv_mmio_rsp[1].payload.data;
    o_rvv_1_res_err               = rvv_mmio_rsp[1].payload.error;
    // 2
    rvv_mmio_req[2].valid         = i_rvv_2_req_valid;
    o_rvv_2_req_ready             = rvv_mmio_rsp[2].ready;
    rvv_mmio_req[2].payload.addr  = i_rvv_2_req_addr[mmio_pkg::MMIO_RVV_ADDR_WIDTH-1:0];
    rvv_mmio_req[2].payload.we    = i_rvv_2_req_we;
    rvv_mmio_req[2].payload.wbe   = i_rvv_2_req_be;
    rvv_mmio_req[2].payload.data  = i_rvv_2_req_wdata;
    rvv_mmio_req[2].rsp_ready     = 1'b1;
    o_rvv_2_res_valid             = rvv_mmio_rsp[2].ack;
    o_rvv_2_res_rdata             = rvv_mmio_rsp[2].payload.data;
    o_rvv_2_res_err               = rvv_mmio_rsp[2].payload.error;
    // 3
    rvv_mmio_req[3].valid         = i_rvv_3_req_valid;
    o_rvv_3_req_ready             = rvv_mmio_rsp[3].ready;
    rvv_mmio_req[3].payload.addr  = i_rvv_3_req_addr[mmio_pkg::MMIO_RVV_ADDR_WIDTH-1:0];
    rvv_mmio_req[3].payload.we    = i_rvv_3_req_we;
    rvv_mmio_req[3].payload.wbe   = i_rvv_3_req_be;
    rvv_mmio_req[3].payload.data  = i_rvv_3_req_wdata;
    rvv_mmio_req[3].rsp_ready     = 1'b1;
    o_rvv_3_res_valid             = rvv_mmio_rsp[3].ack;
    o_rvv_3_res_rdata             = rvv_mmio_rsp[3].payload.data;
    o_rvv_3_res_err               = rvv_mmio_rsp[3].payload.error;
    // 4
    rvv_mmio_req[4].valid         = i_rvv_4_req_valid;
    o_rvv_4_req_ready             = rvv_mmio_rsp[4].ready;
    rvv_mmio_req[4].payload.addr  = i_rvv_4_req_addr[mmio_pkg::MMIO_RVV_ADDR_WIDTH-1:0];
    rvv_mmio_req[4].payload.we    = i_rvv_4_req_we;
    rvv_mmio_req[4].payload.wbe   = i_rvv_4_req_be;
    rvv_mmio_req[4].payload.data  = i_rvv_4_req_wdata;
    rvv_mmio_req[4].rsp_ready     = 1'b1;
    o_rvv_4_res_valid             = rvv_mmio_rsp[4].ack;
    o_rvv_4_res_rdata             = rvv_mmio_rsp[4].payload.data;
    o_rvv_4_res_err               = rvv_mmio_rsp[4].payload.error;
    // 5
    rvv_mmio_req[5].valid         = i_rvv_5_req_valid;
    o_rvv_5_req_ready             = rvv_mmio_rsp[5].ready;
    rvv_mmio_req[5].payload.addr  = i_rvv_5_req_addr[mmio_pkg::MMIO_RVV_ADDR_WIDTH-1:0];
    rvv_mmio_req[5].payload.we    = i_rvv_5_req_we;
    rvv_mmio_req[5].payload.wbe   = i_rvv_5_req_be;
    rvv_mmio_req[5].payload.data  = i_rvv_5_req_wdata;
    rvv_mmio_req[5].rsp_ready     = 1'b1;
    o_rvv_5_res_valid             = rvv_mmio_rsp[5].ack;
    o_rvv_5_res_rdata             = rvv_mmio_rsp[5].payload.data;
    o_rvv_5_res_err               = rvv_mmio_rsp[5].payload.error;
    // 6
    rvv_mmio_req[6].valid         = i_rvv_6_req_valid;
    o_rvv_6_req_ready             = rvv_mmio_rsp[6].ready;
    rvv_mmio_req[6].payload.addr  = i_rvv_6_req_addr[mmio_pkg::MMIO_RVV_ADDR_WIDTH-1:0];
    rvv_mmio_req[6].payload.we    = i_rvv_6_req_we;
    rvv_mmio_req[6].payload.wbe   = i_rvv_6_req_be;
    rvv_mmio_req[6].payload.data  = i_rvv_6_req_wdata;
    rvv_mmio_req[6].rsp_ready     = 1'b1;
    o_rvv_6_res_valid             = rvv_mmio_rsp[6].ack;
    o_rvv_6_res_rdata             = rvv_mmio_rsp[6].payload.data;
    o_rvv_6_res_err               = rvv_mmio_rsp[6].payload.error;
    // 7
    rvv_mmio_req[7].valid         = i_rvv_7_req_valid;
    o_rvv_7_req_ready             = rvv_mmio_rsp[7].ready;
    rvv_mmio_req[7].payload.addr  = i_rvv_7_req_addr[mmio_pkg::MMIO_RVV_ADDR_WIDTH-1:0];
    rvv_mmio_req[7].payload.we    = i_rvv_7_req_we;
    rvv_mmio_req[7].payload.wbe   = i_rvv_7_req_be;
    rvv_mmio_req[7].payload.data  = i_rvv_7_req_wdata;
    rvv_mmio_req[7].rsp_ready     = 1'b1;
    o_rvv_7_res_valid             = rvv_mmio_rsp[7].ack;
    o_rvv_7_res_rdata             = rvv_mmio_rsp[7].payload.data;
    o_rvv_7_res_err               = rvv_mmio_rsp[7].payload.error;
  end
  //////////////////////////////////////////////////////////////
  ////// Modules
  // DMC:
  dmc #(
    .DMC_REGION_SLAVE_ID(AIC_LS_DMC_REGION_SLAVE_ID),
    .DMC_REGION_ST_ADDR(AIC_LS_DMC_REGION_ST_ADDR),
    .DMC_REGION_END_ADDR(AIC_LS_DMC_REGION_END_ADDR),
    .DMC_DEV_REGION_ST_ADDR(AIC_LS_DMC_DEV_REGION_ST_ADDR),
    .DMC_DEV_REGION_END_ADDR(AIC_LS_DMC_DEV_REGION_END_ADDR),
    .L1_ST_ADDR(aic_addr_map_pkg::AIC_L1_ST_ADDR),
    .L1_END_ADDR(aic_addr_map_pkg::AIC_L1_END_ADDR)
  ) u_dmc (
    /// Clock, positive edge triggered
    .i_clk(i_clk),
    /// Asynchronous reset, active low
    .i_rst_n(i_rst_n),

    .i_scan_en(i_scan_en),

    .o_irq(o_dmc_irq),

    // axi streams:
      // IFD:
    .o_dmc_ip_axis_m_tvalid(ifd_axis_tvalid),
    .i_dmc_ip_axis_m_tready(ifd_axis_tready),
    .o_dmc_ip_axis_m_tdata(ifd_axis_tdata),
    .o_dmc_ip_axis_m_tlast(ifd_axis_tlast),
      // ODR:
    .i_ip_dmc_axis_s_tvalid(odr_axis_tvalid),
    .o_ip_dmc_axis_s_tready(odr_axis_tready),
    .i_ip_dmc_axis_s_tdata(odr_axis_tdata),
    .i_ip_dmc_axis_s_tlast(odr_axis_tlast),

    // MMIO L1:
      // DMC -> L1 read only (IFD + A2M)
    .o_mmio_rd_m_req(dmc_mmio_rd_req),
    .i_mmio_rd_m_rsp(dmc_mmio_rd_rsp),
      // DMC -> L1 write only (ODR + A2M)
    .o_mmio_wr_m_req(dmc_mmio_wr_req),
    .i_mmio_wr_m_rsp(dmc_mmio_wr_rsp),

    /////////////// Token ////////////
    .o_dev_prod_vld(dmc_tok_prod_vld),
    .i_dev_prod_rdy(dmc_tok_prod_rdy),
    .i_dev_cons_vld(dmc_tok_cons_vld),
    .o_dev_cons_rdy(dmc_tok_cons_rdy),

    ///// Timestamp:
    .o_ts_start(o_dmc_ts_start),
    .o_ts_end(o_dmc_ts_end),
    ///// ACD sync:
    .o_acd_sync(o_dmc_acd_sync),

    // A2M:
    //------------------------------------------------------
    // AXI write address channel
    .i_hp_axi_s_awvalid(i_hp_axi_s_awvalid),
    .i_hp_axi_s_awaddr(i_hp_axi_s_awaddr),
    .i_hp_axi_s_awid(i_hp_axi_s_awid),
    .i_hp_axi_s_awlen(i_hp_axi_s_awlen),
    .i_hp_axi_s_awsize(i_hp_axi_s_awsize),
    .i_hp_axi_s_awburst(i_hp_axi_s_awburst),
    .i_hp_axi_s_awcache(i_hp_axi_s_awcache),
    .i_hp_axi_s_awprot(i_hp_axi_s_awprot),
    .i_hp_axi_s_awlock(i_hp_axi_s_awlock),
    .o_hp_axi_s_awready(o_hp_axi_s_awready),
    // AXI write data channel
    .i_hp_axi_s_wvalid(i_hp_axi_s_wvalid),
    .i_hp_axi_s_wlast(i_hp_axi_s_wlast),
    .i_hp_axi_s_wstrb(i_hp_axi_s_wstrb),
    .i_hp_axi_s_wdata(i_hp_axi_s_wdata),
    .o_hp_axi_s_wready(o_hp_axi_s_wready),
    // AXI write response channel
    .o_hp_axi_s_bvalid(o_hp_axi_s_bvalid),
    .o_hp_axi_s_bid(o_hp_axi_s_bid),
    .o_hp_axi_s_bresp(o_hp_axi_s_bresp),
    .i_hp_axi_s_bready(i_hp_axi_s_bready),
    // AXI read address channel
    .i_hp_axi_s_arvalid(i_hp_axi_s_arvalid),
    .i_hp_axi_s_araddr(i_hp_axi_s_araddr),
    .i_hp_axi_s_arid(i_hp_axi_s_arid),
    .i_hp_axi_s_arlen(i_hp_axi_s_arlen),
    .i_hp_axi_s_arsize(i_hp_axi_s_arsize),
    .i_hp_axi_s_arburst(i_hp_axi_s_arburst),
    .i_hp_axi_s_arcache(i_hp_axi_s_arcache),
    .i_hp_axi_s_arprot(i_hp_axi_s_arprot),
    .i_hp_axi_s_arlock(i_hp_axi_s_arlock),
    .o_hp_axi_s_arready(o_hp_axi_s_arready),
    // AXI read data/response channel
    .o_hp_axi_s_rvalid(o_hp_axi_s_rvalid),
    .o_hp_axi_s_rlast(o_hp_axi_s_rlast),
    .o_hp_axi_s_rid(o_hp_axi_s_rid),
    .o_hp_axi_s_rdata(o_hp_axi_s_rdata),
    .o_hp_axi_s_rresp(o_hp_axi_s_rresp),
    .i_hp_axi_s_rready(i_hp_axi_s_rready),


    // CFG:
    //------------------------------------------------------
    // AXI write address channel
    .i_cfg_axi_s_awvalid(dmc_cfg_axi_awvalid),
    .i_cfg_axi_s_awaddr(dmc_cfg_axi_awaddr),
    .i_cfg_axi_s_awid(dmc_cfg_axi_awid),
    .i_cfg_axi_s_awlen(dmc_cfg_axi_awlen),
    .i_cfg_axi_s_awsize(dmc_cfg_axi_awsize),
    .i_cfg_axi_s_awburst(dmc_cfg_axi_awburst),
    .o_cfg_axi_s_awready(dmc_cfg_axi_awready),
    // AXI write data channel
    .i_cfg_axi_s_wvalid(dmc_cfg_axi_wvalid),
    .i_cfg_axi_s_wlast(dmc_cfg_axi_wlast),
    .i_cfg_axi_s_wstrb(dmc_cfg_axi_wstrb),
    .i_cfg_axi_s_wdata(dmc_cfg_axi_wdata),
    .o_cfg_axi_s_wready(dmc_cfg_axi_wready),
    // AXI write response channel
    .o_cfg_axi_s_bvalid(dmc_cfg_axi_bvalid),
    .o_cfg_axi_s_bid(dmc_cfg_axi_bid),
    .o_cfg_axi_s_bresp(dmc_cfg_axi_bresp),
    .i_cfg_axi_s_bready(dmc_cfg_axi_bready),
    // AXI read address channel
    .i_cfg_axi_s_arvalid(dmc_cfg_axi_arvalid),
    .i_cfg_axi_s_araddr(dmc_cfg_axi_araddr),
    .i_cfg_axi_s_arid(dmc_cfg_axi_arid),
    .i_cfg_axi_s_arlen(dmc_cfg_axi_arlen),
    .i_cfg_axi_s_arsize(dmc_cfg_axi_arsize),
    .i_cfg_axi_s_arburst(dmc_cfg_axi_arburst),
    .o_cfg_axi_s_arready(dmc_cfg_axi_arready),
    // AXI read data/response channel
    .o_cfg_axi_s_rvalid(dmc_cfg_axi_rvalid),
    .o_cfg_axi_s_rlast(dmc_cfg_axi_rlast),
    .o_cfg_axi_s_rid(dmc_cfg_axi_rid),
    .o_cfg_axi_s_rdata(dmc_cfg_axi_rdata),
    .o_cfg_axi_s_rresp(dmc_cfg_axi_rresp),
    .i_cfg_axi_s_rready(dmc_cfg_axi_rready),

    // Sidebands:
    .i_cid(i_cid),
    .o_dmc_obs(dmc_obs),

    .i_sram_impl(rf_impl_inp),
    .o_sram_impl(rf_impl_oup)
  );

  // L1:
  l1 #(
    .L1_DAISY_CHAIN_MAPPING(AIC_LS_L1_DAISY_CHAIN_MAPPING)
  ) u_l1 (
  // Clock and reset signals
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_scan_en(i_scan_en),

    // =====================================================
    // DMC MMIO
    // =====================================================
    .i_dmc_wo_req(dmc_mmio_wr_req),
    .o_dmc_wo_rsp(dmc_mmio_wr_rsp),
    .i_dmc_ro_req(dmc_mmio_rd_req),
    .o_dmc_ro_rsp(dmc_mmio_rd_rsp),

    // =====================================================
    // RVV MMIO
    // =====================================================
    .i_rvv_req(rvv_mmio_req),
    .o_rvv_rsp(rvv_mmio_rsp),

    .i_mem_impl(mem_impl_inp),
    .o_mem_impl(mem_impl_oup)
  );

  //////////////////////////////////////////////////////////////
  ////// feedthrough:
    /////////// Tokens:
      // MVM exe
  for (genvar prod=0;unsigned'(prod)<TOK_MGR_M_MVMEXE_NR_TOK_PROD; prod++) begin: g_mvm_exe_prod
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_prod_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_mid_mvm_exe_tok_prod_vld[prod]),
      .i_flush(1'b0),
      .o_ready(o_mid_mvm_exe_tok_prod_rdy[prod]),
      .i_data(1'b0),
      .o_valid(o_mid_mvm_exe_tok_prod_vld[prod]),
      .i_ready(i_mid_mvm_exe_tok_prod_rdy[prod]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
  for (genvar cons=0;unsigned'(cons)<TOK_MGR_M_MVMEXE_NR_TOK_CONS; cons++) begin: g_mvm_exe_cons
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_cons_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_mid_mvm_exe_tok_cons_vld[cons]),
      .i_flush(1'b0),
      .o_ready(o_mid_mvm_exe_tok_cons_rdy[cons]),
      .i_data(1'b0),
      .o_valid(o_mid_mvm_exe_tok_cons_vld[cons]),
      .i_ready(i_mid_mvm_exe_tok_cons_rdy[cons]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
      // MVM prg
  for (genvar prod=0;unsigned'(prod)<TOK_MGR_M_MVMPRG_NR_TOK_PROD; prod++) begin: g_mvm_prg_prod
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_prod_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_mid_mvm_prg_tok_prod_vld[prod]),
      .i_flush(1'b0),
      .o_ready(o_mid_mvm_prg_tok_prod_rdy[prod]),
      .i_data(1'b0),
      .o_valid(o_mid_mvm_prg_tok_prod_vld[prod]),
      .i_ready(i_mid_mvm_prg_tok_prod_rdy[prod]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
  for (genvar cons=0;unsigned'(cons)<TOK_MGR_M_MVMPRG_NR_TOK_CONS; cons++) begin: g_mvm_prg_cons
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_cons_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_mid_mvm_prg_tok_cons_vld[cons]),
      .i_flush(1'b0),
      .o_ready(o_mid_mvm_prg_tok_cons_rdy[cons]),
      .i_data(1'b0),
      .o_valid(o_mid_mvm_prg_tok_cons_vld[cons]),
      .i_ready(i_mid_mvm_prg_tok_cons_rdy[cons]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
      // MID_IAU
  for (genvar prod=0;unsigned'(prod)<TOK_MGR_M_IAU_NR_TOK_PROD; prod++) begin: g_mid_iau_prod
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_prod_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_mid_iau_tok_prod_vld[prod]),
      .i_flush(1'b0),
      .o_ready(o_mid_iau_tok_prod_rdy[prod]),
      .i_data(1'b0),
      .o_valid(o_mid_iau_tok_prod_vld[prod]),
      .i_ready(i_mid_iau_tok_prod_rdy[prod]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
  for (genvar cons=0;unsigned'(cons)<TOK_MGR_M_IAU_NR_TOK_CONS; cons++) begin: g_mid_iau_cons
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_cons_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_mid_iau_tok_cons_vld[cons]),
      .i_flush(1'b0),
      .o_ready(o_mid_iau_tok_cons_rdy[cons]),
      .i_data(1'b0),
      .o_valid(o_mid_iau_tok_cons_vld[cons]),
      .i_ready(i_mid_iau_tok_cons_rdy[cons]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
      // MID_DPU
  for (genvar prod=0;unsigned'(prod)<TOK_MGR_M_DPU_NR_TOK_PROD; prod++) begin: g_mid_dpu_prod
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_prod_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_mid_dpu_tok_prod_vld[prod]),
      .i_flush(1'b0),
      .o_ready(o_mid_dpu_tok_prod_rdy[prod]),
      .i_data(1'b0),
      .o_valid(o_mid_dpu_tok_prod_vld[prod]),
      .i_ready(i_mid_dpu_tok_prod_rdy[prod]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
  for (genvar cons=0;unsigned'(cons)<TOK_MGR_M_DPU_NR_TOK_CONS; cons++) begin: g_mid_dpu_cons
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_cons_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_mid_dpu_tok_cons_vld[cons]),
      .i_flush(1'b0),
      .o_ready(o_mid_dpu_tok_cons_rdy[cons]),
      .i_data(1'b0),
      .o_valid(o_mid_dpu_tok_cons_vld[cons]),
      .i_ready(i_mid_dpu_tok_cons_rdy[cons]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
      // MVM prg
  for (genvar prod=0;unsigned'(prod)<TOK_MGR_D_DWPU_NR_TOK_PROD; prod++) begin: g_dwpu_prod
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_prod_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_did_dwpu_tok_prod_vld[prod]),
      .i_flush(1'b0),
      .o_ready(o_did_dwpu_tok_prod_rdy[prod]),
      .i_data(1'b0),
      .o_valid(o_did_dwpu_tok_prod_vld[prod]),
      .i_ready(i_did_dwpu_tok_prod_rdy[prod]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
  for (genvar cons=0;unsigned'(cons)<TOK_MGR_D_DWPU_NR_TOK_CONS; cons++) begin: g_dwpu_cons
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_cons_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_did_dwpu_tok_cons_vld[cons]),
      .i_flush(1'b0),
      .o_ready(o_did_dwpu_tok_cons_rdy[cons]),
      .i_data(1'b0),
      .o_valid(o_did_dwpu_tok_cons_vld[cons]),
      .i_ready(i_did_dwpu_tok_cons_rdy[cons]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
      // MID_IAU
  for (genvar prod=0;unsigned'(prod)<TOK_MGR_D_IAU_NR_TOK_PROD; prod++) begin: g_did_iau_prod
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_prod_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_did_iau_tok_prod_vld[prod]),
      .i_flush(1'b0),
      .o_ready(o_did_iau_tok_prod_rdy[prod]),
      .i_data(1'b0),
      .o_valid(o_did_iau_tok_prod_vld[prod]),
      .i_ready(i_did_iau_tok_prod_rdy[prod]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
  for (genvar cons=0;unsigned'(cons)<TOK_MGR_D_IAU_NR_TOK_CONS; cons++) begin: g_did_iau_cons
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_cons_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_did_iau_tok_cons_vld[cons]),
      .i_flush(1'b0),
      .o_ready(o_did_iau_tok_cons_rdy[cons]),
      .i_data(1'b0),
      .o_valid(o_did_iau_tok_cons_vld[cons]),
      .i_ready(i_did_iau_tok_cons_rdy[cons]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
      // MID_DPU
  for (genvar prod=0;unsigned'(prod)<TOK_MGR_D_DPU_NR_TOK_PROD; prod++) begin: g_did_dpu_prod
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_prod_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_did_dpu_tok_prod_vld[prod]),
      .i_flush(1'b0),
      .o_ready(o_did_dpu_tok_prod_rdy[prod]),
      .i_data(1'b0),
      .o_valid(o_did_dpu_tok_prod_vld[prod]),
      .i_ready(i_did_dpu_tok_prod_rdy[prod]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end
  for (genvar cons=0;unsigned'(cons)<TOK_MGR_D_DPU_NR_TOK_CONS; cons++) begin: g_did_dpu_cons
    cc_stream_spill_reg #(
      .DataWidth(1)
    ) u_cons_spill (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_valid(i_did_dpu_tok_cons_vld[cons]),
      .i_flush(1'b0),
      .o_ready(o_did_dpu_tok_cons_rdy[cons]),
      .i_data(1'b0),
      .o_valid(o_did_dpu_tok_cons_vld[cons]),
      .i_ready(i_did_dpu_tok_cons_rdy[cons]),
      .o_data() // ASO-UNUSED_OUTPUT: not used
    );
  end

  // IRQ:
  reg [aic_mid_pkg::NUM_IRQS-1:0] mid_irq_q;
  reg [2:0] did_irq_q;
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (i_rst_n == 1'b0) begin
      mid_irq_q <= '0;
      did_irq_q <= '0;
    end else begin
      if (mid_irq_q != i_mid_irq)
        mid_irq_q <= i_mid_irq;
      if (did_irq_q != i_did_irq)
        did_irq_q <= i_did_irq;
    end
  end
  always_comb o_mid_irq = mid_irq_q;
  always_comb o_did_irq = did_irq_q;

  // OBS:
  reg [AIC_DEV_OBS_DW-1:0] mid_mvm_exe_obs_q;
  reg [AIC_DEV_OBS_DW-1:0] mid_mvm_prg_obs_q;
  reg [AIC_DEV_OBS_DW-1:0] mid_iau_obs_q;
  reg [AIC_DEV_OBS_DW-1:0] mid_dpu_obs_q;
  reg [AIC_TU_OBS_DW-1:0]  mid_tu_obs_q;
  reg [AIC_DEV_OBS_DW-1:0] did_dwpu_obs_q;
  reg [AIC_DEV_OBS_DW-1:0] did_iau_obs_q;
  reg [AIC_DEV_OBS_DW-1:0] did_dpu_obs_q;
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (i_rst_n == 1'b0) begin
      mid_mvm_exe_obs_q <= '0;
      mid_mvm_prg_obs_q <= '0;
      mid_iau_obs_q     <= '0;
      mid_dpu_obs_q     <= '0;
      mid_tu_obs_q      <= '0;
      did_dwpu_obs_q    <= '0;
      did_iau_obs_q     <= '0;
      did_dpu_obs_q     <= '0;
    end else begin
      if (mid_mvm_exe_obs_q != i_mid_mvm_exe_obs)
        mid_mvm_exe_obs_q <= i_mid_mvm_exe_obs;
      if (mid_mvm_prg_obs_q != i_mid_mvm_prg_obs)
        mid_mvm_prg_obs_q <= i_mid_mvm_prg_obs;
      if (mid_iau_obs_q != i_mid_iau_obs)
        mid_iau_obs_q <= i_mid_iau_obs;
      if (mid_dpu_obs_q != i_mid_dpu_obs)
        mid_dpu_obs_q <= i_mid_dpu_obs;
      if (mid_tu_obs_q != i_mid_tu_obs)
        mid_tu_obs_q <= i_mid_tu_obs;
      if (did_dwpu_obs_q != i_did_dwpu_obs)
        did_dwpu_obs_q <= i_did_dwpu_obs;
      if (did_iau_obs_q != i_did_iau_obs)
        did_iau_obs_q <= i_did_iau_obs;
      if (did_dpu_obs_q != i_did_dpu_obs)
        did_dpu_obs_q <= i_did_dpu_obs;
    end
  end
  always_comb o_mid_mvm_exe_obs  = mid_mvm_exe_obs_q;
  always_comb o_mid_mvm_prg_obs  = mid_mvm_prg_obs_q;
  always_comb o_mid_iau_obs  = mid_iau_obs_q;
  always_comb o_mid_dpu_obs  = mid_dpu_obs_q;
  always_comb o_mid_tu_obs   = mid_tu_obs_q;
  always_comb o_did_dwpu_obs = did_dwpu_obs_q;
  always_comb o_did_iau_obs  = did_iau_obs_q;
  always_comb o_did_dpu_obs  = did_dpu_obs_q;

  // Timestamp / acd sync:
  reg [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] mid_ts_start_q;
  reg [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] mid_ts_end_q;
  reg [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] mid_acd_sync_q;
  reg [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] did_ts_start_q;
  reg [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] did_ts_end_q;
  reg [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] did_acd_sync_q;
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (i_rst_n == 1'b0) begin
      mid_ts_start_q <= '0;
      mid_ts_end_q   <= '0;
      mid_acd_sync_q <= '0;
      did_ts_start_q <= '0;
      did_ts_end_q   <= '0;
      did_acd_sync_q <= '0;
    end else begin
      if (mid_ts_start_q != i_mid_ts_start)
        mid_ts_start_q <= i_mid_ts_start;
      if (mid_ts_end_q != i_mid_ts_end)
        mid_ts_end_q <= i_mid_ts_end;
      if (mid_acd_sync_q != i_mid_acd_sync)
        mid_acd_sync_q <= i_mid_acd_sync;
      if (did_ts_start_q != i_did_ts_start)
        did_ts_start_q <= i_did_ts_start;
      if (did_ts_end_q != i_did_ts_end)
        did_ts_end_q <= i_did_ts_end;
      if (did_acd_sync_q != i_did_acd_sync)
        did_acd_sync_q <= i_did_acd_sync;
    end
  end
  always_comb o_mid_ts_start = mid_ts_start_q;
  always_comb o_mid_ts_end   = mid_ts_end_q;
  always_comb o_mid_acd_sync = mid_acd_sync_q;
  always_comb o_did_ts_start = did_ts_start_q;
  always_comb o_did_ts_end   = did_ts_end_q;
  always_comb o_did_acd_sync = did_acd_sync_q;

  /////////// AXI:
  logic [$clog2(AIC_LS_NR_AXI_DEVS+1)-1:0] bus_sel_rd;
  logic [$clog2(AIC_LS_NR_AXI_DEVS+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(AIC_LS_NR_AXI_DEVS),
    .NR_REGIONS(AIC_LS_NR_REGIONS),
    .REGION_ST_ADDR(AIC_LS_REGION_ST_ADDR),
    .REGION_END_ADDR(AIC_LS_REGION_END_ADDR),
    .REGION_SLAVE_ID(AIC_LS_REGION_SLAVE_ID)
  ) u_ext_decode_wr (
    .addr_in(i_cfg_axi_s_awaddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(AIC_LS_NR_AXI_DEVS),
    .NR_REGIONS(AIC_LS_NR_REGIONS),
    .REGION_ST_ADDR(AIC_LS_REGION_ST_ADDR),
    .REGION_END_ADDR(AIC_LS_REGION_END_ADDR),
    .REGION_SLAVE_ID(AIC_LS_REGION_SLAVE_ID)
  ) u_ext_decode_rd (
    .addr_in(i_cfg_axi_s_araddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  simple_axi_demux #(
    .NR_MASTERS(3),
    .IDW(AIC_LT_AXI_S_ID_WIDTH),
    .AW(AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DW(AIC_LT_AXI_DATA_WIDTH),
    .BW(AIC_LT_AXI_LEN_WIDTH),
    .SL_WREQ_SHIELD(2),
    .SL_RREQ_SHIELD(2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR(AIC_LS_BUS_OSR),

    .EXT_SEL(1)
  ) u_bus (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),

    ///// AXI slave:
    // Write Address Channel
    .s_awid   (i_cfg_axi_s_awid),
    .s_awaddr (i_cfg_axi_s_awaddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]),
    .s_awlen  (i_cfg_axi_s_awlen),
    .s_awsize (i_cfg_axi_s_awsize),
    .s_awburst(i_cfg_axi_s_awburst),
    .s_awlock ('0),
    .s_awprot ('0),
    .s_awcache('0),
    .s_awvalid(i_cfg_axi_s_awvalid),
    .s_awready(o_cfg_axi_s_awready),
    // Read Address Channel
    .s_arid   (i_cfg_axi_s_arid),
    .s_araddr (i_cfg_axi_s_araddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]),
    .s_arlen  (i_cfg_axi_s_arlen),
    .s_arsize (i_cfg_axi_s_arsize),
    .s_arburst(i_cfg_axi_s_arburst),
    .s_arlock ('0),
    .s_arprot ('0),
    .s_arcache('0),
    .s_arvalid(i_cfg_axi_s_arvalid),
    .s_arready(o_cfg_axi_s_arready),
    // Write  Data Channel
    .s_wdata (i_cfg_axi_s_wdata),
    .s_wstrb (i_cfg_axi_s_wstrb),
    .s_wlast (i_cfg_axi_s_wlast),
    .s_wvalid(i_cfg_axi_s_wvalid),
    .s_wready(o_cfg_axi_s_wready),
    // Read Data Channel
    .s_rid   (o_cfg_axi_s_rid),
    .s_rdata (o_cfg_axi_s_rdata),
    .s_rresp (o_cfg_axi_s_rresp),
    .s_rlast (o_cfg_axi_s_rlast),
    .s_rvalid(o_cfg_axi_s_rvalid),
    .s_rready(i_cfg_axi_s_rready),
    // Write Response Channel
    .s_bid   (o_cfg_axi_s_bid),
    .s_bresp (o_cfg_axi_s_bresp),
    .s_bvalid(o_cfg_axi_s_bvalid),
    .s_bready(i_cfg_axi_s_bready),

    ///// AXI Master:
    // Write Address Channel
    .m_awid   ({dmc_cfg_axi_awid,    o_mid_cfg_axi_m_awid,    o_did_cfg_axi_m_awid}),
    .m_awlen  ({dmc_cfg_axi_awlen,   o_mid_cfg_axi_m_awlen,   o_did_cfg_axi_m_awlen}),
    .m_awaddr ({dmc_cfg_axi_awaddr,
                o_mid_cfg_axi_m_awaddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0],
                o_did_cfg_axi_m_awaddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]}),
    .m_awsize ({dmc_cfg_axi_awsize,  o_mid_cfg_axi_m_awsize,  o_did_cfg_axi_m_awsize}),
    .m_awburst({dmc_cfg_axi_awburst, o_mid_cfg_axi_m_awburst, o_did_cfg_axi_m_awburst}),
    .m_awlock (), // ASO-UNUSED_OUTPUT: not used
    .m_awprot (), // ASO-UNUSED_OUTPUT: not used
    .m_awcache(), // ASO-UNUSED_OUTPUT: not used
    .m_awvalid({dmc_cfg_axi_awvalid, o_mid_cfg_axi_m_awvalid, o_did_cfg_axi_m_awvalid}),
    .m_awready({dmc_cfg_axi_awready, i_mid_cfg_axi_m_awready, i_did_cfg_axi_m_awready}),

    // Read Address Channel
    .m_arid   ({dmc_cfg_axi_arid,    o_mid_cfg_axi_m_arid,    o_did_cfg_axi_m_arid}),
    .m_arlen  ({dmc_cfg_axi_arlen,   o_mid_cfg_axi_m_arlen,   o_did_cfg_axi_m_arlen}),
    .m_araddr ({dmc_cfg_axi_araddr,
                o_mid_cfg_axi_m_araddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0],
                o_did_cfg_axi_m_araddr[AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0]}),
    .m_arsize ({dmc_cfg_axi_arsize,  o_mid_cfg_axi_m_arsize,  o_did_cfg_axi_m_arsize}),
    .m_arburst({dmc_cfg_axi_arburst, o_mid_cfg_axi_m_arburst, o_did_cfg_axi_m_arburst}),
    .m_arlock (), // ASO-UNUSED_OUTPUT: not used
    .m_arprot (), // ASO-UNUSED_OUTPUT: not used
    .m_arcache(), // ASO-UNUSED_OUTPUT: not used
    .m_arvalid({dmc_cfg_axi_arvalid, o_mid_cfg_axi_m_arvalid, o_did_cfg_axi_m_arvalid}),
    .m_arready({dmc_cfg_axi_arready, i_mid_cfg_axi_m_arready, i_did_cfg_axi_m_arready}),

    // Read Resp Channel
    .m_rid   ({dmc_cfg_axi_rid,    i_mid_cfg_axi_m_rid,    i_did_cfg_axi_m_rid}),
    .m_rdata ({dmc_cfg_axi_rdata,  i_mid_cfg_axi_m_rdata,  i_did_cfg_axi_m_rdata}),
    .m_rresp ({dmc_cfg_axi_rresp,  i_mid_cfg_axi_m_rresp,  i_did_cfg_axi_m_rresp}),
    .m_rlast ({dmc_cfg_axi_rlast,  i_mid_cfg_axi_m_rlast,  i_did_cfg_axi_m_rlast}),
    .m_rvalid({dmc_cfg_axi_rvalid, i_mid_cfg_axi_m_rvalid, i_did_cfg_axi_m_rvalid}),
    .m_rready({dmc_cfg_axi_rready, o_mid_cfg_axi_m_rready, o_did_cfg_axi_m_rready}),

    // Write  Data Channel
    .m_wdata ({dmc_cfg_axi_wdata,  o_mid_cfg_axi_m_wdata,  o_did_cfg_axi_m_wdata}),
    .m_wstrb ({dmc_cfg_axi_wstrb,  o_mid_cfg_axi_m_wstrb,  o_did_cfg_axi_m_wstrb}),
    .m_wlast ({dmc_cfg_axi_wlast,  o_mid_cfg_axi_m_wlast,  o_did_cfg_axi_m_wlast}),
    .m_wvalid({dmc_cfg_axi_wvalid, o_mid_cfg_axi_m_wvalid, o_did_cfg_axi_m_wvalid}),
    .m_wready({dmc_cfg_axi_wready, i_mid_cfg_axi_m_wready, i_did_cfg_axi_m_wready}),

    // Write Resp Channel
    .m_bid   ({dmc_cfg_axi_bid,    i_mid_cfg_axi_m_bid,    i_did_cfg_axi_m_bid}),
    .m_bresp ({dmc_cfg_axi_bresp,  i_mid_cfg_axi_m_bresp,  i_did_cfg_axi_m_bresp}),
    .m_bvalid({dmc_cfg_axi_bvalid, i_mid_cfg_axi_m_bvalid, i_did_cfg_axi_m_bvalid}),
    .m_bready({dmc_cfg_axi_bready, o_mid_cfg_axi_m_bready, o_did_cfg_axi_m_bready})
  );
  always_comb o_mid_cfg_axi_m_awaddr[AIC_LT_AXI_ADDR_WIDTH-1:AIC_LT_AXI_LOCAL_ADDR_WIDTH] = '0;
  always_comb o_did_cfg_axi_m_awaddr[AIC_LT_AXI_ADDR_WIDTH-1:AIC_LT_AXI_LOCAL_ADDR_WIDTH] = '0;
  always_comb o_mid_cfg_axi_m_araddr[AIC_LT_AXI_ADDR_WIDTH-1:AIC_LT_AXI_LOCAL_ADDR_WIDTH] = '0;
  always_comb o_did_cfg_axi_m_araddr[AIC_LT_AXI_ADDR_WIDTH-1:AIC_LT_AXI_LOCAL_ADDR_WIDTH] = '0;

endmodule
