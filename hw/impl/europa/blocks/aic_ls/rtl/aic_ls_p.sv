
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
module aic_ls_p
  import aic_common_pkg::*, dmc_pkg::*, token_mgr_mapping_aic_pkg::*, aic_ls_pkg::*;
(
  input  wire i_clk,
  input  wire i_rst_n,

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
  input  logic [     AIC_HT_AXI_CACHE_WIDTH-1:0] i_hp_axi_s_awcache,
  input  logic [      AIC_HT_AXI_PROT_WIDTH-1:0] i_hp_axi_s_awprot,
  input  logic                                   i_hp_axi_s_awlock,
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
  input  logic [     AIC_HT_AXI_CACHE_WIDTH-1:0] i_hp_axi_s_arcache,
  input  logic [      AIC_HT_AXI_PROT_WIDTH-1:0] i_hp_axi_s_arprot,
  input  logic                                   i_hp_axi_s_arlock,
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
  input logic [AIC_CID_WIDTH-1:0]                       i_cid,
  output logic [AIC_DMC_OBS_DW-1:0]                     o_dmc_obs,

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
    /// Margin adjustment for access disturbance margin enhancement (Vmin Feature Control Pins)
  input  logic [2:0] i_rf_adme,
    /// Power up ready negative
  output logic       o_rf_prn,

  input wire  ijtag_tck,
  input wire  ijtag_reset,
  input logic  ijtag_sel,
  input logic  ijtag_ue,
  input logic  ijtag_se,
  input logic  ijtag_ce,
  input logic  ijtag_si,
  output logic  ijtag_so,
  input wire  test_clk,
  input logic  test_mode,
  input logic  edt_update,
  input logic  scan_en,
  input logic [12-1: 0] scan_in,
  output logic [12-1: 0] scan_out,
  input wire  bisr_clk,
  input wire  bisr_reset,
  input logic  bisr_shift_en,
  input logic  bisr_si,
  output logic  bisr_so
);

  localparam bit RVV_REQ_BYPASS = 1'b0;
  localparam bit RVV_RSP_BYPASS = 1'b1;

  logic [DMC_IRQ_W-1:0] wrp_o_dmc_irq, out_o_dmc_irq;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_dmc_irq_del
    if (i_rst_n == 1'b0) begin
      out_o_dmc_irq <= '0;
    end else begin
      if(out_o_dmc_irq != wrp_o_dmc_irq)
        out_o_dmc_irq  <= wrp_o_dmc_irq;
    end
  end
  always_comb o_dmc_irq = out_o_dmc_irq;

    // axi streams:
    // IFD:
    // M IFD0
  logic                        wrp_o_m_ifd0_axis_m_tvalid;
  logic                        wrp_i_m_ifd0_axis_m_tready;
  logic [AIC_PWORD_WIDTH-1:0]  wrp_o_m_ifd0_axis_m_tdata;
  logic                        wrp_o_m_ifd0_axis_m_tlast;
  cc_stream_spill_reg #(.DataWidth(AIC_PWORD_WIDTH+1)) u_m_ifd0_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_m_ifd0_axis_m_tlast, wrp_o_m_ifd0_axis_m_tdata}),
    .i_valid(wrp_o_m_ifd0_axis_m_tvalid),
    .o_ready(wrp_i_m_ifd0_axis_m_tready),
    .o_data({o_m_ifd0_axis_m_tlast, o_m_ifd0_axis_m_tdata}),
    .o_valid(o_m_ifd0_axis_m_tvalid),
    .i_ready(i_m_ifd0_axis_m_tready)
  );
    // M IFD1
  logic                        wrp_o_m_ifd1_axis_m_tvalid;
  logic                        wrp_i_m_ifd1_axis_m_tready;
  logic [AIC_PWORD_WIDTH-1:0]  wrp_o_m_ifd1_axis_m_tdata;
  logic                        wrp_o_m_ifd1_axis_m_tlast;
  cc_stream_spill_reg #(.DataWidth(AIC_PWORD_WIDTH+1)) u_m_ifd1_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_m_ifd1_axis_m_tlast, wrp_o_m_ifd1_axis_m_tdata}),
    .i_valid(wrp_o_m_ifd1_axis_m_tvalid),
    .o_ready(wrp_i_m_ifd1_axis_m_tready),
    .o_data({o_m_ifd1_axis_m_tlast, o_m_ifd1_axis_m_tdata}),
    .o_valid(o_m_ifd1_axis_m_tvalid),
    .i_ready(i_m_ifd1_axis_m_tready)
  );
    // M IFD2
  logic                        wrp_o_m_ifd2_axis_m_tvalid;
  logic                        wrp_i_m_ifd2_axis_m_tready;
  logic [AIC_PWORD_WIDTH-1:0]  wrp_o_m_ifd2_axis_m_tdata;
  logic                        wrp_o_m_ifd2_axis_m_tlast;
  cc_stream_spill_reg #(.DataWidth(AIC_PWORD_WIDTH+1)) u_m_ifd2_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_m_ifd2_axis_m_tlast, wrp_o_m_ifd2_axis_m_tdata}),
    .i_valid(wrp_o_m_ifd2_axis_m_tvalid),
    .o_ready(wrp_i_m_ifd2_axis_m_tready),
    .o_data({o_m_ifd2_axis_m_tlast, o_m_ifd2_axis_m_tdata}),
    .o_valid(o_m_ifd2_axis_m_tvalid),
    .i_ready(i_m_ifd2_axis_m_tready)
  );
    // M IFDW
  logic                        wrp_o_m_ifdw_axis_m_tvalid;
  logic                        wrp_i_m_ifdw_axis_m_tready;
  logic [AIC_PWORD_WIDTH-1:0]  wrp_o_m_ifdw_axis_m_tdata;
  logic                        wrp_o_m_ifdw_axis_m_tlast;
  cc_stream_spill_reg #(.DataWidth(AIC_PWORD_WIDTH+1)) u_m_ifdw_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_m_ifdw_axis_m_tlast, wrp_o_m_ifdw_axis_m_tdata}),
    .i_valid(wrp_o_m_ifdw_axis_m_tvalid),
    .o_ready(wrp_i_m_ifdw_axis_m_tready),
    .o_data({o_m_ifdw_axis_m_tlast, o_m_ifdw_axis_m_tdata}),
    .o_valid(o_m_ifdw_axis_m_tvalid),
    .i_ready(i_m_ifdw_axis_m_tready)
  );
    // D IFD0
  logic                        wrp_o_d_ifd0_axis_m_tvalid;
  logic                        wrp_i_d_ifd0_axis_m_tready;
  logic [AIC_PWORD_WIDTH-1:0]  wrp_o_d_ifd0_axis_m_tdata;
  logic                        wrp_o_d_ifd0_axis_m_tlast;
  cc_stream_spill_reg #(.DataWidth(AIC_PWORD_WIDTH+1)) u_d_ifd0_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_d_ifd0_axis_m_tlast, wrp_o_d_ifd0_axis_m_tdata}),
    .i_valid(wrp_o_d_ifd0_axis_m_tvalid),
    .o_ready(wrp_i_d_ifd0_axis_m_tready),
    .o_data({o_d_ifd0_axis_m_tlast, o_d_ifd0_axis_m_tdata}),
    .o_valid(o_d_ifd0_axis_m_tvalid),
    .i_ready(i_d_ifd0_axis_m_tready)
  );
    // D IFD1
  logic                        wrp_o_d_ifd1_axis_m_tvalid;
  logic                        wrp_i_d_ifd1_axis_m_tready;
  logic [AIC_PWORD_WIDTH-1:0]  wrp_o_d_ifd1_axis_m_tdata;
  logic                        wrp_o_d_ifd1_axis_m_tlast;
  cc_stream_spill_reg #(.DataWidth(AIC_PWORD_WIDTH+1)) u_d_ifd1_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_d_ifd1_axis_m_tlast, wrp_o_d_ifd1_axis_m_tdata}),
    .i_valid(wrp_o_d_ifd1_axis_m_tvalid),
    .o_ready(wrp_i_d_ifd1_axis_m_tready),
    .o_data({o_d_ifd1_axis_m_tlast, o_d_ifd1_axis_m_tdata}),
    .o_valid(o_d_ifd1_axis_m_tvalid),
    .i_ready(i_d_ifd1_axis_m_tready)
  );
    // ODR:
    // M ODR
  logic                        wrp_i_m_odr_axis_s_tvalid;
  logic                        wrp_o_m_odr_axis_s_tready;
  logic [AIC_PWORD_WIDTH-1:0]  wrp_i_m_odr_axis_s_tdata;
  logic                        wrp_i_m_odr_axis_s_tlast;
  cc_stream_spill_reg #(.DataWidth(AIC_PWORD_WIDTH+1)) u_m_odr_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_m_odr_axis_s_tlast, i_m_odr_axis_s_tdata}),
    .i_valid(i_m_odr_axis_s_tvalid),
    .o_ready(o_m_odr_axis_s_tready),
    .o_data({wrp_i_m_odr_axis_s_tlast, wrp_i_m_odr_axis_s_tdata}),
    .o_valid(wrp_i_m_odr_axis_s_tvalid),
    .i_ready(wrp_o_m_odr_axis_s_tready)
  );
    // D ODR:
  logic                        wrp_i_d_odr_axis_s_tvalid;
  logic                        wrp_o_d_odr_axis_s_tready;
  logic [AIC_PWORD_WIDTH-1:0]  wrp_i_d_odr_axis_s_tdata;
  logic                        wrp_i_d_odr_axis_s_tlast;
  cc_stream_spill_reg #(.DataWidth(AIC_PWORD_WIDTH+1)) u_d_odr_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_d_odr_axis_s_tlast, i_d_odr_axis_s_tdata}),
    .i_valid(i_d_odr_axis_s_tvalid),
    .o_ready(o_d_odr_axis_s_tready),
    .o_data({wrp_i_d_odr_axis_s_tlast, wrp_i_d_odr_axis_s_tdata}),
    .o_valid(wrp_i_d_odr_axis_s_tvalid),
    .i_ready(wrp_o_d_odr_axis_s_tready)
  );

  // RVV input
    // 0
  logic                                           wrp_i_rvv_0_req_valid;
  logic                                           wrp_o_rvv_0_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] wrp_i_rvv_0_req_addr;
  logic                                           wrp_i_rvv_0_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] wrp_i_rvv_0_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_i_rvv_0_req_wdata;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortAddrWidth + 1 + cva6v_ai_core_pkg::MemPortBeWidth + cva6v_ai_core_pkg::MemPortWidth),
    .Bypass(RVV_REQ_BYPASS)
  ) u_rvv_0_req_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_rvv_0_req_addr, i_rvv_0_req_we, i_rvv_0_req_be, i_rvv_0_req_wdata}),
    .i_valid(i_rvv_0_req_valid),
    .o_ready(o_rvv_0_req_ready),
    .o_data({wrp_i_rvv_0_req_addr, wrp_i_rvv_0_req_we, wrp_i_rvv_0_req_be, wrp_i_rvv_0_req_wdata}),
    .o_valid(wrp_i_rvv_0_req_valid),
    .i_ready(wrp_o_rvv_0_req_ready)
  );
  logic                                           wrp_o_rvv_0_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_o_rvv_0_res_rdata;
  logic                                           wrp_o_rvv_0_res_err;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortWidth+1),
    .Bypass(RVV_RSP_BYPASS)
  ) u_rvv_0_rsp_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_rvv_0_res_rdata, wrp_o_rvv_0_res_err}),
    .i_valid(wrp_o_rvv_0_res_valid),
    .o_ready(), // ASO-UNUSED_OUTPUT: not used, always ready
    .o_data({o_rvv_0_res_rdata, o_rvv_0_res_err}),
    .o_valid(o_rvv_0_res_valid),
    .i_ready(1'b1)
  );
    // 1
  logic                                           wrp_i_rvv_1_req_valid;
  logic                                           wrp_o_rvv_1_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] wrp_i_rvv_1_req_addr;
  logic                                           wrp_i_rvv_1_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] wrp_i_rvv_1_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_i_rvv_1_req_wdata;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortAddrWidth + 1 + cva6v_ai_core_pkg::MemPortBeWidth + cva6v_ai_core_pkg::MemPortWidth),
    .Bypass(RVV_REQ_BYPASS)
  ) u_rvv_1_req_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_rvv_1_req_addr, i_rvv_1_req_we, i_rvv_1_req_be, i_rvv_1_req_wdata}),
    .i_valid(i_rvv_1_req_valid),
    .o_ready(o_rvv_1_req_ready),
    .o_data({wrp_i_rvv_1_req_addr, wrp_i_rvv_1_req_we, wrp_i_rvv_1_req_be, wrp_i_rvv_1_req_wdata}),
    .o_valid(wrp_i_rvv_1_req_valid),
    .i_ready(wrp_o_rvv_1_req_ready)
  );
  logic                                           wrp_o_rvv_1_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_o_rvv_1_res_rdata;
  logic                                           wrp_o_rvv_1_res_err;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortWidth+1),
    .Bypass(RVV_RSP_BYPASS)
  ) u_rvv_1_rsp_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_rvv_1_res_rdata, wrp_o_rvv_1_res_err}),
    .i_valid(wrp_o_rvv_1_res_valid),
    .o_ready(), // ASO-UNUSED_OUTPUT: not used, always ready
    .o_data({o_rvv_1_res_rdata, o_rvv_1_res_err}),
    .o_valid(o_rvv_1_res_valid),
    .i_ready(1'b1)
  );
    // 2
  logic                                           wrp_i_rvv_2_req_valid;
  logic                                           wrp_o_rvv_2_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] wrp_i_rvv_2_req_addr;
  logic                                           wrp_i_rvv_2_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] wrp_i_rvv_2_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_i_rvv_2_req_wdata;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortAddrWidth + 1 + cva6v_ai_core_pkg::MemPortBeWidth + cva6v_ai_core_pkg::MemPortWidth),
    .Bypass(RVV_REQ_BYPASS)
  ) u_rvv_2_req_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_rvv_2_req_addr, i_rvv_2_req_we, i_rvv_2_req_be, i_rvv_2_req_wdata}),
    .i_valid(i_rvv_2_req_valid),
    .o_ready(o_rvv_2_req_ready),
    .o_data({wrp_i_rvv_2_req_addr, wrp_i_rvv_2_req_we, wrp_i_rvv_2_req_be, wrp_i_rvv_2_req_wdata}),
    .o_valid(wrp_i_rvv_2_req_valid),
    .i_ready(wrp_o_rvv_2_req_ready)
  );
  logic                                           wrp_o_rvv_2_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_o_rvv_2_res_rdata;
  logic                                           wrp_o_rvv_2_res_err;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortWidth+1),
    .Bypass(RVV_RSP_BYPASS)
  ) u_rvv_2_rsp_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_rvv_2_res_rdata, wrp_o_rvv_2_res_err}),
    .i_valid(wrp_o_rvv_2_res_valid),
    .o_ready(), // ASO-UNUSED_OUTPUT: not used, always ready
    .o_data({o_rvv_2_res_rdata, o_rvv_2_res_err}),
    .o_valid(o_rvv_2_res_valid),
    .i_ready(1'b1)
  );
    // 3
  logic                                           wrp_i_rvv_3_req_valid;
  logic                                           wrp_o_rvv_3_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] wrp_i_rvv_3_req_addr;
  logic                                           wrp_i_rvv_3_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] wrp_i_rvv_3_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_i_rvv_3_req_wdata;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortAddrWidth + 1 + cva6v_ai_core_pkg::MemPortBeWidth + cva6v_ai_core_pkg::MemPortWidth),
    .Bypass(RVV_REQ_BYPASS)
  ) u_rvv_3_req_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_rvv_3_req_addr, i_rvv_3_req_we, i_rvv_3_req_be, i_rvv_3_req_wdata}),
    .i_valid(i_rvv_3_req_valid),
    .o_ready(o_rvv_3_req_ready),
    .o_data({wrp_i_rvv_3_req_addr, wrp_i_rvv_3_req_we, wrp_i_rvv_3_req_be, wrp_i_rvv_3_req_wdata}),
    .o_valid(wrp_i_rvv_3_req_valid),
    .i_ready(wrp_o_rvv_3_req_ready)
  );
  logic                                           wrp_o_rvv_3_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_o_rvv_3_res_rdata;
  logic                                           wrp_o_rvv_3_res_err;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortWidth+1),
    .Bypass(RVV_RSP_BYPASS)
  ) u_rvv_3_rsp_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_rvv_3_res_rdata, wrp_o_rvv_3_res_err}),
    .i_valid(wrp_o_rvv_3_res_valid),
    .o_ready(), // ASO-UNUSED_OUTPUT: not used, always ready
    .o_data({o_rvv_3_res_rdata, o_rvv_3_res_err}),
    .o_valid(o_rvv_3_res_valid),
    .i_ready(1'b1)
  );
    // 4
  logic                                           wrp_i_rvv_4_req_valid;
  logic                                           wrp_o_rvv_4_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] wrp_i_rvv_4_req_addr;
  logic                                           wrp_i_rvv_4_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] wrp_i_rvv_4_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_i_rvv_4_req_wdata;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortAddrWidth + 1 + cva6v_ai_core_pkg::MemPortBeWidth + cva6v_ai_core_pkg::MemPortWidth),
    .Bypass(RVV_REQ_BYPASS)
  ) u_rvv_4_req_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_rvv_4_req_addr, i_rvv_4_req_we, i_rvv_4_req_be, i_rvv_4_req_wdata}),
    .i_valid(i_rvv_4_req_valid),
    .o_ready(o_rvv_4_req_ready),
    .o_data({wrp_i_rvv_4_req_addr, wrp_i_rvv_4_req_we, wrp_i_rvv_4_req_be, wrp_i_rvv_4_req_wdata}),
    .o_valid(wrp_i_rvv_4_req_valid),
    .i_ready(wrp_o_rvv_4_req_ready)
  );
  logic                                           wrp_o_rvv_4_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_o_rvv_4_res_rdata;
  logic                                           wrp_o_rvv_4_res_err;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortWidth+1),
    .Bypass(RVV_RSP_BYPASS)
  ) u_rvv_4_rsp_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_rvv_4_res_rdata, wrp_o_rvv_4_res_err}),
    .i_valid(wrp_o_rvv_4_res_valid),
    .o_ready(), // ASO-UNUSED_OUTPUT: not used, always ready
    .o_data({o_rvv_4_res_rdata, o_rvv_4_res_err}),
    .o_valid(o_rvv_4_res_valid),
    .i_ready(1'b1)
  );
    // 5
  logic                                           wrp_i_rvv_5_req_valid;
  logic                                           wrp_o_rvv_5_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] wrp_i_rvv_5_req_addr;
  logic                                           wrp_i_rvv_5_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] wrp_i_rvv_5_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_i_rvv_5_req_wdata;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortAddrWidth + 1 + cva6v_ai_core_pkg::MemPortBeWidth + cva6v_ai_core_pkg::MemPortWidth),
    .Bypass(RVV_REQ_BYPASS)
  ) u_rvv_5_req_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_rvv_5_req_addr, i_rvv_5_req_we, i_rvv_5_req_be, i_rvv_5_req_wdata}),
    .i_valid(i_rvv_5_req_valid),
    .o_ready(o_rvv_5_req_ready),
    .o_data({wrp_i_rvv_5_req_addr, wrp_i_rvv_5_req_we, wrp_i_rvv_5_req_be, wrp_i_rvv_5_req_wdata}),
    .o_valid(wrp_i_rvv_5_req_valid),
    .i_ready(wrp_o_rvv_5_req_ready)
  );
  logic                                           wrp_o_rvv_5_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_o_rvv_5_res_rdata;
  logic                                           wrp_o_rvv_5_res_err;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortWidth+1),
    .Bypass(RVV_RSP_BYPASS)
  ) u_rvv_5_rsp_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_rvv_5_res_rdata, wrp_o_rvv_5_res_err}),
    .i_valid(wrp_o_rvv_5_res_valid),
    .o_ready(), // ASO-UNUSED_OUTPUT: not used, always ready
    .o_data({o_rvv_5_res_rdata, o_rvv_5_res_err}),
    .o_valid(o_rvv_5_res_valid),
    .i_ready(1'b1)
  );
    // 6
  logic                                           wrp_i_rvv_6_req_valid;
  logic                                           wrp_o_rvv_6_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] wrp_i_rvv_6_req_addr;
  logic                                           wrp_i_rvv_6_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] wrp_i_rvv_6_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_i_rvv_6_req_wdata;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortAddrWidth + 1 + cva6v_ai_core_pkg::MemPortBeWidth + cva6v_ai_core_pkg::MemPortWidth),
    .Bypass(RVV_REQ_BYPASS)
  ) u_rvv_6_req_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_rvv_6_req_addr, i_rvv_6_req_we, i_rvv_6_req_be, i_rvv_6_req_wdata}),
    .i_valid(i_rvv_6_req_valid),
    .o_ready(o_rvv_6_req_ready),
    .o_data({wrp_i_rvv_6_req_addr, wrp_i_rvv_6_req_we, wrp_i_rvv_6_req_be, wrp_i_rvv_6_req_wdata}),
    .o_valid(wrp_i_rvv_6_req_valid),
    .i_ready(wrp_o_rvv_6_req_ready)
  );
  logic                                           wrp_o_rvv_6_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_o_rvv_6_res_rdata;
  logic                                           wrp_o_rvv_6_res_err;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortWidth+1),
    .Bypass(RVV_RSP_BYPASS)
  ) u_rvv_6_rsp_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_rvv_6_res_rdata, wrp_o_rvv_6_res_err}),
    .i_valid(wrp_o_rvv_6_res_valid),
    .o_ready(), // ASO-UNUSED_OUTPUT: not used, always ready
    .o_data({o_rvv_6_res_rdata, o_rvv_6_res_err}),
    .o_valid(o_rvv_6_res_valid),
    .i_ready(1'b1)
  );
    // 7
  logic                                           wrp_i_rvv_7_req_valid;
  logic                                           wrp_o_rvv_7_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] wrp_i_rvv_7_req_addr;
  logic                                           wrp_i_rvv_7_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] wrp_i_rvv_7_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_i_rvv_7_req_wdata;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortAddrWidth + 1 + cva6v_ai_core_pkg::MemPortBeWidth + cva6v_ai_core_pkg::MemPortWidth),
    .Bypass(RVV_REQ_BYPASS)
  ) u_rvv_7_req_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({i_rvv_7_req_addr, i_rvv_7_req_we, i_rvv_7_req_be, i_rvv_7_req_wdata}),
    .i_valid(i_rvv_7_req_valid),
    .o_ready(o_rvv_7_req_ready),
    .o_data({wrp_i_rvv_7_req_addr, wrp_i_rvv_7_req_we, wrp_i_rvv_7_req_be, wrp_i_rvv_7_req_wdata}),
    .o_valid(wrp_i_rvv_7_req_valid),
    .i_ready(wrp_o_rvv_7_req_ready)
  );
  logic                                           wrp_o_rvv_7_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] wrp_o_rvv_7_res_rdata;
  logic                                           wrp_o_rvv_7_res_err;
  cc_stream_spill_reg #(
    .DataWidth(cva6v_ai_core_pkg::MemPortWidth+1),
    .Bypass(RVV_RSP_BYPASS)
  ) u_rvv_7_rsp_spill (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data({wrp_o_rvv_7_res_rdata, wrp_o_rvv_7_res_err}),
    .i_valid(wrp_o_rvv_7_res_valid),
    .o_ready(), // ASO-UNUSED_OUTPUT: not used, always ready
    .o_data({o_rvv_7_res_rdata, o_rvv_7_res_err}),
    .o_valid(o_rvv_7_res_valid),
    .i_ready(1'b1)
  );

  /////////////// Token ////////////
    // IFD:
    // M IFD0
  logic [DMC_TOKENS_PROD-1:0] wrp_o_m_ifd0_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] wrp_i_m_ifd0_tok_prod_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_PROD)) u_tok_m_ifd0_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_m_ifd0_tok_prod_vld),
    .o_s_ready(wrp_i_m_ifd0_tok_prod_rdy),
    .o_m_valid(o_m_ifd0_tok_prod_vld),
    .i_m_ready(i_m_ifd0_tok_prod_rdy)
  );
  logic [DMC_TOKENS_CONS-1:0] wrp_i_m_ifd0_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] wrp_o_m_ifd0_tok_cons_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_CONS)) u_tok_m_ifd0_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_m_ifd0_tok_cons_vld),
    .o_s_ready(o_m_ifd0_tok_cons_rdy),
    .o_m_valid(wrp_i_m_ifd0_tok_cons_vld),
    .i_m_ready(wrp_o_m_ifd0_tok_cons_rdy)
  );

    // M IFD1
  logic [DMC_TOKENS_PROD-1:0] wrp_o_m_ifd1_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] wrp_i_m_ifd1_tok_prod_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_PROD)) u_tok_m_ifd1_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_m_ifd1_tok_prod_vld),
    .o_s_ready(wrp_i_m_ifd1_tok_prod_rdy),
    .o_m_valid(o_m_ifd1_tok_prod_vld),
    .i_m_ready(i_m_ifd1_tok_prod_rdy)
  );
  logic [DMC_TOKENS_CONS-1:0] wrp_i_m_ifd1_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] wrp_o_m_ifd1_tok_cons_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_CONS)) u_tok_m_ifd1_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_m_ifd1_tok_cons_vld),
    .o_s_ready(o_m_ifd1_tok_cons_rdy),
    .o_m_valid(wrp_i_m_ifd1_tok_cons_vld),
    .i_m_ready(wrp_o_m_ifd1_tok_cons_rdy)
  );

    // M IFD2
  logic [DMC_TOKENS_PROD-1:0] wrp_o_m_ifd2_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] wrp_i_m_ifd2_tok_prod_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_PROD)) u_tok_m_ifd2_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_m_ifd2_tok_prod_vld),
    .o_s_ready(wrp_i_m_ifd2_tok_prod_rdy),
    .o_m_valid(o_m_ifd2_tok_prod_vld),
    .i_m_ready(i_m_ifd2_tok_prod_rdy)
  );
  logic [DMC_TOKENS_CONS-1:0] wrp_i_m_ifd2_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] wrp_o_m_ifd2_tok_cons_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_CONS)) u_tok_m_ifd2_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_m_ifd2_tok_cons_vld),
    .o_s_ready(o_m_ifd2_tok_cons_rdy),
    .o_m_valid(wrp_i_m_ifd2_tok_cons_vld),
    .i_m_ready(wrp_o_m_ifd2_tok_cons_rdy)
  );
    // M IFDW
  logic [DMC_TOKENS_PROD-1:0] wrp_o_m_ifdw_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] wrp_i_m_ifdw_tok_prod_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_PROD)) u_tok_m_ifdw_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_m_ifdw_tok_prod_vld),
    .o_s_ready(wrp_i_m_ifdw_tok_prod_rdy),
    .o_m_valid(o_m_ifdw_tok_prod_vld),
    .i_m_ready(i_m_ifdw_tok_prod_rdy)
  );
  logic [DMC_TOKENS_CONS-1:0] wrp_i_m_ifdw_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] wrp_o_m_ifdw_tok_cons_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_CONS)) u_tok_m_ifdw_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_m_ifdw_tok_cons_vld),
    .o_s_ready(o_m_ifdw_tok_cons_rdy),
    .o_m_valid(wrp_i_m_ifdw_tok_cons_vld),
    .i_m_ready(wrp_o_m_ifdw_tok_cons_rdy)
  );
    // D IFD0
  logic [DMC_TOKENS_PROD-1:0] wrp_o_d_ifd0_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] wrp_i_d_ifd0_tok_prod_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_PROD)) u_tok_d_ifd0_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_d_ifd0_tok_prod_vld),
    .o_s_ready(wrp_i_d_ifd0_tok_prod_rdy),
    .o_m_valid(o_d_ifd0_tok_prod_vld),
    .i_m_ready(i_d_ifd0_tok_prod_rdy)
  );
  logic [DMC_TOKENS_CONS-1:0] wrp_i_d_ifd0_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] wrp_o_d_ifd0_tok_cons_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_CONS)) u_tok_d_ifd0_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_d_ifd0_tok_cons_vld),
    .o_s_ready(o_d_ifd0_tok_cons_rdy),
    .o_m_valid(wrp_i_d_ifd0_tok_cons_vld),
    .i_m_ready(wrp_o_d_ifd0_tok_cons_rdy)
  );
    // D IFD1
  logic [DMC_TOKENS_PROD-1:0] wrp_o_d_ifd1_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] wrp_i_d_ifd1_tok_prod_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_PROD)) u_tok_d_ifd1_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_d_ifd1_tok_prod_vld),
    .o_s_ready(wrp_i_d_ifd1_tok_prod_rdy),
    .o_m_valid(o_d_ifd1_tok_prod_vld),
    .i_m_ready(i_d_ifd1_tok_prod_rdy)
  );
  logic [DMC_TOKENS_CONS-1:0] wrp_i_d_ifd1_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] wrp_o_d_ifd1_tok_cons_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_CONS)) u_tok_d_ifd1_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_d_ifd1_tok_cons_vld),
    .o_s_ready(o_d_ifd1_tok_cons_rdy),
    .o_m_valid(wrp_i_d_ifd1_tok_cons_vld),
    .i_m_ready(wrp_o_d_ifd1_tok_cons_rdy)
  );
    // ODR:
    // M ODR
  logic [DMC_TOKENS_PROD-1:0] wrp_o_m_odr_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] wrp_i_m_odr_tok_prod_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_PROD)) u_tok_m_odr_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_m_odr_tok_prod_vld),
    .o_s_ready(wrp_i_m_odr_tok_prod_rdy),
    .o_m_valid(o_m_odr_tok_prod_vld),
    .i_m_ready(i_m_odr_tok_prod_rdy)
  );
  logic [DMC_TOKENS_CONS-1:0] wrp_i_m_odr_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] wrp_o_m_odr_tok_cons_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_CONS)) u_tok_m_odr_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_m_odr_tok_cons_vld),
    .o_s_ready(o_m_odr_tok_cons_rdy),
    .o_m_valid(wrp_i_m_odr_tok_cons_vld),
    .i_m_ready(wrp_o_m_odr_tok_cons_rdy)
  );
    // D ODR:
  logic [DMC_TOKENS_PROD-1:0] wrp_o_d_odr_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] wrp_i_d_odr_tok_prod_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_PROD)) u_tok_d_odr_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_d_odr_tok_prod_vld),
    .o_s_ready(wrp_i_d_odr_tok_prod_rdy),
    .o_m_valid(o_d_odr_tok_prod_vld),
    .i_m_ready(i_d_odr_tok_prod_rdy)
  );
  logic [DMC_TOKENS_CONS-1:0] wrp_i_d_odr_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] wrp_o_d_odr_tok_cons_rdy;
  token_cut #(.NumTokens(DMC_TOKENS_CONS)) u_tok_d_odr_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_d_odr_tok_cons_vld),
    .o_s_ready(o_d_odr_tok_cons_rdy),
    .o_m_valid(wrp_i_d_odr_tok_cons_vld),
    .i_m_ready(wrp_o_d_odr_tok_cons_rdy)
  );

  ///// Timestamp:
  logic [DMC_NR_IFDS_ODRS-1:0] wrp_o_dmc_ts_start, out_o_dmc_ts_start;
  logic [DMC_NR_IFDS_ODRS-1:0] wrp_o_dmc_ts_end, out_o_dmc_ts_end;
  ///// ACD sync:
  logic [DMC_NR_IFDS_ODRS-1:0] wrp_o_dmc_acd_sync, out_o_dmc_acd_sync;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_dmc_ts_sync_del
    if (i_rst_n == 1'b0) begin
      out_o_dmc_ts_start <= '0;
      out_o_dmc_ts_end <= '0;
      out_o_dmc_acd_sync <= '0;
    end else begin
      if(out_o_dmc_ts_start != wrp_o_dmc_ts_start)
        out_o_dmc_ts_start  <= wrp_o_dmc_ts_start;
      if(out_o_dmc_ts_end != wrp_o_dmc_ts_end)
        out_o_dmc_ts_end    <= wrp_o_dmc_ts_end;
      if(out_o_dmc_acd_sync != wrp_o_dmc_acd_sync)
        out_o_dmc_acd_sync  <= wrp_o_dmc_acd_sync;
    end
  end
  always_comb o_dmc_ts_start = out_o_dmc_ts_start;
  always_comb o_dmc_ts_end   = out_o_dmc_ts_end;
  always_comb o_dmc_acd_sync = out_o_dmc_acd_sync;

  // A2M:
  //------------------------------------------------------
  // AXI address channels
  typedef struct packed {
    logic [      AIC_HT_AXI_ADDR_WIDTH-1:0] addr;
    logic [      AIC_HT_AXI_S_ID_WIDTH-1:0] id;
    logic [       AIC_HT_AXI_LEN_WIDTH-1:0] len;
    logic [      AIC_HT_AXI_SIZE_WIDTH-1:0] size;
    logic [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] burst;
    logic [     AIC_HT_AXI_CACHE_WIDTH-1:0] cache;
    logic [      AIC_HT_AXI_PROT_WIDTH-1:0] prot;
    logic                                   lock;
  } aic_ls_hp_axi_addr_t;

  aic_ls_hp_axi_addr_t wrp_i_hp_axi_s_aw, in_i_hp_axi_s_aw;
  logic                wrp_i_hp_axi_s_awvalid;
  logic                wrp_o_hp_axi_s_awready;
  aic_ls_hp_axi_addr_t wrp_i_hp_axi_s_ar, in_i_hp_axi_s_ar;
  logic                wrp_i_hp_axi_s_arvalid;
  logic                wrp_o_hp_axi_s_arready;

  // AXI write data channel
  typedef struct packed {
    logic                                   last;
    logic [     AIC_HT_AXI_WSTRB_WIDTH-1:0] strb;
    logic [      AIC_HT_AXI_DATA_WIDTH-1:0] data;
  } aic_ls_hp_axi_wdata_t;

  aic_ls_hp_axi_wdata_t wrp_i_hp_axi_s_wdata, in_i_hp_axi_s_wdata;
  logic                 wrp_i_hp_axi_s_wvalid;
  logic                 wrp_o_hp_axi_s_wready;

  // AXI write response channel
  typedef struct packed {
    logic [      AIC_HT_AXI_S_ID_WIDTH-1:0] id;
    logic [      AIC_HT_AXI_RESP_WIDTH-1:0] resp;
  } aic_ls_hp_axi_bresp_t;

  aic_ls_hp_axi_bresp_t wrp_o_hp_axi_s_bresp, out_o_hp_axi_s_bresp;
  logic                 wrp_o_hp_axi_s_bvalid;
  logic                 wrp_i_hp_axi_s_bready;

  // AXI read data/response channel
  typedef struct packed {
    logic                                   last;
    logic [      AIC_HT_AXI_S_ID_WIDTH-1:0] id;
    logic [      AIC_HT_AXI_DATA_WIDTH-1:0] data;
    logic [      AIC_HT_AXI_RESP_WIDTH-1:0] resp;
  } aic_ls_hp_axi_rdata_t;

  aic_ls_hp_axi_rdata_t wrp_o_hp_axi_s_rdata, out_o_hp_axi_s_rdata;
  logic                 wrp_o_hp_axi_s_rvalid;
  logic                 wrp_i_hp_axi_s_rready;

  always_comb in_i_hp_axi_s_aw = aic_ls_hp_axi_addr_t'{
    addr:   i_hp_axi_s_awaddr,
    id:     i_hp_axi_s_awid,
    len:    i_hp_axi_s_awlen,
    size:   i_hp_axi_s_awsize,
    burst:  i_hp_axi_s_awburst,
    cache:  i_hp_axi_s_awcache,
    prot:   i_hp_axi_s_awprot,
    lock:   i_hp_axi_s_awlock
  };
  always_comb in_i_hp_axi_s_wdata = aic_ls_hp_axi_wdata_t'{
      last:   i_hp_axi_s_wlast,
      strb:   i_hp_axi_s_wstrb,
      data:   i_hp_axi_s_wdata
  };
  always_comb in_i_hp_axi_s_ar = aic_ls_hp_axi_addr_t'{
      addr:   i_hp_axi_s_araddr,
      id:     i_hp_axi_s_arid,
      len:    i_hp_axi_s_arlen,
      size:   i_hp_axi_s_arsize,
      burst:  i_hp_axi_s_arburst,
      cache:  i_hp_axi_s_arcache,
      prot:   i_hp_axi_s_arprot,
      lock:   i_hp_axi_s_arlock
    };
  axe_axi_multicut #(
    .NumCuts  (1), // Number of cuts.
    // AXI channel structs
    .axi_aw_t (aic_ls_hp_axi_addr_t),
    .axi_w_t  (aic_ls_hp_axi_wdata_t),
    .axi_b_t  (aic_ls_hp_axi_bresp_t),
    .axi_ar_t (aic_ls_hp_axi_addr_t),
    .axi_r_t  (aic_ls_hp_axi_rdata_t)
  ) u_axi_hp_cut (
    .i_clk,
    .i_rst_n,
    // External AXI Interface
    .i_axi_s_aw      (in_i_hp_axi_s_aw),
    .i_axi_s_aw_valid(i_hp_axi_s_awvalid),
    .o_axi_s_aw_ready(o_hp_axi_s_awready),
    .i_axi_s_w       (in_i_hp_axi_s_wdata),
    .i_axi_s_w_valid (i_hp_axi_s_wvalid),
    .o_axi_s_w_ready (o_hp_axi_s_wready),
    .o_axi_s_b       (out_o_hp_axi_s_bresp),
    .o_axi_s_b_valid (o_hp_axi_s_bvalid),
    .i_axi_s_b_ready (i_hp_axi_s_bready),
    .i_axi_s_ar      (in_i_hp_axi_s_ar),
    .i_axi_s_ar_valid(i_hp_axi_s_arvalid),
    .o_axi_s_ar_ready(o_hp_axi_s_arready),
    .o_axi_s_r       (out_o_hp_axi_s_rdata),
    .o_axi_s_r_valid (o_hp_axi_s_rvalid),
    .i_axi_s_r_ready (i_hp_axi_s_rready),
    // Internal AXI Interface
    .o_axi_m_aw      (wrp_i_hp_axi_s_aw),
    .o_axi_m_aw_valid(wrp_i_hp_axi_s_awvalid),
    .i_axi_m_aw_ready(wrp_o_hp_axi_s_awready),
    .o_axi_m_w       (wrp_i_hp_axi_s_wdata),
    .o_axi_m_w_valid (wrp_i_hp_axi_s_wvalid),
    .i_axi_m_w_ready (wrp_o_hp_axi_s_wready),
    .i_axi_m_b       (wrp_o_hp_axi_s_bresp),
    .i_axi_m_b_valid (wrp_o_hp_axi_s_bvalid),
    .o_axi_m_b_ready (wrp_i_hp_axi_s_bready),
    .o_axi_m_ar      (wrp_i_hp_axi_s_ar),
    .o_axi_m_ar_valid(wrp_i_hp_axi_s_arvalid),
    .i_axi_m_ar_ready(wrp_o_hp_axi_s_arready),
    .i_axi_m_r       (wrp_o_hp_axi_s_rdata),
    .i_axi_m_r_valid (wrp_o_hp_axi_s_rvalid),
    .o_axi_m_r_ready (wrp_i_hp_axi_s_rready)
  );
  always_comb o_hp_axi_s_bid    = out_o_hp_axi_s_bresp.id;
  always_comb o_hp_axi_s_bresp  = out_o_hp_axi_s_bresp.resp;
  always_comb o_hp_axi_s_rlast  = out_o_hp_axi_s_rdata.last;
  always_comb o_hp_axi_s_rid    = out_o_hp_axi_s_rdata.id;
  always_comb o_hp_axi_s_rdata  = out_o_hp_axi_s_rdata.data;
  always_comb o_hp_axi_s_rresp  = out_o_hp_axi_s_rdata.resp;

  // CFG:
  //------------------------------------------------------
  // AXI address channels
  typedef struct packed {
    logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] addr;
    logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] id;
    logic [       AIC_LT_AXI_LEN_WIDTH-1:0] len;
    logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] size;
    logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] burst;
  } aic_ls_lp_axi_addr_t;

  aic_ls_lp_axi_addr_t wrp_i_cfg_axi_s_aw, in_i_cfg_axi_s_aw;
  logic                wrp_i_cfg_axi_s_awvalid;
  logic                wrp_o_cfg_axi_s_awready;
  aic_ls_lp_axi_addr_t wrp_i_cfg_axi_s_ar, in_i_cfg_axi_s_ar;
  logic                wrp_i_cfg_axi_s_arvalid;
  logic                wrp_o_cfg_axi_s_arready;

  // AXI write data channel
  typedef struct packed {
    logic                                   last;
    logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] strb;
    logic [      AIC_LT_AXI_DATA_WIDTH-1:0] data;
  } aic_ls_lp_axi_wdata_t;

  aic_ls_lp_axi_wdata_t wrp_i_cfg_axi_s_wdata, in_i_cfg_axi_s_wdata;
  logic                 wrp_i_cfg_axi_s_wvalid;
  logic                 wrp_o_cfg_axi_s_wready;

  // AXI write response channel
  typedef struct packed {
    logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] id;
    logic [      AIC_LT_AXI_RESP_WIDTH-1:0] resp;
  } aic_ls_lp_axi_bresp_t;

  aic_ls_lp_axi_bresp_t wrp_o_cfg_axi_s_bresp, out_o_cfg_axi_s_bresp;
  logic                 wrp_o_cfg_axi_s_bvalid;
  logic                 wrp_i_cfg_axi_s_bready;

  // AXI read data/response channel
  typedef struct packed {
    logic                                   last;
    logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] id;
    logic [      AIC_LT_AXI_DATA_WIDTH-1:0] data;
    logic [      AIC_LT_AXI_RESP_WIDTH-1:0] resp;
  } aic_ls_lp_axi_rdata_t;

  aic_ls_lp_axi_rdata_t wrp_o_cfg_axi_s_rdata, out_o_cfg_axi_s_rdata;
  logic                 wrp_o_cfg_axi_s_rvalid;
  logic                 wrp_i_cfg_axi_s_rready;

  always_comb in_i_cfg_axi_s_aw = aic_ls_lp_axi_addr_t'{
      addr:   i_cfg_axi_s_awaddr,
      id:     i_cfg_axi_s_awid,
      len:    i_cfg_axi_s_awlen,
      size:   i_cfg_axi_s_awsize,
      burst:  i_cfg_axi_s_awburst
  };
  always_comb in_i_cfg_axi_s_wdata = aic_ls_lp_axi_wdata_t'{
      last:   i_cfg_axi_s_wlast,
      strb:   i_cfg_axi_s_wstrb,
      data:   i_cfg_axi_s_wdata
  };
  always_comb in_i_cfg_axi_s_ar = aic_ls_lp_axi_addr_t'{
      addr:   i_cfg_axi_s_araddr,
      id:     i_cfg_axi_s_arid,
      len:    i_cfg_axi_s_arlen,
      size:   i_cfg_axi_s_arsize,
      burst:  i_cfg_axi_s_arburst
  };
  axe_axi_multicut #(
    .NumCuts  (1), // Number of cuts.
    // AXI channel structs
    .axi_aw_t (aic_ls_lp_axi_addr_t),
    .axi_w_t  (aic_ls_lp_axi_wdata_t),
    .axi_b_t  (aic_ls_lp_axi_bresp_t),
    .axi_ar_t (aic_ls_lp_axi_addr_t),
    .axi_r_t  (aic_ls_lp_axi_rdata_t)
  ) u_axi_cfg_cut (
    .i_clk,
    .i_rst_n,
    // External AXI Interface
    .i_axi_s_aw      (in_i_cfg_axi_s_aw),
    .i_axi_s_aw_valid(i_cfg_axi_s_awvalid),
    .o_axi_s_aw_ready(o_cfg_axi_s_awready),
    .i_axi_s_w       (in_i_cfg_axi_s_wdata),
    .i_axi_s_w_valid (i_cfg_axi_s_wvalid),
    .o_axi_s_w_ready (o_cfg_axi_s_wready),
    .o_axi_s_b       (out_o_cfg_axi_s_bresp),
    .o_axi_s_b_valid (o_cfg_axi_s_bvalid),
    .i_axi_s_b_ready (i_cfg_axi_s_bready),
    .i_axi_s_ar      (in_i_cfg_axi_s_ar),
    .i_axi_s_ar_valid(i_cfg_axi_s_arvalid),
    .o_axi_s_ar_ready(o_cfg_axi_s_arready),
    .o_axi_s_r       (out_o_cfg_axi_s_rdata),
    .o_axi_s_r_valid (o_cfg_axi_s_rvalid),
    .i_axi_s_r_ready (i_cfg_axi_s_rready),
    // Internal AXI Interface
    .o_axi_m_aw      (wrp_i_cfg_axi_s_aw),
    .o_axi_m_aw_valid(wrp_i_cfg_axi_s_awvalid),
    .i_axi_m_aw_ready(wrp_o_cfg_axi_s_awready),
    .o_axi_m_w       (wrp_i_cfg_axi_s_wdata),
    .o_axi_m_w_valid (wrp_i_cfg_axi_s_wvalid),
    .i_axi_m_w_ready (wrp_o_cfg_axi_s_wready),
    .i_axi_m_b       (wrp_o_cfg_axi_s_bresp),
    .i_axi_m_b_valid (wrp_o_cfg_axi_s_bvalid),
    .o_axi_m_b_ready (wrp_i_cfg_axi_s_bready),
    .o_axi_m_ar      (wrp_i_cfg_axi_s_ar),
    .o_axi_m_ar_valid(wrp_i_cfg_axi_s_arvalid),
    .i_axi_m_ar_ready(wrp_o_cfg_axi_s_arready),
    .i_axi_m_r       (wrp_o_cfg_axi_s_rdata),
    .i_axi_m_r_valid (wrp_o_cfg_axi_s_rvalid),
    .o_axi_m_r_ready (wrp_i_cfg_axi_s_rready)
  );
  always_comb o_cfg_axi_s_bid    = out_o_cfg_axi_s_bresp.id;
  always_comb o_cfg_axi_s_bresp  = out_o_cfg_axi_s_bresp.resp;
  always_comb o_cfg_axi_s_rlast  = out_o_cfg_axi_s_rdata.last;
  always_comb o_cfg_axi_s_rid    = out_o_cfg_axi_s_rdata.id;
  always_comb o_cfg_axi_s_rdata  = out_o_cfg_axi_s_rdata.data;
  always_comb o_cfg_axi_s_rresp  = out_o_cfg_axi_s_rdata.resp;

  // Sidebands:
  logic [AIC_CID_WIDTH-1:0]                      wrp_i_cid;
  logic [AIC_DMC_OBS_DW-1:0]                     wrp_o_dmc_obs, out_o_dmc_obs;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_dmc_obs_del
    if (i_rst_n == 1'b0) begin
      out_o_dmc_obs <= '0;
    end else begin
      if(out_o_dmc_obs != wrp_o_dmc_obs)
        out_o_dmc_obs  <= wrp_o_dmc_obs;
    end
  end
  always_comb o_dmc_obs = out_o_dmc_obs;

  ////////////////////////////////////////////////
  //////// MID feedthrough
  /////////////// Token ////////////
  //// MVM EXE:
    // MID2LS:
  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] wrp_i_mid_mvm_exe_tok_prod_vld;
  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] wrp_o_mid_mvm_exe_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_MVMEXE_NR_TOK_PROD)) u_tok_i_mid_mvm_exe_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_mid_mvm_exe_tok_prod_vld),
    .o_s_ready(o_mid_mvm_exe_tok_prod_rdy),
    .o_m_valid(wrp_i_mid_mvm_exe_tok_prod_vld),
    .i_m_ready(wrp_o_mid_mvm_exe_tok_prod_rdy)
  );
  logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] wrp_o_mid_mvm_exe_tok_cons_vld;
  logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] wrp_i_mid_mvm_exe_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_MVMEXE_NR_TOK_CONS)) u_tok_o_mid_mvm_exe_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_mid_mvm_exe_tok_cons_vld),
    .o_s_ready(wrp_i_mid_mvm_exe_tok_cons_rdy),
    .o_m_valid(o_mid_mvm_exe_tok_cons_vld),
    .i_m_ready(i_mid_mvm_exe_tok_cons_rdy)
  );
    // LS2AIC:
  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] wrp_o_mid_mvm_exe_tok_prod_vld;
  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] wrp_i_mid_mvm_exe_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_MVMEXE_NR_TOK_PROD)) u_tok_o_mid_mvm_exe_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_mid_mvm_exe_tok_prod_vld),
    .o_s_ready(wrp_i_mid_mvm_exe_tok_prod_rdy),
    .o_m_valid(o_mid_mvm_exe_tok_prod_vld),
    .i_m_ready(i_mid_mvm_exe_tok_prod_rdy)
  );
  logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] wrp_i_mid_mvm_exe_tok_cons_vld;
  logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] wrp_o_mid_mvm_exe_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_MVMEXE_NR_TOK_CONS)) u_tok_i_mid_mvm_exe_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_mid_mvm_exe_tok_cons_vld),
    .o_s_ready(o_mid_mvm_exe_tok_cons_rdy),
    .o_m_valid(wrp_i_mid_mvm_exe_tok_cons_vld),
    .i_m_ready(wrp_o_mid_mvm_exe_tok_cons_rdy)
  );
  //// MVM PRG:
    // MID2LS:
  logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] wrp_i_mid_mvm_prg_tok_prod_vld;
  logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] wrp_o_mid_mvm_prg_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_MVMPRG_NR_TOK_PROD)) u_tok_i_mid_mvm_prg_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_mid_mvm_prg_tok_prod_vld),
    .o_s_ready(o_mid_mvm_prg_tok_prod_rdy),
    .o_m_valid(wrp_i_mid_mvm_prg_tok_prod_vld),
    .i_m_ready(wrp_o_mid_mvm_prg_tok_prod_rdy)
  );
  logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] wrp_o_mid_mvm_prg_tok_cons_vld;
  logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] wrp_i_mid_mvm_prg_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_MVMPRG_NR_TOK_CONS)) u_tok_o_mid_mvm_prg_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_mid_mvm_prg_tok_cons_vld),
    .o_s_ready(wrp_i_mid_mvm_prg_tok_cons_rdy),
    .o_m_valid(o_mid_mvm_prg_tok_cons_vld),
    .i_m_ready(i_mid_mvm_prg_tok_cons_rdy)
  );
    // LS2AIC:
  logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] wrp_o_mid_mvm_prg_tok_prod_vld;
  logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] wrp_i_mid_mvm_prg_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_MVMPRG_NR_TOK_PROD)) u_tok_o_mid_mvm_prg_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_mid_mvm_prg_tok_prod_vld),
    .o_s_ready(wrp_i_mid_mvm_prg_tok_prod_rdy),
    .o_m_valid(o_mid_mvm_prg_tok_prod_vld),
    .i_m_ready(i_mid_mvm_prg_tok_prod_rdy)
  );
  logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] wrp_i_mid_mvm_prg_tok_cons_vld;
  logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] wrp_o_mid_mvm_prg_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_MVMPRG_NR_TOK_CONS)) u_tok_i_mid_mvm_prg_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_mid_mvm_prg_tok_cons_vld),
    .o_s_ready(o_mid_mvm_prg_tok_cons_rdy),
    .o_m_valid(wrp_i_mid_mvm_prg_tok_cons_vld),
    .i_m_ready(wrp_o_mid_mvm_prg_tok_cons_rdy)
  );
  //// IAU:
    // MID2LS:
  logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] wrp_i_mid_iau_tok_prod_vld;
  logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] wrp_o_mid_iau_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_IAU_NR_TOK_PROD)) u_tok_i_mid_iau_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_mid_iau_tok_prod_vld),
    .o_s_ready(o_mid_iau_tok_prod_rdy),
    .o_m_valid(wrp_i_mid_iau_tok_prod_vld),
    .i_m_ready(wrp_o_mid_iau_tok_prod_rdy)
  );
  logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] wrp_o_mid_iau_tok_cons_vld;
  logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] wrp_i_mid_iau_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_IAU_NR_TOK_CONS)) u_tok_o_mid_iau_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_mid_iau_tok_cons_vld),
    .o_s_ready(wrp_i_mid_iau_tok_cons_rdy),
    .o_m_valid(o_mid_iau_tok_cons_vld),
    .i_m_ready(i_mid_iau_tok_cons_rdy)
  );
    // LS2AIC:
  logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] wrp_o_mid_iau_tok_prod_vld;
  logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] wrp_i_mid_iau_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_IAU_NR_TOK_PROD)) u_tok_o_mid_iau_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_mid_iau_tok_prod_vld),
    .o_s_ready(wrp_i_mid_iau_tok_prod_rdy),
    .o_m_valid(o_mid_iau_tok_prod_vld),
    .i_m_ready(i_mid_iau_tok_prod_rdy)
  );
  logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] wrp_i_mid_iau_tok_cons_vld;
  logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] wrp_o_mid_iau_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_IAU_NR_TOK_CONS)) u_tok_i_mid_iau_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_mid_iau_tok_cons_vld),
    .o_s_ready(o_mid_iau_tok_cons_rdy),
    .o_m_valid(wrp_i_mid_iau_tok_cons_vld),
    .i_m_ready(wrp_o_mid_iau_tok_cons_rdy)
  );
  //// DPU:
    // MID2LS:
  logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] wrp_i_mid_dpu_tok_prod_vld;
  logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] wrp_o_mid_dpu_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_DPU_NR_TOK_PROD)) u_tok_i_mid_dpu_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_mid_dpu_tok_prod_vld),
    .o_s_ready(o_mid_dpu_tok_prod_rdy),
    .o_m_valid(wrp_i_mid_dpu_tok_prod_vld),
    .i_m_ready(wrp_o_mid_dpu_tok_prod_rdy)
  );
  logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] wrp_o_mid_dpu_tok_cons_vld;
  logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] wrp_i_mid_dpu_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_DPU_NR_TOK_CONS)) u_tok_o_mid_dpu_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_mid_dpu_tok_cons_vld),
    .o_s_ready(wrp_i_mid_dpu_tok_cons_rdy),
    .o_m_valid(o_mid_dpu_tok_cons_vld),
    .i_m_ready(i_mid_dpu_tok_cons_rdy)
  );
    // LS2AIC:
  logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] wrp_o_mid_dpu_tok_prod_vld;
  logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] wrp_i_mid_dpu_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_DPU_NR_TOK_PROD)) u_tok_o_mid_dpu_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_mid_dpu_tok_prod_vld),
    .o_s_ready(wrp_i_mid_dpu_tok_prod_rdy),
    .o_m_valid(o_mid_dpu_tok_prod_vld),
    .i_m_ready(i_mid_dpu_tok_prod_rdy)
  );
  logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] wrp_i_mid_dpu_tok_cons_vld;
  logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] wrp_o_mid_dpu_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_M_DPU_NR_TOK_CONS)) u_tok_i_mid_dpu_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_mid_dpu_tok_cons_vld),
    .o_s_ready(o_mid_dpu_tok_cons_rdy),
    .o_m_valid(wrp_i_mid_dpu_tok_cons_vld),
    .i_m_ready(wrp_o_mid_dpu_tok_cons_rdy)
  );

  /////////////// IRQ ////////////
  logic [aic_mid_pkg::NUM_IRQS-1:0] wrp_i_mid_irq;
  logic [aic_mid_pkg::NUM_IRQS-1:0] wrp_o_mid_irq, out_o_mid_irq;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_mid_irq_del
    if (i_rst_n == 1'b0) begin
      wrp_i_mid_irq <= '0;
      out_o_mid_irq <= '0;
    end else begin
      if(wrp_i_mid_irq != i_mid_irq)
        wrp_i_mid_irq  <= i_mid_irq;
      if(out_o_mid_irq != wrp_o_mid_irq)
        out_o_mid_irq    <= wrp_o_mid_irq;
    end
  end
  always_comb o_mid_irq = out_o_mid_irq;

  /////////////// OBS ////////////
    // MID2LS:
  logic [AIC_DEV_OBS_DW-1:0]  wrp_i_mid_mvm_exe_obs;
  logic [AIC_DEV_OBS_DW-1:0]  wrp_i_mid_mvm_prg_obs;
  logic [AIC_DEV_OBS_DW-1:0]  wrp_i_mid_iau_obs;
  logic [AIC_DEV_OBS_DW-1:0]  wrp_i_mid_dpu_obs;
  logic [AIC_TU_OBS_DW-1:0]   wrp_i_mid_tu_obs;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_i_mid_obs_del
    if (i_rst_n == 1'b0) begin
      wrp_i_mid_mvm_exe_obs <= '0;
      wrp_i_mid_mvm_prg_obs <= '0;
      wrp_i_mid_iau_obs <= '0;
      wrp_i_mid_dpu_obs <= '0;
      wrp_i_mid_tu_obs <= '0;
    end else begin
      if(wrp_i_mid_mvm_exe_obs != i_mid_mvm_exe_obs)
        wrp_i_mid_mvm_exe_obs  <= i_mid_mvm_exe_obs;
      if(wrp_i_mid_mvm_prg_obs != i_mid_mvm_prg_obs)
        wrp_i_mid_mvm_prg_obs    <= i_mid_mvm_prg_obs;
      if(wrp_i_mid_iau_obs != i_mid_iau_obs)
        wrp_i_mid_iau_obs  <= i_mid_iau_obs;
      if(wrp_i_mid_dpu_obs != i_mid_dpu_obs)
        wrp_i_mid_dpu_obs  <= i_mid_dpu_obs;
      if(wrp_i_mid_tu_obs != i_mid_tu_obs)
        wrp_i_mid_tu_obs  <= i_mid_tu_obs;
    end
  end
    // LS2AIC:
  logic [AIC_DEV_OBS_DW-1:0]  wrp_o_mid_mvm_exe_obs, out_o_mid_mvm_exe_obs;
  logic [AIC_DEV_OBS_DW-1:0]  wrp_o_mid_mvm_prg_obs, out_o_mid_mvm_prg_obs;
  logic [AIC_DEV_OBS_DW-1:0]  wrp_o_mid_iau_obs, out_o_mid_iau_obs;
  logic [AIC_DEV_OBS_DW-1:0]  wrp_o_mid_dpu_obs, out_o_mid_dpu_obs;
  logic [AIC_TU_OBS_DW-1:0]   wrp_o_mid_tu_obs, out_o_mid_tu_obs;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_o_mid_obs_del
    if (i_rst_n == 1'b0) begin
      out_o_mid_mvm_exe_obs <= '0;
      out_o_mid_mvm_prg_obs <= '0;
      out_o_mid_iau_obs <= '0;
      out_o_mid_dpu_obs <= '0;
      out_o_mid_tu_obs <= '0;
    end else begin
      if(out_o_mid_mvm_exe_obs != wrp_o_mid_mvm_exe_obs)
        out_o_mid_mvm_exe_obs  <= wrp_o_mid_mvm_exe_obs;
      if(out_o_mid_mvm_prg_obs != wrp_o_mid_mvm_prg_obs)
        out_o_mid_mvm_prg_obs    <= wrp_o_mid_mvm_prg_obs;
      if(out_o_mid_iau_obs != wrp_o_mid_iau_obs)
        out_o_mid_iau_obs  <= wrp_o_mid_iau_obs;
      if(out_o_mid_dpu_obs != wrp_o_mid_dpu_obs)
        out_o_mid_dpu_obs  <= wrp_o_mid_dpu_obs;
      if(out_o_mid_tu_obs != wrp_o_mid_tu_obs)
        out_o_mid_tu_obs  <= wrp_o_mid_tu_obs;
    end
  end
  always_comb o_mid_mvm_exe_obs = out_o_mid_mvm_exe_obs;
  always_comb o_mid_mvm_prg_obs   = out_o_mid_mvm_prg_obs;
  always_comb o_mid_iau_obs = out_o_mid_iau_obs;
  always_comb o_mid_dpu_obs = out_o_mid_dpu_obs;
  always_comb o_mid_tu_obs = out_o_mid_tu_obs;

  /////////////// Timestamp & ACD sync ////////////
    // MID2LS:
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] wrp_i_mid_ts_start;
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] wrp_i_mid_ts_end;
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] wrp_i_mid_acd_sync;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_i_mid_ts_sync_del
    if (i_rst_n == 1'b0) begin
      wrp_i_mid_ts_start <= '0;
      wrp_i_mid_ts_end <= '0;
      wrp_i_mid_acd_sync <= '0;
    end else begin
      if(wrp_i_mid_ts_start != i_mid_ts_start)
        wrp_i_mid_ts_start  <= i_mid_ts_start;
      if(wrp_i_mid_ts_end != i_mid_ts_end)
        wrp_i_mid_ts_end    <= i_mid_ts_end;
      if(wrp_i_mid_acd_sync != i_mid_acd_sync)
        wrp_i_mid_acd_sync  <= i_mid_acd_sync;
    end
  end
    // LS2AIC:
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] wrp_o_mid_ts_start, out_o_mid_ts_start;
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] wrp_o_mid_ts_end, out_o_mid_ts_end;
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] wrp_o_mid_acd_sync, out_o_mid_acd_sync;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_o_mid_ts_sync_del
    if (i_rst_n == 1'b0) begin
      out_o_mid_ts_start <= '0;
      out_o_mid_ts_end <= '0;
      out_o_mid_acd_sync <= '0;
    end else begin
      if(out_o_mid_ts_start != wrp_o_mid_ts_start)
        out_o_mid_ts_start  <= wrp_o_mid_ts_start;
      if(out_o_mid_ts_end != wrp_o_mid_ts_end)
        out_o_mid_ts_end    <= wrp_o_mid_ts_end;
      if(out_o_mid_acd_sync != wrp_o_mid_acd_sync)
        out_o_mid_acd_sync  <= wrp_o_mid_acd_sync;
    end
  end
  always_comb o_mid_ts_start = out_o_mid_ts_start;
  always_comb o_mid_ts_end   = out_o_mid_ts_end;
  always_comb o_mid_acd_sync = out_o_mid_acd_sync;

  ////////////////////////////////////////////////
  //////// DID feedthrough
  /////////////// Token ////////////
  //// DWPU:
    // MID2LS:
  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] wrp_i_did_dwpu_tok_prod_vld;
  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] wrp_o_did_dwpu_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_DWPU_NR_TOK_PROD)) u_tok_i_did_dwpu_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_did_dwpu_tok_prod_vld),
    .o_s_ready(o_did_dwpu_tok_prod_rdy),
    .o_m_valid(wrp_i_did_dwpu_tok_prod_vld),
    .i_m_ready(wrp_o_did_dwpu_tok_prod_rdy)
  );
  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] wrp_o_did_dwpu_tok_cons_vld;
  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] wrp_i_did_dwpu_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_DWPU_NR_TOK_CONS)) u_tok_o_did_dwpu_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_did_dwpu_tok_cons_vld),
    .o_s_ready(wrp_i_did_dwpu_tok_cons_rdy),
    .o_m_valid(o_did_dwpu_tok_cons_vld),
    .i_m_ready(i_did_dwpu_tok_cons_rdy)
  );
    // LS2AIC:
  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] wrp_o_did_dwpu_tok_prod_vld;
  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] wrp_i_did_dwpu_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_DWPU_NR_TOK_PROD)) u_tok_o_did_dwpu_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_did_dwpu_tok_prod_vld),
    .o_s_ready(wrp_i_did_dwpu_tok_prod_rdy),
    .o_m_valid(o_did_dwpu_tok_prod_vld),
    .i_m_ready(i_did_dwpu_tok_prod_rdy)
  );
  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] wrp_i_did_dwpu_tok_cons_vld;
  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] wrp_o_did_dwpu_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_DWPU_NR_TOK_CONS)) u_tok_i_did_dwpu_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_did_dwpu_tok_cons_vld),
    .o_s_ready(o_did_dwpu_tok_cons_rdy),
    .o_m_valid(wrp_i_did_dwpu_tok_cons_vld),
    .i_m_ready(wrp_o_did_dwpu_tok_cons_rdy)
  );
  //// IAU:
    // MID2LS:
  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] wrp_i_did_iau_tok_prod_vld;
  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] wrp_o_did_iau_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_IAU_NR_TOK_PROD)) u_tok_i_did_iau_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_did_iau_tok_prod_vld),
    .o_s_ready(o_did_iau_tok_prod_rdy),
    .o_m_valid(wrp_i_did_iau_tok_prod_vld),
    .i_m_ready(wrp_o_did_iau_tok_prod_rdy)
  );
  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] wrp_o_did_iau_tok_cons_vld;
  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] wrp_i_did_iau_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_IAU_NR_TOK_CONS)) u_tok_o_did_iau_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_did_iau_tok_cons_vld),
    .o_s_ready(wrp_i_did_iau_tok_cons_rdy),
    .o_m_valid(o_did_iau_tok_cons_vld),
    .i_m_ready(i_did_iau_tok_cons_rdy)
  );
    // LS2AIC:
  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] wrp_o_did_iau_tok_prod_vld;
  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] wrp_i_did_iau_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_IAU_NR_TOK_PROD)) u_tok_o_did_iau_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_did_iau_tok_prod_vld),
    .o_s_ready(wrp_i_did_iau_tok_prod_rdy),
    .o_m_valid(o_did_iau_tok_prod_vld),
    .i_m_ready(i_did_iau_tok_prod_rdy)
  );
  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] wrp_i_did_iau_tok_cons_vld;
  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] wrp_o_did_iau_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_IAU_NR_TOK_CONS)) u_tok_i_did_iau_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_did_iau_tok_cons_vld),
    .o_s_ready(o_did_iau_tok_cons_rdy),
    .o_m_valid(wrp_i_did_iau_tok_cons_vld),
    .i_m_ready(wrp_o_did_iau_tok_cons_rdy)
  );
  //// DPU:
    // MID2LS:
  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] wrp_i_did_dpu_tok_prod_vld;
  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] wrp_o_did_dpu_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_DPU_NR_TOK_PROD)) u_tok_i_did_dpu_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_did_dpu_tok_prod_vld),
    .o_s_ready(o_did_dpu_tok_prod_rdy),
    .o_m_valid(wrp_i_did_dpu_tok_prod_vld),
    .i_m_ready(wrp_o_did_dpu_tok_prod_rdy)
  );
  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] wrp_o_did_dpu_tok_cons_vld;
  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] wrp_i_did_dpu_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_DPU_NR_TOK_CONS)) u_tok_o_did_dpu_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_did_dpu_tok_cons_vld),
    .o_s_ready(wrp_i_did_dpu_tok_cons_rdy),
    .o_m_valid(o_did_dpu_tok_cons_vld),
    .i_m_ready(i_did_dpu_tok_cons_rdy)
  );
    // LS2AIC:
  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] wrp_o_did_dpu_tok_prod_vld;
  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] wrp_i_did_dpu_tok_prod_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_DPU_NR_TOK_PROD)) u_tok_o_did_dpu_prod_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(wrp_o_did_dpu_tok_prod_vld),
    .o_s_ready(wrp_i_did_dpu_tok_prod_rdy),
    .o_m_valid(o_did_dpu_tok_prod_vld),
    .i_m_ready(i_did_dpu_tok_prod_rdy)
  );
  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] wrp_i_did_dpu_tok_cons_vld;
  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] wrp_o_did_dpu_tok_cons_rdy;
  token_cut #(.NumTokens(TOK_MGR_D_DPU_NR_TOK_CONS)) u_tok_i_did_dpu_cons_spill (
    .i_clk,
    .i_rst_n,
    .i_s_valid(i_did_dpu_tok_cons_vld),
    .o_s_ready(o_did_dpu_tok_cons_rdy),
    .o_m_valid(wrp_i_did_dpu_tok_cons_vld),
    .i_m_ready(wrp_o_did_dpu_tok_cons_rdy)
  );

  /////////////// IRQ ////////////
  logic [2:0] wrp_i_did_irq;
  logic [2:0] wrp_o_did_irq, out_o_did_irq;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_did_irq_del
    if (i_rst_n == 1'b0) begin
      wrp_i_did_irq <= '0;
      out_o_did_irq <= '0;
    end else begin
      if(wrp_i_did_irq != i_did_irq)
        wrp_i_did_irq  <= i_did_irq;
      if(out_o_did_irq != wrp_o_did_irq)
        out_o_did_irq    <= wrp_o_did_irq;
    end
  end
  always_comb o_did_irq = out_o_did_irq;

  /////////////// OBS ////////////
    // DID2LS:
  logic [AIC_DEV_OBS_DW-1:0] wrp_i_did_dwpu_obs;
  logic [AIC_DEV_OBS_DW-1:0] wrp_i_did_iau_obs;
  logic [AIC_DEV_OBS_DW-1:0] wrp_i_did_dpu_obs;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_i_did_obs_del
    if (i_rst_n == 1'b0) begin
      wrp_i_did_dwpu_obs <= '0;
      wrp_i_did_iau_obs <= '0;
      wrp_i_did_dpu_obs <= '0;
    end else begin
      if(wrp_i_did_dwpu_obs != i_did_dwpu_obs)
        wrp_i_did_dwpu_obs  <= i_did_dwpu_obs;
      if(wrp_i_did_iau_obs != i_did_iau_obs)
        wrp_i_did_iau_obs  <= i_did_iau_obs;
      if(wrp_i_did_dpu_obs != i_did_dpu_obs)
        wrp_i_did_dpu_obs  <= i_did_dpu_obs;
    end
  end
    // LS2AIC:
  logic [AIC_DEV_OBS_DW-1:0] wrp_o_did_dwpu_obs, out_o_did_dwpu_obs;
  logic [AIC_DEV_OBS_DW-1:0] wrp_o_did_iau_obs, out_o_did_iau_obs;
  logic [AIC_DEV_OBS_DW-1:0] wrp_o_did_dpu_obs, out_o_did_dpu_obs;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_o_did_obs_del
    if (i_rst_n == 1'b0) begin
      out_o_did_dwpu_obs <= '0;
      out_o_did_iau_obs <= '0;
      out_o_did_dpu_obs <= '0;
    end else begin
      if(out_o_did_dwpu_obs != wrp_o_did_dwpu_obs)
        out_o_did_dwpu_obs  <= wrp_o_did_dwpu_obs;
      if(out_o_did_iau_obs != wrp_o_did_iau_obs)
        out_o_did_iau_obs  <= wrp_o_did_iau_obs;
      if(out_o_did_dpu_obs != wrp_o_did_dpu_obs)
        out_o_did_dpu_obs  <= wrp_o_did_dpu_obs;
    end
  end
  always_comb o_did_dwpu_obs   = out_o_did_dwpu_obs;
  always_comb o_did_iau_obs = out_o_did_iau_obs;
  always_comb o_did_dpu_obs = out_o_did_dpu_obs;

  /////////////// Timestamp & ACD sync ////////////
    // DID2LS:
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] wrp_i_did_ts_start;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] wrp_i_did_ts_end;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] wrp_i_did_acd_sync;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_i_did_ts_sync_del
    if (i_rst_n == 1'b0) begin
      wrp_i_did_ts_start <= '0;
      wrp_i_did_ts_end <= '0;
      wrp_i_did_acd_sync <= '0;
    end else begin
      if(wrp_i_did_ts_start != i_did_ts_start)
        wrp_i_did_ts_start  <= i_did_ts_start;
      if(wrp_i_did_ts_end != i_did_ts_end)
        wrp_i_did_ts_end    <= i_did_ts_end;
      if(wrp_i_did_acd_sync != i_did_acd_sync)
        wrp_i_did_acd_sync  <= i_did_acd_sync;
    end
  end
    // LS2AIC:
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] wrp_o_did_ts_start, out_o_did_ts_start;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] wrp_o_did_ts_end, out_o_did_ts_end;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] wrp_o_did_acd_sync, out_o_did_acd_sync;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_o_did_ts_sync_del
    if (i_rst_n == 1'b0) begin
      out_o_did_ts_start <= '0;
      out_o_did_ts_end <= '0;
      out_o_did_acd_sync <= '0;
    end else begin
      if(out_o_did_ts_start != wrp_o_did_ts_start)
        out_o_did_ts_start  <= wrp_o_did_ts_start;
      if(out_o_did_ts_end != wrp_o_did_ts_end)
        out_o_did_ts_end    <= wrp_o_did_ts_end;
      if(out_o_did_acd_sync != wrp_o_did_acd_sync)
        out_o_did_acd_sync  <= wrp_o_did_acd_sync;
    end
  end
  always_comb o_did_ts_start = out_o_did_ts_start;
  always_comb o_did_ts_end   = out_o_did_ts_end;
  always_comb o_did_acd_sync = out_o_did_acd_sync;

  //------------------------------------------------------
  // AXI address channels
  typedef struct packed {
    logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] addr;
    logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] id;
    logic [       AIC_LT_AXI_LEN_WIDTH-1:0] len;
    logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] size;
    logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] burst;
  } aic_ls_cfg_out_axi_addr_t;

  aic_ls_cfg_out_axi_addr_t wrp_o_mid_cfg_axi_m_aw, out_o_mid_cfg_axi_m_aw;
  logic                     wrp_o_mid_cfg_axi_m_awvalid;
  logic                     wrp_i_mid_cfg_axi_m_awready;
  aic_ls_cfg_out_axi_addr_t wrp_o_mid_cfg_axi_m_ar, out_o_mid_cfg_axi_m_ar;
  logic                     wrp_o_mid_cfg_axi_m_arvalid;
  logic                     wrp_i_mid_cfg_axi_m_arready;

  // AXI write data channel
  aic_ls_lp_axi_wdata_t wrp_o_mid_cfg_axi_m_wdata, out_o_mid_cfg_axi_m_wdata;
  logic                 wrp_o_mid_cfg_axi_m_wvalid;
  logic                 wrp_i_mid_cfg_axi_m_wready;

  // AXI write response channel
  aic_ls_lp_axi_bresp_t wrp_i_mid_cfg_axi_m_bresp, in_i_mid_cfg_axi_m_bresp;
  logic                 wrp_i_mid_cfg_axi_m_bvalid;
  logic                 wrp_o_mid_cfg_axi_m_bready;

  // AXI read data/response channel
  aic_ls_lp_axi_rdata_t wrp_i_mid_cfg_axi_m_rdata, in_i_mid_cfg_axi_m_rdata;
  logic                 wrp_i_mid_cfg_axi_m_rvalid;
  logic                 wrp_o_mid_cfg_axi_m_rready;

  always_comb in_i_mid_cfg_axi_m_bresp = aic_ls_lp_axi_bresp_t'{
      id:     i_mid_cfg_axi_m_bid,
      resp:   i_mid_cfg_axi_m_bresp
  };
  always_comb in_i_mid_cfg_axi_m_rdata = aic_ls_lp_axi_rdata_t'{
      last:   i_mid_cfg_axi_m_rlast,
      id:     i_mid_cfg_axi_m_rid,
      data:   i_mid_cfg_axi_m_rdata,
      resp:   i_mid_cfg_axi_m_rresp
  };
  axe_axi_multicut #(
    .NumCuts  (1), // Number of cuts.
    // AXI channel structs
    .axi_aw_t (aic_ls_cfg_out_axi_addr_t),
    .axi_w_t  (aic_ls_lp_axi_wdata_t),
    .axi_b_t  (aic_ls_lp_axi_bresp_t),
    .axi_ar_t (aic_ls_cfg_out_axi_addr_t),
    .axi_r_t  (aic_ls_lp_axi_rdata_t)
  ) u_axi_mid_cfg_cut (
    .i_clk,
    .i_rst_n,
    // External AXI Interface
    .i_axi_s_aw      (wrp_o_mid_cfg_axi_m_aw),
    .i_axi_s_aw_valid(wrp_o_mid_cfg_axi_m_awvalid),
    .o_axi_s_aw_ready(wrp_i_mid_cfg_axi_m_awready),
    .i_axi_s_w       (wrp_o_mid_cfg_axi_m_wdata),
    .i_axi_s_w_valid (wrp_o_mid_cfg_axi_m_wvalid),
    .o_axi_s_w_ready (wrp_i_mid_cfg_axi_m_wready),
    .o_axi_s_b       (wrp_i_mid_cfg_axi_m_bresp),
    .o_axi_s_b_valid (wrp_i_mid_cfg_axi_m_bvalid),
    .i_axi_s_b_ready (wrp_o_mid_cfg_axi_m_bready),
    .i_axi_s_ar      (wrp_o_mid_cfg_axi_m_ar),
    .i_axi_s_ar_valid(wrp_o_mid_cfg_axi_m_arvalid),
    .o_axi_s_ar_ready(wrp_i_mid_cfg_axi_m_arready),
    .o_axi_s_r       (wrp_i_mid_cfg_axi_m_rdata),
    .o_axi_s_r_valid (wrp_i_mid_cfg_axi_m_rvalid),
    .i_axi_s_r_ready (wrp_o_mid_cfg_axi_m_rready),
    // Internal AXI Interface
    .o_axi_m_aw      (out_o_mid_cfg_axi_m_aw),
    .o_axi_m_aw_valid(o_mid_cfg_axi_m_awvalid),
    .i_axi_m_aw_ready(i_mid_cfg_axi_m_awready),
    .o_axi_m_w       (out_o_mid_cfg_axi_m_wdata),
    .o_axi_m_w_valid (o_mid_cfg_axi_m_wvalid),
    .i_axi_m_w_ready (i_mid_cfg_axi_m_wready),
    .i_axi_m_b       (in_i_mid_cfg_axi_m_bresp),
    .i_axi_m_b_valid (i_mid_cfg_axi_m_bvalid),
    .o_axi_m_b_ready (o_mid_cfg_axi_m_bready),
    .o_axi_m_ar      (out_o_mid_cfg_axi_m_ar),
    .o_axi_m_ar_valid(o_mid_cfg_axi_m_arvalid),
    .i_axi_m_ar_ready(i_mid_cfg_axi_m_arready),
    .i_axi_m_r       (in_i_mid_cfg_axi_m_rdata),
    .i_axi_m_r_valid (i_mid_cfg_axi_m_rvalid),
    .o_axi_m_r_ready (o_mid_cfg_axi_m_rready)
  );
  always_comb o_mid_cfg_axi_m_awaddr  = out_o_mid_cfg_axi_m_aw.addr;
  always_comb o_mid_cfg_axi_m_awid    = out_o_mid_cfg_axi_m_aw.id;
  always_comb o_mid_cfg_axi_m_awlen   = out_o_mid_cfg_axi_m_aw.len;
  always_comb o_mid_cfg_axi_m_awsize  = out_o_mid_cfg_axi_m_aw.size;
  always_comb o_mid_cfg_axi_m_awburst = out_o_mid_cfg_axi_m_aw.burst;

  always_comb o_mid_cfg_axi_m_wlast   = out_o_mid_cfg_axi_m_wdata.last;
  always_comb o_mid_cfg_axi_m_wstrb   = out_o_mid_cfg_axi_m_wdata.strb;
  always_comb o_mid_cfg_axi_m_wdata   = out_o_mid_cfg_axi_m_wdata.data;

  always_comb o_mid_cfg_axi_m_araddr  = out_o_mid_cfg_axi_m_ar.addr;
  always_comb o_mid_cfg_axi_m_arid    = out_o_mid_cfg_axi_m_ar.id;
  always_comb o_mid_cfg_axi_m_arlen   = out_o_mid_cfg_axi_m_ar.len;
  always_comb o_mid_cfg_axi_m_arsize  = out_o_mid_cfg_axi_m_ar.size;
  always_comb o_mid_cfg_axi_m_arburst = out_o_mid_cfg_axi_m_ar.burst;

    // CFG to DID:
  //------------------------------------------------------
  // AXI address channels
  aic_ls_cfg_out_axi_addr_t wrp_o_did_cfg_axi_m_aw, out_o_did_cfg_axi_m_aw;
  logic                     wrp_o_did_cfg_axi_m_awvalid;
  logic                     wrp_i_did_cfg_axi_m_awready;
  aic_ls_cfg_out_axi_addr_t wrp_o_did_cfg_axi_m_ar, out_o_did_cfg_axi_m_ar;
  logic                     wrp_o_did_cfg_axi_m_arvalid;
  logic                     wrp_i_did_cfg_axi_m_arready;

  // AXI write data channel
  aic_ls_lp_axi_wdata_t wrp_o_did_cfg_axi_m_wdata, out_o_did_cfg_axi_m_wdata;
  logic                 wrp_o_did_cfg_axi_m_wvalid;
  logic                 wrp_i_did_cfg_axi_m_wready;

  // AXI write response channel
  aic_ls_lp_axi_bresp_t wrp_i_did_cfg_axi_m_bresp, in_i_did_cfg_axi_m_bresp;
  logic                 wrp_i_did_cfg_axi_m_bvalid;
  logic                 wrp_o_did_cfg_axi_m_bready;

  // AXI read data/response channel
  aic_ls_lp_axi_rdata_t wrp_i_did_cfg_axi_m_rdata, in_i_did_cfg_axi_m_rdata;
  logic                 wrp_i_did_cfg_axi_m_rvalid;
  logic                 wrp_o_did_cfg_axi_m_rready;

  always_comb in_i_did_cfg_axi_m_bresp = aic_ls_lp_axi_bresp_t'{
      id:     i_did_cfg_axi_m_bid,
      resp:   i_did_cfg_axi_m_bresp
  };
  always_comb in_i_did_cfg_axi_m_rdata = aic_ls_lp_axi_rdata_t'{
      last:   i_did_cfg_axi_m_rlast,
      id:     i_did_cfg_axi_m_rid,
      data:   i_did_cfg_axi_m_rdata,
      resp:   i_did_cfg_axi_m_rresp
  };
  axe_axi_multicut #(
    .NumCuts  (1), // Number of cuts.
    // AXI channel structs
    .axi_aw_t (aic_ls_cfg_out_axi_addr_t),
    .axi_w_t  (aic_ls_lp_axi_wdata_t),
    .axi_b_t  (aic_ls_lp_axi_bresp_t),
    .axi_ar_t (aic_ls_cfg_out_axi_addr_t),
    .axi_r_t  (aic_ls_lp_axi_rdata_t)
  ) u_axi_did_cfg_cut (
    .i_clk,
    .i_rst_n,
    // External AXI Interface
    .i_axi_s_aw      (wrp_o_did_cfg_axi_m_aw),
    .i_axi_s_aw_valid(wrp_o_did_cfg_axi_m_awvalid),
    .o_axi_s_aw_ready(wrp_i_did_cfg_axi_m_awready),
    .i_axi_s_w       (wrp_o_did_cfg_axi_m_wdata),
    .i_axi_s_w_valid (wrp_o_did_cfg_axi_m_wvalid),
    .o_axi_s_w_ready (wrp_i_did_cfg_axi_m_wready),
    .o_axi_s_b       (wrp_i_did_cfg_axi_m_bresp),
    .o_axi_s_b_valid (wrp_i_did_cfg_axi_m_bvalid),
    .i_axi_s_b_ready (wrp_o_did_cfg_axi_m_bready),
    .i_axi_s_ar      (wrp_o_did_cfg_axi_m_ar),
    .i_axi_s_ar_valid(wrp_o_did_cfg_axi_m_arvalid),
    .o_axi_s_ar_ready(wrp_i_did_cfg_axi_m_arready),
    .o_axi_s_r       (wrp_i_did_cfg_axi_m_rdata),
    .o_axi_s_r_valid (wrp_i_did_cfg_axi_m_rvalid),
    .i_axi_s_r_ready (wrp_o_did_cfg_axi_m_rready),
    // Internal AXI Interface
    .o_axi_m_aw      (out_o_did_cfg_axi_m_aw),
    .o_axi_m_aw_valid(o_did_cfg_axi_m_awvalid),
    .i_axi_m_aw_ready(i_did_cfg_axi_m_awready),
    .o_axi_m_w       (out_o_did_cfg_axi_m_wdata),
    .o_axi_m_w_valid (o_did_cfg_axi_m_wvalid),
    .i_axi_m_w_ready (i_did_cfg_axi_m_wready),
    .i_axi_m_b       (in_i_did_cfg_axi_m_bresp),
    .i_axi_m_b_valid (i_did_cfg_axi_m_bvalid),
    .o_axi_m_b_ready (o_did_cfg_axi_m_bready),
    .o_axi_m_ar      (out_o_did_cfg_axi_m_ar),
    .o_axi_m_ar_valid(o_did_cfg_axi_m_arvalid),
    .i_axi_m_ar_ready(i_did_cfg_axi_m_arready),
    .i_axi_m_r       (in_i_did_cfg_axi_m_rdata),
    .i_axi_m_r_valid (i_did_cfg_axi_m_rvalid),
    .o_axi_m_r_ready (o_did_cfg_axi_m_rready)
  );
  always_comb o_did_cfg_axi_m_awaddr  = out_o_did_cfg_axi_m_aw.addr;
  always_comb o_did_cfg_axi_m_awid    = out_o_did_cfg_axi_m_aw.id;
  always_comb o_did_cfg_axi_m_awlen   = out_o_did_cfg_axi_m_aw.len;
  always_comb o_did_cfg_axi_m_awsize  = out_o_did_cfg_axi_m_aw.size;
  always_comb o_did_cfg_axi_m_awburst = out_o_did_cfg_axi_m_aw.burst;

  always_comb o_did_cfg_axi_m_wlast   = out_o_did_cfg_axi_m_wdata.last;
  always_comb o_did_cfg_axi_m_wstrb   = out_o_did_cfg_axi_m_wdata.strb;
  always_comb o_did_cfg_axi_m_wdata   = out_o_did_cfg_axi_m_wdata.data;

  always_comb o_did_cfg_axi_m_araddr  = out_o_did_cfg_axi_m_ar.addr;
  always_comb o_did_cfg_axi_m_arid    = out_o_did_cfg_axi_m_ar.id;
  always_comb o_did_cfg_axi_m_arlen   = out_o_did_cfg_axi_m_ar.len;
  always_comb o_did_cfg_axi_m_arsize  = out_o_did_cfg_axi_m_ar.size;
  always_comb o_did_cfg_axi_m_arburst = out_o_did_cfg_axi_m_ar.burst;

  aic_ls u_aic_ls (

  .i_clk(i_clk),
  .i_rst_n(i_rst_n),
  .i_scan_en(scan_en),
  .o_dmc_irq(wrp_o_dmc_irq),
  .o_m_ifd0_axis_m_tvalid(wrp_o_m_ifd0_axis_m_tvalid),
  .i_m_ifd0_axis_m_tready(wrp_i_m_ifd0_axis_m_tready),
  .o_m_ifd0_axis_m_tdata(wrp_o_m_ifd0_axis_m_tdata),
  .o_m_ifd0_axis_m_tlast(wrp_o_m_ifd0_axis_m_tlast),
  .o_m_ifd1_axis_m_tvalid(wrp_o_m_ifd1_axis_m_tvalid),
  .i_m_ifd1_axis_m_tready(wrp_i_m_ifd1_axis_m_tready),
  .o_m_ifd1_axis_m_tdata(wrp_o_m_ifd1_axis_m_tdata),
  .o_m_ifd1_axis_m_tlast(wrp_o_m_ifd1_axis_m_tlast),
  .o_m_ifd2_axis_m_tvalid(wrp_o_m_ifd2_axis_m_tvalid),
  .i_m_ifd2_axis_m_tready(wrp_i_m_ifd2_axis_m_tready),
  .o_m_ifd2_axis_m_tdata(wrp_o_m_ifd2_axis_m_tdata),
  .o_m_ifd2_axis_m_tlast(wrp_o_m_ifd2_axis_m_tlast),
  .o_m_ifdw_axis_m_tvalid(wrp_o_m_ifdw_axis_m_tvalid),
  .i_m_ifdw_axis_m_tready(wrp_i_m_ifdw_axis_m_tready),
  .o_m_ifdw_axis_m_tdata(wrp_o_m_ifdw_axis_m_tdata),
  .o_m_ifdw_axis_m_tlast(wrp_o_m_ifdw_axis_m_tlast),
  .o_d_ifd0_axis_m_tvalid(wrp_o_d_ifd0_axis_m_tvalid),
  .i_d_ifd0_axis_m_tready(wrp_i_d_ifd0_axis_m_tready),
  .o_d_ifd0_axis_m_tdata(wrp_o_d_ifd0_axis_m_tdata),
  .o_d_ifd0_axis_m_tlast(wrp_o_d_ifd0_axis_m_tlast),
  .o_d_ifd1_axis_m_tvalid(wrp_o_d_ifd1_axis_m_tvalid),
  .i_d_ifd1_axis_m_tready(wrp_i_d_ifd1_axis_m_tready),
  .o_d_ifd1_axis_m_tdata(wrp_o_d_ifd1_axis_m_tdata),
  .o_d_ifd1_axis_m_tlast(wrp_o_d_ifd1_axis_m_tlast),
  .i_m_odr_axis_s_tvalid(wrp_i_m_odr_axis_s_tvalid),
  .o_m_odr_axis_s_tready(wrp_o_m_odr_axis_s_tready),
  .i_m_odr_axis_s_tdata(wrp_i_m_odr_axis_s_tdata),
  .i_m_odr_axis_s_tlast(wrp_i_m_odr_axis_s_tlast),
  .i_d_odr_axis_s_tvalid(wrp_i_d_odr_axis_s_tvalid),
  .o_d_odr_axis_s_tready(wrp_o_d_odr_axis_s_tready),
  .i_d_odr_axis_s_tdata(wrp_i_d_odr_axis_s_tdata),
  .i_d_odr_axis_s_tlast(wrp_i_d_odr_axis_s_tlast),
  .i_rvv_0_req_valid(wrp_i_rvv_0_req_valid),
  .o_rvv_0_req_ready(wrp_o_rvv_0_req_ready),
  .i_rvv_0_req_addr(wrp_i_rvv_0_req_addr),
  .i_rvv_0_req_we(wrp_i_rvv_0_req_we),
  .i_rvv_0_req_be(wrp_i_rvv_0_req_be),
  .i_rvv_0_req_wdata(wrp_i_rvv_0_req_wdata),
  .o_rvv_0_res_valid(wrp_o_rvv_0_res_valid),
  .o_rvv_0_res_rdata(wrp_o_rvv_0_res_rdata),
  .o_rvv_0_res_err(wrp_o_rvv_0_res_err),
  .i_rvv_1_req_valid(wrp_i_rvv_1_req_valid),
  .o_rvv_1_req_ready(wrp_o_rvv_1_req_ready),
  .i_rvv_1_req_addr(wrp_i_rvv_1_req_addr),
  .i_rvv_1_req_we(wrp_i_rvv_1_req_we),
  .i_rvv_1_req_be(wrp_i_rvv_1_req_be),
  .i_rvv_1_req_wdata(wrp_i_rvv_1_req_wdata),
  .o_rvv_1_res_valid(wrp_o_rvv_1_res_valid),
  .o_rvv_1_res_rdata(wrp_o_rvv_1_res_rdata),
  .o_rvv_1_res_err(wrp_o_rvv_1_res_err),
  .i_rvv_2_req_valid(wrp_i_rvv_2_req_valid),
  .o_rvv_2_req_ready(wrp_o_rvv_2_req_ready),
  .i_rvv_2_req_addr(wrp_i_rvv_2_req_addr),
  .i_rvv_2_req_we(wrp_i_rvv_2_req_we),
  .i_rvv_2_req_be(wrp_i_rvv_2_req_be),
  .i_rvv_2_req_wdata(wrp_i_rvv_2_req_wdata),
  .o_rvv_2_res_valid(wrp_o_rvv_2_res_valid),
  .o_rvv_2_res_rdata(wrp_o_rvv_2_res_rdata),
  .o_rvv_2_res_err(wrp_o_rvv_2_res_err),
  .i_rvv_3_req_valid(wrp_i_rvv_3_req_valid),
  .o_rvv_3_req_ready(wrp_o_rvv_3_req_ready),
  .i_rvv_3_req_addr(wrp_i_rvv_3_req_addr),
  .i_rvv_3_req_we(wrp_i_rvv_3_req_we),
  .i_rvv_3_req_be(wrp_i_rvv_3_req_be),
  .i_rvv_3_req_wdata(wrp_i_rvv_3_req_wdata),
  .o_rvv_3_res_valid(wrp_o_rvv_3_res_valid),
  .o_rvv_3_res_rdata(wrp_o_rvv_3_res_rdata),
  .o_rvv_3_res_err(wrp_o_rvv_3_res_err),
  .i_rvv_4_req_valid(wrp_i_rvv_4_req_valid),
  .o_rvv_4_req_ready(wrp_o_rvv_4_req_ready),
  .i_rvv_4_req_addr(wrp_i_rvv_4_req_addr),
  .i_rvv_4_req_we(wrp_i_rvv_4_req_we),
  .i_rvv_4_req_be(wrp_i_rvv_4_req_be),
  .i_rvv_4_req_wdata(wrp_i_rvv_4_req_wdata),
  .o_rvv_4_res_valid(wrp_o_rvv_4_res_valid),
  .o_rvv_4_res_rdata(wrp_o_rvv_4_res_rdata),
  .o_rvv_4_res_err(wrp_o_rvv_4_res_err),
  .i_rvv_5_req_valid(wrp_i_rvv_5_req_valid),
  .o_rvv_5_req_ready(wrp_o_rvv_5_req_ready),
  .i_rvv_5_req_addr(wrp_i_rvv_5_req_addr),
  .i_rvv_5_req_we(wrp_i_rvv_5_req_we),
  .i_rvv_5_req_be(wrp_i_rvv_5_req_be),
  .i_rvv_5_req_wdata(wrp_i_rvv_5_req_wdata),
  .o_rvv_5_res_valid(wrp_o_rvv_5_res_valid),
  .o_rvv_5_res_rdata(wrp_o_rvv_5_res_rdata),
  .o_rvv_5_res_err(wrp_o_rvv_5_res_err),
  .i_rvv_6_req_valid(wrp_i_rvv_6_req_valid),
  .o_rvv_6_req_ready(wrp_o_rvv_6_req_ready),
  .i_rvv_6_req_addr(wrp_i_rvv_6_req_addr),
  .i_rvv_6_req_we(wrp_i_rvv_6_req_we),
  .i_rvv_6_req_be(wrp_i_rvv_6_req_be),
  .i_rvv_6_req_wdata(wrp_i_rvv_6_req_wdata),
  .o_rvv_6_res_valid(wrp_o_rvv_6_res_valid),
  .o_rvv_6_res_rdata(wrp_o_rvv_6_res_rdata),
  .o_rvv_6_res_err(wrp_o_rvv_6_res_err),
  .i_rvv_7_req_valid(wrp_i_rvv_7_req_valid),
  .o_rvv_7_req_ready(wrp_o_rvv_7_req_ready),
  .i_rvv_7_req_addr(wrp_i_rvv_7_req_addr),
  .i_rvv_7_req_we(wrp_i_rvv_7_req_we),
  .i_rvv_7_req_be(wrp_i_rvv_7_req_be),
  .i_rvv_7_req_wdata(wrp_i_rvv_7_req_wdata),
  .o_rvv_7_res_valid(wrp_o_rvv_7_res_valid),
  .o_rvv_7_res_rdata(wrp_o_rvv_7_res_rdata),
  .o_rvv_7_res_err(wrp_o_rvv_7_res_err),
  .o_m_ifd0_tok_prod_vld(wrp_o_m_ifd0_tok_prod_vld),
  .i_m_ifd0_tok_prod_rdy(wrp_i_m_ifd0_tok_prod_rdy),
  .i_m_ifd0_tok_cons_vld(wrp_i_m_ifd0_tok_cons_vld),
  .o_m_ifd0_tok_cons_rdy(wrp_o_m_ifd0_tok_cons_rdy),
  .o_m_ifd1_tok_prod_vld(wrp_o_m_ifd1_tok_prod_vld),
  .i_m_ifd1_tok_prod_rdy(wrp_i_m_ifd1_tok_prod_rdy),
  .i_m_ifd1_tok_cons_vld(wrp_i_m_ifd1_tok_cons_vld),
  .o_m_ifd1_tok_cons_rdy(wrp_o_m_ifd1_tok_cons_rdy),
  .o_m_ifd2_tok_prod_vld(wrp_o_m_ifd2_tok_prod_vld),
  .i_m_ifd2_tok_prod_rdy(wrp_i_m_ifd2_tok_prod_rdy),
  .i_m_ifd2_tok_cons_vld(wrp_i_m_ifd2_tok_cons_vld),
  .o_m_ifd2_tok_cons_rdy(wrp_o_m_ifd2_tok_cons_rdy),
  .o_m_ifdw_tok_prod_vld(wrp_o_m_ifdw_tok_prod_vld),
  .i_m_ifdw_tok_prod_rdy(wrp_i_m_ifdw_tok_prod_rdy),
  .i_m_ifdw_tok_cons_vld(wrp_i_m_ifdw_tok_cons_vld),
  .o_m_ifdw_tok_cons_rdy(wrp_o_m_ifdw_tok_cons_rdy),
  .o_d_ifd0_tok_prod_vld(wrp_o_d_ifd0_tok_prod_vld),
  .i_d_ifd0_tok_prod_rdy(wrp_i_d_ifd0_tok_prod_rdy),
  .i_d_ifd0_tok_cons_vld(wrp_i_d_ifd0_tok_cons_vld),
  .o_d_ifd0_tok_cons_rdy(wrp_o_d_ifd0_tok_cons_rdy),
  .o_d_ifd1_tok_prod_vld(wrp_o_d_ifd1_tok_prod_vld),
  .i_d_ifd1_tok_prod_rdy(wrp_i_d_ifd1_tok_prod_rdy),
  .i_d_ifd1_tok_cons_vld(wrp_i_d_ifd1_tok_cons_vld),
  .o_d_ifd1_tok_cons_rdy(wrp_o_d_ifd1_tok_cons_rdy),
  .o_m_odr_tok_prod_vld(wrp_o_m_odr_tok_prod_vld),
  .i_m_odr_tok_prod_rdy(wrp_i_m_odr_tok_prod_rdy),
  .i_m_odr_tok_cons_vld(wrp_i_m_odr_tok_cons_vld),
  .o_m_odr_tok_cons_rdy(wrp_o_m_odr_tok_cons_rdy),
  .o_d_odr_tok_prod_vld(wrp_o_d_odr_tok_prod_vld),
  .i_d_odr_tok_prod_rdy(wrp_i_d_odr_tok_prod_rdy),
  .i_d_odr_tok_cons_vld(wrp_i_d_odr_tok_cons_vld),
  .o_d_odr_tok_cons_rdy(wrp_o_d_odr_tok_cons_rdy),
  .o_dmc_ts_start(wrp_o_dmc_ts_start),
  .o_dmc_ts_end(wrp_o_dmc_ts_end),
  .o_dmc_acd_sync(wrp_o_dmc_acd_sync),
  .i_hp_axi_s_awvalid(wrp_i_hp_axi_s_awvalid),
  .i_hp_axi_s_awaddr(wrp_i_hp_axi_s_aw.addr),
  .i_hp_axi_s_awid(wrp_i_hp_axi_s_aw.id),
  .i_hp_axi_s_awlen(wrp_i_hp_axi_s_aw.len),
  .i_hp_axi_s_awsize(wrp_i_hp_axi_s_aw.size),
  .i_hp_axi_s_awburst(wrp_i_hp_axi_s_aw.burst),
  .i_hp_axi_s_awcache(wrp_i_hp_axi_s_aw.cache),
  .i_hp_axi_s_awprot(wrp_i_hp_axi_s_aw.prot),
  .i_hp_axi_s_awlock(wrp_i_hp_axi_s_aw.lock),
  .o_hp_axi_s_awready(wrp_o_hp_axi_s_awready),
  .i_hp_axi_s_wvalid(wrp_i_hp_axi_s_wvalid),
  .i_hp_axi_s_wlast(wrp_i_hp_axi_s_wdata.last),
  .i_hp_axi_s_wstrb(wrp_i_hp_axi_s_wdata.strb),
  .i_hp_axi_s_wdata(wrp_i_hp_axi_s_wdata.data),
  .o_hp_axi_s_wready(wrp_o_hp_axi_s_wready),
  .o_hp_axi_s_bvalid(wrp_o_hp_axi_s_bvalid),
  .o_hp_axi_s_bid(wrp_o_hp_axi_s_bresp.id),
  .o_hp_axi_s_bresp(wrp_o_hp_axi_s_bresp.resp),
  .i_hp_axi_s_bready(wrp_i_hp_axi_s_bready),
  .i_hp_axi_s_arvalid(wrp_i_hp_axi_s_arvalid),
  .i_hp_axi_s_araddr(wrp_i_hp_axi_s_ar.addr),
  .i_hp_axi_s_arid(wrp_i_hp_axi_s_ar.id),
  .i_hp_axi_s_arlen(wrp_i_hp_axi_s_ar.len),
  .i_hp_axi_s_arsize(wrp_i_hp_axi_s_ar.size),
  .i_hp_axi_s_arburst(wrp_i_hp_axi_s_ar.burst),
  .i_hp_axi_s_arcache(wrp_i_hp_axi_s_ar.cache),
  .i_hp_axi_s_arprot(wrp_i_hp_axi_s_ar.prot),
  .i_hp_axi_s_arlock(wrp_i_hp_axi_s_ar.lock),
  .o_hp_axi_s_arready(wrp_o_hp_axi_s_arready),
  .o_hp_axi_s_rvalid(wrp_o_hp_axi_s_rvalid),
  .o_hp_axi_s_rlast(wrp_o_hp_axi_s_rdata.last),
  .o_hp_axi_s_rid(wrp_o_hp_axi_s_rdata.id),
  .o_hp_axi_s_rdata(wrp_o_hp_axi_s_rdata.data),
  .o_hp_axi_s_rresp(wrp_o_hp_axi_s_rdata.resp),
  .i_hp_axi_s_rready(wrp_i_hp_axi_s_rready),
  .i_cfg_axi_s_awvalid(wrp_i_cfg_axi_s_awvalid),
  .i_cfg_axi_s_awaddr(wrp_i_cfg_axi_s_aw.addr),
  .i_cfg_axi_s_awid(wrp_i_cfg_axi_s_aw.id),
  .i_cfg_axi_s_awlen(wrp_i_cfg_axi_s_aw.len),
  .i_cfg_axi_s_awsize(wrp_i_cfg_axi_s_aw.size),
  .i_cfg_axi_s_awburst(wrp_i_cfg_axi_s_aw.burst),
  .o_cfg_axi_s_awready(wrp_o_cfg_axi_s_awready),
  .i_cfg_axi_s_wvalid(wrp_i_cfg_axi_s_wvalid),
  .i_cfg_axi_s_wlast(wrp_i_cfg_axi_s_wdata.last),
  .i_cfg_axi_s_wstrb(wrp_i_cfg_axi_s_wdata.strb),
  .i_cfg_axi_s_wdata(wrp_i_cfg_axi_s_wdata.data),
  .o_cfg_axi_s_wready(wrp_o_cfg_axi_s_wready),
  .o_cfg_axi_s_bvalid(wrp_o_cfg_axi_s_bvalid),
  .o_cfg_axi_s_bid(wrp_o_cfg_axi_s_bresp.id),
  .o_cfg_axi_s_bresp(wrp_o_cfg_axi_s_bresp.resp),
  .i_cfg_axi_s_bready(wrp_i_cfg_axi_s_bready),
  .i_cfg_axi_s_arvalid(wrp_i_cfg_axi_s_arvalid),
  .i_cfg_axi_s_araddr(wrp_i_cfg_axi_s_ar.addr),
  .i_cfg_axi_s_arid(wrp_i_cfg_axi_s_ar.id),
  .i_cfg_axi_s_arlen(wrp_i_cfg_axi_s_ar.len),
  .i_cfg_axi_s_arsize(wrp_i_cfg_axi_s_ar.size),
  .i_cfg_axi_s_arburst(wrp_i_cfg_axi_s_ar.burst),
  .o_cfg_axi_s_arready(wrp_o_cfg_axi_s_arready),
  .o_cfg_axi_s_rvalid(wrp_o_cfg_axi_s_rvalid),
  .o_cfg_axi_s_rlast(wrp_o_cfg_axi_s_rdata.last),
  .o_cfg_axi_s_rid(wrp_o_cfg_axi_s_rdata.id),
  .o_cfg_axi_s_rdata(wrp_o_cfg_axi_s_rdata.data),
  .o_cfg_axi_s_rresp(wrp_o_cfg_axi_s_rdata.resp),
  .i_cfg_axi_s_rready(wrp_i_cfg_axi_s_rready),
  .i_cid(i_cid),
  .o_dmc_obs(wrp_o_dmc_obs),
  .i_mid_mvm_exe_tok_prod_vld(wrp_i_mid_mvm_exe_tok_prod_vld),
  .o_mid_mvm_exe_tok_prod_rdy(wrp_o_mid_mvm_exe_tok_prod_rdy),
  .o_mid_mvm_exe_tok_cons_vld(wrp_o_mid_mvm_exe_tok_cons_vld),
  .i_mid_mvm_exe_tok_cons_rdy(wrp_i_mid_mvm_exe_tok_cons_rdy),
  .o_mid_mvm_exe_tok_prod_vld(wrp_o_mid_mvm_exe_tok_prod_vld),
  .i_mid_mvm_exe_tok_prod_rdy(wrp_i_mid_mvm_exe_tok_prod_rdy),
  .i_mid_mvm_exe_tok_cons_vld(wrp_i_mid_mvm_exe_tok_cons_vld),
  .o_mid_mvm_exe_tok_cons_rdy(wrp_o_mid_mvm_exe_tok_cons_rdy),
  .i_mid_mvm_prg_tok_prod_vld(wrp_i_mid_mvm_prg_tok_prod_vld),
  .o_mid_mvm_prg_tok_prod_rdy(wrp_o_mid_mvm_prg_tok_prod_rdy),
  .o_mid_mvm_prg_tok_cons_vld(wrp_o_mid_mvm_prg_tok_cons_vld),
  .i_mid_mvm_prg_tok_cons_rdy(wrp_i_mid_mvm_prg_tok_cons_rdy),
  .o_mid_mvm_prg_tok_prod_vld(wrp_o_mid_mvm_prg_tok_prod_vld),
  .i_mid_mvm_prg_tok_prod_rdy(wrp_i_mid_mvm_prg_tok_prod_rdy),
  .i_mid_mvm_prg_tok_cons_vld(wrp_i_mid_mvm_prg_tok_cons_vld),
  .o_mid_mvm_prg_tok_cons_rdy(wrp_o_mid_mvm_prg_tok_cons_rdy),
  .i_mid_iau_tok_prod_vld(wrp_i_mid_iau_tok_prod_vld),
  .o_mid_iau_tok_prod_rdy(wrp_o_mid_iau_tok_prod_rdy),
  .o_mid_iau_tok_cons_vld(wrp_o_mid_iau_tok_cons_vld),
  .i_mid_iau_tok_cons_rdy(wrp_i_mid_iau_tok_cons_rdy),
  .o_mid_iau_tok_prod_vld(wrp_o_mid_iau_tok_prod_vld),
  .i_mid_iau_tok_prod_rdy(wrp_i_mid_iau_tok_prod_rdy),
  .i_mid_iau_tok_cons_vld(wrp_i_mid_iau_tok_cons_vld),
  .o_mid_iau_tok_cons_rdy(wrp_o_mid_iau_tok_cons_rdy),
  .i_mid_dpu_tok_prod_vld(wrp_i_mid_dpu_tok_prod_vld),
  .o_mid_dpu_tok_prod_rdy(wrp_o_mid_dpu_tok_prod_rdy),
  .o_mid_dpu_tok_cons_vld(wrp_o_mid_dpu_tok_cons_vld),
  .i_mid_dpu_tok_cons_rdy(wrp_i_mid_dpu_tok_cons_rdy),
  .o_mid_dpu_tok_prod_vld(wrp_o_mid_dpu_tok_prod_vld),
  .i_mid_dpu_tok_prod_rdy(wrp_i_mid_dpu_tok_prod_rdy),
  .i_mid_dpu_tok_cons_vld(wrp_i_mid_dpu_tok_cons_vld),
  .o_mid_dpu_tok_cons_rdy(wrp_o_mid_dpu_tok_cons_rdy),
  .i_mid_irq(wrp_i_mid_irq),
  .o_mid_irq(wrp_o_mid_irq),
  .i_mid_mvm_exe_obs(wrp_i_mid_mvm_exe_obs),
  .i_mid_mvm_prg_obs(wrp_i_mid_mvm_prg_obs),
  .i_mid_iau_obs(wrp_i_mid_iau_obs),
  .i_mid_dpu_obs(wrp_i_mid_dpu_obs),
  .i_mid_tu_obs(wrp_i_mid_tu_obs),
  .o_mid_mvm_exe_obs(wrp_o_mid_mvm_exe_obs),
  .o_mid_mvm_prg_obs(wrp_o_mid_mvm_prg_obs),
  .o_mid_iau_obs(wrp_o_mid_iau_obs),
  .o_mid_dpu_obs(wrp_o_mid_dpu_obs),
  .o_mid_tu_obs(wrp_o_mid_tu_obs),
  .i_mid_ts_start(wrp_i_mid_ts_start),
  .i_mid_ts_end(wrp_i_mid_ts_end),
  .i_mid_acd_sync(wrp_i_mid_acd_sync),
  .o_mid_ts_start(wrp_o_mid_ts_start),
  .o_mid_ts_end(wrp_o_mid_ts_end),
  .o_mid_acd_sync(wrp_o_mid_acd_sync),
  .i_did_dwpu_tok_prod_vld(wrp_i_did_dwpu_tok_prod_vld),
  .o_did_dwpu_tok_prod_rdy(wrp_o_did_dwpu_tok_prod_rdy),
  .o_did_dwpu_tok_cons_vld(wrp_o_did_dwpu_tok_cons_vld),
  .i_did_dwpu_tok_cons_rdy(wrp_i_did_dwpu_tok_cons_rdy),
  .o_did_dwpu_tok_prod_vld(wrp_o_did_dwpu_tok_prod_vld),
  .i_did_dwpu_tok_prod_rdy(wrp_i_did_dwpu_tok_prod_rdy),
  .i_did_dwpu_tok_cons_vld(wrp_i_did_dwpu_tok_cons_vld),
  .o_did_dwpu_tok_cons_rdy(wrp_o_did_dwpu_tok_cons_rdy),
  .i_did_iau_tok_prod_vld(wrp_i_did_iau_tok_prod_vld),
  .o_did_iau_tok_prod_rdy(wrp_o_did_iau_tok_prod_rdy),
  .o_did_iau_tok_cons_vld(wrp_o_did_iau_tok_cons_vld),
  .i_did_iau_tok_cons_rdy(wrp_i_did_iau_tok_cons_rdy),
  .o_did_iau_tok_prod_vld(wrp_o_did_iau_tok_prod_vld),
  .i_did_iau_tok_prod_rdy(wrp_i_did_iau_tok_prod_rdy),
  .i_did_iau_tok_cons_vld(wrp_i_did_iau_tok_cons_vld),
  .o_did_iau_tok_cons_rdy(wrp_o_did_iau_tok_cons_rdy),
  .i_did_dpu_tok_prod_vld(wrp_i_did_dpu_tok_prod_vld),
  .o_did_dpu_tok_prod_rdy(wrp_o_did_dpu_tok_prod_rdy),
  .o_did_dpu_tok_cons_vld(wrp_o_did_dpu_tok_cons_vld),
  .i_did_dpu_tok_cons_rdy(wrp_i_did_dpu_tok_cons_rdy),
  .o_did_dpu_tok_prod_vld(wrp_o_did_dpu_tok_prod_vld),
  .i_did_dpu_tok_prod_rdy(wrp_i_did_dpu_tok_prod_rdy),
  .i_did_dpu_tok_cons_vld(wrp_i_did_dpu_tok_cons_vld),
  .o_did_dpu_tok_cons_rdy(wrp_o_did_dpu_tok_cons_rdy),
  .i_did_irq(wrp_i_did_irq),
  .o_did_irq(wrp_o_did_irq),
  .i_did_dwpu_obs(wrp_i_did_dwpu_obs),
  .i_did_iau_obs(wrp_i_did_iau_obs),
  .i_did_dpu_obs(wrp_i_did_dpu_obs),
  .o_did_dwpu_obs(wrp_o_did_dwpu_obs),
  .o_did_iau_obs(wrp_o_did_iau_obs),
  .o_did_dpu_obs(wrp_o_did_dpu_obs),
  .i_did_ts_start(wrp_i_did_ts_start),
  .i_did_ts_end(wrp_i_did_ts_end),
  .i_did_acd_sync(wrp_i_did_acd_sync),
  .o_did_ts_start(wrp_o_did_ts_start),
  .o_did_ts_end(wrp_o_did_ts_end),
  .o_did_acd_sync(wrp_o_did_acd_sync),
  .o_mid_cfg_axi_m_awvalid(wrp_o_mid_cfg_axi_m_awvalid),
  .o_mid_cfg_axi_m_awaddr(wrp_o_mid_cfg_axi_m_aw.addr),
  .o_mid_cfg_axi_m_awid(wrp_o_mid_cfg_axi_m_aw.id),
  .o_mid_cfg_axi_m_awlen(wrp_o_mid_cfg_axi_m_aw.len),
  .o_mid_cfg_axi_m_awsize(wrp_o_mid_cfg_axi_m_aw.size),
  .o_mid_cfg_axi_m_awburst(wrp_o_mid_cfg_axi_m_aw.burst),
  .i_mid_cfg_axi_m_awready(wrp_i_mid_cfg_axi_m_awready),
  .o_mid_cfg_axi_m_wvalid(wrp_o_mid_cfg_axi_m_wvalid),
  .o_mid_cfg_axi_m_wlast(wrp_o_mid_cfg_axi_m_wdata.last),
  .o_mid_cfg_axi_m_wstrb(wrp_o_mid_cfg_axi_m_wdata.strb),
  .o_mid_cfg_axi_m_wdata(wrp_o_mid_cfg_axi_m_wdata.data),
  .i_mid_cfg_axi_m_wready(wrp_i_mid_cfg_axi_m_wready),
  .i_mid_cfg_axi_m_bvalid(wrp_i_mid_cfg_axi_m_bvalid),
  .i_mid_cfg_axi_m_bid(wrp_i_mid_cfg_axi_m_bresp.id),
  .i_mid_cfg_axi_m_bresp(wrp_i_mid_cfg_axi_m_bresp.resp),
  .o_mid_cfg_axi_m_bready(wrp_o_mid_cfg_axi_m_bready),
  .o_mid_cfg_axi_m_arvalid(wrp_o_mid_cfg_axi_m_arvalid),
  .o_mid_cfg_axi_m_araddr(wrp_o_mid_cfg_axi_m_ar.addr),
  .o_mid_cfg_axi_m_arid(wrp_o_mid_cfg_axi_m_ar.id),
  .o_mid_cfg_axi_m_arlen(wrp_o_mid_cfg_axi_m_ar.len),
  .o_mid_cfg_axi_m_arsize(wrp_o_mid_cfg_axi_m_ar.size),
  .o_mid_cfg_axi_m_arburst(wrp_o_mid_cfg_axi_m_ar.burst),
  .i_mid_cfg_axi_m_arready(wrp_i_mid_cfg_axi_m_arready),
  .i_mid_cfg_axi_m_rvalid(wrp_i_mid_cfg_axi_m_rvalid),
  .i_mid_cfg_axi_m_rlast(wrp_i_mid_cfg_axi_m_rdata.last),
  .i_mid_cfg_axi_m_rid(wrp_i_mid_cfg_axi_m_rdata.id),
  .i_mid_cfg_axi_m_rdata(wrp_i_mid_cfg_axi_m_rdata.data),
  .i_mid_cfg_axi_m_rresp(wrp_i_mid_cfg_axi_m_rdata.resp),
  .o_mid_cfg_axi_m_rready(wrp_o_mid_cfg_axi_m_rready),
  .o_did_cfg_axi_m_awvalid(wrp_o_did_cfg_axi_m_awvalid),
  .o_did_cfg_axi_m_awaddr(wrp_o_did_cfg_axi_m_aw.addr),
  .o_did_cfg_axi_m_awid(wrp_o_did_cfg_axi_m_aw.id),
  .o_did_cfg_axi_m_awlen(wrp_o_did_cfg_axi_m_aw.len),
  .o_did_cfg_axi_m_awsize(wrp_o_did_cfg_axi_m_aw.size),
  .o_did_cfg_axi_m_awburst(wrp_o_did_cfg_axi_m_aw.burst),
  .i_did_cfg_axi_m_awready(wrp_i_did_cfg_axi_m_awready),
  .o_did_cfg_axi_m_wvalid(wrp_o_did_cfg_axi_m_wvalid),
  .o_did_cfg_axi_m_wlast(wrp_o_did_cfg_axi_m_wdata.last),
  .o_did_cfg_axi_m_wstrb(wrp_o_did_cfg_axi_m_wdata.strb),
  .o_did_cfg_axi_m_wdata(wrp_o_did_cfg_axi_m_wdata.data),
  .i_did_cfg_axi_m_wready(wrp_i_did_cfg_axi_m_wready),
  .i_did_cfg_axi_m_bvalid(wrp_i_did_cfg_axi_m_bvalid),
  .i_did_cfg_axi_m_bid(wrp_i_did_cfg_axi_m_bresp.id),
  .i_did_cfg_axi_m_bresp(wrp_i_did_cfg_axi_m_bresp.resp),
  .o_did_cfg_axi_m_bready(wrp_o_did_cfg_axi_m_bready),
  .o_did_cfg_axi_m_arvalid(wrp_o_did_cfg_axi_m_arvalid),
  .o_did_cfg_axi_m_araddr(wrp_o_did_cfg_axi_m_ar.addr),
  .o_did_cfg_axi_m_arid(wrp_o_did_cfg_axi_m_ar.id),
  .o_did_cfg_axi_m_arlen(wrp_o_did_cfg_axi_m_ar.len),
  .o_did_cfg_axi_m_arsize(wrp_o_did_cfg_axi_m_ar.size),
  .o_did_cfg_axi_m_arburst(wrp_o_did_cfg_axi_m_ar.burst),
  .i_did_cfg_axi_m_arready(wrp_i_did_cfg_axi_m_arready),
  .i_did_cfg_axi_m_rvalid(wrp_i_did_cfg_axi_m_rvalid),
  .i_did_cfg_axi_m_rlast(wrp_i_did_cfg_axi_m_rdata.last),
  .i_did_cfg_axi_m_rid(wrp_i_did_cfg_axi_m_rdata.id),
  .i_did_cfg_axi_m_rdata(wrp_i_did_cfg_axi_m_rdata.data),
  .i_did_cfg_axi_m_rresp(wrp_i_did_cfg_axi_m_rdata.resp),
  .o_did_cfg_axi_m_rready(wrp_o_did_cfg_axi_m_rready),
  .i_sram_mcs(i_sram_mcs),
  .i_sram_mcsw(i_sram_mcsw),
  .i_sram_ret(i_sram_ret),
  .i_sram_pde(i_sram_pde),
  .i_sram_se(scan_en),
  .i_sram_adme(i_sram_adme),
  .o_sram_prn(o_sram_prn),
  .i_rf_mcs(i_rf_mcs),
  .i_rf_mcsw(i_rf_mcsw),
  .i_rf_ret(i_rf_ret),
  .i_rf_pde(i_rf_pde),
  .i_rf_se(scan_en),
  .i_rf_adme(i_rf_adme),
  .o_rf_prn(o_rf_prn)
  );


endmodule
