// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>
//        Luyi <yi.lu@axelera.ai>

/// AIC infra, containing fabric, CVA6, DMA's etc
///
module aic_infra #(
  localparam int unsigned RvvPortSizeWidth = $clog2(cva6v_ai_core_pkg::MemPortBeWidth)
)(
  /// Clock, positive edge triggered
  input wire i_clk,
  /// Asynchronous reset, active low
  input wire i_rst_n,

  input logic i_scan_en,

  input logic [aic_common_pkg::AIC_CID_WIDTH-1:0] i_cid,  // ID of AI Core

  input logic i_inter_core_sync,

  input logic i_thermal_warning_async,

  output logic [4:0] o_reserved,  // backup pins for HOTFIX
  input  logic [4:0] i_reserved,  // backup pins for HOTFIX

  //--------------------------------------------------
  // Obervability
  //--------------------------------------------------
  input  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_mvm_exe_obs,
  input  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_mvm_prg_obs,
  input  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_m_iau_obs,
  input  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_m_dpu_obs,
  input  logic [aic_common_pkg::AIC_TU_OBS_DW-1:0]  i_tu_obs,
  input  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_dwpu_obs,
  input  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_d_iau_obs,
  input  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_d_dpu_obs,
  input  logic [aic_common_pkg::AIC_DMC_OBS_DW-1:0] i_dmc_obs,
  output logic [aic_common_pkg::AIC_OBS_DW-1:0]     o_aic_obs,    // ai_core observability pins

  ///// Timestamp:
  input logic [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] i_dmc_ts_start,
  input logic [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] i_dmc_ts_end,
  input logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] i_did_ts_start,
  input logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] i_did_ts_end,
  input logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] i_mid_ts_start,
  input logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] i_mid_ts_end,
  ///// ACD sync:
  input logic [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] i_dmc_acd_sync,
  input logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] i_did_acd_sync,
  input logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] i_mid_acd_sync,

  // // infra AXI HP dlock
  // output logic [11:0] infra_hp_dlock,
  // // infra AXI LP dlock
  // output logic [13:0] infra_lp_dlock,

  ////////////////////////////////////////
  // CVA6 Core ctrl and debug interface //
  ////////////////////////////////////////
  input  logic [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_cva6v_boot_addr,
  input  logic                                             i_cva6v_debug_req_async,
  input  logic                                             i_cva6v_debug_rst_halt_req_async,
  output logic                                             o_cva6v_debug_stop_time_async,
  output logic                                             o_cva6v_hart_unavail_async,
  output logic                                             o_cva6v_hart_under_reset_async,

  input logic                                              i_mtip_async,
  input logic                                              i_msip_async,

  // RVV part:
    // 0
  output logic                                           o_rvv_0_req_valid,
  input  logic                                           i_rvv_0_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_0_req_addr,
  output logic                                           o_rvv_0_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_0_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_0_req_wdata,
  input  logic                                           i_rvv_0_res_valid,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_0_res_rdata,
  input  logic                                           i_rvv_0_res_err,
    // 0
  output logic                                           o_rvv_1_req_valid,
  input  logic                                           i_rvv_1_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_1_req_addr,
  output logic                                           o_rvv_1_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_1_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_1_req_wdata,
  input  logic                                           i_rvv_1_res_valid,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_1_res_rdata,
  input  logic                                           i_rvv_1_res_err,
    // 2
  output logic                                           o_rvv_2_req_valid,
  input  logic                                           i_rvv_2_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_2_req_addr,
  output logic                                           o_rvv_2_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_2_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_2_req_wdata,
  input  logic                                           i_rvv_2_res_valid,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_2_res_rdata,
  input  logic                                           i_rvv_2_res_err,
    // 3
  output logic                                           o_rvv_3_req_valid,
  input  logic                                           i_rvv_3_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_3_req_addr,
  output logic                                           o_rvv_3_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_3_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_3_req_wdata,
  input  logic                                           i_rvv_3_res_valid,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_3_res_rdata,
  input  logic                                           i_rvv_3_res_err,
    // 4
  output logic                                           o_rvv_4_req_valid,
  input  logic                                           i_rvv_4_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_4_req_addr,
  output logic                                           o_rvv_4_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_4_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_4_req_wdata,
  input  logic                                           i_rvv_4_res_valid,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_4_res_rdata,
  input  logic                                           i_rvv_4_res_err,
    // 5
  output logic                                           o_rvv_5_req_valid,
  input  logic                                           i_rvv_5_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_5_req_addr,
  output logic                                           o_rvv_5_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_5_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_5_req_wdata,
  input  logic                                           i_rvv_5_res_valid,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_5_res_rdata,
  input  logic                                           i_rvv_5_res_err,
    // 6
  output logic                                           o_rvv_6_req_valid,
  input  logic                                           i_rvv_6_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_6_req_addr,
  output logic                                           o_rvv_6_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_6_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_6_req_wdata,
  input  logic                                           i_rvv_6_res_valid,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_6_res_rdata,
  input  logic                                           i_rvv_6_res_err,
    // 7
  output logic                                           o_rvv_7_req_valid,
  input  logic                                           i_rvv_7_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_7_req_addr,
  output logic                                           o_rvv_7_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_7_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_7_req_wdata,
  input  logic                                           i_rvv_7_res_valid,
  input  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_7_res_rdata,
  input  logic                                           i_rvv_7_res_err,

  //--------------------------------------------------
  // Token OCP L
  //--------------------------------------------------
  output chip_pkg::chip_ocpl_token_addr_t o_tok_prod_ocpl_m_maddr,
  output logic                            o_tok_prod_ocpl_m_mcmd,
  input  logic                            i_tok_prod_ocpl_m_scmdaccept,
  output chip_pkg::chip_ocpl_token_data_t o_tok_prod_ocpl_m_mdata,
  input  chip_pkg::chip_ocpl_token_addr_t i_tok_cons_ocpl_s_maddr,
  input  logic                            i_tok_cons_ocpl_s_mcmd,
  output logic                            o_tok_cons_ocpl_s_scmdaccept,
  input  chip_pkg::chip_ocpl_token_data_t i_tok_cons_ocpl_s_mdata,


  //--------------------------------------------------
  // IRQ ai_core subips
  //--------------------------------------------------
  input logic [dmc_pkg::DMC_IRQ_W-1:0]    i_irq_dmc,
  input logic [aic_mid_pkg::NUM_IRQS-1:0] i_irq_aic_mid,
  input logic [2:0]                       i_irq_aic_did,

  //--------------------------------------------------
  // Tokens ai_core subips
  //--------------------------------------------------
  // DMC
    // M IFD0
  input  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifd0_tok_prod_vld,
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifd0_tok_prod_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifd0_tok_cons_vld,
  input  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifd0_tok_cons_rdy,
    // M IFD1
  input  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifd1_tok_prod_vld,
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifd1_tok_prod_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifd1_tok_cons_vld,
  input  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifd1_tok_cons_rdy,
    // M IFD2
  input  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifd2_tok_prod_vld,
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifd2_tok_prod_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifd2_tok_cons_vld,
  input  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifd2_tok_cons_rdy,
    // M IFDW
  input  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifdw_tok_prod_vld,
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifdw_tok_prod_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifdw_tok_cons_vld,
  input  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifdw_tok_cons_rdy,
    // D IFD0
  input  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_d_ifd0_tok_prod_vld,
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_d_ifd0_tok_prod_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_d_ifd0_tok_cons_vld,
  input  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_d_ifd0_tok_cons_rdy,
    // D IFD1
  input  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_d_ifd1_tok_prod_vld,
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_d_ifd1_tok_prod_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_d_ifd1_tok_cons_vld,
  input  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_d_ifd1_tok_cons_rdy,
    // ODR:
    // M ODR
  input  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_odr_tok_prod_vld,
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_odr_tok_prod_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_odr_tok_cons_vld,
  input  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_odr_tok_cons_rdy,
    // D ODR:
  input  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_d_odr_tok_prod_vld,
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_d_odr_tok_prod_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_d_odr_tok_cons_vld,
  input  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_d_odr_tok_cons_rdy,

  // MVM EXE
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] i_mvm_exe_tok_prod_vld,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] o_mvm_exe_tok_prod_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] o_mvm_exe_tok_cons_vld,
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] i_mvm_exe_tok_cons_rdy,

  // MVM PRG
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] i_mvm_prg_tok_prod_vld,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] o_mvm_prg_tok_prod_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] o_mvm_prg_tok_cons_vld,
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] i_mvm_prg_tok_cons_rdy,

  // M_IAU
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD-1:0] i_m_iau_tok_prod_vld,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD-1:0] o_m_iau_tok_prod_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS-1:0] o_m_iau_tok_cons_vld,
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS-1:0] i_m_iau_tok_cons_rdy,

  // M_DPU
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD-1:0] i_m_dpu_tok_prod_vld,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD-1:0] o_m_dpu_tok_prod_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS-1:0] o_m_dpu_tok_cons_vld,
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS-1:0] i_m_dpu_tok_cons_rdy,

  // DWPU
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_dwpu_tok_prod_vld,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] o_dwpu_tok_prod_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] o_dwpu_tok_cons_vld,
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] i_dwpu_tok_cons_rdy,

  // D_IAU
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_d_iau_tok_prod_vld,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] o_d_iau_tok_prod_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] o_d_iau_tok_cons_vld,
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_d_iau_tok_cons_rdy,

  // D_DPU
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_d_dpu_tok_prod_vld,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD-1:0] o_d_dpu_tok_prod_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS-1:0] o_d_dpu_tok_cons_vld,
  input  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_d_dpu_tok_cons_rdy,

  //--------------------------------------------------
  // L1 related
  //--------------------------------------------------

  //--------------------------------------------------
  // AXI HT NOC
  //--------------------------------------------------
  // AXI write address channel
  output logic                                                   o_noc_ht_axi_m_awvalid,
  output logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_noc_ht_axi_m_awaddr,
  output logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_noc_ht_axi_m_awid,
  output logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_noc_ht_axi_m_awlen,
  output logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_awsize,
  output logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_awburst,
  output logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_awcache,
  output logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_awprot,
  output logic                                                   o_noc_ht_axi_m_awlock,
  input  logic                                                   i_noc_ht_axi_m_awready,
  // AXI write data channel
  output logic                                                   o_noc_ht_axi_m_wvalid,
  output logic                                                   o_noc_ht_axi_m_wlast,
  output logic [     aic_common_pkg::AIC_HT_AXI_WSTRB_WIDTH-1:0] o_noc_ht_axi_m_wstrb,
  output logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] o_noc_ht_axi_m_wdata,
  input  logic                                                   i_noc_ht_axi_m_wready,
  // AXI write response channel
  input  logic                                                   i_noc_ht_axi_m_bvalid,
  input  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_noc_ht_axi_m_bid,
  input  logic [      aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_bresp,
  output logic                                                   o_noc_ht_axi_m_bready,
  // AXI read address channel
  output logic                                                   o_noc_ht_axi_m_arvalid,
  output logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_noc_ht_axi_m_araddr,
  output logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_noc_ht_axi_m_arid,
  output logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_noc_ht_axi_m_arlen,
  output logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_arsize,
  output logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_arburst,
  output logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_arcache,
  output logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_arprot,
  output logic                                                   o_noc_ht_axi_m_arlock,
  input  logic                                                   i_noc_ht_axi_m_arready,
  // AXI read data/response channel
  input  logic                                                   i_noc_ht_axi_m_rvalid,
  input  logic                                                   i_noc_ht_axi_m_rlast,
  input  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_noc_ht_axi_m_rid,
  input  logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] i_noc_ht_axi_m_rdata,
  input  logic [      aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_rresp,
  output logic                                                   o_noc_ht_axi_m_rready,

  //--------------------------------------------------
  // AXI HT DMC_L1
  //--------------------------------------------------
  // AXI write address channel
  output logic                                                   o_dmc_l1_ht_axi_m_awvalid,
  output logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_ht_axi_m_awaddr,
  output logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_ht_axi_m_awid,
  output logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_dmc_l1_ht_axi_m_awlen,
  output logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_ht_axi_m_awsize,
  output logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_ht_axi_m_awburst,
  output logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_dmc_l1_ht_axi_m_awcache,
  output logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_dmc_l1_ht_axi_m_awprot,
  output logic                                                   o_dmc_l1_ht_axi_m_awlock,
  input  logic                                                   i_dmc_l1_ht_axi_m_awready,
  // AXI write data channel
  output logic                                                   o_dmc_l1_ht_axi_m_wvalid,
  output logic                                                   o_dmc_l1_ht_axi_m_wlast,
  output logic [     aic_common_pkg::AIC_HT_AXI_WSTRB_WIDTH-1:0] o_dmc_l1_ht_axi_m_wstrb,
  output logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] o_dmc_l1_ht_axi_m_wdata,
  input  logic                                                   i_dmc_l1_ht_axi_m_wready,
  // AXI write response channel
  input  logic                                                   i_dmc_l1_ht_axi_m_bvalid,
  input  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_ht_axi_m_bid,
  input  logic [      aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_dmc_l1_ht_axi_m_bresp,
  output logic                                                   o_dmc_l1_ht_axi_m_bready,
  // AXI read address channel
  output logic                                                   o_dmc_l1_ht_axi_m_arvalid,
  output logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_ht_axi_m_araddr,
  output logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_ht_axi_m_arid,
  output logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_dmc_l1_ht_axi_m_arlen,
  output logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_ht_axi_m_arsize,
  output logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_ht_axi_m_arburst,
  output logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_dmc_l1_ht_axi_m_arcache,
  output logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_dmc_l1_ht_axi_m_arprot,
  output logic                                                   o_dmc_l1_ht_axi_m_arlock,
  input  logic                                                   i_dmc_l1_ht_axi_m_arready,
  // AXI read data/response channel
  input  logic                                                   i_dmc_l1_ht_axi_m_rvalid,
  input  logic                                                   i_dmc_l1_ht_axi_m_rlast,
  input  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_ht_axi_m_rid,
  input  logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] i_dmc_l1_ht_axi_m_rdata,
  input  logic [      aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_dmc_l1_ht_axi_m_rresp,
  output logic                                                   o_dmc_l1_ht_axi_m_rready,

  //--------------------------------------------------
  // AXI LT NOC S
  //--------------------------------------------------
  // AXI write address channel
  input  logic                                                   i_noc_lt_axi_s_awvalid,
  input  logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_noc_lt_axi_s_awaddr,
  input  logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] i_noc_lt_axi_s_awid,
  input  logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] i_noc_lt_axi_s_awlen,
  input  logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_awsize,
  input  logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_awburst,
  input  logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_awcache,
  input  logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_awprot,
  input  logic                                                   i_noc_lt_axi_s_awlock,
  output logic                                                   o_noc_lt_axi_s_awready,
  // AXI write data channel
  input  logic                                                   i_noc_lt_axi_s_wvalid,
  input  logic                                                   i_noc_lt_axi_s_wlast,
  input  logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] i_noc_lt_axi_s_wstrb,
  input  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_noc_lt_axi_s_wdata,
  output logic                                                   o_noc_lt_axi_s_wready,
  // AXI write response channel
  output logic                                                   o_noc_lt_axi_s_bvalid,
  output logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] o_noc_lt_axi_s_bid,
  output logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_bresp,
  input  logic                                                   i_noc_lt_axi_s_bready,
  // AXI read address channel
  input  logic                                                   i_noc_lt_axi_s_arvalid,
  input  logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_noc_lt_axi_s_araddr,
  input  logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] i_noc_lt_axi_s_arid,
  input  logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] i_noc_lt_axi_s_arlen,
  input  logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_arsize,
  input  logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_arburst,
  input  logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_arcache,
  input  logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_arprot,
  input  logic                                                   i_noc_lt_axi_s_arlock,
  output logic                                                   o_noc_lt_axi_s_arready,
  // AXI read data/response channel
  output logic                                                   o_noc_lt_axi_s_rvalid,
  output logic                                                   o_noc_lt_axi_s_rlast,
  output logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] o_noc_lt_axi_s_rid,
  output logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_noc_lt_axi_s_rdata,
  output logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_rresp,
  input  logic                                                   i_noc_lt_axi_s_rready,

  //--------------------------------------------------
  // AXI LT NOC M
  //--------------------------------------------------
  // AXI write address channel
  output logic                                                   o_noc_lt_axi_m_awvalid,
  output logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_noc_lt_axi_m_awaddr,
  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_noc_lt_axi_m_awid,
  output logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_noc_lt_axi_m_awlen,
  output logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_awsize,
  output logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_awburst,
  output logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_awcache,
  output logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_awprot,
  output logic                                                   o_noc_lt_axi_m_awlock,
  input  logic                                                   i_noc_lt_axi_m_awready,
  // AXI write data channel
  output logic                                                   o_noc_lt_axi_m_wvalid,
  output logic                                                   o_noc_lt_axi_m_wlast,
  output logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] o_noc_lt_axi_m_wstrb,
  output logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_noc_lt_axi_m_wdata,
  input  logic                                                   i_noc_lt_axi_m_wready,
  // AXI write response channel
  input  logic                                                   i_noc_lt_axi_m_bvalid,
  input  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_noc_lt_axi_m_bid,
  input  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_bresp,
  output logic                                                   o_noc_lt_axi_m_bready,
  // AXI read address channel
  output logic                                                   o_noc_lt_axi_m_arvalid,
  output logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_noc_lt_axi_m_araddr,
  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_noc_lt_axi_m_arid,
  output logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_noc_lt_axi_m_arlen,
  output logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_arsize,
  output logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_arburst,
  output logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_arcache,
  output logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_arprot,
  output logic                                                   o_noc_lt_axi_m_arlock,
  input  logic                                                   i_noc_lt_axi_m_arready,
  // AXI read data/response channel
  input  logic                                                   i_noc_lt_axi_m_rvalid,
  input  logic                                                   i_noc_lt_axi_m_rlast,
  input  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_noc_lt_axi_m_rid,
  input  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_noc_lt_axi_m_rdata,
  input  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_rresp,
  output logic                                                   o_noc_lt_axi_m_rready,


  //--------------------------------------------------
  // AXI DMC L1 M
  //--------------------------------------------------
  // AXI write address channel
  output logic                                                   o_dmc_l1_lt_axi_m_awvalid,
  output logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_lt_axi_m_awaddr,
  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_lt_axi_m_awid,
  output logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_dmc_l1_lt_axi_m_awlen,
  output logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_lt_axi_m_awsize,
  output logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_lt_axi_m_awburst,
  input  logic                                                   i_dmc_l1_lt_axi_m_awready,
  // AXI write data channel
  output logic                                                   o_dmc_l1_lt_axi_m_wvalid,
  output logic                                                   o_dmc_l1_lt_axi_m_wlast,
  output logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] o_dmc_l1_lt_axi_m_wstrb,
  output logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_dmc_l1_lt_axi_m_wdata,
  input  logic                                                   i_dmc_l1_lt_axi_m_wready,
  // AXI write response channel
  input  logic                                                   i_dmc_l1_lt_axi_m_bvalid,
  input  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_lt_axi_m_bid,
  input  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_dmc_l1_lt_axi_m_bresp,
  output logic                                                   o_dmc_l1_lt_axi_m_bready,
  // AXI read address channel
  output logic                                                   o_dmc_l1_lt_axi_m_arvalid,
  output logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_lt_axi_m_araddr,
  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_lt_axi_m_arid,
  output logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_dmc_l1_lt_axi_m_arlen,
  output logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_lt_axi_m_arsize,
  output logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_lt_axi_m_arburst,
  input  logic                                                   i_dmc_l1_lt_axi_m_arready,
  // AXI read data/response channel
  input  logic                                                   i_dmc_l1_lt_axi_m_rvalid,
  input  logic                                                   i_dmc_l1_lt_axi_m_rlast,
  input  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_lt_axi_m_rid,
  input  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_dmc_l1_lt_axi_m_rdata,
  input  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_dmc_l1_lt_axi_m_rresp,
  output logic                                                   o_dmc_l1_lt_axi_m_rready,

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
  output logic       o_sram_prn
);

  axe_tcl_sram_pkg::impl_inp_t                                    mem_impl_inp;
  axe_tcl_sram_pkg::impl_oup_t                                    mem_impl_oup;
  axe_tcl_sram_pkg::impl_inp_t [aic_infra_pkg::NUM_SRAM_IMPL-1:0] sram_impl_inp;
  axe_tcl_sram_pkg::impl_oup_t [aic_infra_pkg::NUM_SRAM_IMPL-1:0] sram_impl_oup;

  always_comb mem_impl_inp = '{
      mcs:  i_sram_mcs,
      mcsw: i_sram_mcsw,
      ret:  i_sram_ret,
      pde:  i_sram_pde,
      se:   i_sram_se,
      adme: i_sram_adme
    };
  always_comb o_sram_prn = mem_impl_oup.prn;

  axe_tcl_sram_cfg #(
    .NUM_SRAMS(aic_infra_pkg::NUM_SRAM_IMPL)
  ) u_sram_cfg (
    .i_s(mem_impl_inp),
    .o_s(mem_impl_oup),
    .o_m(sram_impl_inp),
    .i_m(sram_impl_oup)
  );

  ///////////// (extra) shielding:
  ///// Timestamp flop:
  logic [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] dmc_ts_start_q;
  logic [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] dmc_ts_end_q;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] did_ts_start_q;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] did_ts_end_q;
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] mid_ts_start_q;
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] mid_ts_end_q;
  ///// ACD sync flop:
  logic [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] dmc_acd_sync_q;
  logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] did_acd_sync_q;
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] mid_acd_sync_q;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_ts_sync_del
    if (i_rst_n == 1'b0) begin
      dmc_ts_start_q <= '0;
      dmc_ts_end_q <= '0;
      did_ts_start_q <= '0;
      did_ts_end_q <= '0;
      mid_ts_start_q <= '0;
      mid_ts_end_q <= '0;
      dmc_acd_sync_q <= '0;
      did_acd_sync_q <= '0;
      mid_acd_sync_q <= '0;
    end else begin
      if (dmc_ts_start_q != i_dmc_ts_start) dmc_ts_start_q <= i_dmc_ts_start;
      if (dmc_ts_end_q != i_dmc_ts_end) dmc_ts_end_q <= i_dmc_ts_end;
      if (did_ts_start_q != i_did_ts_start) did_ts_start_q <= i_did_ts_start;
      if (did_ts_end_q != i_did_ts_end) did_ts_end_q <= i_did_ts_end;
      if (mid_ts_start_q != i_mid_ts_start) mid_ts_start_q <= i_mid_ts_start;
      if (mid_ts_end_q != i_mid_ts_end) mid_ts_end_q <= i_mid_ts_end;
      if (dmc_acd_sync_q != i_dmc_acd_sync) dmc_acd_sync_q <= i_dmc_acd_sync;
      if (did_acd_sync_q != i_did_acd_sync) did_acd_sync_q <= i_did_acd_sync;
      if (mid_acd_sync_q != i_mid_acd_sync) mid_acd_sync_q <= i_mid_acd_sync;
    end
  end
  // obs:
  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] mvm_exe_obs_q;
  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] mvm_prg_obs_q;
  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] m_iau_obs_q;
  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] m_dpu_obs_q;
  logic [aic_common_pkg::AIC_TU_OBS_DW-1:0]  tu_obs_q;
  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] dwpu_obs_q;
  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] d_iau_obs_q;
  logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] d_dpu_obs_q;
  logic [aic_common_pkg::AIC_DMC_OBS_DW-1:0] dmc_obs_q;
  logic [aic_common_pkg::AIC_OBS_DW-1:0] aic_obs_d, aic_obs_q;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin : u_obs_del
    if (i_rst_n == 1'b0) begin
      mvm_exe_obs_q <= '0;
      mvm_prg_obs_q <= '0;
      m_iau_obs_q <= '0;
      m_dpu_obs_q <= '0;
      tu_obs_q <= '0;
      dwpu_obs_q <= '0;
      d_iau_obs_q <= '0;
      d_dpu_obs_q <= '0;
      dmc_obs_q <= '0;
      aic_obs_q <= '0;
    end else begin
      if (mvm_exe_obs_q != i_mvm_exe_obs) mvm_exe_obs_q <= i_mvm_exe_obs;
      if (mvm_prg_obs_q != i_mvm_prg_obs) mvm_prg_obs_q <= i_mvm_prg_obs;
      if (m_iau_obs_q != i_m_iau_obs) m_iau_obs_q <= i_m_iau_obs;
      if (m_dpu_obs_q != i_m_dpu_obs) m_dpu_obs_q <= i_m_dpu_obs;
      if (tu_obs_q != i_tu_obs) tu_obs_q <= i_tu_obs;
      if (dwpu_obs_q != i_dwpu_obs) dwpu_obs_q <= i_dwpu_obs;
      if (d_iau_obs_q != i_d_iau_obs) d_iau_obs_q <= i_d_iau_obs;
      if (d_dpu_obs_q != i_d_dpu_obs) d_dpu_obs_q <= i_d_dpu_obs;
      if (dmc_obs_q != i_dmc_obs) dmc_obs_q <= i_dmc_obs;
      if (aic_obs_q != aic_obs_d) aic_obs_q <= aic_obs_d;
    end
  end
  always_comb o_aic_obs = aic_obs_q;

  ///////////// DMA specific signals
  ///// Tokens:
  localparam HT_DMA_MAX_NR_TOK_PROD = token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_PROD;
  localparam HT_DMA_MAX_NR_TOK_CONS = token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_CONS;
  if (token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_PROD != token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_NR_TOK_PROD)
    $fatal(1, "token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_PROD and token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_NR_TOK_PROD\
                  are expected to be the same");
  if (token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_CONS != token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_NR_TOK_CONS)
    $fatal(1, "token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_CONS and token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_NR_TOK_CONS\
                  are expected to be the same");

  logic [HT_DMA_MAX_NR_TOK_PROD-1:0]   ht_dma_tok_prod_vld[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [HT_DMA_MAX_NR_TOK_PROD-1:0]   ht_dma_tok_prod_rdy[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [HT_DMA_MAX_NR_TOK_CONS-1:0]   ht_dma_tok_cons_vld[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [HT_DMA_MAX_NR_TOK_CONS-1:0]   ht_dma_tok_cons_rdy[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];

  localparam DMA_NR_TOP_TOK_PROD = token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_PROD;
  localparam DMA_NR_TOP_TOK_CONS = token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_CONS;
  if (token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_PROD != token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_NR_TOK_PROD)
    $fatal(1, "token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_PROD and token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_NR_TOK_PROD\
                  are expected to be the same");
  if (token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_CONS != token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_NR_TOK_CONS)
    $fatal(1, "token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_CONS and token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_NR_TOK_CONS\
                  are expected to be the same");

  logic [DMA_NR_TOP_TOK_PROD-1:0]   ht_dma_top_tok_prod_vld[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [DMA_NR_TOP_TOK_PROD-1:0]   ht_dma_top_tok_prod_rdy[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [DMA_NR_TOP_TOK_CONS-1:0]   ht_dma_top_tok_cons_vld[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [DMA_NR_TOP_TOK_CONS-1:0]   ht_dma_top_tok_cons_rdy[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [HT_DMA_MAX_NR_TOK_PROD+DMA_NR_TOP_TOK_PROD-1:0]   ht_dma_all_prod_vld[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [HT_DMA_MAX_NR_TOK_PROD+DMA_NR_TOP_TOK_PROD-1:0]   ht_dma_all_prod_rdy[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [HT_DMA_MAX_NR_TOK_CONS+DMA_NR_TOP_TOK_CONS-1:0]   ht_dma_all_cons_vld[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];
  logic [HT_DMA_MAX_NR_TOK_CONS+DMA_NR_TOP_TOK_CONS-1:0]   ht_dma_all_cons_rdy[aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS];

  always_comb begin
    for (int unsigned ch=0; ch<aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS; ch++) begin
      {ht_dma_top_tok_prod_vld[ch], ht_dma_tok_prod_vld[ch]} = ht_dma_all_prod_vld[ch];
      ht_dma_all_prod_rdy[ch] = {ht_dma_top_tok_prod_rdy[ch], ht_dma_tok_prod_rdy[ch]};
      ht_dma_all_cons_vld[ch] = {ht_dma_top_tok_cons_vld[ch], ht_dma_tok_cons_vld[ch]};
      {ht_dma_top_tok_cons_rdy[ch], ht_dma_tok_cons_rdy[ch]} = ht_dma_all_cons_rdy[ch];
    end
  end

  logic [token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_PROD-1:0]                acd_top_tok_prod_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_PROD-1:0]                acd_top_tok_prod_rdy;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_CONS-1:0]                acd_top_tok_cons_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_CONS-1:0]                acd_top_tok_cons_rdy;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_CFG.nr_loc_devs-1:0]                        acd_tok_prod_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_CFG.nr_loc_devs-1:0]                        acd_tok_prod_rdy;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_CFG.nr_loc_devs-1:0]                        acd_tok_cons_vld;
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_CFG.nr_loc_devs-1:0]                        acd_tok_cons_rdy;

  ///// Timestamp:
  logic [aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS-1:0] ht_dma_ts_start;
  logic [aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS-1:0] ht_dma_ts_end;
  ///// ACD sync:
  logic [aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS-1:0] ht_dma_acd_sync;
  dma_pkg::dma_dev_obs_t [aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS-1:0] ht_dma_obs;

  //////////////////////////
  // internal signals
  //////////////////////////
  aic_csr_reg_pkg::aic_csr_reg2hw_t reg2hw;
  aic_csr_reg_pkg::aic_csr_hw2reg_t hw2reg;

  // Interrupts
  logic [aic_rv_plic_reg_pkg::NumSrc   -1:0] irq_sources;
  logic [aic_rv_plic_reg_pkg::NumTarget-1:0] irq_to_cva6;
  logic [aic_rv_plic_reg_pkg::NumTarget-1:0] irq_to_cva6_software;

  // Thermal Warning
  logic thermal_warning;

  axe_tcl_seq_sync #(
    .SyncStages( 3 ),
    .ResetValue(1'b0)
  ) u_global_sync_resync (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),
    .i_d    (i_thermal_warning_async),
    .o_q    (thermal_warning)
  );

  ///////////////////
  // Observability //
  ///////////////////
  aic_infra_observability_mux u_aic_infra_observability_mux (
    .i_clk,
    .i_rst_n,
    .i_obs_ctrl(reg2hw.obs_ctrl),
    .i_obs_rearange(reg2hw.obs_rearange),
    .i_sw_obs(reg2hw.sw_obs),
    .i_tu_obs(tu_obs_q),
    .i_mvm_exe_obs(mvm_exe_obs_q),
    .i_mvm_prg_obs(mvm_prg_obs_q),
    .i_m_iau_obs(m_iau_obs_q),
    .i_m_dpu_obs(m_dpu_obs_q),
    .i_dwpu_obs(dwpu_obs_q),
    .i_d_iau_obs(d_iau_obs_q),
    .i_d_dpu_obs(d_dpu_obs_q),
    .i_dmc_obs(dmc_obs_q),
    .i_dma_0_obs(ht_dma_obs[0]),
    .i_dma_1_obs(ht_dma_obs[1]),
    .o_aic_obs(aic_obs_d),
    .o_sw_obs_rd  (hw2reg.obs_sig)
  );

  ////////////////////
  // CVA6v INSTANCE //
  ////////////////////
  // Async section for the debug requests to get into this domain
  logic cva6v_debug_req;
  logic cva6v_debug_rst_halt_req;
  logic cva6v_mtip;
  logic cva6v_msip;

  axe_tcl_seq_sync #(
    .SyncStages(3),
    .ResetValue(1'b0)
  ) u_ai_core_cva6v_debug_req_sync (
    .i_clk,
    .i_rst_n,
    .i_d    (i_cva6v_debug_req_async),
    .o_q    (cva6v_debug_req)
  );

  axe_tcl_seq_sync #(
    .SyncStages(3),
    .ResetValue(1'b0)
  ) u_ai_core_cva6v_debug_rst_halt_req_sync (
    .i_clk,
    .i_rst_n,
    .i_d    (i_cva6v_debug_rst_halt_req_async),
    .o_q    (cva6v_debug_rst_halt_req)
  );

  axe_tcl_seq_sync #(
    .SyncStages(3),
    .ResetValue(1'b0)
  ) u_ai_core_cva6v_mtip_sync (
    .i_clk,
    .i_rst_n,
    .i_d    (i_mtip_async),
    .o_q    (cva6v_mtip)
  );

  axe_tcl_seq_sync #(
    .SyncStages(3),
    .ResetValue(1'b0)
  ) u_ai_core_cva6v_msip_sync (
    .i_clk,
    .i_rst_n,
    .i_d    (i_msip_async),
    .o_q    (cva6v_msip)
  );

  // Note: CVA6V has ID width 4
  cva6v_ai_core_pkg::axi_aw_chan_t axi_cva6v_aw;
  logic                            axi_cva6v_aw_valid;
  logic                            axi_cva6v_aw_ready;
  cva6v_ai_core_pkg::axi_w_chan_t  axi_cva6v_w;
  logic                            axi_cva6v_w_valid;
  logic                            axi_cva6v_w_ready;
  cva6v_ai_core_pkg::axi_b_chan_t  axi_cva6v_b;
  logic                            axi_cva6v_b_valid;
  logic                            axi_cva6v_b_ready;
  cva6v_ai_core_pkg::axi_ar_chan_t axi_cva6v_ar;
  logic                            axi_cva6v_ar_valid;
  logic                            axi_cva6v_ar_ready;
  cva6v_ai_core_pkg::axi_r_chan_t  axi_cva6v_r;
  logic                            axi_cva6v_r_valid;
  logic                            axi_cva6v_r_ready;


  aic_cva6v_pkg::aic_cva6v_perf_delta_t cva6v_perf_event_0_0_delta;
  aic_cva6v_pkg::aic_cva6v_perf_addr_t  cva6v_perf_event_0_addr;
  aic_cva6v_pkg::aic_cva6v_perf_delta_t cva6v_perf_event_1_0_delta;
  aic_cva6v_pkg::aic_cva6v_perf_addr_t  cva6v_perf_event_1_addr;

  aic_cva6v_pkg::aic_cva6v_paddr_t cva6v_memreg_default_addr[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];
  aic_cva6v_pkg::aic_cva6v_psize_t cva6v_memreg_default_size[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];
  logic                            cva6v_memreg_default_tcdm[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];

  // Note the cid matches the address map
  // Only use the local part, then extend it up again to match cva6v
  localparam aic_cva6v_pkg::aic_cva6v_paddr_t L1AddrBase =
      aic_cva6v_pkg::aic_cva6v_paddr_t'(aic_addr_map_pkg::loc_addr_t'(aic_addr_map_pkg::AIC_L1_ST_ADDR));
  localparam aic_cva6v_pkg::aic_cva6v_paddr_t L1AddrSize =
      aic_cva6v_pkg::aic_cva6v_paddr_t'(aic_addr_map_pkg::AIC_L1_END_ADDR - aic_addr_map_pkg::AIC_L1_ST_ADDR + 1);
  // Note questa: if always_comb is triggering internal error...
  assign cva6v_memreg_default_addr[0] = aic_cva6v_pkg::aic_cva6v_paddr_t'(i_cid << 28) | L1AddrBase;
  assign cva6v_memreg_default_size[0] = aic_cva6v_pkg::aic_cva6v_psize_t'($clog2(L1AddrSize / 2));
  assign cva6v_memreg_default_tcdm[0] = 1'b1;
  assign cva6v_memreg_default_addr[1] = aic_cva6v_pkg::aic_cva6v_paddr_t'(i_cid << 28) | (L1AddrBase + L1AddrSize/2);
  assign cva6v_memreg_default_size[1] = aic_cva6v_pkg::aic_cva6v_psize_t'($clog2(L1AddrSize / 2));
  assign cva6v_memreg_default_tcdm[1] = 1'b1;

  // To make PD happy, give an extra pipe
  aic_cva6v_pkg::aic_cva6v_paddr_t cva6v_memreg_addr_q[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];
  aic_cva6v_pkg::aic_cva6v_psize_t cva6v_memreg_size_q[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];
  logic                            cva6v_memreg_tcdm_q[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];

  logic cva6v_memreg_update[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];
  logic cva6v_memreg_use_csr_q[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];

  aic_cva6v_pkg::aic_cva6v_paddr_t cva6v_memreg_addr[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];
  aic_cva6v_pkg::aic_cva6v_psize_t cva6v_memreg_size[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];
  logic                            cva6v_memreg_tcdm[aic_csr_reg_pkg::CVA6V_MEMREG_NUM];

  for (genvar memreg_idx = 0; memreg_idx < aic_csr_reg_pkg::CVA6V_MEMREG_NUM; memreg_idx++) begin : gen_memreg
    always_comb cva6v_memreg_update[memreg_idx] = reg2hw.cva6v_memreg[memreg_idx].addr.qe
                                                | reg2hw.cva6v_memreg[memreg_idx].size.qe
                                                | reg2hw.cva6v_memreg[memreg_idx].tcdm.qe;

    always_comb cva6v_memreg_addr[memreg_idx] = cva6v_memreg_use_csr_q[memreg_idx] ? cva6v_memreg_addr_q[memreg_idx] : cva6v_memreg_default_addr[memreg_idx];
    always_comb cva6v_memreg_size[memreg_idx] = cva6v_memreg_use_csr_q[memreg_idx] ? cva6v_memreg_size_q[memreg_idx] : cva6v_memreg_default_size[memreg_idx];
    always_comb cva6v_memreg_tcdm[memreg_idx] = cva6v_memreg_use_csr_q[memreg_idx] ? cva6v_memreg_tcdm_q[memreg_idx] : cva6v_memreg_default_tcdm[memreg_idx];
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      for (int memreg_index = 0; memreg_index < aic_csr_reg_pkg::CVA6V_MEMREG_NUM; memreg_index++) begin
        cva6v_memreg_use_csr_q[memreg_index] <= 1'b0;
      end
    end else begin
      for (int memreg_index = 0; memreg_index < aic_csr_reg_pkg::CVA6V_MEMREG_NUM; memreg_index++) begin
        if (cva6v_memreg_update[memreg_index]) begin
          cva6v_memreg_use_csr_q[memreg_index] <= 1'b1;
          cva6v_memreg_addr_q[memreg_index]    <= reg2hw.cva6v_memreg[memreg_index].addr.q;
          cva6v_memreg_size_q[memreg_index]    <= reg2hw.cva6v_memreg[memreg_index].size.q;
          cva6v_memreg_tcdm_q[memreg_index]    <= reg2hw.cva6v_memreg[memreg_index].tcdm.q;
        end
      end
    end
  end

  // cva6v gated clock
  logic cva6v_clk_en;
  logic cva6v_gclk;
  always_comb cva6v_clk_en = reg2hw.cva6_clk_en;

  axe_tcl_clk_gating cva6v_cg (
    .i_clk (i_clk),
    .i_en (cva6v_clk_en),
    .i_test_en (i_scan_en),
    .o_clk(cva6v_gclk)
  );

  ai_core_cva6v u_ai_core_cva6v (
    .i_clk                           (cva6v_gclk),
    .i_rst_n                         (i_rst_n),
    .i_boot_addr                     (aic_cva6v_pkg::aic_cva6v_xwidth_t'(i_cva6v_boot_addr)),
    .i_hart_id                       (aic_infra_pkg::cid_to_hart_id(i_cid)),
    .i_memreg_0_addr                 (cva6v_memreg_addr[0]),
    .i_memreg_0_size                 (cva6v_memreg_size[0]),
    .i_memreg_0_tcdm                 (cva6v_memreg_tcdm[0]),
    .i_memreg_1_addr                 (cva6v_memreg_addr[1]),
    .i_memreg_1_size                 (cva6v_memreg_size[1]),
    .i_memreg_1_tcdm                 (cva6v_memreg_tcdm[1]),
    .i_irq                           (irq_to_cva6),
    .i_ipi                           (cva6v_msip),
    .i_time_irq                      (cva6v_mtip),
    .i_platform_irq                  (aic_cva6v_pkg::aic_cva6v_platf_irq_t'(irq_to_cva6_software)),
    .i_debug_req                     (cva6v_debug_req),
    .i_debug_rst_halt_req            (cva6v_debug_rst_halt_req),
    .o_debug_stop_time               (o_cva6v_debug_stop_time_async),
    .o_hart_is_wfi                   (hw2reg.ai_core_status.d),
    .o_hart_unavail                  (o_cva6v_hart_unavail_async),
    .o_hart_under_reset              (o_cva6v_hart_under_reset_async),
    .o_axi_m_awvalid                 (axi_cva6v_aw_valid),
    .i_axi_m_awready                 (axi_cva6v_aw_ready),
    .o_axi_m_awid                    (axi_cva6v_aw.id),
    .o_axi_m_awaddr                  (axi_cva6v_aw.addr),
    .o_axi_m_awlen                   (axi_cva6v_aw.len),
    .o_axi_m_awsize                  (axi_cva6v_aw.size),
    .o_axi_m_awburst                 (axi_cva6v_aw.burst),
    .o_axi_m_awlock                  (axi_cva6v_aw.lock),
    .o_axi_m_awcache                 (axi_cva6v_aw.cache),
    .o_axi_m_awprot                  (axi_cva6v_aw.prot),
    .o_axi_m_awqos                   (axi_cva6v_aw.qos),
    .o_axi_m_awregion                (axi_cva6v_aw.region),
    .o_axi_m_awatop                  (axi_cva6v_aw.atop),
    .o_axi_m_awuser                  (axi_cva6v_aw.user),
    .o_axi_m_wvalid                  (axi_cva6v_w_valid),
    .i_axi_m_wready                  (axi_cva6v_w_ready),
    .o_axi_m_wdata                   (axi_cva6v_w.data),
    .o_axi_m_wstrb                   (axi_cva6v_w.strb),
    .o_axi_m_wlast                   (axi_cva6v_w.last),
    .o_axi_m_wuser                   (axi_cva6v_w.user),
    .o_axi_m_arvalid                 (axi_cva6v_ar_valid),
    .i_axi_m_arready                 (axi_cva6v_ar_ready),
    .o_axi_m_arid                    (axi_cva6v_ar.id),
    .o_axi_m_araddr                  (axi_cva6v_ar.addr),
    .o_axi_m_arlen                   (axi_cva6v_ar.len),
    .o_axi_m_arsize                  (axi_cva6v_ar.size),
    .o_axi_m_arburst                 (axi_cva6v_ar.burst),
    .o_axi_m_arlock                  (axi_cva6v_ar.lock),
    .o_axi_m_arcache                 (axi_cva6v_ar.cache),
    .o_axi_m_arprot                  (axi_cva6v_ar.prot),
    .o_axi_m_arqos                   (axi_cva6v_ar.qos),
    .o_axi_m_arregion                (axi_cva6v_ar.region),
    .o_axi_m_aruser                  (axi_cva6v_ar.user),
    .i_axi_m_bvalid                  (axi_cva6v_b_valid),
    .o_axi_m_bready                  (axi_cva6v_b_ready),
    .i_axi_m_bid                     (axi_cva6v_b.id),
    .i_axi_m_bresp                   (axi_cva6v_b.resp),
    .i_axi_m_buser                   (axi_cva6v_b.user),
    .i_axi_m_rvalid                  (axi_cva6v_r_valid),
    .o_axi_m_rready                  (axi_cva6v_r_ready),
    .i_axi_m_rid                     (axi_cva6v_r.id),
    .i_axi_m_rdata                   (axi_cva6v_r.data),
    .i_axi_m_rresp                   (axi_cva6v_r.resp),
    .i_axi_m_rlast                   (axi_cva6v_r.last),
    .i_axi_m_ruser                   (axi_cva6v_r.user),
    .o_mem_req_0_valid               (o_rvv_0_req_valid),
    .i_mem_req_0_ready               (i_rvv_0_req_ready),
    .o_mem_req_0_addr                (o_rvv_0_req_addr),
    .o_mem_req_0_we                  (o_rvv_0_req_we),
    .o_mem_req_0_be                  (o_rvv_0_req_be),
    .o_mem_req_0_wdata               (o_rvv_0_req_wdata),
    .i_mem_res_0_valid               (i_rvv_0_res_valid),
    .i_mem_res_0_rdata               (i_rvv_0_res_rdata),
    .i_mem_res_0_err                 (i_rvv_0_res_err),
    .o_mem_req_1_valid               (o_rvv_1_req_valid),
    .i_mem_req_1_ready               (i_rvv_1_req_ready),
    .o_mem_req_1_addr                (o_rvv_1_req_addr),
    .o_mem_req_1_we                  (o_rvv_1_req_we),
    .o_mem_req_1_be                  (o_rvv_1_req_be),
    .o_mem_req_1_wdata               (o_rvv_1_req_wdata),
    .i_mem_res_1_valid               (i_rvv_1_res_valid),
    .i_mem_res_1_rdata               (i_rvv_1_res_rdata),
    .i_mem_res_1_err                 (i_rvv_1_res_err),
    .o_mem_req_2_valid               (o_rvv_2_req_valid),
    .i_mem_req_2_ready               (i_rvv_2_req_ready),
    .o_mem_req_2_addr                (o_rvv_2_req_addr),
    .o_mem_req_2_we                  (o_rvv_2_req_we),
    .o_mem_req_2_be                  (o_rvv_2_req_be),
    .o_mem_req_2_wdata               (o_rvv_2_req_wdata),
    .i_mem_res_2_valid               (i_rvv_2_res_valid),
    .i_mem_res_2_rdata               (i_rvv_2_res_rdata),
    .i_mem_res_2_err                 (i_rvv_2_res_err),
    .o_mem_req_3_valid               (o_rvv_3_req_valid),
    .i_mem_req_3_ready               (i_rvv_3_req_ready),
    .o_mem_req_3_addr                (o_rvv_3_req_addr),
    .o_mem_req_3_we                  (o_rvv_3_req_we),
    .o_mem_req_3_be                  (o_rvv_3_req_be),
    .o_mem_req_3_wdata               (o_rvv_3_req_wdata),
    .i_mem_res_3_valid               (i_rvv_3_res_valid),
    .i_mem_res_3_rdata               (i_rvv_3_res_rdata),
    .i_mem_res_3_err                 (i_rvv_3_res_err),
    .o_mem_req_4_valid               (o_rvv_4_req_valid),
    .i_mem_req_4_ready               (i_rvv_4_req_ready),
    .o_mem_req_4_addr                (o_rvv_4_req_addr),
    .o_mem_req_4_we                  (o_rvv_4_req_we),
    .o_mem_req_4_be                  (o_rvv_4_req_be),
    .o_mem_req_4_wdata               (o_rvv_4_req_wdata),
    .i_mem_res_4_valid               (i_rvv_4_res_valid),
    .i_mem_res_4_rdata               (i_rvv_4_res_rdata),
    .i_mem_res_4_err                 (i_rvv_4_res_err),
    .o_mem_req_5_valid               (o_rvv_5_req_valid),
    .i_mem_req_5_ready               (i_rvv_5_req_ready),
    .o_mem_req_5_addr                (o_rvv_5_req_addr),
    .o_mem_req_5_we                  (o_rvv_5_req_we),
    .o_mem_req_5_be                  (o_rvv_5_req_be),
    .o_mem_req_5_wdata               (o_rvv_5_req_wdata),
    .i_mem_res_5_valid               (i_rvv_5_res_valid),
    .i_mem_res_5_rdata               (i_rvv_5_res_rdata),
    .i_mem_res_5_err                 (i_rvv_5_res_err),
    .o_mem_req_6_valid               (o_rvv_6_req_valid),
    .i_mem_req_6_ready               (i_rvv_6_req_ready),
    .o_mem_req_6_addr                (o_rvv_6_req_addr),
    .o_mem_req_6_we                  (o_rvv_6_req_we),
    .o_mem_req_6_be                  (o_rvv_6_req_be),
    .o_mem_req_6_wdata               (o_rvv_6_req_wdata),
    .i_mem_res_6_valid               (i_rvv_6_res_valid),
    .i_mem_res_6_rdata               (i_rvv_6_res_rdata),
    .i_mem_res_6_err                 (i_rvv_6_res_err),
    .o_mem_req_7_valid               (o_rvv_7_req_valid),
    .i_mem_req_7_ready               (i_rvv_7_req_ready),
    .o_mem_req_7_addr                (o_rvv_7_req_addr),
    .o_mem_req_7_we                  (o_rvv_7_req_we),
    .o_mem_req_7_be                  (o_rvv_7_req_be),
    .o_mem_req_7_wdata               (o_rvv_7_req_wdata),
    .i_mem_res_7_valid               (i_rvv_7_res_valid),
    .i_mem_res_7_rdata               (i_rvv_7_res_rdata),
    .i_mem_res_7_err                 (i_rvv_7_res_err),
    .o_perf_cntr_fu_0_status         (),
    .o_perf_cntr_fu_1_status         (),
    .o_perf_cntr_fu_2_status         (),
    .o_perf_cntr_dispatch_queue_full (),
    .o_perf_cntr_dispatch_queue_empty(),
    .o_perf_cntr_commit_queue_full   (),
    .o_perf_cntr_commit_queue_empty  (),
    .o_perf_event_0_addr             (cva6v_perf_event_0_addr),
    .o_perf_event_0_0_delta          (cva6v_perf_event_0_0_delta),
    .o_perf_event_0_1_delta          (),
    .o_perf_event_1_addr             (cva6v_perf_event_1_addr),
    .o_perf_event_1_0_delta          (cva6v_perf_event_1_0_delta),
    .o_perf_event_1_1_delta          (),
    .o_perf_event_2_addr             (),
    .o_perf_event_2_0_delta          (),
    .o_perf_event_2_1_delta          (),
    .i_mem_impl                      (sram_impl_inp[aic_infra_pkg::SRAM_IMPL_IDX_CVA6V]),
    .o_mem_impl                      (sram_impl_oup[aic_infra_pkg::SRAM_IMPL_IDX_CVA6V])
  );

  ////////////////////////////
  // ATOP Adapter for CVA6V //
  ////////////////////////////

  cva6v_ai_core_pkg::axi_aw_chan_t axi_cva6v_no_atomics_aw;
  logic                            axi_cva6v_no_atomics_aw_valid;
  logic                            axi_cva6v_no_atomics_aw_ready;
  cva6v_ai_core_pkg::axi_w_chan_t  axi_cva6v_no_atomics_w;
  logic                            axi_cva6v_no_atomics_w_valid;
  logic                            axi_cva6v_no_atomics_w_ready;
  cva6v_ai_core_pkg::axi_b_chan_t  axi_cva6v_no_atomics_b;
  logic                            axi_cva6v_no_atomics_b_valid;
  logic                            axi_cva6v_no_atomics_b_ready;
  cva6v_ai_core_pkg::axi_ar_chan_t axi_cva6v_no_atomics_ar;
  logic                            axi_cva6v_no_atomics_ar_valid;
  logic                            axi_cva6v_no_atomics_ar_ready;
  cva6v_ai_core_pkg::axi_r_chan_t  axi_cva6v_no_atomics_r;
  logic                            axi_cva6v_no_atomics_r_valid;
  logic                            axi_cva6v_no_atomics_r_ready;

  // Note: To make it compile in RTLA
  localparam int unsigned RiscvWordWidth = cva6v_ai_core_pkg::CVA6UserCfg.XLEN;

  axe_axi_riscv_amos #(
    .AxiIdWidth      (cva6v_ai_core_pkg::AxiIdWidth),
    .AxiAddrWidth    (cva6v_ai_core_pkg::AxiAddrWidth),
    .AxiDataWidth    (cva6v_ai_core_pkg::AxiDataWidth),
    .AxiMaxWriteTxns (aic_infra_pkg::AxiMaxWriteTxns),
    .RiscvWordWidth  (RiscvWordWidth),
    .axi_aw_t        (cva6v_ai_core_pkg::axi_aw_chan_t),
    .axi_w_t         (cva6v_ai_core_pkg::axi_w_chan_t),
    .axi_b_t         (cva6v_ai_core_pkg::axi_b_chan_t),
    .axi_ar_t        (cva6v_ai_core_pkg::axi_ar_chan_t),
    .axi_r_t         (cva6v_ai_core_pkg::axi_r_chan_t)
  ) u_axe_axi_riscv_amos_cva6v (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_cva6v_aw),
    .i_axi_s_aw_valid(axi_cva6v_aw_valid),
    .o_axi_s_aw_ready(axi_cva6v_aw_ready),
    .i_axi_s_w       (axi_cva6v_w),
    .i_axi_s_w_valid (axi_cva6v_w_valid),
    .o_axi_s_w_ready (axi_cva6v_w_ready),
    .o_axi_s_b       (axi_cva6v_b),
    .o_axi_s_b_valid (axi_cva6v_b_valid),
    .i_axi_s_b_ready (axi_cva6v_b_ready),
    .i_axi_s_ar      (axi_cva6v_ar),
    .i_axi_s_ar_valid(axi_cva6v_ar_valid),
    .o_axi_s_ar_ready(axi_cva6v_ar_ready),
    .o_axi_s_r       (axi_cva6v_r),
    .o_axi_s_r_valid (axi_cva6v_r_valid),
    .i_axi_s_r_ready (axi_cva6v_r_ready),
    .o_axi_m_aw      (axi_cva6v_no_atomics_aw),
    .o_axi_m_aw_valid(axi_cva6v_no_atomics_aw_valid),
    .i_axi_m_aw_ready(axi_cva6v_no_atomics_aw_ready),
    .o_axi_m_w       (axi_cva6v_no_atomics_w),
    .o_axi_m_w_valid (axi_cva6v_no_atomics_w_valid),
    .i_axi_m_w_ready (axi_cva6v_no_atomics_w_ready),
    .i_axi_m_b       (axi_cva6v_no_atomics_b),
    .i_axi_m_b_valid (axi_cva6v_no_atomics_b_valid),
    .o_axi_m_b_ready (axi_cva6v_no_atomics_b_ready),
    .o_axi_m_ar      (axi_cva6v_no_atomics_ar),
    .o_axi_m_ar_valid(axi_cva6v_no_atomics_ar_valid),
    .i_axi_m_ar_ready(axi_cva6v_no_atomics_ar_ready),
    .i_axi_m_r       (axi_cva6v_no_atomics_r),
    .i_axi_m_r_valid (axi_cva6v_no_atomics_r_valid),
    .o_axi_m_r_ready (axi_cva6v_no_atomics_r_ready)
  );

  // Cast the needed fields before going to the Synopsys fabric
  aic_infra_pkg::axi_lt_config_m_aw_t axi_cva6v_no_atomics_cast_aw;
  aic_infra_pkg::axi_lt_w_t           axi_cva6v_no_atomics_cast_w;
  aic_infra_pkg::axi_lt_config_m_b_t  axi_cva6v_no_atomics_cast_b;
  aic_infra_pkg::axi_lt_config_m_ar_t axi_cva6v_no_atomics_cast_ar;
  aic_infra_pkg::axi_lt_config_m_r_t  axi_cva6v_no_atomics_cast_r;

  always_comb axi_cva6v_no_atomics_cast_aw = '{
    id:    aic_common_pkg::aic_lt_axi_m_id_t'(axi_cva6v_no_atomics_aw.id),
    addr:  axi_cva6v_no_atomics_aw.addr,
    len:   axi_cva6v_no_atomics_aw.len,
    size:  axi_cva6v_no_atomics_aw.size,
    burst: axi_cva6v_no_atomics_aw.burst,
    lock:  axi_cva6v_no_atomics_aw.lock,
    cache: axi_cva6v_no_atomics_aw.cache,
    prot:  axi_cva6v_no_atomics_aw.prot,
    default: '0
  };
  always_comb axi_cva6v_no_atomics_cast_w = '{
    data: axi_cva6v_no_atomics_w.data,
    strb: axi_cva6v_no_atomics_w.strb,
    last: axi_cva6v_no_atomics_w.last
  };
  always_comb axi_cva6v_no_atomics_b = '{
    id:      cva6v_ai_core_pkg::AxiIdWidth'(axi_cva6v_no_atomics_cast_b.id),
    resp:    axi_cva6v_no_atomics_cast_b.resp,
    default: '0 // CVA6V has more unused fields, uses sensible default
  };
  always_comb axi_cva6v_no_atomics_cast_ar = '{
    id:    aic_common_pkg::aic_lt_axi_m_id_t'(axi_cva6v_no_atomics_ar.id),
    addr:  axi_cva6v_no_atomics_ar.addr,
    len:   axi_cva6v_no_atomics_ar.len,
    size:  axi_cva6v_no_atomics_ar.size,
    burst: axi_cva6v_no_atomics_ar.burst,
    lock:  axi_cva6v_no_atomics_ar.lock,
    cache: axi_cva6v_no_atomics_ar.cache,
    prot:  axi_cva6v_no_atomics_ar.prot
  };
  always_comb axi_cva6v_no_atomics_r = '{
    id:      cva6v_ai_core_pkg::AxiIdWidth'(axi_cva6v_no_atomics_cast_r.id),
    data:    axi_cva6v_no_atomics_cast_r.data,
    resp:    axi_cva6v_no_atomics_cast_r.resp,
    last:    axi_cva6v_no_atomics_cast_r.last,
    default: '0 // CVA6V has more unused fields, uses sensible default
  };

  aic_infra_pkg::axi_lt_config_m_aw_t axi_cva6v_cut_aw;
  logic                               axi_cva6v_cut_aw_valid;
  logic                               axi_cva6v_cut_aw_ready;
  aic_infra_pkg::axi_lt_w_t           axi_cva6v_cut_w;
  logic                               axi_cva6v_cut_w_valid;
  logic                               axi_cva6v_cut_w_ready;
  aic_infra_pkg::axi_lt_config_m_b_t  axi_cva6v_cut_b;
  logic                               axi_cva6v_cut_b_valid;
  logic                               axi_cva6v_cut_b_ready;
  aic_infra_pkg::axi_lt_config_m_ar_t axi_cva6v_cut_ar;
  logic                               axi_cva6v_cut_ar_valid;
  logic                               axi_cva6v_cut_ar_ready;
  aic_infra_pkg::axi_lt_config_m_r_t  axi_cva6v_cut_r;
  logic                               axi_cva6v_cut_r_valid;
  logic                               axi_cva6v_cut_r_ready;

  axe_axi_cut #(
    .CutAw   (1'b1),
    .CutW    (1'b1),
    .CutB    (1'b1), // This breaks a violating path
    .CutAr   (1'b1),
    .CutR    (1'b1),
    .axi_aw_t(aic_infra_pkg::axi_lt_config_m_aw_t),
    .axi_w_t (aic_infra_pkg::axi_lt_w_t),
    .axi_b_t (aic_infra_pkg::axi_lt_config_m_b_t),
    .axi_ar_t(aic_infra_pkg::axi_lt_config_m_ar_t),
    .axi_r_t (aic_infra_pkg::axi_lt_config_m_r_t)
  ) u_axe_axi_cut_cva6v (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_cva6v_no_atomics_cast_aw),
    .i_axi_s_aw_valid(axi_cva6v_no_atomics_aw_valid),
    .o_axi_s_aw_ready(axi_cva6v_no_atomics_aw_ready),
    .i_axi_s_w       (axi_cva6v_no_atomics_cast_w),
    .i_axi_s_w_valid (axi_cva6v_no_atomics_w_valid),
    .o_axi_s_w_ready (axi_cva6v_no_atomics_w_ready),
    .o_axi_s_b       (axi_cva6v_no_atomics_cast_b),
    .o_axi_s_b_valid (axi_cva6v_no_atomics_b_valid),
    .i_axi_s_b_ready (axi_cva6v_no_atomics_b_ready),
    .i_axi_s_ar      (axi_cva6v_no_atomics_cast_ar),
    .i_axi_s_ar_valid(axi_cva6v_no_atomics_ar_valid),
    .o_axi_s_ar_ready(axi_cva6v_no_atomics_ar_ready),
    .o_axi_s_r       (axi_cva6v_no_atomics_cast_r),
    .o_axi_s_r_valid (axi_cva6v_no_atomics_r_valid),
    .i_axi_s_r_ready (axi_cva6v_no_atomics_r_ready),
    .o_axi_m_aw      (axi_cva6v_cut_aw),
    .o_axi_m_aw_valid(axi_cva6v_cut_aw_valid),
    .i_axi_m_aw_ready(axi_cva6v_cut_aw_ready),
    .o_axi_m_w       (axi_cva6v_cut_w),
    .o_axi_m_w_valid (axi_cva6v_cut_w_valid),
    .i_axi_m_w_ready (axi_cva6v_cut_w_ready),
    .i_axi_m_b       (axi_cva6v_cut_b),
    .i_axi_m_b_valid (axi_cva6v_cut_b_valid),
    .o_axi_m_b_ready (axi_cva6v_cut_b_ready),
    .o_axi_m_ar      (axi_cva6v_cut_ar),
    .o_axi_m_ar_valid(axi_cva6v_cut_ar_valid),
    .i_axi_m_ar_ready(axi_cva6v_cut_ar_ready),
    .i_axi_m_r       (axi_cva6v_cut_r),
    .i_axi_m_r_valid (axi_cva6v_cut_r_valid),
    .o_axi_m_r_ready (axi_cva6v_cut_r_ready)
  );

  /////////////
  // Mailbox //
  /////////////
  axi_mailbox_csr_reg_pkg::axi_a_ch_h2d_t axi_lt_mailbox_aw;
  logic                                   axi_lt_mailbox_aw_ready;
  axi_mailbox_csr_reg_pkg::axi_w_ch_h2d_t axi_lt_mailbox_w;
  logic                                   axi_lt_mailbox_w_ready;
  axi_mailbox_csr_reg_pkg::axi_b_ch_d2h_t axi_lt_mailbox_b;
  logic                                   axi_lt_mailbox_b_ready;
  axi_mailbox_csr_reg_pkg::axi_a_ch_h2d_t axi_lt_mailbox_ar;
  logic                                   axi_lt_mailbox_ar_ready;
  axi_mailbox_csr_reg_pkg::axi_r_ch_d2h_t axi_lt_mailbox_r;
  logic                                   axi_lt_mailbox_r_ready;

  // making sure not to send Xs as AXI id to mailbox CSR
  always_comb axi_lt_mailbox_aw.id[axi_mailbox_csr_reg_pkg::AXI_IDW-1:aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW] = 'b0;
  always_comb axi_lt_mailbox_ar.id[axi_mailbox_csr_reg_pkg::AXI_IDW-1:aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW] = 'b0;

  axi_mailbox #(
    .MailboxDepth(aic_infra_pkg::MailboxDepth)
  ) u_axi_mailbox (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_lt_mailbox_aw),
    .o_axi_s_aw_ready(axi_lt_mailbox_aw_ready),
    .i_axi_s_w       (axi_lt_mailbox_w),
    .o_axi_s_w_ready (axi_lt_mailbox_w_ready),
    .o_axi_s_b       (axi_lt_mailbox_b),
    .i_axi_s_b_ready (axi_lt_mailbox_b_ready),
    .i_axi_s_ar      (axi_lt_mailbox_ar),
    .o_axi_s_ar_ready(axi_lt_mailbox_ar_ready),
    .o_axi_s_r       (axi_lt_mailbox_r),
    .i_axi_s_r_ready (axi_lt_mailbox_r_ready),
    .o_irq           (irq_sources[aic_infra_pkg::IRQ_IDX_MAILBOX])
  );

  ///////////////////
  // Token Manager //
  ///////////////////
  token_manager_aic_csr_reg_pkg::axi_a_ch_h2d_t axi_lt_token_manager_aw;
  logic                                         axi_lt_token_manager_aw_ready;
  token_manager_aic_csr_reg_pkg::axi_w_ch_h2d_t axi_lt_token_manager_w;
  logic                                         axi_lt_token_manager_w_ready;
  token_manager_aic_csr_reg_pkg::axi_b_ch_d2h_t axi_lt_token_manager_b;
  logic                                         axi_lt_token_manager_b_ready;
  token_manager_aic_csr_reg_pkg::axi_a_ch_h2d_t axi_lt_token_manager_ar;
  logic                                         axi_lt_token_manager_ar_ready;
  token_manager_aic_csr_reg_pkg::axi_r_ch_d2h_t axi_lt_token_manager_r;
  logic                                         axi_lt_token_manager_r_ready;

  // local network:
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_CFG.max_num_prod-1:0] token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_CFG.nr_loc_devs];
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_CFG.max_num_prod-1:0] token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_CFG.nr_loc_devs];
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_CFG.max_num_cons-1:0] token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_CFG.nr_loc_devs];
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_CFG.max_num_cons-1:0] token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_CFG.nr_loc_devs];
  // top network:
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG.max_num_prod-1:0] token_top_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG.nr_loc_devs];
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG.max_num_prod-1:0] token_top_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG.nr_loc_devs];
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG.max_num_cons-1:0] token_top_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG.nr_loc_devs];
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG.max_num_cons-1:0] token_top_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG.nr_loc_devs];

  // Token Assignments
  always_comb begin
    // Don't propagate X
    foreach (token_dev_prod_valid[dev_idx]) token_dev_prod_valid[dev_idx] = '0;
    foreach (token_top_prod_valid[dev_idx]) token_top_prod_valid[dev_idx] = '0;

    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_0_NR_TOK_PROD-1:0]   = i_m_ifd0_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_1_NR_TOK_PROD-1:0]   = i_m_ifd1_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_2_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_2_NR_TOK_PROD-1:0]   = i_m_ifd2_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_W_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_W_NR_TOK_PROD-1:0]   = i_m_ifdw_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_ODR_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_ODR_NR_TOK_PROD-1:0]       = i_m_odr_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_0_NR_TOK_PROD-1:0]   = i_d_ifd0_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_1_NR_TOK_PROD-1:0]   = i_d_ifd1_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_ODR_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_ODR_NR_TOK_PROD-1:0]       = i_d_odr_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] = i_mvm_exe_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] = i_mvm_prg_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD-1:0]       = i_m_iau_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD-1:0]       = i_m_dpu_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0]     = i_dwpu_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0]       = i_d_iau_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD-1:0]       = i_d_dpu_tok_prod_vld;
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_PROD-1:0] = ht_dma_tok_prod_vld[0];
    token_dev_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_NR_TOK_PROD-1:0] = ht_dma_tok_prod_vld[1];

    token_top_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_PROD-1:0] = acd_top_tok_prod_vld;
    token_top_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_PROD-1:0] = ht_dma_top_tok_prod_vld[0];
    token_top_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_NR_TOK_PROD-1:0] = ht_dma_top_tok_prod_vld[1];
  end

  always_comb o_m_ifd0_tok_prod_rdy                   = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_0_NR_TOK_PROD-1:0];
  always_comb o_m_ifd1_tok_prod_rdy                   = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_1_NR_TOK_PROD-1:0];
  always_comb o_m_ifd2_tok_prod_rdy                   = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_2_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_2_NR_TOK_PROD-1:0];
  always_comb o_m_ifdw_tok_prod_rdy                   = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_W_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_W_NR_TOK_PROD-1:0];
  always_comb o_m_odr_tok_prod_rdy                    = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_ODR_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_ODR_NR_TOK_PROD-1:0];
  always_comb o_d_ifd0_tok_prod_rdy                   = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_0_NR_TOK_PROD-1:0];
  always_comb o_d_ifd1_tok_prod_rdy                   = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_1_NR_TOK_PROD-1:0];
  always_comb o_d_odr_tok_prod_rdy                    = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_ODR_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_ODR_NR_TOK_PROD-1:0];
  always_comb o_mvm_exe_tok_prod_rdy                  = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0];
  always_comb o_mvm_prg_tok_prod_rdy                  = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0];
  always_comb o_m_iau_tok_prod_rdy                    = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD-1:0];
  always_comb o_m_dpu_tok_prod_rdy                    = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD-1:0];
  always_comb o_dwpu_tok_prod_rdy                     = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0];
  always_comb o_d_iau_tok_prod_rdy                    = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0];
  always_comb o_d_dpu_tok_prod_rdy                    = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD-1:0];
  always_comb ht_dma_tok_prod_rdy[0]                  = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_PROD-1:0];
  always_comb ht_dma_tok_prod_rdy[1]                  = token_dev_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_NR_TOK_PROD-1:0];

  always_comb acd_top_tok_prod_rdy                    = token_top_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_PROD-1:0];
  always_comb ht_dma_top_tok_prod_rdy[0]              = token_top_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_PROD-1:0];
  always_comb ht_dma_top_tok_prod_rdy[1]              = token_top_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_NR_TOK_PROD-1:0];

  always_comb o_m_ifd0_tok_cons_vld                   = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_0_NR_TOK_CONS-1:0];
  always_comb o_m_ifd1_tok_cons_vld                   = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_1_NR_TOK_CONS-1:0];
  always_comb o_m_ifd2_tok_cons_vld                   = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_2_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_2_NR_TOK_CONS-1:0];
  always_comb o_m_ifdw_tok_cons_vld                   = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_W_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_W_NR_TOK_CONS-1:0];
  always_comb o_m_odr_tok_cons_vld                    = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_ODR_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_ODR_NR_TOK_CONS-1:0];
  always_comb o_d_ifd0_tok_cons_vld                   = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_0_NR_TOK_CONS-1:0];
  always_comb o_d_ifd1_tok_cons_vld                   = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_1_NR_TOK_CONS-1:0];
  always_comb o_d_odr_tok_cons_vld                    = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_ODR_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_ODR_NR_TOK_CONS-1:0];
  always_comb o_mvm_exe_tok_cons_vld                  = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0];
  always_comb o_mvm_prg_tok_cons_vld                  = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0];
  always_comb o_m_iau_tok_cons_vld                    = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS-1:0];
  always_comb o_m_dpu_tok_cons_vld                    = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS-1:0];
  always_comb o_dwpu_tok_cons_vld                     = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0];
  always_comb o_d_iau_tok_cons_vld                    = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0];
  always_comb o_d_dpu_tok_cons_vld                    = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS-1:0];
  always_comb ht_dma_tok_cons_vld[0]                  = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_CONS-1:0];
  always_comb ht_dma_tok_cons_vld[1]                  = token_dev_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_NR_TOK_CONS-1:0];

  always_comb acd_top_tok_cons_vld                    = token_top_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_CONS-1:0];
  always_comb ht_dma_top_tok_cons_vld[0]              = token_top_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_CONS-1:0];
  always_comb ht_dma_top_tok_cons_vld[1]              = token_top_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_NR_TOK_CONS-1:0];

  always_comb begin
    // Don't propagate X
    foreach (token_dev_cons_ready[dev_idx]) token_dev_cons_ready[dev_idx] = '1;
    foreach (token_top_cons_ready[dev_idx]) token_top_cons_ready[dev_idx] = '1;

    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_0_NR_TOK_CONS-1:0]   = i_m_ifd0_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_1_NR_TOK_CONS-1:0]   = i_m_ifd1_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_2_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_2_NR_TOK_CONS-1:0]   = i_m_ifd2_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_W_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IFD_W_NR_TOK_CONS-1:0]   = i_m_ifdw_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_ODR_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_ODR_NR_TOK_CONS-1:0]       = i_m_odr_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_0_NR_TOK_CONS-1:0]   = i_d_ifd0_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IFD_1_NR_TOK_CONS-1:0]   = i_d_ifd1_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_ODR_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_ODR_NR_TOK_CONS-1:0]       = i_d_odr_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] = i_mvm_exe_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] = i_mvm_prg_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS-1:0]       = i_m_iau_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS-1:0]       = i_m_dpu_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0]     = i_dwpu_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0]       = i_d_iau_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS-1:0]       = i_d_dpu_tok_cons_rdy;
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_0_NR_TOK_CONS-1:0] = ht_dma_tok_cons_rdy[0];
    token_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_HP_DMA_1_NR_TOK_CONS-1:0] = ht_dma_tok_cons_rdy[1];

    token_top_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_CONS-1:0] = acd_top_tok_cons_rdy;
    token_top_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C0_NR_TOK_CONS-1:0] = ht_dma_top_tok_cons_rdy[0];
    token_top_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_DEV_IDX][token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_DMA_C1_NR_TOK_CONS-1:0] = ht_dma_top_tok_cons_rdy[1];
  end

  token_manager_pkg::tokmgr_uid_all_t tok_uid_to_vuid, tok_vuid_to_uid;
  always_comb begin
    tok_uid_to_vuid = '0; // rsvd fields to zero
    tok_vuid_to_uid = '0; // rsvd fields to zero

    tok_uid_to_vuid.aic0  = reg2hw.uid_to_vuid_aic0;
    tok_uid_to_vuid.aic1  = reg2hw.uid_to_vuid_aic1;
    tok_uid_to_vuid.aic2  = reg2hw.uid_to_vuid_aic2;
    tok_uid_to_vuid.aic3  = reg2hw.uid_to_vuid_aic3;
    tok_uid_to_vuid.aic4  = reg2hw.uid_to_vuid_aic4;
    tok_uid_to_vuid.aic5  = reg2hw.uid_to_vuid_aic5;
    tok_uid_to_vuid.aic6  = reg2hw.uid_to_vuid_aic6;
    tok_uid_to_vuid.aic7  = reg2hw.uid_to_vuid_aic7;
    tok_uid_to_vuid.sdma0 = reg2hw.uid_to_vuid_sdma0;
    tok_uid_to_vuid.sdma1 = reg2hw.uid_to_vuid_sdma1;
    tok_uid_to_vuid.apu   = reg2hw.uid_to_vuid_apu;

    tok_vuid_to_uid.aic0  = reg2hw.vuid_to_uid_aic0;
    tok_vuid_to_uid.aic1  = reg2hw.vuid_to_uid_aic1;
    tok_vuid_to_uid.aic2  = reg2hw.vuid_to_uid_aic2;
    tok_vuid_to_uid.aic3  = reg2hw.vuid_to_uid_aic3;
    tok_vuid_to_uid.aic4  = reg2hw.vuid_to_uid_aic4;
    tok_vuid_to_uid.aic5  = reg2hw.vuid_to_uid_aic5;
    tok_vuid_to_uid.aic6  = reg2hw.vuid_to_uid_aic6;
    tok_vuid_to_uid.aic7  = reg2hw.vuid_to_uid_aic7;
    tok_vuid_to_uid.sdma0 = reg2hw.vuid_to_uid_sdma0;
    tok_vuid_to_uid.sdma1 = reg2hw.vuid_to_uid_sdma1;
    tok_vuid_to_uid.apu   = reg2hw.vuid_to_uid_apu;
  end

  // Global sync:
  logic global_sync_d, global_sync_q, global_sync_pulse;
  logic global_sync_mvmexe, global_sync_mvmexe_en, global_sync_timestamplogger;

  axe_tcl_seq_sync #(
    .SyncStages(2),
    .ResetValue(1'b0)
  ) u_sync_inter_core_sync (
    .i_clk,
    .i_rst_n,
    .i_d    (i_inter_core_sync),
    .o_q    (global_sync_d)
  );

  always_comb global_sync_pulse = global_sync_d ^ global_sync_q;
  always_comb begin
    global_sync_mvmexe = 1'b0;
    global_sync_mvmexe_en = 1'b0;
    global_sync_timestamplogger = 1'b0;
    if (reg2hw.global_sync_control.en.q) begin
      if (reg2hw.global_sync_control.select.q == 0) begin // timestamp logger
        global_sync_timestamplogger = global_sync_pulse;
      end else begin // 1: mvm exe
        global_sync_mvmexe_en = 1'b1;
        global_sync_mvmexe = global_sync_pulse;
      end
    end
  end

  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n)
      global_sync_q <= 1'b0;
    else if (global_sync_pulse)
      global_sync_q <= global_sync_d;
  end
  token_manager_aic u_token_manager (
    .i_clk,
    .i_rst_n,
    .i_sync_mvm_exe_swep_en(global_sync_mvmexe_en),
    .i_sync_mvm_exe_swep(global_sync_mvmexe),
    .i_swep_is_acd(reg2hw.swep_token_select.q),
    .i_dev_prod_valid(token_dev_prod_valid),
    .o_dev_prod_ready(token_dev_prod_ready),
    .o_dev_cons_valid(token_dev_cons_valid),
    .i_dev_cons_ready(token_dev_cons_ready),
    .i_acd_prod_valid(acd_tok_prod_vld),
    .o_acd_prod_ready(acd_tok_prod_rdy),
    .o_acd_cons_valid(acd_tok_cons_vld),
    .i_acd_cons_ready(acd_tok_cons_rdy),
    .i_cid(i_cid[token_manager_pkg::TOKEN_MANAGER_UID_W-1:0]),
    .i_uid_to_vuid   (tok_uid_to_vuid),
    .i_vuid_to_uid   (tok_vuid_to_uid),
    .o_tok_prod_ocpl_m_maddr,
    .o_tok_prod_ocpl_m_mcmd,
    .i_tok_prod_ocpl_m_scmdaccept,
    .o_tok_prod_ocpl_m_mdata,
    .i_tok_cons_ocpl_s_maddr,
    .i_tok_cons_ocpl_s_mcmd,
    .o_tok_cons_ocpl_s_scmdaccept,
    .i_tok_cons_ocpl_s_mdata,
    .i_top_prod_valid(token_top_prod_valid),
    .o_top_prod_ready(token_top_prod_ready),
    .o_top_cons_valid(token_top_cons_valid),
    .i_top_cons_ready(token_top_cons_ready),
    .i_axi_s_aw      (axi_lt_token_manager_aw),
    .o_axi_s_aw_ready(axi_lt_token_manager_aw_ready),
    .i_axi_s_w       (axi_lt_token_manager_w),
    .o_axi_s_w_ready (axi_lt_token_manager_w_ready),
    .o_axi_s_b       (axi_lt_token_manager_b),
    .i_axi_s_b_ready (axi_lt_token_manager_b_ready),
    .i_axi_s_ar      (axi_lt_token_manager_ar),
    .o_axi_s_ar_ready(axi_lt_token_manager_ar_ready),
    .o_axi_s_r       (axi_lt_token_manager_r),
    .i_axi_s_r_ready (axi_lt_token_manager_r_ready),
    .o_irq           (irq_sources[aic_infra_pkg::IRQ_IDX_TOKEN_MGR])
  );

  ///////////////////////////////////////////
  // AI Core Controll and Status Registers //
  ///////////////////////////////////////////
  // Connect observability stuff
  if ($bits(hw2reg.id.core_id.d)         != aic_common_pkg::AIC_CID_WIDTH) $fatal(1, "$bits(hw2reg.id.core_id.d) != aic_common_pkg::AIC_CID_WIDTH does not match!");

  localparam int unsigned CsrBlockIdWidth       = $bits(hw2reg.id.block_id.d);
  localparam int unsigned CsrHwRevisionMinWidth = $bits(hw2reg.id.hw_revision_min.d);
  localparam int unsigned CsrHwRevisionMajWidth = $bits(hw2reg.id.hw_revision_maj.d);

  assign hw2reg.id.block_id.d        = CsrBlockIdWidth'(aic_common_pkg::AIC_BLOCK_ID_CSR);
  assign hw2reg.id.core_id.d         = i_cid;
  assign hw2reg.id.hw_revision_min.d = CsrHwRevisionMinWidth'(aic_common_pkg::AIC_HW_REVISION_MIN);
  assign hw2reg.id.hw_revision_maj.d = CsrHwRevisionMajWidth'(aic_common_pkg::AIC_HW_REVISION_MAJ);

  aic_csr_reg_pkg::axi_a_ch_h2d_t axi_lt_aw;
  logic                           axi_lt_aw_ready;
  aic_csr_reg_pkg::axi_a_ch_h2d_t axi_lt_ar;
  logic                           axi_lt_ar_ready;
  aic_csr_reg_pkg::axi_w_ch_h2d_t axi_lt_w;
  logic                           axi_lt_w_ready;
  aic_csr_reg_pkg::axi_b_ch_d2h_t axi_lt_b;
  logic                           axi_lt_b_ready;
  aic_csr_reg_pkg::axi_r_ch_d2h_t axi_lt_r;
  logic                           axi_lt_r_ready;

  aic_csr_reg_top #(
    .StageNum(3)
  ) u_aic_csr_reg_top (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    .axi_aw_i   (axi_lt_aw),
    .axi_awready(axi_lt_aw_ready),
    .axi_ar_i   (axi_lt_ar),
    .axi_arready(axi_lt_ar_ready),
    .axi_w_i    (axi_lt_w),
    .axi_wready (axi_lt_w_ready),
    .axi_b_o    (axi_lt_b),
    .axi_bready (axi_lt_b_ready),
    .axi_r_o    (axi_lt_r),
    .axi_rready (axi_lt_r_ready),
    .reg2hw, // Write
    .hw2reg, // Read
    .devmode_i  (1'b1) // If 1, explicit error return for unmapped register access
  );

  /////////////
  // RV PLIC //
  /////////////

  // Connect up irqs from different partitons
  // Local IRQs are connected at a specific instance
  if ( aic_rv_plic_reg_pkg::NumSrc !=
    (
        aic_mid_pkg::NUM_IRQS                              // Number of IRQ from aic_mid_p
      + aic_did_pkg::NUM_AXI_ENDPOINTS                     // Number of IRQ from aic_did_p
      + dmc_pkg::DMC_IRQ_W                                 // Number of IRQ from aic_ls_p
      + 1                                                  // Number of IRQ from token_manager
      + 1                                                  // Number of IRQ from LT DMA Ctrl
      + snps_dma_pkg::SNPS_DMA_AIC_LT_CFG.dma_nbr_channels // Number of IRQ from LT DMA Channels
      + aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS // Number of IRQ from HT DMA Channels
      + 1                                                  // Number of IRQ from Thermal warning
      + 1                                                  // Number of IRQ from Mailbox
      + 1                                                  // Number of IRQ from AIC_CD
      + 1                                                  // Number of IRQ from SPM
    )
  ) $fatal(1, "Number of interrupt sources does not match configured aic_rv_plic!");
  if (aic_rv_plic_reg_pkg::AXI_LENW != axi_pkg::AXI_LEN_WIDTH) $fatal(1, "aic_rv_plic: AXI LENW does not match!");

  // Connect up external sourcse, sources in this file re connected directly there

  assign irq_sources[aic_infra_pkg::IRQ_IDX_MID_MVM]      = i_irq_aic_mid[aic_mid_pkg::Mvm_irq];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_MID_IAU]      = i_irq_aic_mid[aic_mid_pkg::Iau_irq];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_MID_DPU]      = i_irq_aic_mid[aic_mid_pkg::Dpu_irq];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_MID_GEN]      = i_irq_aic_mid[aic_mid_pkg::MID_irq];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_MID_TU_WRN]   = i_irq_aic_mid[aic_mid_pkg::TU_warning_irq];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_MID_TU_CRIT]  = i_irq_aic_mid[aic_mid_pkg::TU_critical_irq];

  assign irq_sources[aic_infra_pkg::IRQ_IDX_DID_DWPU] = i_irq_aic_did[aic_did_pkg::EndPointDwpu];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_DID_IAU]  = i_irq_aic_did[aic_did_pkg::EndPointIau];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_DID_DPU]  = i_irq_aic_did[aic_did_pkg::EndPointDpu];

  assign irq_sources[aic_infra_pkg::IRQ_IDX_M_IFD_0]  = i_irq_dmc[dmc_pkg::m_ifd0_idx];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_M_IFD_1]  = i_irq_dmc[dmc_pkg::m_ifd1_idx];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_M_IFD_2]  = i_irq_dmc[dmc_pkg::m_ifd2_idx];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_M_IFDW]   = i_irq_dmc[dmc_pkg::m_ifdw_idx];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_D_IFD_0]  = i_irq_dmc[dmc_pkg::d_ifd0_idx];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_D_IFD_1]  = i_irq_dmc[dmc_pkg::d_ifd1_idx];

  assign irq_sources[aic_infra_pkg::IRQ_IDX_M_ODR]    = i_irq_dmc[dmc_pkg::m_odr_idx];
  assign irq_sources[aic_infra_pkg::IRQ_IDX_D_ODR]    = i_irq_dmc[dmc_pkg::d_odr_idx];

  assign irq_sources[aic_infra_pkg::IRQ_IDX_THERMAL_WARNING]  = thermal_warning;

  aic_rv_plic_reg_pkg::axi_a_ch_h2d_t axi_rv_plic_aw;
  logic                               axi_rv_plic_aw_ready;
  aic_rv_plic_reg_pkg::axi_w_ch_h2d_t axi_rv_plic_w;
  logic                               axi_rv_plic_w_ready;
  aic_rv_plic_reg_pkg::axi_b_ch_d2h_t axi_rv_plic_b;
  logic                               axi_rv_plic_b_ready;
  aic_rv_plic_reg_pkg::axi_a_ch_h2d_t axi_rv_plic_ar;
  logic                               axi_rv_plic_ar_ready;
  aic_rv_plic_reg_pkg::axi_r_ch_d2h_t axi_rv_plic_r;
  logic                               axi_rv_plic_r_ready;

  aic_rv_plic #(
    .LevelEdgeTrig('0),
    .SyncStages   (3)
  ) u_aic_rv_plic (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    .axi_aw_i   (axi_rv_plic_aw),
    .axi_awready(axi_rv_plic_aw_ready),
    .axi_w_i    (axi_rv_plic_w),
    .axi_wready (axi_rv_plic_w_ready),
    .axi_b_o    (axi_rv_plic_b),
    .axi_bready (axi_rv_plic_b_ready),
    .axi_ar_i   (axi_rv_plic_ar),
    .axi_arready(axi_rv_plic_ar_ready),
    .axi_r_o    (axi_rv_plic_r),
    .axi_rready (axi_rv_plic_r_ready),
    .devmode_i  (1'b1),
    .intr_src_i (irq_sources),
    .irq_o      (irq_to_cva6),
    .irq_id_o   (/* open */), // ASO-UNUSED_OUTPUT : Not used according to @florian.zaruba.
    .msip_o     (irq_to_cva6_software)
  );

  //////////////////////
  // TIMESTAMP LOGGER //
  //////////////////////

  aic_infra_pkg::axi_lt_config_s_aw_t axi_timestamp_logger_aw;
  logic                               axi_timestamp_logger_aw_valid;
  logic                               axi_timestamp_logger_aw_ready;
  aic_infra_pkg::axi_lt_w_t           axi_timestamp_logger_w;
  logic                               axi_timestamp_logger_w_valid;
  logic                               axi_timestamp_logger_w_ready;
  aic_infra_pkg::axi_lt_config_s_b_t  axi_timestamp_logger_b;
  logic                               axi_timestamp_logger_b_valid;
  logic                               axi_timestamp_logger_b_ready;
  aic_infra_pkg::axi_lt_config_s_ar_t axi_timestamp_logger_ar;
  logic                               axi_timestamp_logger_ar_valid;
  logic                               axi_timestamp_logger_ar_ready;
  aic_infra_pkg::axi_lt_config_s_r_t  axi_timestamp_logger_r;
  logic                               axi_timestamp_logger_r_valid;
  logic                               axi_timestamp_logger_r_ready;

  aic_cd_pkg::timestamp_trigger_id_t  aic_cd_timestamp_id;
  logic                               aic_cd_timestamp_active_pulse;

  localparam int unsigned NumTimeLogTransferBusses = 3;
  // Note: This is too wide, though should not matter as we are not using it as a signal
  typedef enum int unsigned {
    AxiTimeLogPortIdxMan    = 0,
    AxiTimeLogPortIdxAtu    = 1,
    AxiTimeLogPortIdxFabric = 2
  } axi_timelog_bus_idx_e;

  aic_infra_pkg::axi_lt_config_m_aw_t axi_timelog_aw[NumTimeLogTransferBusses];
  logic                               axi_timelog_aw_valid[NumTimeLogTransferBusses];
  logic                               axi_timelog_aw_ready[NumTimeLogTransferBusses];
  aic_infra_pkg::axi_lt_w_t           axi_timelog_w[NumTimeLogTransferBusses];
  logic                               axi_timelog_w_valid[NumTimeLogTransferBusses];
  logic                               axi_timelog_w_ready[NumTimeLogTransferBusses];
  aic_infra_pkg::axi_lt_config_m_b_t  axi_timelog_b[NumTimeLogTransferBusses];
  logic                               axi_timelog_b_valid[NumTimeLogTransferBusses];
  logic                               axi_timelog_b_ready[NumTimeLogTransferBusses];
  aic_infra_pkg::axi_lt_config_m_ar_t axi_timelog_ar[NumTimeLogTransferBusses];
  logic                               axi_timelog_ar_valid[NumTimeLogTransferBusses];
  logic                               axi_timelog_ar_ready[NumTimeLogTransferBusses];
  aic_infra_pkg::axi_lt_config_m_r_t  axi_timelog_r[NumTimeLogTransferBusses];
  logic                               axi_timelog_r_valid[NumTimeLogTransferBusses];
  logic                               axi_timelog_r_ready[NumTimeLogTransferBusses];

  timestamp_logger_aic #(
    .AxiSIdWidth     (aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW),
    .AxiMIdWidth     (aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH),
    .AxiAddrWidth   (aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiDataWidth   (aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
    .sram_impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
    .sram_impl_oup_t(axe_tcl_sram_pkg::impl_oup_t),
    .REGION_ST_ADDR('{aipu_addr_map_pkg::AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR_ST_ADDR,
                      aipu_addr_map_pkg::AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM_ST_ADDR}),
    .REGION_END_ADDR('{aipu_addr_map_pkg::AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR_END_ADDR,
                      aipu_addr_map_pkg::AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM_END_ADDR})
  ) u_timestamp_logger (
    .i_clk,
    .i_rst_n,

    .i_scan_en,

    .i_sync_start(global_sync_timestamplogger),

    .i_m_ifd0_st(dmc_ts_start_q[dmc_pkg::m_ifd0_idx]),
    .i_m_ifd1_st(dmc_ts_start_q[dmc_pkg::m_ifd1_idx]),
    .i_m_ifd2_st(dmc_ts_start_q[dmc_pkg::m_ifd2_idx]),
    .i_m_ifdw_st(dmc_ts_start_q[dmc_pkg::m_ifdw_idx]),
    .i_d_ifd0_st(dmc_ts_start_q[dmc_pkg::d_ifd0_idx]),
    .i_d_ifd1_st(dmc_ts_start_q[dmc_pkg::d_ifd1_idx]),
    .i_m_odr_st(dmc_ts_start_q[dmc_pkg::m_odr_idx]),
    .i_d_odr_st(dmc_ts_start_q[dmc_pkg::d_odr_idx]),
    .i_mid_mvmexe_st(mid_ts_start_q[aic_mid_pkg::EndPointTSMvmPrg]),
    .i_mid_mvmprg_st(mid_ts_start_q[aic_mid_pkg::EndPointTSMvmPrg]),
    .i_mid_iau_st(mid_ts_start_q[aic_mid_pkg::EndPointTSIau]),
    .i_mid_dpu_st(mid_ts_start_q[aic_mid_pkg::EndPointTSDpu]),
    .i_did_dwpu_st(did_ts_start_q[aic_did_pkg::EndPointDwpu]),
    .i_did_iau_st(did_ts_start_q[aic_did_pkg::EndPointIau]),
    .i_did_dpu_st(did_ts_start_q[aic_did_pkg::EndPointDpu]),
    .i_dma_ch0_st(ht_dma_ts_start[0]),
    .i_dma_ch1_st(ht_dma_ts_start[1]),

    .i_m_ifd0_end(dmc_ts_end_q[dmc_pkg::m_ifd0_idx]),
    .i_m_ifd1_end(dmc_ts_end_q[dmc_pkg::m_ifd1_idx]),
    .i_m_ifd2_end(dmc_ts_end_q[dmc_pkg::m_ifd2_idx]),
    .i_m_ifdw_end(dmc_ts_end_q[dmc_pkg::m_ifdw_idx]),
    .i_d_ifd0_end(dmc_ts_end_q[dmc_pkg::d_ifd0_idx]),
    .i_d_ifd1_end(dmc_ts_end_q[dmc_pkg::d_ifd1_idx]),
    .i_m_odr_end(dmc_ts_end_q[dmc_pkg::m_odr_idx]),
    .i_d_odr_end(dmc_ts_end_q[dmc_pkg::d_odr_idx]),
    .i_mid_mvmexe_end(mid_ts_end_q[aic_mid_pkg::EndPointTSMvmPrg]),
    .i_mid_mvmprg_end(mid_ts_end_q[aic_mid_pkg::EndPointTSMvmPrg]),
    .i_mid_iau_end(mid_ts_end_q[aic_mid_pkg::EndPointTSIau]),
    .i_mid_dpu_end(mid_ts_end_q[aic_mid_pkg::EndPointTSDpu]),
    .i_did_dwpu_end(did_ts_end_q[aic_did_pkg::EndPointDwpu]),
    .i_did_iau_end(did_ts_end_q[aic_did_pkg::EndPointIau]),
    .i_did_dpu_end(did_ts_end_q[aic_did_pkg::EndPointDpu]),
    .i_dma_ch0_end(ht_dma_ts_end[0]),
    .i_dma_ch1_end(ht_dma_ts_end[1]),

    .i_acd_trigger(aic_cd_timestamp_active_pulse),
    .i_acd_message(aic_cd_timestamp_id),

    .i_pc_0_valid(cva6v_perf_event_0_0_delta[0]),
    .i_pc_0      (cva6v_perf_event_0_addr),
    .i_pc_1_valid(cva6v_perf_event_1_0_delta[0]),
    .i_pc_1      (cva6v_perf_event_1_addr),

    .i_st_valid(axi_cva6v_aw_valid & axi_cva6v_aw_ready),
    .i_st_addr (axi_cva6v_aw.addr),

    .i_ld_valid(axi_cva6v_ar_valid & axi_cva6v_ar_ready),
    .i_ld_addr (axi_cva6v_ar.addr),

    .i_axi_s_aw_id   (axi_timestamp_logger_aw.id),
    .i_axi_s_aw_addr (axi_timestamp_logger_aw.addr),
    .i_axi_s_aw_len  (axi_timestamp_logger_aw.len),
    .i_axi_s_aw_size (axi_timestamp_logger_aw.size),
    .i_axi_s_aw_burst(axi_timestamp_logger_aw.burst),
    .i_axi_s_aw_valid(axi_timestamp_logger_aw_valid),
    .o_axi_s_aw_ready(axi_timestamp_logger_aw_ready),

    .i_axi_s_w_data  (axi_timestamp_logger_w.data),
    .i_axi_s_w_strb  (axi_timestamp_logger_w.strb),
    .i_axi_s_w_last  (axi_timestamp_logger_w.last),
    .i_axi_s_w_valid (axi_timestamp_logger_w_valid),
    .o_axi_s_w_ready (axi_timestamp_logger_w_ready),

    .o_axi_s_b_id    (axi_timestamp_logger_b.id),
    .o_axi_s_b_resp  (axi_timestamp_logger_b.resp),
    .o_axi_s_b_valid (axi_timestamp_logger_b_valid),
    .i_axi_s_b_ready (axi_timestamp_logger_b_ready),

    .i_axi_s_ar_id   (axi_timestamp_logger_ar.id),
    .i_axi_s_ar_addr (axi_timestamp_logger_ar.addr),
    .i_axi_s_ar_len  (axi_timestamp_logger_ar.len),
    .i_axi_s_ar_size (axi_timestamp_logger_ar.size),
    .i_axi_s_ar_burst(axi_timestamp_logger_ar.burst),
    .i_axi_s_ar_valid(axi_timestamp_logger_ar_valid),
    .o_axi_s_ar_ready(axi_timestamp_logger_ar_ready),

    .o_axi_s_r_id    (axi_timestamp_logger_r.id),
    .o_axi_s_r_data  (axi_timestamp_logger_r.data),
    .o_axi_s_r_resp  (axi_timestamp_logger_r.resp),
    .o_axi_s_r_last  (axi_timestamp_logger_r.last),
    .o_axi_s_r_valid (axi_timestamp_logger_r_valid),
    .i_axi_s_r_ready (axi_timestamp_logger_r_ready),

    .o_axi_m_aw_id   (axi_timelog_aw[AxiTimeLogPortIdxMan].id),
    .o_axi_m_aw_addr (axi_timelog_aw[AxiTimeLogPortIdxMan].addr),
    .o_axi_m_aw_len  (axi_timelog_aw[AxiTimeLogPortIdxMan].len),
    .o_axi_m_aw_size (axi_timelog_aw[AxiTimeLogPortIdxMan].size),
    .o_axi_m_aw_burst(axi_timelog_aw[AxiTimeLogPortIdxMan].burst),
    .o_axi_m_aw_valid(axi_timelog_aw_valid[AxiTimeLogPortIdxMan]),
    .i_axi_m_aw_ready(axi_timelog_aw_ready[AxiTimeLogPortIdxMan]),

    .o_axi_m_w_data  (axi_timelog_w[AxiTimeLogPortIdxMan].data),
    .o_axi_m_w_strb  (axi_timelog_w[AxiTimeLogPortIdxMan].strb),
    .o_axi_m_w_last  (axi_timelog_w[AxiTimeLogPortIdxMan].last),
    .o_axi_m_w_valid (axi_timelog_w_valid[AxiTimeLogPortIdxMan]),
    .i_axi_m_w_ready (axi_timelog_w_ready[AxiTimeLogPortIdxMan]),

    .i_axi_m_b_id    (axi_timelog_b[AxiTimeLogPortIdxMan].id),
    .i_axi_m_b_resp  (axi_timelog_b[AxiTimeLogPortIdxMan].resp),
    .i_axi_m_b_valid (axi_timelog_b_valid[AxiTimeLogPortIdxMan]),
    .o_axi_m_b_ready (axi_timelog_b_ready[AxiTimeLogPortIdxMan]),

    .o_axi_m_ar_id   (axi_timelog_ar[AxiTimeLogPortIdxMan].id),
    .o_axi_m_ar_addr (axi_timelog_ar[AxiTimeLogPortIdxMan].addr),
    .o_axi_m_ar_len  (axi_timelog_ar[AxiTimeLogPortIdxMan].len),
    .o_axi_m_ar_size (axi_timelog_ar[AxiTimeLogPortIdxMan].size),
    .o_axi_m_ar_burst(axi_timelog_ar[AxiTimeLogPortIdxMan].burst),
    .o_axi_m_ar_valid(axi_timelog_ar_valid[AxiTimeLogPortIdxMan]),
    .i_axi_m_ar_ready(axi_timelog_ar_ready[AxiTimeLogPortIdxMan]),

    .i_axi_m_r_id    (axi_timelog_r[AxiTimeLogPortIdxMan].id),
    .i_axi_m_r_data  (axi_timelog_r[AxiTimeLogPortIdxMan].data),
    .i_axi_m_r_resp  (axi_timelog_r[AxiTimeLogPortIdxMan].resp),
    .i_axi_m_r_last  (axi_timelog_r[AxiTimeLogPortIdxMan].last),
    .i_axi_m_r_valid (axi_timelog_r_valid[AxiTimeLogPortIdxMan]),
    .o_axi_m_r_ready (axi_timelog_r_ready[AxiTimeLogPortIdxMan]),

    .i_sram_impl     (sram_impl_inp[aic_infra_pkg::SRAM_IMPL_IDX_TIMESTAMP_LOGGER]),
    .o_sram_impl     (sram_impl_oup[aic_infra_pkg::SRAM_IMPL_IDX_TIMESTAMP_LOGGER])
  );

  //////////////////////////////////////////////
  // TimestampLogger Address Translation Unit //
  //////////////////////////////////////////////
  aic_infra_pkg::timelog_atu_entry_t timelog_atu_entries[aic_csr_reg_pkg::TIMELOG_ATU_ENTRIES];

  for (genvar entry_idx = 0; entry_idx < aic_csr_reg_pkg::TIMELOG_ATU_ENTRIES; entry_idx++) begin : gen_timelog_atu_entries
    always_comb timelog_atu_entries[entry_idx] = '{
        first:     reg2hw.timelog_atu_first[entry_idx].q,
        last:      reg2hw.timelog_atu_last[entry_idx].q,
        base:      reg2hw.timelog_atu_base[entry_idx].q,
        valid:     reg2hw.timelog_atu_cfg[entry_idx].valid.q,
        read_only: reg2hw.timelog_atu_cfg[entry_idx].read_only.q
        };
  end

  // Note: atop, cache, prot and lock are not used:
  always_comb begin
    axi_timelog_aw[AxiTimeLogPortIdxMan].atop = axi_pkg::axi_atop_t'(0);
    axi_timelog_aw[AxiTimeLogPortIdxMan].lock = '0;
    axi_timelog_ar[AxiTimeLogPortIdxMan].lock = '0;
    axi_timelog_aw[AxiTimeLogPortIdxMan].cache = '0;
    axi_timelog_ar[AxiTimeLogPortIdxMan].cache = '0;
    axi_timelog_aw[AxiTimeLogPortIdxMan].prot = '0;
    axi_timelog_ar[AxiTimeLogPortIdxMan].prot = '0;
  end


  axe_axi_atu #(
    .AxiIdWidth         (aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH),
    .AxiSubPortAddrWidth(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiManPortAddrWidth(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiSubPortMaxTxns  (aic_infra_pkg::AxiMaxTxns),
    .SupportAtops       (1'b0), // There should be no atomics at this stage
    .L1PageOffsetSize   (aic_csr_reg_pkg::TIMELOG_ATU_PO_SIZE),
    .L1NumEntries       (aic_csr_reg_pkg::TIMELOG_ATU_ENTRIES),
    .L1CutAx            (1'b1), // To be safe
    .axi_s_aw_t         (aic_infra_pkg::axi_lt_config_m_aw_t),
    .axi_m_aw_t         (aic_infra_pkg::axi_lt_config_m_aw_t),
    .axi_w_t            (aic_infra_pkg::axi_lt_w_t),
    .axi_b_t            (aic_infra_pkg::axi_lt_config_m_b_t),
    .axi_s_ar_t         (aic_infra_pkg::axi_lt_config_m_ar_t),
    .axi_m_ar_t         (aic_infra_pkg::axi_lt_config_m_ar_t),
    .axi_r_t            (aic_infra_pkg::axi_lt_config_m_r_t),
    .entry_t            (aic_infra_pkg::timelog_atu_entry_t)
  ) u_timelog_axe_axi_atu (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_timelog_aw[AxiTimeLogPortIdxMan]),
    .i_axi_s_aw_valid(axi_timelog_aw_valid[AxiTimeLogPortIdxMan]),
    .o_axi_s_aw_ready(axi_timelog_aw_ready[AxiTimeLogPortIdxMan]),
    .i_axi_s_w       (axi_timelog_w[AxiTimeLogPortIdxMan]),
    .i_axi_s_w_valid (axi_timelog_w_valid[AxiTimeLogPortIdxMan]),
    .o_axi_s_w_ready (axi_timelog_w_ready[AxiTimeLogPortIdxMan]),
    .o_axi_s_b       (axi_timelog_b[AxiTimeLogPortIdxMan]),
    .o_axi_s_b_valid (axi_timelog_b_valid[AxiTimeLogPortIdxMan]),
    .i_axi_s_b_ready (axi_timelog_b_ready[AxiTimeLogPortIdxMan]),
    .i_axi_s_ar      (axi_timelog_ar[AxiTimeLogPortIdxMan]),
    .i_axi_s_ar_valid(axi_timelog_ar_valid[AxiTimeLogPortIdxMan]),
    .o_axi_s_ar_ready(axi_timelog_ar_ready[AxiTimeLogPortIdxMan]),
    .o_axi_s_r       (axi_timelog_r[AxiTimeLogPortIdxMan]),
    .o_axi_s_r_valid (axi_timelog_r_valid[AxiTimeLogPortIdxMan]),
    .i_axi_s_r_ready (axi_timelog_r_ready[AxiTimeLogPortIdxMan]),
    .o_axi_m_aw      (axi_timelog_aw[AxiTimeLogPortIdxAtu]),
    .o_axi_m_aw_valid(axi_timelog_aw_valid[AxiTimeLogPortIdxAtu]),
    .i_axi_m_aw_ready(axi_timelog_aw_ready[AxiTimeLogPortIdxAtu]),
    .o_axi_m_w       (axi_timelog_w[AxiTimeLogPortIdxAtu]),
    .o_axi_m_w_valid (axi_timelog_w_valid[AxiTimeLogPortIdxAtu]),
    .i_axi_m_w_ready (axi_timelog_w_ready[AxiTimeLogPortIdxAtu]),
    .i_axi_m_b       (axi_timelog_b[AxiTimeLogPortIdxAtu]),
    .i_axi_m_b_valid (axi_timelog_b_valid[AxiTimeLogPortIdxAtu]),
    .o_axi_m_b_ready (axi_timelog_b_ready[AxiTimeLogPortIdxAtu]),
    .o_axi_m_ar      (axi_timelog_ar[AxiTimeLogPortIdxAtu]),
    .o_axi_m_ar_valid(axi_timelog_ar_valid[AxiTimeLogPortIdxAtu]),
    .i_axi_m_ar_ready(axi_timelog_ar_ready[AxiTimeLogPortIdxAtu]),
    .i_axi_m_r       (axi_timelog_r[AxiTimeLogPortIdxAtu]),
    .i_axi_m_r_valid (axi_timelog_r_valid[AxiTimeLogPortIdxAtu]),
    .o_axi_m_r_ready (axi_timelog_r_ready[AxiTimeLogPortIdxAtu]),
    .i_entries       (timelog_atu_entries),
    .i_bypass        (reg2hw.atu_bypass.timelog.q)
  );

  axe_axi_cut #(
    .CutAw   (1'b1), // Breaks long path
    .CutW    (1'b1), // Breaks long path
    .CutB    (1'b0),
    .CutAr   (1'b1), // Breaks long path
    .CutR    (1'b0),
    .axi_aw_t(aic_infra_pkg::axi_lt_config_m_aw_t),
    .axi_w_t (aic_infra_pkg::axi_lt_w_t),
    .axi_b_t (aic_infra_pkg::axi_lt_config_m_b_t),
    .axi_ar_t(aic_infra_pkg::axi_lt_config_m_ar_t),
    .axi_r_t (aic_infra_pkg::axi_lt_config_m_r_t)
  ) u_timestamp_axe_axi_cut (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_timelog_aw[AxiTimeLogPortIdxAtu]),
    .i_axi_s_aw_valid(axi_timelog_aw_valid[AxiTimeLogPortIdxAtu]),
    .o_axi_s_aw_ready(axi_timelog_aw_ready[AxiTimeLogPortIdxAtu]),
    .i_axi_s_w       (axi_timelog_w[AxiTimeLogPortIdxAtu]),
    .i_axi_s_w_valid (axi_timelog_w_valid[AxiTimeLogPortIdxAtu]),
    .o_axi_s_w_ready (axi_timelog_w_ready[AxiTimeLogPortIdxAtu]),
    .o_axi_s_b       (axi_timelog_b[AxiTimeLogPortIdxAtu]),
    .o_axi_s_b_valid (axi_timelog_b_valid[AxiTimeLogPortIdxAtu]),
    .i_axi_s_b_ready (axi_timelog_b_ready[AxiTimeLogPortIdxAtu]),
    .i_axi_s_ar      (axi_timelog_ar[AxiTimeLogPortIdxAtu]),
    .i_axi_s_ar_valid(axi_timelog_ar_valid[AxiTimeLogPortIdxAtu]),
    .o_axi_s_ar_ready(axi_timelog_ar_ready[AxiTimeLogPortIdxAtu]),
    .o_axi_s_r       (axi_timelog_r[AxiTimeLogPortIdxAtu]),
    .o_axi_s_r_valid (axi_timelog_r_valid[AxiTimeLogPortIdxAtu]),
    .i_axi_s_r_ready (axi_timelog_r_ready[AxiTimeLogPortIdxAtu]),
    .o_axi_m_aw      (axi_timelog_aw[AxiTimeLogPortIdxFabric]),
    .o_axi_m_aw_valid(axi_timelog_aw_valid[AxiTimeLogPortIdxFabric]),
    .i_axi_m_aw_ready(axi_timelog_aw_ready[AxiTimeLogPortIdxFabric]),
    .o_axi_m_w       (axi_timelog_w[AxiTimeLogPortIdxFabric]),
    .o_axi_m_w_valid (axi_timelog_w_valid[AxiTimeLogPortIdxFabric]),
    .i_axi_m_w_ready (axi_timelog_w_ready[AxiTimeLogPortIdxFabric]),
    .i_axi_m_b       (axi_timelog_b[AxiTimeLogPortIdxFabric]),
    .i_axi_m_b_valid (axi_timelog_b_valid[AxiTimeLogPortIdxFabric]),
    .o_axi_m_b_ready (axi_timelog_b_ready[AxiTimeLogPortIdxFabric]),
    .o_axi_m_ar      (axi_timelog_ar[AxiTimeLogPortIdxFabric]),
    .o_axi_m_ar_valid(axi_timelog_ar_valid[AxiTimeLogPortIdxFabric]),
    .i_axi_m_ar_ready(axi_timelog_ar_ready[AxiTimeLogPortIdxFabric]),
    .i_axi_m_r       (axi_timelog_r[AxiTimeLogPortIdxFabric]),
    .i_axi_m_r_valid (axi_timelog_r_valid[AxiTimeLogPortIdxFabric]),
    .o_axi_m_r_ready (axi_timelog_r_ready[AxiTimeLogPortIdxFabric])
  );


  ////////////
  // LT DMA //
  ////////////
  // Note, this is taken straight from the wrapper, some sanity id done in elaboration...
  localparam int unsigned LtDmaDebugChannelNumWidth =
      cc_math_pkg::index_width(snps_dma_pkg::SNPS_DMA_AIC_LT_CFG.dma_nbr_channels);
  localparam int unsigned LtDmaDebugWidth =
        snps_dma_pkg::SNPS_DMA_AIC_LT_CFG.dma_nbr_ports * ($clog2(snps_dma_pkg::SNPS_DMA_AIC_LT_CFG.dma_nbr_channels) + 2)
      + snps_dma_pkg::SNPS_DMA_AIC_LT_CFG.dma_nbr_ports * ($clog2(snps_dma_pkg::SNPS_DMA_AIC_LT_CFG.dma_nbr_channels) + 2)
      + ((snps_dma_pkg::SNPS_DMA_AIC_LT_CFG.dma_nbr_ports * 3) + 1) * snps_dma_pkg::SNPS_DMA_AIC_LT_CFG.dma_nbr_channels
      + 12;

  if (LtDmaDebugChannelNumWidth != $bits(reg2hw.lt_dma_debug_ctrl.q)) $fatal(1, "LtDmaDebugChannelNumWidth != $bits(reg2hw.lt_dma_debug_ctrl.q) does not match!");
  if (LtDmaDebugWidth           != $bits(hw2reg.lt_dma_debug.d))      $fatal(1, "LtDmaDebugWidth != $bits(hw2reg.lt_dma_debug.d) does not match!");

  localparam int unsigned NumLtDmaTransferBusses = 3;
  // Note: This is too wide, though should not matter as we are not using it as a signal
  typedef enum int unsigned {
    AxiLtDmaPortIdxMan    = 0,
    AxiLtDmaPortIdxAtu    = 1,
    AxiLtDmaPortIdxFabric = 2
  } axi_lt_dma_bus_idx_e;

  aic_infra_pkg::axi_lt_config_s_aw_t axi_lt_dma_config_aw;
  logic                               axi_lt_dma_config_aw_valid;
  logic                               axi_lt_dma_config_aw_ready;
  aic_infra_pkg::axi_lt_w_t           axi_lt_dma_config_w;
  logic                               axi_lt_dma_config_w_valid;
  logic                               axi_lt_dma_config_w_ready;
  aic_infra_pkg::axi_lt_config_s_b_t  axi_lt_dma_config_b;
  logic                               axi_lt_dma_config_b_valid;
  logic                               axi_lt_dma_config_b_ready;
  aic_infra_pkg::axi_lt_config_s_ar_t axi_lt_dma_config_ar;
  logic                               axi_lt_dma_config_ar_valid;
  logic                               axi_lt_dma_config_ar_ready;
  aic_infra_pkg::axi_lt_config_s_r_t  axi_lt_dma_config_r;
  logic                               axi_lt_dma_config_r_valid;
  logic                               axi_lt_dma_config_r_ready;

  aic_infra_pkg::axi_lt_config_m_aw_t axi_lt_dma_transfer_aw[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_aw_valid[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_aw_ready[NumLtDmaTransferBusses];
  aic_infra_pkg::axi_lt_w_t           axi_lt_dma_transfer_w[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_w_valid[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_w_ready[NumLtDmaTransferBusses];
  aic_infra_pkg::axi_lt_config_m_b_t  axi_lt_dma_transfer_b[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_b_valid[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_b_ready[NumLtDmaTransferBusses];
  aic_infra_pkg::axi_lt_config_m_ar_t axi_lt_dma_transfer_ar[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_ar_valid[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_ar_ready[NumLtDmaTransferBusses];
  aic_infra_pkg::axi_lt_config_m_r_t  axi_lt_dma_transfer_r[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_r_valid[NumLtDmaTransferBusses];
  logic                               axi_lt_dma_transfer_r_ready[NumLtDmaTransferBusses];

  snps_dma #(
    .DMA_VERSION("aic_lt"),
    .SL_AW(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .SL_DW(aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
    .SL_IDW(aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW),
    .SL_BW(axi_pkg::AXI_LEN_WIDTH)
  ) u_lt_aic_dma (
    .i_clk,
    .i_rst_n,
    .i_test_mode(i_scan_en),
    ///// AXI slave:
    // Write Address Channel
    .i_awid         (axi_lt_dma_config_aw.id),
    .i_awaddr       (axi_lt_dma_config_aw.addr),
    .i_awlen        (axi_lt_dma_config_aw.len),
    .i_awsize       (axi_lt_dma_config_aw.size),
    .i_awburst      (axi_lt_dma_config_aw.burst),
    .i_awvalid      (axi_lt_dma_config_aw_valid),
    .o_awready      (axi_lt_dma_config_aw_ready),
    // Read Address Channel
    .i_arid         (axi_lt_dma_config_ar.id),
    .i_araddr       (axi_lt_dma_config_ar.addr),
    .i_arlen        (axi_lt_dma_config_ar.len),
    .i_arsize       (axi_lt_dma_config_ar.size),
    .i_arburst      (axi_lt_dma_config_ar.burst),
    .i_arvalid      (axi_lt_dma_config_ar_valid),
    .o_arready      (axi_lt_dma_config_ar_ready),
    // Write  Data Channel
    .i_wdata        (axi_lt_dma_config_w.data),
    .i_wstrb        (axi_lt_dma_config_w.strb),
    .i_wlast        (axi_lt_dma_config_w.last),
    .i_wvalid       (axi_lt_dma_config_w_valid),
    .o_wready       (axi_lt_dma_config_w_ready),
    // Read Data Channel
    .o_rid          (axi_lt_dma_config_r.id),
    .o_rdata        (axi_lt_dma_config_r.data),
    .o_rresp        (axi_lt_dma_config_r.resp),
    .o_rlast        (axi_lt_dma_config_r.last),
    .o_rvalid       (axi_lt_dma_config_r_valid),
    .i_rready       (axi_lt_dma_config_r_ready),
    // Write Response Channel
    .o_bid          (axi_lt_dma_config_b.id),
    .o_bresp        (axi_lt_dma_config_b.resp),
    .o_bvalid       (axi_lt_dma_config_b_valid),
    .i_bready       (axi_lt_dma_config_b_ready),
    ///// Masters:
    // Write Address Channel
    .o_axi_m_awid   (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxMan].id),
    .o_axi_m_awaddr (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxMan].addr),
    .o_axi_m_awlen  (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxMan].len),
    .o_axi_m_awsize (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxMan].size),
    .o_axi_m_awburst(axi_lt_dma_transfer_aw[AxiLtDmaPortIdxMan].burst),
    .o_axi_m_awlock (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxMan].lock),
    .o_axi_m_awcache(axi_lt_dma_transfer_aw[AxiLtDmaPortIdxMan].cache),
    .o_axi_m_awprot (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxMan].prot),
    .o_axi_m_awvalid(axi_lt_dma_transfer_aw_valid[AxiLtDmaPortIdxMan]),
    .i_axi_m_awready(axi_lt_dma_transfer_aw_ready[AxiLtDmaPortIdxMan]),
    // Read Address Channel
    .o_axi_m_arid   (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxMan].id),
    .o_axi_m_araddr (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxMan].addr),
    .o_axi_m_arlen  (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxMan].len),
    .o_axi_m_arsize (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxMan].size),
    .o_axi_m_arburst(axi_lt_dma_transfer_ar[AxiLtDmaPortIdxMan].burst),
    .o_axi_m_arlock (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxMan].lock),
    .o_axi_m_arcache(axi_lt_dma_transfer_ar[AxiLtDmaPortIdxMan].cache),
    .o_axi_m_arprot (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxMan].prot),
    .o_axi_m_arvalid(axi_lt_dma_transfer_ar_valid[AxiLtDmaPortIdxMan]),
    .i_axi_m_arready(axi_lt_dma_transfer_ar_valid[AxiLtDmaPortIdxMan]),
    // Write  Data Channel
    .o_axi_m_wdata  (axi_lt_dma_transfer_w[AxiLtDmaPortIdxMan].data),
    .o_axi_m_wstrb  (axi_lt_dma_transfer_w[AxiLtDmaPortIdxMan].strb),
    .o_axi_m_wlast  (axi_lt_dma_transfer_w[AxiLtDmaPortIdxMan].last),
    .o_axi_m_wvalid (axi_lt_dma_transfer_w_valid[AxiLtDmaPortIdxMan]),
    .i_axi_m_wready (axi_lt_dma_transfer_w_ready[AxiLtDmaPortIdxMan]),
    // Read Data Channel
    .i_axi_m_rid    (axi_lt_dma_transfer_r[AxiLtDmaPortIdxMan].id),
    .i_axi_m_rdata  (axi_lt_dma_transfer_r[AxiLtDmaPortIdxMan].data),
    .i_axi_m_rresp  (axi_lt_dma_transfer_r[AxiLtDmaPortIdxMan].resp),
    .i_axi_m_rlast  (axi_lt_dma_transfer_r[AxiLtDmaPortIdxMan].last),
    .i_axi_m_rvalid (axi_lt_dma_transfer_r_valid[AxiLtDmaPortIdxMan]),
    .o_axi_m_rready (axi_lt_dma_transfer_r_ready[AxiLtDmaPortIdxMan]),
    // Write Response Channel
    .i_axi_m_bid    (axi_lt_dma_transfer_b[AxiLtDmaPortIdxMan].id),
    .i_axi_m_bresp  (axi_lt_dma_transfer_b[AxiLtDmaPortIdxMan].resp),
    .i_axi_m_bvalid (axi_lt_dma_transfer_b_valid[AxiLtDmaPortIdxMan]),
    .o_axi_m_bready (axi_lt_dma_transfer_b_ready[AxiLtDmaPortIdxMan]),
    // Interrupts
    .o_irq_ch       (irq_sources[aic_infra_pkg::IRQ_IDX_DMA_LT_CHANNEL_0]),
    .o_irq_cmn      (irq_sources[aic_infra_pkg::IRQ_IDX_DMA_LT_COMMON]),
    // SRAM config registers
    .i_impl_inp     (sram_impl_inp[aic_infra_pkg::SRAM_IMPL_IDX_LT_AIC_DMA]),
    .o_impl_oup     (sram_impl_oup[aic_infra_pkg::SRAM_IMPL_IDX_LT_AIC_DMA]),
    // Tokens:
    .o_tok_prod_vld(),
    .i_tok_prod_rdy('1),
    .i_tok_cons_vld('0),
    .o_tok_cons_rdy(),
    // Timestamp:
    .o_ts_start(),
    .o_ts_end(),
    // ACD sync:
    .o_acd_sync(), // Is not being used
    // Debug signals
    .i_debug_ch_num (reg2hw.lt_dma_debug_ctrl.q),
    .o_dma_debug    (hw2reg.lt_dma_debug.d)
  );

  /////////////////////////////////////
  // LT DMA Address Translation Unit //
  /////////////////////////////////////
  aic_infra_pkg::lt_atu_entry_t lt_atu_entries[aic_csr_reg_pkg::LT_DMA_ATU_ENTRIES];

  for (genvar entry_idx = 0; entry_idx < aic_csr_reg_pkg::LT_DMA_ATU_ENTRIES; entry_idx++) begin : gen_lt_atu_entries
    always_comb lt_atu_entries[entry_idx] = '{
        first:     reg2hw.lt_dma_atu_first[entry_idx].q,
        last:      reg2hw.lt_dma_atu_last[entry_idx].q,
        base:      reg2hw.lt_dma_atu_base[entry_idx].q,
        valid:     reg2hw.lt_dma_atu_cfg[entry_idx].valid.q,
        read_only: reg2hw.lt_dma_atu_cfg[entry_idx].read_only.q
        };
  end

  // Note: atop is not used, however still needs to be defined in the struct, setting to sensible default
  always_comb axi_lt_dma_transfer_aw[0].atop = axi_pkg::axi_atop_t'(0);

  axe_axi_atu #(
    .AxiIdWidth         (aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH),
    .AxiSubPortAddrWidth(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiManPortAddrWidth(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiSubPortMaxTxns  (aic_infra_pkg::AxiMaxTxns),
    .SupportAtops       (1'b0), // There should be no atomics at this stage
    .L1PageOffsetSize   (aic_csr_reg_pkg::LT_DMA_ATU_PO_SIZE),
    .L1NumEntries       (aic_csr_reg_pkg::LT_DMA_ATU_ENTRIES),
    .L1CutAx            (1'b1), // To be safe
    .axi_s_aw_t         (aic_infra_pkg::axi_lt_config_m_aw_t),
    .axi_m_aw_t         (aic_infra_pkg::axi_lt_config_m_aw_t),
    .axi_w_t            (aic_infra_pkg::axi_lt_w_t),
    .axi_b_t            (aic_infra_pkg::axi_lt_config_m_b_t),
    .axi_s_ar_t         (aic_infra_pkg::axi_lt_config_m_ar_t),
    .axi_m_ar_t         (aic_infra_pkg::axi_lt_config_m_ar_t),
    .axi_r_t            (aic_infra_pkg::axi_lt_config_m_r_t),
    .entry_t            (aic_infra_pkg::lt_atu_entry_t)
  ) u_lt_aic_dma_axe_axi_atu (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxMan]),
    .i_axi_s_aw_valid(axi_lt_dma_transfer_aw_valid[AxiLtDmaPortIdxMan]),
    .o_axi_s_aw_ready(axi_lt_dma_transfer_aw_ready[AxiLtDmaPortIdxMan]),
    .i_axi_s_w       (axi_lt_dma_transfer_w[AxiLtDmaPortIdxMan]),
    .i_axi_s_w_valid (axi_lt_dma_transfer_w_valid[AxiLtDmaPortIdxMan]),
    .o_axi_s_w_ready (axi_lt_dma_transfer_w_ready[AxiLtDmaPortIdxMan]),
    .o_axi_s_b       (axi_lt_dma_transfer_b[AxiLtDmaPortIdxMan]),
    .o_axi_s_b_valid (axi_lt_dma_transfer_b_valid[AxiLtDmaPortIdxMan]),
    .i_axi_s_b_ready (axi_lt_dma_transfer_b_ready[AxiLtDmaPortIdxMan]),
    .i_axi_s_ar      (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxMan]),
    .i_axi_s_ar_valid(axi_lt_dma_transfer_ar_valid[AxiLtDmaPortIdxMan]),
    .o_axi_s_ar_ready(axi_lt_dma_transfer_ar_ready[AxiLtDmaPortIdxMan]),
    .o_axi_s_r       (axi_lt_dma_transfer_r[AxiLtDmaPortIdxMan]),
    .o_axi_s_r_valid (axi_lt_dma_transfer_r_valid[AxiLtDmaPortIdxMan]),
    .i_axi_s_r_ready (axi_lt_dma_transfer_r_ready[AxiLtDmaPortIdxMan]),
    .o_axi_m_aw      (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxAtu]),
    .o_axi_m_aw_valid(axi_lt_dma_transfer_aw_valid[AxiLtDmaPortIdxAtu]),
    .i_axi_m_aw_ready(axi_lt_dma_transfer_aw_ready[AxiLtDmaPortIdxAtu]),
    .o_axi_m_w       (axi_lt_dma_transfer_w[AxiLtDmaPortIdxAtu]),
    .o_axi_m_w_valid (axi_lt_dma_transfer_w_valid[AxiLtDmaPortIdxAtu]),
    .i_axi_m_w_ready (axi_lt_dma_transfer_w_ready[AxiLtDmaPortIdxAtu]),
    .i_axi_m_b       (axi_lt_dma_transfer_b[AxiLtDmaPortIdxAtu]),
    .i_axi_m_b_valid (axi_lt_dma_transfer_b_valid[AxiLtDmaPortIdxAtu]),
    .o_axi_m_b_ready (axi_lt_dma_transfer_b_ready[AxiLtDmaPortIdxAtu]),
    .o_axi_m_ar      (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxAtu]),
    .o_axi_m_ar_valid(axi_lt_dma_transfer_ar_valid[AxiLtDmaPortIdxAtu]),
    .i_axi_m_ar_ready(axi_lt_dma_transfer_ar_ready[AxiLtDmaPortIdxAtu]),
    .i_axi_m_r       (axi_lt_dma_transfer_r[AxiLtDmaPortIdxAtu]),
    .i_axi_m_r_valid (axi_lt_dma_transfer_r_valid[AxiLtDmaPortIdxAtu]),
    .o_axi_m_r_ready (axi_lt_dma_transfer_r_ready[AxiLtDmaPortIdxAtu]),
    .i_entries       (lt_atu_entries),
    .i_bypass        (reg2hw.atu_bypass.lt_dma.q)
  );

  axe_axi_cut #(
    .CutAw   (1'b1), // Breaks long path
    .CutW    (1'b1), // Breaks long path
    .CutB    (1'b0),
    .CutAr   (1'b1), // Breaks long path
    .CutR    (1'b0),
    .axi_aw_t(aic_infra_pkg::axi_lt_config_m_aw_t),
    .axi_w_t (aic_infra_pkg::axi_lt_w_t),
    .axi_b_t (aic_infra_pkg::axi_lt_config_m_b_t),
    .axi_ar_t(aic_infra_pkg::axi_lt_config_m_ar_t),
    .axi_r_t (aic_infra_pkg::axi_lt_config_m_r_t)
  ) u_lt_aic_dma_axe_axi_cut (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxAtu]),
    .i_axi_s_aw_valid(axi_lt_dma_transfer_aw_valid[AxiLtDmaPortIdxAtu]),
    .o_axi_s_aw_ready(axi_lt_dma_transfer_aw_ready[AxiLtDmaPortIdxAtu]),
    .i_axi_s_w       (axi_lt_dma_transfer_w[AxiLtDmaPortIdxAtu]),
    .i_axi_s_w_valid (axi_lt_dma_transfer_w_valid[AxiLtDmaPortIdxAtu]),
    .o_axi_s_w_ready (axi_lt_dma_transfer_w_ready[AxiLtDmaPortIdxAtu]),
    .o_axi_s_b       (axi_lt_dma_transfer_b[AxiLtDmaPortIdxAtu]),
    .o_axi_s_b_valid (axi_lt_dma_transfer_b_valid[AxiLtDmaPortIdxAtu]),
    .i_axi_s_b_ready (axi_lt_dma_transfer_b_ready[AxiLtDmaPortIdxAtu]),
    .i_axi_s_ar      (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxAtu]),
    .i_axi_s_ar_valid(axi_lt_dma_transfer_ar_valid[AxiLtDmaPortIdxAtu]),
    .o_axi_s_ar_ready(axi_lt_dma_transfer_ar_ready[AxiLtDmaPortIdxAtu]),
    .o_axi_s_r       (axi_lt_dma_transfer_r[AxiLtDmaPortIdxAtu]),
    .o_axi_s_r_valid (axi_lt_dma_transfer_r_valid[AxiLtDmaPortIdxAtu]),
    .i_axi_s_r_ready (axi_lt_dma_transfer_r_ready[AxiLtDmaPortIdxAtu]),
    .o_axi_m_aw      (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxFabric]),
    .o_axi_m_aw_valid(axi_lt_dma_transfer_aw_valid[AxiLtDmaPortIdxFabric]),
    .i_axi_m_aw_ready(axi_lt_dma_transfer_aw_ready[AxiLtDmaPortIdxFabric]),
    .o_axi_m_w       (axi_lt_dma_transfer_w[AxiLtDmaPortIdxFabric]),
    .o_axi_m_w_valid (axi_lt_dma_transfer_w_valid[AxiLtDmaPortIdxFabric]),
    .i_axi_m_w_ready (axi_lt_dma_transfer_w_ready[AxiLtDmaPortIdxFabric]),
    .i_axi_m_b       (axi_lt_dma_transfer_b[AxiLtDmaPortIdxFabric]),
    .i_axi_m_b_valid (axi_lt_dma_transfer_b_valid[AxiLtDmaPortIdxFabric]),
    .o_axi_m_b_ready (axi_lt_dma_transfer_b_ready[AxiLtDmaPortIdxFabric]),
    .o_axi_m_ar      (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxFabric]),
    .o_axi_m_ar_valid(axi_lt_dma_transfer_ar_valid[AxiLtDmaPortIdxFabric]),
    .i_axi_m_ar_ready(axi_lt_dma_transfer_ar_ready[AxiLtDmaPortIdxFabric]),
    .i_axi_m_r       (axi_lt_dma_transfer_r[AxiLtDmaPortIdxFabric]),
    .i_axi_m_r_valid (axi_lt_dma_transfer_r_valid[AxiLtDmaPortIdxFabric]),
    .o_axi_m_r_ready (axi_lt_dma_transfer_r_ready[AxiLtDmaPortIdxFabric])
  );


  ////////////
  // HT DMA //
  ////////////
  localparam int unsigned NumHtDmaTransferBusses = 3;
  // Note: This is too wide, though should not matter as we are not using it as a signal

  typedef enum int unsigned {
    AxiHtDmaPortIdxMan    = (0 * snps_dma_pkg::SNPS_DMA_AIC_HT_CFG.dma_nbr_ports),
    AxiHtDmaPortIdxAtu    = (1 * snps_dma_pkg::SNPS_DMA_AIC_HT_CFG.dma_nbr_ports),
    AxiHtDmaPortIdxFabric = (2 * snps_dma_pkg::SNPS_DMA_AIC_HT_CFG.dma_nbr_ports)
  } axi_ht_dma_bus_idx_e;

  aic_infra_pkg::axi_lt_control_s_aw_t  axi_ht_dma_config_aw;
  logic                                 axi_ht_dma_config_aw_valid;
  logic                                 axi_ht_dma_config_aw_ready;
  aic_infra_pkg::axi_lt_w_t             axi_ht_dma_config_w;
  logic                                 axi_ht_dma_config_w_valid;
  logic                                 axi_ht_dma_config_w_ready;
  aic_infra_pkg::axi_lt_control_s_b_t   axi_ht_dma_config_b;
  logic                                 axi_ht_dma_config_b_valid;
  logic                                 axi_ht_dma_config_b_ready;
  aic_infra_pkg::axi_lt_control_s_ar_t  axi_ht_dma_config_ar;
  logic                                 axi_ht_dma_config_ar_valid;
  logic                                 axi_ht_dma_config_ar_ready;
  aic_infra_pkg::axi_lt_control_s_r_t   axi_ht_dma_config_r;
  logic                                 axi_ht_dma_config_r_valid;
  logic                                 axi_ht_dma_config_r_ready;

  aic_infra_pkg::axi_ht_m_aw_t  axi_ht_dma_transfer_aw[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_aw_valid[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_aw_ready[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  aic_infra_pkg::axi_ht_w_t     axi_ht_dma_transfer_w[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_w_valid[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_w_ready[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  aic_infra_pkg::axi_ht_m_b_t   axi_ht_dma_transfer_b[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_b_valid[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_b_ready[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  aic_infra_pkg::axi_ht_m_ar_t  axi_ht_dma_transfer_ar[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_ar_valid[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_ar_ready[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  aic_infra_pkg::axi_ht_m_r_t   axi_ht_dma_transfer_r[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_r_valid[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                         axi_ht_dma_transfer_r_ready[NumHtDmaTransferBusses * aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];


  aic_common_pkg::aic_ht_axi_m_id_t axi_ht_dma_transfer_aw_id_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  aic_common_pkg::aic_ht_axi_addr_t axi_ht_dma_transfer_aw_addr_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_len_t                axi_ht_dma_transfer_aw_len_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_size_e               axi_ht_dma_transfer_aw_size_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_burst_e              axi_ht_dma_transfer_aw_burst_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_aw_lock_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_cache_e              axi_ht_dma_transfer_aw_cache_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_prot_t               axi_ht_dma_transfer_aw_prot_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];

  logic                             axi_ht_dma_transfer_aw_valid_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_aw_ready_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];

  aic_common_pkg::aic_ht_axi_data_t axi_ht_dma_transfer_w_data_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  aic_common_pkg::aic_ht_axi_strb_t axi_ht_dma_transfer_w_strb_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_w_last_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];

  logic                             axi_ht_dma_transfer_w_valid_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_w_ready_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];

  aic_common_pkg::aic_ht_axi_m_id_t axi_ht_dma_transfer_b_id_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_resp_e               axi_ht_dma_transfer_b_resp_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_b_valid_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_b_ready_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];

  aic_common_pkg::aic_ht_axi_m_id_t axi_ht_dma_transfer_ar_id_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  aic_common_pkg::aic_ht_axi_addr_t axi_ht_dma_transfer_ar_addr_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_len_t                axi_ht_dma_transfer_ar_len_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_size_e               axi_ht_dma_transfer_ar_size_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_burst_e              axi_ht_dma_transfer_ar_burst_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_ar_lock_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_cache_e              axi_ht_dma_transfer_ar_cache_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_prot_t               axi_ht_dma_transfer_ar_prot_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];

  logic                             axi_ht_dma_transfer_ar_valid_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_ar_ready_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];

  aic_common_pkg::aic_ht_axi_m_id_t axi_ht_dma_transfer_r_id_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  aic_common_pkg::aic_ht_axi_data_t axi_ht_dma_transfer_r_data_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  axi_pkg::axi_resp_e               axi_ht_dma_transfer_r_resp_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_r_last_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];

  logic                             axi_ht_dma_transfer_r_valid_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];
  logic                             axi_ht_dma_transfer_r_ready_conn[aic_infra_pkg::AIC_HT_DMA_NUM_PORTS];

  for (genvar idx = 0; idx < aic_infra_pkg::AIC_HT_DMA_NUM_PORTS; idx++) begin: gen_type_cast
    always_comb begin
      axi_ht_dma_transfer_aw[AxiHtDmaPortIdxMan+idx].id = axi_ht_dma_transfer_aw_id_conn[idx];
      axi_ht_dma_transfer_aw[AxiHtDmaPortIdxMan+idx].addr = axi_ht_dma_transfer_aw_addr_conn[idx];
      axi_ht_dma_transfer_aw[AxiHtDmaPortIdxMan+idx].len = axi_ht_dma_transfer_aw_len_conn[idx];
      axi_ht_dma_transfer_aw[AxiHtDmaPortIdxMan+idx].size = axi_pkg::axi_size_t'(axi_ht_dma_transfer_aw_size_conn[idx]);
      axi_ht_dma_transfer_aw[AxiHtDmaPortIdxMan+idx].burst = axi_pkg::axi_burst_t'(axi_ht_dma_transfer_aw_burst_conn[idx]);
      axi_ht_dma_transfer_aw[AxiHtDmaPortIdxMan+idx].lock = axi_ht_dma_transfer_aw_lock_conn[idx];
      axi_ht_dma_transfer_aw[AxiHtDmaPortIdxMan+idx].cache = axi_pkg::axi_cache_t'(axi_ht_dma_transfer_aw_cache_conn[idx]);
      axi_ht_dma_transfer_aw[AxiHtDmaPortIdxMan+idx].prot = axi_ht_dma_transfer_aw_prot_conn[idx];
      axi_ht_dma_transfer_aw_valid[AxiHtDmaPortIdxMan+idx] = axi_ht_dma_transfer_aw_valid_conn[idx];
      axi_ht_dma_transfer_aw_ready_conn[idx] = axi_ht_dma_transfer_aw_ready[AxiHtDmaPortIdxMan+idx];

      axi_ht_dma_transfer_w[AxiHtDmaPortIdxMan+idx].data = axi_ht_dma_transfer_w_data_conn[idx];
      axi_ht_dma_transfer_w[AxiHtDmaPortIdxMan+idx].strb = axi_ht_dma_transfer_w_strb_conn[idx];
      axi_ht_dma_transfer_w[AxiHtDmaPortIdxMan+idx].last = axi_ht_dma_transfer_w_last_conn[idx];
      axi_ht_dma_transfer_w_valid[AxiHtDmaPortIdxMan+idx] = axi_ht_dma_transfer_w_valid_conn[idx];
      axi_ht_dma_transfer_w_ready_conn[idx] = axi_ht_dma_transfer_w_ready[AxiHtDmaPortIdxMan+idx];

      axi_ht_dma_transfer_b_id_conn[idx] = axi_ht_dma_transfer_b[AxiHtDmaPortIdxMan+idx].id;
      axi_ht_dma_transfer_b_resp_conn[idx] = axi_pkg::axi_resp_e'(axi_ht_dma_transfer_b[AxiHtDmaPortIdxMan+idx].resp);
      axi_ht_dma_transfer_b_valid_conn[idx] = axi_ht_dma_transfer_b_valid[AxiHtDmaPortIdxMan+idx];
      axi_ht_dma_transfer_b_ready[AxiHtDmaPortIdxMan+idx] = axi_ht_dma_transfer_b_ready_conn[idx];

      axi_ht_dma_transfer_ar[AxiHtDmaPortIdxMan+idx].id = axi_ht_dma_transfer_ar_id_conn[idx];
      axi_ht_dma_transfer_ar[AxiHtDmaPortIdxMan+idx].addr = axi_ht_dma_transfer_ar_addr_conn[idx];
      axi_ht_dma_transfer_ar[AxiHtDmaPortIdxMan+idx].len = axi_ht_dma_transfer_ar_len_conn[idx];
      axi_ht_dma_transfer_ar[AxiHtDmaPortIdxMan+idx].size = axi_pkg::axi_size_t'(axi_ht_dma_transfer_ar_size_conn[idx]);
      axi_ht_dma_transfer_ar[AxiHtDmaPortIdxMan+idx].burst = axi_pkg::axi_burst_t'(axi_ht_dma_transfer_ar_burst_conn[idx]);
      axi_ht_dma_transfer_ar[AxiHtDmaPortIdxMan+idx].lock = axi_ht_dma_transfer_ar_lock_conn[idx];
      axi_ht_dma_transfer_ar[AxiHtDmaPortIdxMan+idx].cache = axi_pkg::axi_cache_t'(axi_ht_dma_transfer_ar_cache_conn[idx]);
      axi_ht_dma_transfer_ar[AxiHtDmaPortIdxMan+idx].prot = axi_ht_dma_transfer_ar_prot_conn[idx];
      axi_ht_dma_transfer_ar_valid[AxiHtDmaPortIdxMan+idx] = axi_ht_dma_transfer_ar_valid_conn[idx];
      axi_ht_dma_transfer_ar_ready_conn[idx] =  axi_ht_dma_transfer_ar_ready[AxiHtDmaPortIdxMan+idx];

      axi_ht_dma_transfer_r_id_conn[idx] = axi_ht_dma_transfer_r[AxiHtDmaPortIdxMan+idx].id;
      axi_ht_dma_transfer_r_data_conn[idx] = axi_ht_dma_transfer_r[AxiHtDmaPortIdxMan+idx].data;
      axi_ht_dma_transfer_r_resp_conn[idx] = axi_pkg::axi_resp_e'(axi_ht_dma_transfer_r[AxiHtDmaPortIdxMan+idx].resp);
      axi_ht_dma_transfer_r_last_conn[idx] = axi_ht_dma_transfer_r[AxiHtDmaPortIdxMan+idx].last;
      axi_ht_dma_transfer_r_valid_conn[idx] = axi_ht_dma_transfer_r_valid[AxiHtDmaPortIdxMan+idx];
      axi_ht_dma_transfer_r_ready[AxiHtDmaPortIdxMan+idx] = axi_ht_dma_transfer_r_ready_conn[idx];
    end
  end

  dma #(
    .NUM_PORTS(aic_infra_pkg::AIC_HT_DMA_NUM_PORTS),
    .NUM_CHNLS(aic_infra_pkg::AIC_HT_DMA_NUM_CHNLS),
    .DMA_N_BUF_IDXS(256),
    .DMA_N_IMPL_BUF_IDXS(256),
    .NR_TOK_PROD(HT_DMA_MAX_NR_TOK_PROD),
    .NR_TOK_CONS(HT_DMA_MAX_NR_TOK_CONS),
    .NR_TOP_TOK_PROD(DMA_NR_TOP_TOK_PROD),
    .NR_TOP_TOK_CONS(DMA_NR_TOP_TOK_CONS),
    .dma_axi_s_data_t( aic_common_pkg::aic_lt_axi_data_t ),
    .dma_axi_s_addr_t( aic_common_pkg::aic_lt_axi_loc_addr_t ),
    .dma_axi_s_id_t( logic [aic_infra_pkg::AIC_INFRA_CONTROL_AXI_S_IDW-1:0] ),
    .dma_axi_m_data_t( aic_common_pkg::aic_ht_axi_data_t ),
    .dma_axi_m_addr_t( aic_common_pkg::aic_ht_axi_addr_t ),
    .dma_axi_m_id_t( aic_common_pkg::aic_ht_axi_m_id_t ),
    .dma_token_prod_t( logic [HT_DMA_MAX_NR_TOK_PROD+DMA_NR_TOP_TOK_PROD-1:0] ),
    .dma_token_cons_t( logic [HT_DMA_MAX_NR_TOK_CONS+DMA_NR_TOP_TOK_CONS-1:0] ),
    .RegionStAddr(aic_infra_pkg::AIC_LOC_HP_DMA_REGION_ST_ADDR),
    .RegionEndAddr(aic_infra_pkg::AIC_LOC_HP_DMA_REGION_END_ADDR)
  ) u_ht_aic_dma (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_impl   (sram_impl_inp[aic_infra_pkg::SRAM_IMPL_IDX_HT_AIC_DMA]),
    .o_impl   (sram_impl_oup[aic_infra_pkg::SRAM_IMPL_IDX_HT_AIC_DMA]),
    .o_int    ({
        irq_sources[aic_infra_pkg::IRQ_IDX_DMA_HT_CHANNEL_1],
        irq_sources[aic_infra_pkg::IRQ_IDX_DMA_HT_CHANNEL_0] }),

    .o_tok_prod_vld   (ht_dma_all_prod_vld),
    .i_tok_prod_rdy   (ht_dma_all_prod_rdy),
    .i_tok_cons_vld   (ht_dma_all_cons_vld),
    .o_tok_cons_rdy   (ht_dma_all_cons_rdy),

    .o_ts_start       (ht_dma_ts_start),
    .o_ts_end         (ht_dma_ts_end),
    .o_acd_sync       (ht_dma_acd_sync),
    .o_obs            (ht_dma_obs),

    .i_axi_s_awid     (axi_ht_dma_config_aw.id),
    .i_axi_s_awaddr   (aic_common_pkg::aic_lt_axi_loc_addr_t'(axi_ht_dma_config_aw.addr)), // local address as CID needs to be capped off
    .i_axi_s_awlen    (axi_ht_dma_config_aw.len),
    .i_axi_s_awsize   (axi_pkg::axi_size_e'(axi_ht_dma_config_aw.size)),
    .i_axi_s_awburst  (axi_pkg::axi_burst_e'(axi_ht_dma_config_aw.burst)),
    .i_axi_s_awvalid  (axi_ht_dma_config_aw_valid),
    .o_axi_s_awready  (axi_ht_dma_config_aw_ready),

    .i_axi_s_awlock   (axi_ht_dma_config_aw.lock),
    .i_axi_s_awcache  (axi_pkg::axi_cache_e'(axi_ht_dma_config_aw.cache)),
    .i_axi_s_awprot   (axi_ht_dma_config_aw.prot),

    .i_axi_s_wdata    (axi_ht_dma_config_w.data),
    .i_axi_s_wstrb    (axi_ht_dma_config_w.strb),
    .i_axi_s_wlast    (axi_ht_dma_config_w.last),
    .i_axi_s_wvalid   (axi_ht_dma_config_w_valid),
    .o_axi_s_wready   (axi_ht_dma_config_w_ready),

    .o_axi_s_bid      (axi_ht_dma_config_b.id),
    .o_axi_s_bresp    (axi_ht_dma_config_b.resp),
    .o_axi_s_bvalid   (axi_ht_dma_config_b_valid),
    .i_axi_s_bready   (axi_ht_dma_config_b_ready),

    .i_axi_s_arid     (axi_ht_dma_config_ar.id),
    .i_axi_s_araddr   (aic_common_pkg::aic_lt_axi_loc_addr_t'(axi_ht_dma_config_ar.addr)), // local address as CID needs to be capped off
    .i_axi_s_arlen    (axi_ht_dma_config_ar.len),
    .i_axi_s_arsize   (axi_pkg::axi_size_e'(axi_ht_dma_config_ar.size)),
    .i_axi_s_arburst  (axi_pkg::axi_burst_e'(axi_ht_dma_config_ar.burst)),
    .i_axi_s_arvalid  (axi_ht_dma_config_ar_valid),
    .o_axi_s_arready  (axi_ht_dma_config_ar_ready),

    .i_axi_s_arlock   (axi_ht_dma_config_ar.lock),
    .i_axi_s_arcache  (axi_pkg::axi_cache_e'(axi_ht_dma_config_ar.cache)),
    .i_axi_s_arprot   (axi_ht_dma_config_ar.prot),

    .o_axi_s_rid      (axi_ht_dma_config_r.id),
    .o_axi_s_rdata    (axi_ht_dma_config_r.data),
    .o_axi_s_rresp    (axi_ht_dma_config_r.resp),
    .o_axi_s_rlast    (axi_ht_dma_config_r.last),
    .o_axi_s_rvalid   (axi_ht_dma_config_r_valid),
    .i_axi_s_rready   (axi_ht_dma_config_r_ready),

    .o_axi_m_awid    (axi_ht_dma_transfer_aw_id_conn),
    .o_axi_m_awaddr  (axi_ht_dma_transfer_aw_addr_conn),
    .o_axi_m_awlen   (axi_ht_dma_transfer_aw_len_conn),
    .o_axi_m_awsize  (axi_ht_dma_transfer_aw_size_conn),
    .o_axi_m_awburst (axi_ht_dma_transfer_aw_burst_conn),
    .o_axi_m_awlock  (axi_ht_dma_transfer_aw_lock_conn),
    .o_axi_m_awcache (axi_ht_dma_transfer_aw_cache_conn),
    .o_axi_m_awprot  (axi_ht_dma_transfer_aw_prot_conn),
    .o_axi_m_awvalid (axi_ht_dma_transfer_aw_valid_conn),
    .i_axi_m_awready (axi_ht_dma_transfer_aw_ready_conn),

    .o_axi_m_wdata   (axi_ht_dma_transfer_w_data_conn),
    .o_axi_m_wstrb   (axi_ht_dma_transfer_w_strb_conn),
    .o_axi_m_wlast   (axi_ht_dma_transfer_w_last_conn),
    .o_axi_m_wvalid  (axi_ht_dma_transfer_w_valid_conn),
    .i_axi_m_wready  (axi_ht_dma_transfer_w_ready_conn),

    .i_axi_m_bid     (axi_ht_dma_transfer_b_id_conn),
    .i_axi_m_bresp   (axi_ht_dma_transfer_b_resp_conn),
    .i_axi_m_bvalid  (axi_ht_dma_transfer_b_valid_conn),
    .o_axi_m_bready  (axi_ht_dma_transfer_b_ready_conn),

    .o_axi_m_arid    (axi_ht_dma_transfer_ar_id_conn),
    .o_axi_m_araddr  (axi_ht_dma_transfer_ar_addr_conn),
    .o_axi_m_arlen   (axi_ht_dma_transfer_ar_len_conn),
    .o_axi_m_arsize  (axi_ht_dma_transfer_ar_size_conn),
    .o_axi_m_arburst (axi_ht_dma_transfer_ar_burst_conn),
    .o_axi_m_arlock  (axi_ht_dma_transfer_ar_lock_conn),
    .o_axi_m_arcache (axi_ht_dma_transfer_ar_cache_conn),
    .o_axi_m_arprot  (axi_ht_dma_transfer_ar_prot_conn),
    .o_axi_m_arvalid (axi_ht_dma_transfer_ar_valid_conn),
    .i_axi_m_arready (axi_ht_dma_transfer_ar_ready_conn),

    .i_axi_m_rid     (axi_ht_dma_transfer_r_id_conn),
    .i_axi_m_rdata   (axi_ht_dma_transfer_r_data_conn),
    .i_axi_m_rresp   (axi_ht_dma_transfer_r_resp_conn),
    .i_axi_m_rlast   (axi_ht_dma_transfer_r_last_conn),
    .i_axi_m_rvalid  (axi_ht_dma_transfer_r_valid_conn),
    .o_axi_m_rready  (axi_ht_dma_transfer_r_ready_conn)
  );

  // Note: Setting atop field to default, it is not used, but required because of language limitation.
  always_comb axi_ht_dma_config_aw.atop = axi_pkg::axi_atop_t'(0);

  ////////////////
  // HT DMA Cut //
  ////////////////

  for (
      genvar ht_dma_port_idx = 0;
      ht_dma_port_idx < aic_infra_pkg::AIC_HT_DMA_NUM_PORTS;
      ht_dma_port_idx++
  ) begin : gen_ht_dma_atu
    // Silence unuced struct field
    always_comb axi_ht_dma_transfer_aw[ht_dma_port_idx].atop = axi_pkg::axi_atop_t'(0);

    axe_axi_cut #(
      .CutAw   (1'b1), // Breaks long path
      .CutW    (1'b1), // Breaks long path
      .CutB    (1'b0),
      .CutAr   (1'b1), // Breaks long path
      .CutR    (1'b0),
      .axi_aw_t(aic_infra_pkg::axi_ht_m_aw_t),
      .axi_w_t (aic_infra_pkg::axi_ht_w_t),
      .axi_b_t (aic_infra_pkg::axi_ht_m_b_t),
      .axi_ar_t(aic_infra_pkg::axi_ht_m_ar_t),
      .axi_r_t (aic_infra_pkg::axi_ht_m_r_t)
    ) u_ht_aic_dma_axe_axi_cut (
      .i_clk,
      .i_rst_n,
      .i_axi_s_aw      (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .i_axi_s_aw_valid(axi_ht_dma_transfer_aw_valid[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .o_axi_s_aw_ready(axi_ht_dma_transfer_aw_ready[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .i_axi_s_w       (axi_ht_dma_transfer_w[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .i_axi_s_w_valid (axi_ht_dma_transfer_w_valid[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .o_axi_s_w_ready (axi_ht_dma_transfer_w_ready[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .o_axi_s_b       (axi_ht_dma_transfer_b[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .o_axi_s_b_valid (axi_ht_dma_transfer_b_valid[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .i_axi_s_b_ready (axi_ht_dma_transfer_b_ready[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .i_axi_s_ar      (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .i_axi_s_ar_valid(axi_ht_dma_transfer_ar_valid[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .o_axi_s_ar_ready(axi_ht_dma_transfer_ar_ready[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .o_axi_s_r       (axi_ht_dma_transfer_r[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .o_axi_s_r_valid (axi_ht_dma_transfer_r_valid[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .i_axi_s_r_ready (axi_ht_dma_transfer_r_ready[AxiHtDmaPortIdxMan + ht_dma_port_idx]),
      .o_axi_m_aw      (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .o_axi_m_aw_valid(axi_ht_dma_transfer_aw_valid[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .i_axi_m_aw_ready(axi_ht_dma_transfer_aw_ready[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .o_axi_m_w       (axi_ht_dma_transfer_w[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .o_axi_m_w_valid (axi_ht_dma_transfer_w_valid[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .i_axi_m_w_ready (axi_ht_dma_transfer_w_ready[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .i_axi_m_b       (axi_ht_dma_transfer_b[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .i_axi_m_b_valid (axi_ht_dma_transfer_b_valid[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .o_axi_m_b_ready (axi_ht_dma_transfer_b_ready[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .o_axi_m_ar      (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .o_axi_m_ar_valid(axi_ht_dma_transfer_ar_valid[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .i_axi_m_ar_ready(axi_ht_dma_transfer_ar_ready[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .i_axi_m_r       (axi_ht_dma_transfer_r[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .i_axi_m_r_valid (axi_ht_dma_transfer_r_valid[AxiHtDmaPortIdxFabric + ht_dma_port_idx]),
      .o_axi_m_r_ready (axi_ht_dma_transfer_r_ready[AxiHtDmaPortIdxFabric + ht_dma_port_idx])
    );
  end

  ////////////////////////////////
  // AI-Core Control Dispatcher //
  ////////////////////////////////

  aic_infra_pkg::axi_lt_config_s_aw_t axi_aic_cd_s_aw;
  logic                               axi_aic_cd_s_aw_valid;
  logic                               axi_aic_cd_s_aw_ready;
  aic_infra_pkg::axi_lt_w_t           axi_aic_cd_s_w;
  logic                               axi_aic_cd_s_w_valid;
  logic                               axi_aic_cd_s_w_ready;
  aic_infra_pkg::axi_lt_config_s_b_t  axi_aic_cd_s_b;
  logic                               axi_aic_cd_s_b_valid;
  logic                               axi_aic_cd_s_b_ready;
  aic_infra_pkg::axi_lt_config_s_ar_t axi_aic_cd_s_ar;
  logic                               axi_aic_cd_s_ar_valid;
  logic                               axi_aic_cd_s_ar_ready;
  aic_infra_pkg::axi_lt_config_s_r_t  axi_aic_cd_s_r;
  logic                               axi_aic_cd_s_r_valid;
  logic                               axi_aic_cd_s_r_ready;

  aic_infra_pkg::axi_lt_config_m_aw_t axi_aic_cd_m_aw;
  logic                               axi_aic_cd_m_aw_valid;
  logic                               axi_aic_cd_m_aw_ready;
  aic_infra_pkg::axi_lt_w_t           axi_aic_cd_m_w;
  logic                               axi_aic_cd_m_w_valid;
  logic                               axi_aic_cd_m_w_ready;
  aic_infra_pkg::axi_lt_config_m_b_t  axi_aic_cd_m_b;
  logic                               axi_aic_cd_m_b_valid;
  logic                               axi_aic_cd_m_b_ready;
  aic_infra_pkg::axi_lt_config_m_ar_t axi_aic_cd_m_ar;
  logic                               axi_aic_cd_m_ar_valid;
  logic                               axi_aic_cd_m_ar_ready;
  aic_infra_pkg::axi_lt_config_m_r_t  axi_aic_cd_m_r;
  logic                               axi_aic_cd_m_r_valid;
  logic                               axi_aic_cd_m_r_ready;

  if ( token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_PROD
    != token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_CONS
  ) $fatal(1, "AIC_CD: Global token number prod and cons must be equal;");

  // Address map for AIC_CD
  localparam aic_addr_map_pkg::loc_addr_t AicCdAddrStart[aic_cd_pkg::NUM_AXI_ENDPOINTS] = '{
    aic_addr_map_pkg::AIC_LOC_CFG_ACD_CSR_ST_ADDR,
    aic_addr_map_pkg::AIC_LOC_CFG_ACD_CMD_ST_ADDR
  };
  // Note: The aic_cd subordinate decoder is non-inclusive for the end address
  localparam aic_addr_map_pkg::loc_addr_t AicCdAddrEnd[aic_cd_pkg::NUM_AXI_ENDPOINTS] = '{
    aic_addr_map_pkg::AIC_LOC_CFG_ACD_CSR_END_ADDR + aic_addr_map_pkg::loc_addr_t'(1),
    aic_addr_map_pkg::AIC_LOC_CFG_ACD_CMD_END_ADDR + aic_addr_map_pkg::loc_addr_t'(1)
  };

  logic [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] aic_base_addr;
  always_comb begin
    aic_base_addr = '0;
    aic_base_addr[aic_common_pkg::AIC_CID_LSB+:aic_common_pkg::AIC_CID_SUB_W] = i_cid;
  end

  logic [aic_cd_csr_reg_pkg::NUM_DESTINATIONS-1:0] aic_cd_destination_cmd_done;

  always_comb begin
    aic_cd_destination_cmd_done = '0;
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_M_IDF_0]   = i_dmc_ts_end[dmc_pkg::m_ifd0_idx];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_M_IDF_1]   = i_dmc_ts_end[dmc_pkg::m_ifd1_idx];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_M_IDF_2]   = i_dmc_ts_end[dmc_pkg::m_ifd2_idx];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_M_IDF_W]   = i_dmc_ts_end[dmc_pkg::m_ifdw_idx];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_M_ODR]     = i_dmc_ts_end[dmc_pkg::m_odr_idx];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_D_IDF_0]   = i_dmc_ts_end[dmc_pkg::d_ifd0_idx];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_D_IDF_1]   = i_dmc_ts_end[dmc_pkg::d_ifd1_idx];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_D_ODR]     = i_dmc_ts_end[dmc_pkg::d_odr_idx];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_M_MVM_EXE] = i_mid_acd_sync[aic_mid_pkg::EndPointTSMvmExe];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_M_MVM_PRG] = i_mid_acd_sync[aic_mid_pkg::EndPointTSMvmPrg];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_M_IAU]     = i_mid_acd_sync[aic_mid_pkg::EndPointTSIau];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_M_DPU]     = i_mid_acd_sync[aic_mid_pkg::EndPointTSDpu];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_D_DWPU]    = i_did_acd_sync[aic_did_pkg::EndPointDwpu];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_D_IAU]     = i_did_acd_sync[aic_did_pkg::EndPointIau];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_D_DPU]     = i_did_acd_sync[aic_did_pkg::EndPointDpu];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_DMA_0]     = ht_dma_acd_sync[0];
    aic_cd_destination_cmd_done[aic_infra_pkg::AIC_CD_IDX_DMA_1]     = ht_dma_acd_sync[1];
  end

  localparam int unsigned ACDTokenDevs = token_mgr_mapping_aic_pkg::TOK_MGR_CFG.nr_loc_devs;
  aic_cd #(
    .NumDestinations       (aic_cd_csr_reg_pkg::NUM_DESTINATIONS),
    .NumPatchModeEntries   (8),
    .NumPatchTableEntries  (16),
    .NumLocalTokens        (ACDTokenDevs),
    .NumGlobalTokens       (token_mgr_mapping_aic_pkg::TOK_MGR_TOP_AIC0_CD_NR_TOK_PROD),
    .CommandFifoDepth      (16),
    .InstructionBufferDepth(16),
    .CopyBufferDepth       (32),
    .FillCounterDepth      (16),
    .InstrBufferUsesMacro  (1'b1),
    .InstrMemImplKey       ("default"),
    .instr_ram_impl_inp_t  (axe_tcl_sram_pkg::impl_inp_t),
    .instr_ram_impl_oup_t  (axe_tcl_sram_pkg::impl_oup_t),
    .CopyBufferUsesMacro   (1'b1),
    .CopyMemImplKey        ("default"),
    .copy_ram_impl_inp_t   (axe_tcl_sram_pkg::impl_inp_t),
    .copy_ram_impl_oup_t   (axe_tcl_sram_pkg::impl_oup_t),
    .AxiSubIdWidth         (aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW),
    .AxiSubAddrWidth       (aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiSubDataWidth       (aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
    .axi_decode_addr_t     (aic_addr_map_pkg::loc_addr_t),
    .AxiEndpointAddrStart  (AicCdAddrStart),
    .AxiEndpointAddrEnd    (AicCdAddrEnd),
    .axi_s_aw_t            (aic_infra_pkg::axi_lt_config_s_aw_t),
    .axi_s_w_t             (aic_infra_pkg::axi_lt_w_t),
    .axi_s_b_t             (aic_infra_pkg::axi_lt_config_s_b_t),
    .axi_s_ar_t            (aic_infra_pkg::axi_lt_config_s_ar_t),
    .axi_s_r_t             (aic_infra_pkg::axi_lt_config_s_r_t),
    .AxiManIdWidth         (aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH),
    .AxiIdForFetch         (aic_common_pkg::aic_lt_axi_m_id_t'(0)),
    .AxiIdForCopy          (aic_common_pkg::aic_lt_axi_m_id_t'(1)),
    .AxiManAddrWidth       (aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiManDataWidth       (aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
    .CutAxiManAw           (1'b0),
    .CutAxiManW            (1'b0),
    .CutAxiManB            (1'b0),
    .CutAxiManAr           (1'b0),
    .CutAxiManR            (1'b0),
    .axi_m_aw_t            (aic_infra_pkg::axi_lt_config_m_aw_t),
    .axi_m_w_t             (aic_infra_pkg::axi_lt_w_t),
    .axi_m_b_t             (aic_infra_pkg::axi_lt_config_m_b_t),
    .axi_m_ar_t            (aic_infra_pkg::axi_lt_config_m_ar_t),
    .axi_m_r_t             (aic_infra_pkg::axi_lt_config_m_r_t)
  ) u_aic_cd (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw               (axi_aic_cd_s_aw),
    .i_axi_s_aw_valid         (axi_aic_cd_s_aw_valid),
    .o_axi_s_aw_ready         (axi_aic_cd_s_aw_ready),
    .i_axi_s_w                (axi_aic_cd_s_w),
    .i_axi_s_w_valid          (axi_aic_cd_s_w_valid),
    .o_axi_s_w_ready          (axi_aic_cd_s_w_ready),
    .o_axi_s_b                (axi_aic_cd_s_b),
    .o_axi_s_b_valid          (axi_aic_cd_s_b_valid),
    .i_axi_s_b_ready          (axi_aic_cd_s_b_ready),
    .i_axi_s_ar               (axi_aic_cd_s_ar),
    .i_axi_s_ar_valid         (axi_aic_cd_s_ar_valid),
    .o_axi_s_ar_ready         (axi_aic_cd_s_ar_ready),
    .o_axi_s_r                (axi_aic_cd_s_r),
    .o_axi_s_r_valid          (axi_aic_cd_s_r_valid),
    .i_axi_s_r_ready          (axi_aic_cd_s_r_ready),
    .o_axi_m_aw               (axi_aic_cd_m_aw),
    .o_axi_m_aw_valid         (axi_aic_cd_m_aw_valid),
    .i_axi_m_aw_ready         (axi_aic_cd_m_aw_ready),
    .o_axi_m_w                (axi_aic_cd_m_w),
    .o_axi_m_w_valid          (axi_aic_cd_m_w_valid),
    .i_axi_m_w_ready          (axi_aic_cd_m_w_ready),
    .i_axi_m_b                (axi_aic_cd_m_b),
    .i_axi_m_b_valid          (axi_aic_cd_m_b_valid),
    .o_axi_m_b_ready          (axi_aic_cd_m_b_ready),
    .o_axi_m_ar               (axi_aic_cd_m_ar),
    .o_axi_m_ar_valid         (axi_aic_cd_m_ar_valid),
    .i_axi_m_ar_ready         (axi_aic_cd_m_ar_ready),
    .i_axi_m_r                (axi_aic_cd_m_r),
    .i_axi_m_r_valid          (axi_aic_cd_m_r_valid),
    .o_axi_m_r_ready          (axi_aic_cd_m_r_ready),
    .o_token_local_prod_valid (acd_tok_prod_vld),
    .i_token_local_prod_ready (acd_tok_prod_rdy),
    .i_token_local_cons_valid (acd_tok_cons_vld),
    .o_token_local_cons_ready (acd_tok_cons_rdy),
    .o_token_global_prod_valid(acd_top_tok_prod_vld),
    .i_token_global_prod_ready(acd_top_tok_prod_rdy),
    .i_token_global_cons_valid(acd_top_tok_cons_vld),
    .o_token_global_cons_ready(acd_top_tok_cons_rdy),
    .o_timestamp_id           (aic_cd_timestamp_id),
    .o_timestamp_active_pulse (aic_cd_timestamp_active_pulse),
    .i_destination_cmd_done   (aic_cd_destination_cmd_done),
    .i_aic_base_addr          (aic_base_addr),
    .o_irq                    (irq_sources[aic_infra_pkg::IRQ_IDX_AIC_CD]),
    .i_instr_ram_impl         (sram_impl_inp[aic_infra_pkg::SRAM_IMPL_IDX_AIC_CD_INSTR]),
    .o_instr_ram_impl         (sram_impl_oup[aic_infra_pkg::SRAM_IMPL_IDX_AIC_CD_INSTR]),
    .i_copy_ram_impl          (sram_impl_inp[aic_infra_pkg::SRAM_IMPL_IDX_AIC_CD_COPY]),
    .o_copy_ram_impl          (sram_impl_oup[aic_infra_pkg::SRAM_IMPL_IDX_AIC_CD_COPY])
  );



  //////////////////////////
  // SPM
  //////////////////////////
  aic_infra_pkg::axi_lt_s_aw_t axi_lt_spm_aw;
  logic                        axi_lt_spm_aw_valid;
  logic                        axi_lt_spm_aw_ready;
  aic_infra_pkg::axi_lt_w_t    axi_lt_spm_w;
  logic                        axi_lt_spm_w_valid;
  logic                        axi_lt_spm_w_ready;
  aic_infra_pkg::axi_lt_s_b_t  axi_lt_spm_b;
  logic                        axi_lt_spm_b_valid;
  logic                        axi_lt_spm_b_ready;
  aic_infra_pkg::axi_lt_s_ar_t axi_lt_spm_ar;
  logic                        axi_lt_spm_ar_valid;
  logic                        axi_lt_spm_ar_ready;
  aic_infra_pkg::axi_lt_s_r_t  axi_lt_spm_r;
  logic                        axi_lt_spm_r_valid;
  logic                        axi_lt_spm_r_ready;

  spm_pkg::spm_error_status_t spm_err_status;

  always_comb hw2reg.spm_err_status.ecc_err_present.d = spm_err_status.ecc_err;
  always_comb hw2reg.spm_err_status.ecc_err_type.d = spm_err_status.ecc_err_type;
  always_comb hw2reg.spm_err_status.ecc_err_syndrome.d = spm_err_status.ecc_err_syndrome;
  always_comb hw2reg.spm_err_status.ecc_err_index.d = spm_err_status.ecc_err_index;

  always_comb hw2reg.spm_err_status.ecc_err_present.de = spm_err_status.ecc_err;
  always_comb hw2reg.spm_err_status.ecc_err_type.de = spm_err_status.ecc_err;
  always_comb hw2reg.spm_err_status.ecc_err_syndrome.de = spm_err_status.ecc_err;
  always_comb hw2reg.spm_err_status.ecc_err_index.de = spm_err_status.ecc_err;

  spm #(
    .SPM_MEM_SIZE_KB      (512),
    .SPM_MEM_MACRO_DEPTH_K(8),

    //
    .SPM_NB_BANKS               (2),
    .SPM_NB_SUB_BANKS           (1),
    .SPM_NB_MINI_BANKS          (2),
    .SPM_NB_SRAMS_PER_MINI_BANK (2),
    .SPM_NB_REQ_PIPELINE(0),
    .SPM_NB_RSP_PIPELINE(0),

    .ECC_PROTECTION_EN     (1),
    .EN_ATOMIC_SUPPORT     (0), // AICORE SPM does not support atomics
    .spm_axi_data_t        (aic_common_pkg::aic_lt_axi_data_t),
    .spm_axi_addr_t        (logic [18:0]),
    .spm_axi_strb_t        (aic_common_pkg::aic_lt_axi_strb_t),
    .spm_axi_id_t          (aic_common_pkg::aic_lt_axi_s_id_t)
  ) u_aic_spm (
    .i_clk,
    .i_rst_n,
    .i_axi_s_awid      (axi_lt_spm_aw.id),
    .i_axi_s_awaddr    (axi_lt_spm_aw.addr[18:0]),
    .i_axi_s_awlen     (axi_lt_spm_aw.len),
    .i_axi_s_awsize    (axi_lt_spm_aw.size),
    .i_axi_s_awburst   (axi_lt_spm_aw.burst),
    .i_axi_s_awlock    (axi_lt_spm_aw.lock),
    .i_axi_s_awcache   (axi_lt_spm_aw.cache),
    .i_axi_s_awprot    (axi_lt_spm_aw.prot),
    .i_axi_s_awatop    ('{default:0}), // No support, tie to not have undriven input
    .i_axi_s_awvalid   (axi_lt_spm_aw_valid),
    .o_axi_s_awready   (axi_lt_spm_aw_ready),
    .i_axi_s_wdata     (axi_lt_spm_w.data),
    .i_axi_s_wstrb     (axi_lt_spm_w.strb),
    .i_axi_s_wlast     (axi_lt_spm_w.last),
    .o_axi_s_wready    (axi_lt_spm_w_ready),
    .i_axi_s_wvalid    (axi_lt_spm_w_valid),
    .o_axi_s_bid       (axi_lt_spm_b.id),
    .o_axi_s_bresp     (axi_lt_spm_b.resp),
    .o_axi_s_bvalid    (axi_lt_spm_b_valid),
    .i_axi_s_bready    (axi_lt_spm_b_ready),
    .i_axi_s_arid      (axi_lt_spm_ar.id),
    .i_axi_s_araddr    (axi_lt_spm_ar.addr[18:0]),
    .i_axi_s_arlen     (axi_lt_spm_ar.len),
    .i_axi_s_arsize    (axi_lt_spm_ar.size),
    .i_axi_s_arburst   (axi_lt_spm_ar.burst),
    .i_axi_s_arlock    (axi_lt_spm_ar.lock),
    .i_axi_s_arcache   (axi_lt_spm_ar.cache),
    .i_axi_s_arprot    (axi_lt_spm_ar.prot),
    .i_axi_s_arvalid   (axi_lt_spm_ar_valid),
    .o_axi_s_arready   (axi_lt_spm_ar_ready),
    .o_axi_s_rid       (axi_lt_spm_r.id),
    .o_axi_s_rdata     (axi_lt_spm_r.data),
    .o_axi_s_rresp     (axi_lt_spm_r.resp),
    .o_axi_s_rlast     (axi_lt_spm_r.last),
    .o_axi_s_rvalid    (axi_lt_spm_r_valid),
    .i_axi_s_rready    (axi_lt_spm_r_ready),
    .i_scp_ecc_disable (1'b0),
    .o_scp_error_status(spm_err_status),
    .o_irq             (irq_sources[aic_infra_pkg::IRQ_IDX_SPM]),
    .i_impl            (sram_impl_inp[aic_infra_pkg::SRAM_IMPL_IDX_SPM]),
    .o_impl            (sram_impl_oup[aic_infra_pkg::SRAM_IMPL_IDX_SPM])
  );

  ///////////////
  // Firewalls //
  ///////////////
  aic_infra_pkg::axi_lt_config_s_aw_t axi_config_to_firewall_aw;
  logic                               axi_config_to_firewall_aw_valid;
  logic                               axi_config_to_firewall_aw_ready;
  aic_infra_pkg::axi_lt_w_t           axi_config_to_firewall_w;
  logic                               axi_config_to_firewall_w_valid;
  logic                               axi_config_to_firewall_w_ready;
  aic_infra_pkg::axi_lt_config_s_b_t  axi_config_to_firewall_b;
  logic                               axi_config_to_firewall_b_valid;
  logic                               axi_config_to_firewall_b_ready;
  aic_infra_pkg::axi_lt_config_s_ar_t axi_config_to_firewall_ar;
  logic                               axi_config_to_firewall_ar_valid;
  logic                               axi_config_to_firewall_ar_ready;
  aic_infra_pkg::axi_lt_config_s_r_t  axi_config_to_firewall_r;
  logic                               axi_config_to_firewall_r_valid;
  logic                               axi_config_to_firewall_r_ready;

  aic_infra_pkg::axi_lt_acd_s_aw_t    axi_acd_to_firewall_aw;
  logic                               axi_acd_to_firewall_aw_valid;
  logic                               axi_acd_to_firewall_aw_ready;
  aic_infra_pkg::axi_lt_w_t           axi_acd_to_firewall_w;
  logic                               axi_acd_to_firewall_w_valid;
  logic                               axi_acd_to_firewall_w_ready;
  aic_infra_pkg::axi_lt_acd_s_b_t     axi_acd_to_firewall_b;
  logic                               axi_acd_to_firewall_b_valid;
  logic                               axi_acd_to_firewall_b_ready;
  aic_infra_pkg::axi_lt_acd_s_ar_t    axi_acd_to_firewall_ar;
  logic                               axi_acd_to_firewall_ar_valid;
  logic                               axi_acd_to_firewall_ar_ready;
  aic_infra_pkg::axi_lt_acd_s_r_t     axi_acd_to_firewall_r;
  logic                               axi_acd_to_firewall_r_valid;
  logic                               axi_acd_to_firewall_r_ready;

  logic axi_acd_to_firewall_rid_dummy;
  logic axi_acd_to_firewall_bid_dummy;

  /////////////////////////
  // aic_fabric instance //
  /////////////////////////

  // datapath firewall switch

  logic datapath_firewall_sel;
  always_comb datapath_firewall_sel = reg2hw.datapath_firewall;

  // Extend the ID with properly for the Datapath
  // This only works because the port we have is a manager port and the ID's
  // are wider. So we can just extend/cut theupper part of ID
  localparam int unsigned CONTROL_AXI_S_DATAPATH_ID_WIDTH = 8;

  logic [CONTROL_AXI_S_DATAPATH_ID_WIDTH-1:0] dmc_l1_lt_axi_m_awid;
  logic [CONTROL_AXI_S_DATAPATH_ID_WIDTH-1:0] dmc_l1_lt_axi_m_bid;
  logic [CONTROL_AXI_S_DATAPATH_ID_WIDTH-1:0] dmc_l1_lt_axi_m_arid;
  logic [CONTROL_AXI_S_DATAPATH_ID_WIDTH-1:0] dmc_l1_lt_axi_m_rid;

  always_comb o_dmc_l1_lt_axi_m_awid = aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH'(dmc_l1_lt_axi_m_awid);
  always_comb   dmc_l1_lt_axi_m_bid  = CONTROL_AXI_S_DATAPATH_ID_WIDTH'(i_dmc_l1_lt_axi_m_bid);
  always_comb o_dmc_l1_lt_axi_m_arid = aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH'(dmc_l1_lt_axi_m_arid);
  always_comb   dmc_l1_lt_axi_m_rid  = CONTROL_AXI_S_DATAPATH_ID_WIDTH'(i_dmc_l1_lt_axi_m_rid);

  aic_fabric #(
    .IdleDelayW($bits(aic_csr_reg_pkg::aic_csr_reg2hw_low_power_control_reg_t) - 1)
  ) u_aic_fabric (
    .i_rst_n        (i_rst_n),
    .i_aclk         (i_clk),
    .i_scan_en,
    .i_core_id      (i_cid),
    .i_datapath_firewall_sel (datapath_firewall_sel),
    /////////////////////////////////
    // Config Connection to AIC_CD //
    /////////////////////////////////
    .i_acd_demux_axi_m_01_araddr (axi_aic_cd_m_ar.addr),
    .i_acd_demux_axi_m_01_arburst(axi_aic_cd_m_ar.burst),
    .i_acd_demux_axi_m_01_arcache(axi_aic_cd_m_ar.cache),
    .i_acd_demux_axi_m_01_arid   (axi_aic_cd_m_ar.id),
    .i_acd_demux_axi_m_01_arlen  (axi_aic_cd_m_ar.len),
    .i_acd_demux_axi_m_01_arlock (axi_aic_cd_m_ar.lock),
    .i_acd_demux_axi_m_01_arprot (axi_aic_cd_m_ar.prot),
    .i_acd_demux_axi_m_01_arsize (axi_aic_cd_m_ar.size),
    .i_acd_demux_axi_m_01_arvalid(axi_aic_cd_m_ar_valid),
    .i_acd_demux_axi_m_01_awaddr (axi_aic_cd_m_aw.addr),
    .i_acd_demux_axi_m_01_awburst(axi_aic_cd_m_aw.burst),
    .i_acd_demux_axi_m_01_awcache(axi_aic_cd_m_aw.cache),
    .i_acd_demux_axi_m_01_awid   (axi_aic_cd_m_aw.id),
    .i_acd_demux_axi_m_01_awlen  (axi_aic_cd_m_aw.len),
    .i_acd_demux_axi_m_01_awlock (axi_aic_cd_m_aw.lock),
    .i_acd_demux_axi_m_01_awprot (axi_aic_cd_m_aw.prot),
    .i_acd_demux_axi_m_01_awsize (axi_aic_cd_m_aw.size),
    .i_acd_demux_axi_m_01_awvalid(axi_aic_cd_m_aw_valid),
    .i_acd_demux_axi_m_01_bready (axi_aic_cd_m_b_ready),
    .i_acd_demux_axi_m_01_rready (axi_aic_cd_m_r_ready),
    .i_acd_demux_axi_m_01_wdata  (axi_aic_cd_m_w.data),
    .i_acd_demux_axi_m_01_wlast  (axi_aic_cd_m_w.last),
    .i_acd_demux_axi_m_01_wstrb  (axi_aic_cd_m_w.strb),
    .i_acd_demux_axi_m_01_wvalid (axi_aic_cd_m_w_valid),
    .o_acd_demux_axi_m_01_arready(axi_aic_cd_m_ar_ready),
    .o_acd_demux_axi_m_01_awready(axi_aic_cd_m_aw_ready),
    .o_acd_demux_axi_m_01_bid    (axi_aic_cd_m_b.id),
    .o_acd_demux_axi_m_01_bresp  (axi_aic_cd_m_b.resp),
    .o_acd_demux_axi_m_01_bvalid (axi_aic_cd_m_b_valid),
    .o_acd_demux_axi_m_01_rdata  (axi_aic_cd_m_r.data),
    .o_acd_demux_axi_m_01_rid    (axi_aic_cd_m_r.id),
    .o_acd_demux_axi_m_01_rlast  (axi_aic_cd_m_r.last),
    .o_acd_demux_axi_m_01_rresp  (axi_aic_cd_m_r.resp),
    .o_acd_demux_axi_m_01_rvalid (axi_aic_cd_m_r_valid),
    .o_acd_demux_axi_m_01_wready (axi_aic_cd_m_w_ready),
    ///////////////////////////////////
    // Config Connection to Firewall //
    ///////////////////////////////////
    .o_acd_demux_axi_s_awid   (axi_acd_to_firewall_aw.id),
    .o_acd_demux_axi_s_awaddr (axi_acd_to_firewall_aw.addr),
    .o_acd_demux_axi_s_awsize (axi_acd_to_firewall_aw.size),
    .o_acd_demux_axi_s_awlen  (axi_acd_to_firewall_aw.len),
    .o_acd_demux_axi_s_awburst(axi_acd_to_firewall_aw.burst),
    .o_acd_demux_axi_s_awlock (axi_acd_to_firewall_aw.lock),
    .o_acd_demux_axi_s_awcache(axi_acd_to_firewall_aw.cache),
    .o_acd_demux_axi_s_awprot (axi_acd_to_firewall_aw.prot),
    .o_acd_demux_axi_s_awvalid(axi_acd_to_firewall_aw_valid),
    .i_acd_demux_axi_s_awready(axi_acd_to_firewall_aw_ready),

    .o_acd_demux_axi_s_wdata  (axi_acd_to_firewall_w.data),
    .o_acd_demux_axi_s_wstrb  (axi_acd_to_firewall_w.strb),
    .o_acd_demux_axi_s_wlast  (axi_acd_to_firewall_w.last),
    .o_acd_demux_axi_s_wvalid (axi_acd_to_firewall_w_valid),
    .i_acd_demux_axi_s_wready (axi_acd_to_firewall_w_ready),

    .i_acd_demux_axi_s_bid    (axi_acd_to_firewall_b.id),
    .i_acd_demux_axi_s_bresp  (axi_acd_to_firewall_b.resp),
    .i_acd_demux_axi_s_bvalid (axi_acd_to_firewall_b_valid),
    .o_acd_demux_axi_s_bready (axi_acd_to_firewall_b_ready),

    .o_acd_demux_axi_s_arid   (axi_acd_to_firewall_ar.id),
    .o_acd_demux_axi_s_araddr (axi_acd_to_firewall_ar.addr),
    .o_acd_demux_axi_s_arlen  (axi_acd_to_firewall_ar.len),
    .o_acd_demux_axi_s_arsize (axi_acd_to_firewall_ar.size),
    .o_acd_demux_axi_s_arburst(axi_acd_to_firewall_ar.burst),
    .o_acd_demux_axi_s_arlock (axi_acd_to_firewall_ar.lock),
    .o_acd_demux_axi_s_arcache(axi_acd_to_firewall_ar.cache),
    .o_acd_demux_axi_s_arprot (axi_acd_to_firewall_ar.prot),
    .o_acd_demux_axi_s_arvalid(axi_acd_to_firewall_ar_valid),
    .i_acd_demux_axi_s_arready(axi_acd_to_firewall_ar_ready),

    .i_acd_demux_axi_s_rid    (axi_acd_to_firewall_r.id),
    .i_acd_demux_axi_s_rdata  (axi_acd_to_firewall_r.data),
    .i_acd_demux_axi_s_rlast  (axi_acd_to_firewall_r.last),
    .i_acd_demux_axi_s_rresp  (axi_acd_to_firewall_r.resp),
    .i_acd_demux_axi_s_rvalid (axi_acd_to_firewall_r_valid),
    .o_acd_demux_axi_s_rready (axi_acd_to_firewall_r_ready),

    //////////////////////////////////
    // Config Connection to Mailbox //
    //////////////////////////////////
    .o_config_axi_s_mailbox_awid   (axi_lt_mailbox_aw.id[aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW -1:0]),
    .o_config_axi_s_mailbox_awaddr (axi_lt_mailbox_aw.addr),
    .o_config_axi_s_mailbox_awlen  (axi_lt_mailbox_aw.len),
    .o_config_axi_s_mailbox_awsize (axi_lt_mailbox_aw.size),
    .o_config_axi_s_mailbox_awburst(axi_lt_mailbox_aw.burst),
    .o_config_axi_s_mailbox_awlock (/* not supported by CSR */),
    .o_config_axi_s_mailbox_awcache(/* not supported by CSR */),
    .o_config_axi_s_mailbox_awprot (/* not supported by CSR */),
    .o_config_axi_s_mailbox_awvalid(axi_lt_mailbox_aw.valid),
    .i_config_axi_s_mailbox_awready(axi_lt_mailbox_aw_ready),

    .o_config_axi_s_mailbox_wdata  (axi_lt_mailbox_w.data),
    .o_config_axi_s_mailbox_wstrb  (axi_lt_mailbox_w.strb),
    .o_config_axi_s_mailbox_wlast  (axi_lt_mailbox_w.last),
    .o_config_axi_s_mailbox_wvalid (axi_lt_mailbox_w.valid),
    .i_config_axi_s_mailbox_wready (axi_lt_mailbox_w_ready),

    .i_config_axi_s_mailbox_bid    (axi_lt_mailbox_b.id[aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW -1:0]),
    .i_config_axi_s_mailbox_bresp  (axi_lt_mailbox_b.resp),
    .i_config_axi_s_mailbox_bvalid (axi_lt_mailbox_b.valid),
    .o_config_axi_s_mailbox_bready (axi_lt_mailbox_b_ready),

    .o_config_axi_s_mailbox_arid   (axi_lt_mailbox_ar.id[aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW -1:0]),
    .o_config_axi_s_mailbox_araddr (axi_lt_mailbox_ar.addr),
    .o_config_axi_s_mailbox_arlen  (axi_lt_mailbox_ar.len),
    .o_config_axi_s_mailbox_arsize (axi_lt_mailbox_ar.size),
    .o_config_axi_s_mailbox_arburst(axi_lt_mailbox_ar.burst),
    .o_config_axi_s_mailbox_arlock (/* not supported by CSR */),
    .o_config_axi_s_mailbox_arcache(/* not supported by CSR */),
    .o_config_axi_s_mailbox_arprot (/* not supported by CSR */),
    .o_config_axi_s_mailbox_arvalid(axi_lt_mailbox_ar.valid),
    .i_config_axi_s_mailbox_arready(axi_lt_mailbox_ar_ready),

    .i_config_axi_s_mailbox_rid    (axi_lt_mailbox_r.id[aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW -1:0]),
    .i_config_axi_s_mailbox_rdata  (axi_lt_mailbox_r.data),
    .i_config_axi_s_mailbox_rresp  (axi_lt_mailbox_r.resp),
    .i_config_axi_s_mailbox_rlast  (axi_lt_mailbox_r.last),
    .i_config_axi_s_mailbox_rvalid (axi_lt_mailbox_r.valid),
    .o_config_axi_s_mailbox_rready (axi_lt_mailbox_r_ready),
    ////////////////////////////////////////
    // Config Connection to Token Manager //
    ////////////////////////////////////////
    .o_config_axi_s_token_awid   (axi_lt_token_manager_aw.id),
    .o_config_axi_s_token_awaddr (axi_lt_token_manager_aw.addr),
    .o_config_axi_s_token_awlen  (axi_lt_token_manager_aw.len),
    .o_config_axi_s_token_awsize (axi_lt_token_manager_aw.size),
    .o_config_axi_s_token_awburst(axi_lt_token_manager_aw.burst),
    .o_config_axi_s_token_awlock (/* not supported by CSR */),
    .o_config_axi_s_token_awcache(/* not supported by CSR */),
    .o_config_axi_s_token_awprot (/* not supported by CSR */),
    .o_config_axi_s_token_awvalid(axi_lt_token_manager_aw.valid),
    .i_config_axi_s_token_awready(axi_lt_token_manager_aw_ready),

    .o_config_axi_s_token_wdata  (axi_lt_token_manager_w.data),
    .o_config_axi_s_token_wstrb  (axi_lt_token_manager_w.strb),
    .o_config_axi_s_token_wlast  (axi_lt_token_manager_w.last),
    .o_config_axi_s_token_wvalid (axi_lt_token_manager_w.valid),
    .i_config_axi_s_token_wready (axi_lt_token_manager_w_ready),

    .i_config_axi_s_token_bid    (axi_lt_token_manager_b.id),
    .i_config_axi_s_token_bresp  (axi_lt_token_manager_b.resp),
    .i_config_axi_s_token_bvalid (axi_lt_token_manager_b.valid),
    .o_config_axi_s_token_bready (axi_lt_token_manager_b_ready),

    .o_config_axi_s_token_arid   (axi_lt_token_manager_ar.id),
    .o_config_axi_s_token_araddr (axi_lt_token_manager_ar.addr),
    .o_config_axi_s_token_arlen  (axi_lt_token_manager_ar.len),
    .o_config_axi_s_token_arsize (axi_lt_token_manager_ar.size),
    .o_config_axi_s_token_arburst(axi_lt_token_manager_ar.burst),
    .o_config_axi_s_token_arlock (/* not supported by CSR */),
    .o_config_axi_s_token_arcache(/* not supported by CSR */),
    .o_config_axi_s_token_arprot (/* not supported by CSR */),
    .o_config_axi_s_token_arvalid(axi_lt_token_manager_ar.valid),
    .i_config_axi_s_token_arready(axi_lt_token_manager_ar_ready),

    .i_config_axi_s_token_rid    (axi_lt_token_manager_r.id),
    .i_config_axi_s_token_rdata  (axi_lt_token_manager_r.data),
    .i_config_axi_s_token_rresp  (axi_lt_token_manager_r.resp),
    .i_config_axi_s_token_rlast  (axi_lt_token_manager_r.last),
    .i_config_axi_s_token_rvalid (axi_lt_token_manager_r.valid),
    .o_config_axi_s_token_rready (axi_lt_token_manager_r_ready),
    ///////////////////////////////////
    // Config Connection to AIC CSRs //
    ///////////////////////////////////
    .o_config_axi_s_csr_awid   (axi_lt_aw.id),
    .o_config_axi_s_csr_awaddr (axi_lt_aw.addr),
    .o_config_axi_s_csr_awlen  (axi_lt_aw.len),
    .o_config_axi_s_csr_awsize (axi_lt_aw.size),
    .o_config_axi_s_csr_awburst(axi_lt_aw.burst),
    .o_config_axi_s_csr_awlock (/* not supported by CSR */),
    .o_config_axi_s_csr_awcache(/* not supported by CSR */),
    .o_config_axi_s_csr_awprot (/* not supported by CSR */),
    .o_config_axi_s_csr_awvalid(axi_lt_aw.valid),
    .i_config_axi_s_csr_awready(axi_lt_aw_ready),

    .o_config_axi_s_csr_wdata  (axi_lt_w.data),
    .o_config_axi_s_csr_wstrb  (axi_lt_w.strb),
    .o_config_axi_s_csr_wlast  (axi_lt_w.last),
    .o_config_axi_s_csr_wvalid (axi_lt_w.valid),
    .i_config_axi_s_csr_wready (axi_lt_w_ready),

    .i_config_axi_s_csr_bid    (axi_lt_b.id),
    .i_config_axi_s_csr_bresp  (axi_lt_b.resp),
    .i_config_axi_s_csr_bvalid (axi_lt_b.valid),
    .o_config_axi_s_csr_bready (axi_lt_b_ready),

    .o_config_axi_s_csr_arid   (axi_lt_ar.id),
    .o_config_axi_s_csr_araddr (axi_lt_ar.addr),
    .o_config_axi_s_csr_arlen  (axi_lt_ar.len),
    .o_config_axi_s_csr_arsize (axi_lt_ar.size),
    .o_config_axi_s_csr_arburst(axi_lt_ar.burst),
    .o_config_axi_s_csr_arlock (/* not supported by CSR */),
    .o_config_axi_s_csr_arcache(/* not supported by CSR */),
    .o_config_axi_s_csr_arprot (/* not supported by CSR */),
    .o_config_axi_s_csr_arvalid(axi_lt_ar.valid),
    .i_config_axi_s_csr_arready(axi_lt_ar_ready),

    .i_config_axi_s_csr_rid    (axi_lt_r.id),
    .i_config_axi_s_csr_rdata  (axi_lt_r.data),
    .i_config_axi_s_csr_rresp  (axi_lt_r.resp),
    .i_config_axi_s_csr_rlast  (axi_lt_r.last),
    .i_config_axi_s_csr_rvalid (axi_lt_r.valid),
    .o_config_axi_s_csr_rready (axi_lt_r_ready),
    ///////////////////////////////////////////
    // Config Connection to TIMESTAMP_LOGGER //
    ///////////////////////////////////////////
    .o_config_axi_s_ts_awid   (axi_timestamp_logger_aw.id),
    .o_config_axi_s_ts_awaddr (axi_timestamp_logger_aw.addr),
    .o_config_axi_s_ts_awlen  (axi_timestamp_logger_aw.len),
    .o_config_axi_s_ts_awsize (axi_timestamp_logger_aw.size),
    .o_config_axi_s_ts_awburst(axi_timestamp_logger_aw.burst),
    .o_config_axi_s_ts_awlock (axi_timestamp_logger_aw.lock),
    .o_config_axi_s_ts_awcache(axi_timestamp_logger_aw.cache),
    .o_config_axi_s_ts_awprot (axi_timestamp_logger_aw.prot),
    .o_config_axi_s_ts_awvalid(axi_timestamp_logger_aw_valid),
    .i_config_axi_s_ts_awready(axi_timestamp_logger_aw_ready),
    .o_config_axi_s_ts_wdata  (axi_timestamp_logger_w.data),
    .o_config_axi_s_ts_wstrb  (axi_timestamp_logger_w.strb),
    .o_config_axi_s_ts_wlast  (axi_timestamp_logger_w.last),
    .o_config_axi_s_ts_wvalid (axi_timestamp_logger_w_valid),
    .i_config_axi_s_ts_wready (axi_timestamp_logger_w_ready),
    .i_config_axi_s_ts_bid    (axi_timestamp_logger_b.id),
    .i_config_axi_s_ts_bresp  (axi_timestamp_logger_b.resp),
    .i_config_axi_s_ts_bvalid (axi_timestamp_logger_b_valid),
    .o_config_axi_s_ts_bready (axi_timestamp_logger_b_ready),
    .o_config_axi_s_ts_arid   (axi_timestamp_logger_ar.id),
    .o_config_axi_s_ts_araddr (axi_timestamp_logger_ar.addr),
    .o_config_axi_s_ts_arlen  (axi_timestamp_logger_ar.len),
    .o_config_axi_s_ts_arsize (axi_timestamp_logger_ar.size),
    .o_config_axi_s_ts_arburst(axi_timestamp_logger_ar.burst),
    .o_config_axi_s_ts_arlock (axi_timestamp_logger_ar.lock),
    .o_config_axi_s_ts_arcache(axi_timestamp_logger_ar.cache),
    .o_config_axi_s_ts_arprot (axi_timestamp_logger_ar.prot),
    .o_config_axi_s_ts_arvalid(axi_timestamp_logger_ar_valid),
    .i_config_axi_s_ts_arready(axi_timestamp_logger_ar_ready),
    .i_config_axi_s_ts_rid    (axi_timestamp_logger_r.id),
    .i_config_axi_s_ts_rdata  (axi_timestamp_logger_r.data),
    .i_config_axi_s_ts_rresp  (axi_timestamp_logger_r.resp),
    .i_config_axi_s_ts_rlast  (axi_timestamp_logger_r.last),
    .i_config_axi_s_ts_rvalid (axi_timestamp_logger_r_valid),
    .o_config_axi_s_ts_rready (axi_timestamp_logger_r_ready),
    //////////////////////////////////
    // Config Connection to RV_PLIC //
    //////////////////////////////////
    .o_config_axi_s_plic_awid   (axi_rv_plic_aw.id),
    .o_config_axi_s_plic_awaddr (axi_rv_plic_aw.addr),
    .o_config_axi_s_plic_awlen  (axi_rv_plic_aw.len),
    .o_config_axi_s_plic_awsize (axi_rv_plic_aw.size),
    .o_config_axi_s_plic_awburst(axi_rv_plic_aw.burst),
    .o_config_axi_s_plic_awlock (/* not used by plic */),
    .o_config_axi_s_plic_awcache(/* not used by plic */),
    .o_config_axi_s_plic_awprot (/* not used by plic */),
    .o_config_axi_s_plic_awvalid(axi_rv_plic_aw.valid),
    .i_config_axi_s_plic_awready(axi_rv_plic_aw_ready),
    .o_config_axi_s_plic_wdata  (axi_rv_plic_w.data),
    .o_config_axi_s_plic_wstrb  (axi_rv_plic_w.strb),
    .o_config_axi_s_plic_wlast  (axi_rv_plic_w.last),
    .o_config_axi_s_plic_wvalid (axi_rv_plic_w.valid),
    .i_config_axi_s_plic_wready (axi_rv_plic_w_ready),
    .i_config_axi_s_plic_bid    (axi_rv_plic_b.id),
    .i_config_axi_s_plic_bresp  (axi_rv_plic_b.resp),
    .i_config_axi_s_plic_bvalid (axi_rv_plic_b.valid),
    .o_config_axi_s_plic_bready (axi_rv_plic_b_ready),
    .o_config_axi_s_plic_arid   (axi_rv_plic_ar.id),
    .o_config_axi_s_plic_araddr (axi_rv_plic_ar.addr),
    .o_config_axi_s_plic_arlen  (axi_rv_plic_ar.len),
    .o_config_axi_s_plic_arsize (axi_rv_plic_ar.size),
    .o_config_axi_s_plic_arburst(axi_rv_plic_ar.burst),
    .o_config_axi_s_plic_arlock (/* not used by plic */),
    .o_config_axi_s_plic_arcache(/* not used by plic */),
    .o_config_axi_s_plic_arprot (/* not used by plic */),
    .o_config_axi_s_plic_arvalid(axi_rv_plic_ar.valid),
    .i_config_axi_s_plic_arready(axi_rv_plic_ar_ready),
    .i_config_axi_s_plic_rid    (axi_rv_plic_r.id),
    .i_config_axi_s_plic_rdata  (axi_rv_plic_r.data),
    .i_config_axi_s_plic_rresp  (axi_rv_plic_r.resp),
    .i_config_axi_s_plic_rlast  (axi_rv_plic_r.last),
    .i_config_axi_s_plic_rvalid (axi_rv_plic_r.valid),
    .o_config_axi_s_plic_rready (axi_rv_plic_r_ready),
    ///////////////////////////////////
    // Config Connection from LT DMA //
    ///////////////////////////////////
    .o_config_axi_s_lpdma_awid   (axi_lt_dma_config_aw.id),
    .o_config_axi_s_lpdma_awaddr (axi_lt_dma_config_aw.addr),
    .o_config_axi_s_lpdma_awlen  (axi_lt_dma_config_aw.len),
    .o_config_axi_s_lpdma_awsize (axi_lt_dma_config_aw.size),
    .o_config_axi_s_lpdma_awburst(axi_lt_dma_config_aw.burst),
    .o_config_axi_s_lpdma_awlock (axi_lt_dma_config_aw.lock),
    .o_config_axi_s_lpdma_awcache(axi_lt_dma_config_aw.cache),
    .o_config_axi_s_lpdma_awprot (axi_lt_dma_config_aw.prot),
    .o_config_axi_s_lpdma_awvalid(axi_lt_dma_config_aw_valid),
    .i_config_axi_s_lpdma_awready(axi_lt_dma_config_aw_ready),

    .o_config_axi_s_lpdma_wdata  (axi_lt_dma_config_w.data),
    .o_config_axi_s_lpdma_wstrb  (axi_lt_dma_config_w.strb),
    .o_config_axi_s_lpdma_wlast  (axi_lt_dma_config_w.last),
    .o_config_axi_s_lpdma_wvalid (axi_lt_dma_config_w_valid),
    .i_config_axi_s_lpdma_wready (axi_lt_dma_config_w_ready),

    .i_config_axi_s_lpdma_bid    (axi_lt_dma_config_b.id),
    .i_config_axi_s_lpdma_bresp  (axi_lt_dma_config_b.resp),
    .i_config_axi_s_lpdma_bvalid (axi_lt_dma_config_b_valid),
    .o_config_axi_s_lpdma_bready (axi_lt_dma_config_b_ready),

    .o_config_axi_s_lpdma_arid   (axi_lt_dma_config_ar.id),
    .o_config_axi_s_lpdma_araddr (axi_lt_dma_config_ar.addr),
    .o_config_axi_s_lpdma_arsize (axi_lt_dma_config_ar.size),
    .o_config_axi_s_lpdma_arlen  (axi_lt_dma_config_ar.len),
    .o_config_axi_s_lpdma_arburst(axi_lt_dma_config_ar.burst),
    .o_config_axi_s_lpdma_arlock (axi_lt_dma_config_ar.lock),
    .o_config_axi_s_lpdma_arcache(axi_lt_dma_config_ar.cache),
    .o_config_axi_s_lpdma_arprot (axi_lt_dma_config_ar.prot),
    .o_config_axi_s_lpdma_arvalid(axi_lt_dma_config_ar_valid),
    .i_config_axi_s_lpdma_arready(axi_lt_dma_config_ar_ready),

    .i_config_axi_s_lpdma_rid    (axi_lt_dma_config_r.id),
    .i_config_axi_s_lpdma_rdata  (axi_lt_dma_config_r.data),
    .i_config_axi_s_lpdma_rresp  (axi_lt_dma_config_r.resp),
    .i_config_axi_s_lpdma_rlast  (axi_lt_dma_config_r.last),
    .i_config_axi_s_lpdma_rvalid (axi_lt_dma_config_r_valid),
    .o_config_axi_s_lpdma_rready (axi_lt_dma_config_r_ready),
    /////////////////////////////////
    // Config Connection to AIC_CD //
    /////////////////////////////////
    .i_config_axi_s_acd_arready(axi_aic_cd_s_ar_ready),
    .i_config_axi_s_acd_awready(axi_aic_cd_s_aw_ready),
    .i_config_axi_s_acd_bid    (axi_aic_cd_s_b.id),
    .i_config_axi_s_acd_bresp  (axi_aic_cd_s_b.resp),
    .i_config_axi_s_acd_bvalid (axi_aic_cd_s_b_valid),
    .i_config_axi_s_acd_rdata  (axi_aic_cd_s_r.data),
    .i_config_axi_s_acd_rid    (axi_aic_cd_s_r.id),
    .i_config_axi_s_acd_rlast  (axi_aic_cd_s_r.last),
    .i_config_axi_s_acd_rresp  (axi_aic_cd_s_r.resp),
    .i_config_axi_s_acd_rvalid (axi_aic_cd_s_r_valid),
    .i_config_axi_s_acd_wready (axi_aic_cd_s_w_ready),
    .o_config_axi_s_acd_araddr (axi_aic_cd_s_ar.addr),
    .o_config_axi_s_acd_arburst(axi_aic_cd_s_ar.burst),
    .o_config_axi_s_acd_arcache(axi_aic_cd_s_ar.cache),
    .o_config_axi_s_acd_arid   (axi_aic_cd_s_ar.id),
    .o_config_axi_s_acd_arlen  (axi_aic_cd_s_ar.len),
    .o_config_axi_s_acd_arlock (axi_aic_cd_s_ar.lock),
    .o_config_axi_s_acd_arprot (axi_aic_cd_s_ar.prot),
    .o_config_axi_s_acd_arsize (axi_aic_cd_s_ar.size),
    .o_config_axi_s_acd_arvalid(axi_aic_cd_s_ar_valid),
    .o_config_axi_s_acd_awaddr (axi_aic_cd_s_aw.addr),
    .o_config_axi_s_acd_awburst(axi_aic_cd_s_aw.burst),
    .o_config_axi_s_acd_awcache(axi_aic_cd_s_aw.cache),
    .o_config_axi_s_acd_awid   (axi_aic_cd_s_aw.id),
    .o_config_axi_s_acd_awlen  (axi_aic_cd_s_aw.len),
    .o_config_axi_s_acd_awlock (axi_aic_cd_s_aw.lock),
    .o_config_axi_s_acd_awprot (axi_aic_cd_s_aw.prot),
    .o_config_axi_s_acd_awsize (axi_aic_cd_s_aw.size),
    .o_config_axi_s_acd_awvalid(axi_aic_cd_s_aw_valid),
    .o_config_axi_s_acd_bready (axi_aic_cd_s_b_ready),
    .o_config_axi_s_acd_rready (axi_aic_cd_s_r_ready),
    .o_config_axi_s_acd_wdata  (axi_aic_cd_s_w.data),
    .o_config_axi_s_acd_wlast  (axi_aic_cd_s_w.last),
    .o_config_axi_s_acd_wstrb  (axi_aic_cd_s_w.strb),
    .o_config_axi_s_acd_wvalid (axi_aic_cd_s_w_valid),
    ////////////////////////////////////////////////////////
    // Config Connection to Firewall to Controll Crossbar //
    ///////////////////////////////////////////////////////
    .o_config_axi_s_firew_awid   (axi_config_to_firewall_aw.id),
    .o_config_axi_s_firew_awaddr (axi_config_to_firewall_aw.addr),
    .o_config_axi_s_firew_awlen  (axi_config_to_firewall_aw.len),
    .o_config_axi_s_firew_awsize (axi_config_to_firewall_aw.size),
    .o_config_axi_s_firew_awburst(axi_config_to_firewall_aw.burst),
    .o_config_axi_s_firew_awlock (axi_config_to_firewall_aw.lock),
    .o_config_axi_s_firew_awcache(axi_config_to_firewall_aw.cache),
    .o_config_axi_s_firew_awprot (axi_config_to_firewall_aw.prot),
    .o_config_axi_s_firew_awvalid(axi_config_to_firewall_aw_valid),
    .i_config_axi_s_firew_awready(axi_config_to_firewall_aw_ready),

    .o_config_axi_s_firew_wdata  (axi_config_to_firewall_w.data),
    .o_config_axi_s_firew_wstrb  (axi_config_to_firewall_w.strb),
    .o_config_axi_s_firew_wlast  (axi_config_to_firewall_w.last),
    .o_config_axi_s_firew_wvalid (axi_config_to_firewall_w_valid),
    .i_config_axi_s_firew_wready (axi_config_to_firewall_w_ready),

    .i_config_axi_s_firew_bid    (axi_config_to_firewall_b.id),
    .i_config_axi_s_firew_bresp  (axi_config_to_firewall_b.resp),
    .i_config_axi_s_firew_bvalid (axi_config_to_firewall_b_valid),
    .o_config_axi_s_firew_bready (axi_config_to_firewall_b_ready),

    .o_config_axi_s_firew_arid   (axi_config_to_firewall_ar.id),
    .o_config_axi_s_firew_araddr (axi_config_to_firewall_ar.addr),
    .o_config_axi_s_firew_arlen  (axi_config_to_firewall_ar.len),
    .o_config_axi_s_firew_arsize (axi_config_to_firewall_ar.size),
    .o_config_axi_s_firew_arburst(axi_config_to_firewall_ar.burst),
    .o_config_axi_s_firew_arlock (axi_config_to_firewall_ar.lock),
    .o_config_axi_s_firew_arcache(axi_config_to_firewall_ar.cache),
    .o_config_axi_s_firew_arprot (axi_config_to_firewall_ar.prot),
    .o_config_axi_s_firew_arvalid(axi_config_to_firewall_ar_valid),
    .i_config_axi_s_firew_arready(axi_config_to_firewall_ar_ready),

    .i_config_axi_s_firew_rid    (axi_config_to_firewall_r.id),
    .i_config_axi_s_firew_rdata  (axi_config_to_firewall_r.data),
    .i_config_axi_s_firew_rresp  (axi_config_to_firewall_r.resp),
    .i_config_axi_s_firew_rlast  (axi_config_to_firewall_r.last),
    .i_config_axi_s_firew_rvalid (axi_config_to_firewall_r_valid),
    .o_config_axi_s_firew_rready (axi_config_to_firewall_r_ready),
    ///////////////////////////////////////////
    // Control Connection from ACD Fire Wall //
    ///////////////////////////////////////////
    .i_control_axi_m_01_awid   ({1'b0, axi_acd_to_firewall_aw.id}),
    .i_control_axi_m_01_awaddr (axi_acd_to_firewall_aw.addr),
    .i_control_axi_m_01_awlen  (axi_acd_to_firewall_aw.len),
    .i_control_axi_m_01_awsize (axi_acd_to_firewall_aw.size),
    .i_control_axi_m_01_awburst(axi_acd_to_firewall_aw.burst),
    .i_control_axi_m_01_awlock (axi_acd_to_firewall_aw.lock),
    .i_control_axi_m_01_awcache(axi_acd_to_firewall_aw.cache),
    .i_control_axi_m_01_awprot (axi_acd_to_firewall_aw.prot),
    .i_control_axi_m_01_awvalid(axi_acd_to_firewall_aw_valid),
    .o_control_axi_m_01_awready(axi_acd_to_firewall_aw_ready),

    .i_control_axi_m_01_wdata  (axi_acd_to_firewall_w.data),
    .i_control_axi_m_01_wstrb  (axi_acd_to_firewall_w.strb),
    .i_control_axi_m_01_wlast  (axi_acd_to_firewall_w.last),
    .i_control_axi_m_01_wvalid (axi_acd_to_firewall_w_valid),
    .o_control_axi_m_01_wready (axi_acd_to_firewall_w_ready),

    .o_control_axi_m_01_bid    ({axi_acd_to_firewall_bid_dummy, axi_acd_to_firewall_b.id}),
    .o_control_axi_m_01_bresp  (axi_acd_to_firewall_b.resp),
    .o_control_axi_m_01_bvalid (axi_acd_to_firewall_b_valid),
    .i_control_axi_m_01_bready (axi_acd_to_firewall_b_ready),

    .i_control_axi_m_01_arid   ({1'b0, axi_acd_to_firewall_ar.id}),
    .i_control_axi_m_01_araddr (axi_acd_to_firewall_ar.addr),
    .i_control_axi_m_01_arlen  (axi_acd_to_firewall_ar.len),
    .i_control_axi_m_01_arsize (axi_acd_to_firewall_ar.size),
    .i_control_axi_m_01_arburst(axi_acd_to_firewall_ar.burst),
    .i_control_axi_m_01_arlock (axi_acd_to_firewall_ar.lock),
    .i_control_axi_m_01_arcache(axi_acd_to_firewall_ar.cache),
    .i_control_axi_m_01_arprot (axi_acd_to_firewall_ar.prot),
    .i_control_axi_m_01_arvalid(axi_acd_to_firewall_ar_valid),
    .o_control_axi_m_01_arready(axi_acd_to_firewall_ar_ready),

    .o_control_axi_m_01_rid    ({axi_acd_to_firewall_rid_dummy, axi_acd_to_firewall_r.id}),
    .o_control_axi_m_01_rdata  (axi_acd_to_firewall_r.data),
    .o_control_axi_m_01_rresp  (axi_acd_to_firewall_r.resp),
    .o_control_axi_m_01_rlast  (axi_acd_to_firewall_r.last),
    .o_control_axi_m_01_rvalid (axi_acd_to_firewall_r_valid),
    .i_control_axi_m_01_rready (axi_acd_to_firewall_r_ready),
    //////////////////////////////////////////////////////
    // Control Connection from Config Crossbar Firewall //
    //////////////////////////////////////////////////////
    .i_control_axi_m_02_awid   (axi_config_to_firewall_aw.id),
    .i_control_axi_m_02_awaddr (axi_config_to_firewall_aw.addr),
    .i_control_axi_m_02_awlen  (axi_config_to_firewall_aw.len),
    .i_control_axi_m_02_awsize (axi_config_to_firewall_aw.size),
    .i_control_axi_m_02_awburst(axi_config_to_firewall_aw.burst),
    .i_control_axi_m_02_awlock (axi_config_to_firewall_aw.lock),
    .i_control_axi_m_02_awcache(axi_config_to_firewall_aw.cache),
    .i_control_axi_m_02_awprot (axi_config_to_firewall_aw.prot),
    .i_control_axi_m_02_awvalid(axi_config_to_firewall_aw_valid),
    .o_control_axi_m_02_awready(axi_config_to_firewall_aw_ready),

    .i_control_axi_m_02_wdata  (axi_config_to_firewall_w.data),
    .i_control_axi_m_02_wstrb  (axi_config_to_firewall_w.strb),
    .i_control_axi_m_02_wlast  (axi_config_to_firewall_w.last),
    .i_control_axi_m_02_wvalid (axi_config_to_firewall_w_valid),
    .o_control_axi_m_02_wready (axi_config_to_firewall_w_ready),

    .o_control_axi_m_02_bid    (axi_config_to_firewall_b.id),
    .o_control_axi_m_02_bresp  (axi_config_to_firewall_b.resp),
    .o_control_axi_m_02_bvalid (axi_config_to_firewall_b_valid),
    .i_control_axi_m_02_bready (axi_config_to_firewall_b_ready),

    .i_control_axi_m_02_arid   (axi_config_to_firewall_ar.id),
    .i_control_axi_m_02_araddr (axi_config_to_firewall_ar.addr),
    .i_control_axi_m_02_arlen  (axi_config_to_firewall_ar.len),
    .i_control_axi_m_02_arsize (axi_config_to_firewall_ar.size),
    .i_control_axi_m_02_arburst(axi_config_to_firewall_ar.burst),
    .i_control_axi_m_02_arlock (axi_config_to_firewall_ar.lock),
    .i_control_axi_m_02_arcache(axi_config_to_firewall_ar.cache),
    .i_control_axi_m_02_arprot (axi_config_to_firewall_ar.prot),
    .i_control_axi_m_02_arvalid(axi_config_to_firewall_ar_valid),
    .o_control_axi_m_02_arready(axi_config_to_firewall_ar_ready),

    .o_control_axi_m_02_rid    (axi_config_to_firewall_r.id),
    .o_control_axi_m_02_rdata  (axi_config_to_firewall_r.data),
    .o_control_axi_m_02_rresp  (axi_config_to_firewall_r.resp),
    .o_control_axi_m_02_rlast  (axi_config_to_firewall_r.last),
    .o_control_axi_m_02_rvalid (axi_config_to_firewall_r_valid),
    .i_control_axi_m_02_rready (axi_config_to_firewall_r_ready),
    //////////////////////////
    // HT Connection to DMA //
    //////////////////////////
    .o_control_axi_s_hpdma_awid   (axi_ht_dma_config_aw.id),
    .o_control_axi_s_hpdma_awaddr (axi_ht_dma_config_aw.addr),
    .o_control_axi_s_hpdma_awsize (axi_ht_dma_config_aw.size),
    .o_control_axi_s_hpdma_awlen  (axi_ht_dma_config_aw.len),
    .o_control_axi_s_hpdma_awburst(axi_ht_dma_config_aw.burst),
    .o_control_axi_s_hpdma_awlock (axi_ht_dma_config_aw.lock),
    .o_control_axi_s_hpdma_awcache(axi_ht_dma_config_aw.cache),
    .o_control_axi_s_hpdma_awprot (axi_ht_dma_config_aw.prot),
    .o_control_axi_s_hpdma_awvalid(axi_ht_dma_config_aw_valid),
    .i_control_axi_s_hpdma_awready(axi_ht_dma_config_aw_ready),

    .o_control_axi_s_hpdma_wdata  (axi_ht_dma_config_w.data),
    .o_control_axi_s_hpdma_wstrb  (axi_ht_dma_config_w.strb),
    .o_control_axi_s_hpdma_wlast  (axi_ht_dma_config_w.last),
    .o_control_axi_s_hpdma_wvalid (axi_ht_dma_config_w_valid),
    .i_control_axi_s_hpdma_wready (axi_ht_dma_config_w_ready),

    .i_control_axi_s_hpdma_bid    (axi_ht_dma_config_b.id),
    .i_control_axi_s_hpdma_bresp  (axi_ht_dma_config_b.resp),
    .i_control_axi_s_hpdma_bvalid (axi_ht_dma_config_b_valid),
    .o_control_axi_s_hpdma_bready (axi_ht_dma_config_b_ready),

    .o_control_axi_s_hpdma_arid   (axi_ht_dma_config_ar.id),
    .o_control_axi_s_hpdma_araddr (axi_ht_dma_config_ar.addr),
    .o_control_axi_s_hpdma_arlen  (axi_ht_dma_config_ar.len),
    .o_control_axi_s_hpdma_arsize (axi_ht_dma_config_ar.size),
    .o_control_axi_s_hpdma_arburst(axi_ht_dma_config_ar.burst),
    .o_control_axi_s_hpdma_arlock (axi_ht_dma_config_ar.lock),
    .o_control_axi_s_hpdma_arcache(axi_ht_dma_config_ar.cache),
    .o_control_axi_s_hpdma_arprot (axi_ht_dma_config_ar.prot),
    .o_control_axi_s_hpdma_arvalid(axi_ht_dma_config_ar_valid),
    .i_control_axi_s_hpdma_arready(axi_ht_dma_config_ar_ready),

    .i_control_axi_s_hpdma_rid    (axi_ht_dma_config_r.id),
    .i_control_axi_s_hpdma_rdata  (axi_ht_dma_config_r.data),
    .i_control_axi_s_hpdma_rlast  (axi_ht_dma_config_r.last),
    .i_control_axi_s_hpdma_rresp  (axi_ht_dma_config_r.resp),
    .i_control_axi_s_hpdma_rvalid (axi_ht_dma_config_r_valid),
    .o_control_axi_s_hpdma_rready (axi_ht_dma_config_r_ready),
    //////////////////////////////////////
    // LT Connection to DMC L1 Datapath //
    //////////////////////////////////////
    .o_control_axi_s_datapath_awid   (  dmc_l1_lt_axi_m_awid),
    .o_control_axi_s_datapath_awaddr (o_dmc_l1_lt_axi_m_awaddr),
    .o_control_axi_s_datapath_awlen  (o_dmc_l1_lt_axi_m_awlen),
    .o_control_axi_s_datapath_awsize (o_dmc_l1_lt_axi_m_awsize),
    .o_control_axi_s_datapath_awburst(o_dmc_l1_lt_axi_m_awburst),
    .o_control_axi_s_datapath_awlock (), // ASO-UNUSED_OUTPUT: not used
    .o_control_axi_s_datapath_awcache(), // ASO-UNUSED_OUTPUT: not used
    .o_control_axi_s_datapath_awprot (), // ASO-UNUSED_OUTPUT: not used
    .o_control_axi_s_datapath_awvalid(o_dmc_l1_lt_axi_m_awvalid),
    .i_control_axi_s_datapath_awready(i_dmc_l1_lt_axi_m_awready),

    .o_control_axi_s_datapath_wdata  (o_dmc_l1_lt_axi_m_wdata),
    .o_control_axi_s_datapath_wstrb  (o_dmc_l1_lt_axi_m_wstrb),
    .o_control_axi_s_datapath_wlast  (o_dmc_l1_lt_axi_m_wlast),
    .o_control_axi_s_datapath_wvalid (o_dmc_l1_lt_axi_m_wvalid),
    .i_control_axi_s_datapath_wready (i_dmc_l1_lt_axi_m_wready),

    .i_control_axi_s_datapath_bid    (  dmc_l1_lt_axi_m_bid),
    .i_control_axi_s_datapath_bresp  (i_dmc_l1_lt_axi_m_bresp),
    .i_control_axi_s_datapath_bvalid (i_dmc_l1_lt_axi_m_bvalid),
    .o_control_axi_s_datapath_bready (o_dmc_l1_lt_axi_m_bready),

    .o_control_axi_s_datapath_arid   (  dmc_l1_lt_axi_m_arid),
    .o_control_axi_s_datapath_araddr (o_dmc_l1_lt_axi_m_araddr),
    .o_control_axi_s_datapath_arlen  (o_dmc_l1_lt_axi_m_arlen),
    .o_control_axi_s_datapath_arsize (o_dmc_l1_lt_axi_m_arsize),
    .o_control_axi_s_datapath_arburst(o_dmc_l1_lt_axi_m_arburst),
    .o_control_axi_s_datapath_arlock (), // ASO-UNUSED_OUTPUT: not used
    .o_control_axi_s_datapath_arcache(), // ASO-UNUSED_OUTPUT: not used
    .o_control_axi_s_datapath_arprot (), // ASO-UNUSED_OUTPUT: not used
    .o_control_axi_s_datapath_arvalid(o_dmc_l1_lt_axi_m_arvalid),
    .i_control_axi_s_datapath_arready(i_dmc_l1_lt_axi_m_arready),

    .i_control_axi_s_datapath_rid    (  dmc_l1_lt_axi_m_rid),
    .i_control_axi_s_datapath_rdata  (i_dmc_l1_lt_axi_m_rdata),
    .i_control_axi_s_datapath_rresp  (i_dmc_l1_lt_axi_m_rresp),
    .i_control_axi_s_datapath_rlast  (i_dmc_l1_lt_axi_m_rlast),
    .i_control_axi_s_datapath_rvalid (i_dmc_l1_lt_axi_m_rvalid),
    .o_control_axi_s_datapath_rready (o_dmc_l1_lt_axi_m_rready),
    //////////////////////////////
    // HT Connection from CVA6V //
    //////////////////////////////
    .i_cva6_demux_axi_m_01_awid   (axi_cva6v_cut_aw.id),
    .i_cva6_demux_axi_m_01_awaddr (axi_cva6v_cut_aw.addr),
    .i_cva6_demux_axi_m_01_awlen  (axi_cva6v_cut_aw.len),
    .i_cva6_demux_axi_m_01_awsize (axi_cva6v_cut_aw.size),
    .i_cva6_demux_axi_m_01_awlock (axi_cva6v_cut_aw.lock),
    .i_cva6_demux_axi_m_01_awburst(axi_cva6v_cut_aw.burst),
    .i_cva6_demux_axi_m_01_awcache(axi_cva6v_cut_aw.cache),
    .i_cva6_demux_axi_m_01_awprot (axi_cva6v_cut_aw.prot),
    .i_cva6_demux_axi_m_01_awvalid(axi_cva6v_cut_aw_valid),
    .o_cva6_demux_axi_m_01_awready(axi_cva6v_cut_aw_ready),

    .i_cva6_demux_axi_m_01_wdata  (axi_cva6v_cut_w.data),
    .i_cva6_demux_axi_m_01_wstrb  (axi_cva6v_cut_w.strb),
    .i_cva6_demux_axi_m_01_wlast  (axi_cva6v_cut_w.last),
    .i_cva6_demux_axi_m_01_wvalid (axi_cva6v_cut_w_valid),
    .o_cva6_demux_axi_m_01_wready (axi_cva6v_cut_w_ready),

    .o_cva6_demux_axi_m_01_bid    (axi_cva6v_cut_b.id),
    .o_cva6_demux_axi_m_01_bresp  (axi_cva6v_cut_b.resp),
    .o_cva6_demux_axi_m_01_bvalid (axi_cva6v_cut_b_valid),
    .i_cva6_demux_axi_m_01_bready (axi_cva6v_cut_b_ready),

    .i_cva6_demux_axi_m_01_arid   (axi_cva6v_cut_ar.id),
    .i_cva6_demux_axi_m_01_araddr (axi_cva6v_cut_ar.addr),
    .i_cva6_demux_axi_m_01_arlen  (axi_cva6v_cut_ar.len),
    .i_cva6_demux_axi_m_01_arsize (axi_cva6v_cut_ar.size),
    .i_cva6_demux_axi_m_01_arburst(axi_cva6v_cut_ar.burst),
    .i_cva6_demux_axi_m_01_arlock (axi_cva6v_cut_ar.lock),
    .i_cva6_demux_axi_m_01_arcache(axi_cva6v_cut_ar.cache),
    .i_cva6_demux_axi_m_01_arprot (axi_cva6v_cut_ar.prot),
    .i_cva6_demux_axi_m_01_arvalid(axi_cva6v_cut_ar_valid),
    .o_cva6_demux_axi_m_01_arready(axi_cva6v_cut_ar_ready),

    .o_cva6_demux_axi_m_01_rid    (axi_cva6v_cut_r.id),
    .o_cva6_demux_axi_m_01_rdata  (axi_cva6v_cut_r.data),
    .o_cva6_demux_axi_m_01_rresp  (axi_cva6v_cut_r.resp),
    .o_cva6_demux_axi_m_01_rlast  (axi_cva6v_cut_r.last),
    .o_cva6_demux_axi_m_01_rvalid (axi_cva6v_cut_r_valid),
    .i_cva6_demux_axi_m_01_rready (axi_cva6v_cut_r_ready),
    ////////////////////////////////
    // HT Connection to DMA ATU 1 //
    ////////////////////////////////
    .i_hp_axi_m_02_awid   (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric].id),
    .i_hp_axi_m_02_awaddr (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric].addr),
    .i_hp_axi_m_02_awlen  (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric].len),
    .i_hp_axi_m_02_awsize (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric].size),
    .i_hp_axi_m_02_awburst(axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric].burst),
    .i_hp_axi_m_02_awlock (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric].lock),
    .i_hp_axi_m_02_awcache(axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric].cache),
    .i_hp_axi_m_02_awprot (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric].prot),
    .i_hp_axi_m_02_awvalid(axi_ht_dma_transfer_aw_valid[AxiHtDmaPortIdxFabric]),
    .o_hp_axi_m_02_awready(axi_ht_dma_transfer_aw_ready[AxiHtDmaPortIdxFabric]),

    .i_hp_axi_m_02_wdata  (axi_ht_dma_transfer_w[AxiHtDmaPortIdxFabric].data),
    .i_hp_axi_m_02_wstrb  (axi_ht_dma_transfer_w[AxiHtDmaPortIdxFabric].strb),
    .i_hp_axi_m_02_wlast  (axi_ht_dma_transfer_w[AxiHtDmaPortIdxFabric].last),
    .i_hp_axi_m_02_wvalid (axi_ht_dma_transfer_w_valid[AxiHtDmaPortIdxFabric]),
    .o_hp_axi_m_02_wready (axi_ht_dma_transfer_w_ready[AxiHtDmaPortIdxFabric]),

    .o_hp_axi_m_02_bid    (axi_ht_dma_transfer_b[AxiHtDmaPortIdxFabric].id),
    .o_hp_axi_m_02_bresp  (axi_ht_dma_transfer_b[AxiHtDmaPortIdxFabric].resp),
    .o_hp_axi_m_02_bvalid (axi_ht_dma_transfer_b_valid[AxiHtDmaPortIdxFabric]),
    .i_hp_axi_m_02_bready (axi_ht_dma_transfer_b_ready[AxiHtDmaPortIdxFabric]),

    .i_hp_axi_m_02_arid   (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric].id),
    .i_hp_axi_m_02_araddr (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric].addr),
    .i_hp_axi_m_02_arlen  (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric].len),
    .i_hp_axi_m_02_arsize (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric].size),
    .i_hp_axi_m_02_arburst(axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric].burst),
    .i_hp_axi_m_02_arlock (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric].lock),
    .i_hp_axi_m_02_arcache(axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric].cache),
    .i_hp_axi_m_02_arprot (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric].prot),
    .i_hp_axi_m_02_arvalid(axi_ht_dma_transfer_ar_valid[AxiHtDmaPortIdxFabric]),
    .o_hp_axi_m_02_arready(axi_ht_dma_transfer_ar_ready[AxiHtDmaPortIdxFabric]),

    .o_hp_axi_m_02_rid    (axi_ht_dma_transfer_r[AxiHtDmaPortIdxFabric].id),
    .o_hp_axi_m_02_rdata  (axi_ht_dma_transfer_r[AxiHtDmaPortIdxFabric].data),
    .o_hp_axi_m_02_rresp  (axi_ht_dma_transfer_r[AxiHtDmaPortIdxFabric].resp),
    .o_hp_axi_m_02_rlast  (axi_ht_dma_transfer_r[AxiHtDmaPortIdxFabric].last),
    .o_hp_axi_m_02_rvalid (axi_ht_dma_transfer_r_valid[AxiHtDmaPortIdxFabric]),
    .i_hp_axi_m_02_rready (axi_ht_dma_transfer_r_ready[AxiHtDmaPortIdxFabric]),
    ////////////////////////////////
    // HT Connection to DMA ATU 1 //
    ////////////////////////////////
    // Note the plus 1 is the port index
    .i_hp_axi_m_03_awid   (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric + 1].id),
    .i_hp_axi_m_03_awaddr (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric + 1].addr),
    .i_hp_axi_m_03_awlen  (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric + 1].len),
    .i_hp_axi_m_03_awsize (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric + 1].size),
    .i_hp_axi_m_03_awburst(axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric + 1].burst),
    .i_hp_axi_m_03_awlock (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric + 1].lock),
    .i_hp_axi_m_03_awcache(axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric + 1].cache),
    .i_hp_axi_m_03_awprot (axi_ht_dma_transfer_aw[AxiHtDmaPortIdxFabric + 1].prot),
    .i_hp_axi_m_03_awvalid(axi_ht_dma_transfer_aw_valid[AxiHtDmaPortIdxFabric + 1]),
    .o_hp_axi_m_03_awready(axi_ht_dma_transfer_aw_ready[AxiHtDmaPortIdxFabric + 1]),

    .i_hp_axi_m_03_wdata  (axi_ht_dma_transfer_w[AxiHtDmaPortIdxFabric + 1].data),
    .i_hp_axi_m_03_wstrb  (axi_ht_dma_transfer_w[AxiHtDmaPortIdxFabric + 1].strb),
    .i_hp_axi_m_03_wlast  (axi_ht_dma_transfer_w[AxiHtDmaPortIdxFabric + 1].last),
    .i_hp_axi_m_03_wvalid (axi_ht_dma_transfer_w_valid[AxiHtDmaPortIdxFabric + 1]),
    .o_hp_axi_m_03_wready (axi_ht_dma_transfer_w_ready[AxiHtDmaPortIdxFabric + 1]),

    .o_hp_axi_m_03_bid    (axi_ht_dma_transfer_b[AxiHtDmaPortIdxFabric + 1].id),
    .o_hp_axi_m_03_bresp  (axi_ht_dma_transfer_b[AxiHtDmaPortIdxFabric + 1].resp),
    .o_hp_axi_m_03_bvalid (axi_ht_dma_transfer_b_valid[AxiHtDmaPortIdxFabric + 1]),
    .i_hp_axi_m_03_bready (axi_ht_dma_transfer_b_ready[AxiHtDmaPortIdxFabric + 1]),

    .i_hp_axi_m_03_arid   (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric + 1].id),
    .i_hp_axi_m_03_araddr (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric + 1].addr),
    .i_hp_axi_m_03_arlen  (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric + 1].len),
    .i_hp_axi_m_03_arsize (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric + 1].size),
    .i_hp_axi_m_03_arburst(axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric + 1].burst),
    .i_hp_axi_m_03_arlock (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric + 1].lock),
    .i_hp_axi_m_03_arcache(axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric + 1].cache),
    .i_hp_axi_m_03_arprot (axi_ht_dma_transfer_ar[AxiHtDmaPortIdxFabric + 1].prot),
    .i_hp_axi_m_03_arvalid(axi_ht_dma_transfer_ar_valid[AxiHtDmaPortIdxFabric + 1]),
    .o_hp_axi_m_03_arready(axi_ht_dma_transfer_ar_ready[AxiHtDmaPortIdxFabric + 1]),

    .o_hp_axi_m_03_rid    (axi_ht_dma_transfer_r[AxiHtDmaPortIdxFabric + 1].id),
    .o_hp_axi_m_03_rdata  (axi_ht_dma_transfer_r[AxiHtDmaPortIdxFabric + 1].data),
    .o_hp_axi_m_03_rresp  (axi_ht_dma_transfer_r[AxiHtDmaPortIdxFabric + 1].resp),
    .o_hp_axi_m_03_rlast  (axi_ht_dma_transfer_r[AxiHtDmaPortIdxFabric + 1].last),
    .o_hp_axi_m_03_rvalid (axi_ht_dma_transfer_r_valid[AxiHtDmaPortIdxFabric + 1]),
    .i_hp_axi_m_03_rready (axi_ht_dma_transfer_r_ready[AxiHtDmaPortIdxFabric + 1]),
    /////////////////////////////
    // HT Connection to DMC L1 //
    /////////////////////////////
    .o_hp_axi_s_l1_awid   (o_dmc_l1_ht_axi_m_awid),
    .o_hp_axi_s_l1_awaddr (o_dmc_l1_ht_axi_m_awaddr),
    .o_hp_axi_s_l1_awlen  (o_dmc_l1_ht_axi_m_awlen),
    .o_hp_axi_s_l1_awsize (o_dmc_l1_ht_axi_m_awsize),
    .o_hp_axi_s_l1_awburst(o_dmc_l1_ht_axi_m_awburst),
    .o_hp_axi_s_l1_awlock (o_dmc_l1_ht_axi_m_awlock),
    .o_hp_axi_s_l1_awcache(o_dmc_l1_ht_axi_m_awcache),
    .o_hp_axi_s_l1_awprot (o_dmc_l1_ht_axi_m_awprot),
    .o_hp_axi_s_l1_awvalid(o_dmc_l1_ht_axi_m_awvalid),
    .i_hp_axi_s_l1_awready(i_dmc_l1_ht_axi_m_awready),

    .o_hp_axi_s_l1_wdata  (o_dmc_l1_ht_axi_m_wdata),
    .o_hp_axi_s_l1_wstrb  (o_dmc_l1_ht_axi_m_wstrb),
    .o_hp_axi_s_l1_wlast  (o_dmc_l1_ht_axi_m_wlast),
    .o_hp_axi_s_l1_wvalid (o_dmc_l1_ht_axi_m_wvalid),
    .i_hp_axi_s_l1_wready (i_dmc_l1_ht_axi_m_wready),

    .i_hp_axi_s_l1_bid    (i_dmc_l1_ht_axi_m_bid),
    .i_hp_axi_s_l1_bresp  (i_dmc_l1_ht_axi_m_bresp),
    .i_hp_axi_s_l1_bvalid (i_dmc_l1_ht_axi_m_bvalid),
    .o_hp_axi_s_l1_bready (o_dmc_l1_ht_axi_m_bready),

    .o_hp_axi_s_l1_arid   (o_dmc_l1_ht_axi_m_arid),
    .o_hp_axi_s_l1_araddr (o_dmc_l1_ht_axi_m_araddr),
    .o_hp_axi_s_l1_arlen  (o_dmc_l1_ht_axi_m_arlen),
    .o_hp_axi_s_l1_arsize (o_dmc_l1_ht_axi_m_arsize),
    .o_hp_axi_s_l1_arburst(o_dmc_l1_ht_axi_m_arburst),
    .o_hp_axi_s_l1_arlock (o_dmc_l1_ht_axi_m_arlock),
    .o_hp_axi_s_l1_arcache(o_dmc_l1_ht_axi_m_arcache),
    .o_hp_axi_s_l1_arprot (o_dmc_l1_ht_axi_m_arprot),
    .o_hp_axi_s_l1_arvalid(o_dmc_l1_ht_axi_m_arvalid),
    .i_hp_axi_s_l1_arready(i_dmc_l1_ht_axi_m_arready),

    .i_hp_axi_s_l1_rid    (i_dmc_l1_ht_axi_m_rid),
    .i_hp_axi_s_l1_rdata  (i_dmc_l1_ht_axi_m_rdata),
    .i_hp_axi_s_l1_rresp  (i_dmc_l1_ht_axi_m_rresp),
    .i_hp_axi_s_l1_rlast  (i_dmc_l1_ht_axi_m_rlast),
    .i_hp_axi_s_l1_rvalid (i_dmc_l1_ht_axi_m_rvalid),
    .o_hp_axi_s_l1_rready (o_dmc_l1_ht_axi_m_rready),
    //////////////////////////
    // HT Connection to NOC //
    //////////////////////////
    .i_hp_axi_s_nochp_arready(i_noc_ht_axi_m_arready),
    .i_hp_axi_s_nochp_awready(i_noc_ht_axi_m_awready),
    .i_hp_axi_s_nochp_bid    (i_noc_ht_axi_m_bid),
    .i_hp_axi_s_nochp_bresp  (i_noc_ht_axi_m_bresp),
    .i_hp_axi_s_nochp_bvalid (i_noc_ht_axi_m_bvalid),
    .i_hp_axi_s_nochp_rdata  (i_noc_ht_axi_m_rdata),
    .i_hp_axi_s_nochp_rid    (i_noc_ht_axi_m_rid),
    .i_hp_axi_s_nochp_rlast  (i_noc_ht_axi_m_rlast),
    .i_hp_axi_s_nochp_rresp  (i_noc_ht_axi_m_rresp),
    .i_hp_axi_s_nochp_rvalid (i_noc_ht_axi_m_rvalid),
    .i_hp_axi_s_nochp_wready (i_noc_ht_axi_m_wready),
    .o_hp_axi_s_nochp_araddr (o_noc_ht_axi_m_araddr),
    .o_hp_axi_s_nochp_arburst(o_noc_ht_axi_m_arburst),
    .o_hp_axi_s_nochp_arcache(o_noc_ht_axi_m_arcache),
    .o_hp_axi_s_nochp_arid   (o_noc_ht_axi_m_arid),
    .o_hp_axi_s_nochp_arlen  (o_noc_ht_axi_m_arlen),
    .o_hp_axi_s_nochp_arlock (o_noc_ht_axi_m_arlock),
    .o_hp_axi_s_nochp_arprot (o_noc_ht_axi_m_arprot),
    .o_hp_axi_s_nochp_arsize (o_noc_ht_axi_m_arsize),
    .o_hp_axi_s_nochp_arvalid(o_noc_ht_axi_m_arvalid),
    .o_hp_axi_s_nochp_awaddr (o_noc_ht_axi_m_awaddr),
    .o_hp_axi_s_nochp_awburst(o_noc_ht_axi_m_awburst),
    .o_hp_axi_s_nochp_awcache(o_noc_ht_axi_m_awcache),
    .o_hp_axi_s_nochp_awid   (o_noc_ht_axi_m_awid),
    .o_hp_axi_s_nochp_awlen  (o_noc_ht_axi_m_awlen),
    .o_hp_axi_s_nochp_awlock (o_noc_ht_axi_m_awlock),
    .o_hp_axi_s_nochp_awprot (o_noc_ht_axi_m_awprot),
    .o_hp_axi_s_nochp_awsize (o_noc_ht_axi_m_awsize),
    .o_hp_axi_s_nochp_awvalid(o_noc_ht_axi_m_awvalid),
    .o_hp_axi_s_nochp_bready (o_noc_ht_axi_m_bready),
    .o_hp_axi_s_nochp_rready (o_noc_ht_axi_m_rready),
    .o_hp_axi_s_nochp_wdata  (o_noc_ht_axi_m_wdata),
    .o_hp_axi_s_nochp_wlast  (o_noc_ht_axi_m_wlast),
    .o_hp_axi_s_nochp_wstrb  (o_noc_ht_axi_m_wstrb),
    .o_hp_axi_s_nochp_wvalid (o_noc_ht_axi_m_wvalid),
    /////////////////////////////////////
    // LT Connection to Timestamp      //
    /////////////////////////////////////
    .i_lp_axi_m_02_awid   (axi_timelog_aw[AxiTimeLogPortIdxFabric].id),
    .i_lp_axi_m_02_awaddr (axi_timelog_aw[AxiTimeLogPortIdxFabric].addr),
    .i_lp_axi_m_02_awlen  (axi_timelog_aw[AxiTimeLogPortIdxFabric].len),
    .i_lp_axi_m_02_awsize (axi_timelog_aw[AxiTimeLogPortIdxFabric].size),
    .i_lp_axi_m_02_awburst(axi_timelog_aw[AxiTimeLogPortIdxFabric].burst),
    .i_lp_axi_m_02_awlock (axi_timelog_aw[AxiTimeLogPortIdxFabric].lock),
    .i_lp_axi_m_02_awcache(axi_timelog_aw[AxiTimeLogPortIdxFabric].cache),
    .i_lp_axi_m_02_awprot (axi_timelog_aw[AxiTimeLogPortIdxFabric].prot),
    .i_lp_axi_m_02_awvalid(axi_timelog_aw_valid[AxiTimeLogPortIdxFabric]),
    .o_lp_axi_m_02_awready(axi_timelog_aw_ready[AxiTimeLogPortIdxFabric]),

    .i_lp_axi_m_02_wdata  (axi_timelog_w[AxiTimeLogPortIdxFabric].data),
    .i_lp_axi_m_02_wstrb  (axi_timelog_w[AxiTimeLogPortIdxFabric].strb),
    .i_lp_axi_m_02_wlast  (axi_timelog_w[AxiTimeLogPortIdxFabric].last),
    .i_lp_axi_m_02_wvalid (axi_timelog_w_valid[AxiTimeLogPortIdxFabric]),
    .o_lp_axi_m_02_wready (axi_timelog_w_ready[AxiTimeLogPortIdxFabric]),

    .o_lp_axi_m_02_bid    (axi_timelog_b[AxiTimeLogPortIdxFabric].id),
    .o_lp_axi_m_02_bresp  (axi_timelog_b[AxiTimeLogPortIdxFabric].resp),
    .o_lp_axi_m_02_bvalid (axi_timelog_b_valid[AxiTimeLogPortIdxFabric]),
    .i_lp_axi_m_02_bready (axi_timelog_b_ready[AxiTimeLogPortIdxFabric]),

    .i_lp_axi_m_02_arid   (axi_timelog_ar[AxiTimeLogPortIdxFabric].id),
    .i_lp_axi_m_02_araddr (axi_timelog_ar[AxiTimeLogPortIdxFabric].addr),
    .i_lp_axi_m_02_arlen  (axi_timelog_ar[AxiTimeLogPortIdxFabric].len),
    .i_lp_axi_m_02_arsize (axi_timelog_ar[AxiTimeLogPortIdxFabric].size),
    .i_lp_axi_m_02_arburst(axi_timelog_ar[AxiTimeLogPortIdxFabric].burst),
    .i_lp_axi_m_02_arlock (axi_timelog_ar[AxiTimeLogPortIdxFabric].lock),
    .i_lp_axi_m_02_arcache(axi_timelog_ar[AxiTimeLogPortIdxFabric].cache),
    .i_lp_axi_m_02_arprot (axi_timelog_ar[AxiTimeLogPortIdxFabric].prot),
    .i_lp_axi_m_02_arvalid(axi_timelog_ar_valid[AxiTimeLogPortIdxFabric]),
    .o_lp_axi_m_02_arready(axi_timelog_ar_ready[AxiTimeLogPortIdxFabric]),

    .o_lp_axi_m_02_rid    (axi_timelog_r[AxiTimeLogPortIdxFabric].id),
    .o_lp_axi_m_02_rdata  (axi_timelog_r[AxiTimeLogPortIdxFabric].data),
    .o_lp_axi_m_02_rresp  (axi_timelog_r[AxiTimeLogPortIdxFabric].resp),
    .o_lp_axi_m_02_rlast  (axi_timelog_r[AxiTimeLogPortIdxFabric].last),
    .o_lp_axi_m_02_rvalid (axi_timelog_r_valid[AxiTimeLogPortIdxFabric]),
    .i_lp_axi_m_02_rready (axi_timelog_r_ready[AxiTimeLogPortIdxFabric]),
    ///////////////////////////////////
    // LT Connection from LT DMA ATU //
    ///////////////////////////////////
    .i_lp_axi_m_03_awid   (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxFabric].id),
    .i_lp_axi_m_03_awaddr (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxFabric].addr),
    .i_lp_axi_m_03_awlen  (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxFabric].len),
    .i_lp_axi_m_03_awsize (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxFabric].size),
    .i_lp_axi_m_03_awburst(axi_lt_dma_transfer_aw[AxiLtDmaPortIdxFabric].burst),
    .i_lp_axi_m_03_awlock (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxFabric].lock),
    .i_lp_axi_m_03_awcache(axi_lt_dma_transfer_aw[AxiLtDmaPortIdxFabric].cache),
    .i_lp_axi_m_03_awprot (axi_lt_dma_transfer_aw[AxiLtDmaPortIdxFabric].prot),
    .i_lp_axi_m_03_awvalid(axi_lt_dma_transfer_aw_valid[AxiLtDmaPortIdxFabric]),
    .o_lp_axi_m_03_awready(axi_lt_dma_transfer_aw_ready[AxiLtDmaPortIdxFabric]),

    .i_lp_axi_m_03_wdata  (axi_lt_dma_transfer_w[AxiLtDmaPortIdxFabric].data),
    .i_lp_axi_m_03_wstrb  (axi_lt_dma_transfer_w[AxiLtDmaPortIdxFabric].strb),
    .i_lp_axi_m_03_wlast  (axi_lt_dma_transfer_w[AxiLtDmaPortIdxFabric].last),
    .i_lp_axi_m_03_wvalid (axi_lt_dma_transfer_w_valid[AxiLtDmaPortIdxFabric]),
    .o_lp_axi_m_03_wready (axi_lt_dma_transfer_w_ready[AxiLtDmaPortIdxFabric]),

    .o_lp_axi_m_03_bid    (axi_lt_dma_transfer_b[AxiLtDmaPortIdxFabric].id),
    .o_lp_axi_m_03_bresp  (axi_lt_dma_transfer_b[AxiLtDmaPortIdxFabric].resp),
    .o_lp_axi_m_03_bvalid (axi_lt_dma_transfer_b_valid[AxiLtDmaPortIdxFabric]),
    .i_lp_axi_m_03_bready (axi_lt_dma_transfer_b_ready[AxiLtDmaPortIdxFabric]),

    .i_lp_axi_m_03_arid   (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxFabric].id),
    .i_lp_axi_m_03_araddr (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxFabric].addr),
    .i_lp_axi_m_03_arlen  (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxFabric].len),
    .i_lp_axi_m_03_arsize (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxFabric].size),
    .i_lp_axi_m_03_arburst(axi_lt_dma_transfer_ar[AxiLtDmaPortIdxFabric].burst),
    .i_lp_axi_m_03_arlock (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxFabric].lock),
    .i_lp_axi_m_03_arcache(axi_lt_dma_transfer_ar[AxiLtDmaPortIdxFabric].cache),
    .i_lp_axi_m_03_arprot (axi_lt_dma_transfer_ar[AxiLtDmaPortIdxFabric].prot),
    .i_lp_axi_m_03_arvalid(axi_lt_dma_transfer_ar_valid[AxiLtDmaPortIdxFabric]),
    .o_lp_axi_m_03_arready(axi_lt_dma_transfer_ar_ready[AxiLtDmaPortIdxFabric]),

    .o_lp_axi_m_03_rid    (axi_lt_dma_transfer_r[AxiLtDmaPortIdxFabric].id),
    .o_lp_axi_m_03_rdata  (axi_lt_dma_transfer_r[AxiLtDmaPortIdxFabric].data),
    .o_lp_axi_m_03_rresp  (axi_lt_dma_transfer_r[AxiLtDmaPortIdxFabric].resp),
    .o_lp_axi_m_03_rlast  (axi_lt_dma_transfer_r[AxiLtDmaPortIdxFabric].last),
    .o_lp_axi_m_03_rvalid (axi_lt_dma_transfer_r_valid[AxiLtDmaPortIdxFabric]),
    .i_lp_axi_m_03_rready (axi_lt_dma_transfer_r_ready[AxiLtDmaPortIdxFabric]),
    //////////////////////////
    // LT Connection to SPM //
    //////////////////////////
    .o_lp_axi_s_spm_awid   (axi_lt_spm_aw.id),
    .o_lp_axi_s_spm_awaddr (axi_lt_spm_aw.addr),
    .o_lp_axi_s_spm_awsize (axi_lt_spm_aw.size),
    .o_lp_axi_s_spm_awlen  (axi_lt_spm_aw.len),
    .o_lp_axi_s_spm_awburst(axi_lt_spm_aw.burst),
    .o_lp_axi_s_spm_awlock (axi_lt_spm_aw.lock),
    .o_lp_axi_s_spm_awcache(axi_lt_spm_aw.cache),
    .o_lp_axi_s_spm_awprot (axi_lt_spm_aw.prot),
    .o_lp_axi_s_spm_awvalid(axi_lt_spm_aw_valid),
    .i_lp_axi_s_spm_awready(axi_lt_spm_aw_ready),

    .o_lp_axi_s_spm_wdata  (axi_lt_spm_w.data),
    .o_lp_axi_s_spm_wstrb  (axi_lt_spm_w.strb),
    .o_lp_axi_s_spm_wlast  (axi_lt_spm_w.last),
    .o_lp_axi_s_spm_wvalid (axi_lt_spm_w_valid),
    .i_lp_axi_s_spm_wready (axi_lt_spm_w_ready),

    .i_lp_axi_s_spm_bid    (axi_lt_spm_b.id),
    .i_lp_axi_s_spm_bresp  (axi_lt_spm_b.resp),
    .i_lp_axi_s_spm_bvalid (axi_lt_spm_b_valid),
    .o_lp_axi_s_spm_bready (axi_lt_spm_b_ready),

    .o_lp_axi_s_spm_arid   (axi_lt_spm_ar.id),
    .o_lp_axi_s_spm_araddr (axi_lt_spm_ar.addr),
    .o_lp_axi_s_spm_arlen  (axi_lt_spm_ar.len),
    .o_lp_axi_s_spm_arsize (axi_lt_spm_ar.size),
    .o_lp_axi_s_spm_arburst(axi_lt_spm_ar.burst),
    .o_lp_axi_s_spm_arlock (axi_lt_spm_ar.lock),
    .o_lp_axi_s_spm_arcache(axi_lt_spm_ar.cache),
    .o_lp_axi_s_spm_arprot (axi_lt_spm_ar.prot),
    .o_lp_axi_s_spm_arvalid(axi_lt_spm_ar_valid),
    .i_lp_axi_s_spm_arready(axi_lt_spm_ar_ready),

    .i_lp_axi_s_spm_rid    (axi_lt_spm_r.id),
    .i_lp_axi_s_spm_rdata  (axi_lt_spm_r.data),
    .i_lp_axi_s_spm_rresp  (axi_lt_spm_r.resp),
    .i_lp_axi_s_spm_rlast  (axi_lt_spm_r.last),
    .i_lp_axi_s_spm_rvalid (axi_lt_spm_r_valid),
    .o_lp_axi_s_spm_rready (axi_lt_spm_r_ready),
    //////////////////////////
    // LT Connection to NOC //
    //////////////////////////
    .i_lp_axi_s_noclp_arready(i_noc_lt_axi_m_arready),
    .i_lp_axi_s_noclp_awready(i_noc_lt_axi_m_awready),
    .i_lp_axi_s_noclp_bid    (i_noc_lt_axi_m_bid),
    .i_lp_axi_s_noclp_bresp  (i_noc_lt_axi_m_bresp),
    .i_lp_axi_s_noclp_bvalid (i_noc_lt_axi_m_bvalid),
    .i_lp_axi_s_noclp_rdata  (i_noc_lt_axi_m_rdata),
    .i_lp_axi_s_noclp_rid    (i_noc_lt_axi_m_rid),
    .i_lp_axi_s_noclp_rlast  (i_noc_lt_axi_m_rlast),
    .i_lp_axi_s_noclp_rresp  (i_noc_lt_axi_m_rresp),
    .i_lp_axi_s_noclp_rvalid (i_noc_lt_axi_m_rvalid),
    .i_lp_axi_s_noclp_wready (i_noc_lt_axi_m_wready),
    .o_lp_axi_s_noclp_araddr (o_noc_lt_axi_m_araddr),
    .o_lp_axi_s_noclp_arburst(o_noc_lt_axi_m_arburst),
    .o_lp_axi_s_noclp_arcache(o_noc_lt_axi_m_arcache),
    .o_lp_axi_s_noclp_arid   (o_noc_lt_axi_m_arid),
    .o_lp_axi_s_noclp_arlen  (o_noc_lt_axi_m_arlen),
    .o_lp_axi_s_noclp_arlock (o_noc_lt_axi_m_arlock),
    .o_lp_axi_s_noclp_arprot (o_noc_lt_axi_m_arprot),
    .o_lp_axi_s_noclp_arsize (o_noc_lt_axi_m_arsize),
    .o_lp_axi_s_noclp_arvalid(o_noc_lt_axi_m_arvalid),
    .o_lp_axi_s_noclp_awaddr (o_noc_lt_axi_m_awaddr),
    .o_lp_axi_s_noclp_awburst(o_noc_lt_axi_m_awburst),
    .o_lp_axi_s_noclp_awcache(o_noc_lt_axi_m_awcache),
    .o_lp_axi_s_noclp_awid   (o_noc_lt_axi_m_awid),
    .o_lp_axi_s_noclp_awlen  (o_noc_lt_axi_m_awlen),
    .o_lp_axi_s_noclp_awlock (o_noc_lt_axi_m_awlock),
    .o_lp_axi_s_noclp_awprot (o_noc_lt_axi_m_awprot),
    .o_lp_axi_s_noclp_awsize (o_noc_lt_axi_m_awsize),
    .o_lp_axi_s_noclp_awvalid(o_noc_lt_axi_m_awvalid),
    .o_lp_axi_s_noclp_bready (o_noc_lt_axi_m_bready),
    .o_lp_axi_s_noclp_rready (o_noc_lt_axi_m_rready),
    .o_lp_axi_s_noclp_wdata  (o_noc_lt_axi_m_wdata),
    .o_lp_axi_s_noclp_wlast  (o_noc_lt_axi_m_wlast),
    .o_lp_axi_s_noclp_wstrb  (o_noc_lt_axi_m_wstrb),
    .o_lp_axi_s_noclp_wvalid (o_noc_lt_axi_m_wvalid),
    ////////////////////////////
    // LT Connection From NOC //
    ////////////////////////////
    .i_noc_lp_s_demux_axi_m_01_araddr (i_noc_lt_axi_s_araddr),
    .i_noc_lp_s_demux_axi_m_01_arburst(i_noc_lt_axi_s_arburst),
    .i_noc_lp_s_demux_axi_m_01_arcache(i_noc_lt_axi_s_arcache),
    .i_noc_lp_s_demux_axi_m_01_arid   (i_noc_lt_axi_s_arid),
    .i_noc_lp_s_demux_axi_m_01_arlen  (i_noc_lt_axi_s_arlen),
    .i_noc_lp_s_demux_axi_m_01_arlock (i_noc_lt_axi_s_arlock),
    .i_noc_lp_s_demux_axi_m_01_arprot (i_noc_lt_axi_s_arprot),
    .i_noc_lp_s_demux_axi_m_01_arsize (i_noc_lt_axi_s_arsize),
    .i_noc_lp_s_demux_axi_m_01_arvalid(i_noc_lt_axi_s_arvalid),
    .i_noc_lp_s_demux_axi_m_01_awaddr (i_noc_lt_axi_s_awaddr),
    .i_noc_lp_s_demux_axi_m_01_awburst(i_noc_lt_axi_s_awburst),
    .i_noc_lp_s_demux_axi_m_01_awcache(i_noc_lt_axi_s_awcache),
    .i_noc_lp_s_demux_axi_m_01_awid   (i_noc_lt_axi_s_awid),
    .i_noc_lp_s_demux_axi_m_01_awlen  (i_noc_lt_axi_s_awlen),
    .i_noc_lp_s_demux_axi_m_01_awlock (i_noc_lt_axi_s_awlock),
    .i_noc_lp_s_demux_axi_m_01_awprot (i_noc_lt_axi_s_awprot),
    .i_noc_lp_s_demux_axi_m_01_awsize (i_noc_lt_axi_s_awsize),
    .i_noc_lp_s_demux_axi_m_01_awvalid(i_noc_lt_axi_s_awvalid),
    .i_noc_lp_s_demux_axi_m_01_bready (i_noc_lt_axi_s_bready),
    .i_noc_lp_s_demux_axi_m_01_rready (i_noc_lt_axi_s_rready),
    .i_noc_lp_s_demux_axi_m_01_wdata  (i_noc_lt_axi_s_wdata),
    .i_noc_lp_s_demux_axi_m_01_wlast  (i_noc_lt_axi_s_wlast),
    .i_noc_lp_s_demux_axi_m_01_wstrb  (i_noc_lt_axi_s_wstrb),
    .i_noc_lp_s_demux_axi_m_01_wvalid (i_noc_lt_axi_s_wvalid),
    .o_noc_lp_s_demux_axi_m_01_arready(o_noc_lt_axi_s_arready),
    .o_noc_lp_s_demux_axi_m_01_awready(o_noc_lt_axi_s_awready),
    .o_noc_lp_s_demux_axi_m_01_bid    (o_noc_lt_axi_s_bid),
    .o_noc_lp_s_demux_axi_m_01_bresp  (o_noc_lt_axi_s_bresp),
    .o_noc_lp_s_demux_axi_m_01_bvalid (o_noc_lt_axi_s_bvalid),
    .o_noc_lp_s_demux_axi_m_01_rdata  (o_noc_lt_axi_s_rdata),
    .o_noc_lp_s_demux_axi_m_01_rid    (o_noc_lt_axi_s_rid),
    .o_noc_lp_s_demux_axi_m_01_rlast  (o_noc_lt_axi_s_rlast),
    .o_noc_lp_s_demux_axi_m_01_rresp  (o_noc_lt_axi_s_rresp),
    .o_noc_lp_s_demux_axi_m_01_rvalid (o_noc_lt_axi_s_rvalid),
    .o_noc_lp_s_demux_axi_m_01_wready (o_noc_lt_axi_s_wready),
    ////////
    //
    ////////
    .i_lp2hp_arresize_pp(1'b1),
    .i_lp2hp_awresize_pp(1'b1),
    .i_low_power_en(reg2hw.low_power_control.lp_en),
    .i_low_power_idle_delay(reg2hw.low_power_control.idle_delay)
  );

  /////////////////////////////////
  // Shared Performance Counters //
  /////////////////////////////////

    // Shared Performance Counter routing signals
    logic [aic_infra_pkg::AIC_INFRA_PERF_CNT_NUM - 1 : 0][aic_infra_pkg::AIC_INFRA_PERF_CNT_WIDTH - 1 : 0]    gen_perf_counters_q;
    logic [aic_infra_pkg::AIC_INFRA_PERF_CNT_NUM - 1 : 0]                                                     gen_perf_counters_de;
    logic [aic_infra_pkg::AIC_INFRA_PERF_CNT_NUM - 1 : 0][aic_infra_pkg::AIC_INFRA_PERF_CNT_WIDTH - 1 : 0]    gen_perf_counters_d;
    logic [aic_infra_pkg::AIC_INFRA_PERF_CNT_NUM - 1 : 0][aic_infra_pkg::AIC_INFRA_PERF_CNT_MODE - 1 : 0]     inc_cnt;

    // Mode-0 incrementer signals
    logic m_mvmexe_busy;
    logic m_mvmexe_stall;
    logic m_mvmprg_busy;
    logic m_mvmprg_stall;
    logic m_iau_busy;
    logic m_iau_stall;
    logic m_dpu_busy;
    logic m_dpu_stall;
    logic d_dwpu_busy;
    logic d_dwpu_stall;
    logic d_iau_busy;
    logic d_iau_stall;
    logic d_dpu_busy;
    logic d_dpu_stall;
    logic total_cycles;

    // Convert inputs to struct to be able read the members easily
    aic_common_pkg::aic_dev_obs_t mvm_exe_obs;
    always_comb mvm_exe_obs   = aic_common_pkg::aic_dev_obs_t'(mvm_exe_obs_q);
    aic_common_pkg::aic_dev_obs_t mvm_prg_obs;
    always_comb mvm_prg_obs   = aic_common_pkg::aic_dev_obs_t'(mvm_prg_obs_q);
    aic_common_pkg::aic_dev_obs_t m_iau_obs;
    always_comb m_iau_obs     = aic_common_pkg::aic_dev_obs_t'(m_iau_obs_q);
    aic_common_pkg::aic_dev_obs_t m_dpu_obs;
    always_comb m_dpu_obs     = aic_common_pkg::aic_dev_obs_t'(m_dpu_obs_q);
    aic_common_pkg::aic_dev_obs_t dwpu_obs;
    always_comb dwpu_obs      = aic_common_pkg::aic_dev_obs_t'(dwpu_obs_q);
    aic_common_pkg::aic_dev_obs_t d_iau_obs;
    always_comb d_iau_obs     = aic_common_pkg::aic_dev_obs_t'(d_iau_obs_q);
    aic_common_pkg::aic_dev_obs_t d_dpu_obs;
    always_comb d_dpu_obs     = aic_common_pkg::aic_dev_obs_t'(d_dpu_obs_q);
    aic_common_pkg::dmc_obs_t     dmc_obs;
    always_comb dmc_obs       = aic_common_pkg::dmc_obs_t'(dmc_obs_q);
    aic_common_pkg::aic_dev_obs_t m_ifd_0_obs;
    always_comb m_ifd_0_obs   = dmc_obs.m_ifd0_obs;
    aic_common_pkg::aic_dev_obs_t m_ifd_1_obs;
    always_comb m_ifd_1_obs   = dmc_obs.m_ifd1_obs;
    aic_common_pkg::aic_dev_obs_t m_ifd_2_obs;
    always_comb m_ifd_2_obs   = dmc_obs.m_ifd2_obs;
    aic_common_pkg::aic_dev_obs_t m_ifd_w_obs;
    always_comb m_ifd_w_obs   = dmc_obs.m_ifdw_obs;
    aic_common_pkg::aic_dev_obs_t m_odr_obs;
    always_comb m_odr_obs     = dmc_obs.m_odr_obs;
    aic_common_pkg::aic_dev_obs_t d_ifd_0_obs;
    always_comb d_ifd_0_obs   = dmc_obs.d_ifd0_obs;
    aic_common_pkg::aic_dev_obs_t d_ifd_1_obs;
    always_comb d_ifd_1_obs   = dmc_obs.d_ifd1_obs;
    aic_common_pkg::aic_dev_obs_t d_odr_obs;
    always_comb d_odr_obs     = dmc_obs.d_odr_obs;

    always_comb begin
      // Generation of Mode-0 incrementers
      m_mvmexe_busy   = mvm_exe_obs.state == cmdblock_pkg::exec;
      m_mvmexe_stall  = mvm_exe_obs.token_stall  || mvm_exe_obs.dp_instr_stall ||
                        mvm_exe_obs.dp_cmd_stall || mvm_exe_obs.dp_in0_stall   ||
                        mvm_exe_obs.dp_in1_stall || mvm_exe_obs.dp_out_stall;

      m_mvmprg_busy   = mvm_prg_obs.state == cmdblock_pkg::exec;
      m_mvmprg_stall  = mvm_prg_obs.token_stall  || mvm_prg_obs.dp_instr_stall ||
                        mvm_prg_obs.dp_cmd_stall || mvm_prg_obs.dp_in0_stall   ||
                        mvm_prg_obs.dp_in1_stall || mvm_prg_obs.dp_out_stall;

      m_iau_busy      = m_iau_obs.state == cmdblock_pkg::exec;
      m_iau_stall     = m_iau_obs.token_stall  || m_iau_obs.dp_instr_stall ||
                        m_iau_obs.dp_cmd_stall || m_iau_obs.dp_in0_stall   ||
                        m_iau_obs.dp_in1_stall || m_iau_obs.dp_out_stall;

      m_dpu_busy      = m_dpu_obs.state == cmdblock_pkg::exec;
      m_dpu_stall     = m_dpu_obs.token_stall  || m_dpu_obs.dp_instr_stall ||
                        m_dpu_obs.dp_cmd_stall || m_dpu_obs.dp_in0_stall   ||
                        m_dpu_obs.dp_in1_stall || m_dpu_obs.dp_out_stall;

      d_dwpu_busy     = dwpu_obs.state == cmdblock_pkg::exec;
      d_dwpu_stall    = dwpu_obs.token_stall  || dwpu_obs.dp_instr_stall ||
                        dwpu_obs.dp_cmd_stall || dwpu_obs.dp_in0_stall   ||
                        dwpu_obs.dp_in1_stall || dwpu_obs.dp_out_stall;

      d_iau_busy      = d_iau_obs.state == cmdblock_pkg::exec;
      d_iau_stall     = d_iau_obs.token_stall  || d_iau_obs.dp_instr_stall ||
                        d_iau_obs.dp_cmd_stall || d_iau_obs.dp_in0_stall   ||
                        d_iau_obs.dp_in1_stall || d_iau_obs.dp_out_stall;

      d_dpu_busy      = d_dpu_obs.state == cmdblock_pkg::exec;
      d_dpu_stall     = d_dpu_obs.token_stall  || d_dpu_obs.dp_instr_stall ||
                        d_dpu_obs.dp_cmd_stall || d_dpu_obs.dp_in0_stall   ||
                        d_dpu_obs.dp_in1_stall || d_dpu_obs.dp_out_stall;

      // Total cycles needs to count regardless of any other signal when the
      // counter is enabled.
      total_cycles    = 1'b1;

    end

    always_comb inc_cnt = {
      // Generic Performance Counter [0] Incrementers
      m_mvmexe_busy,
      m_ifd_0_obs.token_stall,
      mvm_exe_obs.token_stall,
      dwpu_obs.token_stall,
      // Generic Performance Counter [1] Incrementers
      m_mvmexe_stall,
      m_ifd_1_obs.token_stall,
      mvm_exe_obs.dp_cmd_stall,
      dwpu_obs.dp_cmd_stall,
      // Generic Performance Counter [2] Incrementers
      m_mvmprg_busy,
      m_ifd_2_obs.token_stall,
      mvm_exe_obs.dp_instr_stall,
      dwpu_obs.dp_instr_stall,
      // Generic Performance Counter [3] Incrementers
      m_mvmprg_stall,
      m_ifd_w_obs.token_stall,
      (mvm_exe_obs.dp_in0_stall || mvm_exe_obs.dp_in1_stall),
      (dwpu_obs.dp_in0_stall || dwpu_obs.dp_in1_stall),
      // Generic Performance Counter [4] Incrementers
      m_iau_busy,
      m_odr_obs.token_stall,
      mvm_exe_obs.dp_out_stall,
      dwpu_obs.dp_out_stall,
      // Generic Performance Counter [5] Incrementers
      m_iau_stall,
      d_ifd_0_obs.token_stall,
      m_iau_obs.token_stall,
      d_iau_obs.token_stall,
      // Generic Performance Counter [6] Incrementers
      m_dpu_busy,
      d_ifd_1_obs.token_stall,
      m_iau_obs.dp_cmd_stall,
      d_iau_obs.dp_cmd_stall,
      // Generic Performance Counter [7] Incrementers
      m_dpu_stall,
      d_odr_obs.token_stall,
      m_iau_obs.dp_instr_stall,
      d_iau_obs.dp_instr_stall,
      // Generic Performance Counter [8] Incrementers
      d_dwpu_busy,
      mvm_exe_obs.token_stall,
      (m_iau_obs.dp_in0_stall || m_iau_obs.dp_in1_stall),
      (d_iau_obs.dp_in0_stall || d_iau_obs.dp_in1_stall),
      // Generic Performance Counter [9] Incrementers
      d_dwpu_stall,
      mvm_prg_obs.token_stall,
      m_iau_obs.dp_out_stall,
      d_iau_obs.dp_out_stall,
      // Generic Performance Counter [10] Incrementers
      d_iau_busy,
      ht_dma_obs[0].token_stall,
      m_dpu_obs.token_stall,
      d_dpu_obs.token_stall,
      // Generic Performance Counter [11] Incrementers
      d_iau_stall,
      ht_dma_obs[1].token_stall,
      m_dpu_obs.dp_cmd_stall,
      d_dpu_obs.dp_cmd_stall,
      // Generic Performance Counter [12] Incrementers
      d_dpu_busy,
      1'b0,
      m_dpu_obs.dp_instr_stall,
      d_dpu_obs.dp_instr_stall,
      // Generic Performance Counter [13] Incrementers
      d_dpu_stall,
      1'b0,
      (m_dpu_obs.dp_in0_stall || m_dpu_obs.dp_in1_stall),
      (d_dpu_obs.dp_in0_stall || d_dpu_obs.dp_in1_stall),
      // Generic Performance Counter [14] Incrementers
      total_cycles,
      1'b0,
      m_dpu_obs.dp_out_stall,
      d_dpu_obs.dp_out_stall,
      // Generic Performance Counter [15] Incrementers
      1'b0,
      1'b0,
      1'b0,
      1'b0
    };

    // Conversion between array of struc members to multi-dimensinal array
    // to make it easy to connect gen_perf_counter IOs.
    always_comb begin
      for(int idx = 0; idx < aic_infra_pkg::AIC_INFRA_PERF_CNT_NUM; idx++) begin
        gen_perf_counters_q[idx]          = reg2hw.gen_perf_counters[idx].q;
        hw2reg.gen_perf_counters[idx].d   = gen_perf_counters_d[idx];
        hw2reg.gen_perf_counters[idx].de  = gen_perf_counters_de[idx];
      end
    end

    // Shared Performance Counter instantiation
    gen_perf_counter #(
        .NUM_COUNTER    (aic_infra_pkg::AIC_INFRA_PERF_CNT_NUM),
        .COUNTER_WIDTH  (aic_infra_pkg::AIC_INFRA_PERF_CNT_WIDTH),
        .NUM_MODE       (aic_infra_pkg::AIC_INFRA_PERF_CNT_MODE)
    ) u_gen_perf_counter (
        // Clock and Reset
        .i_clk        (i_clk),
        .i_rst_n      (i_rst_n),

        // Inputs
        .i_mode_cnt   (reg2hw.perf_cnt_mode.q),
        .i_in_cnt     (gen_perf_counters_q),
        .i_en_cnt     (reg2hw.perf_ctrl.q),
        .i_inc_cnt    (inc_cnt),

        // Outputs
        .o_wen_cnt    (gen_perf_counters_de),
        .o_out_cnt    (gen_perf_counters_d)
    );

endmodule
