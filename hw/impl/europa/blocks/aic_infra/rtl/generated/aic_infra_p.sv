
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//

module aic_infra_p #(
  localparam int unsigned RvvPortSizeWidth = $clog2(cva6v_ai_core_pkg::MemPortBeWidth)
) (
  //-------------------------------
  // interface signals
  //-------------------------------

  //-------------------------------
  // wrapper io
  //-------------------------------
  input  wire   i_clk,
  input  wire  i_rst_n,
  input  logic [aic_common_pkg::AIC_CID_WIDTH-1:0] i_cid,
  input logic  i_inter_core_sync,
  input logic i_thermal_warning_async,
  output logic [4:0] o_reserved,
  input logic [4:0] i_reserved,
  input logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_mvm_exe_obs,
  input logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_mvm_prg_obs,
  input logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_m_iau_obs,
  input logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_m_dpu_obs,
  input logic [aic_common_pkg::AIC_TU_OBS_DW-1:0] i_tu_obs,
  input logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_dwpu_obs,
  input logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_d_iau_obs,
  input logic [aic_common_pkg::AIC_DEV_OBS_DW-1:0] i_d_dpu_obs,
  input logic [aic_common_pkg::AIC_DMC_OBS_DW-1:0] i_dmc_obs,
  output logic [aic_common_pkg::AIC_OBS_DW-1:0] o_aic_obs,
  input logic [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] i_dmc_ts_start,
  input logic [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] i_dmc_ts_end,
  input logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] i_did_ts_start,
  input logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] i_did_ts_end,
  input logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] i_mid_ts_start,
  input logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] i_mid_ts_end,
  input logic [dmc_pkg::DMC_NR_IFDS_ODRS-1:0] i_dmc_acd_sync,
  input logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] i_did_acd_sync,
  input logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] i_mid_acd_sync,
  input logic [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_cva6v_boot_addr,
  input logic  i_cva6v_debug_req_async,
  input logic  i_cva6v_debug_rst_halt_req_async,
  output logic  o_cva6v_debug_stop_time_async,
  output logic  o_cva6v_hart_unavail_async,
  output logic  o_cva6v_hart_under_reset_async,
  input logic  i_mtip_async,
  input logic  i_msip_async,
  output logic  o_rvv_0_req_valid,
  input logic  i_rvv_0_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_0_req_addr,
  output logic  o_rvv_0_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_0_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_0_req_wdata,
  input logic  i_rvv_0_res_valid,
  input logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_0_res_rdata,
  input logic  i_rvv_0_res_err,
  output logic  o_rvv_1_req_valid,
  input logic  i_rvv_1_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_1_req_addr,
  output logic  o_rvv_1_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_1_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_1_req_wdata,
  input logic  i_rvv_1_res_valid,
  input logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_1_res_rdata,
  input logic  i_rvv_1_res_err,
  output logic  o_rvv_2_req_valid,
  input logic  i_rvv_2_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_2_req_addr,
  output logic  o_rvv_2_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_2_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_2_req_wdata,
  input logic  i_rvv_2_res_valid,
  input logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_2_res_rdata,
  input logic  i_rvv_2_res_err,
  output logic  o_rvv_3_req_valid,
  input logic  i_rvv_3_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_3_req_addr,
  output logic  o_rvv_3_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_3_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_3_req_wdata,
  input logic  i_rvv_3_res_valid,
  input logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_3_res_rdata,
  input logic  i_rvv_3_res_err,
  output logic  o_rvv_4_req_valid,
  input logic  i_rvv_4_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_4_req_addr,
  output logic  o_rvv_4_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_4_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_4_req_wdata,
  input logic  i_rvv_4_res_valid,
  input logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_4_res_rdata,
  input logic  i_rvv_4_res_err,
  output logic  o_rvv_5_req_valid,
  input logic  i_rvv_5_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_5_req_addr,
  output logic  o_rvv_5_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_5_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_5_req_wdata,
  input logic  i_rvv_5_res_valid,
  input logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_5_res_rdata,
  input logic  i_rvv_5_res_err,
  output logic  o_rvv_6_req_valid,
  input logic  i_rvv_6_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_6_req_addr,
  output logic  o_rvv_6_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_6_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_6_req_wdata,
  input logic  i_rvv_6_res_valid,
  input logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_6_res_rdata,
  input logic  i_rvv_6_res_err,
  output logic  o_rvv_7_req_valid,
  input logic  i_rvv_7_req_ready,
  output logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] o_rvv_7_req_addr,
  output logic  o_rvv_7_req_we,
  output logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] o_rvv_7_req_be,
  output logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_7_req_wdata,
  input logic  i_rvv_7_res_valid,
  input logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_7_res_rdata,
  input logic  i_rvv_7_res_err,
  input logic [dmc_pkg::DMC_IRQ_W-1:0] i_irq_dmc,
  input logic [aic_mid_pkg::NUM_IRQS-1:0] i_irq_aic_mid,
  input logic [2:0] i_irq_aic_did,
  input logic [1:0] i_sram_mcs,
  input logic  i_sram_mcsw,
  input logic  i_sram_ret,
  input logic  i_sram_pde,
  input logic [2:0] i_sram_adme,
  output logic  o_sram_prn,

  //-------------------------------
  // protocol ports
  //-------------------------------
  //-------------------------------
  // OCPL o_tok_prod_ocpl_m
  //-------------------------------
  output chip_pkg::chip_ocpl_token_addr_t o_tok_prod_ocpl_m_maddr,
  output logic o_tok_prod_ocpl_m_mcmd,
  output chip_pkg::chip_ocpl_token_data_t o_tok_prod_ocpl_m_mdata,
  //-------------------------------
  // OCPL i_tok_prod_ocpl_m
  //-------------------------------
  input logic i_tok_prod_ocpl_m_scmdaccept,
  //-------------------------------
  // OCPL i_tok_cons_ocpl_s
  //-------------------------------
  input chip_pkg::chip_ocpl_token_addr_t i_tok_cons_ocpl_s_maddr,
  input logic i_tok_cons_ocpl_s_mcmd,
  input chip_pkg::chip_ocpl_token_data_t i_tok_cons_ocpl_s_mdata,
  //-------------------------------
  // OCPL o_tok_cons_ocpl_s
  //-------------------------------
  output logic o_tok_cons_ocpl_s_scmdaccept,
  //-------------------------------
  // Token i_m_ifd0_tok_prod
  //-------------------------------
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifd0_tok_prod_rdy,
  input logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifd0_tok_prod_vld,
  //-------------------------------
  // Token o_m_ifd0_tok_cons
  //-------------------------------
  input logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifd0_tok_cons_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifd0_tok_cons_vld,
  //-------------------------------
  // Token i_m_ifd1_tok_prod
  //-------------------------------
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifd1_tok_prod_rdy,
  input logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifd1_tok_prod_vld,
  //-------------------------------
  // Token o_m_ifd1_tok_cons
  //-------------------------------
  input logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifd1_tok_cons_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifd1_tok_cons_vld,
  //-------------------------------
  // Token i_m_ifd2_tok_prod
  //-------------------------------
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifd2_tok_prod_rdy,
  input logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifd2_tok_prod_vld,
  //-------------------------------
  // Token o_m_ifd2_tok_cons
  //-------------------------------
  input logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifd2_tok_cons_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifd2_tok_cons_vld,
  //-------------------------------
  // Token i_m_ifdw_tok_prod
  //-------------------------------
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifdw_tok_prod_rdy,
  input logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifdw_tok_prod_vld,
  //-------------------------------
  // Token o_m_ifdw_tok_cons
  //-------------------------------
  input logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifdw_tok_cons_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifdw_tok_cons_vld,
  //-------------------------------
  // Token i_d_ifd0_tok_prod
  //-------------------------------
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_d_ifd0_tok_prod_rdy,
  input logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_d_ifd0_tok_prod_vld,
  //-------------------------------
  // Token o_d_ifd0_tok_cons
  //-------------------------------
  input logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_d_ifd0_tok_cons_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_d_ifd0_tok_cons_vld,
  //-------------------------------
  // Token i_d_ifd1_tok_prod
  //-------------------------------
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_d_ifd1_tok_prod_rdy,
  input logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_d_ifd1_tok_prod_vld,
  //-------------------------------
  // Token o_d_ifd1_tok_cons
  //-------------------------------
  input logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_d_ifd1_tok_cons_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_d_ifd1_tok_cons_vld,
  //-------------------------------
  // Token i_m_odr_tok_prod
  //-------------------------------
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_odr_tok_prod_rdy,
  input logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_odr_tok_prod_vld,
  //-------------------------------
  // Token o_m_odr_tok_cons
  //-------------------------------
  input logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_odr_tok_cons_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_odr_tok_cons_vld,
  //-------------------------------
  // Token i_d_odr_tok_prod
  //-------------------------------
  output logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_d_odr_tok_prod_rdy,
  input logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_d_odr_tok_prod_vld,
  //-------------------------------
  // Token o_d_odr_tok_cons
  //-------------------------------
  input logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_d_odr_tok_cons_rdy,
  output logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_d_odr_tok_cons_vld,
  //-------------------------------
  // Token i_mvm_exe_tok_prod
  //-------------------------------
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] o_mvm_exe_tok_prod_rdy,
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] i_mvm_exe_tok_prod_vld,
  //-------------------------------
  // Token o_mvm_exe_tok_cons
  //-------------------------------
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] i_mvm_exe_tok_cons_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] o_mvm_exe_tok_cons_vld,
  //-------------------------------
  // Token i_mvm_prg_tok_prod
  //-------------------------------
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] o_mvm_prg_tok_prod_rdy,
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] i_mvm_prg_tok_prod_vld,
  //-------------------------------
  // Token o_mvm_prg_tok_cons
  //-------------------------------
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] i_mvm_prg_tok_cons_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] o_mvm_prg_tok_cons_vld,
  //-------------------------------
  // Token i_m_iau_tok_prod
  //-------------------------------
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD-1:0] o_m_iau_tok_prod_rdy,
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD-1:0] i_m_iau_tok_prod_vld,
  //-------------------------------
  // Token o_m_iau_tok_cons
  //-------------------------------
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS-1:0] i_m_iau_tok_cons_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS-1:0] o_m_iau_tok_cons_vld,
  //-------------------------------
  // Token i_m_dpu_tok_prod
  //-------------------------------
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD-1:0] o_m_dpu_tok_prod_rdy,
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD-1:0] i_m_dpu_tok_prod_vld,
  //-------------------------------
  // Token o_m_dpu_tok_cons
  //-------------------------------
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS-1:0] i_m_dpu_tok_cons_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS-1:0] o_m_dpu_tok_cons_vld,
  //-------------------------------
  // Token i_dwpu_tok_prod
  //-------------------------------
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] o_dwpu_tok_prod_rdy,
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_dwpu_tok_prod_vld,
  //-------------------------------
  // Token o_dwpu_tok_cons
  //-------------------------------
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] i_dwpu_tok_cons_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] o_dwpu_tok_cons_vld,
  //-------------------------------
  // Token i_d_iau_tok_prod
  //-------------------------------
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] o_d_iau_tok_prod_rdy,
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_d_iau_tok_prod_vld,
  //-------------------------------
  // Token o_d_iau_tok_cons
  //-------------------------------
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_d_iau_tok_cons_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] o_d_iau_tok_cons_vld,
  //-------------------------------
  // Token i_d_dpu_tok_prod
  //-------------------------------
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD-1:0] o_d_dpu_tok_prod_rdy,
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_d_dpu_tok_prod_vld,
  //-------------------------------
  // Token o_d_dpu_tok_cons
  //-------------------------------
  input logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_d_dpu_tok_cons_rdy,
  output logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS-1:0] o_d_dpu_tok_cons_vld,

  //-------------------------------
  // AXI4 o_noc_ht_axi_m
  //-------------------------------
  output logic                                                   o_noc_ht_axi_m_awvalid,
  output logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_noc_ht_axi_m_awaddr,
  output logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_noc_ht_axi_m_awid,
  output logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_noc_ht_axi_m_awlen,
  output logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_awsize,
  output logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_awburst,
  output logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_awcache,
  output logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_awprot,
  output logic                                                   o_noc_ht_axi_m_awlock,
  output logic                                                   o_noc_ht_axi_m_wvalid,
  output logic                                                   o_noc_ht_axi_m_wlast,
  output logic [     aic_common_pkg::AIC_HT_AXI_WSTRB_WIDTH-1:0] o_noc_ht_axi_m_wstrb,
  output logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] o_noc_ht_axi_m_wdata,
  output logic                                                   o_noc_ht_axi_m_bready,
  output logic                                                   o_noc_ht_axi_m_arvalid,
  output logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_noc_ht_axi_m_araddr,
  output logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_noc_ht_axi_m_arid,
  output logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_noc_ht_axi_m_arlen,
  output logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_arsize,
  output logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_arburst,
  output logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_arcache,
  output logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_arprot,
  output logic                                                   o_noc_ht_axi_m_arlock,
  output logic                                                   o_noc_ht_axi_m_rready,

  //-------------------------------
  // AXI4 i_noc_ht_axi_m
  //-------------------------------
  input logic                                             i_noc_ht_axi_m_awready,
  input logic                                             i_noc_ht_axi_m_wready,
  input logic                                             i_noc_ht_axi_m_bvalid,
  input logic [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_noc_ht_axi_m_bid,
  input logic [aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_bresp,
  input logic                                             i_noc_ht_axi_m_arready,
  input logic                                             i_noc_ht_axi_m_rvalid,
  input logic                                             i_noc_ht_axi_m_rlast,
  input logic [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_noc_ht_axi_m_rid,
  input logic [aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] i_noc_ht_axi_m_rdata,
  input logic [aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_rresp,

  //-------------------------------
  // AXI4 o_dmc_l1_ht_axi_m
  //-------------------------------
  output logic                                                   o_dmc_l1_ht_axi_m_awvalid,
  output logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_ht_axi_m_awaddr,
  output logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_ht_axi_m_awid,
  output logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_dmc_l1_ht_axi_m_awlen,
  output logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_ht_axi_m_awsize,
  output logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_ht_axi_m_awburst,
  output logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_dmc_l1_ht_axi_m_awcache,
  output logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_dmc_l1_ht_axi_m_awprot,
  output logic                                                   o_dmc_l1_ht_axi_m_awlock,
  output logic                                                   o_dmc_l1_ht_axi_m_wvalid,
  output logic                                                   o_dmc_l1_ht_axi_m_wlast,
  output logic [     aic_common_pkg::AIC_HT_AXI_WSTRB_WIDTH-1:0] o_dmc_l1_ht_axi_m_wstrb,
  output logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] o_dmc_l1_ht_axi_m_wdata,
  output logic                                                   o_dmc_l1_ht_axi_m_bready,
  output logic                                                   o_dmc_l1_ht_axi_m_arvalid,
  output logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_ht_axi_m_araddr,
  output logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_ht_axi_m_arid,
  output logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_dmc_l1_ht_axi_m_arlen,
  output logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_ht_axi_m_arsize,
  output logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_ht_axi_m_arburst,
  output logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_dmc_l1_ht_axi_m_arcache,
  output logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_dmc_l1_ht_axi_m_arprot,
  output logic                                                   o_dmc_l1_ht_axi_m_arlock,
  output logic                                                   o_dmc_l1_ht_axi_m_rready,

  //-------------------------------
  // AXI4 i_dmc_l1_ht_axi_m
  //-------------------------------
  input logic                                             i_dmc_l1_ht_axi_m_awready,
  input logic                                             i_dmc_l1_ht_axi_m_wready,
  input logic                                             i_dmc_l1_ht_axi_m_bvalid,
  input logic [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_ht_axi_m_bid,
  input logic [aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_dmc_l1_ht_axi_m_bresp,
  input logic                                             i_dmc_l1_ht_axi_m_arready,
  input logic                                             i_dmc_l1_ht_axi_m_rvalid,
  input logic                                             i_dmc_l1_ht_axi_m_rlast,
  input logic [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_ht_axi_m_rid,
  input logic [aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] i_dmc_l1_ht_axi_m_rdata,
  input logic [aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_dmc_l1_ht_axi_m_rresp,

  //-------------------------------
  // AXI4 i_noc_lt_axi_s
  //-------------------------------
  input logic                                                   i_noc_lt_axi_s_awvalid,
  input logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_noc_lt_axi_s_awaddr,
  input logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] i_noc_lt_axi_s_awid,
  input logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] i_noc_lt_axi_s_awlen,
  input logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_awsize,
  input logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_awburst,
  input logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_awcache,
  input logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_awprot,
  input logic                                                   i_noc_lt_axi_s_awlock,
  input logic                                                   i_noc_lt_axi_s_wvalid,
  input logic                                                   i_noc_lt_axi_s_wlast,
  input logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] i_noc_lt_axi_s_wstrb,
  input logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_noc_lt_axi_s_wdata,
  input logic                                                   i_noc_lt_axi_s_bready,
  input logic                                                   i_noc_lt_axi_s_arvalid,
  input logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_noc_lt_axi_s_araddr,
  input logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] i_noc_lt_axi_s_arid,
  input logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] i_noc_lt_axi_s_arlen,
  input logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_arsize,
  input logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_arburst,
  input logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_arcache,
  input logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_arprot,
  input logic                                                   i_noc_lt_axi_s_arlock,
  input logic                                                   i_noc_lt_axi_s_rready,

  //-------------------------------
  // AXI4 o_noc_lt_axi_s
  //-------------------------------
  output logic                                             o_noc_lt_axi_s_awready,
  output logic                                             o_noc_lt_axi_s_wready,
  output logic                                             o_noc_lt_axi_s_bvalid,
  output logic [aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] o_noc_lt_axi_s_bid,
  output logic [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_bresp,
  output logic                                             o_noc_lt_axi_s_arready,
  output logic                                             o_noc_lt_axi_s_rvalid,
  output logic                                             o_noc_lt_axi_s_rlast,
  output logic [aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] o_noc_lt_axi_s_rid,
  output logic [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_noc_lt_axi_s_rdata,
  output logic [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_rresp,

  //-------------------------------
  // AXI4 o_noc_lt_axi_m
  //-------------------------------
  output logic                                                   o_noc_lt_axi_m_awvalid,
  output logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_noc_lt_axi_m_awaddr,
  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_noc_lt_axi_m_awid,
  output logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_noc_lt_axi_m_awlen,
  output logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_awsize,
  output logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_awburst,
  output logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_awcache,
  output logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_awprot,
  output logic                                                   o_noc_lt_axi_m_awlock,
  output logic                                                   o_noc_lt_axi_m_wvalid,
  output logic                                                   o_noc_lt_axi_m_wlast,
  output logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] o_noc_lt_axi_m_wstrb,
  output logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_noc_lt_axi_m_wdata,
  output logic                                                   o_noc_lt_axi_m_bready,
  output logic                                                   o_noc_lt_axi_m_arvalid,
  output logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_noc_lt_axi_m_araddr,
  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_noc_lt_axi_m_arid,
  output logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_noc_lt_axi_m_arlen,
  output logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_arsize,
  output logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_arburst,
  output logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_arcache,
  output logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_arprot,
  output logic                                                   o_noc_lt_axi_m_arlock,
  output logic                                                   o_noc_lt_axi_m_rready,

  //-------------------------------
  // AXI4 i_noc_lt_axi_m
  //-------------------------------
  input logic                                             i_noc_lt_axi_m_awready,
  input logic                                             i_noc_lt_axi_m_wready,
  input logic                                             i_noc_lt_axi_m_bvalid,
  input logic [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_noc_lt_axi_m_bid,
  input logic [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_bresp,
  input logic                                             i_noc_lt_axi_m_arready,
  input logic                                             i_noc_lt_axi_m_rvalid,
  input logic                                             i_noc_lt_axi_m_rlast,
  input logic [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_noc_lt_axi_m_rid,
  input logic [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_noc_lt_axi_m_rdata,
  input logic [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_rresp,

  //-------------------------------
  // AXI4 o_dmc_l1_lt_axi_m
  //-------------------------------
  output logic                                                   o_dmc_l1_lt_axi_m_awvalid,
  output logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_lt_axi_m_awaddr,
  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_lt_axi_m_awid,
  output logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_dmc_l1_lt_axi_m_awlen,
  output logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_lt_axi_m_awsize,
  output logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_lt_axi_m_awburst,
  output logic                                                   o_dmc_l1_lt_axi_m_wvalid,
  output logic                                                   o_dmc_l1_lt_axi_m_wlast,
  output logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] o_dmc_l1_lt_axi_m_wstrb,
  output logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_dmc_l1_lt_axi_m_wdata,
  output logic                                                   o_dmc_l1_lt_axi_m_bready,
  output logic                                                   o_dmc_l1_lt_axi_m_arvalid,
  output logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_lt_axi_m_araddr,
  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_lt_axi_m_arid,
  output logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_dmc_l1_lt_axi_m_arlen,
  output logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_lt_axi_m_arsize,
  output logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_lt_axi_m_arburst,
  output logic                                                   o_dmc_l1_lt_axi_m_rready,

  //-------------------------------
  // AXI4 i_dmc_l1_lt_axi_m
  //-------------------------------
  input logic                                             i_dmc_l1_lt_axi_m_awready,
  input logic                                             i_dmc_l1_lt_axi_m_wready,
  input logic                                             i_dmc_l1_lt_axi_m_bvalid,
  input logic [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_lt_axi_m_bid,
  input logic [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_dmc_l1_lt_axi_m_bresp,
  input logic                                             i_dmc_l1_lt_axi_m_arready,
  input logic                                             i_dmc_l1_lt_axi_m_rvalid,
  input logic                                             i_dmc_l1_lt_axi_m_rlast,
  input logic [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_lt_axi_m_rid,
  input logic [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_dmc_l1_lt_axi_m_rdata,
  input logic [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_dmc_l1_lt_axi_m_rresp,


  //-------------------------------
  // DFT Interface
  //-------------------------------
  input wire ijtag_tck,
  input wire ijtag_reset,
  input logic ijtag_sel,
  input logic ijtag_ue,
  input logic ijtag_se,
  input logic ijtag_ce,
  input logic ijtag_si,
  output logic ijtag_so,
  input wire test_clk,
  input logic test_mode,
  input logic edt_update,
  input logic scan_en,
  input logic [12-1:0] scan_in,
  output logic [12-1:0] scan_out,
  input wire bisr_clk,
  input wire bisr_reset,
  input logic bisr_shift_en,
  input logic bisr_si,
  output logic bisr_so
);

  //-------------------------------
  // Protocols
  //-------------------------------



  //-------------------------------
  // TOKEN SPILL for i_m_ifd0_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifd0_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_m_ifd0_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifd0_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_PROD)
  ) o_m_ifd0_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_m_ifd0_tok_prod_vld),
    .o_s_ready(o_m_ifd0_tok_prod_rdy),
    .o_m_valid(i_m_ifd0_tok_prod_subip_vld),
    .i_m_ready(o_m_ifd0_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_m_ifd0_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifd0_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_m_ifd0_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifd0_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_CONS)
  ) i_m_ifd0_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_m_ifd0_tok_cons_subip_vld),
    .o_s_ready(i_m_ifd0_tok_cons_subip_rdy),
    .o_m_valid(o_m_ifd0_tok_cons_vld),
    .i_m_ready(i_m_ifd0_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_m_ifd1_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifd1_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_m_ifd1_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifd1_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_PROD)
  ) o_m_ifd1_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_m_ifd1_tok_prod_vld),
    .o_s_ready(o_m_ifd1_tok_prod_rdy),
    .o_m_valid(i_m_ifd1_tok_prod_subip_vld),
    .i_m_ready(o_m_ifd1_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_m_ifd1_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifd1_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_m_ifd1_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifd1_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_CONS)
  ) i_m_ifd1_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_m_ifd1_tok_cons_subip_vld),
    .o_s_ready(i_m_ifd1_tok_cons_subip_rdy),
    .o_m_valid(o_m_ifd1_tok_cons_vld),
    .i_m_ready(i_m_ifd1_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_m_ifd2_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifd2_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_m_ifd2_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifd2_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_PROD)
  ) o_m_ifd2_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_m_ifd2_tok_prod_vld),
    .o_s_ready(o_m_ifd2_tok_prod_rdy),
    .o_m_valid(i_m_ifd2_tok_prod_subip_vld),
    .i_m_ready(o_m_ifd2_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_m_ifd2_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifd2_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_m_ifd2_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifd2_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_CONS)
  ) i_m_ifd2_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_m_ifd2_tok_cons_subip_vld),
    .o_s_ready(i_m_ifd2_tok_cons_subip_rdy),
    .o_m_valid(o_m_ifd2_tok_cons_vld),
    .i_m_ready(i_m_ifd2_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_m_ifdw_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_ifdw_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_m_ifdw_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_ifdw_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_PROD)
  ) o_m_ifdw_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_m_ifdw_tok_prod_vld),
    .o_s_ready(o_m_ifdw_tok_prod_rdy),
    .o_m_valid(i_m_ifdw_tok_prod_subip_vld),
    .i_m_ready(o_m_ifdw_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_m_ifdw_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_ifdw_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_m_ifdw_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_ifdw_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_CONS)
  ) i_m_ifdw_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_m_ifdw_tok_cons_subip_vld),
    .o_s_ready(i_m_ifdw_tok_cons_subip_rdy),
    .o_m_valid(o_m_ifdw_tok_cons_vld),
    .i_m_ready(i_m_ifdw_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_d_ifd0_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_d_ifd0_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_d_ifd0_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_d_ifd0_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_PROD)
  ) o_d_ifd0_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_d_ifd0_tok_prod_vld),
    .o_s_ready(o_d_ifd0_tok_prod_rdy),
    .o_m_valid(i_d_ifd0_tok_prod_subip_vld),
    .i_m_ready(o_d_ifd0_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_d_ifd0_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_d_ifd0_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_d_ifd0_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_d_ifd0_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_CONS)
  ) i_d_ifd0_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_d_ifd0_tok_cons_subip_vld),
    .o_s_ready(i_d_ifd0_tok_cons_subip_rdy),
    .o_m_valid(o_d_ifd0_tok_cons_vld),
    .i_m_ready(i_d_ifd0_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_d_ifd1_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_d_ifd1_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_d_ifd1_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_d_ifd1_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_PROD)
  ) o_d_ifd1_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_d_ifd1_tok_prod_vld),
    .o_s_ready(o_d_ifd1_tok_prod_rdy),
    .o_m_valid(i_d_ifd1_tok_prod_subip_vld),
    .i_m_ready(o_d_ifd1_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_d_ifd1_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_d_ifd1_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_d_ifd1_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_d_ifd1_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_CONS)
  ) i_d_ifd1_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_d_ifd1_tok_cons_subip_vld),
    .o_s_ready(i_d_ifd1_tok_cons_subip_rdy),
    .o_m_valid(o_d_ifd1_tok_cons_vld),
    .i_m_ready(i_d_ifd1_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_m_odr_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_m_odr_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_m_odr_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_m_odr_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_PROD)
  ) o_m_odr_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_m_odr_tok_prod_vld),
    .o_s_ready(o_m_odr_tok_prod_rdy),
    .o_m_valid(i_m_odr_tok_prod_subip_vld),
    .i_m_ready(o_m_odr_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_m_odr_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_m_odr_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_m_odr_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_m_odr_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_CONS)
  ) i_m_odr_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_m_odr_tok_cons_subip_vld),
    .o_s_ready(i_m_odr_tok_cons_subip_rdy),
    .o_m_valid(o_m_odr_tok_cons_vld),
    .i_m_ready(i_m_odr_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_d_odr_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] i_d_odr_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_d_odr_tok_prod
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_PROD-1:0] o_d_odr_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_PROD)
  ) o_d_odr_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_d_odr_tok_prod_vld),
    .o_s_ready(o_d_odr_tok_prod_rdy),
    .o_m_valid(i_d_odr_tok_prod_subip_vld),
    .i_m_ready(o_d_odr_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_d_odr_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] o_d_odr_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_d_odr_tok_cons
  //-------------------------------
  logic [dmc_pkg::DMC_TOKENS_CONS-1:0] i_d_odr_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(dmc_pkg::DMC_TOKENS_CONS)
  ) i_d_odr_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_d_odr_tok_cons_subip_vld),
    .o_s_ready(i_d_odr_tok_cons_subip_rdy),
    .o_m_valid(o_d_odr_tok_cons_vld),
    .i_m_ready(i_d_odr_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_mvm_exe_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] i_mvm_exe_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_mvm_exe_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] o_mvm_exe_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD)
  ) o_mvm_exe_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_mvm_exe_tok_prod_vld),
    .o_s_ready(o_mvm_exe_tok_prod_rdy),
    .o_m_valid(i_mvm_exe_tok_prod_subip_vld),
    .i_m_ready(o_mvm_exe_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_mvm_exe_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] o_mvm_exe_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_mvm_exe_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] i_mvm_exe_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS)
  ) i_mvm_exe_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_mvm_exe_tok_cons_subip_vld),
    .o_s_ready(i_mvm_exe_tok_cons_subip_rdy),
    .o_m_valid(o_mvm_exe_tok_cons_vld),
    .i_m_ready(i_mvm_exe_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_mvm_prg_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] i_mvm_prg_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_mvm_prg_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] o_mvm_prg_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD)
  ) o_mvm_prg_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_mvm_prg_tok_prod_vld),
    .o_s_ready(o_mvm_prg_tok_prod_rdy),
    .o_m_valid(i_mvm_prg_tok_prod_subip_vld),
    .i_m_ready(o_mvm_prg_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_mvm_prg_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] o_mvm_prg_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_mvm_prg_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] i_mvm_prg_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS)
  ) i_mvm_prg_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_mvm_prg_tok_cons_subip_vld),
    .o_s_ready(i_mvm_prg_tok_cons_subip_rdy),
    .o_m_valid(o_mvm_prg_tok_cons_vld),
    .i_m_ready(i_mvm_prg_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_m_iau_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD-1:0] i_m_iau_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_m_iau_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD-1:0] o_m_iau_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD)
  ) o_m_iau_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_m_iau_tok_prod_vld),
    .o_s_ready(o_m_iau_tok_prod_rdy),
    .o_m_valid(i_m_iau_tok_prod_subip_vld),
    .i_m_ready(o_m_iau_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_m_iau_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS-1:0] o_m_iau_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_m_iau_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS-1:0] i_m_iau_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS)
  ) i_m_iau_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_m_iau_tok_cons_subip_vld),
    .o_s_ready(i_m_iau_tok_cons_subip_rdy),
    .o_m_valid(o_m_iau_tok_cons_vld),
    .i_m_ready(i_m_iau_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_m_dpu_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD-1:0] i_m_dpu_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_m_dpu_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD-1:0] o_m_dpu_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD)
  ) o_m_dpu_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_m_dpu_tok_prod_vld),
    .o_s_ready(o_m_dpu_tok_prod_rdy),
    .o_m_valid(i_m_dpu_tok_prod_subip_vld),
    .i_m_ready(o_m_dpu_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_m_dpu_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS-1:0] o_m_dpu_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_m_dpu_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS-1:0] i_m_dpu_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS)
  ) i_m_dpu_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_m_dpu_tok_cons_subip_vld),
    .o_s_ready(i_m_dpu_tok_cons_subip_rdy),
    .o_m_valid(o_m_dpu_tok_cons_vld),
    .i_m_ready(i_m_dpu_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_dwpu_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_dwpu_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_dwpu_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] o_dwpu_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD)
  ) o_dwpu_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_dwpu_tok_prod_vld),
    .o_s_ready(o_dwpu_tok_prod_rdy),
    .o_m_valid(i_dwpu_tok_prod_subip_vld),
    .i_m_ready(o_dwpu_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_dwpu_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] o_dwpu_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_dwpu_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] i_dwpu_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS)
  ) i_dwpu_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_dwpu_tok_cons_subip_vld),
    .o_s_ready(i_dwpu_tok_cons_subip_rdy),
    .o_m_valid(o_dwpu_tok_cons_vld),
    .i_m_ready(i_dwpu_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_d_iau_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_d_iau_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_d_iau_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] o_d_iau_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD)
  ) o_d_iau_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_d_iau_tok_prod_vld),
    .o_s_ready(o_d_iau_tok_prod_rdy),
    .o_m_valid(i_d_iau_tok_prod_subip_vld),
    .i_m_ready(o_d_iau_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_d_iau_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] o_d_iau_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_d_iau_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_d_iau_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS)
  ) i_d_iau_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_d_iau_tok_cons_subip_vld),
    .o_s_ready(i_d_iau_tok_cons_subip_rdy),
    .o_m_valid(o_d_iau_tok_cons_vld),
    .i_m_ready(i_d_iau_tok_cons_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for i_d_dpu_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_d_dpu_tok_prod_subip_vld;


  //-------------------------------
  // TOKEN SPILL for o_d_dpu_tok_prod
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD-1:0] o_d_dpu_tok_prod_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD)
  ) o_d_dpu_tok_prod_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(i_d_dpu_tok_prod_vld),
    .o_s_ready(o_d_dpu_tok_prod_rdy),
    .o_m_valid(i_d_dpu_tok_prod_subip_vld),
    .i_m_ready(o_d_dpu_tok_prod_subip_rdy)
  );
  //-------------------------------
  // TOKEN SPILL for o_d_dpu_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS-1:0] o_d_dpu_tok_cons_subip_vld;


  //-------------------------------
  // TOKEN SPILL for i_d_dpu_tok_cons
  //-------------------------------
  logic [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_d_dpu_tok_cons_subip_rdy;

  token_cut #(
    .NumTokens(token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS)
  ) i_d_dpu_tok_cons_spill (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_s_valid(o_d_dpu_tok_cons_subip_vld),
    .o_s_ready(i_d_dpu_tok_cons_subip_rdy),
    .o_m_valid(o_d_dpu_tok_cons_vld),
    .i_m_ready(i_d_dpu_tok_cons_rdy)
  );


  //-------------------------------
  // OCPL SPILL for o_tok_prod_ocpl_m
  //-------------------------------
  logic o_tok_prod_ocpl_m_subip_mcmd;
  logic o_tok_prod_ocpl_m_subip_pipe_1_mcmd;
  chip_pkg::chip_ocpl_token_addr_t o_tok_prod_ocpl_m_subip_maddr;
  chip_pkg::chip_ocpl_token_addr_t o_tok_prod_ocpl_m_subip_pipe_1_maddr;
  chip_pkg::chip_ocpl_token_data_t o_tok_prod_ocpl_m_subip_mdata;
  chip_pkg::chip_ocpl_token_data_t o_tok_prod_ocpl_m_subip_pipe_1_mdata;


  //-------------------------------
  // OCPL SPILL for i_tok_prod_ocpl_m
  //-------------------------------
  logic i_tok_prod_ocpl_m_subip_accept;
  logic i_tok_prod_ocpl_m_subip_pipe_1_accept;

  ocp_lite_cut #(
    .addr_t(logic [chip_pkg::CHIP_OCPL_TOKEN_ADDR_W-1:0]),
    .data_t(logic [chip_pkg::CHIP_OCPL_TOKEN_DATA_W-1:0])
  ) i_tok_prod_ocpl_m_spill (
    .i_clk          (i_clk),
    .i_rst_n        (i_rst_n),
    .i_s_mcmd       (o_tok_prod_ocpl_m_subip_pipe_1_mcmd),
    .i_s_maddr      (o_tok_prod_ocpl_m_subip_pipe_1_maddr),
    .i_s_mdata      (o_tok_prod_ocpl_m_subip_pipe_1_mdata),
    .o_s_scmd_accept(i_tok_prod_ocpl_m_subip_pipe_1_scmdaccept),
    .o_m_mcmd       (o_tok_prod_ocpl_m_mcmd),
    .o_m_maddr      (o_tok_prod_ocpl_m_maddr),
    .o_m_mdata      (o_tok_prod_ocpl_m_mdata),
    .i_m_scmd_accept(i_tok_prod_ocpl_m_scmdaccept)
  );
  ocp_lite_cut #(
    .addr_t(logic [chip_pkg::CHIP_OCPL_TOKEN_ADDR_W-1:0]),
    .data_t(logic [chip_pkg::CHIP_OCPL_TOKEN_DATA_W-1:0])
  ) i_tok_prod_ocpl_m_spill_1 (
    .i_clk          (i_clk),
    .i_rst_n        (i_rst_n),
    .i_s_mcmd       (o_tok_prod_ocpl_m_subip_mcmd),
    .i_s_maddr      (o_tok_prod_ocpl_m_subip_maddr),
    .i_s_mdata      (o_tok_prod_ocpl_m_subip_mdata),
    .o_s_scmd_accept(i_tok_prod_ocpl_m_subip_scmdaccept),
    .o_m_mcmd       (o_tok_prod_ocpl_m_subip_pipe_1_mcmd),
    .o_m_maddr      (o_tok_prod_ocpl_m_subip_pipe_1_maddr),
    .o_m_mdata      (o_tok_prod_ocpl_m_subip_pipe_1_mdata),
    .i_m_scmd_accept(i_tok_prod_ocpl_m_subip_pipe_1_scmdaccept)
  );
  //-------------------------------
  // OCPL SPILL for i_tok_cons_ocpl_s
  //-------------------------------
  logic i_tok_cons_ocpl_s_subip_mcmd;
  logic i_tok_cons_ocpl_s_subip_pipe_1_mcmd;
  chip_pkg::chip_ocpl_token_addr_t i_tok_cons_ocpl_s_subip_maddr;
  chip_pkg::chip_ocpl_token_addr_t i_tok_cons_ocpl_s_subip_pipe_1_maddr;
  chip_pkg::chip_ocpl_token_data_t i_tok_cons_ocpl_s_subip_mdata;
  chip_pkg::chip_ocpl_token_data_t i_tok_cons_ocpl_s_subip_pipe_1_mdata;


  //-------------------------------
  // OCPL SPILL for o_tok_cons_ocpl_s
  //-------------------------------
  logic o_tok_cons_ocpl_s_subip_n;
  logic o_tok_cons_ocpl_s_subip_pipe_1_n;
  logic o_tok_cons_ocpl_s_subip_accept;
  logic o_tok_cons_ocpl_s_subip_pipe_1_accept;

  ocp_lite_cut #(
    .addr_t(logic [chip_pkg::CHIP_OCPL_TOKEN_ADDR_W-1:0]),
    .data_t(logic [chip_pkg::CHIP_OCPL_TOKEN_DATA_W-1:0])
  ) o_tok_cons_ocpl_s_spill (
    .i_clk          (i_clk),
    .i_rst_n        (i_rst_n),
    .i_s_mcmd       (i_tok_cons_ocpl_s_mcmd),
    .i_s_maddr      (i_tok_cons_ocpl_s_maddr),
    .i_s_mdata      (i_tok_cons_ocpl_s_mdata),
    .o_s_scmd_accept(o_tok_cons_ocpl_s_scmdaccept),
    .o_m_mcmd       (i_tok_cons_ocpl_s_subip_pipe_1_mcmd),
    .o_m_maddr      (i_tok_cons_ocpl_s_subip_pipe_1_maddr),
    .o_m_mdata      (i_tok_cons_ocpl_s_subip_pipe_1_mdata),
    .i_m_scmd_accept(o_tok_cons_ocpl_s_subip_pipe_1_scmdaccept)
  );
  ocp_lite_cut #(
    .addr_t(logic [chip_pkg::CHIP_OCPL_TOKEN_ADDR_W-1:0]),
    .data_t(logic [chip_pkg::CHIP_OCPL_TOKEN_DATA_W-1:0])
  ) o_tok_cons_ocpl_s_spill_1 (
    .i_clk          (i_clk),
    .i_rst_n        (i_rst_n),
    .i_s_mcmd       (i_tok_cons_ocpl_s_subip_pipe_1_mcmd),
    .i_s_maddr      (i_tok_cons_ocpl_s_subip_pipe_1_maddr),
    .i_s_mdata      (i_tok_cons_ocpl_s_subip_pipe_1_mdata),
    .o_s_scmd_accept(o_tok_cons_ocpl_s_subip_pipe_1_scmdaccept),
    .o_m_mcmd       (i_tok_cons_ocpl_s_subip_mcmd),
    .o_m_maddr      (i_tok_cons_ocpl_s_subip_maddr),
    .o_m_mdata      (i_tok_cons_ocpl_s_subip_mdata),
    .i_m_scmd_accept(o_tok_cons_ocpl_s_subip_scmdaccept)
  );


  //-------------------------------
  // AXI SPILL for o_noc_ht_axi_m
  //-------------------------------
  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_noc_ht_axi_m_subip_awid;
  logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_noc_ht_axi_m_subip_awaddr;
  logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_noc_ht_axi_m_subip_awlen;
  logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_subip_awsize;
  logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_subip_awburst;
  logic                                                   o_noc_ht_axi_m_subip_awlock;
  logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_subip_awcache;
  logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_subip_awprot;
  logic                                                   o_noc_ht_axi_m_subip_awvalid;
  logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] o_noc_ht_axi_m_subip_wdata;
  logic [     aic_common_pkg::AIC_HT_AXI_WSTRB_WIDTH-1:0] o_noc_ht_axi_m_subip_wstrb;
  logic                                                   o_noc_ht_axi_m_subip_wlast;
  logic                                                   o_noc_ht_axi_m_subip_wvalid;
  logic                                                   o_noc_ht_axi_m_subip_bready;
  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_noc_ht_axi_m_subip_arid;
  logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_noc_ht_axi_m_subip_araddr;
  logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_noc_ht_axi_m_subip_arlen;
  logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_subip_arsize;
  logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_subip_arburst;
  logic                                                   o_noc_ht_axi_m_subip_arlock;
  logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_subip_arcache;
  logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_subip_arprot;
  logic                                                   o_noc_ht_axi_m_subip_arvalid;
  logic                                                   o_noc_ht_axi_m_subip_rready;


  //-------------------------------
  // AXI SPILL for i_noc_ht_axi_m
  //-------------------------------
  logic                                                   i_noc_ht_axi_m_subip_awready;
  logic                                                   i_noc_ht_axi_m_subip_wready;
  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_noc_ht_axi_m_subip_bid;
  logic [      aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_subip_bresp;
  logic                                                   i_noc_ht_axi_m_subip_bvalid;
  logic                                                   i_noc_ht_axi_m_subip_arready;
  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_noc_ht_axi_m_subip_rid;
  logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] i_noc_ht_axi_m_subip_rdata;
  logic [      aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_subip_rresp;
  logic                                                   i_noc_ht_axi_m_subip_rlast;
  logic                                                   i_noc_ht_axi_m_subip_rvalid;

  axe_axi_multicut_flat #(
    .AxiAddrWidth(aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH),
    .AxiIdWidth(aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH),
    .AxiDataWidth(aic_common_pkg::AIC_HT_AXI_DATA_WIDTH),
    .NumCuts(1)
  ) i_noc_ht_axi_m_spill_flat (
    .i_clk            (i_clk),
    .i_rst_n          (i_rst_n),
    .i_axi_s_aw_id    (o_noc_ht_axi_m_subip_awid),
    .i_axi_s_aw_addr  (o_noc_ht_axi_m_subip_awaddr),
    .i_axi_s_aw_len   (o_noc_ht_axi_m_subip_awlen),
    .i_axi_s_aw_size  (o_noc_ht_axi_m_subip_awsize),
    .i_axi_s_aw_burst (o_noc_ht_axi_m_subip_awburst),
    .i_axi_s_aw_lock  (o_noc_ht_axi_m_subip_awlock),
    .i_axi_s_aw_cache (o_noc_ht_axi_m_subip_awcache),
    .i_axi_s_aw_prot  (o_noc_ht_axi_m_subip_awprot),
    .i_axi_s_aw_qos   ('0),
    .i_axi_s_aw_region('0),
    .i_axi_s_aw_user  ('0),
    .i_axi_s_aw_valid (o_noc_ht_axi_m_subip_awvalid),
    .o_axi_s_aw_ready (i_noc_ht_axi_m_subip_awready),
    .i_axi_s_w_data   (o_noc_ht_axi_m_subip_wdata),
    .i_axi_s_w_strb   (o_noc_ht_axi_m_subip_wstrb),
    .i_axi_s_w_last   (o_noc_ht_axi_m_subip_wlast),
    .i_axi_s_w_user   ('0),
    .i_axi_s_w_valid  (o_noc_ht_axi_m_subip_wvalid),
    .o_axi_s_w_ready  (i_noc_ht_axi_m_subip_wready),
    .o_axi_s_b_id     (i_noc_ht_axi_m_subip_bid),
    .o_axi_s_b_resp   (i_noc_ht_axi_m_subip_bresp),
    .o_axi_s_b_user   (),
    .o_axi_s_b_valid  (i_noc_ht_axi_m_subip_bvalid),
    .i_axi_s_b_ready  (o_noc_ht_axi_m_subip_bready),
    .i_axi_s_ar_id    (o_noc_ht_axi_m_subip_arid),
    .i_axi_s_ar_addr  (o_noc_ht_axi_m_subip_araddr),
    .i_axi_s_ar_len   (o_noc_ht_axi_m_subip_arlen),
    .i_axi_s_ar_size  (o_noc_ht_axi_m_subip_arsize),
    .i_axi_s_ar_burst (o_noc_ht_axi_m_subip_arburst),
    .i_axi_s_ar_lock  (o_noc_ht_axi_m_subip_arlock),
    .i_axi_s_ar_cache (o_noc_ht_axi_m_subip_arcache),
    .i_axi_s_ar_prot  (o_noc_ht_axi_m_subip_arprot),
    .i_axi_s_ar_qos   ('0),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user  ('0),
    .i_axi_s_ar_valid (o_noc_ht_axi_m_subip_arvalid),
    .o_axi_s_ar_ready (i_noc_ht_axi_m_subip_arready),
    .o_axi_s_r_id     (i_noc_ht_axi_m_subip_rid),
    .o_axi_s_r_data   (i_noc_ht_axi_m_subip_rdata),
    .o_axi_s_r_resp   (i_noc_ht_axi_m_subip_rresp),
    .o_axi_s_r_last   (i_noc_ht_axi_m_subip_rlast),
    .o_axi_s_r_user   (),
    .o_axi_s_r_valid  (i_noc_ht_axi_m_subip_rvalid),
    .i_axi_s_r_ready  (o_noc_ht_axi_m_subip_rready),
    .o_axi_m_aw_id    (o_noc_ht_axi_m_awid),
    .o_axi_m_aw_addr  (o_noc_ht_axi_m_awaddr),
    .o_axi_m_aw_len   (o_noc_ht_axi_m_awlen),
    .o_axi_m_aw_size  (o_noc_ht_axi_m_awsize),
    .o_axi_m_aw_burst (o_noc_ht_axi_m_awburst),
    .o_axi_m_aw_lock  (o_noc_ht_axi_m_awlock),
    .o_axi_m_aw_cache (o_noc_ht_axi_m_awcache),
    .o_axi_m_aw_prot  (o_noc_ht_axi_m_awprot),
    .o_axi_m_aw_qos   (),
    .o_axi_m_aw_region(),
    .o_axi_m_aw_valid (o_noc_ht_axi_m_awvalid),
    .o_axi_m_aw_user  (),
    .i_axi_m_aw_ready (i_noc_ht_axi_m_awready),
    .o_axi_m_w_data   (o_noc_ht_axi_m_wdata),
    .o_axi_m_w_strb   (o_noc_ht_axi_m_wstrb),
    .o_axi_m_w_last   (o_noc_ht_axi_m_wlast),
    .o_axi_m_w_user   (),
    .o_axi_m_w_valid  (o_noc_ht_axi_m_wvalid),
    .i_axi_m_w_ready  (i_noc_ht_axi_m_wready),
    .i_axi_m_b_id     (i_noc_ht_axi_m_bid),
    .i_axi_m_b_resp   (i_noc_ht_axi_m_bresp),
    .i_axi_m_b_user   ('0),
    .i_axi_m_b_valid  (i_noc_ht_axi_m_bvalid),
    .o_axi_m_b_ready  (o_noc_ht_axi_m_bready),
    .o_axi_m_ar_id    (o_noc_ht_axi_m_arid),
    .o_axi_m_ar_addr  (o_noc_ht_axi_m_araddr),
    .o_axi_m_ar_len   (o_noc_ht_axi_m_arlen),
    .o_axi_m_ar_size  (o_noc_ht_axi_m_arsize),
    .o_axi_m_ar_burst (o_noc_ht_axi_m_arburst),
    .o_axi_m_ar_lock  (o_noc_ht_axi_m_arlock),
    .o_axi_m_ar_cache (o_noc_ht_axi_m_arcache),
    .o_axi_m_ar_prot  (o_noc_ht_axi_m_arprot),
    .o_axi_m_ar_qos   (),
    .o_axi_m_ar_region(),
    .o_axi_m_ar_user  (),
    .o_axi_m_ar_valid (o_noc_ht_axi_m_arvalid),
    .i_axi_m_ar_ready (i_noc_ht_axi_m_arready),
    .i_axi_m_r_id     (i_noc_ht_axi_m_rid),
    .i_axi_m_r_data   (i_noc_ht_axi_m_rdata),
    .i_axi_m_r_resp   (i_noc_ht_axi_m_rresp),
    .i_axi_m_r_last   (i_noc_ht_axi_m_rlast),
    .i_axi_m_r_user   ('0),
    .i_axi_m_r_valid  (i_noc_ht_axi_m_rvalid),
    .o_axi_m_r_ready  (o_noc_ht_axi_m_rready)
  );
  //-------------------------------
  // AXI SPILL for o_dmc_l1_ht_axi_m
  //-------------------------------
  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_awid;
  logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_awaddr;
  logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_awlen;
  logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_awsize;
  logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_awburst;
  logic                                                   o_dmc_l1_ht_axi_m_subip_awlock;
  logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_awcache;
  logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_awprot;
  logic                                                   o_dmc_l1_ht_axi_m_subip_awvalid;
  logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_wdata;
  logic [     aic_common_pkg::AIC_HT_AXI_WSTRB_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_wstrb;
  logic                                                   o_dmc_l1_ht_axi_m_subip_wlast;
  logic                                                   o_dmc_l1_ht_axi_m_subip_wvalid;
  logic                                                   o_dmc_l1_ht_axi_m_subip_bready;
  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_arid;
  logic [      aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_araddr;
  logic [       aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_arlen;
  logic [      aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_arsize;
  logic [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_arburst;
  logic                                                   o_dmc_l1_ht_axi_m_subip_arlock;
  logic [     aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_arcache;
  logic [      aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_dmc_l1_ht_axi_m_subip_arprot;
  logic                                                   o_dmc_l1_ht_axi_m_subip_arvalid;
  logic                                                   o_dmc_l1_ht_axi_m_subip_rready;


  //-------------------------------
  // AXI SPILL for i_dmc_l1_ht_axi_m
  //-------------------------------
  logic                                                   i_dmc_l1_ht_axi_m_subip_awready;
  logic                                                   i_dmc_l1_ht_axi_m_subip_wready;
  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_ht_axi_m_subip_bid;
  logic [      aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_dmc_l1_ht_axi_m_subip_bresp;
  logic                                                   i_dmc_l1_ht_axi_m_subip_bvalid;
  logic                                                   i_dmc_l1_ht_axi_m_subip_arready;
  logic [      aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_ht_axi_m_subip_rid;
  logic [      aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] i_dmc_l1_ht_axi_m_subip_rdata;
  logic [      aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_dmc_l1_ht_axi_m_subip_rresp;
  logic                                                   i_dmc_l1_ht_axi_m_subip_rlast;
  logic                                                   i_dmc_l1_ht_axi_m_subip_rvalid;

  axe_axi_multicut_flat #(
    .AxiAddrWidth(aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH),
    .AxiIdWidth(aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH),
    .AxiDataWidth(aic_common_pkg::AIC_HT_AXI_DATA_WIDTH),
    .NumCuts(1)
  ) i_dmc_l1_ht_axi_m_spill_flat (
    .i_clk            (i_clk),
    .i_rst_n          (i_rst_n),
    .i_axi_s_aw_id    (o_dmc_l1_ht_axi_m_subip_awid),
    .i_axi_s_aw_addr  (o_dmc_l1_ht_axi_m_subip_awaddr),
    .i_axi_s_aw_len   (o_dmc_l1_ht_axi_m_subip_awlen),
    .i_axi_s_aw_size  (o_dmc_l1_ht_axi_m_subip_awsize),
    .i_axi_s_aw_burst (o_dmc_l1_ht_axi_m_subip_awburst),
    .i_axi_s_aw_lock  (o_dmc_l1_ht_axi_m_subip_awlock),
    .i_axi_s_aw_cache (o_dmc_l1_ht_axi_m_subip_awcache),
    .i_axi_s_aw_prot  (o_dmc_l1_ht_axi_m_subip_awprot),
    .i_axi_s_aw_qos   ('0),
    .i_axi_s_aw_region('0),
    .i_axi_s_aw_user  ('0),
    .i_axi_s_aw_valid (o_dmc_l1_ht_axi_m_subip_awvalid),
    .o_axi_s_aw_ready (i_dmc_l1_ht_axi_m_subip_awready),
    .i_axi_s_w_data   (o_dmc_l1_ht_axi_m_subip_wdata),
    .i_axi_s_w_strb   (o_dmc_l1_ht_axi_m_subip_wstrb),
    .i_axi_s_w_last   (o_dmc_l1_ht_axi_m_subip_wlast),
    .i_axi_s_w_user   ('0),
    .i_axi_s_w_valid  (o_dmc_l1_ht_axi_m_subip_wvalid),
    .o_axi_s_w_ready  (i_dmc_l1_ht_axi_m_subip_wready),
    .o_axi_s_b_id     (i_dmc_l1_ht_axi_m_subip_bid),
    .o_axi_s_b_resp   (i_dmc_l1_ht_axi_m_subip_bresp),
    .o_axi_s_b_user   (),
    .o_axi_s_b_valid  (i_dmc_l1_ht_axi_m_subip_bvalid),
    .i_axi_s_b_ready  (o_dmc_l1_ht_axi_m_subip_bready),
    .i_axi_s_ar_id    (o_dmc_l1_ht_axi_m_subip_arid),
    .i_axi_s_ar_addr  (o_dmc_l1_ht_axi_m_subip_araddr),
    .i_axi_s_ar_len   (o_dmc_l1_ht_axi_m_subip_arlen),
    .i_axi_s_ar_size  (o_dmc_l1_ht_axi_m_subip_arsize),
    .i_axi_s_ar_burst (o_dmc_l1_ht_axi_m_subip_arburst),
    .i_axi_s_ar_lock  (o_dmc_l1_ht_axi_m_subip_arlock),
    .i_axi_s_ar_cache (o_dmc_l1_ht_axi_m_subip_arcache),
    .i_axi_s_ar_prot  (o_dmc_l1_ht_axi_m_subip_arprot),
    .i_axi_s_ar_qos   ('0),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user  ('0),
    .i_axi_s_ar_valid (o_dmc_l1_ht_axi_m_subip_arvalid),
    .o_axi_s_ar_ready (i_dmc_l1_ht_axi_m_subip_arready),
    .o_axi_s_r_id     (i_dmc_l1_ht_axi_m_subip_rid),
    .o_axi_s_r_data   (i_dmc_l1_ht_axi_m_subip_rdata),
    .o_axi_s_r_resp   (i_dmc_l1_ht_axi_m_subip_rresp),
    .o_axi_s_r_last   (i_dmc_l1_ht_axi_m_subip_rlast),
    .o_axi_s_r_user   (),
    .o_axi_s_r_valid  (i_dmc_l1_ht_axi_m_subip_rvalid),
    .i_axi_s_r_ready  (o_dmc_l1_ht_axi_m_subip_rready),
    .o_axi_m_aw_id    (o_dmc_l1_ht_axi_m_awid),
    .o_axi_m_aw_addr  (o_dmc_l1_ht_axi_m_awaddr),
    .o_axi_m_aw_len   (o_dmc_l1_ht_axi_m_awlen),
    .o_axi_m_aw_size  (o_dmc_l1_ht_axi_m_awsize),
    .o_axi_m_aw_burst (o_dmc_l1_ht_axi_m_awburst),
    .o_axi_m_aw_lock  (o_dmc_l1_ht_axi_m_awlock),
    .o_axi_m_aw_cache (o_dmc_l1_ht_axi_m_awcache),
    .o_axi_m_aw_prot  (o_dmc_l1_ht_axi_m_awprot),
    .o_axi_m_aw_qos   (),
    .o_axi_m_aw_region(),
    .o_axi_m_aw_valid (o_dmc_l1_ht_axi_m_awvalid),
    .o_axi_m_aw_user  (),
    .i_axi_m_aw_ready (i_dmc_l1_ht_axi_m_awready),
    .o_axi_m_w_data   (o_dmc_l1_ht_axi_m_wdata),
    .o_axi_m_w_strb   (o_dmc_l1_ht_axi_m_wstrb),
    .o_axi_m_w_last   (o_dmc_l1_ht_axi_m_wlast),
    .o_axi_m_w_user   (),
    .o_axi_m_w_valid  (o_dmc_l1_ht_axi_m_wvalid),
    .i_axi_m_w_ready  (i_dmc_l1_ht_axi_m_wready),
    .i_axi_m_b_id     (i_dmc_l1_ht_axi_m_bid),
    .i_axi_m_b_resp   (i_dmc_l1_ht_axi_m_bresp),
    .i_axi_m_b_user   ('0),
    .i_axi_m_b_valid  (i_dmc_l1_ht_axi_m_bvalid),
    .o_axi_m_b_ready  (o_dmc_l1_ht_axi_m_bready),
    .o_axi_m_ar_id    (o_dmc_l1_ht_axi_m_arid),
    .o_axi_m_ar_addr  (o_dmc_l1_ht_axi_m_araddr),
    .o_axi_m_ar_len   (o_dmc_l1_ht_axi_m_arlen),
    .o_axi_m_ar_size  (o_dmc_l1_ht_axi_m_arsize),
    .o_axi_m_ar_burst (o_dmc_l1_ht_axi_m_arburst),
    .o_axi_m_ar_lock  (o_dmc_l1_ht_axi_m_arlock),
    .o_axi_m_ar_cache (o_dmc_l1_ht_axi_m_arcache),
    .o_axi_m_ar_prot  (o_dmc_l1_ht_axi_m_arprot),
    .o_axi_m_ar_qos   (),
    .o_axi_m_ar_region(),
    .o_axi_m_ar_user  (),
    .o_axi_m_ar_valid (o_dmc_l1_ht_axi_m_arvalid),
    .i_axi_m_ar_ready (i_dmc_l1_ht_axi_m_arready),
    .i_axi_m_r_id     (i_dmc_l1_ht_axi_m_rid),
    .i_axi_m_r_data   (i_dmc_l1_ht_axi_m_rdata),
    .i_axi_m_r_resp   (i_dmc_l1_ht_axi_m_rresp),
    .i_axi_m_r_last   (i_dmc_l1_ht_axi_m_rlast),
    .i_axi_m_r_user   ('0),
    .i_axi_m_r_valid  (i_dmc_l1_ht_axi_m_rvalid),
    .o_axi_m_r_ready  (o_dmc_l1_ht_axi_m_rready)
  );
  //-------------------------------
  // AXI SPILL for i_noc_lt_axi_s
  //-------------------------------
  logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] i_noc_lt_axi_s_subip_awid;
  logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_noc_lt_axi_s_subip_awaddr;
  logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] i_noc_lt_axi_s_subip_awlen;
  logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_subip_awsize;
  logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_subip_awburst;
  logic                                                   i_noc_lt_axi_s_subip_awlock;
  logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_subip_awcache;
  logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_subip_awprot;
  logic                                                   i_noc_lt_axi_s_subip_awvalid;
  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_noc_lt_axi_s_subip_wdata;
  logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] i_noc_lt_axi_s_subip_wstrb;
  logic                                                   i_noc_lt_axi_s_subip_wlast;
  logic                                                   i_noc_lt_axi_s_subip_wvalid;
  logic                                                   i_noc_lt_axi_s_subip_bready;
  logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] i_noc_lt_axi_s_subip_arid;
  logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_noc_lt_axi_s_subip_araddr;
  logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] i_noc_lt_axi_s_subip_arlen;
  logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_subip_arsize;
  logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_subip_arburst;
  logic                                                   i_noc_lt_axi_s_subip_arlock;
  logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_subip_arcache;
  logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_subip_arprot;
  logic                                                   i_noc_lt_axi_s_subip_arvalid;
  logic                                                   i_noc_lt_axi_s_subip_rready;


  //-------------------------------
  // AXI SPILL for o_noc_lt_axi_s
  //-------------------------------
  logic                                                   o_noc_lt_axi_s_subip_awready;
  logic                                                   o_noc_lt_axi_s_subip_wready;
  logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] o_noc_lt_axi_s_subip_bid;
  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_subip_bresp;
  logic                                                   o_noc_lt_axi_s_subip_bvalid;
  logic                                                   o_noc_lt_axi_s_subip_arready;
  logic [      aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] o_noc_lt_axi_s_subip_rid;
  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_noc_lt_axi_s_subip_rdata;
  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_subip_rresp;
  logic                                                   o_noc_lt_axi_s_subip_rlast;
  logic                                                   o_noc_lt_axi_s_subip_rvalid;

  axe_axi_multicut_flat #(
    .AxiAddrWidth(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiIdWidth(aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH),
    .AxiDataWidth(aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
    .NumCuts(1)
  ) o_noc_lt_axi_s_spill_flat (
    .i_clk            (i_clk),
    .i_rst_n          (i_rst_n),
    .i_axi_s_aw_id    (i_noc_lt_axi_s_awid),
    .i_axi_s_aw_addr  (i_noc_lt_axi_s_awaddr),
    .i_axi_s_aw_len   (i_noc_lt_axi_s_awlen),
    .i_axi_s_aw_size  (i_noc_lt_axi_s_awsize),
    .i_axi_s_aw_burst (i_noc_lt_axi_s_awburst),
    .i_axi_s_aw_lock  (i_noc_lt_axi_s_awlock),
    .i_axi_s_aw_cache (i_noc_lt_axi_s_awcache),
    .i_axi_s_aw_prot  (i_noc_lt_axi_s_awprot),
    .i_axi_s_aw_qos   ('0),
    .i_axi_s_aw_region('0),
    .i_axi_s_aw_user  ('0),
    .i_axi_s_aw_valid (i_noc_lt_axi_s_awvalid),
    .o_axi_s_aw_ready (o_noc_lt_axi_s_awready),
    .i_axi_s_w_data   (i_noc_lt_axi_s_wdata),
    .i_axi_s_w_strb   (i_noc_lt_axi_s_wstrb),
    .i_axi_s_w_last   (i_noc_lt_axi_s_wlast),
    .i_axi_s_w_user   ('0),
    .i_axi_s_w_valid  (i_noc_lt_axi_s_wvalid),
    .o_axi_s_w_ready  (o_noc_lt_axi_s_wready),
    .o_axi_s_b_id     (o_noc_lt_axi_s_bid),
    .o_axi_s_b_resp   (o_noc_lt_axi_s_bresp),
    .o_axi_s_b_user   (),
    .o_axi_s_b_valid  (o_noc_lt_axi_s_bvalid),
    .i_axi_s_b_ready  (i_noc_lt_axi_s_bready),
    .i_axi_s_ar_id    (i_noc_lt_axi_s_arid),
    .i_axi_s_ar_addr  (i_noc_lt_axi_s_araddr),
    .i_axi_s_ar_len   (i_noc_lt_axi_s_arlen),
    .i_axi_s_ar_size  (i_noc_lt_axi_s_arsize),
    .i_axi_s_ar_burst (i_noc_lt_axi_s_arburst),
    .i_axi_s_ar_lock  (i_noc_lt_axi_s_arlock),
    .i_axi_s_ar_cache (i_noc_lt_axi_s_arcache),
    .i_axi_s_ar_prot  (i_noc_lt_axi_s_arprot),
    .i_axi_s_ar_qos   ('0),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user  ('0),
    .i_axi_s_ar_valid (i_noc_lt_axi_s_arvalid),
    .o_axi_s_ar_ready (o_noc_lt_axi_s_arready),
    .o_axi_s_r_id     (o_noc_lt_axi_s_rid),
    .o_axi_s_r_data   (o_noc_lt_axi_s_rdata),
    .o_axi_s_r_resp   (o_noc_lt_axi_s_rresp),
    .o_axi_s_r_last   (o_noc_lt_axi_s_rlast),
    .o_axi_s_r_user   (),
    .o_axi_s_r_valid  (o_noc_lt_axi_s_rvalid),
    .i_axi_s_r_ready  (i_noc_lt_axi_s_rready),
    .o_axi_m_aw_id    (i_noc_lt_axi_s_subip_awid),
    .o_axi_m_aw_addr  (i_noc_lt_axi_s_subip_awaddr),
    .o_axi_m_aw_len   (i_noc_lt_axi_s_subip_awlen),
    .o_axi_m_aw_size  (i_noc_lt_axi_s_subip_awsize),
    .o_axi_m_aw_burst (i_noc_lt_axi_s_subip_awburst),
    .o_axi_m_aw_lock  (i_noc_lt_axi_s_subip_awlock),
    .o_axi_m_aw_cache (i_noc_lt_axi_s_subip_awcache),
    .o_axi_m_aw_prot  (i_noc_lt_axi_s_subip_awprot),
    .o_axi_m_aw_qos   (),
    .o_axi_m_aw_region(),
    .o_axi_m_aw_valid (i_noc_lt_axi_s_subip_awvalid),
    .o_axi_m_aw_user  (),
    .i_axi_m_aw_ready (o_noc_lt_axi_s_subip_awready),
    .o_axi_m_w_data   (i_noc_lt_axi_s_subip_wdata),
    .o_axi_m_w_strb   (i_noc_lt_axi_s_subip_wstrb),
    .o_axi_m_w_last   (i_noc_lt_axi_s_subip_wlast),
    .o_axi_m_w_user   (),
    .o_axi_m_w_valid  (i_noc_lt_axi_s_subip_wvalid),
    .i_axi_m_w_ready  (o_noc_lt_axi_s_subip_wready),
    .i_axi_m_b_id     (o_noc_lt_axi_s_subip_bid),
    .i_axi_m_b_resp   (o_noc_lt_axi_s_subip_bresp),
    .i_axi_m_b_user   ('0),
    .i_axi_m_b_valid  (o_noc_lt_axi_s_subip_bvalid),
    .o_axi_m_b_ready  (i_noc_lt_axi_s_subip_bready),
    .o_axi_m_ar_id    (i_noc_lt_axi_s_subip_arid),
    .o_axi_m_ar_addr  (i_noc_lt_axi_s_subip_araddr),
    .o_axi_m_ar_len   (i_noc_lt_axi_s_subip_arlen),
    .o_axi_m_ar_size  (i_noc_lt_axi_s_subip_arsize),
    .o_axi_m_ar_burst (i_noc_lt_axi_s_subip_arburst),
    .o_axi_m_ar_lock  (i_noc_lt_axi_s_subip_arlock),
    .o_axi_m_ar_cache (i_noc_lt_axi_s_subip_arcache),
    .o_axi_m_ar_prot  (i_noc_lt_axi_s_subip_arprot),
    .o_axi_m_ar_qos   (),
    .o_axi_m_ar_region(),
    .o_axi_m_ar_user  (),
    .o_axi_m_ar_valid (i_noc_lt_axi_s_subip_arvalid),
    .i_axi_m_ar_ready (o_noc_lt_axi_s_subip_arready),
    .i_axi_m_r_id     (o_noc_lt_axi_s_subip_rid),
    .i_axi_m_r_data   (o_noc_lt_axi_s_subip_rdata),
    .i_axi_m_r_resp   (o_noc_lt_axi_s_subip_rresp),
    .i_axi_m_r_last   (o_noc_lt_axi_s_subip_rlast),
    .i_axi_m_r_user   ('0),
    .i_axi_m_r_valid  (o_noc_lt_axi_s_subip_rvalid),
    .o_axi_m_r_ready  (i_noc_lt_axi_s_subip_rready)
  );
  //-------------------------------
  // AXI SPILL for o_noc_lt_axi_m
  //-------------------------------
  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_noc_lt_axi_m_subip_awid;
  logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_noc_lt_axi_m_subip_awaddr;
  logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_noc_lt_axi_m_subip_awlen;
  logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_subip_awsize;
  logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_subip_awburst;
  logic                                                   o_noc_lt_axi_m_subip_awlock;
  logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_subip_awcache;
  logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_subip_awprot;
  logic                                                   o_noc_lt_axi_m_subip_awvalid;
  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_noc_lt_axi_m_subip_wdata;
  logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] o_noc_lt_axi_m_subip_wstrb;
  logic                                                   o_noc_lt_axi_m_subip_wlast;
  logic                                                   o_noc_lt_axi_m_subip_wvalid;
  logic                                                   o_noc_lt_axi_m_subip_bready;
  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_noc_lt_axi_m_subip_arid;
  logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_noc_lt_axi_m_subip_araddr;
  logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_noc_lt_axi_m_subip_arlen;
  logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_subip_arsize;
  logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_subip_arburst;
  logic                                                   o_noc_lt_axi_m_subip_arlock;
  logic [     aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_subip_arcache;
  logic [      aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_subip_arprot;
  logic                                                   o_noc_lt_axi_m_subip_arvalid;
  logic                                                   o_noc_lt_axi_m_subip_rready;


  //-------------------------------
  // AXI SPILL for i_noc_lt_axi_m
  //-------------------------------
  logic                                                   i_noc_lt_axi_m_subip_awready;
  logic                                                   i_noc_lt_axi_m_subip_wready;
  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_noc_lt_axi_m_subip_bid;
  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_subip_bresp;
  logic                                                   i_noc_lt_axi_m_subip_bvalid;
  logic                                                   i_noc_lt_axi_m_subip_arready;
  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_noc_lt_axi_m_subip_rid;
  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_noc_lt_axi_m_subip_rdata;
  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_subip_rresp;
  logic                                                   i_noc_lt_axi_m_subip_rlast;
  logic                                                   i_noc_lt_axi_m_subip_rvalid;

  axe_axi_multicut_flat #(
    .AxiAddrWidth(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiIdWidth(aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH),
    .AxiDataWidth(aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
    .NumCuts(1)
  ) i_noc_lt_axi_m_spill_flat (
    .i_clk            (i_clk),
    .i_rst_n          (i_rst_n),
    .i_axi_s_aw_id    (o_noc_lt_axi_m_subip_awid),
    .i_axi_s_aw_addr  (o_noc_lt_axi_m_subip_awaddr),
    .i_axi_s_aw_len   (o_noc_lt_axi_m_subip_awlen),
    .i_axi_s_aw_size  (o_noc_lt_axi_m_subip_awsize),
    .i_axi_s_aw_burst (o_noc_lt_axi_m_subip_awburst),
    .i_axi_s_aw_lock  (o_noc_lt_axi_m_subip_awlock),
    .i_axi_s_aw_cache (o_noc_lt_axi_m_subip_awcache),
    .i_axi_s_aw_prot  (o_noc_lt_axi_m_subip_awprot),
    .i_axi_s_aw_qos   ('0),
    .i_axi_s_aw_region('0),
    .i_axi_s_aw_user  ('0),
    .i_axi_s_aw_valid (o_noc_lt_axi_m_subip_awvalid),
    .o_axi_s_aw_ready (i_noc_lt_axi_m_subip_awready),
    .i_axi_s_w_data   (o_noc_lt_axi_m_subip_wdata),
    .i_axi_s_w_strb   (o_noc_lt_axi_m_subip_wstrb),
    .i_axi_s_w_last   (o_noc_lt_axi_m_subip_wlast),
    .i_axi_s_w_user   ('0),
    .i_axi_s_w_valid  (o_noc_lt_axi_m_subip_wvalid),
    .o_axi_s_w_ready  (i_noc_lt_axi_m_subip_wready),
    .o_axi_s_b_id     (i_noc_lt_axi_m_subip_bid),
    .o_axi_s_b_resp   (i_noc_lt_axi_m_subip_bresp),
    .o_axi_s_b_user   (),
    .o_axi_s_b_valid  (i_noc_lt_axi_m_subip_bvalid),
    .i_axi_s_b_ready  (o_noc_lt_axi_m_subip_bready),
    .i_axi_s_ar_id    (o_noc_lt_axi_m_subip_arid),
    .i_axi_s_ar_addr  (o_noc_lt_axi_m_subip_araddr),
    .i_axi_s_ar_len   (o_noc_lt_axi_m_subip_arlen),
    .i_axi_s_ar_size  (o_noc_lt_axi_m_subip_arsize),
    .i_axi_s_ar_burst (o_noc_lt_axi_m_subip_arburst),
    .i_axi_s_ar_lock  (o_noc_lt_axi_m_subip_arlock),
    .i_axi_s_ar_cache (o_noc_lt_axi_m_subip_arcache),
    .i_axi_s_ar_prot  (o_noc_lt_axi_m_subip_arprot),
    .i_axi_s_ar_qos   ('0),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user  ('0),
    .i_axi_s_ar_valid (o_noc_lt_axi_m_subip_arvalid),
    .o_axi_s_ar_ready (i_noc_lt_axi_m_subip_arready),
    .o_axi_s_r_id     (i_noc_lt_axi_m_subip_rid),
    .o_axi_s_r_data   (i_noc_lt_axi_m_subip_rdata),
    .o_axi_s_r_resp   (i_noc_lt_axi_m_subip_rresp),
    .o_axi_s_r_last   (i_noc_lt_axi_m_subip_rlast),
    .o_axi_s_r_user   (),
    .o_axi_s_r_valid  (i_noc_lt_axi_m_subip_rvalid),
    .i_axi_s_r_ready  (o_noc_lt_axi_m_subip_rready),
    .o_axi_m_aw_id    (o_noc_lt_axi_m_awid),
    .o_axi_m_aw_addr  (o_noc_lt_axi_m_awaddr),
    .o_axi_m_aw_len   (o_noc_lt_axi_m_awlen),
    .o_axi_m_aw_size  (o_noc_lt_axi_m_awsize),
    .o_axi_m_aw_burst (o_noc_lt_axi_m_awburst),
    .o_axi_m_aw_lock  (o_noc_lt_axi_m_awlock),
    .o_axi_m_aw_cache (o_noc_lt_axi_m_awcache),
    .o_axi_m_aw_prot  (o_noc_lt_axi_m_awprot),
    .o_axi_m_aw_qos   (),
    .o_axi_m_aw_region(),
    .o_axi_m_aw_valid (o_noc_lt_axi_m_awvalid),
    .o_axi_m_aw_user  (),
    .i_axi_m_aw_ready (i_noc_lt_axi_m_awready),
    .o_axi_m_w_data   (o_noc_lt_axi_m_wdata),
    .o_axi_m_w_strb   (o_noc_lt_axi_m_wstrb),
    .o_axi_m_w_last   (o_noc_lt_axi_m_wlast),
    .o_axi_m_w_user   (),
    .o_axi_m_w_valid  (o_noc_lt_axi_m_wvalid),
    .i_axi_m_w_ready  (i_noc_lt_axi_m_wready),
    .i_axi_m_b_id     (i_noc_lt_axi_m_bid),
    .i_axi_m_b_resp   (i_noc_lt_axi_m_bresp),
    .i_axi_m_b_user   ('0),
    .i_axi_m_b_valid  (i_noc_lt_axi_m_bvalid),
    .o_axi_m_b_ready  (o_noc_lt_axi_m_bready),
    .o_axi_m_ar_id    (o_noc_lt_axi_m_arid),
    .o_axi_m_ar_addr  (o_noc_lt_axi_m_araddr),
    .o_axi_m_ar_len   (o_noc_lt_axi_m_arlen),
    .o_axi_m_ar_size  (o_noc_lt_axi_m_arsize),
    .o_axi_m_ar_burst (o_noc_lt_axi_m_arburst),
    .o_axi_m_ar_lock  (o_noc_lt_axi_m_arlock),
    .o_axi_m_ar_cache (o_noc_lt_axi_m_arcache),
    .o_axi_m_ar_prot  (o_noc_lt_axi_m_arprot),
    .o_axi_m_ar_qos   (),
    .o_axi_m_ar_region(),
    .o_axi_m_ar_user  (),
    .o_axi_m_ar_valid (o_noc_lt_axi_m_arvalid),
    .i_axi_m_ar_ready (i_noc_lt_axi_m_arready),
    .i_axi_m_r_id     (i_noc_lt_axi_m_rid),
    .i_axi_m_r_data   (i_noc_lt_axi_m_rdata),
    .i_axi_m_r_resp   (i_noc_lt_axi_m_rresp),
    .i_axi_m_r_last   (i_noc_lt_axi_m_rlast),
    .i_axi_m_r_user   ('0),
    .i_axi_m_r_valid  (i_noc_lt_axi_m_rvalid),
    .o_axi_m_r_ready  (o_noc_lt_axi_m_rready)
  );
  //-------------------------------
  // AXI SPILL for o_dmc_l1_lt_axi_m
  //-------------------------------
  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_awid;
  logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_awaddr;
  logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_awlen;
  logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_awsize;
  logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_awburst;
  logic                                                   o_dmc_l1_lt_axi_m_subip_awvalid;
  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_wdata;
  logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_wstrb;
  logic                                                   o_dmc_l1_lt_axi_m_subip_wlast;
  logic                                                   o_dmc_l1_lt_axi_m_subip_wvalid;
  logic                                                   o_dmc_l1_lt_axi_m_subip_bready;
  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_arid;
  logic [      aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_araddr;
  logic [       aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_arlen;
  logic [      aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_arsize;
  logic [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_dmc_l1_lt_axi_m_subip_arburst;
  logic                                                   o_dmc_l1_lt_axi_m_subip_arvalid;
  logic                                                   o_dmc_l1_lt_axi_m_subip_rready;


  //-------------------------------
  // AXI SPILL for i_dmc_l1_lt_axi_m
  //-------------------------------
  logic                                                   i_dmc_l1_lt_axi_m_subip_awready;
  logic                                                   i_dmc_l1_lt_axi_m_subip_wready;
  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_lt_axi_m_subip_bid;
  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_dmc_l1_lt_axi_m_subip_bresp;
  logic                                                   i_dmc_l1_lt_axi_m_subip_bvalid;
  logic                                                   i_dmc_l1_lt_axi_m_subip_arready;
  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_dmc_l1_lt_axi_m_subip_rid;
  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_dmc_l1_lt_axi_m_subip_rdata;
  logic [      aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_dmc_l1_lt_axi_m_subip_rresp;
  logic                                                   i_dmc_l1_lt_axi_m_subip_rlast;
  logic                                                   i_dmc_l1_lt_axi_m_subip_rvalid;

  axe_axi_multicut_flat #(
    .AxiAddrWidth(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH),
    .AxiIdWidth(aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH),
    .AxiDataWidth(aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
    .NumCuts(1)
  ) i_dmc_l1_lt_axi_m_spill_flat (
    .i_clk            (i_clk),
    .i_rst_n          (i_rst_n),
    .i_axi_s_aw_id    (o_dmc_l1_lt_axi_m_subip_awid),
    .i_axi_s_aw_addr  (o_dmc_l1_lt_axi_m_subip_awaddr),
    .i_axi_s_aw_len   (o_dmc_l1_lt_axi_m_subip_awlen),
    .i_axi_s_aw_size  (o_dmc_l1_lt_axi_m_subip_awsize),
    .i_axi_s_aw_burst (o_dmc_l1_lt_axi_m_subip_awburst),
    .i_axi_s_aw_lock  ('0),
    .i_axi_s_aw_cache ('0),
    .i_axi_s_aw_prot  ('0),
    .i_axi_s_aw_qos   ('0),
    .i_axi_s_aw_region('0),
    .i_axi_s_aw_user  ('0),
    .i_axi_s_aw_valid (o_dmc_l1_lt_axi_m_subip_awvalid),
    .o_axi_s_aw_ready (i_dmc_l1_lt_axi_m_subip_awready),
    .i_axi_s_w_data   (o_dmc_l1_lt_axi_m_subip_wdata),
    .i_axi_s_w_strb   (o_dmc_l1_lt_axi_m_subip_wstrb),
    .i_axi_s_w_last   (o_dmc_l1_lt_axi_m_subip_wlast),
    .i_axi_s_w_user   ('0),
    .i_axi_s_w_valid  (o_dmc_l1_lt_axi_m_subip_wvalid),
    .o_axi_s_w_ready  (i_dmc_l1_lt_axi_m_subip_wready),
    .o_axi_s_b_id     (i_dmc_l1_lt_axi_m_subip_bid),
    .o_axi_s_b_resp   (i_dmc_l1_lt_axi_m_subip_bresp),
    .o_axi_s_b_user   (),
    .o_axi_s_b_valid  (i_dmc_l1_lt_axi_m_subip_bvalid),
    .i_axi_s_b_ready  (o_dmc_l1_lt_axi_m_subip_bready),
    .i_axi_s_ar_id    (o_dmc_l1_lt_axi_m_subip_arid),
    .i_axi_s_ar_addr  (o_dmc_l1_lt_axi_m_subip_araddr),
    .i_axi_s_ar_len   (o_dmc_l1_lt_axi_m_subip_arlen),
    .i_axi_s_ar_size  (o_dmc_l1_lt_axi_m_subip_arsize),
    .i_axi_s_ar_burst (o_dmc_l1_lt_axi_m_subip_arburst),
    .i_axi_s_ar_lock  ('0),
    .i_axi_s_ar_cache ('0),
    .i_axi_s_ar_prot  ('0),
    .i_axi_s_ar_qos   ('0),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user  ('0),
    .i_axi_s_ar_valid (o_dmc_l1_lt_axi_m_subip_arvalid),
    .o_axi_s_ar_ready (i_dmc_l1_lt_axi_m_subip_arready),
    .o_axi_s_r_id     (i_dmc_l1_lt_axi_m_subip_rid),
    .o_axi_s_r_data   (i_dmc_l1_lt_axi_m_subip_rdata),
    .o_axi_s_r_resp   (i_dmc_l1_lt_axi_m_subip_rresp),
    .o_axi_s_r_last   (i_dmc_l1_lt_axi_m_subip_rlast),
    .o_axi_s_r_user   (),
    .o_axi_s_r_valid  (i_dmc_l1_lt_axi_m_subip_rvalid),
    .i_axi_s_r_ready  (o_dmc_l1_lt_axi_m_subip_rready),
    .o_axi_m_aw_id    (o_dmc_l1_lt_axi_m_awid),
    .o_axi_m_aw_addr  (o_dmc_l1_lt_axi_m_awaddr),
    .o_axi_m_aw_len   (o_dmc_l1_lt_axi_m_awlen),
    .o_axi_m_aw_size  (o_dmc_l1_lt_axi_m_awsize),
    .o_axi_m_aw_burst (o_dmc_l1_lt_axi_m_awburst),
    .o_axi_m_aw_lock  (),
    .o_axi_m_aw_cache (),
    .o_axi_m_aw_prot  (),
    .o_axi_m_aw_qos   (),
    .o_axi_m_aw_region(),
    .o_axi_m_aw_valid (o_dmc_l1_lt_axi_m_awvalid),
    .o_axi_m_aw_user  (),
    .i_axi_m_aw_ready (i_dmc_l1_lt_axi_m_awready),
    .o_axi_m_w_data   (o_dmc_l1_lt_axi_m_wdata),
    .o_axi_m_w_strb   (o_dmc_l1_lt_axi_m_wstrb),
    .o_axi_m_w_last   (o_dmc_l1_lt_axi_m_wlast),
    .o_axi_m_w_user   (),
    .o_axi_m_w_valid  (o_dmc_l1_lt_axi_m_wvalid),
    .i_axi_m_w_ready  (i_dmc_l1_lt_axi_m_wready),
    .i_axi_m_b_id     (i_dmc_l1_lt_axi_m_bid),
    .i_axi_m_b_resp   (i_dmc_l1_lt_axi_m_bresp),
    .i_axi_m_b_user   ('0),
    .i_axi_m_b_valid  (i_dmc_l1_lt_axi_m_bvalid),
    .o_axi_m_b_ready  (o_dmc_l1_lt_axi_m_bready),
    .o_axi_m_ar_id    (o_dmc_l1_lt_axi_m_arid),
    .o_axi_m_ar_addr  (o_dmc_l1_lt_axi_m_araddr),
    .o_axi_m_ar_len   (o_dmc_l1_lt_axi_m_arlen),
    .o_axi_m_ar_size  (o_dmc_l1_lt_axi_m_arsize),
    .o_axi_m_ar_burst (o_dmc_l1_lt_axi_m_arburst),
    .o_axi_m_ar_lock  (),
    .o_axi_m_ar_cache (),
    .o_axi_m_ar_prot  (),
    .o_axi_m_ar_qos   (),
    .o_axi_m_ar_region(),
    .o_axi_m_ar_user  (),
    .o_axi_m_ar_valid (o_dmc_l1_lt_axi_m_arvalid),
    .i_axi_m_ar_ready (i_dmc_l1_lt_axi_m_arready),
    .i_axi_m_r_id     (i_dmc_l1_lt_axi_m_rid),
    .i_axi_m_r_data   (i_dmc_l1_lt_axi_m_rdata),
    .i_axi_m_r_resp   (i_dmc_l1_lt_axi_m_rresp),
    .i_axi_m_r_last   (i_dmc_l1_lt_axi_m_rlast),
    .i_axi_m_r_user   ('0),
    .i_axi_m_r_valid  (i_dmc_l1_lt_axi_m_rvalid),
    .o_axi_m_r_ready  (o_dmc_l1_lt_axi_m_rready)
  );
  //-------------------------------
  // Wrapped module instantiation
  //-------------------------------
  aic_infra u_aic_infra (
    .i_clk                           (i_clk),
    .i_rst_n                         (i_rst_n),
    .i_scan_en                       (scan_en),
    .i_cid                           (i_cid),
    .i_inter_core_sync               (i_inter_core_sync),
    .i_thermal_warning_async         (i_thermal_warning_async),
    .o_reserved                      (o_reserved),
    .i_reserved                      (i_reserved),
    .i_mvm_exe_obs                   (i_mvm_exe_obs),
    .i_mvm_prg_obs                   (i_mvm_prg_obs),
    .i_m_iau_obs                     (i_m_iau_obs),
    .i_m_dpu_obs                     (i_m_dpu_obs),
    .i_tu_obs                        (i_tu_obs),
    .i_dwpu_obs                      (i_dwpu_obs),
    .i_d_iau_obs                     (i_d_iau_obs),
    .i_d_dpu_obs                     (i_d_dpu_obs),
    .i_dmc_obs                       (i_dmc_obs),
    .o_aic_obs                       (o_aic_obs),
    .i_dmc_ts_start                  (i_dmc_ts_start),
    .i_dmc_ts_end                    (i_dmc_ts_end),
    .i_did_ts_start                  (i_did_ts_start),
    .i_did_ts_end                    (i_did_ts_end),
    .i_mid_ts_start                  (i_mid_ts_start),
    .i_mid_ts_end                    (i_mid_ts_end),
    .i_dmc_acd_sync                  (i_dmc_acd_sync),
    .i_did_acd_sync                  (i_did_acd_sync),
    .i_mid_acd_sync                  (i_mid_acd_sync),
    .i_cva6v_boot_addr               (i_cva6v_boot_addr),
    .i_cva6v_debug_req_async         (i_cva6v_debug_req_async),
    .i_cva6v_debug_rst_halt_req_async(i_cva6v_debug_rst_halt_req_async),
    .o_cva6v_debug_stop_time_async   (o_cva6v_debug_stop_time_async),
    .o_cva6v_hart_unavail_async      (o_cva6v_hart_unavail_async),
    .o_cva6v_hart_under_reset_async  (o_cva6v_hart_under_reset_async),
    .i_mtip_async                    (i_mtip_async),
    .i_msip_async                    (i_msip_async),
    .o_rvv_0_req_valid               (o_rvv_0_req_valid),
    .i_rvv_0_req_ready               (i_rvv_0_req_ready),
    .o_rvv_0_req_addr                (o_rvv_0_req_addr),
    .o_rvv_0_req_we                  (o_rvv_0_req_we),
    .o_rvv_0_req_be                  (o_rvv_0_req_be),
    .o_rvv_0_req_wdata               (o_rvv_0_req_wdata),
    .i_rvv_0_res_valid               (i_rvv_0_res_valid),
    .i_rvv_0_res_rdata               (i_rvv_0_res_rdata),
    .i_rvv_0_res_err                 (i_rvv_0_res_err),
    .o_rvv_1_req_valid               (o_rvv_1_req_valid),
    .i_rvv_1_req_ready               (i_rvv_1_req_ready),
    .o_rvv_1_req_addr                (o_rvv_1_req_addr),
    .o_rvv_1_req_we                  (o_rvv_1_req_we),
    .o_rvv_1_req_be                  (o_rvv_1_req_be),
    .o_rvv_1_req_wdata               (o_rvv_1_req_wdata),
    .i_rvv_1_res_valid               (i_rvv_1_res_valid),
    .i_rvv_1_res_rdata               (i_rvv_1_res_rdata),
    .i_rvv_1_res_err                 (i_rvv_1_res_err),
    .o_rvv_2_req_valid               (o_rvv_2_req_valid),
    .i_rvv_2_req_ready               (i_rvv_2_req_ready),
    .o_rvv_2_req_addr                (o_rvv_2_req_addr),
    .o_rvv_2_req_we                  (o_rvv_2_req_we),
    .o_rvv_2_req_be                  (o_rvv_2_req_be),
    .o_rvv_2_req_wdata               (o_rvv_2_req_wdata),
    .i_rvv_2_res_valid               (i_rvv_2_res_valid),
    .i_rvv_2_res_rdata               (i_rvv_2_res_rdata),
    .i_rvv_2_res_err                 (i_rvv_2_res_err),
    .o_rvv_3_req_valid               (o_rvv_3_req_valid),
    .i_rvv_3_req_ready               (i_rvv_3_req_ready),
    .o_rvv_3_req_addr                (o_rvv_3_req_addr),
    .o_rvv_3_req_we                  (o_rvv_3_req_we),
    .o_rvv_3_req_be                  (o_rvv_3_req_be),
    .o_rvv_3_req_wdata               (o_rvv_3_req_wdata),
    .i_rvv_3_res_valid               (i_rvv_3_res_valid),
    .i_rvv_3_res_rdata               (i_rvv_3_res_rdata),
    .i_rvv_3_res_err                 (i_rvv_3_res_err),
    .o_rvv_4_req_valid               (o_rvv_4_req_valid),
    .i_rvv_4_req_ready               (i_rvv_4_req_ready),
    .o_rvv_4_req_addr                (o_rvv_4_req_addr),
    .o_rvv_4_req_we                  (o_rvv_4_req_we),
    .o_rvv_4_req_be                  (o_rvv_4_req_be),
    .o_rvv_4_req_wdata               (o_rvv_4_req_wdata),
    .i_rvv_4_res_valid               (i_rvv_4_res_valid),
    .i_rvv_4_res_rdata               (i_rvv_4_res_rdata),
    .i_rvv_4_res_err                 (i_rvv_4_res_err),
    .o_rvv_5_req_valid               (o_rvv_5_req_valid),
    .i_rvv_5_req_ready               (i_rvv_5_req_ready),
    .o_rvv_5_req_addr                (o_rvv_5_req_addr),
    .o_rvv_5_req_we                  (o_rvv_5_req_we),
    .o_rvv_5_req_be                  (o_rvv_5_req_be),
    .o_rvv_5_req_wdata               (o_rvv_5_req_wdata),
    .i_rvv_5_res_valid               (i_rvv_5_res_valid),
    .i_rvv_5_res_rdata               (i_rvv_5_res_rdata),
    .i_rvv_5_res_err                 (i_rvv_5_res_err),
    .o_rvv_6_req_valid               (o_rvv_6_req_valid),
    .i_rvv_6_req_ready               (i_rvv_6_req_ready),
    .o_rvv_6_req_addr                (o_rvv_6_req_addr),
    .o_rvv_6_req_we                  (o_rvv_6_req_we),
    .o_rvv_6_req_be                  (o_rvv_6_req_be),
    .o_rvv_6_req_wdata               (o_rvv_6_req_wdata),
    .i_rvv_6_res_valid               (i_rvv_6_res_valid),
    .i_rvv_6_res_rdata               (i_rvv_6_res_rdata),
    .i_rvv_6_res_err                 (i_rvv_6_res_err),
    .o_rvv_7_req_valid               (o_rvv_7_req_valid),
    .i_rvv_7_req_ready               (i_rvv_7_req_ready),
    .o_rvv_7_req_addr                (o_rvv_7_req_addr),
    .o_rvv_7_req_we                  (o_rvv_7_req_we),
    .o_rvv_7_req_be                  (o_rvv_7_req_be),
    .o_rvv_7_req_wdata               (o_rvv_7_req_wdata),
    .i_rvv_7_res_valid               (i_rvv_7_res_valid),
    .i_rvv_7_res_rdata               (i_rvv_7_res_rdata),
    .i_rvv_7_res_err                 (i_rvv_7_res_err),
    .i_irq_dmc                       (i_irq_dmc),
    .i_irq_aic_mid                   (i_irq_aic_mid),
    .i_irq_aic_did                   (i_irq_aic_did),
    .i_sram_mcs                      (i_sram_mcs),
    .i_sram_mcsw                     (i_sram_mcsw),
    .i_sram_ret                      (i_sram_ret),
    .i_sram_pde                      (i_sram_pde),
    .i_sram_se                       (scan_en),
    .i_sram_adme                     (i_sram_adme),
    .o_sram_prn                      (o_sram_prn),
    .o_tok_prod_ocpl_m_maddr         (o_tok_prod_ocpl_m_subip_maddr),
    .o_tok_prod_ocpl_m_mcmd          (o_tok_prod_ocpl_m_subip_mcmd),
    .o_tok_prod_ocpl_m_mdata         (o_tok_prod_ocpl_m_subip_mdata),
    .i_tok_prod_ocpl_m_scmdaccept    (i_tok_prod_ocpl_m_subip_scmdaccept),
    .i_tok_cons_ocpl_s_maddr         (i_tok_cons_ocpl_s_subip_maddr),
    .i_tok_cons_ocpl_s_mcmd          (i_tok_cons_ocpl_s_subip_mcmd),
    .i_tok_cons_ocpl_s_mdata         (i_tok_cons_ocpl_s_subip_mdata),
    .o_tok_cons_ocpl_s_scmdaccept    (o_tok_cons_ocpl_s_subip_scmdaccept),
    .i_m_ifd0_tok_prod_vld           (i_m_ifd0_tok_prod_subip_vld),
    .o_m_ifd0_tok_prod_rdy           (o_m_ifd0_tok_prod_subip_rdy),
    .o_m_ifd0_tok_cons_vld           (o_m_ifd0_tok_cons_subip_vld),
    .i_m_ifd0_tok_cons_rdy           (i_m_ifd0_tok_cons_subip_rdy),
    .i_m_ifd1_tok_prod_vld           (i_m_ifd1_tok_prod_subip_vld),
    .o_m_ifd1_tok_prod_rdy           (o_m_ifd1_tok_prod_subip_rdy),
    .o_m_ifd1_tok_cons_vld           (o_m_ifd1_tok_cons_subip_vld),
    .i_m_ifd1_tok_cons_rdy           (i_m_ifd1_tok_cons_subip_rdy),
    .i_m_ifd2_tok_prod_vld           (i_m_ifd2_tok_prod_subip_vld),
    .o_m_ifd2_tok_prod_rdy           (o_m_ifd2_tok_prod_subip_rdy),
    .o_m_ifd2_tok_cons_vld           (o_m_ifd2_tok_cons_subip_vld),
    .i_m_ifd2_tok_cons_rdy           (i_m_ifd2_tok_cons_subip_rdy),
    .i_m_ifdw_tok_prod_vld           (i_m_ifdw_tok_prod_subip_vld),
    .o_m_ifdw_tok_prod_rdy           (o_m_ifdw_tok_prod_subip_rdy),
    .o_m_ifdw_tok_cons_vld           (o_m_ifdw_tok_cons_subip_vld),
    .i_m_ifdw_tok_cons_rdy           (i_m_ifdw_tok_cons_subip_rdy),
    .i_d_ifd0_tok_prod_vld           (i_d_ifd0_tok_prod_subip_vld),
    .o_d_ifd0_tok_prod_rdy           (o_d_ifd0_tok_prod_subip_rdy),
    .o_d_ifd0_tok_cons_vld           (o_d_ifd0_tok_cons_subip_vld),
    .i_d_ifd0_tok_cons_rdy           (i_d_ifd0_tok_cons_subip_rdy),
    .i_d_ifd1_tok_prod_vld           (i_d_ifd1_tok_prod_subip_vld),
    .o_d_ifd1_tok_prod_rdy           (o_d_ifd1_tok_prod_subip_rdy),
    .o_d_ifd1_tok_cons_vld           (o_d_ifd1_tok_cons_subip_vld),
    .i_d_ifd1_tok_cons_rdy           (i_d_ifd1_tok_cons_subip_rdy),
    .i_m_odr_tok_prod_vld            (i_m_odr_tok_prod_subip_vld),
    .o_m_odr_tok_prod_rdy            (o_m_odr_tok_prod_subip_rdy),
    .o_m_odr_tok_cons_vld            (o_m_odr_tok_cons_subip_vld),
    .i_m_odr_tok_cons_rdy            (i_m_odr_tok_cons_subip_rdy),
    .i_d_odr_tok_prod_vld            (i_d_odr_tok_prod_subip_vld),
    .o_d_odr_tok_prod_rdy            (o_d_odr_tok_prod_subip_rdy),
    .o_d_odr_tok_cons_vld            (o_d_odr_tok_cons_subip_vld),
    .i_d_odr_tok_cons_rdy            (i_d_odr_tok_cons_subip_rdy),
    .i_mvm_exe_tok_prod_vld          (i_mvm_exe_tok_prod_subip_vld),
    .o_mvm_exe_tok_prod_rdy          (o_mvm_exe_tok_prod_subip_rdy),
    .o_mvm_exe_tok_cons_vld          (o_mvm_exe_tok_cons_subip_vld),
    .i_mvm_exe_tok_cons_rdy          (i_mvm_exe_tok_cons_subip_rdy),
    .i_mvm_prg_tok_prod_vld          (i_mvm_prg_tok_prod_subip_vld),
    .o_mvm_prg_tok_prod_rdy          (o_mvm_prg_tok_prod_subip_rdy),
    .o_mvm_prg_tok_cons_vld          (o_mvm_prg_tok_cons_subip_vld),
    .i_mvm_prg_tok_cons_rdy          (i_mvm_prg_tok_cons_subip_rdy),
    .i_m_iau_tok_prod_vld            (i_m_iau_tok_prod_subip_vld),
    .o_m_iau_tok_prod_rdy            (o_m_iau_tok_prod_subip_rdy),
    .o_m_iau_tok_cons_vld            (o_m_iau_tok_cons_subip_vld),
    .i_m_iau_tok_cons_rdy            (i_m_iau_tok_cons_subip_rdy),
    .i_m_dpu_tok_prod_vld            (i_m_dpu_tok_prod_subip_vld),
    .o_m_dpu_tok_prod_rdy            (o_m_dpu_tok_prod_subip_rdy),
    .o_m_dpu_tok_cons_vld            (o_m_dpu_tok_cons_subip_vld),
    .i_m_dpu_tok_cons_rdy            (i_m_dpu_tok_cons_subip_rdy),
    .i_dwpu_tok_prod_vld             (i_dwpu_tok_prod_subip_vld),
    .o_dwpu_tok_prod_rdy             (o_dwpu_tok_prod_subip_rdy),
    .o_dwpu_tok_cons_vld             (o_dwpu_tok_cons_subip_vld),
    .i_dwpu_tok_cons_rdy             (i_dwpu_tok_cons_subip_rdy),
    .i_d_iau_tok_prod_vld            (i_d_iau_tok_prod_subip_vld),
    .o_d_iau_tok_prod_rdy            (o_d_iau_tok_prod_subip_rdy),
    .o_d_iau_tok_cons_vld            (o_d_iau_tok_cons_subip_vld),
    .i_d_iau_tok_cons_rdy            (i_d_iau_tok_cons_subip_rdy),
    .i_d_dpu_tok_prod_vld            (i_d_dpu_tok_prod_subip_vld),
    .o_d_dpu_tok_prod_rdy            (o_d_dpu_tok_prod_subip_rdy),
    .o_d_dpu_tok_cons_vld            (o_d_dpu_tok_cons_subip_vld),
    .i_d_dpu_tok_cons_rdy            (i_d_dpu_tok_cons_subip_rdy),
    .o_noc_ht_axi_m_awvalid          (o_noc_ht_axi_m_subip_awvalid),
    .o_noc_ht_axi_m_awaddr           (o_noc_ht_axi_m_subip_awaddr),
    .o_noc_ht_axi_m_awid             (o_noc_ht_axi_m_subip_awid),
    .o_noc_ht_axi_m_awlen            (o_noc_ht_axi_m_subip_awlen),
    .o_noc_ht_axi_m_awsize           (o_noc_ht_axi_m_subip_awsize),
    .o_noc_ht_axi_m_awburst          (o_noc_ht_axi_m_subip_awburst),
    .o_noc_ht_axi_m_awcache          (o_noc_ht_axi_m_subip_awcache),
    .o_noc_ht_axi_m_awprot           (o_noc_ht_axi_m_subip_awprot),
    .o_noc_ht_axi_m_awlock           (o_noc_ht_axi_m_subip_awlock),
    .o_noc_ht_axi_m_wvalid           (o_noc_ht_axi_m_subip_wvalid),
    .o_noc_ht_axi_m_wlast            (o_noc_ht_axi_m_subip_wlast),
    .o_noc_ht_axi_m_wstrb            (o_noc_ht_axi_m_subip_wstrb),
    .o_noc_ht_axi_m_wdata            (o_noc_ht_axi_m_subip_wdata),
    .o_noc_ht_axi_m_bready           (o_noc_ht_axi_m_subip_bready),
    .o_noc_ht_axi_m_arvalid          (o_noc_ht_axi_m_subip_arvalid),
    .o_noc_ht_axi_m_araddr           (o_noc_ht_axi_m_subip_araddr),
    .o_noc_ht_axi_m_arid             (o_noc_ht_axi_m_subip_arid),
    .o_noc_ht_axi_m_arlen            (o_noc_ht_axi_m_subip_arlen),
    .o_noc_ht_axi_m_arsize           (o_noc_ht_axi_m_subip_arsize),
    .o_noc_ht_axi_m_arburst          (o_noc_ht_axi_m_subip_arburst),
    .o_noc_ht_axi_m_arcache          (o_noc_ht_axi_m_subip_arcache),
    .o_noc_ht_axi_m_arprot           (o_noc_ht_axi_m_subip_arprot),
    .o_noc_ht_axi_m_arlock           (o_noc_ht_axi_m_subip_arlock),
    .o_noc_ht_axi_m_rready           (o_noc_ht_axi_m_subip_rready),
    .i_noc_ht_axi_m_awready          (i_noc_ht_axi_m_subip_awready),
    .i_noc_ht_axi_m_wready           (i_noc_ht_axi_m_subip_wready),
    .i_noc_ht_axi_m_bvalid           (i_noc_ht_axi_m_subip_bvalid),
    .i_noc_ht_axi_m_bid              (i_noc_ht_axi_m_subip_bid),
    .i_noc_ht_axi_m_bresp            (i_noc_ht_axi_m_subip_bresp),
    .i_noc_ht_axi_m_arready          (i_noc_ht_axi_m_subip_arready),
    .i_noc_ht_axi_m_rvalid           (i_noc_ht_axi_m_subip_rvalid),
    .i_noc_ht_axi_m_rlast            (i_noc_ht_axi_m_subip_rlast),
    .i_noc_ht_axi_m_rid              (i_noc_ht_axi_m_subip_rid),
    .i_noc_ht_axi_m_rdata            (i_noc_ht_axi_m_subip_rdata),
    .i_noc_ht_axi_m_rresp            (i_noc_ht_axi_m_subip_rresp),
    .o_dmc_l1_ht_axi_m_awvalid       (o_dmc_l1_ht_axi_m_subip_awvalid),
    .o_dmc_l1_ht_axi_m_awaddr        (o_dmc_l1_ht_axi_m_subip_awaddr),
    .o_dmc_l1_ht_axi_m_awid          (o_dmc_l1_ht_axi_m_subip_awid),
    .o_dmc_l1_ht_axi_m_awlen         (o_dmc_l1_ht_axi_m_subip_awlen),
    .o_dmc_l1_ht_axi_m_awsize        (o_dmc_l1_ht_axi_m_subip_awsize),
    .o_dmc_l1_ht_axi_m_awburst       (o_dmc_l1_ht_axi_m_subip_awburst),
    .o_dmc_l1_ht_axi_m_awcache       (o_dmc_l1_ht_axi_m_subip_awcache),
    .o_dmc_l1_ht_axi_m_awprot        (o_dmc_l1_ht_axi_m_subip_awprot),
    .o_dmc_l1_ht_axi_m_awlock        (o_dmc_l1_ht_axi_m_subip_awlock),
    .o_dmc_l1_ht_axi_m_wvalid        (o_dmc_l1_ht_axi_m_subip_wvalid),
    .o_dmc_l1_ht_axi_m_wlast         (o_dmc_l1_ht_axi_m_subip_wlast),
    .o_dmc_l1_ht_axi_m_wstrb         (o_dmc_l1_ht_axi_m_subip_wstrb),
    .o_dmc_l1_ht_axi_m_wdata         (o_dmc_l1_ht_axi_m_subip_wdata),
    .o_dmc_l1_ht_axi_m_bready        (o_dmc_l1_ht_axi_m_subip_bready),
    .o_dmc_l1_ht_axi_m_arvalid       (o_dmc_l1_ht_axi_m_subip_arvalid),
    .o_dmc_l1_ht_axi_m_araddr        (o_dmc_l1_ht_axi_m_subip_araddr),
    .o_dmc_l1_ht_axi_m_arid          (o_dmc_l1_ht_axi_m_subip_arid),
    .o_dmc_l1_ht_axi_m_arlen         (o_dmc_l1_ht_axi_m_subip_arlen),
    .o_dmc_l1_ht_axi_m_arsize        (o_dmc_l1_ht_axi_m_subip_arsize),
    .o_dmc_l1_ht_axi_m_arburst       (o_dmc_l1_ht_axi_m_subip_arburst),
    .o_dmc_l1_ht_axi_m_arcache       (o_dmc_l1_ht_axi_m_subip_arcache),
    .o_dmc_l1_ht_axi_m_arprot        (o_dmc_l1_ht_axi_m_subip_arprot),
    .o_dmc_l1_ht_axi_m_arlock        (o_dmc_l1_ht_axi_m_subip_arlock),
    .o_dmc_l1_ht_axi_m_rready        (o_dmc_l1_ht_axi_m_subip_rready),
    .i_dmc_l1_ht_axi_m_awready       (i_dmc_l1_ht_axi_m_subip_awready),
    .i_dmc_l1_ht_axi_m_wready        (i_dmc_l1_ht_axi_m_subip_wready),
    .i_dmc_l1_ht_axi_m_bvalid        (i_dmc_l1_ht_axi_m_subip_bvalid),
    .i_dmc_l1_ht_axi_m_bid           (i_dmc_l1_ht_axi_m_subip_bid),
    .i_dmc_l1_ht_axi_m_bresp         (i_dmc_l1_ht_axi_m_subip_bresp),
    .i_dmc_l1_ht_axi_m_arready       (i_dmc_l1_ht_axi_m_subip_arready),
    .i_dmc_l1_ht_axi_m_rvalid        (i_dmc_l1_ht_axi_m_subip_rvalid),
    .i_dmc_l1_ht_axi_m_rlast         (i_dmc_l1_ht_axi_m_subip_rlast),
    .i_dmc_l1_ht_axi_m_rid           (i_dmc_l1_ht_axi_m_subip_rid),
    .i_dmc_l1_ht_axi_m_rdata         (i_dmc_l1_ht_axi_m_subip_rdata),
    .i_dmc_l1_ht_axi_m_rresp         (i_dmc_l1_ht_axi_m_subip_rresp),
    .i_noc_lt_axi_s_awvalid          (i_noc_lt_axi_s_subip_awvalid),
    .i_noc_lt_axi_s_awaddr           (i_noc_lt_axi_s_subip_awaddr),
    .i_noc_lt_axi_s_awid             (i_noc_lt_axi_s_subip_awid),
    .i_noc_lt_axi_s_awlen            (i_noc_lt_axi_s_subip_awlen),
    .i_noc_lt_axi_s_awsize           (i_noc_lt_axi_s_subip_awsize),
    .i_noc_lt_axi_s_awburst          (i_noc_lt_axi_s_subip_awburst),
    .i_noc_lt_axi_s_awcache          (i_noc_lt_axi_s_subip_awcache),
    .i_noc_lt_axi_s_awprot           (i_noc_lt_axi_s_subip_awprot),
    .i_noc_lt_axi_s_awlock           (i_noc_lt_axi_s_subip_awlock),
    .i_noc_lt_axi_s_wvalid           (i_noc_lt_axi_s_subip_wvalid),
    .i_noc_lt_axi_s_wlast            (i_noc_lt_axi_s_subip_wlast),
    .i_noc_lt_axi_s_wstrb            (i_noc_lt_axi_s_subip_wstrb),
    .i_noc_lt_axi_s_wdata            (i_noc_lt_axi_s_subip_wdata),
    .i_noc_lt_axi_s_bready           (i_noc_lt_axi_s_subip_bready),
    .i_noc_lt_axi_s_arvalid          (i_noc_lt_axi_s_subip_arvalid),
    .i_noc_lt_axi_s_araddr           (i_noc_lt_axi_s_subip_araddr),
    .i_noc_lt_axi_s_arid             (i_noc_lt_axi_s_subip_arid),
    .i_noc_lt_axi_s_arlen            (i_noc_lt_axi_s_subip_arlen),
    .i_noc_lt_axi_s_arsize           (i_noc_lt_axi_s_subip_arsize),
    .i_noc_lt_axi_s_arburst          (i_noc_lt_axi_s_subip_arburst),
    .i_noc_lt_axi_s_arcache          (i_noc_lt_axi_s_subip_arcache),
    .i_noc_lt_axi_s_arprot           (i_noc_lt_axi_s_subip_arprot),
    .i_noc_lt_axi_s_arlock           (i_noc_lt_axi_s_subip_arlock),
    .i_noc_lt_axi_s_rready           (i_noc_lt_axi_s_subip_rready),
    .o_noc_lt_axi_s_awready          (o_noc_lt_axi_s_subip_awready),
    .o_noc_lt_axi_s_wready           (o_noc_lt_axi_s_subip_wready),
    .o_noc_lt_axi_s_bvalid           (o_noc_lt_axi_s_subip_bvalid),
    .o_noc_lt_axi_s_bid              (o_noc_lt_axi_s_subip_bid),
    .o_noc_lt_axi_s_bresp            (o_noc_lt_axi_s_subip_bresp),
    .o_noc_lt_axi_s_arready          (o_noc_lt_axi_s_subip_arready),
    .o_noc_lt_axi_s_rvalid           (o_noc_lt_axi_s_subip_rvalid),
    .o_noc_lt_axi_s_rlast            (o_noc_lt_axi_s_subip_rlast),
    .o_noc_lt_axi_s_rid              (o_noc_lt_axi_s_subip_rid),
    .o_noc_lt_axi_s_rdata            (o_noc_lt_axi_s_subip_rdata),
    .o_noc_lt_axi_s_rresp            (o_noc_lt_axi_s_subip_rresp),
    .o_noc_lt_axi_m_awvalid          (o_noc_lt_axi_m_subip_awvalid),
    .o_noc_lt_axi_m_awaddr           (o_noc_lt_axi_m_subip_awaddr),
    .o_noc_lt_axi_m_awid             (o_noc_lt_axi_m_subip_awid),
    .o_noc_lt_axi_m_awlen            (o_noc_lt_axi_m_subip_awlen),
    .o_noc_lt_axi_m_awsize           (o_noc_lt_axi_m_subip_awsize),
    .o_noc_lt_axi_m_awburst          (o_noc_lt_axi_m_subip_awburst),
    .o_noc_lt_axi_m_awcache          (o_noc_lt_axi_m_subip_awcache),
    .o_noc_lt_axi_m_awprot           (o_noc_lt_axi_m_subip_awprot),
    .o_noc_lt_axi_m_awlock           (o_noc_lt_axi_m_subip_awlock),
    .o_noc_lt_axi_m_wvalid           (o_noc_lt_axi_m_subip_wvalid),
    .o_noc_lt_axi_m_wlast            (o_noc_lt_axi_m_subip_wlast),
    .o_noc_lt_axi_m_wstrb            (o_noc_lt_axi_m_subip_wstrb),
    .o_noc_lt_axi_m_wdata            (o_noc_lt_axi_m_subip_wdata),
    .o_noc_lt_axi_m_bready           (o_noc_lt_axi_m_subip_bready),
    .o_noc_lt_axi_m_arvalid          (o_noc_lt_axi_m_subip_arvalid),
    .o_noc_lt_axi_m_araddr           (o_noc_lt_axi_m_subip_araddr),
    .o_noc_lt_axi_m_arid             (o_noc_lt_axi_m_subip_arid),
    .o_noc_lt_axi_m_arlen            (o_noc_lt_axi_m_subip_arlen),
    .o_noc_lt_axi_m_arsize           (o_noc_lt_axi_m_subip_arsize),
    .o_noc_lt_axi_m_arburst          (o_noc_lt_axi_m_subip_arburst),
    .o_noc_lt_axi_m_arcache          (o_noc_lt_axi_m_subip_arcache),
    .o_noc_lt_axi_m_arprot           (o_noc_lt_axi_m_subip_arprot),
    .o_noc_lt_axi_m_arlock           (o_noc_lt_axi_m_subip_arlock),
    .o_noc_lt_axi_m_rready           (o_noc_lt_axi_m_subip_rready),
    .i_noc_lt_axi_m_awready          (i_noc_lt_axi_m_subip_awready),
    .i_noc_lt_axi_m_wready           (i_noc_lt_axi_m_subip_wready),
    .i_noc_lt_axi_m_bvalid           (i_noc_lt_axi_m_subip_bvalid),
    .i_noc_lt_axi_m_bid              (i_noc_lt_axi_m_subip_bid),
    .i_noc_lt_axi_m_bresp            (i_noc_lt_axi_m_subip_bresp),
    .i_noc_lt_axi_m_arready          (i_noc_lt_axi_m_subip_arready),
    .i_noc_lt_axi_m_rvalid           (i_noc_lt_axi_m_subip_rvalid),
    .i_noc_lt_axi_m_rlast            (i_noc_lt_axi_m_subip_rlast),
    .i_noc_lt_axi_m_rid              (i_noc_lt_axi_m_subip_rid),
    .i_noc_lt_axi_m_rdata            (i_noc_lt_axi_m_subip_rdata),
    .i_noc_lt_axi_m_rresp            (i_noc_lt_axi_m_subip_rresp),
    .o_dmc_l1_lt_axi_m_awvalid       (o_dmc_l1_lt_axi_m_subip_awvalid),
    .o_dmc_l1_lt_axi_m_awaddr        (o_dmc_l1_lt_axi_m_subip_awaddr),
    .o_dmc_l1_lt_axi_m_awid          (o_dmc_l1_lt_axi_m_subip_awid),
    .o_dmc_l1_lt_axi_m_awlen         (o_dmc_l1_lt_axi_m_subip_awlen),
    .o_dmc_l1_lt_axi_m_awsize        (o_dmc_l1_lt_axi_m_subip_awsize),
    .o_dmc_l1_lt_axi_m_awburst       (o_dmc_l1_lt_axi_m_subip_awburst),
    .o_dmc_l1_lt_axi_m_wvalid        (o_dmc_l1_lt_axi_m_subip_wvalid),
    .o_dmc_l1_lt_axi_m_wlast         (o_dmc_l1_lt_axi_m_subip_wlast),
    .o_dmc_l1_lt_axi_m_wstrb         (o_dmc_l1_lt_axi_m_subip_wstrb),
    .o_dmc_l1_lt_axi_m_wdata         (o_dmc_l1_lt_axi_m_subip_wdata),
    .o_dmc_l1_lt_axi_m_bready        (o_dmc_l1_lt_axi_m_subip_bready),
    .o_dmc_l1_lt_axi_m_arvalid       (o_dmc_l1_lt_axi_m_subip_arvalid),
    .o_dmc_l1_lt_axi_m_araddr        (o_dmc_l1_lt_axi_m_subip_araddr),
    .o_dmc_l1_lt_axi_m_arid          (o_dmc_l1_lt_axi_m_subip_arid),
    .o_dmc_l1_lt_axi_m_arlen         (o_dmc_l1_lt_axi_m_subip_arlen),
    .o_dmc_l1_lt_axi_m_arsize        (o_dmc_l1_lt_axi_m_subip_arsize),
    .o_dmc_l1_lt_axi_m_arburst       (o_dmc_l1_lt_axi_m_subip_arburst),
    .o_dmc_l1_lt_axi_m_rready        (o_dmc_l1_lt_axi_m_subip_rready),
    .i_dmc_l1_lt_axi_m_awready       (i_dmc_l1_lt_axi_m_subip_awready),
    .i_dmc_l1_lt_axi_m_wready        (i_dmc_l1_lt_axi_m_subip_wready),
    .i_dmc_l1_lt_axi_m_bvalid        (i_dmc_l1_lt_axi_m_subip_bvalid),
    .i_dmc_l1_lt_axi_m_bid           (i_dmc_l1_lt_axi_m_subip_bid),
    .i_dmc_l1_lt_axi_m_bresp         (i_dmc_l1_lt_axi_m_subip_bresp),
    .i_dmc_l1_lt_axi_m_arready       (i_dmc_l1_lt_axi_m_subip_arready),
    .i_dmc_l1_lt_axi_m_rvalid        (i_dmc_l1_lt_axi_m_subip_rvalid),
    .i_dmc_l1_lt_axi_m_rlast         (i_dmc_l1_lt_axi_m_subip_rlast),
    .i_dmc_l1_lt_axi_m_rid           (i_dmc_l1_lt_axi_m_subip_rid),
    .i_dmc_l1_lt_axi_m_rdata         (i_dmc_l1_lt_axi_m_subip_rdata),
    .i_dmc_l1_lt_axi_m_rresp         (i_dmc_l1_lt_axi_m_subip_rresp)
  );

endmodule
