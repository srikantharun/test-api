// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: token manager IF, used to drive and monitor the token manager for AIC
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>

`ifndef GUARD_TKN_MNG_AIC_IF_SVI
`define GUARD_TKN_MNG_AIC_IF_SVI

interface tkn_mng_aic_interface#(
        localparam token_manager_pkg::tokmgr_cfg_t LocCfg = token_mgr_mapping_aic_pkg::TOK_MGR_CFG,
        localparam token_manager_pkg::tokmgr_cfg_t TopCfg = token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG
    )(
        input bit clk,
        input bit rst_n
    );

    import token_manager_pkg::*;
    import token_mgr_mapping_aic_pkg::*;

    logic tkn_mng_sync_mvm_exe_swep_en;
    logic tkn_mng_sync_mvm_exe_swep;
    logic tkn_mng_swep_is_acd;
    logic [LocCfg.max_num_prod-1:0] tkn_mng_dev_prod_valid[LocCfg.nr_loc_devs];
    logic [LocCfg.max_num_prod-1:0] tkn_mng_dev_prod_ready[LocCfg.nr_loc_devs];
    logic [LocCfg.max_num_cons-1:0] tkn_mng_dev_cons_valid[LocCfg.nr_loc_devs];
    logic [LocCfg.max_num_cons-1:0] tkn_mng_dev_cons_ready[LocCfg.nr_loc_devs];
    logic [LocCfg.nr_loc_devs-1:0] tkn_mng_acd_prod_valid;
    logic [LocCfg.nr_loc_devs-1:0] tkn_mng_acd_prod_ready;
    logic [LocCfg.nr_loc_devs-1:0] tkn_mng_acd_cons_valid;
    logic [LocCfg.nr_loc_devs-1:0] tkn_mng_acd_cons_ready;
    logic [token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] tkn_mng_cid;
    token_manager_pkg::tokmgr_uid_all_t tkn_mng_uid_to_vuid;
    token_manager_pkg::tokmgr_uid_all_t tkn_mng_vuid_to_uid;
    logic [7:0] tkn_mng_tok_prod_ocpl_m_maddr;
    logic tkn_mng_tok_prod_ocpl_m_mcmd;
    logic tkn_mng_tok_prod_ocpl_m_scmdaccept;
    logic [7:0] tkn_mng_tok_prod_ocpl_m_mdata;
    logic [7:0] tkn_mng_tok_cons_ocpl_s_maddr;
    logic tkn_mng_tok_cons_ocpl_s_mcmd;
    logic tkn_mng_tok_cons_ocpl_s_scmdaccept;
    logic [7:0] tkn_mng_tok_cons_ocpl_s_mdata;
    logic [TopCfg.max_num_prod-1:0] tkn_mng_top_prod_valid[TopCfg.nr_loc_devs];
    logic [TopCfg.max_num_prod-1:0] tkn_mng_top_prod_ready[TopCfg.nr_loc_devs];
    logic [TopCfg.max_num_cons-1:0] tkn_mng_top_cons_valid[TopCfg.nr_loc_devs];
    logic [TopCfg.max_num_cons-1:0] tkn_mng_top_cons_ready[TopCfg.nr_loc_devs];
    token_manager_aic_csr_reg_pkg::axi_a_ch_h2d_t tkn_mng_axi_s_aw;
    logic tkn_mng_axi_s_aw_ready;
    token_manager_aic_csr_reg_pkg::axi_w_ch_h2d_t tkn_mng_axi_s_w;
    logic tkn_mng_axi_s_w_ready;
    token_manager_aic_csr_reg_pkg::axi_b_ch_d2h_t tkn_mng_axi_s_b;
    logic tkn_mng_axi_s_b_ready;
    token_manager_aic_csr_reg_pkg::axi_a_ch_h2d_t tkn_mng_axi_s_ar;
    logic tkn_mng_axi_s_ar_ready;
    token_manager_aic_csr_reg_pkg::axi_r_ch_d2h_t tkn_mng_axi_s_r;
    logic tkn_mng_axi_s_r_ready;
    logic tkn_mng_irq;


endinterface
`endif // GUARD_TKN_MNG_AIC_IF_SVI

