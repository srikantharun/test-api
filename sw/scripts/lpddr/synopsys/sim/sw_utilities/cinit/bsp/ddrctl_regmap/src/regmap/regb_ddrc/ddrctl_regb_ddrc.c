// ------------------------------------------------------------------------------
//
// Copyright 2023 Synopsys, INC.
//
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
//
// ------------------------------------------------------------------------------

#include "ddrctl_regb_ddrc.h"

const ddrctl_field_t reg_cgctl[] = {
    {"force_clk_te_en" ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"force_clk_arb_en",  4,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_clkgatectl[] = {
    {"bsm_clk_on",  0,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL        , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_datactl0[] = {
    {"rd_data_copy_en", 16,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wr_data_copy_en", 17,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wr_data_x_en"   , 18,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dbictl[] = {
    {"dm_en"    ,  0,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"wr_dbi_en",  1,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rd_dbi_en",  2,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL       , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ddrctl_ver_number[] = {
    {"ver_number",  0, 32, ACCESS_READ, PROG_STATIC},
    {NULL        , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ddrctl_ver_type[] = {
    {"ver_type",  0, 32, ACCESS_READ, PROG_STATIC},
    {NULL      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_deratectl0[] = {
    {"derate_enable"          ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"lpddr4_refresh_mode"    ,  1,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"derate_mr4_pause_fc"    ,  2,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dis_trefi_x6x8"         ,  3,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dis_trefi_x0125"        ,  4,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"use_slow_rm_in_low_temp",  5,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_deratectl1[] = {
    {"active_derate_byte_rank0",  0,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_deratectl2[] = {
    {"active_derate_byte_rank1",  0,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_deratectl5[] = {
    {"derate_temp_limit_intr_en"   ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"derate_temp_limit_intr_clr"  ,  1,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"derate_temp_limit_intr_force",  2,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                          , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_deratectl6[] = {
    {"derate_mr4_tuf_dis",  0,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_deratedbgctl[] = {
    {"dbg_mr4_rank_sel",  4,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_deratedbgstat[] = {
    {"dbg_mr4_byte0",  0,  8, ACCESS_READ, PROG_DYNAMIC},
    {"dbg_mr4_byte1",  8,  8, ACCESS_READ, PROG_DYNAMIC},
    {"dbg_mr4_byte2", 16,  8, ACCESS_READ, PROG_DYNAMIC},
    {"dbg_mr4_byte3", 24,  8, ACCESS_READ, PROG_DYNAMIC},
    {NULL           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_deratestat0[] = {
    {"derate_temp_limit_intr",  0,  1, ACCESS_READ, PROG_STATIC},
    {NULL                    , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfilpcfg0[] = {
    {"dfi_lp_en_pd"             ,  0,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_lp_en_sr"             ,  4,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_lp_en_dsm"            ,  8,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_lp_en_data"           , 16,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_lp_data_req_en"       , 20,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"extra_gap_for_dfi_lp_data", 28,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                       , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfimisc[] = {
    {"dfi_init_complete_en",  0,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"phy_dbi_mode"        ,  1,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_data_cs_polarity",  2,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_reset_n"         ,  4,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_init_start"      ,  5,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"lp_optimized_write"  ,  7,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_frequency"       ,  8,  5, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_freq_fsp"        , 14,  2, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dfi_channel_mode"    , 16,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfiphymstr[] = {
    {"dfi_phymstr_en"         ,  0,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_phymstr_blk_ref_x32", 24,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfistat[] = {
    {"dfi_init_complete"   ,  0,  1, ACCESS_READ, PROG_DYNAMIC},
    {"dfi_lp_ctrl_ack_stat",  1,  1, ACCESS_READ, PROG_DYNAMIC},
    {"dfi_lp_data_ack_stat",  2,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfiupd0[] = {
    {"dfi_phyupd_en"       , 15,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"ctrlupd_pre_srx"     , 29,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_auto_ctrlupd_srx", 30,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_auto_ctrlupd"    , 31,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dqsosccfg0[] = {
    {"dis_dqsosc_srx",  0,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dqsoscruntime[] = {
    {"dqsosc_runtime" ,  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wck2dqo_runtime", 16,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dqsoscstat0[] = {
    {"dqsosc_state"        ,  0,  3, ACCESS_READ, PROG_STATIC},
    {"dqsosc_per_rank_stat",  4,  2, ACCESS_READ, PROG_STATIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccapstat[] = {
    {"ecc_ap_err",  0,  1, ACCESS_READ, PROG_STATIC},
    {NULL        , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccbitmask0[] = {
    {"ecc_corr_bit_mask_31_0",  0, 32, ACCESS_READ, PROG_DYNAMIC},
    {NULL                    , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccbitmask1[] = {
    {"ecc_corr_bit_mask_63_32",  0, 32, ACCESS_READ, PROG_DYNAMIC},
    {NULL                     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccbitmask2[] = {
    {"ecc_corr_bit_mask_71_64",  0,  8, ACCESS_READ, PROG_DYNAMIC},
    {NULL                     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ecccaddr0[] = {
    {"ecc_corr_row" ,  0, 18, ACCESS_READ, PROG_DYNAMIC},
    {"ecc_corr_rank", 24,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ecccaddr1[] = {
    {"ecc_corr_col" ,  0, 11, ACCESS_READ, PROG_DYNAMIC},
    {"ecc_corr_bank", 16,  3, ACCESS_READ, PROG_DYNAMIC},
    {"ecc_corr_bg"  , 24,  2, ACCESS_READ, PROG_DYNAMIC},
    {NULL           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ecccfg0[] = {
    {"ecc_mode"                 ,  0,  3, ACCESS_READ_WRITE, PROG_STATIC},
    {"ecc_ap_en"                ,  6,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"ecc_region_remap_en"      ,  7,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"ecc_region_map"           ,  8,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"blk_channel_idle_time_x32", 16,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"ecc_ap_err_threshold"     , 24,  3, ACCESS_READ_WRITE, PROG_STATIC},
    {"ecc_region_map_other"     , 29,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"ecc_region_map_granu"     , 30,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                       , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ecccfg1[] = {
    {"data_poison_en"         ,  0,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"data_poison_bit"        ,  1,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"ecc_region_parity_lock" ,  4,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"ecc_region_waste_lock"  ,  5,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"med_ecc_en"             ,  6,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"blk_channel_active_term",  7,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"active_blk_channel"     ,  8,  5, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ecccsyn0[] = {
    {"ecc_corr_syndromes_31_0",  0, 32, ACCESS_READ, PROG_DYNAMIC},
    {NULL                     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ecccsyn1[] = {
    {"ecc_corr_syndromes_63_32",  0, 32, ACCESS_READ, PROG_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ecccsyn2[] = {
    {"ecc_corr_syndromes_71_64",  0,  8, ACCESS_READ, PROG_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccctl[] = {
    {"ecc_corrected_err_clr"         ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_uncorrected_err_clr"       ,  1,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_corr_err_cnt_clr"          ,  2,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_uncorr_err_cnt_clr"        ,  3,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_ap_err_intr_clr"           ,  4,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_corrected_err_intr_en"     ,  8,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_uncorrected_err_intr_en"   ,  9,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_ap_err_intr_en"            , 10,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_corrected_err_intr_force"  , 16,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_uncorrected_err_intr_force", 17,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ecc_ap_err_intr_force"         , 18,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccerrcnt[] = {
    {"ecc_corr_err_cnt"  ,  0, 16, ACCESS_READ, PROG_DYNAMIC},
    {"ecc_uncorr_err_cnt", 16, 16, ACCESS_READ, PROG_DYNAMIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccpoisonaddr0[] = {
    {"ecc_poison_col" ,  0, 12, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"ecc_poison_rank", 24,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccpoisonaddr1[] = {
    {"ecc_poison_row" ,  0, 18, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"ecc_poison_bank", 24,  3, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"ecc_poison_bg"  , 28,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccpoisonpat0[] = {
    {"ecc_poison_data_31_0",  0, 32, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccpoisonpat2[] = {
    {"ecc_poison_data_71_64",  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                   , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccstat[] = {
    {"ecc_corrected_bit_num",  0,  7, ACCESS_READ, PROG_STATIC},
    {"ecc_corrected_err"    ,  8,  1, ACCESS_READ, PROG_STATIC},
    {"ecc_uncorrected_err"  , 16,  1, ACCESS_READ, PROG_STATIC},
    {"sbr_read_ecc_ce"      , 24,  1, ACCESS_READ, PROG_STATIC},
    {"sbr_read_ecc_ue"      , 25,  1, ACCESS_READ, PROG_STATIC},
    {NULL                   , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccuaddr0[] = {
    {"ecc_uncorr_row" ,  0, 18, ACCESS_READ, PROG_DYNAMIC},
    {"ecc_uncorr_rank", 24,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccuaddr1[] = {
    {"ecc_uncorr_col" ,  0, 11, ACCESS_READ, PROG_DYNAMIC},
    {"ecc_uncorr_bank", 16,  3, ACCESS_READ, PROG_DYNAMIC},
    {"ecc_uncorr_bg"  , 24,  2, ACCESS_READ, PROG_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccusyn0[] = {
    {"ecc_uncorr_syndromes_31_0",  0, 32, ACCESS_READ, PROG_DYNAMIC},
    {NULL                       , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccusyn1[] = {
    {"ecc_uncorr_syndromes_63_32",  0, 32, ACCESS_READ, PROG_DYNAMIC},
    {NULL                        , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_eccusyn2[] = {
    {"ecc_uncorr_syndromes_71_64",  0,  8, ACCESS_READ, PROG_DYNAMIC},
    {NULL                        , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_hwffcctl[] = {
    {"hwffc_en"          ,  0,  2, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"init_fsp"          ,  4,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"init_vrcg"         ,  5,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"target_vrcg"       ,  6,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"skip_mrw_odtvref"  , 24,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"skip_zq_stop_start", 25,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"zq_interval"       , 26,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {"hwffc_mode"        , 31,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_hwffcstat[] = {
    {"hwffc_in_progress"   ,  0,  1, ACCESS_READ, PROG_DYNAMIC},
    {"hwffc_operating_mode",  1,  1, ACCESS_READ, PROG_DYNAMIC},
    {"current_frequency"   ,  4,  2, ACCESS_READ, PROG_DYNAMIC},
    {"current_fsp"         ,  8,  1, ACCESS_READ, PROG_DYNAMIC},
    {"current_vrcg"        ,  9,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_hwlpctl[] = {
    {"hw_lp_en"          ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"hw_lp_exit_idle_en",  1,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_inittmg0[] = {
    {"pre_cke_x1024" ,  0, 13, ACCESS_READ_WRITE, PROG_STATIC},
    {"post_cke_x1024", 16, 10, ACCESS_READ_WRITE, PROG_STATIC},
    {"skip_dram_init", 30,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkecccaddr0[] = {
    {"link_ecc_corr_row" ,  0, 18, ACCESS_READ, PROG_DYNAMIC},
    {"link_ecc_corr_rank", 24,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkecccaddr1[] = {
    {"link_ecc_corr_col" ,  0, 11, ACCESS_READ, PROG_DYNAMIC},
    {"link_ecc_corr_bank", 16,  3, ACCESS_READ, PROG_DYNAMIC},
    {"link_ecc_corr_bg"  , 24,  2, ACCESS_READ, PROG_DYNAMIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkeccctl1[] = {
    {"rd_link_ecc_corr_intr_en"     ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_link_ecc_corr_intr_clr"    ,  1,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_link_ecc_corr_cnt_clr"     ,  2,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_link_ecc_corr_intr_force"  ,  3,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_link_ecc_uncorr_intr_en"   ,  4,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_link_ecc_uncorr_intr_clr"  ,  5,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_link_ecc_uncorr_cnt_clr"   ,  6,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_link_ecc_uncorr_intr_force",  7,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkeccerrcnt0[] = {
    {"rd_link_ecc_err_syndrome",  0,  9, ACCESS_READ, PROG_DYNAMIC},
    {"rd_link_ecc_corr_cnt"    , 16,  8, ACCESS_READ, PROG_DYNAMIC},
    {"rd_link_ecc_uncorr_cnt"  , 24,  8, ACCESS_READ, PROG_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkeccerrstat[] = {
    {"rd_link_ecc_corr_err_int"  ,  0,  4, ACCESS_READ, PROG_STATIC},
    {"rd_link_ecc_uncorr_err_int",  8,  4, ACCESS_READ, PROG_STATIC},
    {NULL                        , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkeccindex[] = {
    {"rd_link_ecc_err_byte_sel",  0,  3, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rd_link_ecc_err_rank_sel",  4,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkeccpoisonctl0[] = {
    {"linkecc_poison_inject_en",  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"linkecc_poison_type"     ,  1,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"linkecc_poison_rw"       ,  2,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"linkecc_poison_dmi_sel"  , 16,  4, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"linkecc_poison_byte_sel" , 24,  4, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkeccpoisonstat[] = {
    {"linkecc_poison_complete",  0,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL                     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkeccuaddr0[] = {
    {"link_ecc_uncorr_row" ,  0, 18, ACCESS_READ, PROG_DYNAMIC},
    {"link_ecc_uncorr_rank", 24,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkeccuaddr1[] = {
    {"link_ecc_uncorr_col" ,  0, 11, ACCESS_READ, PROG_DYNAMIC},
    {"link_ecc_uncorr_bank", 16,  3, ACCESS_READ, PROG_DYNAMIC},
    {"link_ecc_uncorr_bg"  , 24,  2, ACCESS_READ, PROG_DYNAMIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_mrctrl0[] = {
    {"mr_type"      ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"sw_init_int"  ,  3,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"mr_rank"      ,  4,  2, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"mr_addr"      , 12,  4, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"mrr_done_clr" , 24,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dis_mrrw_trfc", 27,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ppr_en"       , 28,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ppr_pgmpst_en", 29,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"mr_wr"        , 31,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_mrctrl1[] = {
    {"mr_data",  0, 18, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_mrrdata0[] = {
    {"mrr_data_lwr",  0, 32, ACCESS_READ, PROG_DYNAMIC},
    {NULL          , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_mrrdata1[] = {
    {"mrr_data_upr",  0, 32, ACCESS_READ, PROG_DYNAMIC},
    {NULL          , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_mrstat[] = {
    {"mr_wr_busy",  0,  1, ACCESS_READ, PROG_DYNAMIC},
    {"mrr_done"  , 16,  1, ACCESS_READ, PROG_DYNAMIC},
    {"ppr_done"  , 17,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL        , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_mstr0[] = {
    {"lpddr4"        ,  1,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"lpddr5"        ,  3,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"lpddr5x"       , 11,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"data_bus_width", 12,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {"burst_rdwr"    , 16,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"active_ranks"  , 24,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_mstr2[] = {
    {"target_frequency",  0,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_mstr4[] = {
    {"wck_on"        ,  0,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wck_suspend_en",  4,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"ws_off_en"     ,  8,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_odtmap[] = {
    {"rank0_wr_odt",  0,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {"rank0_rd_odt",  4,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {"rank1_wr_odt",  8,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {"rank1_rd_odt", 12,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL          , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_opctrl0[] = {
    {"dis_wc"             ,  0,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_max_rank_rd_opt",  6,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_max_rank_wr_opt",  7,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                 , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_opctrl1[] = {
    {"dis_dq" ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dis_hif",  1,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_opctrlcam[] = {
    {"dbg_hpr_q_depth"       ,  0,  7, ACCESS_READ, PROG_DYNAMIC},
    {"dbg_lpr_q_depth"       ,  8,  7, ACCESS_READ, PROG_DYNAMIC},
    {"dbg_w_q_depth"         , 16,  7, ACCESS_READ, PROG_DYNAMIC},
    {"dbg_stall"             , 24,  1, ACCESS_READ, PROG_DYNAMIC},
    {"dbg_rd_q_empty"        , 25,  1, ACCESS_READ, PROG_DYNAMIC},
    {"dbg_wr_q_empty"        , 26,  1, ACCESS_READ, PROG_DYNAMIC},
    {"rd_data_pipeline_empty", 28,  1, ACCESS_READ, PROG_DYNAMIC},
    {"wr_data_pipeline_empty", 29,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL                    , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_opctrlcam1[] = {
    {"dbg_wrecc_q_depth",  0,  7, ACCESS_READ, PROG_DYNAMIC},
    {NULL               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_opctrlcmd[] = {
    {"zq_calib_short", 16,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ctrlupd"       , 17,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ctrlupd_burst" , 18,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_opctrlstat[] = {
    {"zq_calib_short_busy", 16,  1, ACCESS_READ, PROG_DYNAMIC},
    {"ctrlupd_busy"       , 17,  1, ACCESS_READ, PROG_DYNAMIC},
    {"ctrlupd_burst_busy" , 18,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL                 , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_oprefctrl0[] = {
    {"rank0_refresh",  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rank1_refresh",  1,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_oprefstat0[] = {
    {"rank0_refresh_busy",  0,  1, ACCESS_READ, PROG_DYNAMIC},
    {"rank1_refresh_busy",  1,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_poisoncfg[] = {
    {"wr_poison_slverr_en",  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"wr_poison_intr_en"  ,  4,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"wr_poison_intr_clr" ,  8,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_poison_slverr_en", 16,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_poison_intr_en"  , 20,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"rd_poison_intr_clr" , 24,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                 , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_poisonstat[] = {
    {"wr_poison_intr_0",  0,  1, ACCESS_READ, PROG_DYNAMIC},
    {"rd_poison_intr_0", 16,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ppt2ctrl0[] = {
    {"ppt2_burst_num"       ,  0, 10, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ppt2_ctrlupd_num_dfi0", 12,  6, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ppt2_ctrlupd_num_dfi1", 18,  6, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ppt2_burst"           , 28,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ppt2_wait_ref"        , 31,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                   , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ppt2stat0[] = {
    {"ppt2_state"     ,  0,  4, ACCESS_READ, PROG_DYNAMIC},
    {"ppt2_burst_busy", 28,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pwrctl[] = {
    {"selfref_en"             ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"powerdown_en"           ,  4,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"en_dfi_dram_clk_disable",  9,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"selfref_sw"             , 11,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"stay_in_selfref"        , 15,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dis_cam_drain_selfref"  , 16,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"lpddr4_sr_allowed"      , 17,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dsm_en"                 , 18,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rankctl[] = {
    {"max_rank_rd",  0,  4, ACCESS_READ_WRITE, PROG_STATIC},
    {"max_rank_wr", 12,  4, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL         , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfmctl[] = {
    {"dbg_raa_rank"   ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dbg_raa_bg_bank",  4,  4, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfmmod0[] = {
    {"rfm_en"      ,  0,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rfmsbc"      ,  4,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"raaimt"      ,  8,  5, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"raamult"     , 16,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"raadec"      , 18,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rfmth_rm_thr", 24,  5, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL          , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfmmod1[] = {
    {"init_raa_cnt",  0, 11, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL          , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfmstat[] = {
    {"rank_raa_cnt_gt0",  0,  2, ACCESS_READ, PROG_DYNAMIC},
    {"dbg_raa_cnt"     , 16, 11, ACCESS_READ, PROG_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfshctl0[] = {
    {"dis_auto_refresh"    ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"refresh_update_level",  4,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfshmod0[] = {
    {"refresh_burst"           ,  0,  6, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"auto_refab_en"           ,  6,  2, ACCESS_READ_WRITE, PROG_STATIC},
    {"per_bank_refresh"        ,  8,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"per_bank_refresh_opt_en" ,  9,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"fixed_crit_refpb_bank_en", 24,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sched0[] = {
    {"dis_opt_wrecc_collision_flush",  0,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"prefer_write"                 ,  1,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"pageclose"                    ,  2,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"opt_wrcam_fill_level"         ,  4,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_opt_ntt_by_act"           ,  5,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_opt_ntt_by_pre"           ,  6,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"autopre_rmw"                  ,  7,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"lpr_num_entries"              ,  8,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {"lpddr4_opt_act_timing"        , 15,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"lpddr5_opt_act_timing"        , 16,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"w_starve_free_running"        , 24,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"opt_act_lat"                  , 27,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"prefer_read"                  , 29,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_speculative_act"          , 30,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"opt_vprw_sch"                 , 31,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sched1[] = {
    {"delay_switch_write"     , 12,  4, ACCESS_READ_WRITE, PROG_STATIC},
    {"visible_window_limit_wr", 16,  3, ACCESS_READ_WRITE, PROG_STATIC},
    {"visible_window_limit_rd", 20,  3, ACCESS_READ_WRITE, PROG_STATIC},
    {"page_hit_limit_wr"      , 24,  3, ACCESS_READ_WRITE, PROG_STATIC},
    {"page_hit_limit_rd"      , 28,  3, ACCESS_READ_WRITE, PROG_STATIC},
    {"opt_hit_gt_hpr"         , 31,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sched3[] = {
    {"wrcam_lowthresh"    ,  0,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {"wrcam_highthresh"   ,  8,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {"wr_pghit_num_thresh", 16,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {"rd_pghit_num_thresh", 24,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                 , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sched4[] = {
    {"rd_act_idle_gap"   ,  0,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {"wr_act_idle_gap"   ,  8,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {"rd_page_exp_cycles", 16,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {"wr_page_exp_cycles", 24,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sched5[] = {
    {"wrecc_cam_lowthresh"                ,  0,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"wrecc_cam_highthresh"               ,  8,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_opt_loaded_wrecc_cam_fill_level", 28,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_opt_valid_wrecc_cam_fill_level" , 29,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                                 , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_stat[] = {
    {"operating_mode"       ,  0,  3, ACCESS_READ, PROG_STATIC},
    {"selfref_type"         ,  4,  2, ACCESS_READ, PROG_STATIC},
    {"selfref_state"        , 12,  3, ACCESS_READ, PROG_STATIC},
    {"selfref_cam_not_empty", 16,  1, ACCESS_READ, PROG_STATIC},
    {NULL                   , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_swctl[] = {
    {"sw_done",  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_swctlstatic[] = {
    {"sw_static_unlock",  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_swstat[] = {
    {"sw_done_ack",  0,  1, ACCESS_READ, PROG_STATIC},
    {NULL         , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_zqctl0[] = {
    {"zq_resistor_shared", 29,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"dis_auto_zq"       , 31,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_zqctl1[] = {
    {"zq_reset",  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_zqctl2[] = {
    {"dis_srx_zqcl"      ,  0,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dis_srx_zqcl_hwffc",  1,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_zqstat[] = {
    {"zq_reset_busy",  0,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

