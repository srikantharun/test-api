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

#include "ddrctl_regb_freq.h"

const ddrctl_field_t reg_ddr4pprtmg0[] = {
    {"t_pgm_x1_x1024",  0, 22, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_pgm_x1_sel"  , 31,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ddr4pprtmg1[] = {
    {"t_pgmpst_x32",  0, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_pgm_exit"  , 24,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL          , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_derateint[] = {
    {"mr4_read_interval",  0, 32, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_derateval0[] = {
    {"derated_t_rrd"    ,  0,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"derated_t_rp"     ,  8,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"derated_t_ras_min", 16,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"derated_t_rcd"    , 24,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_derateval1[] = {
    {"derated_t_rc"       ,  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"derated_t_rcd_write",  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                 , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfilptmg0[] = {
    {"dfi_lp_wakeup_pd" ,  0,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_lp_wakeup_sr" ,  8,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_lp_wakeup_dsm", 16,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfilptmg1[] = {
    {"dfi_lp_wakeup_data",  0,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_tlp_resp"      ,  8,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfitmg0[] = {
    {"dfi_tphy_wrlat"  ,  0,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_tphy_wrdata" ,  8,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_t_rddata_en" , 16,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_t_ctrl_delay", 24,  5, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfitmg1[] = {
    {"dfi_t_dram_clk_enable" ,  0,  5, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_t_dram_clk_disable",  8,  5, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_t_wrdata_delay"    , 16,  5, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                    , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfitmg2[] = {
    {"dfi_tphy_wrcslat",  0,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_tphy_rdcslat",  8,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_twck_delay"  , 16,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfitmg4[] = {
    {"dfi_twck_dis"  ,  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_twck_en_fs",  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_twck_en_wr", 16,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_twck_en_rd", 24,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfitmg5[] = {
    {"dfi_twck_toggle_post",  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_twck_toggle_cs"  ,  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_twck_toggle"     , 16,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_twck_fast_toggle", 24,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfitmg6[] = {
    {"dfi_twck_toggle_post_rd"   ,  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"dfi_twck_toggle_post_rd_en",  8,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                        , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfiupdtmg0[] = {
    {"dfi_t_ctrlup_min",  0, 10, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_t_ctrlup_max", 16, 10, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfiupdtmg1[] = {
    {"dfi_t_ctrlupd_interval_max_x1024",  0,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {"dfi_t_ctrlupd_interval_min_x1024", 16,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfiupdtmg2[] = {
    {"dfi_t_ctrlupd_interval_type1"     ,  0, 12, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"ctrlupd_after_dqsosc"             , 27,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"ppt2_override"                    , 28,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"ppt2_en"                          , 29,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dfi_t_ctrlupd_interval_type1_unit", 30,  2, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dfiupdtmg3[] = {
    {"dfi_t_ctrlupd_burst_interval_x8",  0,  9, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dqsoscctl0[] = {
    {"dqsosc_enable"       ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dqsosc_interval_unit",  2,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"dqsosc_interval"     ,  4, 12, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg0[] = {
    {"t_ras_min",  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_ras_max",  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_faw"    , 16,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wr2pre"   , 24,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL       , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg1[] = {
    {"t_rc"       ,  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rd2pre"     ,  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_xp"       , 16,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_rcd_write", 24,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL         , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg12[] = {
    {"t_cmdcke", 16,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg13[] = {
    {"t_ppd"   ,  0,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_ccd_mw", 16,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"odtloff" , 24,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg14[] = {
    {"t_xsr" ,  0, 12, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_osco", 16,  9, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL    , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg17[] = {
    {"t_vrcg_disable",  0, 10, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_vrcg_enable" , 16, 10, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg2[] = {
    {"wr2rd"        ,  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rd2wr"        ,  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"read_latency" , 16,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"write_latency", 24,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg23[] = {
    {"t_pdn"          ,  0, 12, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"t_xsr_dsm_x1024", 16,  8, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg24[] = {
    {"max_wr_sync",  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"max_rd_sync",  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rd2wr_s"    , 16,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"bank_org"   , 24,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL         , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg25[] = {
    {"rda2pre"                 ,  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wra2pre"                 ,  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"lpddr4_diff_bank_rwa2pre", 16,  3, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg3[] = {
    {"wr2mr",  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rd2mr",  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_mr" , 16,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL   , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg30[] = {
    {"mrr2rd" ,  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"mrr2wr" ,  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"mrr2mrw", 16,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg32[] = {
    {"ws_fs2wck_sus",  0,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_wcksus"     ,  8,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"ws_off2ws_fs" , 16,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg4[] = {
    {"t_rp" ,  0,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_rrd",  8,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_ccd", 16,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_rcd", 24,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL   , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg5[] = {
    {"t_cke"  ,  0,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_ckesr",  8,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_cksre", 16,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_cksrx", 24,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg6[] = {
    {"t_ckcsx",  0,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg7[] = {
    {"t_csh",  0,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL   , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dramset1tmg9[] = {
    {"wr2rd_s",  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_rrd_s",  8,  6, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"t_ccd_s", 16,  5, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_dvfsctl0[] = {
    {"dvfsq_enable",  2,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL          , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_hwlptmg0[] = {
    {"hw_lp_idle_x32", 16, 12, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_initmr0[] = {
    {"emr",  0, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"mr" , 16, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_initmr1[] = {
    {"emr3",  0, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"emr2", 16, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_initmr2[] = {
    {"mr5",  0, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"mr4", 16, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_initmr3[] = {
    {"mr6" ,  0, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"mr22", 16, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_lnkeccctl0[] = {
    {"wr_link_ecc_enable",  0,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"rd_link_ecc_enable",  1,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_perfhpr1[] = {
    {"hpr_max_starve"     ,  0, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"hpr_xact_run_length", 24,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                 , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_perflpr1[] = {
    {"lpr_max_starve"     ,  0, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"lpr_xact_run_length", 24,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL                 , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_perfwr1[] = {
    {"w_max_starve"     ,  0, 16, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"w_xact_run_length", 24,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pwrtmg[] = {
    {"powerdown_to_x32",  0,  7, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"selfref_to_x32"  , 16, 10, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ranktmg0[] = {
    {"diff_rank_rd_gap",  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"diff_rank_wr_gap",  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_ranktmg1[] = {
    {"wr2rd_dr",  0,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rd2wr_dr",  8,  8, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfmset1tmg0[] = {
    {"t_rfmpb",  0, 12, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfshset1tmg0[] = {
    {"t_refi_x1_x32"    ,  0, 14, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"refresh_to_x1_x32", 16,  6, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"refresh_margin"   , 24,  4, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"refresh_to_x1_sel", 30,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"t_refi_x1_sel"    , 31,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfshset1tmg1[] = {
    {"t_rfc_min"   ,  0, 12, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"t_rfc_min_ab", 16, 12, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL          , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfshset1tmg2[] = {
    {"t_pbr2pbr", 16,  8, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"t_pbr2act", 24,  8, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL       , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfshset1tmg3[] = {
    {"refresh_to_ab_x32", 24,  6, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_rfshset1tmg4[] = {
    {"refresh_timer0_start_value_x32",  0, 12, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"refresh_timer1_start_value_x32", 16, 12, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_schedtmg0[] = {
    {"pageclose_timer",  0,  8, ACCESS_READ_WRITE, PROG_STATIC},
    {"rdwr_idle_gap"  ,  8,  7, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_tmgcfg[] = {
    {"frequency_ratio",  0,  1, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_zqset1tmg0[] = {
    {"t_zq_long_nop" ,  0, 14, ACCESS_READ_WRITE, PROG_STATIC},
    {"t_zq_short_nop", 16, 10, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_zqset1tmg1[] = {
    {"t_zq_short_interval_x1024",  0, 20, ACCESS_READ_WRITE, PROG_STATIC},
    {"t_zq_reset_nop"           , 20, 10, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                       , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_zqset1tmg2[] = {
    {"t_zq_stop",  0,  7, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL       , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

