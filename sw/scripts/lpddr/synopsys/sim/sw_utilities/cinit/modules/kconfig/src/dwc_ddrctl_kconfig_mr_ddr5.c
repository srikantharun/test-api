// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
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
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
// ------------------------------------------------------------------------------


#include "dwc_ddrctl_cinit_kconfig_headers.h"
#include "dwc_ddrctl_kconfig_mr_lpddr4.h"

#define DDR5_PSTATE_MR_DEFINE_STR(prefix, pstate, separator, name) prefix ## pstate ## separator ## name

#define DDR5_PSTATE_MR_DEFINE(pstate, name) DDR5_PSTATE_MR_DEFINE_STR(DWC_DDRCTL_CINIT_DDR5_PSTATE, pstate, _, name)

#define DDR5_PSTATE_MR_SET(pstate, mr_variable, mr_macro) \
    do { \
        mr_variable = DDR5_PSTATE_MR_DEFINE(pstate, mr_macro); \
    } while (0)

#define DDR5_MR_CONFIG(mr_cfg, pstate) \
    do { \
        /* MR0 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr0.cl, MR0_CL); \
        /* MR2 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr2.rd_preamble_enable, MR2_RD_PREAMBLE_ENABLE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr2.wr_leveling, MR2_WR_LEVELING); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr2.ddr5_2n_mode, MR2_DDR5_2N_MODE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr2.mpsm, MR2_MPSM); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr2.cs_assertion_duration, MR2_CS_ASSERTION_DURATION); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr2.dev15_mpsm, MR2_DEV15_MPSM); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr2.internal_wr_timing, MR2_INTERNAL_WR_TIMING); \
        /* MR3 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr3.wr_leveling_internal_lower_byte, MR3_WR_LEVELING_INTERNAL_LOWER_BYTE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr3.wr_leveling_internal_upper_byte, MR3_WR_LEVELING_INTERNAL_UPPER_BYTE); \
        /* MR4 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr4.refresh_rate, MR4_REFRESH_RATE); \
        /* MR5 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr5.data_output_disable, MR5_DATA_OUTPUT_DISABLE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr5.pull_up_output_drv_impedance, MR5_PULL_UP_OUTPUT_DRV_IMPEDANCE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr5.tdqs_enable, MR5_TDQS_ENABLE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr5.dm_enable, MR5_DM_ENABLE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr5.pull_down_output_drv_impedance, MR5_PULL_DOWN_OUTPUT_DRV_IMPEDANCE); \
        /* MR6 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr6.trtp, MR6_TRTP); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr6.wr_recovery, MR6_WR_RECOVERY); \
        /* MR8 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr8.rd_preamble, MR8_RD_PREAMBLE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr8.wr_preamble, MR8_WR_PREAMBLE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr8.rd_postamble, MR8_RD_POSTAMBLE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr8.wr_postamble, MR8_WR_POSTAMBLE); \
        /* MR13 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr13.tccd_l, MR13_TCCD_L); \
        /* MR34 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr34.rtt_park, MR34_RTT_PARK); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr34.rtt_wr, MR34_RTT_WR); \
        /* MR35 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr35.rtt_nom_wr, MR35_RTT_NOM_WR); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr35.rtt_nom_rd, MR35_RTT_NOM_RD); \
        /* MR37 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr37.odtlon_wr_offset, MR37_ODTLON_WR_OFFSET); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr37.odtloff_wr_offset, MR37_ODTLOFF_WR_OFFSET); \
        /* MR38 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr38.odtlon_wr_nt_offset, MR38_ODTLON_WR_NT_OFFSET); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr38.odtloff_wr_nt_offset, MR38_ODTLOFF_WR_NT_OFFSET); \
        /* MR39 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr39.odtlon_rd_nt_offset, MR39_ODTLON_RD_NT_OFFSET); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr39.odtloff_rd_nt_offset, MR39_ODTLOFF_RD_NT_OFFSET); \
        /* MR40 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr40.rd_dqs_offset, MR40_RD_DQS_OFFSET); \
        /* MR45 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr45.osc_run_time, MR45_OSC_RUN_TIME); \
        /* MR50 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr50.wr_crc_error_status, MR50_WR_CRC_ERROR_STATUS); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr50.wr_crc_auto_disable_enable, MR50_WR_CRC_AUTO_DISABLE_ENABLE); \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr50.wr_crc_auto_disable_status, MR50_WR_CRC_AUTO_DISABLE_STATUS); \
        /* MR51 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr51.wr_crc_auto_disable_thre, MR51_WR_CRC_AUTO_DISABLE_THRE); \
        /* MR52 */ \
        DDR5_PSTATE_MR_SET(pstate, mr_cfg.mr52.wr_crc_auto_disable_window, MR52_WR_CRC_AUTO_DISABLE_WINDOW); \
    } while (0)


#define DDR5_PSTATE_RANK_MR_DEFINE_STR(prefix, pstate, rank_str, rank, separator, name) \
        prefix ## pstate ## rank_str ## rank ## separator ## name

#define DDR5_PSTATE_RANK_MR_DEFINE(pstate, rank, name) \
        DDR5_PSTATE_RANK_MR_DEFINE_STR(DWC_DDRCTL_CINIT_DDR5_PSTATE, pstate, _RANK, rank, _, name)

#define DDR5_PSTATE_RANK_MR_SET(pstate, rank, mr_variable, mr_macro) \
    do { \
        mr_variable = DDR5_PSTATE_RANK_MR_DEFINE(pstate, rank, mr_macro); \
        SNPS_LOG(#mr_variable " = 0x%.8x", mr_variable); \
    } while (0)

#define DDR5_MR_RANK_CONFIG(mr_cfg, pstate, rank) \
    do { \
        /* MR58 */ \
        DDR5_PSTATE_RANK_MR_SET(pstate, rank, mr_cfg.mr58[rank].rfm_required, MR58_RFM_REQUIRED); \
        DDR5_PSTATE_RANK_MR_SET(pstate, rank, mr_cfg.mr58[rank].raa_initial_management_threshold, MR58_RAA_INITIAL_MANAGEMENT_THRESHOLD); \
        DDR5_PSTATE_RANK_MR_SET(pstate, rank, mr_cfg.mr58[rank].raa_maximum_management_threshold, MR58_RAA_MAXIMUM_MANAGEMENT_THRESHOLD); \
        /* MR59 */ \
        DDR5_PSTATE_RANK_MR_SET(pstate, rank, mr_cfg.mr59[rank].raa_counter_decr_per_ref_cmd, MR59_RAA_COUNTER_DECR_PER_REF_CMD); \
    } while (0)


/**
 * @brief Get the DDR5 Mode Register Kconfig comfigurations.
 *
 * @param cfg Configuration structure
 */
void ddrctl_kconfig_mode_registers_ddr5(SubsysHdlr_t *cfg)
{
#if defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5)

    DDR5_MR_CONFIG(cfg->memCtrlr_m.ddr5_mr[0], 0);
#if MEMC_NUM_RANKS > 0
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[0], 0, 0);
#endif /* MEMC_NUM_RANKS > 0 */
#ifdef MEMC_NUM_RANKS_GT_1
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[0], 0, 1);
#endif /* MEMC_NUM_RANKS_GT_1 */
#ifdef MEMC_NUM_RANKS_GT_2
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[0], 0, 2);
#endif /* MEMC_NUM_RANKS_GT_2 */
#ifdef MEMC_NUM_RANKS_GT_3
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[0], 0, 3);
#endif /* MEMC_NUM_RANKS_GT_3 */

#if NUM_PSTATES > 1
    DDR5_MR_CONFIG(cfg->memCtrlr_m.ddr5_mr[1], 1);
#if MEMC_NUM_RANKS > 0
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[1], 1, 0);
#endif /* MEMC_NUM_RANKS > 0 */
#ifdef MEMC_NUM_RANKS_GT_1
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[1], 1, 1);
#endif /* MEMC_NUM_RANKS_GT_1 */
#ifdef MEMC_NUM_RANKS_GT_2
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[1], 1, 2);
#endif /* MEMC_NUM_RANKS_GT_2 */
#ifdef MEMC_NUM_RANKS_GT_3
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[1], 1, 3);
#endif /* MEMC_NUM_RANKS_GT_3 */
#endif // NUM_PSTATES > 1

#if NUM_PSTATES > 2
    DDR5_MR_CONFIG(cfg->memCtrlr_m.ddr5_mr[2], 2);
#if MEMC_NUM_RANKS > 0
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[2], 2, 0);
#endif /* MEMC_NUM_RANKS > 0 */
#ifdef MEMC_NUM_RANKS_GT_1
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[2], 2, 1);
#endif /* MEMC_NUM_RANKS_GT_1 */
#ifdef MEMC_NUM_RANKS_GT_2
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[2], 2, 2);
#endif /* MEMC_NUM_RANKS_GT_2 */
#ifdef MEMC_NUM_RANKS_GT_3
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[2], 2, 3);
#endif /* MEMC_NUM_RANKS_GT_3 */
#endif // NUM_PSTATES > 2

#if NUM_PSTATES > 3
    DDR5_MR_CONFIG(cfg->memCtrlr_m.ddr5_mr[3], 3);
#if MEMC_NUM_RANKS > 0
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[3], 3, 0);
#endif /* MEMC_NUM_RANKS > 0 */
#ifdef MEMC_NUM_RANKS_GT_1
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[3], 3, 1);
#endif /* MEMC_NUM_RANKS_GT_1 */
#ifdef MEMC_NUM_RANKS_GT_2
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[3], 3, 2);
#endif /* MEMC_NUM_RANKS_GT_2 */
#ifdef MEMC_NUM_RANKS_GT_3
    DDR5_MR_RANK_CONFIG(cfg->memCtrlr_m.ddr5_mr[3], 3, 3);
#endif /* MEMC_NUM_RANKS_GT_3 */
#endif // NUM_PSTATES > 3

#endif // defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5)
}
