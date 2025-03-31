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
#include "dwc_ddrctl_cinit_set_kconfig_uncategorized_cfg.h"

/**
 * @brief Function to set automatic periodical calibration events and transactions configurations.
 */
static void ddrctl_kconfig_ddr5_specific_features(void)
{

#ifdef DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5
    CFG->ddr5_cw.rw00.sdr_mode = DWC_DDRCTL_CINIT_RW00_SDR_MODE;

    CFG->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd = DWC_DDRCTL_CINIT_RW11_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD;
    CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[0][0] = DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_0_0;
    CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[0][0] = DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_0_0;
#if NUM_DCH > 1
    CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[0][1] = DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_0_1;
    CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[0][1] = DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_0_1;
#endif /* NUM_DCH > 1 */

#if NUM_PSTATES > 1
    CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[1][0] = DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_1_0;
    CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[1][0] = DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_1_0;

#if NUM_DCH > 1
    CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[1][1] = DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_1_1;
    CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[1][1] = DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_1_1;
#endif /* NUM_DCH > 1 */
#endif /* NUM_PSTATES > 1*/

#if NUM_PSTATES > 2
    CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[2][0] = DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_2_0;
    CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[2][0] = DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_2_0;
#if NUM_DCH > 1
    CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[2][1] = DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_2_1;
    CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[2][1] = DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_2_1;
#endif /* NUM_DCH > 1 */
#endif /* NUM_PSTATES > 2 */

#if NUM_PSTATES > 3
    CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[3][0] = DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_3_0;
    CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[3][0] = DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_3_0;
#if NUM_DCH > 1
    CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[3][1] = DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_3_1;
    CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[3][1] = DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_3_1;
#endif /* NUM_DCH > 1 */
#endif /* NUM_PSTATES > 3 */

    /*********************************************************************/
    /*                            pasdu                                  */
    /*********************************************************************/

    /*********************************************************************/
    /*                           Channel 0                               */
    /*********************************************************************/

    CFG->ddr5_pasdu_en.base_timer_interval_us[0] = DWC_DDRCTL_CINIT_BASE_TIMER_INTERVAL_US_0;
    CFG->ddr5_pasdu_en.all_rank_zqcal_en[0] = DWC_DDRCTL_CINIT_ALL_RANK_ZQCAL_EN_0;
    CFG->ddr5_pasdu_thres.all_rank_zqcal_thres[0] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_0_ALL_RANKS;
    CFG->ddr5_pasdu_thres.all_rank_zqlat_thres[0] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_0_ALL_RANKS;
    CFG->ddr5_pasdu_en.ctlupd_en[0] = DWC_DDRCTL_CINIT_CTLUPD_EN_0;
    CFG->ddr5_pasdu_thres.ctlupd_thres[0] = DWC_DDRCTL_CTL_UPD_TIMER_CH_0;

    /***********************     Rank 0     ***************************/

    CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][0] = DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_0;
    CFG->ddr5_pasdu_thres.dqsosc_thres[0][0] = DWC_DDRCTL_CINIT_DQSOSC_TIMER_CH_0_RANK_0;
    CFG->ddr5_pasdu_thres.tcr_mrr_thres[0][0] = DWC_DDRCTL_CINIT_TCR_TIMER_CH_0_RANK_0;
    CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][0] = DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_0;
    CFG->ddr5_pasdu_thres.per_rank_zqcal_thres[0][0] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_0_RANK_0;
    CFG->ddr5_pasdu_thres.per_rank_zqlat_thres[0][0] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_0_RANK_0;
    CFG->ddr5_pasdu_en.per_rank_ecs_en[0][0] = DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_0;
    CFG->ddr5_pasdu_thres.ecs_thres[0][0] = DWC_DDRCTL_CINIT_ECS_TIMER_CH_0_RANK_0;
#if MEMC_NUM_RANKS > 1

    /***********************     Rank 1     ***************************/

    CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][1] = DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_1;
    CFG->ddr5_pasdu_thres.dqsosc_thres[0][1] = DWC_DDRCTL_CINIT_DQSOSC_TIMER_CH_0_RANK_1;
    CFG->ddr5_pasdu_thres.tcr_mrr_thres[0][1] = DWC_DDRCTL_CINIT_TCR_TIMER_CH_0_RANK_1;
    CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][1] = DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_1;
    CFG->ddr5_pasdu_thres.per_rank_zqcal_thres[0][1] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_0_RANK_1;
    CFG->ddr5_pasdu_thres.per_rank_zqlat_thres[0][1] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_0_RANK_1;
    CFG->ddr5_pasdu_en.per_rank_ecs_en[0][1] = DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_1;
    CFG->ddr5_pasdu_thres.ecs_thres[0][1] = DWC_DDRCTL_CINIT_ECS_TIMER_CH_0_RANK_1;

#endif /* MEMC_NUM_RANKS > 1 */
#if MEMC_NUM_RANKS > 2

    /***********************     Rank 2     ***************************/

    CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][2] = DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_2;
    CFG->ddr5_pasdu_thres.dqsosc_thres[0][2] = DWC_DDRCTL_CINIT_DQSOSC_TIMER_CH_0_RANK_2;
    CFG->ddr5_pasdu_thres.tcr_mrr_thres[0][2] = DWC_DDRCTL_CINIT_TCR_TIMER_CH_0_RANK_2;
    CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][2] = DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_2;
    CFG->ddr5_pasdu_thres.per_rank_zqcal_thres[0][2] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_0_RANK_2;
    CFG->ddr5_pasdu_thres.per_rank_zqlat_thres[0][2] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_0_RANK_2;
    CFG->ddr5_pasdu_en.per_rank_ecs_en[0][2] = DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_2;
    CFG->ddr5_pasdu_thres.ecs_thres[0][2] = DWC_DDRCTL_CINIT_ECS_TIMER_CH_0_RANK_2;

#endif /* MEMC_NUM_RANKS > 2 */
#if MEMC_NUM_RANKS > 3

    /***********************     Rank 3     ***************************/

    CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][3] = DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_3;
    CFG->ddr5_pasdu_thres.dqsosc_thres[0][3] = DWC_DDRCTL_CINIT_DQSOSC_TIMER_CH_0_RANK_3;
    CFG->ddr5_pasdu_thres.tcr_mrr_thres[0][3] = DWC_DDRCTL_CINIT_TCR_TIMER_CH_0_RANK_3;
    CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][3] = DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_3;
    CFG->ddr5_pasdu_thres.per_rank_zqcal_thres[0][3] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_0_RANK_3;
    CFG->ddr5_pasdu_thres.per_rank_zqlat_thres[0][3] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_0_RANK_3;
    CFG->ddr5_pasdu_en.per_rank_ecs_en[0][3] = DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_3;
    CFG->ddr5_pasdu_thres.ecs_thres[0][3] = DWC_DDRCTL_CINIT_ECS_TIMER_CH_0_RANK_3;
#endif /* MEMC_NUM_RANKS > 3 */


#ifdef UMCTL2_NUM_DATA_CHANNEL_GT_1

    /*********************************************************************/
    /*                           Channel 1                               */
    /*********************************************************************/

    CFG->ddr5_pasdu_en.base_timer_interval_us[1] = DWC_DDRCTL_CINIT_BASE_TIMER_INTERVAL_US_1;
    CFG->ddr5_pasdu_en.all_rank_zqcal_en[1] = DWC_DDRCTL_CINIT_ALL_RANK_ZQCAL_EN_1;
    CFG->ddr5_pasdu_thres.all_rank_zqcal_thres[1] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_1_ALL_RANKS;
    CFG->ddr5_pasdu_thres.all_rank_zqlat_thres[1] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_1_ALL_RANKS;
    CFG->ddr5_pasdu_en.ctlupd_en[1] = DWC_DDRCTL_CINIT_CTLUPD_EN_1;
    CFG->ddr5_pasdu_thres.ctlupd_thres[1] = DWC_DDRCTL_CTL_UPD_TIMER_CH_1;
    /***********************     Rank 0     ***************************/

    CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][0] = DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_0;
    CFG->ddr5_pasdu_thres.dqsosc_thres[1][0] = DWC_DDRCTL_CINIT_DQSOSC_TIMER_CH_1_RANK_0;
    CFG->ddr5_pasdu_thres.tcr_mrr_thres[1][0] = DWC_DDRCTL_CINIT_TCR_TIMER_CH_1_RANK_0;
    CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][0] = DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_0;
    CFG->ddr5_pasdu_thres.per_rank_zqcal_thres[1][0] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_1_RANK_0;
    CFG->ddr5_pasdu_thres.per_rank_zqlat_thres[1][0] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_1_RANK_0;
    CFG->ddr5_pasdu_en.per_rank_ecs_en[1][0] = DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_0;
    CFG->ddr5_pasdu_thres.ecs_thres[1][0] = DWC_DDRCTL_CINIT_ECS_TIMER_CH_1_RANK_0;
#if MEMC_NUM_RANKS > 1

    /***********************     Rank 1     ***************************/
    CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][1] = DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_1;
    CFG->ddr5_pasdu_thres.dqsosc_thres[1][1] = DWC_DDRCTL_CINIT_DQSOSC_TIMER_CH_1_RANK_1;
    CFG->ddr5_pasdu_thres.tcr_mrr_thres[1][1] = DWC_DDRCTL_CINIT_TCR_TIMER_CH_1_RANK_1;
    CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][1] = DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_1;
    CFG->ddr5_pasdu_thres.per_rank_zqcal_thres[1][1] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_1_RANK_1;
    CFG->ddr5_pasdu_thres.per_rank_zqlat_thres[1][1] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_1_RANK_1;
    CFG->ddr5_pasdu_en.per_rank_ecs_en[1][1] = DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_1;
    CFG->ddr5_pasdu_thres.ecs_thres[1][1] = DWC_DDRCTL_CINIT_ECS_TIMER_CH_1_RANK_1;
#endif /* MEMC_NUM_RANKS > 1 */
#if MEMC_NUM_RANKS > 2

    /***********************     Rank 2     ***************************/
    CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][2] = DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_2;
    CFG->ddr5_pasdu_thres.dqsosc_thres[1][2] = DWC_DDRCTL_CINIT_DQSOSC_TIMER_CH_1_RANK_2;
    CFG->ddr5_pasdu_thres.tcr_mrr_thres[1][2] = DWC_DDRCTL_CINIT_TCR_TIMER_CH_1_RANK_2;
    CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][2] = DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_2;
    CFG->ddr5_pasdu_thres.per_rank_zqcal_thres[1][2] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_1_RANK_2;
    CFG->ddr5_pasdu_thres.per_rank_zqlat_thres[1][2] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_1_RANK_2;
    CFG->ddr5_pasdu_en.per_rank_ecs_en[1][2] = DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_2;
    CFG->ddr5_pasdu_thres.ecs_thres[1][2] = DWC_DDRCTL_CINIT_ECS_TIMER_CH_1_RANK_2;
#endif /* MEMC_NUM_RANKS > 2 */
#if MEMC_NUM_RANKS > 3

    /***********************     Rank 3     ***************************/

    CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][3] = DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_3;
    CFG->ddr5_pasdu_thres.dqsosc_thres[1][3] = DWC_DDRCTL_CINIT_DQSOSC_TIMER_CH_1_RANK_3;
    CFG->ddr5_pasdu_thres.tcr_mrr_thres[1][3] = DWC_DDRCTL_CINIT_TCR_TIMER_CH_1_RANK_3;
    CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][3] = DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_3;
    CFG->ddr5_pasdu_thres.per_rank_zqcal_thres[1][3] = DWC_DDRCTL_CINIT_ZQCAL_TIMER_CH_1_RANK_3;
    CFG->ddr5_pasdu_thres.per_rank_zqlat_thres[1][3] = DWC_DDRCTL_CINIT_ZQLAT_TIMER_CH_1_RANK_3;
    CFG->ddr5_pasdu_en.per_rank_ecs_en[1][3] = DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_3;
    CFG->ddr5_pasdu_thres.ecs_thres[1][3] = DWC_DDRCTL_CINIT_ECS_TIMER_CH_1_RANK_3;

#endif /* MEMC_NUM_RANKS > 3 */
#endif /* UMCTL2_NUM_DATA_CHANNEL_GT_1 */
#endif /* DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5 */
}


/**
 * @brief Function to set static, quasi-dynamic and dynamic confguration values from Kconfig.
 */
void dwc_ddrctl_cinit_set_kconfig_uncategorized_cfg(void)
{
    CFG->memCtrlr_m.sdram_bus_width = (dwc_sdram_bus_width_e)DWC_DDRCTL_CINIT_SDRAM_BUS_WIDTH;
#ifdef DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR4
    CFG->ddr4_cw.rc0f.latency_adder_nladd_to_all_dram_cmd = DWC_DDRCTL_CINIT_RC0F_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD;
#endif
#ifdef DDRCTL_DDR
    CFG->capar_retry_window_internal_delay_extra = DWC_DDRCTL_CINIT_CAPAR_RETRY_WINDOW_INTERNAL_DELAY_EXTRA;
#endif

    ddrctl_kconfig_ddr5_specific_features();
}
