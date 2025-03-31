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


#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_types.h"

#define CFG_MR_DDR4_PREFIX   "CONFIG_DWC_DDRCTL_CINIT_DDR4_PSTATE"
#define CFG_MR_DDR5_PREFIX   "CONFIG_DWC_DDRCTL_CINIT_DDR5_PSTATE"
#define CFG_MR_LPDDR4_PREFIX "CONFIG_DWC_DDRCTL_CINIT_LPDDR4_PSTATE"
#define CFG_MR_LPDDR5_PREFIX "CONFIG_DWC_DDRCTL_CINIT_LPDDR5_PSTATE"

static void gen_cfg_mr_ddr4(SubsysHdlr_t *cfg)
{
#ifdef DDRCTL_DDR
    ddr4_mode_registers_t *mr_cfg;
    uint8_t pstate;
    for(pstate = 0; pstate < cfg->num_pstates; pstate++) {
        mr_cfg = &(cfg->memCtrlr_m.ddr4_mr[pstate]);
        /* MR0 */
        SNPS_DEFCFG_WR("%s%u_MR0_WR_RECOVERY=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr0.wr_recovery);
        SNPS_DEFCFG_WR("%s%u_MR0_DLL_RESET=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr0.dll_reset);
        SNPS_DEFCFG_WR("%s%u_MR0_CL=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr0.cl);
        SNPS_DEFCFG_WR("%s%u_MR0_BURST_TYPE=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr0.burst_type);
        /* MR1 */
        SNPS_DEFCFG_WR("%s%u_MR1_RTT_NOM=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr1.rtt_nom);
        SNPS_DEFCFG_WR("%s%u_MR1_WR_LEVELING_ENABLE=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr1.wr_leveling_enable);
        SNPS_DEFCFG_WR("%s%u_MR1_AL=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr1.al);
        SNPS_DEFCFG_WR("%s%u_MR1_OUTPUT_DRIVER_IMPEDANCE=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr1.output_driver_impedance);
        /* MR2 */
        SNPS_DEFCFG_WR("%s%u_MR2_RTT_WR=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr2.rtt_wr);
        SNPS_DEFCFG_WR("%s%u_MR2_AUTO_SELF_REF=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr2.auto_self_ref);
        SNPS_DEFCFG_WR("%s%u_MR2_CWL=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr2.cwl);
        /* MR3 */
        SNPS_DEFCFG_WR("%s%u_MR3_WCL=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr3.wcl);
        SNPS_DEFCFG_WR("%s%u_MR3_MPR_OP=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr3.mpr_op);
        SNPS_DEFCFG_WR("%s%u_MR3_MPR_PS=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr3.mpr_ps);
        /* MR4 */
        SNPS_DEFCFG_WR("%s%u_MR4_RD_PREAMBLE=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr4.rd_preamble);
        SNPS_DEFCFG_WR("%s%u_MR4_SELFREF_ABORT=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr4.selfref_abort);
        SNPS_DEFCFG_WR("%s%u_MR4_CAL=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr4.cal);
        SNPS_DEFCFG_WR("%s%u_MR4_REFRESH_MODE=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr4.refresh_mode);
        SNPS_DEFCFG_WR("%s%u_MR4_REFRESH_RANGE=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr4.refresh_range);
        /* MR5 */
        SNPS_DEFCFG_WR("%s%u_MR5_RTT_PARK=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr5.rtt_park);
        SNPS_DEFCFG_WR("%s%u_MR5_DIS_ODT_INPUT_BUF_IN_PD=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr5.dis_odt_input_buf_in_pd);
        SNPS_DEFCFG_WR("%s%u_MR5_PARITY_LATENCY_MODE=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr5.parity_latency_mode);
        /* MR6 */
        SNPS_DEFCFG_WR("%s%u_MR6_TCCD_L=%u", CFG_MR_DDR4_PREFIX, pstate, mr_cfg->mr6.tccd_l);
    }
#endif /* DDRCTL_DDR */
}


static void gen_cfg_mr_ddr5(SubsysHdlr_t *cfg)
{
#ifdef DDRCTL_DDR
    ddr5_mode_registers_t *mr_cfg;
    uint8_t pstate;
    uint8_t rank;

    for(pstate = 0; pstate < cfg->num_pstates; pstate++) {
        mr_cfg = &(cfg->memCtrlr_m.ddr5_mr[pstate]);
        /* MR0 */
        SNPS_DEFCFG_WR("%s%u_MR0_CL=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr0.cl);
        /* MR2 */
        SNPS_DEFCFG_WR("%s%u_MR2_RD_PREAMBLE_ENABLE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr2.rd_preamble_enable);
        SNPS_DEFCFG_WR("%s%u_MR2_WR_LEVELING=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr2.wr_leveling);
        SNPS_DEFCFG_WR("%s%u_MR2_DDR5_2N_MODE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr2.ddr5_2n_mode);
        SNPS_DEFCFG_WR("%s%u_MR2_MPSM=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr2.mpsm);
        SNPS_DEFCFG_WR("%s%u_MR2_CS_ASSERTION_DURATION=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr2.cs_assertion_duration);
        SNPS_DEFCFG_WR("%s%u_MR2_DEV15_MPSM=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr2.dev15_mpsm);
        SNPS_DEFCFG_WR("%s%u_MR2_INTERNAL_WR_TIMING=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr2.internal_wr_timing);
        /* MR3 */
        SNPS_DEFCFG_WR("%s%u_MR3_WR_LEVELING_INTERNAL_LOWER_BYTE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr3.wr_leveling_internal_lower_byte);
        SNPS_DEFCFG_WR("%s%u_MR3_WR_LEVELING_INTERNAL_UPPER_BYTE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr3.wr_leveling_internal_upper_byte);
        /* MR4 */
        SNPS_DEFCFG_WR("%s%u_MR4_REFRESH_RATE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr4.refresh_rate);
        /* MR5 */
        SNPS_DEFCFG_WR("%s%u_MR5_DATA_OUTPUT_DISABLE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr5.data_output_disable);
        SNPS_DEFCFG_WR("%s%u_MR5_PULL_UP_OUTPUT_DRV_IMPEDANCE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr5.pull_up_output_drv_impedance);
        SNPS_DEFCFG_WR("%s%u_MR5_TDQS_ENABLE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr5.tdqs_enable);
        SNPS_DEFCFG_WR("%s%u_MR5_DM_ENABLE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr5.dm_enable);
        SNPS_DEFCFG_WR("%s%u_MR5_PULL_DOWN_OUTPUT_DRV_IMPEDANCE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr5.pull_down_output_drv_impedance);
        /* MR6 */
        SNPS_DEFCFG_WR("%s%u_MR6_TRTP=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr6.trtp);
        SNPS_DEFCFG_WR("%s%u_MR6_WR_RECOVERY=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr6.wr_recovery);
        /* MR8 */
        SNPS_DEFCFG_WR("%s%u_MR8_RD_PREAMBLE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr8.rd_preamble);
        SNPS_DEFCFG_WR("%s%u_MR8_WR_PREAMBLE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr8.wr_preamble);
        SNPS_DEFCFG_WR("%s%u_MR8_RD_POSTAMBLE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr8.rd_postamble);
        SNPS_DEFCFG_WR("%s%u_MR8_WR_POSTAMBLE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr8.wr_postamble);
        /* MR13 */
        SNPS_DEFCFG_WR("%s%u_MR13_TCCD_L=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr13.tccd_l);
        /* MR34 */
        SNPS_DEFCFG_WR("%s%u_MR34_RTT_PARK=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr34.rtt_park);
        SNPS_DEFCFG_WR("%s%u_MR34_RTT_WR=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr34.rtt_wr);
        /* MR35 */
        SNPS_DEFCFG_WR("%s%u_MR35_RTT_NOM_WR=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr35.rtt_nom_wr);
        SNPS_DEFCFG_WR("%s%u_MR35_RTT_NOM_RD=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr35.rtt_nom_rd);
        /* MR37 */
        SNPS_DEFCFG_WR("%s%u_MR37_ODTLON_WR_OFFSET=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr37.odtlon_wr_offset);
        SNPS_DEFCFG_WR("%s%u_MR37_ODTLOFF_WR_OFFSET=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr37.odtloff_wr_offset);
        /* MR38 */
        SNPS_DEFCFG_WR("%s%u_MR38_ODTLON_WR_NT_OFFSET=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr38.odtlon_wr_nt_offset);
        SNPS_DEFCFG_WR("%s%u_MR38_ODTLOFF_WR_NT_OFFSET=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr38.odtloff_wr_nt_offset);
        /* MR39 */
        SNPS_DEFCFG_WR("%s%u_MR39_ODTLON_RD_NT_OFFSET=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr39.odtlon_rd_nt_offset);
        SNPS_DEFCFG_WR("%s%u_MR39_ODTLOFF_RD_NT_OFFSET=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr39.odtloff_rd_nt_offset);
        /* MR40 */
        SNPS_DEFCFG_WR("%s%u_MR40_RD_DQS_OFFSET=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr40.rd_dqs_offset);
        /* MR45 */
        SNPS_DEFCFG_WR("%s%u_MR45_OSC_RUN_TIME=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr45.osc_run_time);
        /* MR50 */
        SNPS_DEFCFG_WR("%s%u_MR50_WR_CRC_ERROR_STATUS=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr50.wr_crc_error_status);
        SNPS_DEFCFG_WR("%s%u_MR50_WR_CRC_AUTO_DISABLE_ENABLE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr50.wr_crc_auto_disable_enable);
        SNPS_DEFCFG_WR("%s%u_MR50_WR_CRC_AUTO_DISABLE_STATUS=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr50.wr_crc_auto_disable_status);
        /* MR51 */
        SNPS_DEFCFG_WR("%s%u_MR51_WR_CRC_AUTO_DISABLE_THRE=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr51.wr_crc_auto_disable_thre);
        /* MR52 */
        SNPS_DEFCFG_WR("%s%u_MR52_WR_CRC_AUTO_DISABLE_WINDOW=%u", CFG_MR_DDR5_PREFIX, pstate, mr_cfg->mr52.wr_crc_auto_disable_window);

        for(rank = 0; rank < cfg->spdData_m.num_ranks; rank++) {
            /* MR58 */
            SNPS_DEFCFG_WR("%s%u_RANK%u_MR58_RFM_REQUIRED=%u", CFG_MR_DDR5_PREFIX, pstate, rank, mr_cfg->mr58[rank].rfm_required);
            SNPS_DEFCFG_WR("%s%u_RANK%u_MR58_RAA_INITIAL_MANAGEMENT_THRESHOLD=%u", CFG_MR_DDR5_PREFIX, pstate, rank, mr_cfg->mr58[rank].raa_initial_management_threshold);
            SNPS_DEFCFG_WR("%s%u_RANK%u_MR58_RAA_MAXIMUM_MANAGEMENT_THRESHOLD=%u", CFG_MR_DDR5_PREFIX, pstate, rank, mr_cfg->mr58[rank].raa_maximum_management_threshold);
            /* MR59 */
            SNPS_DEFCFG_WR("%s%u_RANK%u_MR59_RAA_COUNTER_DECR_PER_REF_CMD=%u", CFG_MR_DDR5_PREFIX, pstate, rank, mr_cfg->mr59[rank].raa_counter_decr_per_ref_cmd);
        }
    }
#endif /* DDRCTL_DDR */
}


static void gen_cfg_mr_lpddr4(SubsysHdlr_t *cfg)
{
#ifdef DDRCTL_LPDDR
    lpddr4_mode_registers_t *mr_cfg;
    uint8_t pstate;
    for(pstate = 0; pstate < cfg->num_pstates; pstate++) {
        mr_cfg = &(cfg->memCtrlr_m.lpddr4_mr[pstate]);
        /* MR1 */
        SNPS_DEFCFG_WR("%s%u_MR1_RD_POSTAMBLE=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr1.rd_postamble);
        SNPS_DEFCFG_WR("%s%u_MR1_WR_RECOVERY=%u",  CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr1.wr_recovery);
        SNPS_DEFCFG_WR("%s%u_MR1_RD_PREAMBLE=%u",  CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr1.rd_preamble);
        SNPS_DEFCFG_WR("%s%u_MR1_WR_PREAMBLE=%u",  CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr1.wr_preamble);
        SNPS_DEFCFG_WR("%s%u_MR1_BURST_LENGTH=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr1.burst_length);
        /* MR2 */
        SNPS_DEFCFG_WR("%s%u_MR2_WLS=%u",   CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr2.wls);
        SNPS_DEFCFG_WR("%s%u_MR2_RL_WL=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr2.rl_wl);
        /* MR3 */
        SNPS_DEFCFG_WR("%s%u_MR3_PDDS=%u",         CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr3.pdds);
        SNPS_DEFCFG_WR("%s%u_MR3_PPRP=%u",         CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr3.pprp);
        SNPS_DEFCFG_WR("%s%u_MR3_PU_CAL=%u",       CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr3.pu_cal);
        /* MR11 */
        SNPS_DEFCFG_WR("%s%u_MR11_CA_ODT=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr11.ca_odt);
        SNPS_DEFCFG_WR("%s%u_MR11_DQ_ODT=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr11.dq_odt);
        /* MR12 */
        SNPS_DEFCFG_WR("%s%u_MR12_VR_CA=%u",   CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr12.vr_ca);
        SNPS_DEFCFG_WR("%s%u_MR12_VREF_CA=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr12.vref_ca);
        /* MR13 */
        SNPS_DEFCFG_WR("%s%u_MR13_FSP_OP=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr13.fsp_op);
        SNPS_DEFCFG_WR("%s%u_MR13_FSP_WR=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr13.fsp_wr);
        /* MR14 */
        SNPS_DEFCFG_WR("%s%u_MR14_VR_DQ=%u",   CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr14.vr_dq);
        SNPS_DEFCFG_WR("%s%u_MR14_VREF_DQ=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr14.vref_dq);
        /* MR22 */
        SNPS_DEFCFG_WR("%s%u_MR22_ODTD=%u",    CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr22.odtd);
        SNPS_DEFCFG_WR("%s%u_MR22_ODTD_CA=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr22.odtd_ca);
        SNPS_DEFCFG_WR("%s%u_MR22_ODTD_CS=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr22.odtd_cs);
        SNPS_DEFCFG_WR("%s%u_MR22_ODTD_CK=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr22.odtd_ck);
        SNPS_DEFCFG_WR("%s%u_MR22_SOC_ODT=%u", CFG_MR_LPDDR4_PREFIX, pstate, mr_cfg->mr22.soc_odt);
    }
#endif /* DDRCTL_LPDDR */
}

static void gen_cfg_mr_lpddr5(SubsysHdlr_t *cfg)
{
#ifdef DDRCTL_LPDDR
    lpddr5_mode_registers_t *mr_cfg;
    uint8_t pstate;
    for(pstate = 0; pstate < cfg->num_pstates; pstate++) {
        mr_cfg = &(cfg->memCtrlr_m.lpddr5_mr[pstate]);
        /* MR1 */
        SNPS_DEFCFG_WR("%s%u_MR1_WRITE_LATENCY=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr1.write_latency);
        SNPS_DEFCFG_WR("%s%u_MR1_CK_MODE=%u",       CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr1.ck_mode);
        /* MR2 */
        SNPS_DEFCFG_WR("%s%u_MR2_NWR=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr2.nwr);
        SNPS_DEFCFG_WR("%s%u_MR2_RL_NRTP=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr2.rl_nrtp);
        /* MR3 */
        SNPS_DEFCFG_WR("%s%u_MR3_WLS=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr3.wls);
        SNPS_DEFCFG_WR("%s%u_MR3_BK_BG_ORG=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr3.bk_bg_org);
        SNPS_DEFCFG_WR("%s%u_MR3_PDDS=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr3.pdds);
        /* MR10 */
        SNPS_DEFCFG_WR("%s%u_MR10_RDQS_PST_MODE=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr10.rdqs_pst_mode);
        SNPS_DEFCFG_WR("%s%u_MR10_RDQS_PST=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr10.rdqs_pst);
        SNPS_DEFCFG_WR("%s%u_MR10_RDQS_PRE_2=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr10.rdqs_pre_2);
        SNPS_DEFCFG_WR("%s%u_MR10_WCK_PST=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr10.wck_pst);
        SNPS_DEFCFG_WR("%s%u_MR10_RDQS_PRE=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr10.rdqs_pre);
        /* MR11 */
        SNPS_DEFCFG_WR("%s%u_MR11_CS_ODT_OP=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr11.cs_odt_op);
        SNPS_DEFCFG_WR("%s%u_MR11_CA_ODT=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr11.ca_odt);
        SNPS_DEFCFG_WR("%s%u_MR11_NT_ODT=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr11.nt_odt);
        SNPS_DEFCFG_WR("%s%u_MR11_DQ_ODT=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr11.dq_odt);
        /* MR12 */
        SNPS_DEFCFG_WR("%s%u_MR12_VBS=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr12.vbs);
        SNPS_DEFCFG_WR("%s%u_MR12_VREF_CA=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr12.vref_ca);
        /* MR13 */
        SNPS_DEFCFG_WR("%s%u_MR13_DUAL_VDD2=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr13.dual_vdd2);
        SNPS_DEFCFG_WR("%s%u_MR13_VRO=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr13.vro);
        SNPS_DEFCFG_WR("%s%u_MR13_THERMAL_OFFSET=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr13.thermal_offset);
        /* MR14 */
        SNPS_DEFCFG_WR("%s%u_MR14_VDLC=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr14.vdlc);
        SNPS_DEFCFG_WR("%s%u_MR14_VREF_DQ=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr14.vref_dq);
        /* MR15 */
        SNPS_DEFCFG_WR("%s%u_MR15_VREF_DQ=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr15.vref_dq);
        /* MR16 */
        SNPS_DEFCFG_WR("%s%u_MR16_CBT=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr16.cbt);
        SNPS_DEFCFG_WR("%s%u_MR16_VRCG=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr16.vrcg);
        SNPS_DEFCFG_WR("%s%u_MR16_FSP_OP=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr16.fsp_op);
        SNPS_DEFCFG_WR("%s%u_MR16_FSP_WR=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr16.fsp_wr);
        /* MR17 */
        SNPS_DEFCFG_WR("%s%u_MR17_ODTD=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr17.odtd);
        SNPS_DEFCFG_WR("%s%u_MR17_ODTD_CA=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr17.odtd_ca);
        SNPS_DEFCFG_WR("%s%u_MR17_ODTD_CS=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr17.odtd_cs);
        SNPS_DEFCFG_WR("%s%u_MR17_ODTD_CK=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr17.odtd_ck);
        SNPS_DEFCFG_WR("%s%u_MR17_SOC_ODT=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr17.soc_odt);
        /* MR18 */
        SNPS_DEFCFG_WR("%s%u_MR18_WCK2CK_LEVELING=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr18.wck2ck_leveling);
        SNPS_DEFCFG_WR("%s%u_MR18_WCK_ODT=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr18.wck_odt);
        /* MR19 */
        SNPS_DEFCFG_WR("%s%u_MR19_DVFSQ=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr19.dvfsq);
        SNPS_DEFCFG_WR("%s%u_MR19_DVFSC=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr19.dvfsc);
        /* MR20 */
        SNPS_DEFCFG_WR("%s%u_MR20_WCK_MODE=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr20.wck_mode);
        SNPS_DEFCFG_WR("%s%u_MR20_RDQS=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr20.rdqs);
        /* MR21 */
        SNPS_DEFCFG_WR("%s%u_MR21_DCFE=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr21.dcfe);
        SNPS_DEFCFG_WR("%s%u_MR21_WXFS=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr21.wxfs);
        /* MR23 */
        SNPS_DEFCFG_WR("%s%u_MR23_PASR_MASK=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr23.pasr_mask);
        /* MR24 */
        SNPS_DEFCFG_WR("%s%u_MR24_DFEQL=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr24.dfeql);
        SNPS_DEFCFG_WR("%s%u_MR24_DFEQU=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr24.dfequ);
        /* MR25 */
        SNPS_DEFCFG_WR("%s%u_MR25_CK_BUS_TERM=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr25.ck_bus_term);
        SNPS_DEFCFG_WR("%s%u_MR25_CA_BUS_TERM=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr25.ca_bus_term);
        SNPS_DEFCFG_WR("%s%u_MR25_PARC=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr25.parc);
        /* MR28 */
        SNPS_DEFCFG_WR("%s%u_MR28_ZQ_INT=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr28.zq_int);
        SNPS_DEFCFG_WR("%s%u_MR28_ZQ_STOP=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr28.zq_stop);
        SNPS_DEFCFG_WR("%s%u_MR28_ZQ_RESET=%u", CFG_MR_LPDDR5_PREFIX, pstate, mr_cfg->mr28.zq_reset);
    }
#endif /* DDRCTL_LPDDR */
}

/**
 * @brief Function to create the defconfig more registers configuration
 *
 * @param cfg
 */
void dwc_ddrctl_cinit_gen_cfg_mr(SubsysHdlr_t *cfg)
{
    switch (cfg->spdData_m.sdram_protocol) {
        case DWC_DDR4:
            gen_cfg_mr_ddr4(cfg);
            break;
        case DWC_DDR5:
            gen_cfg_mr_ddr5(cfg);
            break;
        case DWC_LPDDR4:
            gen_cfg_mr_lpddr4(cfg);
            break;
        case DWC_LPDDR5:
            gen_cfg_mr_lpddr5(cfg);
            break;
    }
}

