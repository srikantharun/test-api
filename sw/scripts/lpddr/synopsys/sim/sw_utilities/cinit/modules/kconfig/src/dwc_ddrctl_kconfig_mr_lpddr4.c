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

#define LPDDR4_MR_DEFINE_STR(prefix, pstate, separator, name) prefix ## pstate ## separator ## name

#define LPDDR4_MR_DEFINE(pstate, name) LPDDR4_MR_DEFINE_STR(DWC_DDRCTL_CINIT_LPDDR4_PSTATE, pstate, _, name)

#define LPDDR4_MR_SET(pstate, mr_variable, mr_macro) \
    do { \
        mr_variable = LPDDR4_MR_DEFINE(pstate, mr_macro); \
    } while (0)


#define LPDDR4_MR_CONFIG(mr_cfg, pstate) \
    do { \
        /* MR1 */ \
        LPDDR4_MR_SET(pstate, mr_cfg.mr1.rd_postamble, MR1_RD_POSTAMBLE); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr1.wr_recovery, MR1_WR_RECOVERY); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr1.rd_preamble, MR1_RD_PREAMBLE); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr1.wr_preamble, MR1_WR_PREAMBLE); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr1.burst_length, MR1_BURST_LENGTH); \
        /* MR2 */ \
        LPDDR4_MR_SET(pstate, mr_cfg.mr2.wls, MR2_WLS); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr2.rl_wl, MR2_RL_WL); \
        /* MR3 */ \
        LPDDR4_MR_SET(pstate, mr_cfg.mr3.pdds, MR3_PDDS); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr3.pprp, MR3_PPRP); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr3.pu_cal, MR3_PU_CAL); \
        /* MR11 */ \
        LPDDR4_MR_SET(pstate, mr_cfg.mr11.ca_odt, MR11_CA_ODT); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr11.dq_odt, MR11_DQ_ODT); \
        /* MR12 */ \
        LPDDR4_MR_SET(pstate, mr_cfg.mr12.vr_ca, MR12_VR_CA); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr12.vref_ca, MR12_VREF_CA); \
        /* MR13 */ \
        LPDDR4_MR_SET(pstate, mr_cfg.mr13.fsp_op,MR13_FSP_OP); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr13.fsp_wr, MR13_FSP_WR); \
        /* MR14 */ \
        LPDDR4_MR_SET(pstate, mr_cfg.mr14.vr_dq, MR14_VR_DQ); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr14.vref_dq, MR14_VREF_DQ); \
        /* MR22 */ \
        LPDDR4_MR_SET(pstate, mr_cfg.mr22.odtd, MR22_ODTD); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr22.odtd_ca, MR22_ODTD_CA); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr22.odtd_cs, MR22_ODTD_CS); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr22.odtd_ck, MR22_ODTD_CK); \
        LPDDR4_MR_SET(pstate, mr_cfg.mr22.soc_odt, MR22_SOC_ODT); \
    } while (0)

/**
 * @brief Get the LPDDR4 Mode Register Kconfig comfigurations.
 *
 * @param cfg Configuration structure
 */
void ddrctl_kconfig_mode_registers_lpddr4(SubsysHdlr_t *cfg)
{
#if defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR4) || defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR4X)
#if NUM_PSTATES > 0
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[0], 0);
#endif // NUM_PSTATES > 0
#if NUM_PSTATES > 1
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[1], 1);
#endif // NUM_PSTATES > 1
#if NUM_PSTATES > 2
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[2], 2);
#endif // NUM_PSTATES > 2
#if NUM_PSTATES > 3
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[3], 3);
#endif // NUM_PSTATES > 3
#if NUM_PSTATES > 4
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[4], 4);
#endif // NUM_PSTATES > 4
#if NUM_PSTATES > 5
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[5], 5);
#endif // NUM_PSTATES > 5
#if NUM_PSTATES > 6
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[6], 6);
#endif // NUM_PSTATES > 6
#if NUM_PSTATES > 7
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[7], 7);
#endif // NUM_PSTATES > 7
#if NUM_PSTATES > 8
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[8], 8);
#endif // NUM_PSTATES > 8
#if NUM_PSTATES > 9
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[9], 9);
#endif // NUM_PSTATES > 9
#if NUM_PSTATES > 10
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[10], 10);
#endif // NUM_PSTATES > 10
#if NUM_PSTATES > 11
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[11], 11);
#endif // NUM_PSTATES > 11
#if NUM_PSTATES > 12
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[12], 12);
#endif // NUM_PSTATES > 12
#if NUM_PSTATES > 13
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[13], 13);
#endif // NUM_PSTATES > 13
#if NUM_PSTATES > 14
    LPDDR4_MR_CONFIG(cfg->memCtrlr_m.lpddr4_mr[14], 14);
#endif // NUM_PSTATES > 14
#endif // defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR4) || defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR4X)
}
