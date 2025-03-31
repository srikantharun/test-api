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

#define DDR4_MR_DEFINE_STR(prefix, pstate, separator, name) prefix ## pstate ## separator ## name

#define DDR4_MR_DEFINE(pstate, name) DDR4_MR_DEFINE_STR(DWC_DDRCTL_CINIT_DDR4_PSTATE, pstate, _, name)

#define DDR4_MR_SET(pstate, mr_variable, mr_macro) \
    do { \
        mr_variable = DDR4_MR_DEFINE(pstate, mr_macro); \
    } while (0)


#define DDR4_MR_CONFIG(mr_cfg, pstate) \
    do { \
        /* MR0 */ \
        DDR4_MR_SET(pstate, mr_cfg.mr0.wr_recovery, MR0_WR_RECOVERY); \
        DDR4_MR_SET(pstate, mr_cfg.mr0.dll_reset, MR0_DLL_RESET); \
        DDR4_MR_SET(pstate, mr_cfg.mr0.cl, MR0_CL); \
        DDR4_MR_SET(pstate, mr_cfg.mr0.burst_type, MR0_BURST_TYPE); \
        /* MR1 */ \
        DDR4_MR_SET(pstate, mr_cfg.mr1.rtt_nom, MR1_RTT_NOM); \
        DDR4_MR_SET(pstate, mr_cfg.mr1.wr_leveling_enable, MR1_WR_LEVELING_ENABLE); \
        DDR4_MR_SET(pstate, mr_cfg.mr1.al, MR1_AL); \
        DDR4_MR_SET(pstate, mr_cfg.mr1.output_driver_impedance, MR1_OUTPUT_DRIVER_IMPEDANCE); \
        /* MR2 */ \
        DDR4_MR_SET(pstate, mr_cfg.mr2.rtt_wr, MR2_RTT_WR); \
        DDR4_MR_SET(pstate, mr_cfg.mr2.auto_self_ref, MR2_AUTO_SELF_REF); \
        DDR4_MR_SET(pstate, mr_cfg.mr2.cwl, MR2_CWL); \
        /* MR3 */ \
        DDR4_MR_SET(pstate, mr_cfg.mr3.wcl, MR3_WCL); \
        DDR4_MR_SET(pstate, mr_cfg.mr3.mpr_op, MR3_MPR_OP); \
        DDR4_MR_SET(pstate, mr_cfg.mr3.mpr_ps, MR3_MPR_PS); \
        /* MR4 */ \
        DDR4_MR_SET(pstate, mr_cfg.mr4.rd_preamble, MR4_RD_PREAMBLE); \
        DDR4_MR_SET(pstate, mr_cfg.mr4.selfref_abort, MR4_SELFREF_ABORT); \
        DDR4_MR_SET(pstate, mr_cfg.mr4.cal, MR4_CAL); \
        DDR4_MR_SET(pstate, mr_cfg.mr4.refresh_mode, MR4_REFRESH_MODE); \
        DDR4_MR_SET(pstate, mr_cfg.mr4.refresh_range, MR4_REFRESH_RANGE); \
        /* MR5 */ \
        DDR4_MR_SET(pstate, mr_cfg.mr5.rtt_park, MR5_RTT_PARK); \
        DDR4_MR_SET(pstate, mr_cfg.mr5.dis_odt_input_buf_in_pd, MR5_DIS_ODT_INPUT_BUF_IN_PD); \
        DDR4_MR_SET(pstate, mr_cfg.mr5.parity_latency_mode, MR5_PARITY_LATENCY_MODE); \
        /* MR6 */ \
        DDR4_MR_SET(pstate, mr_cfg.mr6.tccd_l, MR6_TCCD_L); \
    } while (0)

/**
 * @brief Get the DDR4 Mode Register Kconfig comfigurations.
 *
 * @param cfg Configuration structure
 */
void ddrctl_kconfig_mode_registers_ddr4(SubsysHdlr_t *cfg)
{
#if defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR4)
#if NUM_PSTATES > 0
    DDR4_MR_CONFIG(cfg->memCtrlr_m.ddr4_mr[0], 0);
#endif // NUM_PSTATES > 0
#if NUM_PSTATES > 1
    DDR4_MR_CONFIG(cfg->memCtrlr_m.ddr4_mr[1], 1);
#endif // NUM_PSTATES > 1
#if NUM_PSTATES > 2
    DDR4_MR_CONFIG(cfg->memCtrlr_m.ddr4_mr[2], 2);
#endif // NUM_PSTATES > 2
#if NUM_PSTATES > 3
    DDR4_MR_CONFIG(cfg->memCtrlr_m.ddr4_mr[3], 3);
#endif // NUM_PSTATES > 3
#endif // defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR4)
}
