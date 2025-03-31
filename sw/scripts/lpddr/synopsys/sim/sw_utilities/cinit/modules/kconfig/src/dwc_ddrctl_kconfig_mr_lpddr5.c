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
#include "dwc_ddrctl_kconfig_mr_lpddr5.h"


#define LPDDR5_KCFG_DEFINE_STR(prefix, pstate, separator, name) prefix ## pstate ## separator ## name

#define LPDDR5_KCFG_DEFINE(pstate, name) LPDDR5_KCFG_DEFINE_STR(DWC_DDRCTL_CINIT_LPDDR5_PSTATE, pstate, _, name)

#define LPDDR5_KCFG_SET(pstate, variable, macro) \
    do { \
        (variable) = LPDDR5_KCFG_DEFINE(pstate, macro); \
    } while (0)

#define LPDDR5_MEM_CONFIG(mem_cfg, pstate) \
    do { \
        /* BK/BG ORG (Bank/Bank Group Organization) */ \
        LPDDR5_KCFG_SET(pstate, mem_cfg.lpddr5_bk_bg_org[pstate], BK_BG); \
    } while (0)

#define LPDDR5_MR_CONFIG(mr_cfg, pstate) \
    do { \
        /* MR1 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr1.write_latency, MR1_WRITE_LATENCY); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr1.ck_mode, MR1_CK_MODE); \
        /* MR2 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr2.nwr, MR2_NWR); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr2.rl_nrtp, MR2_RL_NRTP); \
        /* MR3 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr3.wls, MR3_WLS); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr3.bk_bg_org, MR3_BK_BG_ORG); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr3.pdds, MR3_PDDS); \
        /* MR10 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr10.rdqs_pst_mode, MR10_RDQS_PST_MODE); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr10.rdqs_pst, MR10_RDQS_PST); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr10.rdqs_pre_2, MR10_RDQS_PRE_2); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr10.wck_pst, MR10_WCK_PST); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr10.rdqs_pre, MR10_RDQS_PRE); \
        /* MR11 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr11.cs_odt_op, MR11_CS_ODT_OP); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr11.ca_odt, MR11_CA_ODT); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr11.nt_odt, MR11_NT_ODT); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr11.dq_odt, MR11_DQ_ODT); \
        /* MR12 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr12.vbs, MR12_VBS); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr12.vref_ca, MR12_VREF_CA); \
        /* MR13 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr13.dual_vdd2, MR13_DUAL_VDD2); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr13.vro, MR13_VRO); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr13.thermal_offset, MR13_THERMAL_OFFSET); \
        /* MR14 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr14.vdlc, MR14_VDLC); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr14.vref_dq, MR14_VREF_DQ); \
        /* MR15 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr15.vref_dq, MR15_VREF_DQ); \
        /* MR16 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr16.cbt, MR16_CBT); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr16.vrcg, MR16_VRCG); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr16.fsp_op, MR16_FSP_OP); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr16.fsp_wr, MR16_FSP_WR); \
        /* MR17 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr17.odtd, MR17_ODTD); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr17.odtd_ca, MR17_ODTD_CA); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr17.odtd_cs, MR17_ODTD_CS); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr17.odtd_ck, MR17_ODTD_CK); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr17.soc_odt, MR17_SOC_ODT); \
        /* MR18 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr18.wck2ck_leveling, MR18_WCK2CK_LEVELING); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr18.wck_odt, MR18_WCK_ODT); \
        /* MR19 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr19.dvfsq, MR19_DVFSQ); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr19.dvfsc, MR19_DVFSC); \
        /* MR20 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr20.wck_mode, MR20_WCK_MODE); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr20.rdqs, MR20_RDQS); \
        /* MR21 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr21.dcfe, MR21_DCFE); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr21.wxfs, MR21_WXFS); \
        /* MR23 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr23.pasr_mask, MR23_PASR_MASK); \
        /* MR24 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr24.dfeql, MR24_DFEQL); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr24.dfequ, MR24_DFEQU); \
        /* MR25 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr25.ck_bus_term, MR25_CK_BUS_TERM); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr25.ca_bus_term, MR25_CA_BUS_TERM); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr25.parc, MR25_PARC); \
        /* MR28 */ \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr28.zq_int, MR28_ZQ_INT); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr28.zq_stop, MR28_ZQ_STOP); \
        LPDDR5_KCFG_SET(pstate, mr_cfg.mr28.zq_reset, MR28_ZQ_RESET); \
         \
    } while (0)


/**
 * @brief Get the LPDDR5 Mode Register Kconfig comfigurations.
 *
 * @param cfg Configuration structure
 */
void ddrctl_kconfig_mode_registers_lpddr5(SubsysHdlr_t *cfg)
{
#if defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR5) || defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR5X)
#if NUM_PSTATES > 0
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[0], 0);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 0);
#endif // NUM_PSTATES > 0
#if NUM_PSTATES > 1
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[1], 1);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 1);
#endif // NUM_PSTATES > 1
#if NUM_PSTATES > 2
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[2], 2);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 2);
#endif // NUM_PSTATES > 2
#if NUM_PSTATES > 3
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[3], 3);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 3);
#endif // NUM_PSTATES > 3
#if NUM_PSTATES > 4
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[4], 4);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 4);
#endif // NUM_PSTATES > 4
#if NUM_PSTATES > 5
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[5], 5);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 5);
#endif // NUM_PSTATES > 5
#if NUM_PSTATES > 6
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[6], 6);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 6);
#endif // NUM_PSTATES > 6
#if NUM_PSTATES > 7
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[7], 7);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 7);
#endif // NUM_PSTATES > 7
#if NUM_PSTATES > 8
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[8], 8);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 8);
#endif // NUM_PSTATES > 8
#if NUM_PSTATES > 9
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[9], 9);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 9);
#endif // NUM_PSTATES > 9
#if NUM_PSTATES > 10
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[10], 10);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 10);
#endif // NUM_PSTATES > 10
#if NUM_PSTATES > 11
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[11], 11);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 11);
#endif // NUM_PSTATES > 11
#if NUM_PSTATES > 12
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[12], 12);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 12);
#endif // NUM_PSTATES > 12
#if NUM_PSTATES > 13
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[13], 13);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 13);
#endif // NUM_PSTATES > 13
#if NUM_PSTATES > 14
    LPDDR5_MR_CONFIG(cfg->memCtrlr_m.lpddr5_mr[14], 14);
    LPDDR5_MEM_CONFIG(cfg->spdData_m, 14);
#endif // NUM_PSTATES > 14
#endif // defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR5) || defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR5X)
}
