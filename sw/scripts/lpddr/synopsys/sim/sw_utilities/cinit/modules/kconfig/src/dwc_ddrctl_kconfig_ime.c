
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



#include "dwc_ddrctl_kconfig_ime.h"
#include "dwc_ddrctl_cinit_defines.h"

#include ".autoconf.h"


#define IME_DEFINE_STR(prefix, channel, middle, reg_number, separator, name) \
        prefix ## channel ## middle ## reg_number ## separator ## name

#define IME_DEFINE(channel, reg_number, name) IME_DEFINE_STR(DDRCTL_IME_CH, channel, _REGION, reg_number, _, name)

#define IME_CFG_SET(channel, reg_number, cfg, cfg_macro) \
    do { \
        cfg = IME_DEFINE(channel, reg_number, cfg_macro); \
    } while (0)

#define IME_REGION_CONFIG(ime_cfg, channel, reg_number) \
    do { \
        IME_CFG_SET(channel, reg_number, ime_cfg.region[reg_number].address_start, ADDR_START); \
        IME_CFG_SET(channel, reg_number, ime_cfg.region[reg_number].address_end,   ADDR_END); \
        IME_CFG_SET(channel, reg_number, ime_cfg.region[reg_number].c_key_id[0],   PRI_CKEY_ID); \
        IME_CFG_SET(channel, reg_number, ime_cfg.region[reg_number].t_key_id[0],   PRI_TKEY_ID); \
        IME_CFG_SET(channel, reg_number, ime_cfg.region[reg_number].c_key_id[1],   SEC_CKEY_ID); \
        IME_CFG_SET(channel, reg_number, ime_cfg.region[reg_number].t_key_id[1],   SEC_TKEY_ID); \
    } while (0)

void ddrctl_kconfig_ime(SubsysHdlr_t *cinit_cfg)
{

#ifdef DDRCTL_SECURE
    cinit_cfg->ime_cfg[0].enable = DDRCTL_IME_EN_CH0;
    cinit_cfg->ime_cfg[0].key_size = DDRCTL_IME_KEY_SIZE_CH0;

#if NUM_DCH > 1
    cinit_cfg->ime_cfg[1].enable = DDRCTL_IME_EN_CH1;
    cinit_cfg->ime_cfg[1].key_size = DDRCTL_IME_KEY_SIZE_CH1;
#endif // NUM_DCH > 1

#if DWC_IME_REGION_ADDR_EN == 1
#if DWC_IME_NUM_REGIONS > 0
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 0);
#endif // DWC_IME_NUM_REGIONS > 0
#if DWC_IME_NUM_REGIONS > 1
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 1);
#endif // DWC_IME_NUM_REGIONS > 1
#if DWC_IME_NUM_REGIONS > 2
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 2);
#endif // DWC_IME_NUM_REGIONS > 2
#if DWC_IME_NUM_REGIONS > 3
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 3);
#endif // DWC_IME_NUM_REGIONS > 3
#if DWC_IME_NUM_REGIONS > 4
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 4);
#endif // DWC_IME_NUM_REGIONS > 4
#if DWC_IME_NUM_REGIONS > 5
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 5);
#endif // DWC_IME_NUM_REGIONS > 5
#if DWC_IME_NUM_REGIONS > 6
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 6);
#endif // DWC_IME_NUM_REGIONS > 6
#if DWC_IME_NUM_REGIONS > 7
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 7);
#endif // DWC_IME_NUM_REGIONS > 7
#if DWC_IME_NUM_REGIONS > 8
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 8);
#endif // DWC_IME_NUM_REGIONS > 8
#if DWC_IME_NUM_REGIONS > 9
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 9);
#endif // DWC_IME_NUM_REGIONS > 9
#if DWC_IME_NUM_REGIONS > 10
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 10);
#endif // DWC_IME_NUM_REGIONS > 10
#if DWC_IME_NUM_REGIONS > 11
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 11);
#endif // DWC_IME_NUM_REGIONS > 11
#if DWC_IME_NUM_REGIONS > 12
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 12);
#endif // DWC_IME_NUM_REGIONS > 12
#if DWC_IME_NUM_REGIONS > 13
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 13);
#endif // DWC_IME_NUM_REGIONS > 13
#if DWC_IME_NUM_REGIONS > 14
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 14);
#endif // DWC_IME_NUM_REGIONS > 14
#if DWC_IME_NUM_REGIONS > 15
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 15);
#endif // DWC_IME_NUM_REGIONS > 15

#if NUM_DCH > 1
#if DWC_IME_NUM_REGIONS > 0
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 0);
#endif // DWC_IME_NUM_REGIONS > 0
#if DWC_IME_NUM_REGIONS > 1
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 1);
#endif // DWC_IME_NUM_REGIONS > 1
#if DWC_IME_NUM_REGIONS > 2
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 2);
#endif // DWC_IME_NUM_REGIONS > 2
#if DWC_IME_NUM_REGIONS > 3
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 3);
#endif // DWC_IME_NUM_REGIONS > 3
#if DWC_IME_NUM_REGIONS > 4
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 4);
#endif // DWC_IME_NUM_REGIONS > 4
#if DWC_IME_NUM_REGIONS > 5
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 5);
#endif // DWC_IME_NUM_REGIONS > 5
#if DWC_IME_NUM_REGIONS > 6
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 6);
#endif // DWC_IME_NUM_REGIONS > 6
#if DWC_IME_NUM_REGIONS > 7
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 7);
#endif // DWC_IME_NUM_REGIONS > 7
#if DWC_IME_NUM_REGIONS > 8
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 8);
#endif // DWC_IME_NUM_REGIONS > 8
#if DWC_IME_NUM_REGIONS > 9
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 9);
#endif // DWC_IME_NUM_REGIONS > 9
#if DWC_IME_NUM_REGIONS > 10
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 10);
#endif // DWC_IME_NUM_REGIONS > 10
#if DWC_IME_NUM_REGIONS > 11
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 11);
#endif // DWC_IME_NUM_REGIONS > 11
#if DWC_IME_NUM_REGIONS > 12
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 12);
#endif // DWC_IME_NUM_REGIONS > 12
#if DWC_IME_NUM_REGIONS > 13
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 13);
#endif // DWC_IME_NUM_REGIONS > 13
#if DWC_IME_NUM_REGIONS > 14
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 14);
#endif // DWC_IME_NUM_REGIONS > 14
#if DWC_IME_NUM_REGIONS > 15
    IME_REGION_CONFIG(cinit_cfg->ime_cfg[0], 0, 15);
#endif // DWC_IME_NUM_REGIONS > 15
#endif // NUM_DCH > 1
#endif // DWC_IME_REGION_ADDR_EN == 1

#endif // DDRCTL_SECURE
}
