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


#ifndef __INCLUDE_DWC_DDRCTL_CINIT_DEFINES_H__
#define __INCLUDE_DWC_DDRCTL_CINIT_DEFINES_H__

#include "dwc_ddrctl_cinit.h"


/**
 * @brief Enum type for device capacity
 */
typedef enum ddrctl_mem_capacity_e {
    DDRCTL_256MB =   256,
    DDRCTL_512MB =   512,
    DDRCTL_1GB   =  1024,
    DDRCTL_2GB   =  2048,
    DDRCTL_4GB   =  4096,
    DDRCTL_8GB   =  8192,
    DDRCTL_12GB  = 12288,
    DDRCTL_16GB  = 16384,
    DDRCTL_24GB  = 24576,
    DDRCTL_32GB  = 32768,
    DDRCTL_64GB  = 65536
} ddrctl_mem_capacity_t;


/**
 * @brief Enum type for represent Fine Granularity Refresh
 */
typedef enum ddrctl_fgr_mode_e {
    FGR_MODE_FIXED_1X           = 0,  /**< Fixed 1x (Normal mode)  */
    FGR_MODE_FIXED_2X           = 1,  /**< Fixed 2x  */
    FGR_MODE_FIXED_4X           = 2,  /**< Fixed 4x  (DDR4 only) */
    FGR_MODE_EN_ON_THE_FLY_2X   = 5,  /**< Enable on the fly 2x (not supported)  */
    FGR_MODE_EN_ON_THE_FLY_4X   = 6,  /**< Enable on the fly 4x (not supported)  */
} ddrctl_fgr_mode_t;


/**
 * @brief Enum type for bank number
 */
typedef enum ddrctl_bank_number_e {
    DDRCTL_BANK_NUMBER_2  = 0x1,
    DDRCTL_BANK_NUMBER_4  = 0x2,
    DDRCTL_BANK_NUMBER_8  = 0x3
} ddrctl_bank_number_t;


/**
 * @brief Enum type to define the channel
 */
typedef enum ddrctl_channel_e {
    DDRCTL_CHANNEL_0         = 0x0,
    DDRCTL_CHANNEL_1         = 0x1,
    DDRCTL_CHANNEL_ALL       = 0x8
} ddrctl_channel_t;


static inline const char * ddrctl_sw_channel_str(ddrctl_channel_t channel)
{
    switch (channel) {
        case DDRCTL_CHANNEL_0:
            return "0";
        case DDRCTL_CHANNEL_1:
            return "1";
        case DDRCTL_CHANNEL_ALL:
            return "All";
        default:
            return "Unknown";
    }
}


static inline const char * ddrctl_sw_get_ratio_str(dwc_freq_ratio_t ratio)
{
    switch (ratio) {
        case DWC_RATIO_1_2:
            return "1:2";
        case DWC_RATIO_1_4:
            return "1:4";
        case DWC_RATIO_WCK_CK_2_1:
            return "2:1";
        case DWC_RATIO_WCK_CK_4_1:
            return "4:1";
        default:
            return "Unknown";
    }
}


/**
 * @brief Inline function to get the frequency ratio
 * 
 * @param cinit_cfg         CINIT configuration structure
 * @param pstate            pState number
 * @return dwc_freq_ratio_t   return ratio
 */
static inline dwc_freq_ratio_t ddrctl_sw_get_ratio(SubsysHdlr_t *cinit_cfg, uint8_t pstate)
{
    return (dwc_freq_ratio_t) cinit_cfg->spdData_m.frequency_ratio[pstate];
}


static inline uint8_t ddrctl_sw_get_ratio_factor(SubsysHdlr_t *cinit_cfg, uint8_t pstate)
{
    if ((ddrctl_sw_get_ratio(cinit_cfg, pstate) == DWC_RATIO_1_2) ||
        (ddrctl_sw_get_ratio(cinit_cfg, pstate) == DWC_RATIO_WCK_CK_2_1)) {
        return 2;
    }

    return 4;
}

#endif /* __INCLUDE_DWC_DDRCTL_CINIT_DEFINES_H__ */
