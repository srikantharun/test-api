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


#ifndef __KCONFIG_INCLUDE_SINIT_KCONFIG_TYPES_H__
#define __KCONFIG_INCLUDE_SINIT_KCONFIG_TYPES_H__

#include "dwc_cinit_io.h"
#include "dwc_cinit_log.h"
#include "dwc_cinit_bsp.h"

/**
 * @brief Enumerated type listing possible SDRAM types supported
 */
typedef enum sdram_protocol_e {
    DDRCTL_KCONFIG_DDR4    = 1,                             //!<DDR4 SDRAM
    DDRCTL_KCONFIG_DDR5    = 2,                             //!<DDR5 SDRAM
    DDRCTL_KCONFIG_LPDDR4  = 3,                             //!<LPDDR4 SDRAM
    DDRCTL_KCONFIG_LPDDR4X = 4,                             //!<LPDDR4X SDRAM
    DDRCTL_KCONFIG_LPDDR5  = 5,                             //!<LPDDR5 SDRAM
    DDRCTL_KCONFIG_LPDDR5X = 6                              //!<LPDDR5X SDRAM
} sdram_protocol_t;

#endif /* __KCONFIG_INCLUDE_SINIT_KCONFIG_TYPES_H__ */
