
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


#ifndef __SEQUENCES_INCLUDE_SINIT_TYPES_H__
#define __SEQUENCES_INCLUDE_SINIT_TYPES_H__

#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_util.h"

/**
 * @brief Function return type
 */
typedef enum sinit_error_e {
    SINIT_SUCCESS                        = 0,  /**< Success */
    SINIT_ERROR                          = 1,  /**< Error */
    SINIT_MEMORY_ERROR                   = 2,  /**< Memory error */
    SINIT_TIMEOUT                        = 3,  /**< Timeout */
    SINIT_NOT_SUPPORTED                  = 4,  /**< Not supported */
} sinit_error_t;

#endif /* __SEQUENCES_INCLUDE_SINIT_TYPES_H__ */
