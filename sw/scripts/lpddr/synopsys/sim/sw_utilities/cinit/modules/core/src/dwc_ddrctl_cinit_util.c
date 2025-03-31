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


#include "dwc_ddrctl_cinit_util.h"

/** @brief method to initialize array of integers.
 */
void dwc_cinit_memset32(void *dest, uint32_t value, size_t size)
{
    uint32_t    i;
    uint32_t    n_words;
    uint32_t    *prt_data;

    n_words = size / sizeof(uint32_t);
    prt_data = (uint32_t *) dest;

    for (i = 0; i < n_words; i++) {
            prt_data[i] = value;
    }
}
