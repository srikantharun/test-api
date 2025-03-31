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


#include "dwc_cinit_bsp.h"
#include "dwc_cinit_log.h"

void dwc_ddrctl_cinit_exit(uint32_t error_code)
{
    exit(error_code);
}


void dwc_ddrctl_cinit_assert_exit(const char *assertion, char *file, const char *func, int line)
{
    ddr_bsp_log_entry(SNPS_MAIN_LOG, DWC_LOG_ASSERT, file, func, line, "Assert: %s", assertion);
    dwc_ddrctl_cinit_exit(DDRCTL_ASSERT);
}
