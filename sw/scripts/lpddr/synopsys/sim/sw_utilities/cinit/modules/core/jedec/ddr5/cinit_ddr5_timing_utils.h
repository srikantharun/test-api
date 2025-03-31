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


#ifndef __CORE_JEDEC_CINIT_DDR5_TIMING_UTILS_H__
#define __CORE_JEDEC_CINIT_DDR5_TIMING_UTILS_H__

#include "dwc_ddrctl_cinit.h"
#include "jedec/ddr5/cinit_ddr5_types.h"

dwc_ddr5_speed_grade_t cinit_ddr5_get_speedgrade_from_tck_avg_min(uint32_t tck_avg_min);

uint32_t cinit_ddr5_get_speedgrade_base_frequency(dwc_ddr5_speed_grade_t speed_grade);

uint32_t cinit_round_down_only_int_ddr5(uint32_t value_ps, uint32_t tck_ps);

#endif /* __CORE_JEDEC_CINIT_DDR5_TIMING_UTILS_H__ */
