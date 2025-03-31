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


#ifndef __CORE_JEDEC_DDR5_CINIT_DDR5_SPEED_BINS_3DS_H__
#define __CORE_JEDEC_DDR5_CINIT_DDR5_SPEED_BINS_3DS_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_types.h"

void cinit_ddr5_speed_bin_3ds_get_table(const ddr5_speed_bin_timings_t** table_ptr, uint8_t* n_sgs);

void cinit_ddr5_speed_bin_3ds_get_cas_table(const ddr5_speed_bin_tck_cas_t** table_ptr, uint8_t* n_sgs);

#endif /* __CORE_JEDEC_DDR5_CINIT_DDR5_SPEED_BINS_3DS_H__ */
