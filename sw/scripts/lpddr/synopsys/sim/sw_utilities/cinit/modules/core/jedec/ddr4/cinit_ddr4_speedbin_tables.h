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


#ifndef __CORE_JEDEC_DDR4_CINIT_DDR4_SPEEDBIN_TABLES_H__
#define __CORE_JEDEC_DDR4_CINIT_DDR4_SPEEDBIN_TABLES_H__

/* Include correct ddr4 jedec speedbin table */
#ifdef JESD79_4C_DDR4_SPEEDBINS
#include "cinit_ddr4_speedbins_c.h"
#else
#error DDR4 JEDEC spec needs to be specified for loading the correct speedbin tables
#endif /* JESD79_4C_DDR4_SPEEDBINS */

/* Include correct ddr4 3DS jedec speedbin table */
#ifdef JESD79_4_1_B_DDR4_3DS_SPEEDBINS
#include "cinit_ddr4_3ds_speedbins_1_b.h"
#else
#error DDR4 3DS JEDEC spec needs to be specified for loading the correct speedbin tables
#endif /* JESD79_4_1_B_DDR4_3DS_SPEEDBINS */


#endif /* __CORE_JEDEC_DDR4_CINIT_DDR4_SPEEDBIN_TABLES_H__ */
