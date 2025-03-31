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


#ifndef __CORE_INCLUDE_DDRCTL_SW_DDR5_MODE_REGS_H__
#define __CORE_INCLUDE_DDRCTL_SW_DDR5_MODE_REGS_H__

#include "dwc_ddrctl_cinit.h"

typedef enum ddrctl_ddr5_2n_mode_e {
    DDR5_MR2_2N_MODE = 0x0,
    DDR5_MR2_1N_MODE = 0x1,
} ddrctl_ddr5_2n_mode_t;


uint8_t ddrctl_sw_get_ddr5_mode_reg(SubsysHdlr_t *cfg, uint8_t pstate, uint8_t mr_num);


#endif  //__CORE_INCLUDE_DDRCTL_SW_DDR5_MODE_REGS_H__


