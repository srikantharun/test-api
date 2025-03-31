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


#ifndef __CORE_INCLUDE__MODE_REGS_DDR4_DDRCTL_SW_DDR4_MODE_REGS_H__
#define __CORE_INCLUDE__MODE_REGS_DDR4_DDRCTL_SW_DDR4_MODE_REGS_H__

#include "dwc_ddrctl_cinit.h"



typedef enum ddrctl_ddr4_mr_e {
    DDRCTL_DDR4_MR0 = 0x0,
    DDRCTL_DDR4_MR1 = 0x1,
    DDRCTL_DDR4_MR2 = 0x2,
    DDRCTL_DDR4_MR3 = 0x3,
    DDRCTL_DDR4_MR4 = 0x4,
    DDRCTL_DDR4_MR5 = 0x5,
    DDRCTL_DDR4_MR6 = 0x6,
    DDRCTL_DDR4_MR7 = 0x7
} ddrctl_ddr4_mr_t;

uint16_t ddrctl_sw_get_ddr4_mode_reg(ddrctl_ddr4_mr_t mr, uint8_t pstate, uint8_t channel);

uint8_t ddrctl_sw_get_ddr4_mr0_cl_code(uint8_t cas_latency);


#endif  //__CORE_INCLUDE__MODE_REGS_DDR4_DDRCTL_SW_DDR4_MODE_REGS_H__


