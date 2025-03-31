
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


#ifndef __CORE_JEDEC_CINIT_DDR5_TYPES_H__
#define __CORE_JEDEC_CINIT_DDR5_TYPES_H__

/*
 * ! \enum dwc_ddr5_speed_grade_e
 * Encoding of DDDR5 speed grades.
 */
typedef enum dwc_ddr5_speed_grade_e{
    DWC_DDR5_SG_INVALID,
    DWC_DDR5_SG_2100,
    DWC_DDR5_SG_3200,
    DWC_DDR5_SG_3600,
    DWC_DDR5_SG_4000,
    DWC_DDR5_SG_4400,
    DWC_DDR5_SG_4800,
    DWC_DDR5_SG_5200,
    DWC_DDR5_SG_5600,
    DWC_DDR5_SG_6000,
    DWC_DDR5_SG_6400,
    DWC_DDR5_SG_6800,
    DWC_DDR5_SG_7200,
    DWC_DDR5_SG_7600,
    DWC_DDR5_SG_8000,
    DWC_DDR5_SG_8400,
    DWC_DDR5_SG_8800
} dwc_ddr5_speed_grade_t;


#endif /* __CORE_JEDEC_CINIT_DDR5_TYPES_H__ */


