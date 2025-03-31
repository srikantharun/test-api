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


#ifndef __CORE_CTRL_WORDS_DDR5_CTRL_WORDS_H__
#define __CORE_CTRL_WORDS_DDR5_CTRL_WORDS_H__

#include "dwc_ddrctl_cinit.h"
#include "jedec/ddr5/cinit_ddr5_types.h"
#include "jedec/ddr5/cinit_ddr5_timing_utils.h"

// Convert Period to Frequency - ps to double MHz
#define SNPS_TCK_PS_TO_DDR_MHZ(_tck_ps_) ((2*1000000)/(uint32_t)_tck_ps_)
#define SNPS_DDR_MHZ_TO_TCK_PS(_freq_) SNPS_TCK_PS_TO_DDR_MHZ(_freq_)

uint8_t ddrctl_sw_get_ddr5_ctrl_word(SubsysHdlr_t *cfg, uint32_t pstate, uint8_t mw_num);

ddrctl_error_t cinit_ddr5_get_rw05_speed_grade_id(dwc_ddr5_speed_grade_t speed_grade, uint8_t *sg_id);
ddrctl_error_t cinit_ddr5_get_rw85_fine_grain_speed_grade_id(uint32_t tck_ps, uint8_t *fg_sg_id);

#endif /* __CORE_CTRL_WORDS_DDR5_CTRL_WORDS_H__ */
