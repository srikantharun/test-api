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


#ifndef __DWC_DDRCTL_CINIT_DDR54_DFI_TIMINGS_H__
#define __DWC_DDRCTL_CINIT_DDR54_DFI_TIMINGS_H__

#include "dwc_ddrctl_cinit.h"

void cinit_cal_ddr54_dfi_timings(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n);
#ifdef DDRCTL_DDR
void dwc_ddrctl_cinit_ddr54_prgm_REGB_FREQ_DFITMG7(uint32_t freq, uint32_t ch);
#endif /* DDRCTL_DDR */

void dwc_ddrctl_cinit_ddr54_dfi_control_timing(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch);
void cinit_cal_ddr54_pre_cfg_timing_1st_set(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);


#endif /* __DWC_DDRCTL_CINIT_DDR54_DFI_TIMINGS_H__ */
