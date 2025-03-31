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


#ifndef __DWC_DDRCTL_CINIT_COMMON_DFI_TIMINGS_H__
#define __DWC_DDRCTL_CINIT_COMMON_DFI_TIMINGS_H__

#include "dwc_cinit_bsp.h"
#include "dwc_ddrctl_cinit.h"

void dwc_ddrctl_cinit_common_prgm_REGB_FREQ_DFITMG0(uint32_t freq, uint32_t ch);
void dwc_ddrctl_cinit_common_prgm_REGB_FREQ_DFITMG1(uint32_t freq, uint32_t ch);

#ifdef DDRCTL_CAPAR_RETRY
void dwc_ddrctl_cinit_common_prgm_REGB_FREQ_RETRYTMG1(uint32_t freq, uint32_t ch);
#endif /* DDRCTL_CAPAR_RETRY */

#endif /* __DWC_DDRCTL_CINIT_COMMON_DFI_TIMINGS_H__ */
