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


#ifndef CINIT_MODULES_VERIFICATION_INCLUDE_DWC_CINIT_UTIL_WRAPER_H_
#define CINIT_MODULES_VERIFICATION_INCLUDE_DWC_CINIT_UTIL_WRAPER_H_


int unsigned dwc_cinit_verf_get_cas_latency(dwc_ddr5_speed_bin_t speed_bin,
                                            int unsigned tck_avg_ps);

#endif /* CINIT_MODULES_VERIFICATION_INCLUDE_DWC_CINIT_UTIL_WRAPER_H_ */
