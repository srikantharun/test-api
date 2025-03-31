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

#ifndef __DWC_DDRCTL_CINIT_IME_SEQUENCES_H__
#define __DWC_DDRCTL_CINIT_IME_SEQUENCES_H__

#include "dwc_ddrctl_cinit.h"

ddrctl_error_t ddrctl_sinit_ime_config(SubsysHdlr_t *cinit_cfg);

ddrctl_error_t dwc_ddrctl_cinit_ime_chk_self_test_status(uint32_t channel);

ddrctl_error_t dwc_ddrctl_cinit_ime_key_loading(SubsysHdlr_t *cinit_cfg, uint8_t channel,
                                                uint8_t region, uint8_t slot);

#endif /* __DWC_DDRCTL_CINIT_IME_SEQUENCES_H__ */

