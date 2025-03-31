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


#ifndef __CORE_INCLUDE_CINIT_CTL_STATUS_H__
#define __CORE_INCLUDE_CINIT_CTL_STATUS_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_defines.h"

ddrctl_bool_t cinit_dual_channel_enable();

uint8_t cinit_get_num_channels_enable();

ddrctl_bool_t cinit_is_dual_channel_sync_enable();

uint8_t cinit_get_active_logical_ranks();

uint8_t cinit_get_active_ranks_map();

uint8_t cinit_get_number_ranks();

ddrctl_bool_t cinit_verify_normal_op_mode(ddrctl_channel_t channel_ctrl);

#endif /* __CORE_INCLUDE_CINIT_CTL_STATUS_H__ */
