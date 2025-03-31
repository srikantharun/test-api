
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


#ifndef __SEQUENCES_INCLUDE_SINIT_UTILS_H__
#define __SEQUENCES_INCLUDE_SINIT_UTILS_H__

#include "dwc_ddrctl_cinit.h"
#include "sinit_types.h"


sinit_error_t sinit_phy_get_maillbox_msg(uint32_t timeout, pub_msg_id_t *pub_msg_id);

sinit_error_t sinit_phy_print_streaming_msg(uint32_t timeout);

sinit_error_t sinit_phy_get_smbus_request( uint32_t timeout, uint16_t *smbus_msg, uint16_t *smbus_info);

#endif /* __SEQUENCES_INCLUDE_SINIT_UTILS_H__ */
