
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


#ifndef __SEQUENCES_INCLUDE_PHY_SINIT_PHY_TYPES_H__
#define __SEQUENCES_INCLUDE_PHY_SINIT_PHY_TYPES_H__

#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_util.h"
#include "sinit_types.h"

/* Mailbox Interface types */

typedef enum phy_mailbox_mode_e {
    PHY_MAILBOX_MODE_16 = 0,
    PHY_MAILBOX_MODE_32 = 1,
} phy_mailbox_mode_t;

#define PHY_MAILBOX_MSG_AVAILABLE   0
#define PHY_MAILBOX_MSG_EMPTY       1


#define PHY_MSG_PARAMS_MASK                0x0000FFFF
#define PHY_MSG_PARAMS_BIT_OFFSET                   0
#define PHY_MSG_INDEX_MASK                 0xFFFF0000
#define PHY_MSG_INDEX_BIT_OFFSET                   16

#define PHY_SMBUS_MSG_MASK                 0x0000FFFF
#define PHY_SMBUS_MSG_BIT_OFFSET                    0
#define PHY_SMBUS_INFO_MASK                0xFFFF0000
#define PHY_SMBUS_INFO_BIT_OFFSET                  16

#endif /* __SEQUENCES_INCLUDE_PHY_SINIT_PHY_TYPES_H__ */
