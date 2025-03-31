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


#ifndef __DWC_DDRCTL_PHY_TRAINING_H__
#define __DWC_DDRCTL_PHY_TRAINING_H__

#include "dwc_ddrphy_VDEFINES.h"
#include "dwc_cinit_bsp.h"

#define DDR4_TRAIN_DATA_SIZE 29
#define DDR5_TRAIN_DATA_SIZE 28

bool dwc_ddrctl_apply_training_ddr4(void);

bool dwc_ddrctl_apply_training_ddr5(void);


#endif /* __DWC_DDRCTL_PHY_TRAINING_H__ */
