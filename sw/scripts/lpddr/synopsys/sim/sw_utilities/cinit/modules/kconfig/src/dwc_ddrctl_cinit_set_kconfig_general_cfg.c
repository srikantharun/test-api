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


#include "dwc_ddrctl_cinit_kconfig_headers.h"
#include "dwc_ddrctl_cinit_types_str.h"

/**
 * @brief Function to set static, quasi-dynamic and dynamic configuration values from Kconfig.
 */

void ddrctl_kconfig_general_cfg(SubsysHdlr_t *cinit_cfg)
{
    cinit_cfg->ddrctl_base_addr[0] = MEM_CTL_BASE_ADDRESS_CH0;
#ifdef DDRCTL_SINGLE_INST_DUALCH
    cinit_cfg->ddrctl_base_addr[1] = MEM_CTL_BASE_ADDRESS_CH1;
#endif
    cinit_cfg->num_pstates = NUM_PSTATES;
    cinit_cfg->num_amap = NUM_AMAP;
    cinit_cfg->num_dch = NUM_DCH;
    cinit_cfg->spdData_m.num_dimm = DWC_DDRCTL_CINIT_NUM_DIMM;
    cinit_cfg->ddrPhyType_m = (ddrPhyType_e) DWC_DDRCTL_CINIT_DDRPHYTYPE_M;
    cinit_cfg->phy_training = SCONFIG_PHY_TRAINING;
}

