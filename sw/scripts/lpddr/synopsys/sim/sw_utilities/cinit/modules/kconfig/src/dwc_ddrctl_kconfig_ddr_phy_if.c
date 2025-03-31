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


#include "dwc_ddrctl_kconfig_ddr_phy_if.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_cinit_defines.h"
#include ".autoconf.h"

/**
 * @brief Function to set the mode registers
 */
void ddrctl_kconfig_ddr_phy_if(SubsysHdlr_t *cinit_cfg)
{
    uint8_t pstate;

#if NUM_PSTATES > 0
    cinit_cfg->spdData_m.frequency_ratio[0] = DDRCTL_PSTATE0_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 0
#if NUM_PSTATES > 1
    cinit_cfg->spdData_m.frequency_ratio[1] = DDRCTL_PSTATE1_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 1
#if NUM_PSTATES > 2
    cinit_cfg->spdData_m.frequency_ratio[2] = DDRCTL_PSTATE2_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 2
#if NUM_PSTATES > 3
    cinit_cfg->spdData_m.frequency_ratio[3] = DDRCTL_PSTATE3_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 3
#if NUM_PSTATES > 4
    cinit_cfg->spdData_m.frequency_ratio[4] = DDRCTL_PSTATE4_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 4
#if NUM_PSTATES > 5
    cinit_cfg->spdData_m.frequency_ratio[5] = DDRCTL_PSTATE5_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 5
#if NUM_PSTATES > 6
    cinit_cfg->spdData_m.frequency_ratio[6] = DDRCTL_PSTATE6_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 6
#if NUM_PSTATES > 7
    cinit_cfg->spdData_m.frequency_ratio[7] = DDRCTL_PSTATE7_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 7
#if NUM_PSTATES > 8
    cinit_cfg->spdData_m.frequency_ratio[8] = DDRCTL_PSTATE8_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 8
#if NUM_PSTATES > 9
    cinit_cfg->spdData_m.frequency_ratio[9] = DDRCTL_PSTATE9_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 9
#if NUM_PSTATES > 10
    cinit_cfg->spdData_m.frequency_ratio[10] = DDRCTL_PSTATE10_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 10
#if NUM_PSTATES > 11
    cinit_cfg->spdData_m.frequency_ratio[11] = DDRCTL_PSTATE11_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 11
#if NUM_PSTATES > 12
    cinit_cfg->spdData_m.frequency_ratio[12] = DDRCTL_PSTATE12_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 12
#if NUM_PSTATES > 13
    cinit_cfg->spdData_m.frequency_ratio[13] = DDRCTL_PSTATE13_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 13
#if NUM_PSTATES > 14
    cinit_cfg->spdData_m.frequency_ratio[14] = DDRCTL_PSTATE14_FREQUENCY_RATIO;
#endif // NUM_PSTATES > 14

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        SNPS_LOG("[pState %d] Frequency ratio = %s", pstate,
                 ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(cinit_cfg, pstate)));
    }
}
