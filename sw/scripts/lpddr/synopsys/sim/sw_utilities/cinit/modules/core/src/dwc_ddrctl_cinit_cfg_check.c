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


#include "dwc_ddrctl_cinit_cfg_check.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_defines.h"


/** 
 * @brief method to validate the cinit configuration
 **/
ddrctl_error_t ddrctl_cinit_cfg_check(SubsysHdlr_t *cinit_cfg)
{
    uint8_t pstate;

    for (pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
        if (CINIT_IS_DDR5(cinit_cfg) == DDRCTL_TRUE) {
            if (MEMC_FREQ_RATIO != ddrctl_sw_get_ratio_factor(cinit_cfg, pstate)) {
                SNPS_ERROR("[pState %d] Ratio configuration (%s) not supported",
                           pstate, ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(cinit_cfg, pstate)));
                SNPS_ERROR("[pState %d] Ratio configuration (%d) not supported",
                           pstate, cinit_cfg->memCtrlr_m.qdyn_cfg.frequency_ratio[pstate]);
                return DDRCTL_PARAM_ERROR;
            }
        }

        if (CINIT_IS_DDR4(cinit_cfg) == DDRCTL_TRUE) {
            if (DWC_RATIO_1_2 != ddrctl_sw_get_ratio(cinit_cfg, pstate)) {
                SNPS_ERROR("[pState %d] Ratio configuration (%s) not supported",
                           pstate, ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(cinit_cfg, pstate)));
                return DDRCTL_PARAM_ERROR;
            }
        }
    }


    //TODO: Implement if IME enable -> Quarter Bus Width mode is not supported.
    //       MSTR0.data_bus_width field can be set to either 0 or 1

    //TODO: Implement if IME enable and CHI configuration. DBICTL.dm_en=0 is required


    return DDRCTL_SUCCESS;
}




