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


#include "dwc_ddrctl_cinit_kconfig.h"
#include "dwc_ddrctl_cinit_kconfig_headers.h"
#include "dwc_ddrctl_cinit_set_kconfig_SPD_cfg.h"
#include "dwc_ddrctl_kconfig_mr.h"
#include "dwc_ddrctl_kconfig_ddr_phy_if.h"
#include "dwc_ddrctl_kconfig_ime.h"

extern void dwc_ddrctl_cinit_set_kconfig_sw_cfg(void);
extern void dwc_ddrctl_cinit_set_kconfig_uncategorized_cfg(void);
extern void dwc_ddrctl_cinit_set_kconfig_lut_cfg(void);
extern void ddrctl_kconfig_general_cfg(SubsysHdlr_t *cinit_cfg);

ddrctl_error_t dwc_ddrctl_cinit_kconfig(SubsysHdlr_t *cinit_cfg)
{
    ddrctl_error_t rslt;

    ddrctl_kconfig_general_cfg(cinit_cfg);

    rslt = dwc_ddrctl_cinit_set_kconfig_memory();
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Memory configuration failed %d", rslt);
        return rslt;
    }

    ddrctl_kconfig_ddr_phy_if(cinit_cfg);

    dwc_ddrctl_cinit_set_kconfig_lut_cfg();

    dwc_ddrctl_cinit_set_kconfig_uncategorized_cfg();

    ddrctl_kconfig_mode_registers(cinit_cfg);

    dwc_ddrctl_cinit_set_kconfig_sw_cfg();

    ddrctl_kconfig_ime(cinit_cfg);

    return DDRCTL_SUCCESS;
}
