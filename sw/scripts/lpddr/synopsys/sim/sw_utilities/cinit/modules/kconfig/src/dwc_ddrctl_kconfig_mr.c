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
#include "dwc_ddrctl_kconfig_mr.h"
#include "dwc_ddrctl_kconfig_mr_ddr4.h"
#include "dwc_ddrctl_kconfig_mr_ddr5.h"
#include "dwc_ddrctl_kconfig_mr_lpddr4.h"
#include "dwc_ddrctl_kconfig_mr_lpddr5.h"

/**
 * @brief Function to set the mode registers
 */
void ddrctl_kconfig_mode_registers(SubsysHdlr_t *cfg)
{
    switch (cfg->spdData_m.sdram_protocol) {
        case DWC_DDR4:
            ddrctl_kconfig_mode_registers_ddr4(cfg);
            break;
        case DWC_DDR5:
            ddrctl_kconfig_mode_registers_ddr5(cfg);
            break;
        case DWC_LPDDR4:
            ddrctl_kconfig_mode_registers_lpddr4(cfg);
            break;
        case DWC_LPDDR5:
            ddrctl_kconfig_mode_registers_lpddr5(cfg);
            break;
    }
}
