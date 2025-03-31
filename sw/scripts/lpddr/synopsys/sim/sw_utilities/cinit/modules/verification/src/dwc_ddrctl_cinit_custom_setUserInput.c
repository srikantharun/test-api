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


#include "dwc_cinit_io.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_cinit_REGB.h"
#include "ddrctl_regmap.h"

/**
 * @brief Writes the field value
 *
 * @deprecated Will be removed as soon all call from testbench are removed
 *
 * @param field     field full name
 * @param value     value to write
 */
void dwc_ddrctl_cinit_custom_setUserInput(const char *field, uint32_t value)
{
    ddrctl_error_t   rslt;

    SNPS_INFO("Set UserInput value for %s = %d", field, value);
    rslt = ddrctl_regmap_write_field_by_fullname(field, value);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_WARN("Invalid field name: %s, error %d", field, rslt);
    }
}


/**
 * @brief Writes the field value
 *
 * @param block_name    Block name
 * @param register_name Register name
 * @param field_name    Field name
 * @param value         value to write
 */
void ddrctl_sw_set_field(const char *block_name, const char *register_name,
                         const char *field_name, uint32_t value)
{
    ddrctl_error_t   rslt;

    rslt = ddrctl_regmap_write_field(block_name, register_name, field_name, value);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_WARN("Invalid field name: %s, error %d", field_name, rslt);
    }
}
