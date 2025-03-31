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

#include "cinit_ddr5_speed_bins_strings.h"
#include "dwc_cinit_macros.h"

typedef struct ddr5_speed_bin_str_s {
    dwc_ddr5_speed_bin_t speed_bin;
    char*                name;
} ddr5_speed_bin_str_t;


static const ddr5_speed_bin_str_t ddr5_speed_bin_str_table[] = {
    {DWC_DDR5_2100,       "2100"},
    {DWC_DDR5_3200AN,     "3200AN"},
    {DWC_DDR5_3200B,      "3200B"},
    {DWC_DDR5_3200BN,     "3200BN"},
    {DWC_DDR5_3200C,      "3200C"},
    {DWC_DDR5_3600AN,     "3600AN"},
    {DWC_DDR5_3600B,      "3600B"},
    {DWC_DDR5_3600BN,     "3600BN"},
    {DWC_DDR5_3600C,      "3600C"},
    {DWC_DDR5_4000AN,     "4000AN"},
    {DWC_DDR5_4000B,      "4000B"},
    {DWC_DDR5_4000BN,     "4000BN"},
    {DWC_DDR5_4000C,      "4000C"},
    {DWC_DDR5_4400AN,     "4400AN"},
    {DWC_DDR5_4400B,      "4400B"},
    {DWC_DDR5_4400BN,     "4400BN"},
    {DWC_DDR5_4400C,      "4400C"},
    {DWC_DDR5_4800AN,     "4800AN"},
    {DWC_DDR5_4800B,      "4800B"},
    {DWC_DDR5_4800BN,     "4800BN"},
    {DWC_DDR5_4800C,      "4800C"},
    {DWC_DDR5_5200AN,     "5200AN"},
    {DWC_DDR5_5200B,      "5200B"},
    {DWC_DDR5_5200BN,     "5200BN"},
    {DWC_DDR5_5200C,      "5200C"},
    {DWC_DDR5_5600AN,     "5600AN"},
    {DWC_DDR5_5600B,      "5600B"},
    {DWC_DDR5_5600BN,     "5600BN"},
    {DWC_DDR5_5600C,      "5600C"},
    {DWC_DDR5_6000AN,     "6000AN"},
    {DWC_DDR5_6000B,      "6000B"},
    {DWC_DDR5_6000BN,     "6000BN"},
    {DWC_DDR5_6000C,      "6000C"},
    {DWC_DDR5_6400AN,     "6400AN"},
    {DWC_DDR5_6400B,      "6400B"},
    {DWC_DDR5_6400BN,     "6400BN"},
    {DWC_DDR5_6400C,      "6400C"},
    {DWC_DDR5_6800AN,     "6800AN"},
    {DWC_DDR5_6800B,      "6800B"},
    {DWC_DDR5_6800BN,     "6800BN"},
    {DWC_DDR5_6800C,      "6800C"},
    {DWC_DDR5_7200AN,     "7200AN"},
    {DWC_DDR5_7200B,      "7200B"},
    {DWC_DDR5_7200BN,     "7200BN"},
    {DWC_DDR5_7200C,      "7200C"},
    {DWC_DDR5_7600AN,     "7600AN"},
    {DWC_DDR5_7600B,      "7600B"},
    {DWC_DDR5_7600BN,     "7600BN"},
    {DWC_DDR5_7600C,      "7600C"},
    {DWC_DDR5_8000AN,     "8000AN"},
    {DWC_DDR5_8000B,      "8000B"},
    {DWC_DDR5_8000BN,     "8000BN"},
    {DWC_DDR5_8000C,      "8000C"},
    {DWC_DDR5_8400AN,     "8400AN"},
    {DWC_DDR5_8400B,      "8400B"},
    {DWC_DDR5_8400BN,     "8400BN"},
    {DWC_DDR5_8400C,      "8400C"},
    {DWC_DDR5_8800AN,     "8800AN"},
    {DWC_DDR5_8800B,      "8800B"},
    {DWC_DDR5_8800BN,     "8800BN"},
    {DWC_DDR5_8800C,      "8800C"},
    {DWC_DDR5_3200AN_3DS, "3200AN 3DS"},
    {DWC_DDR5_3200B_3DS,  "3200B 3DS"},
    {DWC_DDR5_3200BN_3DS, "3200BN 3DS"},
    {DWC_DDR5_3200C_3DS,  "3200C 3DS"},
    {DWC_DDR5_3600AN_3DS, "3600AN 3DS"},
    {DWC_DDR5_3600B_3DS,  "3600B 3DS"},
    {DWC_DDR5_3600BN_3DS, "3600BN 3DS"},
    {DWC_DDR5_3600C_3DS,  "3600C 3DS"},
    {DWC_DDR5_4000AN_3DS, "4000AN 3DS"},
    {DWC_DDR5_4000B_3DS,  "4000B 3DS"},
    {DWC_DDR5_4000BN_3DS, "4000BN 3DS"},
    {DWC_DDR5_4000C_3DS,  "4000C 3DS"},
    {DWC_DDR5_4400AN_3DS, "4400AN 3DS"},
    {DWC_DDR5_4400B_3DS,  "4400B 3DS"},
    {DWC_DDR5_4400BN_3DS, "4400BN 3DS"},
    {DWC_DDR5_4400C_3DS,  "4400C 3DS"},
    {DWC_DDR5_4800AN_3DS, "4800AN 3DS"},
    {DWC_DDR5_4800B_3DS,  "4800B 3DS"},
    {DWC_DDR5_4800BN_3DS, "4800BN 3DS"},
    {DWC_DDR5_4800C_3DS,  "4800C 3DS"},
    {DWC_DDR5_5200AN_3DS, "5200AN 3DS"},
    {DWC_DDR5_5200B_3DS,  "5200B 3DS"},
    {DWC_DDR5_5200BN_3DS, "5200BN 3DS"},
    {DWC_DDR5_5200C_3DS,  "5200C 3DS"},
    {DWC_DDR5_5600AN_3DS, "5600AN 3DS"},
    {DWC_DDR5_5600B_3DS,  "5600B 3DS"},
    {DWC_DDR5_5600BN_3DS, "5600BN 3DS"},
    {DWC_DDR5_5600C_3DS,  "5600C 3DS"},
    {DWC_DDR5_6000AN_3DS, "6000AN 3DS"},
    {DWC_DDR5_6000B_3DS,  "6000B 3DS"},
    {DWC_DDR5_6000BN_3DS, "6000BN 3DS"},
    {DWC_DDR5_6000C_3DS,  "6000C 3DS"},
    {DWC_DDR5_6400AN_3DS, "6400AN 3DS"},
    {DWC_DDR5_6400B_3DS,  "6400B 3DS"},
    {DWC_DDR5_6400BN_3DS, "6400BN 3DS"},
    {DWC_DDR5_6400C_3DS,  "6400C 3DS"},
    {DWC_DDR5_6800AN_3DS, "6800AN 3DS"},
    {DWC_DDR5_6800B_3DS,  "6800B 3DS"},
    {DWC_DDR5_6800BN_3DS, "6800BN 3DS"},
    {DWC_DDR5_6800C_3DS,  "6800C 3DS"},
    {DWC_DDR5_7200AN_3DS, "7200AN 3DS"},
    {DWC_DDR5_7200B_3DS,  "7200B 3DS"},
    {DWC_DDR5_7200BN_3DS, "7200BN 3DS"},
    {DWC_DDR5_7200C_3DS,  "7200C 3DS"},
    {DWC_DDR5_7600AN_3DS, "7600AN 3DS"},
    {DWC_DDR5_7600B_3DS,  "7600B 3DS"},
    {DWC_DDR5_7600BN_3DS, "7600BN 3DS"},
    {DWC_DDR5_7600C_3DS,  "7600C 3DS"},
    {DWC_DDR5_8000AN_3DS, "8000AN 3DS"},
    {DWC_DDR5_8000B_3DS,  "8000B 3DS"},
    {DWC_DDR5_8000BN_3DS, "8000BN 3DS"},
    {DWC_DDR5_8000C_3DS,  "8000C 3DS"},
    {DWC_DDR5_8400AN_3DS, "8400AN 3DS"},
    {DWC_DDR5_8400B_3DS,  "8400B 3DS"},
    {DWC_DDR5_8400BN_3DS, "8400BN 3DS"},
    {DWC_DDR5_8400C_3DS,  "8400C 3DS"},
    {DWC_DDR5_8800AN_3DS, "8800AN 3DS"},
    {DWC_DDR5_8800B_3DS,  "8800B 3DS"},
    {DWC_DDR5_8800BN_3DS, "8800BN 3DS"},
    {DWC_DDR5_8800C_3DS,  "8800C 3DS"}
};

const char* ddrctl_cinit_get_ddr5_speed_bin_str(const dwc_ddr5_speed_bin_t speed_bin)
{
    uint8_t i;

    for(i = 0; i < GET_ARR_NELEMS(ddr5_speed_bin_str_table); i++) {
        if(ddr5_speed_bin_str_table[i].speed_bin == speed_bin) {
            return ddr5_speed_bin_str_table[i].name;
        }
    }

    return NULL;
}

const char * ddrctl_cinit_get_ddr5_version_str(ddr5_jedec_spec_t spec_ver)
{
    switch (spec_ver) {
        case JESD79_5:
            return "JESD79 5";
        case JESD79_5A:
            return "JESD79 5A";
        case JESD79_5B:
            return "JESD79 5B";
        default:
            return "Unknown";
    }
}
