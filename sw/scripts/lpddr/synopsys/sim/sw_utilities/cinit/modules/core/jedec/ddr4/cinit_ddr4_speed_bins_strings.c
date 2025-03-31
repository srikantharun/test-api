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

#include "cinit_ddr4_speed_bins_strings.h"
#include "dwc_cinit_macros.h"

typedef struct ddr4_speed_bin_str_s {
    dwc_ddr4_speed_grade_e speed_bin;
    char*                  name;
} ddr4_speed_bin_str_t;


static const ddr4_speed_bin_str_t ddr4_speed_bin_str_table[] = {
    {DWC_DDR4_1600J,         "1600J" },
    {DWC_DDR4_1600K,         "1600K" },
    {DWC_DDR4_1600L,         "1600L" },
    {DWC_DDR4_1866L,         "1866L" },
    {DWC_DDR4_1866M,         "1866M" },
    {DWC_DDR4_1866N,         "1866N" },
    {DWC_DDR4_2133N,         "2133N" },
    {DWC_DDR4_2133P,         "2133P" },
    {DWC_DDR4_2133R,         "2133R" },
    {DWC_DDR4_2400P,         "2400P" },
    {DWC_DDR4_2400R,         "2400R" },
    {DWC_DDR4_2400T,         "2400T" },
    {DWC_DDR4_2400U,         "2400U" },
    {DWC_DDR4_2666T,         "2666T" },
    {DWC_DDR4_2666U,         "2666U" },
    {DWC_DDR4_2666V,         "2666V" },
    {DWC_DDR4_2666W,         "2666W" },
    {DWC_DDR4_2933V,         "2933V" },
    {DWC_DDR4_2933W,         "2933W" },
    {DWC_DDR4_2933Y,         "2933Y" },
    {DWC_DDR4_2933AA,        "2933AA"},
    {DWC_DDR4_3200W,         "3200W" },
    {DWC_DDR4_3200AA,        "3200AA"},
    {DWC_DDR4_3200AC,        "3200AC"},
           /* 3DS configurations */
    {DWC_DDR4_1600J_3DS2B,   "1600J_3DS2B"  },
    {DWC_DDR4_1600K_3DS2B,   "1600K_3DS2B"  },
    {DWC_DDR4_1600L_3DS2B,   "1600L_3DS2B"  },
    {DWC_DDR4_1866L_3DS2B,   "1866L_3DS2B"  },
    {DWC_DDR4_1866M_3DS2B,   "1866M_3DS2B"  },
    {DWC_DDR4_1866N_3DS2B,   "1866N_3DS2B"  },
    {DWC_DDR4_2133P_3DS2A,   "2133P_3DS2A"  },
    {DWC_DDR4_2133P_3DS3A,   "2133P_3DS3A"  },
    {DWC_DDR4_2133R_3DS4A,   "2133R_3DS4A"  },
    {DWC_DDR4_2400P_3DS3B,   "2400P_3DS3B"  },
    {DWC_DDR4_2400T_3DS2A,   "2400T_3DS2A"  },
    {DWC_DDR4_2400U_3DS2A,   "2400U_3DS2A"  },
    {DWC_DDR4_2400U_3DS4A,   "2400U_3DS4A"  },
    {DWC_DDR4_2666T_3DS3A,   "2666T_3DS3A"  },
    {DWC_DDR4_2666V_3DS3A,   "2666V_3DS3A"  },
    {DWC_DDR4_2666W_3DS4A,   "2666W_3DS4A"  },
    {DWC_DDR4_2933W_3DS3A,   "2933W_3DS3A"  },
    {DWC_DDR4_2933Y_3DS3A,   "2933Y_3DS3A"  },
    {DWC_DDR4_2933AA_3DS43A, "2933AA_3DS43A"},
    {DWC_DDR4_3200W_3DS4A,   "3200W_3DS4A"  },
    {DWC_DDR4_3200AA_3DS4A,  "3200AA_3DS4A" },
    {DWC_DDR4_3200AC_3DS4A,  "3200AC_3DS4A" }
};

const char* ddrctl_sw_get_ddr4_speed_bin_str(const dwc_ddr4_speed_grade_e speed_bin)
{
    uint8_t index;

    for(index = 0; index < GET_ARR_NELEMS(ddr4_speed_bin_str_table); index++) {
        if(ddr4_speed_bin_str_table[index].speed_bin == speed_bin) {
            return ddr4_speed_bin_str_table[index].name;
        }
    }

    return NULL;
}

