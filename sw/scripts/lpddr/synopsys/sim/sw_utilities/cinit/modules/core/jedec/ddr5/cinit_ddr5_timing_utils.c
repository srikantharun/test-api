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


#include "jedec/ddr5/cinit_ddr5_timing_utils.h"


/**
 * @brief DDR5 convertion of picoseconds to number of clocks rounding down
 *     based on DDR5 spec: 13.2.1 Example
 *
 * @param value_ps  timing in picoseconds
 * @param tck_ps    tCK(AVG) in picoseconds
 *
 * @return uint32_t number of clocks
 */
uint32_t cinit_round_down_only_int_ddr5(uint32_t value_ps, uint32_t tck_ps)
{
    uint32_t round_down;
    if (0 == tck_ps) {
        return 0;
    }

    round_down = value_ps * 997;
    round_down = (round_down / tck_ps) + 1000;
    round_down = round_down / 1000;
    return round_down;
}


#define JEDEC_1980MT_S                         1011
#define JEDEC_2100MT_S                          952
#define JEDEC_2933MT_S                          682

/**
 * @brief Returns the speed grade based on the application average clock
 *  This implementation is aligned with Jedec Specs JESD79-5 and JESD79-5A
 *
 * @param tck_avg_min_ps
 * @return dwc_ddr5_speed_grade_t
 */
dwc_ddr5_speed_grade_t cinit_ddr5_get_speedgrade_from_tck_avg_min(uint32_t tck_avg_min_ps)
{
    // From spec: DDR5-3200 AC timing apply if DRAM operates at lower than 3200 MT/s data rate
    //  ]0 to 3200] MHz
    if ((tck_avg_min_ps >= JEDEC_2100MT_S) && (tck_avg_min_ps <= JEDEC_1980MT_S)) {
        return DWC_DDR5_SG_2100;
    }

    // tCK is not supported on te range ] 682 (JEDEC_2933MT_S), 952 (JEDEC_2100MT_S)[
    if (tck_avg_min_ps > JEDEC_2933MT_S) {
        return DWC_DDR5_SG_INVALID;
    }

    if (tck_avg_min_ps >= 625) {
        return DWC_DDR5_SG_3200;
    }

    //  ]3200 to 3600] MHz
    if (tck_avg_min_ps >= 555) {
        return DWC_DDR5_SG_3600;
    }

    //  ]3600 to 4000] MHz
    if (tck_avg_min_ps >= 500) {
        return DWC_DDR5_SG_4000;
    }

    //  ]4000 to 4400] MHz
    if (tck_avg_min_ps >= 454) {
        return DWC_DDR5_SG_4400;
    }

    //  ]4400 to 4800] MHz
    if (tck_avg_min_ps >= 416) {
        return DWC_DDR5_SG_4800;
    }

    //  ]4800 to 5200] MHz
    if (tck_avg_min_ps >= 384) {
        return DWC_DDR5_SG_5200;
    }

    //  ]5200 to 5600] MHz
    if (tck_avg_min_ps >= 357) {
        return DWC_DDR5_SG_5600;
    }

    //  ]5600 to 6000] MHz
    if (tck_avg_min_ps >= 333) {
        return DWC_DDR5_SG_6000;
    }
    //  ]6000 to 6400] MHz
    if (tck_avg_min_ps >= 312) {
        return DWC_DDR5_SG_6400;
    }
    //  ]6400 to 6800] MHz
    if (tck_avg_min_ps >= 294) {
        return DWC_DDR5_SG_6800;
    }
    //  ]6800 to 7200] MHz
    if (tck_avg_min_ps >= 277) {
        return DWC_DDR5_SG_7200;
    }
    //  ]7200 to 7600] MHz
    if (tck_avg_min_ps >= 263) {
        return DWC_DDR5_SG_7600;
    }
    //  ]7600 to 8000] MHz
    if (tck_avg_min_ps >= 250) {
        return DWC_DDR5_SG_8000;
    }
    //  ]8000 to 8400] MHz
    if (tck_avg_min_ps >= 238) {
        return DWC_DDR5_SG_8400;
    }
    //  ]8400 to 8800] MHz
    if (tck_avg_min_ps >= 227) {
        return DWC_DDR5_SG_8800;
    }

    return DWC_DDR5_SG_INVALID;
}

/**
 * @brief Returns the base frequency of each speed grade
 *
 * @param speed_grade
 * @return uint8_t
 */
uint32_t cinit_ddr5_get_speedgrade_base_frequency(dwc_ddr5_speed_grade_t speed_grade)
{
    switch(speed_grade) {
        case DWC_DDR5_SG_2100:
            return 2100;
        case DWC_DDR5_SG_3200:
            return 3200;
        case DWC_DDR5_SG_3600:
            return 3600;
        case DWC_DDR5_SG_4000:
            return 4000;
        case DWC_DDR5_SG_4400:
            return 4400;
        case DWC_DDR5_SG_4800:
            return 4800;
        case DWC_DDR5_SG_5200:
            return 5200;
        case DWC_DDR5_SG_5600:
            return 5600;
        case DWC_DDR5_SG_6000:
            return 6000;
        case DWC_DDR5_SG_6400:
            return 6400;
        case DWC_DDR5_SG_6800:
            return 6800;
        case DWC_DDR5_SG_7200:
            return 7200;
        case DWC_DDR5_SG_7600:
            return 7600;
        case DWC_DDR5_SG_8000:
            return 8000;
        case DWC_DDR5_SG_8400:
            return 8400;
        case DWC_DDR5_SG_8800:
            return 8800;
        default:
            return DWC_DDR5_SG_INVALID;
    }
}
