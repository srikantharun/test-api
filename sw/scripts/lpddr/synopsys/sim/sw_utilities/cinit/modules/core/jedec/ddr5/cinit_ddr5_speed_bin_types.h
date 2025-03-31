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


#ifndef __CORE_JEDEC_DDR5_CINIT_DDR5_SPEED_BIN_TYPES_H__
#define __CORE_JEDEC_DDR5_CINIT_DDR5_SPEED_BIN_TYPES_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_types.h"

/**
 * @brief Structure used to describe a possible ddr5's cl configuration
 * when operating under a limited clock frequency range.
 */
typedef struct ddr5_speed_bin_tck_cas_s {
    dwc_ddr5_speed_bin_t    speed_bin;
    uint16_t                min_tck_ps;
    uint16_t                max_tck_ps;
    uint16_t                taa_min_ps;
    uint16_t                trcd_trp_min_ps;
    uint8_t                 cl;
} ddr5_speed_bin_tck_cas_t;


/**
 * @brief Type definition of a structure used to describe DDR5's specific speed bin timing parameters.
 *      The structure's parameters and their values (for each speed bin) can be found in the DDR5's JEDEC spec speedbin tables.
 */
typedef struct ddr5_speed_bin_timings_s {
    dwc_ddr5_speed_bin_t        speed_bin;
    uint8_t                     spec_bitmap;
    uint16_t                    min_tck_ps;
    uint16_t                    taa_min_ps;
    uint16_t                    trcd_ps;
    uint16_t                    trp_ps;
    uint16_t                    tras_min_ps;
    uint16_t                    trc_ps;
    const dwc_ddr5_speed_bin_t* down_bins;
    uint8_t                     num_down_bins;
} ddr5_speed_bin_timings_t;


#endif /* __CORE_JEDEC_DDR5_CINIT_DDR5_SPEED_BIN_TYPES_H__ */
