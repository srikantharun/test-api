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


#ifndef __CORE_JEDEC_DDR4_CINIT_DDR4_SPEEDBIN_TYPES_H__
#define __CORE_JEDEC_DDR4_CINIT_DDR4_SPEEDBIN_TYPES_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_types.h"

//if DLL_OFF_MODE is set, CL value should be always equal to CL_DLL_OFF_MODE
#define CL_DLL_OFF_MODE 10
#define CL_RDBI_DLL_OFF_MODE 10

/**
 * @brief Structure used to describe a possible ddr4's (non-3ds) cl-rdbi configuration
 * when operating under a limited clock frequency range.
 */
typedef struct ddr4_cas_cfg_s {
    uint16_t max_tck_ps;
    uint16_t min_tck_ps;
    uint8_t cl;
    uint8_t rdbi;
} ddr4_cas_cfg_t;

/**
 * @brief Structure used to describe a ddr4's (3ds) cl possible value
 * when operating under a limited clock frequency range.
 */
typedef struct ddr4_3ds_cas_cfg_s {
    uint16_t max_tck_ps;
    uint16_t min_tck_ps;
    uint8_t cl;
} ddr4_3ds_cas_cfg_t;

/**
 * @brief Structure used to describe ddr4 non3ds specific speed bin parameters
 */
typedef struct ddr4_spbin_non3ds_specific_s {
    uint8_t     taa_dbi;
    const ddr4_cas_cfg_t* cas_cfgs;
} spbin_non3ds_specific_t;

/**
 * @brief Structure used to describe ddr4 3ds specific speed bin parameters
 */
typedef struct ddr4_spbin_3ds_specific_s {
    uint8_t     min_nrcd_nck;
    uint8_t     min_nrp_nck;
    const ddr4_3ds_cas_cfg_t* cas_cfgs;
} spbin_3ds_specific_t;

/**
 * @brief Type definition of a structure used to describe DDR4's specific speed grade timing parameters.
 *      The structure's parameters and their values (for each speed grade) can be found in the DDR4's JEDEC spec speedbin tables.
 */
typedef struct ddr4_speedbin_s {
    dwc_ddr4_speed_grade_e sg_e;
    uint16_t    taa_min_ps;
    uint16_t    taa_max_ps;
    uint16_t    trcd_ps;
    uint16_t    trp_ps;
    uint16_t    tras_min_ps;
    uint16_t    trc_ps;
    union {
        spbin_non3ds_specific_t spec_non_3ds;
        spbin_3ds_specific_t spec_3ds;
    } ddr4_type_specific;
    uint8_t n_cas_cfgs;
} ddr4_speedbin_t;


#endif /* __CORE_JEDEC_DDR4_CINIT_DDR4_SPEEDBIN_TYPES_H__ */
