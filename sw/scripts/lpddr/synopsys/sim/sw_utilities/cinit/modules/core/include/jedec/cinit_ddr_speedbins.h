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


#ifndef __INCLUDE_JEDEC_CINIT_DDR_SPEEDBINS_H__
#define __INCLUDE_JEDEC_CINIT_DDR_SPEEDBINS_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_types.h"

/**
 * @brief Type returned by all the interfaces of this module
 * If an interface was called and have satisfied its purposed succesfully it should return SPBINS_OK
 * If an incongruence was found when executing from the interface an error enum code is returned
 */

typedef enum ddr_speedbins_ret_e
{
    SPBINS_OK,
    SPBINS_NOT_OK,
    SPBINS_INVALID_NULL_PTR,
    SPBINS_INVALID_SPEED_BIN,
    SPBINS_SG_MIN_TCK_PS_NOT_FOUND,
    SPBINS_TABLE_NULL_PTR,
    SPBINS_SPEED_BIN_ENTRY_NOT_FOUND,
    SPBINS_CAS_CFG_NOT_FOUND,
    SPBINS_LAST_ELEM,
    SPBINS_NOT_SUPPORTED,
} ddr_speedbins_ret_t;

/**
 * @brief Type definition used when choosing a possible cl value.
 * Gives the user the possibility to set the lower or higher cl configuration for a specific speed grade and tck(AVG)
 *
 */
typedef enum ddr_select_cl_alg_e {
    SELECT_LOWER_CL,
    SELECT_HIGHER_CL,
    SELECT_CL_LAST_ELEM
} ddr_select_cl_alg_t;


/**
 * @brief This function should be used in order to set several timings described in jedec' speed bin tables
 *        From a specified jedec ddr4 revision and a specified speed grade, it will write into *timings the following parameters:
 *              sg_tck_ps      -> Minimum Speed Grade Clock Cycle time
 *              trcd_ps        -> Active to Read/Write command time
 *              trp_ps         -> Precharge command period
 *              tras_min_ps    -> Minimum Active to Precharge command time
 *              trc_ps         -> Active to Active/Auto Refresh command time
 * @param sg -> ddr4's speed grade
 * @param timings -> pointer to structure where clk timings will be written to
 * @return ddr_speedbins_ret_t -> operation status enum code
 */
ddr_speedbins_ret_t cinit_ddr4_speedbins_set_clk_timings(const dwc_ddr4_speed_grade_e sg, ddrTimingParameters_t* const timings);


/**
 * @brief This function should be used in order to set the DDR4 cas latency values
 *        It will write into *timings the following parameters:
 *        tcl_rdbi_tck -> RDBI (only written if memory is NON-3DS)
 *        tcl_tck      -> CL
 * @param sg -> ddr4's speed grade
 * @param tck_avg_ps -> current clock cycle time
 * @param pick_cl_alg -> algorithm used when choosing the cas latencys to set
 * @param dll_off_mode -> boolean that describes if DLL-off Mode is enabled or not
 * @param gd_mode -> boolean that describes if Geardown Mode is enabled or not
 * @param timings -> pointer to structure where cas latency parameters will be written into
 * @return ddr_speedbins_ret_t
 */
ddr_speedbins_ret_t cinit_ddr4_speedbins_set_cas_latencys(const dwc_ddr4_speed_grade_e sg, const uint16_t tck_avg_ps, const ddr_select_cl_alg_t pick_cl_alg,
                                                           const bool dll_off_mode, const bool gd_mode, ddrTimingParameters_t* const timings);


/**
 * @brief This function should be used in order to set several timings described in jedec' speed bin tables
 *        From a specified jedec ddr5 revision and a specified speed grade, it will write into *timings the following parameters:
 *              sg_tck_ps      -> Minimum Speed Bin Clock Cycle time
 *              trcd_ps        -> Active to Read/Write command time
 *              trp_ps         -> Precharge command period
 *              tras_min_ps    -> Minimum Active to Precharge command time
 *              trc_ps         -> Active to Active/Auto Refresh command time
 *
 * @param cfg           CINIT configuration
 * @param speed_bin    ddr5's speed bin
 * @param timings      pointer to structure where clk timings will be written to
 * @return ddrctl_error_t error code
 */
ddrctl_error_t cinit_ddr5_speed_bin_set_clk_timings(ddr5_jedec_spec_t spec, const dwc_ddr5_speed_bin_t speed_bin,
                                                    ddrTimingParameters_t* timings);

/**
 * @brief This function should be used in order to get the DDR5 CAS latency value
 *
 * @param cfg           CINIT configuration
 * @param speed_bin     ddr5's speed bin
 * @param tck_avg_ps    current clock cycle time
 * @param pick_cl_alg   algorithm used when choosing the cas latencys to set
 * @param timings       pointer to uint8_t where possible cl value will be written into
 * @return ddrctl_error_t error code
 */
ddrctl_error_t ddrctl_cinit_get_ddr5_speed_bin_cas_latency(ddr5_jedec_spec_t spec, const dwc_ddr5_speed_bin_t speed_bin,
                                                    const uint16_t tck_avg_ps, const ddr_select_cl_alg_t select_mode,
                                                    uint8_t* cas_latency);


ddrctl_error_t ddrctl_cinit_get_ddr5_cas_latency(const uint16_t tck_avg_ps, const uint16_t taa_min_ps,
                                                 const uint16_t trcd_ps, const uint16_t trp_ps,
                                                 const ddrctl_bool_t is_3ds, uint8_t *cas_latency);


#endif /* __INCLUDE_JEDEC_CINIT_DDR_SPEEDBINS_H__ */
