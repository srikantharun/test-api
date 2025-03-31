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


#include "jedec/cinit_ddr_speedbins.h"
#include "cinit_ddr5_speed_bin_types.h"
#include "cinit_ddr5_speed_bin.h"
#include "cinit_ddr5_speed_bin_3ds.h"
#include "cinit_ddr5_speed_bins_strings.h"
#include "cinit_ddr5_types.h"
#include "jedec/ddr5/cinit_ddr5_timing_utils.h"
#include "dwc_cinit_macros.h"

#ifdef DDRCTL_DDR

#define IS_SPEED_BIN_3DS(speed_bin) (((speed_bin) < DWC_DDR5_3DS_FIRST_SG) ? DDRCTL_FALSE: DDRCTL_TRUE)


/* Auxiliar static functions that can be used internally by this module's interfaces */
static ddrctl_error_t _get_speed_bin_timings(ddr5_jedec_spec_t spec, const dwc_ddr5_speed_bin_t speed_bin,
                                             const ddr5_speed_bin_timings_t** speed_bin_timings);

static ddrctl_error_t _get_speed_bin_tck_cas(ddr5_jedec_spec_t spec, const dwc_ddr5_speed_bin_t speed_bin,
                                             const uint16_t tck_avg_ps, const ddr_select_cl_alg_t select_mode,
                                             uint8_t* cas_latency);


static inline void _get_speed_bin_table(const ddrctl_bool_t is_3ds, const ddr5_speed_bin_timings_t** table_ptr,
                                        uint8_t* n_sgs);



static inline void _get_cas_table(const ddrctl_bool_t is_3ds, const ddr5_speed_bin_tck_cas_t** table_ptr,
                                  uint8_t* n_sgs);



ddrctl_error_t cinit_ddr5_speed_bin_set_clk_timings(ddr5_jedec_spec_t spec, const dwc_ddr5_speed_bin_t speed_bin,
                                                    ddrTimingParameters_t* timings)
{
    ddrctl_error_t rslt;
    const ddr5_speed_bin_timings_t* sb_timings = NULL;

    if(timings == NULL) {
        SNPS_ERROR("Received NULL pointer for ddrTimingParameters_t* timings!");
        return DDRCTL_INVALID_NULL_PTR;
    }

    rslt = _get_speed_bin_timings(spec, speed_bin, &sb_timings);
    if(rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Timings not found for speed bin:%s (%d) on %s spec",
                    ddrctl_cinit_get_ddr5_speed_bin_str(speed_bin), speed_bin,
                    ddrctl_cinit_get_ddr5_version_str(spec));
        return rslt;
    }

    timings->sg_tck_ps        = sb_timings->min_tck_ps;
    timings->trcd_ps          = sb_timings->trcd_ps;
    timings->trp_ps           = sb_timings->trp_ps;
    timings->ddr5_tras_min_ps = sb_timings->tras_min_ps;
    timings->trc_ps           = sb_timings->trc_ps;

    SNPS_LOG("Timing parameters for %s: tCK(AVG)=%u tRCD=%u tRP=%u tRAS(min)=%u tRC=%u",
             ddrctl_cinit_get_ddr5_speed_bin_str(speed_bin), timings->sg_tck_ps, timings->trcd_ps,
             timings->trp_ps, timings->ddr5_tras_min_ps, timings->trc_ps);

    return DDRCTL_SUCCESS;
}


ddrctl_error_t ddrctl_cinit_get_ddr5_speed_bin_cas_latency(ddr5_jedec_spec_t spec, const dwc_ddr5_speed_bin_t speed_bin,
                                                    const uint16_t tck_avg_ps, const ddr_select_cl_alg_t select_mode,
                                                    uint8_t* cas_latency)
{
    ddrctl_error_t  rslt;
    uint8_t         cl_obtained;

    if(cas_latency == NULL) {
        SNPS_ERROR("Received NULL pointer on cas_latency!");
        return DDRCTL_INVALID_NULL_PTR;
    }

    rslt = _get_speed_bin_tck_cas(spec, speed_bin, tck_avg_ps, select_mode, &cl_obtained);
    if(rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Not able to find CAS Latency for speed bin:%s (%d)",
                   ddrctl_cinit_get_ddr5_speed_bin_str(speed_bin), speed_bin);
        return rslt;
    }

    SNPS_LOG("CAS Latency for %s: tCK(AVG)=%u, CL:%u", ddrctl_cinit_get_ddr5_speed_bin_str(speed_bin),
             tck_avg_ps, cl_obtained);

    *cas_latency = cl_obtained;

    return DDRCTL_SUCCESS;
}


static inline void _get_speed_bin_table(const ddrctl_bool_t is_3ds, const ddr5_speed_bin_timings_t** table_ptr,
                                        uint8_t* n_sgs)
{
    if (DDRCTL_TRUE == is_3ds) {
        cinit_ddr5_speed_bin_3ds_get_table(table_ptr, n_sgs);
    } else {
        cinit_ddr5_speed_bin_get_table(table_ptr, n_sgs);
    }
}


static inline void _get_cas_table(const ddrctl_bool_t is_3ds, const ddr5_speed_bin_tck_cas_t** table_ptr,
                                  uint8_t* n_sgs)
{
    if (DDRCTL_TRUE == is_3ds) {
        cinit_ddr5_speed_bin_3ds_get_cas_table(table_ptr, n_sgs);
    } else {
        cinit_ddr5_speed_bin_get_cas_table(table_ptr, n_sgs);
    }
}


static ddrctl_error_t _get_speed_bin_timings(ddr5_jedec_spec_t spec, const dwc_ddr5_speed_bin_t speed_bin,
                                             const ddr5_speed_bin_timings_t** speed_bin_timings)
{
    const ddr5_speed_bin_timings_t* sb_table = NULL;
    uint8_t                         num_sb_entries;
    uint8_t                         i;

    _get_speed_bin_table(IS_SPEED_BIN_3DS(speed_bin), &sb_table, &num_sb_entries);
    if(sb_table == NULL) {
        SNPS_ERROR("Speed bin table ptr acquired is NULL!");
        return DDRCTL_INVALID_NULL_PTR;
    }

    for(i = 0; i < num_sb_entries; i++) {
        if ((sb_table[i].spec_bitmap & spec) == 0) {
            continue;
        }

        if(sb_table[i].speed_bin == speed_bin) {
            *speed_bin_timings = &(sb_table[i]);
            return DDRCTL_SUCCESS;
        }
    }

    return DDRCTL_ENTRY_NOT_FOUND;
}


#define JEDEC_MAX_VALID_SPEED_BINS 4

static ddrctl_error_t _get_speed_bin_tck_cas(ddr5_jedec_spec_t spec, const dwc_ddr5_speed_bin_t speed_bin,
                                             const uint16_t tck_avg_ps, const ddr_select_cl_alg_t select_mode,
                                             uint8_t* cas_latency)
{
    const ddr5_speed_bin_tck_cas_t* tck_cas_table = NULL;
    const ddr5_speed_bin_tck_cas_t* tck_in_range_cas_table[JEDEC_MAX_VALID_SPEED_BINS];
    const ddr5_speed_bin_timings_t* sb_timings = NULL;
    ddrctl_error_t                  rslt;
    uint8_t                         num_tck_cas_entries;
    uint8_t                         valid_entries_count = 0;
    uint8_t                         i, j;

    *cas_latency = (select_mode == SELECT_LOWER_CL ? 0xFF : 0);

    // Get Speed bin timing table entry
    rslt = _get_speed_bin_timings(spec, speed_bin, &sb_timings);
    if(rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Timings not found for speed bin:%s (%d) on %s spec",
                    ddrctl_cinit_get_ddr5_speed_bin_str(speed_bin), speed_bin,
                    ddrctl_cinit_get_ddr5_version_str(spec));
        return rslt;
    }

    rslt = DDRCTL_ENTRY_NOT_FOUND;

    _get_cas_table(IS_SPEED_BIN_3DS(speed_bin), &tck_cas_table, &num_tck_cas_entries);
    if(tck_cas_table == NULL) {
        SNPS_ERROR("Speed Bins CAS table ptr acquired is NULL!");
        return DDRCTL_INVALID_NULL_PTR;
    }

    for(i = 0; i < num_tck_cas_entries; i++) {
        if( tck_avg_ps < tck_cas_table[i].min_tck_ps) {
            continue;
        }
        if( tck_avg_ps > tck_cas_table[i].max_tck_ps) {
            continue;
        }

        // Check if the down bin is supported by the speed bin
        for(j = 0; j < sb_timings->num_down_bins; j++) {
            if (tck_cas_table[i].speed_bin != sb_timings->down_bins[j]) {
                continue;
            }
            tck_in_range_cas_table[valid_entries_count] = &(tck_cas_table[i]);
            valid_entries_count++;
            break;
        }

        // Only four entries are possible for a given tCK(AVG)
        if (valid_entries_count == JEDEC_MAX_VALID_SPEED_BINS) {
            break;
        }
    }

    for(i = 0; i < valid_entries_count; i++) {
        // Get Lower possible CAS Latency
        if (select_mode == SELECT_LOWER_CL) {
            if ((*cas_latency) > tck_in_range_cas_table[i]->cl) {
                *cas_latency = tck_in_range_cas_table[i]->cl;
                rslt = DDRCTL_SUCCESS;
            }
        } else { // Get Higher possible CAS Latency
            if((*cas_latency) < tck_in_range_cas_table[i]->cl) {
                *cas_latency = tck_in_range_cas_table[i]->cl;
                rslt = DDRCTL_SUCCESS;
            }
        }
    }

    return rslt;
}


/**
 * @brief Method to return the lower CAS Latency supported for the provided timings
 *
 * @param tck_avg_ps    Average tCK in picoseconds
 * @param taa_min_ps    Minimum SDRAM Read Command to first data in picoseconds
 * @param trcd_ps       Minimum SDRAM Activate to Read or Write command delay in picoseconds
 * @param trp_ps        Minimum SDRAM Row Precharge Time in picoseconds
 * @param is_3ds        DDRCTL_TRUE if module is 3DS
 * @param cas_latency   returned CAS Latency value
 *
 * @return ddrctl_error_t return code, DDRCTL_SUCCESS, DDRCTL_ENTRY_NOT_FOUND or DDRCTL_INVALID_NULL_PTR
 */
ddrctl_error_t ddrctl_cinit_get_ddr5_cas_latency(const uint16_t tck_avg_ps, const uint16_t taa_min_ps,
                                                 const uint16_t trcd_ps, const uint16_t trp_ps,
                                                 const ddrctl_bool_t is_3ds, uint8_t *cas_latency)
{
    const ddr5_speed_bin_tck_cas_t* tck_cas_table = NULL;
    ddrctl_error_t                  rslt;
    uint8_t                         num_tck_cas_entries;
    uint8_t                         index;

    *cas_latency = 0xFF;
    rslt = DDRCTL_ENTRY_NOT_FOUND;

    _get_cas_table(is_3ds, &tck_cas_table, &num_tck_cas_entries);
    if(tck_cas_table == NULL) {
        SNPS_ERROR("Speed Bins CAS table not found");
        return DDRCTL_INVALID_NULL_PTR;
    }

    for(index = 0; index < num_tck_cas_entries; index++) {
        if( tck_avg_ps < tck_cas_table[index].min_tck_ps) {
            continue;
        }
        if( tck_avg_ps > tck_cas_table[index].max_tck_ps) {
            continue;
        }

        if( taa_min_ps > tck_cas_table[index].taa_min_ps) {
            continue;
        }

        if( trcd_ps > tck_cas_table[index].trcd_trp_min_ps) {
            continue;
        }

        if( trp_ps > tck_cas_table[index].trcd_trp_min_ps) {
            continue;
        }

        if (tck_cas_table[index].cl < (*cas_latency)) {
            *cas_latency = tck_cas_table[index].cl;
            rslt = DDRCTL_SUCCESS;
        }
    }

    return rslt;
}


#endif /* DDRCTL_DDR */
