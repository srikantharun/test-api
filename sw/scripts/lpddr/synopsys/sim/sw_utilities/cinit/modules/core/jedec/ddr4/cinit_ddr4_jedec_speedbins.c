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
#include "cinit_ddr4_speedbin_types.h"
#include "cinit_ddr4_speedbin_tables.h"
#include "dwc_cinit_macros.h"


#ifdef DDRCTL_DDR

/* The following macros should be moved to a different header file */
#define IS_DDR4_SG_NON_3DS(sg_e) (sg_e > DWC_DDR4_MONO_FIRST_SG && sg_e < DWC_DDR4_MONO_LAST_SG) /* UNSAFE MACRO */
#define IS_DDR4_SG_3DS(sg_e) (sg_e > DWC_DDR4_3DS_FIRST_SG && sg_e < DWC_DDR4_3DS_LAST_SG) /* UNSAFE MACRO */
#define IS_DDR4_SG(sg_e) ((IS_DDR4_SG_NON_3DS(sg_e)) || (IS_DDR4_SG_3DS(sg_e))) /* UNSAFE MACRO */

typedef enum ddr4_type_e {
    DDR4_NON_3DS,
    DDR4_3DS,
    DDR4_TYPE_LAST_ELEM
} ddr4_type_t;

typedef struct ddr4_sg_min_clk_ps_s {
    dwc_ddr4_speed_grade_e sg_e;
    uint16_t min_tck_ps;
} ddr4_sg_min_clk_ps_t;

/* TODO Check and update if needed 2133MHZ tck(AVG)min from 938 to 937 for impacted cas configs */
static const ddr4_sg_min_clk_ps_t sg_min_clock_ps_table[] = {
    /* Speed Grade      Min TCK Ps */
    { DWC_DDR4_1600J,       1250 },
    { DWC_DDR4_1600K,       1250 },
    { DWC_DDR4_1600L,       1250 },
    { DWC_DDR4_1866L,       1071 },
    { DWC_DDR4_1866M,       1071 },
    { DWC_DDR4_1866N,       1071 },
    { DWC_DDR4_2133N,       938  },
    { DWC_DDR4_2133P,       938  },
    { DWC_DDR4_2133R,       938  },
    { DWC_DDR4_2400P,       833  },
    { DWC_DDR4_2400R,       833  },
    { DWC_DDR4_2400T,       833  },
    { DWC_DDR4_2400U,       833  },
    { DWC_DDR4_2666T,       750  },
    { DWC_DDR4_2666U,       750  },
    { DWC_DDR4_2666V,       750  },
    { DWC_DDR4_2666W,       750  },
    { DWC_DDR4_2933V,       682  },
    { DWC_DDR4_2933W,       682  },
    { DWC_DDR4_2933Y,       682  },
    { DWC_DDR4_2933AA,      682  },
    { DWC_DDR4_3200W,       625  },
    { DWC_DDR4_3200AA,      625  },
    { DWC_DDR4_3200AC,      625  },
    /* Speed Grade           Min TCK Ps */
    { DWC_DDR4_1600J_3DS2B,     1250 },
    { DWC_DDR4_1600K_3DS2B,     1250 },
    { DWC_DDR4_1600L_3DS2B,     1250 },
    { DWC_DDR4_1866L_3DS2B,     1071 },
    { DWC_DDR4_1866M_3DS2B,     1071 },
    { DWC_DDR4_1866N_3DS2B,     1071 },
    { DWC_DDR4_2133P_3DS2A,     938  },
    { DWC_DDR4_2133P_3DS3A,     938  },
    { DWC_DDR4_2133R_3DS4A,     938  },
    { DWC_DDR4_2400P_3DS3B,     833  },
    { DWC_DDR4_2400T_3DS2A,     833  },
    { DWC_DDR4_2400U_3DS2A,     833  },
    { DWC_DDR4_2400U_3DS4A,     833  },
    { DWC_DDR4_2666T_3DS3A,     750  },
    { DWC_DDR4_2666V_3DS3A,     750  },
    { DWC_DDR4_2666W_3DS4A,     750  },
    { DWC_DDR4_2933W_3DS3A,     682  },
    { DWC_DDR4_2933Y_3DS3A,     682  },
    { DWC_DDR4_2933AA_3DS43A,   682  },
    { DWC_DDR4_3200W_3DS4A,     625  },
    { DWC_DDR4_3200AA_3DS4A,    625  },
    { DWC_DDR4_3200AC_3DS4A,    625  }
};

/* Auxiliar static functions that can be used internally by this module's interfaces */
static ddr_speedbins_ret_t _get_sg_speedbin(const dwc_ddr4_speed_grade_e sg, const ddr4_type_t ddr4_spec_type, const ddr4_speedbin_t** sg_speedbin);
static ddr_speedbins_ret_t _get_sg_cas_cfg(const ddr4_type_t ddr4_spec_type, ddr4_speedbin_t const * const sg_spbin,
                                           const uint16_t tck_avg_ps, const ddr_select_cl_alg_t pick_cl_alg,
                                           uint8_t* const cl, uint8_t* const rdbi);
static ddr_speedbins_ret_t _get_sg_min_clock_cycle_time(const dwc_ddr4_speed_grade_e sg, uint16_t* const sg_min_tck_ps);
static inline ddr_speedbins_ret_t _get_ddr4_spec_type(const dwc_ddr4_speed_grade_e sg, ddr4_type_t* const ddr4_spec_type);
static inline void _adjust_cl_with_geardown_mode(const bool geardown_mode, uint8_t* const cl);


ddr_speedbins_ret_t cinit_ddr4_speedbins_set_clk_timings(const dwc_ddr4_speed_grade_e sg, ddrTimingParameters_t* const timings)
{
    SNPS_TRACE("Entering");
    ddr_speedbins_ret_t op_status;
    uint16_t sg_min_tck_ps;
    ddr4_type_t ddr4_spec_type;
    const ddr4_speedbin_t* sg_spbin = NULL;

    if(timings == NULL) {
        SNPS_ERROR("Received NULL_PTR for ddrTimingParameters_t* const timings!");
        return SPBINS_INVALID_NULL_PTR;
    }

    op_status = _get_ddr4_spec_type(sg, &ddr4_spec_type);
    if(op_status != SPBINS_OK) {
        SNPS_ERROR("Sg:%d input is invalid!",sg);
        return op_status;
    }

    op_status = _get_sg_min_clock_cycle_time(sg, &sg_min_tck_ps);
    if(op_status != SPBINS_OK) {
        SNPS_ERROR("Not able to fetch minimum clock cycle time for the requested sg:%d",sg);
        return op_status;
    }

    op_status = _get_sg_speedbin(sg, ddr4_spec_type, &sg_spbin);
    if(op_status != SPBINS_OK) {
        SNPS_ERROR("Not able to find speed grade speed bin parameters for sg:%d",sg);
        return op_status;
    }

    timings->sg_tck_ps = sg_min_tck_ps;
    timings->trcd_ps = sg_spbin->trcd_ps;
    timings->trp_ps = sg_spbin->trp_ps;
    timings->ddr4_tras_min_ps = sg_spbin->tras_min_ps;
    timings->trc_ps = sg_spbin->trc_ps;

    SNPS_LOG("Set clk parameters for sg:%d, min_tck_ps:%u trcd_ps:%u trp_ps=%u tras_min_ps=%u trc_ps=%u",
            sg,
            timings->sg_tck_ps,
            timings->trcd_ps,
            timings->trp_ps,
            timings->ddr5_tras_min_ps,
            timings->trc_ps);

    SNPS_TRACE("Leaving");
    return SPBINS_OK;
}

bool cinit_ddr4_is_speedbin_geardown_supported(const dwc_ddr4_speed_grade_e sg){
    switch (sg){
        case DWC_DDR4_1600J:
        case DWC_DDR4_1600K:
        case DWC_DDR4_1600L:
        case DWC_DDR4_1600J_3DS2B:
        case DWC_DDR4_1600K_3DS2B:
        case DWC_DDR4_1600L_3DS2B:
        case DWC_DDR4_1866L:
        case DWC_DDR4_1866M:
        case DWC_DDR4_1866N:
        case DWC_DDR4_1866L_3DS2B:
        case DWC_DDR4_1866M_3DS2B:
        case DWC_DDR4_1866N_3DS2B:
        case DWC_DDR4_2133N:
        case DWC_DDR4_2133P:
        case DWC_DDR4_2133R:
        case DWC_DDR4_2133P_3DS2A:
        case DWC_DDR4_2133P_3DS3A:
        case DWC_DDR4_2133R_3DS4A:
        case DWC_DDR4_2400P:
        case DWC_DDR4_2400R:
        case DWC_DDR4_2400T:
        case DWC_DDR4_2400U:
        case DWC_DDR4_2400P_3DS3B:
        case DWC_DDR4_2400T_3DS2A:
        case DWC_DDR4_2400U_3DS2A:
        case DWC_DDR4_2400U_3DS4A:
            return false;
            break;
        case DWC_DDR4_2666T:
        case DWC_DDR4_2666U:
        case DWC_DDR4_2666V:
        case DWC_DDR4_2666W:
        case DWC_DDR4_2666T_3DS3A:
        case DWC_DDR4_2666V_3DS3A:
        case DWC_DDR4_2666W_3DS4A:
        case DWC_DDR4_2933V:
        case DWC_DDR4_2933W:
        case DWC_DDR4_2933Y:
        case DWC_DDR4_2933AA:
        case DWC_DDR4_3200W:
        case DWC_DDR4_3200AA:
        case DWC_DDR4_3200AC:
        case DWC_DDR4_3200W_3DS4A:
        case DWC_DDR4_3200AA_3DS4A:
        case DWC_DDR4_3200AC_3DS4A:
            return true;
            break;
        default:
            return true;
            break;
    }
}

ddr_speedbins_ret_t cinit_ddr4_speedbins_set_cas_latencys(const dwc_ddr4_speed_grade_e sg, const uint16_t tck_avg_ps,
                                                           const ddr_select_cl_alg_t pick_cl_alg, const bool dll_off_mode,
                                                           const bool gd_mode, ddrTimingParameters_t* const timings)
{
    SNPS_TRACE("Entering");
    ddr_speedbins_ret_t op_status;
    ddr4_type_t ddr4_spec_type;
    const ddr4_speedbin_t* sg_spbin = NULL;
    uint8_t cl;
    uint8_t rdbi_cl;

    if(timings == NULL) {
        SNPS_ERROR("Received NULL_PTR for ddrTimingParameters_t* const timings!");
        return SPBINS_INVALID_NULL_PTR;
    }

    if ((gd_mode == true) && (cinit_ddr4_is_speedbin_geardown_supported(sg) == false)) { // error out if geardown is active on an unsupported speed grade
        SNPS_ERROR("Geardown is active on an unsupported speed grade");
        return SPBINS_NOT_SUPPORTED;
    }

    if (dll_off_mode == true) { //No need to search in speedbin cas cfgs
        cl = CL_DLL_OFF_MODE;
        rdbi_cl = CL_RDBI_DLL_OFF_MODE;
        _adjust_cl_with_geardown_mode(gd_mode,&cl);
        _adjust_cl_with_geardown_mode(gd_mode,&rdbi_cl);
        timings->ddr4_tcl_tck = cl;
        timings->ddr4_tcl_rdbi_tck = rdbi_cl;
        SNPS_TRACE("Leaving");
        return SPBINS_OK;
    }

    op_status = _get_ddr4_spec_type(sg,&ddr4_spec_type);
    if(op_status != SPBINS_OK) {
        SNPS_ERROR("Sg:%d input is invalid!",sg);
        return op_status;
    }

    //get sg speed bin ptr
    op_status = _get_sg_speedbin(sg, ddr4_spec_type, &sg_spbin);
    if(op_status != SPBINS_OK) {
        SNPS_ERROR("Not able to find speed grade speed bin parameters for sg:%d",sg);
        return op_status;
    }

    //get cas config for the speedgrade
    op_status = _get_sg_cas_cfg(ddr4_spec_type, sg_spbin, tck_avg_ps, pick_cl_alg, &cl, &rdbi_cl);
    if(op_status != SPBINS_OK && op_status != SPBINS_CAS_CFG_NOT_FOUND) {
        SNPS_ERROR("Not able to find cas cfg for sg:%d tck_ps:%u", sg, tck_avg_ps);
        return op_status;
    } else if(op_status == SPBINS_CAS_CFG_NOT_FOUND) {
        // TODO: Clarify why this branch condition is really needed
        timings->ddr4_tcl_tck = 0;
        timings->ddr4_tcl_rdbi_tck = 0;
        SNPS_LOG("WORKAROUND FOR NO CAS FOUND for sg:%d, tck_ps:%u, cl:%u, rdbi_cl:%u", sg, tck_avg_ps, timings->ddr4_tcl_tck, timings->ddr4_tcl_rdbi_tck);
    } else if(op_status == SPBINS_OK) {
        if (ddr4_spec_type == DDR4_3DS) {
            //Setting rdbi_cl = cl for 3DS packages (3DS spec does not contain information regarding rdbi)
            rdbi_cl = cl;
        }
        _adjust_cl_with_geardown_mode(gd_mode,&cl);
        _adjust_cl_with_geardown_mode(gd_mode,&rdbi_cl);

        timings->ddr4_tcl_tck = cl;
        timings->ddr4_tcl_rdbi_tck = rdbi_cl;
        SNPS_LOG("SET Cas timings to cl:%u, rdbi_cl:%u", timings->ddr4_tcl_tck, timings->ddr4_tcl_rdbi_tck);
    }

    SNPS_TRACE("Leaving");
    return SPBINS_OK;
}

static ddr_speedbins_ret_t _get_sg_min_clock_cycle_time(const dwc_ddr4_speed_grade_e sg, uint16_t* const sg_min_tck_ps)
{
    SNPS_TRACE("Entering");
    uint8_t n_ddr4_sgs = GET_ARR_NELEMS(sg_min_clock_ps_table);
    const ddr4_sg_min_clk_ps_t* sg_min_clk_ps_ptr = sg_min_clock_ps_table;

    for(uint8_t i=0; i < n_ddr4_sgs; i++) {
        if (sg_min_clk_ps_ptr[i].sg_e == sg) {
            *sg_min_tck_ps = sg_min_clk_ps_ptr[i].min_tck_ps;
            SNPS_TRACE("Leaving");
            return SPBINS_OK;
        }
    }
    return SPBINS_SG_MIN_TCK_PS_NOT_FOUND;
}


static ddr_speedbins_ret_t _get_sg_speedbin(const dwc_ddr4_speed_grade_e sg, const ddr4_type_t ddr4_spec_type,
                                            const ddr4_speedbin_t** sg_speedbin)
{
    SNPS_TRACE("Entering");
    uint8_t n_sgs; //number of elements in sg speedbins table

    if(ddr4_spec_type == DDR4_NON_3DS) {
        get_ddr4_speedbin_table(sg_speedbin, &n_sgs);
    } else {
        get_ddr4_3ds_speedbin_table(sg_speedbin, &n_sgs);
    }

    if(*sg_speedbin == NULL) {
        SNPS_ERROR("Speed bin table ptr acquired is NULL!");
        return SPBINS_TABLE_NULL_PTR;
    }
    //iterate over speedbin table until we find the speedgrade table entry we are looking for
    for(uint8_t i=0; i < n_sgs; i++) {
        if((*sg_speedbin)[i].sg_e == sg) {
            *sg_speedbin = &((*sg_speedbin)[i]);
            SNPS_TRACE("Leaving");
            return SPBINS_OK;
        }
    }

    //speed bin was not found in JEDEC speedbin table
    return SPBINS_SPEED_BIN_ENTRY_NOT_FOUND;
}


static ddr_speedbins_ret_t _get_sg_cas_cfg(const ddr4_type_t ddr4_spec_type, ddr4_speedbin_t const * const sg_spbin,
                                           const uint16_t tck_avg_ps, const ddr_select_cl_alg_t pick_cl_alg,
                                           uint8_t* const cl, uint8_t* const rdbi)
{
    SNPS_TRACE("Entering");
    const ddr4_cas_cfg_t* sg_cas_cfgs_non_3ds_ptr;
    const ddr4_3ds_cas_cfg_t* sg_cas_cfgs_3ds_ptr;
    uint8_t n_cas_cfgs;

    uint8_t cl_selected = (pick_cl_alg == SELECT_LOWER_CL ? 0xFF : 0);
    uint8_t rdbi_selected = 0;
    bool  cas_found = false;

    if (NULL == sg_spbin) {
        SNPS_ERROR("Speed bin ptr acquired is NULL!");
        return SPBINS_INVALID_NULL_PTR;
    }

    n_cas_cfgs = sg_spbin->n_cas_cfgs;

    //Assuming that cas configs are not ordered
    if(DDR4_NON_3DS == ddr4_spec_type) {
        sg_cas_cfgs_non_3ds_ptr = sg_spbin->ddr4_type_specific.spec_non_3ds.cas_cfgs;

        if(sg_cas_cfgs_non_3ds_ptr == NULL) {
            SNPS_ERROR("Sg:%d cas configs ptr is set to NULL!",sg_spbin->sg_e);
            return SPBINS_CAS_CFG_NOT_FOUND;
        }

        for(uint8_t i = 0; i < n_cas_cfgs; i++) {
            if(sg_cas_cfgs_non_3ds_ptr[i].min_tck_ps <= tck_avg_ps &&
               sg_cas_cfgs_non_3ds_ptr[i].max_tck_ps >= tck_avg_ps) { //check if cas cfg being iterated is valid for current tCK(AVG)
                if ((pick_cl_alg == SELECT_LOWER_CL && cl_selected > sg_cas_cfgs_non_3ds_ptr[i].cl) || //possible lower cl found
                    (pick_cl_alg == SELECT_HIGHER_CL && cl_selected < sg_cas_cfgs_non_3ds_ptr[i].cl)) { //possible higher cl found
                        cl_selected = sg_cas_cfgs_non_3ds_ptr[i].cl;
                        rdbi_selected = sg_cas_cfgs_non_3ds_ptr[i].rdbi;
                }
            }
        }
    } else { //3DS granted as sg enum ranges were previously verified
        sg_cas_cfgs_3ds_ptr = sg_spbin->ddr4_type_specific.spec_3ds.cas_cfgs;

        if(sg_cas_cfgs_3ds_ptr == NULL) {
            SNPS_ERROR("Sg:%d cas configs ptr is set to NULL!",sg_spbin->sg_e);
            return SPBINS_CAS_CFG_NOT_FOUND;
        }

        for(uint8_t i = 0; i < n_cas_cfgs; i++) {
            if(sg_cas_cfgs_3ds_ptr[i].min_tck_ps <= tck_avg_ps &&
               sg_cas_cfgs_3ds_ptr[i].max_tck_ps >= tck_avg_ps) { //check if cas cfg being iterated is valid for current tCK(AVG)
                if( (pick_cl_alg == SELECT_LOWER_CL && cl_selected > sg_cas_cfgs_3ds_ptr[i].cl) || //possible lower cl found
                    (pick_cl_alg == SELECT_HIGHER_CL && cl_selected < sg_cas_cfgs_3ds_ptr[i].cl) ) {  //possible higher cl found
                    cl_selected = sg_cas_cfgs_3ds_ptr[i].cl;
                    //3DS does not support data bus inversion (no rdbi timing specified in 3ds specs)
                }
            }
        }
    }

    if(cl_selected != 0xFF && cl_selected != 0x00) { //cas config was found
        cas_found = true;
        *cl = cl_selected;
        *rdbi = rdbi_selected;
    }
    SNPS_TRACE("Leaving");
    return cas_found == true ? SPBINS_OK : SPBINS_CAS_CFG_NOT_FOUND;
}

static inline ddr_speedbins_ret_t _get_ddr4_spec_type(const dwc_ddr4_speed_grade_e sg, ddr4_type_t* const ddr4_spec_type)
{
    ddr_speedbins_ret_t op_status = SPBINS_INVALID_SPEED_BIN;
    if (IS_DDR4_SG_NON_3DS(sg)) {
        *ddr4_spec_type = DDR4_NON_3DS;
        op_status = SPBINS_OK;
    } else if (IS_DDR4_SG_3DS(sg)) {
        *ddr4_spec_type = DDR4_3DS;
        op_status = SPBINS_OK;
    }
    return op_status;
};


static inline void _adjust_cl_with_geardown_mode(const bool geardown_mode, uint8_t* const cl) {
    if( (true == geardown_mode) && ((*cl % 2) != 0) ) { //geardown enabled and cl odd -> add 1 to cl obtained from speedbins
        (*cl)++; //increment cl value by one
    }
}

#endif /* DDRCTL_DDR */
