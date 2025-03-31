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


#include "ctrl_words/ddr5/cinit_ddr5_ctrl_words.h"
#include "ddrctl_sw_ddr5_ctrl_words_macros.h"
#include "dwc_ddrctl_cinit_util.h"

#ifdef DDRCTL_DDR

uint8_t ddrctl_sw_get_ddr5_rdimm_operating_speed(SubsysHdlr_t *cfg, uint32_t pstate);


uint8_t ddrctl_sw_get_ddr5_ctrl_word(SubsysHdlr_t *cfg, uint32_t pstate, uint8_t mw_num)
{
    uint8_t mw_value = 0;

    switch(mw_num) {
        case 0:
            SNPS_WRITE_FIELD(mw_value, DDR5_RW00_CMD_ADDR_RATE, cfg->ddr5_cw.rw00.ca_rate); // match mr2.ddr5_2n_mode
            SNPS_WRITE_FIELD(mw_value, DDR5_RW00_SDR_MODE,      cfg->ddr5_cw.rw00.sdr_mode);
            break;
        case 1:
            SNPS_WRITE_FIELD(mw_value, DDR5_RW01_PARITY_CHECKING,   cfg->ddr5_cw.rw01.parity_check);
            SNPS_WRITE_FIELD(mw_value, DDR5_RW01_DRAM_IF_CMDS,      cfg->ddr5_cw.rw01.dram_if_cmds);
            SNPS_WRITE_FIELD(mw_value, DDR5_RW01_DATABUFFER_CMDS,   cfg->ddr5_cw.rw01.databuffer_cmds);
            SNPS_WRITE_FIELD(mw_value, DDR5_RW01_ALERT_N_ASSERTION, cfg->ddr5_cw.rw01.alert_n_assertion);
            SNPS_WRITE_FIELD(mw_value, DDR5_RW01_ALERT_N_RE_ENABLE, cfg->ddr5_cw.rw01.alert_n_reenable);
            break;
        case 5:
            SNPS_WRITE_FIELD(mw_value, DDR5_RW05_OPERATING_SPEED,
                             ddrctl_sw_get_ddr5_rdimm_operating_speed(cfg, pstate));
            break;
        case 0x11:
            SNPS_WRITE_FIELD(mw_value, DDR5_RW11_LATENCY_ADDER_NLADD,
                             cfg->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd);
            break;
        default:
            SNPS_ERROR("Control word 0x%0x not supported", mw_num);
            dwc_ddrctl_cinit_exit(1);
            break;
    }

    return mw_value;
}

/**
 * @brief Returns the speed grade id based on the  speed grade
 *  This implementation is aligned with Jedec Specs DDR5DB02
 *
 * @param speed_grade
 * @return ddrctl_error_t
 */
ddrctl_error_t cinit_ddr5_get_rw05_speed_grade_id(dwc_ddr5_speed_grade_t speed_grade, uint8_t *sg_id)
{
    uint8_t ret_id;
    switch(speed_grade)
    {
        case DWC_DDR5_SG_2100:
            ret_id = 14;
            break;
        case DWC_DDR5_SG_3200:
            ret_id = 0;
            break;
        case DWC_DDR5_SG_3600:
            ret_id = 1;
            break;
        case DWC_DDR5_SG_4000:
            ret_id = 2;
            break;
        case DWC_DDR5_SG_4400:
            ret_id = 3;
            break;
        case DWC_DDR5_SG_4800:
            ret_id = 4;
            break;
        case DWC_DDR5_SG_5200:
            ret_id = 5;
            break;
        case DWC_DDR5_SG_5600:
            ret_id = 6;
            break;
        case DWC_DDR5_SG_6000:
            ret_id = 7;
            break;
        case DWC_DDR5_SG_6400:
            ret_id = 8;
            break;
        case DWC_DDR5_SG_6800:
            ret_id = 9;
            break;
        case DWC_DDR5_SG_7200:
            ret_id = 10;
            break;
        case DWC_DDR5_SG_7600:
            ret_id = 11;
            break;
       case DWC_DDR5_SG_8000:
            ret_id = 12;
            break;
       case DWC_DDR5_SG_8400:
            ret_id = 13;
            break;
        //8800 is not defined in RCD03 spec, so use the same value with 8400.
        case DWC_DDR5_SG_8800:
            ret_id = 13;
            break;
        default:
            return DDRCTL_ERROR;
    }

    (*sg_id) = ret_id;

    return DDRCTL_SUCCESS;
}

/**
 * @brief Returns the fine granularity DIMM operating speed based on the clock
 *  This implementation is aligned with Jedec Specs DDR5DB02
 *
 * @param tck_ps
 * @return ddrctl_error_t
 */
ddrctl_error_t cinit_ddr5_get_rw85_fine_grain_speed_grade_id(uint32_t tck_ps, uint8_t *fg_sg_id)
{
    int32_t freq_mt;
    uint32_t freq_base;
    dwc_ddr5_speed_grade_t speed_grade;

    // Get base frequency
    speed_grade = cinit_ddr5_get_speedgrade_from_tck_avg_min(tck_ps);
    if(speed_grade == DWC_DDR5_SG_INVALID){
        return DDRCTL_ERROR;
    }
    freq_base = cinit_ddr5_get_speedgrade_base_frequency(speed_grade);

    // Calulate Frequency based on period
    freq_mt = SNPS_TCK_PS_TO_DDR_MHZ(tck_ps);

    // Calulate Frequency within that speed grade
    freq_mt = freq_base - freq_mt;

    // Calulate fine grain slot within that speed grade
    (*fg_sg_id) = freq_mt/20;

    return DDRCTL_SUCCESS;
}


uint8_t ddrctl_sw_get_ddr5_rdimm_operating_speed(SubsysHdlr_t *hdlr, uint32_t pstate)
{
    uint8_t operating_speed = 0;
    uint32_t tck_ps = SPD.tck_ps[pstate];

    if (IS_RDIMM || IS_LRDIMM) {
        if (tck_ps >= 625) {
            operating_speed = 0;
        } else if (tck_ps >= 555 && tck_ps < 625) {
            operating_speed = 1;
        } else if (tck_ps >= 500 && tck_ps < 555) {
            operating_speed = 2;
        } else if (tck_ps >= 454 && tck_ps < 500) {
            operating_speed = 3;
        } else if (tck_ps >= 416 && tck_ps < 454) {
            operating_speed = 4;
        } else if (tck_ps >= 384 && tck_ps < 416) {
            operating_speed = 5;
        } else if (tck_ps >= 357 && tck_ps < 384) {
            operating_speed = 6;
        } else if (tck_ps >= 333 && tck_ps < 357) {
            operating_speed = 7;
        } else if (tck_ps >= 312 && tck_ps < 333) {
            operating_speed = 8;
        } else if (tck_ps >= 294 && tck_ps < 312) {
            operating_speed = 9;
        } else if (tck_ps >= 277 && tck_ps < 294) {
            operating_speed = 10;
        } else if (tck_ps >= 263 && tck_ps < 277) {
            operating_speed = 10;
        } else if (tck_ps >= 250 && tck_ps < 263) {
            operating_speed = 10;
        } else if (tck_ps >= 238 && tck_ps < 250) {
            operating_speed = 10;
        } else if (tck_ps >= 227 && tck_ps < 238) {
            operating_speed = 10;
        } else {
            SNPS_ERROR(" tck_ps %u not yet supported for ddr5 rdimm/lrdimm", tck_ps);
        }
    }

    return operating_speed;
}

#endif // DDRCTL_DDR
