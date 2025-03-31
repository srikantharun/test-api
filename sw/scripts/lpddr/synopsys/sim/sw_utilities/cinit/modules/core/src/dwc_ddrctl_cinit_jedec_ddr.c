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


#include "dwc_ddrctl_cinit_jedec_ddr.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_jedec_to_cinit.h"
#include "jedec/cinit_ddr_speedbins.h"
#include "jedec/ddr5/cinit_ddr5_types.h"
#include "jedec/ddr5/cinit_ddr5_timing_utils.h"
#include "jedec/ddr5/cinit_ddr5_speed_bins_strings.h"
#include "dwc_ddrctl_cinit_defines.h"
#include "dwc_ddrctl_cinit_SPD.h"
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_util.h"

#if !defined(DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE) && !defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC) && !defined(DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC)
#define DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
#endif /* !DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE && !DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC && !DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC */

//TODO: Temporary workaround for the verification environment
#if defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC) && defined(DWC_DDRCTL_CINIT_CPU_DPI_MODE)
#undef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC
#define DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
#endif

#ifdef DDRCTL_DDR
// --------------------------------------------------------------------------
// Name        : ddr4::set_clk_speed()
// Description : set the sg_tck_ps value in the hdlr->timingParams_m structure
// Params      : hdlr
// Returns     : none
// --------------------------------------------------------------------------
void ddr4_set_clk_speed(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n)
{
    SNPS_TRACE("Entering");
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];

#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
	dwc_ddr4_speed_grade_e sg = hdlr->spdData_m.ddr4_sg;
    ddr_speedbins_ret_t op_status = cinit_ddr4_speedbins_set_clk_timings(sg, timing);
	if (op_status != SPBINS_OK) {
		SNPS_ERROR("JEDEC DDR4 speedbins module was not able to set clk timings! error code: %d", op_status);
        dwc_ddrctl_cinit_exit(1);
	}
#else /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    timing->sg_tck_ps = SPD_aux.DDR4.tCKAVGmin_ps;
    timing->trcd_ps = SPD_aux.DDR4.tRCDmin_ps;
    timing->trp_ps = SPD_aux.DDR4.tRPmin_ps;
    timing->ddr4_tras_min_ps = SPD_aux.DDR4.tRASmin_ps;
    timing->trc_ps = SPD_aux.DDR4.tRCmin_ps;
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */

    SNPS_TRACE("Leaving");
}

// --------------------------------------------------------------------------
// Name        : ddr4_set_default_timing()
// Description : set all the default values for SNPS VIP
// Returns     : none
// --------------------------------------------------------------------------
ddrctl_error_t ddr4_set_default_timing(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n)
{
    ddrTimingParameters_t *timing = &CFG->timingParams_m[p][n];
    uint32_t tck_ps = SPD.tck_ps[p];
    bool dll_off_init = QDYN.dll_off_mode;
    bool gd_en = CFG->memCtrlr_m.ddr4_mr[p].mr3.geardown;
    uint32_t ca_parity_en = CFG->memCtrlr_m.ddr4_mr[p].mr5.parity_latency_mode;
    uint32_t fgr_mode = CFG->memCtrlr_m.ddr4_mr[p].mr3.fine_granularity_refresh;
    uint32_t sdram_capacity_mbits = SPD.sdram_capacity_mbits[n];

    timing->burst_length = 8;  // BL 8 - Length value supported for DDR4
    timing->ddr4_tckmpe_ps = (24 + 4) * tck_ps;    // tMOD(min) + tCPDED(min) (Micron Datasheet)
    timing->ddr4_tcrc_alert_pw_tck = 10;
    if (dll_off_init == 1) {
        timing->ddr4_tcke_ps = tck_ps * 3;
        timing->ddr4_tpl_tck = 4;
        timing->ddr4_wcl_tck = 4;
        timing->ddr4_cal_tck = 3;
        timing->ddr4_tccd_l_tck = 4;
        timing->ddr4_tccd_dlr_tck = 4;
        timing->ddr4_txsdll_tck = 597;
        timing->ddr4_twtr_l_crc_dm_tck = 4;
        timing->ddr4_twtr_s_crc_dm_tck = 4;
        timing->ddr4_twtr_l_tck = 4;
        timing->ddr4_twtr_s_tck = 2;
        timing->ddr4_tpar_alert_pw_tck = 96;
    } else {
        timing->ddr4_tcke_ps = 5000;
        if (tck_ps >= 1250) { // DDR4-1600
            timing->ddr4_tpl_tck = 4;
            timing->ddr4_wcl_tck = 4;
            timing->ddr4_cal_tck = 3;
            timing->ddr4_tccd_l_tck = 5;
            timing->ddr4_tccd_dlr_tck = 4;
            timing->ddr4_txsdll_tck = 597;
            timing->ddr4_twtr_l_tck = 6;
            timing->ddr4_twtr_s_tck = 2;
            timing->ddr4_twtr_l_crc_dm_tck = 4;
            timing->ddr4_twtr_s_crc_dm_tck = 4;
            timing->ddr4_tpar_alert_pw_tck = 96;
        } else if (tck_ps < 1250 && tck_ps >= 1071) { // DDR4-1866
            timing->ddr4_tpl_tck = 4;
            timing->ddr4_wcl_tck = 5;
            timing->ddr4_cal_tck = 4;
            timing->ddr4_tccd_l_tck = 5;
            timing->ddr4_tccd_dlr_tck = 4;
            timing->ddr4_txsdll_tck = 597;
            timing->ddr4_twtr_l_tck = 8;
            timing->ddr4_twtr_s_tck = 3;
            timing->ddr4_twtr_l_crc_dm_tck = 5;
            timing->ddr4_twtr_s_crc_dm_tck = 5;
            timing->ddr4_tpar_alert_pw_tck = 112;
        } else if (tck_ps < 1071 && tck_ps >= 938) { // DDR4-2133
            timing->ddr4_tpl_tck = 4;
            timing->ddr4_wcl_tck = 5;
            timing->ddr4_cal_tck = 4;
            timing->ddr4_tccd_l_tck = 6;
            timing->ddr4_tccd_dlr_tck = 5;
            timing->ddr4_txsdll_tck = 768;
            timing->ddr4_twtr_l_tck = 8;
            timing->ddr4_twtr_s_tck = 3;
            timing->ddr4_twtr_l_crc_dm_tck = 5;
            timing->ddr4_twtr_s_crc_dm_tck = 5;
            timing->ddr4_tpar_alert_pw_tck = 128;
        } else if (tck_ps < 938 && tck_ps >= 833) { // DDR4-2400
            timing->ddr4_tpl_tck = 5;
            timing->ddr4_wcl_tck = 5;
            timing->ddr4_cal_tck = 5;
            timing->ddr4_tccd_l_tck = 6;
            timing->ddr4_tccd_dlr_tck = 5;
            timing->ddr4_txsdll_tck = 768;
            // In case of SNPS VIP which speedbin is sg083/sg083R/sg083T/sg083U, twtr_l_tck(twtr_s_tck) should be set to 10(4) instead of 9(3) to meet JEDEC, or the VIP checker will report error. See bug3221, comment49
            timing->ddr4_twtr_l_tck = 10;
            timing->ddr4_twtr_s_tck = 4;
            timing->ddr4_twtr_l_crc_dm_tck = 5;
            timing->ddr4_twtr_s_crc_dm_tck = 5;
            timing->ddr4_tpar_alert_pw_tck = 144;
        } else if (tck_ps < 833 && tck_ps >= 750) { // DDR4-2666
            timing->ddr4_tpl_tck = 5;
            timing->ddr4_wcl_tck = 5;    // JESD79-4C
            timing->ddr4_cal_tck = 5;
            timing->ddr4_tccd_l_tck = 7;
            timing->ddr4_tccd_dlr_tck = 5;    // TODO. TBD. This has not been defined in JEDEC v095c1f
            timing->ddr4_txsdll_tck = 1024;    // Jedec JESD79-4C
            timing->ddr4_twtr_l_tck = 10;
            timing->ddr4_twtr_s_tck = 4;
            timing->ddr4_twtr_l_crc_dm_tck = 5;
            timing->ddr4_twtr_s_crc_dm_tck = 5;
            timing->ddr4_tpar_alert_pw_tck = 160;
        } else if (tck_ps < 750 && tck_ps >= 682) { //values taken from Micron model; JEDEC spec not yet available
            timing->ddr4_tpl_tck = 6;    //TBD
            timing->ddr4_wcl_tck = 6;    //TBD
            timing->ddr4_cal_tck = 6;    //TBD
            timing->ddr4_tccd_l_tck = 8;
            timing->ddr4_tccd_dlr_tck = 5;    //TBD
            timing->ddr4_txsdll_tck = 1024;    // Jedec JESD79-4C
            timing->ddr4_twtr_l_tck = 11;
            timing->ddr4_twtr_s_tck = 4;
            timing->ddr4_twtr_l_crc_dm_tck = 6;
            timing->ddr4_twtr_s_crc_dm_tck = 6;
            timing->ddr4_tpar_alert_pw_tck = 176;
        } else if (tck_ps < 682 && tck_ps >= 625) { // DDR4-3200
            timing->ddr4_tpl_tck = 6;
            timing->ddr4_wcl_tck = 6;    // use value same with SNPS VIP
            timing->ddr4_cal_tck = 6;    // Micrion Datasheet
            timing->ddr4_tccd_l_tck = 8;    // Micron Model (Micron Datasheet: =max(5nCK, 5ns)=8)
            timing->ddr4_tccd_dlr_tck = 5;    // TODO. TBD. This has not been defined in JEDEC v095c1f
            timing->ddr4_txsdll_tck = 1024;    // Jedec JESD79-4B
            timing->ddr4_twtr_l_tck = 12;    // max(4nCK, 7.5ns) (Micron Datasheet)
            timing->ddr4_twtr_s_tck = 4;    // max(2nCK, 2.5ns) (Micron Datasheet)
            timing->ddr4_twtr_l_crc_dm_tck = 6;    // The definition of this parameter is tWTR_L+max(5nCK, 3.75ns) (Micron Datasheet).
            // But, in ddrc_cfg.sv, this is used as the delta between tWTR_L and tWTR_L_CRC_DM.
            timing->ddr4_twtr_s_crc_dm_tck = 6;    // The definition of this parameter is tWTR_S+max(5nCK, 3.75ns) (Micron Datasheet).
            // But, in ddrc_cfg.sv, this is used as the delta between tWTR_S and tWTR_S_CRC_DM
            timing->ddr4_tpar_alert_pw_tck = 192;    // tPAR_Alert_PWmax (Micron Datasheet)
        } else { // DLL-off mode
            SNPS_ERROR("Unknown speed grade, tck_ps = %d", tck_ps);
            return DDRCTL_NOT_SUPPORTED;
        }
    }

    // in shareac mode, don't support CAL is ODD value
    // so, plus 1 if CAL value is ODD. (so far, cal can be 3 or 5)
#ifdef UMCTL2_DUAL_DATA_CHANNEL
    if (timing->ddr4_cal_tck == 3)
        timing->ddr4_cal_tck = 4;
    else if (timing->ddr4_cal_tck == 5)
        timing->ddr4_cal_tck = 6;
#endif /* UMCTL2_DUAL_DATA_CHANNEL */
    if (gd_en == 1) {
        if (timing->ddr4_cal_tck % 2 != 0)
            timing->ddr4_cal_tck = timing->ddr4_cal_tck + 1;
        if (timing->ddr4_tpl_tck % 2 != 0)
            timing->ddr4_tpl_tck = timing->ddr4_tpl_tck + 1;
    }

    if (ca_parity_en == 0)
        timing->ddr4_tpl_tck = 0;
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
    if (IS_X16(n)) {
        if (dll_off_init == 1) {
            timing->trrd_l_tck = 4;
            timing->trrd_s_tck = 4;
            timing->ddr4_tfaw_ps = max(CEIL(35000, tck_ps), 28);
        } else {
            switch (tck_ps) {
            case 1250: // DDR4-1600
                timing->trrd_l_tck = 6;
                timing->trrd_s_tck = 5;
                timing->ddr4_tfaw_ps = 35000;
                break;
            case 1071: // DDR4-1866
                timing->trrd_l_tck = 6;
                timing->trrd_s_tck = 5;
                timing->ddr4_tfaw_ps = 30000;
                break;
            case 938: // DDR4-2133
                timing->trrd_l_tck = 7;
                timing->trrd_s_tck = 6;
                timing->ddr4_tfaw_ps = 30000;
                break;
            case 833: // DDR4-2400
                timing->trrd_l_tck = 8;
                timing->trrd_s_tck = 7;
                timing->ddr4_tfaw_ps = 30000;
                break;
            case 750: // DDR4-2666
                timing->trrd_l_tck = 9;
                timing->trrd_s_tck = 8;
                timing->ddr4_tfaw_ps = 30000;
                break;
            case 682: // DDR4-2933
                timing->trrd_l_tck = 10;
                timing->trrd_s_tck = 8;
                timing->ddr4_tfaw_ps = 30000;
                break;
            case 625: // DDR4-3200
                timing->trrd_l_tck = 11; // max(4nCK, 6.4ns) Micron Datasheet
                timing->trrd_s_tck = 9; // max(4nCK, 5.3ns) Micron Datas
                timing->ddr4_tfaw_ps = 30000; // max(16nCK, 10ns) (JESD79-4A_r0 Table 131)
                break;
            default:
                SNPS_ERROR("Unknown speed grade, tck = %d", tck_ps);
                return DDRCTL_NOT_SUPPORTED;
            }
        }
    } else if (IS_X8(n)) {
        timing->ddr4_trrd_dlr_tck = 4;
        timing->ddr4_tfaw_dlr_tck = 16;
        if (dll_off_init == 1) {
            timing->trrd_l_tck = 4;
            timing->trrd_s_tck = 4;
            timing->ddr4_tfaw_ps = max(CEIL(25000, tck_ps), 20);
        } else {
            switch (tck_ps) {
            case 1250:
                timing->trrd_l_tck = 5;
                timing->trrd_s_tck = 4;
                timing->ddr4_tfaw_ps = 25000;
                break;
            case 1071: // DDR4-1866
                timing->trrd_l_tck = 5;
                timing->trrd_s_tck = 4;
                timing->ddr4_tfaw_ps = 23000;
                break;
            case 938: // DDR4-2133
                timing->trrd_l_tck = 6;
                timing->trrd_s_tck = 4;
                timing->ddr4_tfaw_ps = 21000;
                break;
            case 833: // DDR4-2400
                timing->trrd_l_tck = 6;
                timing->trrd_s_tck = 4;
                timing->ddr4_tfaw_ps = 21000;
                break;
            case 750: // DDR4-2666
                timing->trrd_l_tck = 7;
                timing->trrd_s_tck = 4; // max(4nCK, \1 ns) (JESD79-4A_r0 Table 131)
                timing->ddr4_tfaw_ps = 21000; // max(16nCK, 12ns) (JESD79-4A_r0 Table 131)
                break;
            case 682: // DDR4-2933
                timing->trrd_l_tck = 8;
                timing->trrd_s_tck = 4;
                timing->ddr4_tfaw_ps = 21000;
                break;
            case 625: // DDR4-3200
                timing->trrd_l_tck = 8; // max(4nCK, 4.9ns) Micron Datasheet
                timing->trrd_s_tck = 4; // max(4nCK, 2.5 ns) (JESD79-4A_r0 Table 131)
                timing->ddr4_tfaw_ps = 21000; // max(16nCK, 10ns) (JESD79-4A_r0 Table 131)
                break;
            default:
                SNPS_ERROR("Unknown speed grade, tck = %d", tck_ps);
                return DDRCTL_NOT_SUPPORTED;
            }
        }
    } else if (IS_X4(n)) {
        timing->ddr4_trrd_dlr_tck = 4;
        timing->ddr4_tfaw_dlr_tck = 16;
        if (dll_off_init == 1) {
            timing->trrd_l_tck = 4;
            timing->trrd_s_tck = 4;
            timing->ddr4_tfaw_ps = max(CEIL(20000, tck_ps), 16);
        } else {
            switch (tck_ps) {
            case 1250: // DDR4-1600
                timing->trrd_l_tck = 5;
                timing->trrd_s_tck = 4;
                timing->ddr4_tfaw_ps = 20000;
                break;
            case 1071: // DDR4-1866
                timing->trrd_l_tck = 5;
                timing->trrd_s_tck = 4;
                timing->ddr4_tfaw_ps = 17000;
                break;
            case 938: // DDR4-2133
                timing->trrd_l_tck = 6;
                timing->trrd_s_tck = 4;
                timing->ddr4_tfaw_ps = 15000;
                break;
            case 833: // DDR4-2400
                timing->trrd_l_tck = 6;
                timing->trrd_s_tck = 4;
                timing->ddr4_tfaw_ps = 13000;
                break;
            case 750: // DDR4-2666
                timing->trrd_l_tck = 7;
                timing->trrd_s_tck = 4; // max(4nCK, 3 ns) (JESD79-4A_r0 Table 131)
                timing->ddr4_tfaw_ps = 12000;
                break;
            case 682: // DDR4-2933
                timing->trrd_l_tck = 8;
                timing->trrd_s_tck = 5;
                timing->ddr4_tfaw_ps = 10875;
                break;
            case 625: // DDR4-3200
                timing->trrd_l_tck = 8; // max(4nCK, 4.9ns) Micron Datasheet
                timing->trrd_s_tck = 4; // max(4nCK, 2.5 ns) (JESD79-4A_r0 Table 131)
                timing->ddr4_tfaw_ps = 10000; // max(16nCK, 10ns) (JESD79-4A_r0 Table 131)
                break;
            default:
                SNPS_ERROR("Unknown speed grade, tck = %d", tck_ps);
                return DDRCTL_NOT_SUPPORTED;
            }
        }
    } else {
        SNPS_ERROR("Unknown bus width, bus_width = %d", SPD.sdram_width_bits);
        return DDRCTL_NOT_SUPPORTED;
    }
#else /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    timing->trrd_l_tck = (((SPD_aux.DDR4.tRRD_Lmin_ps * 1000) / tck_ps) + 974) / 1000;        //Rounding alg from JESD79-4B
    timing->trrd_s_tck = (((SPD_aux.DDR4.tRRD_Smin_ps * 1000) / tck_ps) + 974) / 1000;        //Rounding alg from JESD79-4B
    if (!IS_X16(n)) {
        timing->ddr4_trrd_dlr_tck = 4;
        timing->ddr4_tfaw_dlr_tck = 16;
    }
    timing->ddr4_tfaw_ps = SPD_aux.DDR4.tFAWmin_ps;
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */

    // Round up t_ccd_l if gd_en=1
    if (gd_en == 1 && (timing->ddr4_tccd_l_tck % 2) != 0)
        timing->ddr4_tccd_l_tck = timing->ddr4_tccd_l_tck + 1;
    // Round up t_ccd_dlr if gd_en=1
    if (gd_en == 1 && (timing->ddr4_tccd_dlr_tck % 2) != 0)
        timing->ddr4_tccd_dlr_tck = timing->ddr4_tccd_dlr_tck + 1;
    // for tccd_s, default to 4 clks
    timing->ddr4_tccd_s_tck = 4;

    timing->ddr4_tmrd_tck = 8 + timing->ddr4_tpl_tck;

    // Assign tcrc_alert value in ps
    timing->ddr4_tcrc_alert_ps = 13000;

    // for tmod, default TMOD_TCK is 24 clocks, so adjust the TMOD to this value
    timing->ddr4_tmod_ps = 24 * tck_ps + timing->ddr4_tpl_tck * tck_ps;    // max(24nCK, 15ns) (Micron Datasheet)

    // tISmin + tIHmin
    timing->ddr4_tmpx_s_tck = 2;    // tISmin + tIHmin (Micron Datasheet)
    // tIS(base)min = 115 - 60[ps], tIS(Vref)min = 215 - 150[ps], tIH(base)min = 140 - 85[ps], tIH(Vref)min = 215 - 150[ps]
    // Not clear how 2 was derived.

    // for tMPX_LH, default to 12000 ps
    timing->ddr4_tmpx_lh_ps = 12000;    // tMPX_LHmin = 12 [ns] (Micron Datasheet)

    // Set Valid Clock Requirement before Self Refresh Exit (SRX) or Power-Down Exit (PDX) or Reset Exit (tCKSRX)
    // tCKSRX = max(5nCK,10ns) based on JESD79-4D
    timing->ddr4_tcksrx_ps = max(5 * tck_ps, 10000);

    // for twr, default to 15000 ps
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
    timing->ddr4_twr_ps = ddr4_get_write_recovery_time(p, gd_en);
#else /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    timing->ddr4_twr_ps = SPD_aux.DDR4.tWRmin_ps;
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */

    // for trtp, it is related to write_recovery (twr) with fixed
    // relationship
    timing->ddr4_trtp_ps = DIV_2(timing->ddr4_twr_ps);

    // set the following in terms of ps
    timing->ddr4_tras_max_ps = 70200000;    // 9 * tREFI, tREFI = 7.8 [ns] (0 C <= T <= 85 C) (Micron Datasheet)

    timing->ddr4_trfc_min_fgr_ps = dwc_cinit_get_ddr4_trfc(sdram_capacity_mbits, fgr_mode);
    timing->ddr4_trfc_min_ps = dwc_cinit_get_ddr4_trfc(sdram_capacity_mbits, 0);
    timing->ddr4_trfc_min2_ps = dwc_cinit_get_ddr4_trfc(sdram_capacity_mbits, 1);
    timing->ddr4_trfc_min4_ps = dwc_cinit_get_ddr4_trfc(sdram_capacity_mbits, 2);
    timing->ddr4_trfc_dlr_fgr_ps = dwc_cinit_get_ddr4_trfc_dlr(sdram_capacity_mbits, fgr_mode);

    timing->ddr4_trfc_max_ps = 70200000;

    // used for post_mpsm_gap_x32
    //txmpdll = tXMP + tXSDLL
    //tXMP= TXS = max(5, tRFCmin) + 10 ns
    timing->ddr4_txmpdll_ps = (max(timing->ddr4_trfc_min_ps, 5 * tck_ps) + 10000) + (timing->ddr4_txsdll_tck * tck_ps);

    timing->trpa_ps = timing->trp_ps + tck_ps;

    // set the following dependent on other params
    // tREFI = 7.8us = 7800000ps in all speed grades
    // timing->ddr4_trefi_ps = (7800000/(SPD.tck_ps*32));
    // timing->ddr4_trefi_ps = (timing->ddr4_trefi_ps*SPD.tck_ps);
    // timing->ddr4_trefi_ps = int (timing->ddr4_trefi);
    timing->ddr4_trefi_ps = 7800000;

    // set the following in terms of clks
    timing->ddr4_tzqinit_tck = 1024;    // Micron Datasheet
    timing->ddr4_tzqoper_tck = 512;    // Micron Datasheet
    timing->ddr4_tzqcs_tck = 128;    // Micron Datasheet

    // set the tXP in terms of ps --- max(4nCK, 6ns) (Micron Datasheet)
    if (tck_ps > 1500)
        timing->ddr4_txp_ps = tck_ps * 4 + timing->ddr4_tpl_tck * tck_ps;
    else
        timing->ddr4_txp_ps = 6000 + timing->ddr4_tpl_tck * tck_ps;

    // set the tXPDLL in terms of ps
    timing->ddr4_txpdll_ps = 24000;    // Micron Model

    // set the CAS Latency and the CAS Write Latency (dependent on the speed grade/tck)
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
	dwc_ddr4_speed_grade_e sg = hdlr->spdData_m.ddr4_sg;
	uint32_t tck_avg_ps = hdlr->spdData_m.tck_ps[p];
	ddr_speedbins_ret_t op_status = cinit_ddr4_speedbins_set_cas_latencys(sg, tck_avg_ps, SELECT_LOWER_CL, dll_off_init, gd_en, timing);
	if(op_status != SPBINS_OK) {
		SNPS_ERROR("JEDEC DDR4 speedbins module was not able to set cas latencys! error code: %d", op_status);
        return DDRCTL_ERROR;
	}
#else /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    timing->ddr4_tcl_rdbi_tck = ddr4_get_cas_latency_rdbi(p, CFG, gd_en, dll_off_init, n);
    timing->ddr4_tcl_tck = ddr4_get_cas_latency(p, CFG, gd_en, dll_off_init, n);
#endif /*  DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    timing->ddr4_tcwl_1st_set_tck = ddr4_get_CWL_1st_set(p, CFG, dll_off_init);
    timing->ddr4_tcwl_2nd_set_tck = ddr4_get_CWL_2nd_set(p, CFG, dll_off_init);

    // geardown
    timing->ddr4_tsync_gear_tck = timing->ddr4_tmod_ps / tck_ps + 4;
    timing->ddr4_tcmd_gear_tck = timing->ddr4_tmod_ps / tck_ps;
    timing->ddr4_tgear_setup_tck = 2;
    timing->ddr4_tgear_hold_tck = 2;

    // for twr_crc_dm
    timing->ddr4_twr_crc_dm_tck = timing->ddr4_wcl_tck;    // The definition of this parameter is tWR + WCL,
    // where WCL=max(NnCK, 3.75ns) (N=4 for 1600, N=5 for higher speeds (Micron Datasheet))
    // But, in ddrc_cfg.sv, this is treated as only WCL portion.

    // CA parity timing
    timing->ddr4_tpar_unknown_ps = timing->ddr4_tpl_tck * tck_ps;    // PL (Micron Datasheet)
    timing->ddr4_tpar_alert_on_ps = (timing->ddr4_tpl_tck * tck_ps) + 6000;    // PL + 6ns (Micron Datasheet)

    // Update timing parameters if DLL-off mode is enabled during SDRAM initialization.
    if (dll_off_init == 1) {
        timing->trrd_l_tck = 4;
        timing->trrd_s_tck = 4;
        timing->ddr4_trrd_dlr_tck = 4;
        timing->ddr4_twtr_l_tck = 4;
        timing->ddr4_twtr_s_tck = 2;
        timing->ddr4_tcke_ps = tck_ps * 3;
        timing->ddr4_trtp_ps = tck_ps * 4;
    }
    // Micron model's tDQSCK (DLL-off) value is 5.8ns.
    timing->ddr4_tdqsck_dll_off_ps = 5800;    // Micron Model

    timing->ddr4_tstab_ps = 5000000;    // JEDEC value 5us

    timing->ddr4_rcd_tpdm_rd_ps = 1370 + CEIL(tck_ps, 4);
    timing->ddr4_rcd_tpdm_wr_ps = 1370 + CEIL(tck_ps, 4);

    return DDRCTL_SUCCESS;
}


/**
 * @brief Get the Lowest CAS latency supported of the configured tCK
 *
 * @param spd_timming_ptr   pointer to the timming structure
 * @param tck_ps            Application tCk in picoseconds
 * @return uint32_t         CAS Latence value
 */
uint32_t ddr4_get_spd_cas_latency(auxDDR4_t *spd_timming_ptr, uint32_t tck_ps)
{
    uint32_t t_aa_in_nck;
    uint32_t cas_latency;

    // CAS latency calculation based On JESD79-4C chapter 10.1 note 2:
    // “NOTE 2 tCK(avg).MIN limits: all possible intermediate frequencies may not be guaranteed. [...]
    // CL in clock cycle is calculated from tAA following rounding algorithm defined in Section 13.5.”

    // tAA(min) calculation to nCk based on JEDEC Standard No. 21-C, Rel 30 chapter 8.1.18 and JESD79-4C Section 13.5
    t_aa_in_nck = cinit_round_down_only_int_ddr4(spd_timming_ptr->tAAmin_ps, tck_ps);

    // Bitmap decode Based on JEDEC Standard No. 21-C, Release 30 chapter 8.1.21
    // NOTE: In this chapter we find also: "CAS Latency Mask may cover either non-DBI mode or both DBI and non-DBI
    //       modes of operation; this is vendor specific."
    //       This implementation assumes that CAS Latency Supported covers both modes of operation. Since this is
    //       vendor specific, this my produce unsupported CAS latency value for some vendors.

    for (cas_latency = CAS_LATENCY_DDR4_MIN; cas_latency <= CAS_LATENCY_DDR4_MAX; cas_latency++) {
        // Check if the bit is set for bitmap index i
        if (SNPS_GET_BIT(spd_timming_ptr->cas_latency_supported, cas_latency) == 1) {
            if (t_aa_in_nck <= cas_latency) { // The CAS latency must be at least equal to the tAA
                return cas_latency;
            }
        }
    }
    SNPS_ERROR("No CAS Latency found for tAA(min) nCK = %d and BITMAP 0x%08x",
                t_aa_in_nck, spd_timming_ptr->cas_latency_supported);
    dwc_ddrctl_cinit_exit(1);
    return 0;
}

/**
 * @brief Get the Lowest CAS latency supported of the configured tCK
 *
 * @param spd_timming_ptr   pointer to the timming structure
 * @param tck_ps            Application tCk in picoseconds
 * @return uint32_t         CAS Latence value
 */
uint32_t ddr4_get_spd_cas_latency_rdbi(auxDDR4_t *spd_timming_ptr, uint32_t tck_ps)
{
    uint8_t rdbi_add_factor;
    uint32_t cas_latency = ddr4_get_spd_cas_latency(spd_timming_ptr, tck_ps);

    if ((cas_latency >= 9) && (cas_latency < 15)) {
        rdbi_add_factor = 2;
    } else if ((cas_latency >= 15) && (cas_latency < 20)) {
        rdbi_add_factor = 3;
    } else if ((cas_latency >= 20) && (cas_latency < 24)) {
        rdbi_add_factor = 4;
    } else {
        SNPS_ERROR("Unsupported CAS Latency (%d) to calculate CAS Latency read DBI", cas_latency);
        dwc_ddrctl_cinit_exit(1);
    }
    return cas_latency + rdbi_add_factor;
}

// --------------------------------------------------------------------------
// Name        : ddr4_get_cas_latency()
// Description : depending on the speed grade/tck, pick a CAS latency
// Params      : pstate, SubsysHdlr_t* hdlr, gd_en, dll_off_mode
// Returns     : CAS Latency value
// --------------------------------------------------------------------------
uint32_t ddr4_get_cas_latency(uint32_t pstate, SubsysHdlr_t *hdlr, bool geardown_en, bool dll_off_mode, uint32_t n)
{
    SNPS_TRACE("Entering");
    uint32_t cas_latency;
    uint32_t tck_ps_p = SPD.tck_ps[pstate];

    if (dll_off_mode == 1) {
        // CL must be set to 10 with DLL-off mode
        cas_latency = 10;
    } else {
        cas_latency = ddr4_get_spd_cas_latency(&SPD_aux.DDR4, tck_ps_p);
    }

    if (geardown_en == 1 && (cas_latency % 2) != 0)
        cas_latency += 1;

    SNPS_TRACE("Leaving");
    return cas_latency;
}

//--------------------------------------------------------------------------
// Name        : ddr4_get_CWL_1st_set
// Description : depending on the speed grade/tck and CAS Latency, pick the lower CAS Write Latency value
// Params      : pstate, SubsysHdlr_t* hdlr, dll_off_init
// Returns     : lower possible CAS Write Latency value
//--------------------------------------------------------------------------
uint32_t ddr4_get_CWL_1st_set(uint32_t pstate, SubsysHdlr_t *hdlr, bool dll_off_init)
{
    SNPS_TRACE("Entering");
    uint32_t cas_write_latency_1st_set = 0;
    uint32_t tck_ps;

    if (dll_off_init) {
        cas_write_latency_1st_set = 9;    //CWL must be set to 9 with DLL-off mode
    } else {
        tck_ps = SPD.tck_ps[pstate];
        if (RANGE(tck_ps, 1250, 1499)) // 1600 (1250ps)
            cas_write_latency_1st_set = 9;
        else if (RANGE(tck_ps, 1071, 1249)) // 1866(1071ps)
            cas_write_latency_1st_set = 10;
        else if (RANGE(tck_ps, 938, 1070)) // 2133(938ps)
            cas_write_latency_1st_set = 11;
        else if (RANGE(tck_ps, 833, 937)) // 2400(833ps)
            cas_write_latency_1st_set = 12;
        else if (RANGE(tck_ps, 750, 832)) // 2666(750ps)
            cas_write_latency_1st_set = 14;
        else if (RANGE(tck_ps, 682, 749)) // 2933(682ps)
            cas_write_latency_1st_set = 16;
        else if (RANGE(tck_ps, 625, 681)) // 3200(625ps)
            cas_write_latency_1st_set = 16;
        else {
            dwc_ddrctl_cinit_exit(1);
            SNPS_ERROR("Unknown tck_ps[%u] = %u", pstate, tck_ps);
        }
    }

    SNPS_TRACE("Leaving");
    return cas_write_latency_1st_set;
}

// --------------------------------------------------------------------------
// Name        : ddr4_get_CWL_2nd_set
// Description : depending on the speed grade/tck and CAS Latency, pick a the upper CAS Write Latency value
// Params      : pstate, SubsysHdlr_t* hdlr, dll_off_init
// Returns     : upper possible CAS Write Latency value
// --------------------------------------------------------------------------
uint32_t ddr4_get_CWL_2nd_set(uint32_t pstate, SubsysHdlr_t *hdlr, bool dll_off_init)
{
    SNPS_TRACE("Entering");
    uint32_t cas_write_latency_2nd_set = 0;
    uint32_t tck_ps;

    if (dll_off_init) {
        cas_write_latency_2nd_set = 9;    //CWL must be set to 9 with DLL-off mode
    } else {
        tck_ps = SPD.tck_ps[pstate];
        if (RANGE(tck_ps, 1250, 1499)) // 1600 (1250ps)
            cas_write_latency_2nd_set = 11;
        else if (RANGE(tck_ps, 1071, 1249)) // 1866(1071ps)
            cas_write_latency_2nd_set = 12;
        else if (RANGE(tck_ps, 938, 1070)) // 2133(938ps)
            cas_write_latency_2nd_set = 14;
        else if (RANGE(tck_ps, 833, 937)) // 2400(833ps)
            cas_write_latency_2nd_set = 16;
        else if (RANGE(tck_ps, 750, 832)) // 2666(750ps)
            cas_write_latency_2nd_set = 18;
        else if (RANGE(tck_ps, 682, 749)) // 2933(682ps)
            cas_write_latency_2nd_set = 20;
        else if (RANGE(tck_ps, 625, 681)) // 3200(625ps)
            cas_write_latency_2nd_set = 20;
        else {
            SNPS_ERROR("Unknown tck_ps[%u] = %u", pstate, tck_ps);
            dwc_ddrctl_cinit_exit(1);
        }
    }

    SNPS_TRACE("Leaving");
    return cas_write_latency_2nd_set;
}

// --------------------------------------------------------------------------
// Name        : ddr4_get_cas_latency_rdbi()
// Description : depending on the speed grade/tck, pick a CAS latency
// Params      :
// Returns     : CAS Latency value with Read DBI
// --------------------------------------------------------------------------
uint32_t ddr4_get_cas_latency_rdbi(uint32_t pstate, SubsysHdlr_t *hdlr, bool gd_en, bool dll_off_mode, uint32_t n)
{
    SNPS_TRACE("Entering");
    uint32_t cas_latency_rdbi;
    uint32_t tck_ps_p = SPD.tck_ps[pstate];

    if (dll_off_mode == 1) {
        cas_latency_rdbi = 10;    // CL must be set to 10 with DLL-off mode (CL_DBI will be 10 as well)
    } else {
    	cas_latency_rdbi = ddr4_get_spd_cas_latency_rdbi(&SPD_aux.DDR4, tck_ps_p);
    }

    if (gd_en == 1 && (cas_latency_rdbi % 2) != 0)
        cas_latency_rdbi +=  1;
    // return the CAS Latency with Read DBI

    SNPS_TRACE("Leaving");
    return cas_latency_rdbi;
}

//--------------------------------------------------------------------------
// Name        : ddr4_get_write_recovery_time
// Description : depending on the speed grade and if gd_en or not, pick up the write recovery time
// Params      : pstate, gd_en
// Returns     : write recovery time
//--------------------------------------------------------------------------
uint32_t ddr4_get_write_recovery_time(uint32_t pstate, bool gd_en)
{
    uint32_t tck_ps = SPD.tck_ps[pstate];

    uint32_t l_ddr4_wr_ps;

    l_ddr4_wr_ps  = 15000;

    // gd_en =1 for tck_ps <= 750
    // so is for:
    // tck_ps = 750 tWR=20 tRTP=10
    // tck_ps = 682 tWR=22 tRTP=11
    // tck_ps = 625 tWR=24 tRTP=12
    // but tWR and TRTP need to be even for Geardown, so need
    // to adjust tWR for tck_ps=682 to higher value
    if (gd_en == 1 && tck_ps == 682)
          l_ddr4_wr_ps = 24 * tck_ps; // 24*682
    return l_ddr4_wr_ps;
}

// --------------------------------------------------------------------------
// Name        : ddr5::set_clk_speed()
// Description : set the value in the hdlr->timingParams_m structure
// Params      : hdlr
// Returns     : none
// --------------------------------------------------------------------------
void ddr5_set_clk_speed(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n)
{
    SNPS_TRACE("Entering");
    ddrTimingParameters_t *timing = &CFG->timingParams_m[p][n];

#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
	ddrctl_error_t rslt;
	rslt = cinit_ddr5_speed_bin_set_clk_timings(hdlr->spdData_m.ddr5_jedec_spec, SPD.ddr5_speed_bin[n], timing);
	if(rslt != DDRCTL_SUCCESS) {
		SNPS_ERROR("JEDEC DDR5 speedbins module was not able to set clk timings! error code: %d", rslt);
        dwc_ddrctl_cinit_exit(1);
	}
	//twr is not specified in speedbin tables
	//twr = 30ns for all the speedgrades
	timing->ddr5_twr_ps = 30000;
#else /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    timing->sg_tck_ps = SPD_aux.DDR5.tCKAVGmin;
    timing->trcd_ps = SPD_aux.DDR5.tRCDmin_ps;
    timing->trp_ps = SPD_aux.DDR5.tRPmin_ps;
    timing->ddr5_tras_min_ps = SPD_aux.DDR5.tRASmin_ps;
    timing->ddr5_twr_ps = SPD_aux.DDR5.tWRmin_ps;
    timing->trc_ps = SPD_aux.DDR5.tRCmin_ps;
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */

    SNPS_TRACE("Leaving");
}

/**
 * @brief method to setup timing parameter for DDR5
 *  @note there are JEDEC timing values: COMMITTEE LETTER BALLOT Item #
 *   Alignment to DDR5 FULL Spec Draft Rev1.90
 * @note TCK is rounded down and JEDEC formula =  roundup (Timing * 0.997/ (round down tCK))
 * tRFC1 and tRFC2 0.999 is used as multiplier
 *
 */
void ddr5_set_default_timing(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n)
{
    SNPS_TRACE("Entering");
    uint32_t l_tccd_l_wr;

	ddrTimingParameters_t *timing = &CFG->timingParams_m[p][n];
	ddr5_scaling_control_t *scaling = &CFG->ddr5_scaling_control;

    uint32_t tck_ps = hdlr->spdData_m.tck_ps[p];
	uint32_t fgr_mode = CFG->memCtrlr_m.ddr5_mr[p].mr4.refresh_trfc_mode;
	uint32_t sdram_capacity_mbits = SPD.sdram_capacity_mbits[n];
    dwc_ddr5_speed_grade_t speed_grade;

    speed_grade = cinit_ddr5_get_speedgrade_from_tck_avg_min(tck_ps);

    if (tck_ps != timing->sg_tck_ps) {
        SNPS_LOG("tck_ps (%u ps) selected is not min JEDEC TCK value(%u)", tck_ps, timing->sg_tck_ps);
    }

    timing->burst_length = 16;  // BL 16 - Length value supported for DDR5

    timing->ddr5_trefi1_ps = 3900000;
    timing->ddr5_trefi2_ps = 1950000;
    timing->ddr5_tinit3_us = 4000;
    timing->ddr5_tinit4_us = 2;

    if (scaling->ddr5_trefi1_ps_scale_en) {
        timing->ddr5_trefi1_ps = scaling->ddr5_trefi1_ps_scale_val;
        timing->ddr5_trefi2_ps = DIV_2(scaling->ddr5_trefi1_ps_scale_val);
    } else {
        timing->ddr5_trefi1_ps = 3900000;
        timing->ddr5_trefi2_ps = 1950000;
    }

    // note this is not a JEDEC value
    // the variable here is used to align setting in VIP with setting in
    // PHYINIT
    // The value is chosen so as not to overflow the dqs counter if large
    // MR45 interval is picked.
    timing->ddr5_tdqs2dq_ps = SPD.trx_dqs2dq;

    SNPS_LOG("sdram_capacity_mbits(%u) = %u", n, sdram_capacity_mbits);

    timing->ddr5_trfc_fgr_ps = dwc_cinit_get_ddr5_trfc(sdram_capacity_mbits, fgr_mode);
    timing->ddr5_trfc1_ps = dwc_cinit_get_ddr5_trfc(sdram_capacity_mbits, 0);
    timing->ddr5_trfc2_ps = dwc_cinit_get_ddr5_trfc(sdram_capacity_mbits, 1);
    timing->ddr5_trfc_dlr_fgr_ps = dwc_cinit_get_ddr5_trfc_dlr(sdram_capacity_mbits, fgr_mode);
    if (IS_DENS_8GBIT(n)) {
        timing->ddr5_trfcsb_ps = 115000;
        timing->ddr5_trefsbrd_ps = 30000;
        timing->ddr5_trfcsb_dlr_ps = 39000;
        timing->ddr5_trefsbrd_dlr_ps = 15000;
    } else if (IS_DENS_16GBIT(n)) {
        timing->ddr5_trfcsb_ps = 130000;
        timing->ddr5_trefsbrd_ps = 30000;
        timing->ddr5_trfcsb_dlr_ps = 44000;
        timing->ddr5_trefsbrd_dlr_ps = 15000;
    } else if (IS_DENS_24GBIT(n)) {
        timing->ddr5_trfcsb_ps = 195000;
        timing->ddr5_trefsbrd_ps = 30000;
        timing->ddr5_trfcsb_dlr_ps = 65000;
        timing->ddr5_trefsbrd_dlr_ps = 15000;
    } else if (IS_DENS_32GBIT(n)) {
        timing->ddr5_trfcsb_ps = 195000;
        timing->ddr5_trefsbrd_ps = 30000;
        timing->ddr5_trfcsb_dlr_ps = 65000;
        timing->ddr5_trefsbrd_dlr_ps = 15000;
    } else if (IS_DENS_64GBIT(n)) {
        timing->ddr5_trfcsb_ps = 195000;
        timing->ddr5_trefsbrd_ps = 30000;
        timing->ddr5_trfcsb_dlr_ps = 65000;
        timing->ddr5_trefsbrd_dlr_ps = 15000;
    }
  // Scale trfc if trefi is scaled
  if (scaling->ddr5_trefi1_ps_scale_en) {
    if(fgr_mode)  {
      timing->ddr5_trfc_fgr_ps = scaling->ddr5_trfc2_ps_scale_val;
      timing->ddr5_trfc_dlr_fgr_ps = CEIL((scaling->ddr5_trfc2_ps_scale_val)/1000, 3) * 1000;
    }    else {
      timing->ddr5_trfc_fgr_ps = scaling->ddr5_trfc1_ps_scale_val;
      timing->ddr5_trfc_dlr_fgr_ps = CEIL((scaling->ddr5_trfc1_ps_scale_val)/1000, 3) * 1000;
    }
    timing->ddr5_trfc1_ps = scaling->ddr5_trfc1_ps_scale_val;
    timing->ddr5_trfc2_ps = scaling->ddr5_trfc2_ps_scale_val;
    timing->ddr5_trfcsb_ps = scaling->ddr5_trfcsb_ps_scale_val;
    timing->ddr5_trefsbrd_ps = 30000;
    timing->ddr5_trfcsb_dlr_ps = scaling->ddr5_trfcsb_dlr_ps_scale_val;
    timing->ddr5_trefsbrd_dlr_ps = 15000;
  }

	// zqcal
	timing->ddr5_tzqcal_ps = 1000000; // 1us
	timing->ddr5_tzqlat_ps = max(30000, 8 * tck_ps);
	// Power down
	timing->ddr5_tcpded_ps = max(5000, 8 * tck_ps);
	timing->ddr5_tpd_ps = max(7500, 8 * tck_ps);
	timing->ddr5_txp_ps = max(7500, 8 * tck_ps);
	timing->ddr5_tactpden_tck = 2;
	timing->ddr5_tprpden_tck = 2;
	timing->ddr5_trefpden_tck = 2;
	// Self-refresh
	timing->ddr5_tcsl_ps = 10000;	//10ns
	timing->ddr5_tcsh_srexit_ps = 13000;	//13ns
	timing->ddr5_tcsl_srexit_tck = 3;
	timing->ddr5_tcksrx_ps = max(3500, 8 * tck_ps);	//3.5ns
	timing->ddr5_tcklcs_tck = CEIL(timing->ddr5_tcpded_ps, tck_ps) + 1;
	// tCASRX = 0(Min) defined in JEDEC
	timing->ddr5_tcasrx_ps = 0;
	timing->ddr5_txs_dll_ps = 0;	//TBD
	// mode register
	timing->ddr5_tmrr_tck = max(cinit_round_down_only_int_ddr5(14000, tck_ps), 16);
	timing->ddr5_tmrr_p_tck = 8;
	timing->ddr5_tmrw_tck = max(cinit_round_down_only_int_ddr5(5000, tck_ps), 8);
	timing->ddr5_tmrd_tck = max(cinit_round_down_only_int_ddr5(14000, tck_ps), 16);
	// MPSM
	timing->ddr5_tmpsmx_ps = max(14000, 16 * tck_ps);
	timing->ddr5_tmpdpdact_ps = 0;	//TBD
	// MPC
	timing->ddr5_tmpc_delay_tck = timing->ddr5_tmrd_tck;
	timing->ddr5_tmc_mpc_setup_tck = 3;
	timing->ddr5_tmc_mpc_hold_tck = 3;
	timing->ddr5_tmpc_cs_min_tck = 4;	//JEDEC 4 tck
	timing->ddr5_tmpc_cs_max_tck = 8;
	// PDA
	timing->ddr5_tpda_latch_min_ps = 0;	//TBD
	timing->ddr5_tpda_dqs_delay_min_ps = 5000;
	timing->ddr5_tpda_dqs_delay_max_ps = 18000;
	timing->ddr5_tpda_delay_ps = timing->ddr5_tpda_dqs_delay_max_ps + DIV_2(1000 * timing->burst_length) + 19000;
	timing->ddr5_tpda_s_tck = 3;
	timing->ddr5_tpda_h_tck = 3;
	timing->ddr5_tccd_l_tck = max(cinit_round_down_only_int_ddr5(5000, tck_ps), 8);

	l_tccd_l_wr = max(20000 / tck_ps, 32);

	timing->ddr5_tccd_l_wr_tck = (l_tccd_l_wr % 4) ? (l_tccd_l_wr + 4 - l_tccd_l_wr % 4) : l_tccd_l_wr;
	timing->trrd_s_tck = 8;
	timing->trrd_l_tck = max(cinit_round_down_only_int_ddr5(5000, tck_ps), 8);
	timing->ddr5_twtr_s_tck = max(cinit_round_down_only_int_ddr5(2500, tck_ps), 4);
	timing->ddr5_twtr_l_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 16);
	timing->ddr5_trtp_ps = max(7500, 12 * tck_ps);
	if(tck_ps <= 263) {
		timing->ddr5_tppd_tck = 4;
	} else {
		timing->ddr5_tppd_tck = 2;
	}
    timing->ddr5_tccd_s_tck = 8;

	// bug10387
	// For x4 device, tCCD_L_WR is used to program reg_tccd_w2 because write for X4 is always RMW in dram internal
	if (IS_X4(n))
		timing->ddr5_tccd_l_wr2_tck = timing->ddr5_tccd_l_wr_tck;
	else
		timing->ddr5_tccd_l_wr2_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 16);

	if(CID_WIDTH(n) == 0) {
		switch (speed_grade) {
		case DWC_DDR5_SG_3200:
		case DWC_DDR5_SG_3600:
		case DWC_DDR5_SG_4000:
		case DWC_DDR5_SG_4400:
		case DWC_DDR5_SG_4800:
		case DWC_DDR5_SG_5200:
		case DWC_DDR5_SG_5600:
		case DWC_DDR5_SG_6000:
		case DWC_DDR5_SG_6400:
			timing->ddr5_tccd_m_tck = max(cinit_round_down_only_int_ddr5(5000, tck_ps), 8);
			timing->ddr5_tccd_m_wr_tck = timing->ddr5_tccd_l_wr_tck;
			timing->ddr5_twtr_m_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 16);
			break;
		case DWC_DDR5_SG_6800:
			timing->ddr5_tccd_m_tck = max(cinit_round_down_only_int_ddr5(4705, tck_ps), 8);
			timing->ddr5_tccd_m_wr_tck = max(cinit_round_down_only_int_ddr5(18823, tck_ps), 32);
			timing->ddr5_twtr_m_tck = max(cinit_round_down_only_int_ddr5(9411, tck_ps), 16);
			break;
		case DWC_DDR5_SG_7200:
			timing->ddr5_tccd_m_tck = max(cinit_round_down_only_int_ddr5(4444, tck_ps), 8);
			timing->ddr5_tccd_m_wr_tck =  max(cinit_round_down_only_int_ddr5(17777, tck_ps), 32);
			timing->ddr5_twtr_m_tck = max(cinit_round_down_only_int_ddr5(8888, tck_ps), 16);
			break;
		case DWC_DDR5_SG_7600:
			timing->ddr5_tccd_m_tck = max(cinit_round_down_only_int_ddr5(4210, tck_ps), 8);
			timing->ddr5_tccd_m_wr_tck =  max(cinit_round_down_only_int_ddr5(16842, tck_ps), 32);
			timing->ddr5_twtr_m_tck = max(cinit_round_down_only_int_ddr5(8421, tck_ps), 16);
			break;
		case DWC_DDR5_SG_8000:
			timing->ddr5_tccd_m_tck = max(cinit_round_down_only_int_ddr5(4000, tck_ps), 8);
			timing->ddr5_tccd_m_wr_tck =  max(cinit_round_down_only_int_ddr5(16000, tck_ps), 32);
			timing->ddr5_twtr_m_tck = max(cinit_round_down_only_int_ddr5(8000, tck_ps), 16);
			break;
		case DWC_DDR5_SG_8400:
			timing->ddr5_tccd_m_tck = max(cinit_round_down_only_int_ddr5(4000, tck_ps), 8);
			timing->ddr5_tccd_m_wr_tck =  max(cinit_round_down_only_int_ddr5(15238, tck_ps), 32);
			timing->ddr5_twtr_m_tck = max(cinit_round_down_only_int_ddr5(7619, tck_ps), 16);
			break;
      case DWC_DDR5_SG_8800:
			timing->ddr5_tccd_m_tck = max(cinit_round_down_only_int_ddr5(3863, tck_ps), 8);
			timing->ddr5_tccd_m_wr_tck =  max(cinit_round_down_only_int_ddr5(14545, tck_ps), 32);
			timing->ddr5_twtr_m_tck = max(cinit_round_down_only_int_ddr5(7272, tck_ps), 16);
			break;
		default:
			SNPS_ERROR("Unknown speedbin = %u", speed_grade);
            dwc_ddrctl_cinit_exit(1);
			break;
		}
	} else {
		// JEDEC REV189 does not defines timing parameter value of tCCD_M, tCCD_M_WR and tWTR_M
		// for 3DS speedbin higher than 6400,  take number from 6400 by compromise
		timing->ddr5_tccd_m_tck = max(cinit_round_down_only_int_ddr5(5000, tck_ps), 8);
		timing->ddr5_tccd_m_wr_tck = timing->ddr5_tccd_l_wr_tck;
		timing->ddr5_twtr_m_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 16);
	}

	// tfaw_dlr/tfaw_slr
	if (CID_WIDTH(n) > 0) {	/* 3DS memories */
		switch (speed_grade) {
        case DWC_DDR5_SG_3200:
			timing->ddr5_tfaw_slr_tck = max(cinit_round_down_only_int_ddr5(20000, tck_ps), 32);
			timing->ddr5_trrd_dlr_tck = max(cinit_round_down_only_int_ddr5(2500, tck_ps), 4);
			timing->ddr5_tfaw_dlr_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 16);
			timing->ddr5_tccd_dlr_tck = max(cinit_round_down_only_int_ddr5(5000, tck_ps), 8); // tCCD_dlr
			timing->ddr5_tccd_wr_dlr_tck = max(cinit_round_down_only_int_ddr5(5000, tck_ps), 8); // tCCD_WR_dlr
			break;
        case DWC_DDR5_SG_3600:
			timing->ddr5_tfaw_slr_tck = max(cinit_round_down_only_int_ddr5(17777, tck_ps), 32);
			timing->ddr5_trrd_dlr_tck = max(cinit_round_down_only_int_ddr5(2222, tck_ps), 4);
			timing->ddr5_tfaw_dlr_tck = max(cinit_round_down_only_int_ddr5(8888, tck_ps), 16);
			timing->ddr5_tccd_dlr_tck = max(cinit_round_down_only_int_ddr5(4444, tck_ps), 8); // tCCD_dlr
			timing->ddr5_tccd_wr_dlr_tck = max(cinit_round_down_only_int_ddr5(4444, tck_ps), 8); // tCCD_WR_dlr
			break;
        case DWC_DDR5_SG_4000:
			timing->ddr5_tfaw_slr_tck = max(cinit_round_down_only_int_ddr5(16000, tck_ps), 32);
			timing->ddr5_trrd_dlr_tck = max(cinit_round_down_only_int_ddr5(2000, tck_ps), 4);
			timing->ddr5_tfaw_dlr_tck = max(cinit_round_down_only_int_ddr5(8000, tck_ps), 16);
			timing->ddr5_tccd_dlr_tck = max(cinit_round_down_only_int_ddr5(4000, tck_ps), 8); // tCCD_dlr
			timing->ddr5_tccd_wr_dlr_tck = max(cinit_round_down_only_int_ddr5(4000, tck_ps), 8); // tCCD_WR_dlr
			break;
        case DWC_DDR5_SG_4400:
			timing->ddr5_tfaw_slr_tck = max(cinit_round_down_only_int_ddr5(14545, tck_ps), 32);
			timing->ddr5_trrd_dlr_tck = max(cinit_round_down_only_int_ddr5(1818, tck_ps), 4);
			timing->ddr5_tfaw_dlr_tck = max(cinit_round_down_only_int_ddr5(7272, tck_ps), 16);
			timing->ddr5_tccd_dlr_tck = max(cinit_round_down_only_int_ddr5(3636, tck_ps), 8); // tCCD_dlr
			timing->ddr5_tccd_wr_dlr_tck = max(cinit_round_down_only_int_ddr5(3636, tck_ps), 8); // tCCD_WR_dlr
			break;
        case DWC_DDR5_SG_4800:
			timing->ddr5_tfaw_slr_tck = max(cinit_round_down_only_int_ddr5(13333, tck_ps), 32);
			timing->ddr5_trrd_dlr_tck = max(cinit_round_down_only_int_ddr5(1666, tck_ps), 4);
			timing->ddr5_tfaw_dlr_tck = max(cinit_round_down_only_int_ddr5(6666, tck_ps), 16);
			timing->ddr5_tccd_dlr_tck = max(cinit_round_down_only_int_ddr5(3333, tck_ps), 8); // tCCD_dlr
			timing->ddr5_tccd_wr_dlr_tck = max(cinit_round_down_only_int_ddr5(3333, tck_ps), 8); // tCCD_WR_dlr
			break;
        case DWC_DDR5_SG_5200:
			timing->ddr5_tfaw_slr_tck = max(cinit_round_down_only_int_ddr5(12307, tck_ps), 32);
			timing->ddr5_trrd_dlr_tck = max(cinit_round_down_only_int_ddr5(1666, tck_ps), 4);
			timing->ddr5_tfaw_dlr_tck = max(cinit_round_down_only_int_ddr5(6666, tck_ps), 16);
			timing->ddr5_tccd_dlr_tck = max(cinit_round_down_only_int_ddr5(3333, tck_ps), 8); // tCCD_dlr
			timing->ddr5_tccd_wr_dlr_tck = max(cinit_round_down_only_int_ddr5(3333, tck_ps), 8); // tCCD_WR_dlr
			break;
        case DWC_DDR5_SG_5600:
			timing->ddr5_tfaw_slr_tck = max(cinit_round_down_only_int_ddr5(11428, tck_ps), 32);
			timing->ddr5_trrd_dlr_tck = max(cinit_round_down_only_int_ddr5(1666, tck_ps), 4);
			timing->ddr5_tfaw_dlr_tck = max(cinit_round_down_only_int_ddr5(6666, tck_ps), 16);
			timing->ddr5_tccd_dlr_tck = max(cinit_round_down_only_int_ddr5(3214, tck_ps), 8); // tCCD_dlr
			timing->ddr5_tccd_wr_dlr_tck = max(cinit_round_down_only_int_ddr5(3214, tck_ps), 8); // tCCD_WR_dlr
			break;
        case DWC_DDR5_SG_6000:
			timing->ddr5_tfaw_slr_tck = max(cinit_round_down_only_int_ddr5(10666, tck_ps), 32);
			timing->ddr5_trrd_dlr_tck = max(cinit_round_down_only_int_ddr5(1666, tck_ps), 4);
			timing->ddr5_tfaw_dlr_tck = max(cinit_round_down_only_int_ddr5(6666, tck_ps), 16);
			timing->ddr5_tccd_dlr_tck = max(cinit_round_down_only_int_ddr5(3214, tck_ps), 8); // tCCD_dlr
			timing->ddr5_tccd_wr_dlr_tck = max(cinit_round_down_only_int_ddr5(3214, tck_ps), 8); // tCCD_WR_dlr
			break;
		case DWC_DDR5_SG_6400:
		// JEDEC REV189 does not defines timing parameter value of tFAW_slr, tRRD_dlr, tFAW_dlr and tCCD_S
		// for speedbin higher than 6400,  take number from 6400 by compromise
		case DWC_DDR5_SG_6800:
		case DWC_DDR5_SG_7200:
		case DWC_DDR5_SG_7600:
		case DWC_DDR5_SG_8000:
		case DWC_DDR5_SG_8400:
      // timing paramters are not defined for DDR-8800,so using the same value with 8400.
      case DWC_DDR5_SG_8800:
			timing->ddr5_tfaw_slr_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 32);
			timing->ddr5_trrd_dlr_tck = max(cinit_round_down_only_int_ddr5(1666, tck_ps), 4);
			timing->ddr5_tfaw_dlr_tck = max(cinit_round_down_only_int_ddr5(6666, tck_ps), 16);
			timing->ddr5_tccd_dlr_tck = max(cinit_round_down_only_int_ddr5(3125, tck_ps), 8); // tCCD_dlr
			timing->ddr5_tccd_wr_dlr_tck = max(cinit_round_down_only_int_ddr5(3125, tck_ps), 8); // tCCD_WR_dlr
			break;
      default:
			SNPS_ERROR("Unknown speed_grade = %u", speed_grade);
            dwc_ddrctl_cinit_exit(1);
			break;
		}
	} else { /* Non 3Ds memories */
		timing->ddr5_tfaw_dlr_tck = 16;

        switch (speed_grade) {
        case DWC_DDR5_SG_3200:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(25000, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(20000, tck_ps), 32);
            }
            break;
        case DWC_DDR5_SG_3600:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(22220, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(1777, tck_ps), 32);
            }
            break;
        case DWC_DDR5_SG_4000:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(20000, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(16000, tck_ps), 32);
            }
            break;
        case DWC_DDR5_SG_4400:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(18181, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(14545, tck_ps), 32);
            }
            break;
        case DWC_DDR5_SG_4800:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(16666, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(13333, tck_ps), 32);
            }
            break;
        case DWC_DDR5_SG_5200:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(15384, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(12307, tck_ps), 32);
            }
            break;
        case DWC_DDR5_SG_5600:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(14285, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(11428, tck_ps), 32);
            }
            break;
        case DWC_DDR5_SG_6000:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(13333, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(10666, tck_ps), 32);
            }
            break;
        case DWC_DDR5_SG_6400:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(12500, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 32);
            }
            break;
		case DWC_DDR5_SG_6800:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(11764, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(9411, tck_ps), 32);
            }
            break;
		case DWC_DDR5_SG_7200:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(11111, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(8888, tck_ps), 32);
            }
            break;
		case DWC_DDR5_SG_7600:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(10526, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(8421, tck_ps), 32);
            }
            break;
		case DWC_DDR5_SG_8000:
            if(IS_X16(n)) {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(8000, tck_ps), 32);
            }
            break;
		case DWC_DDR5_SG_8400:
      case DWC_DDR5_SG_8800:    //timing paramters are not defined for DDR-8800,so using the same value with 8400.
            if(IS_X16(n)) {
				timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(9523, tck_ps), 40);
            } else {
                timing->ddr5_tfaw_tck = max(cinit_round_down_only_int_ddr5(7619, tck_ps), 32);
            }
            break;
      default:
            SNPS_ERROR("Unknown speed_grade = %u", speed_grade);
            dwc_ddrctl_cinit_exit(1);
            break;
        }
	}

    // Get cas_latency and calculate cwl_latency.
    timing->ddr5_tcl_tck = ddr5_get_cas_latency(hdlr, hdlr->spdData_m.ddr5_speed_bin[n], tck_ps);
    timing->ddr5_tcwl_tck = timing->ddr5_tcl_tck - 2;

    // Power down
    timing->ddr5_trdpden_tck = timing->ddr5_tcl_tck + DIV_2(timing->burst_length) + 1;
    timing->ddr5_twrpden_tck = timing->ddr5_tcwl_tck + DIV_2(timing->burst_length) + CEIL(timing->ddr5_twr_ps, tck_ps) + 1;
    timing->ddr5_twrapden_tck = timing->ddr5_tcwl_tck + DIV_2(timing->burst_length) + CEIL(timing->ddr5_twr_ps, tck_ps) + 1;
    timing->ddr5_tmrrpden_tck = timing->ddr5_tcl_tck + 8 + 1;
    timing->ddr5_tmrwpden_tck = timing->ddr5_tmrd_tck;
    timing->ddr5_tmpcpden_tck = 0;    //TBD

	if (CID_WIDTH(n) == 0) {
		timing->ddr5_txs_ps = timing->ddr5_trfc1_ps;
	} else {
		timing->ddr5_txs_ps = timing->ddr5_trfc1_ps + 10000;
	}

	// Initialization
	timing->ddr5_tinit4_ps = 2000000;
	timing->ddr5_tinit5_tck = 3;
	// VrefCA
	timing->ddr5_tvrefca_delay_tck = timing->ddr5_tmrd_tck;
	timing->ddr5_tvrefca_cs_min_tck = 4;	//JEDEC 3.5 tck
	timing->ddr5_tvrefca_cs_max_tck = 8;
	// OSC TBD
	timing->ddr5_tosco_ps = timing->ddr5_tmrd_tck;
	// CRC TBD
	timing->ddr5_tcrc_alert_ps = 0;
	timing->ddr5_tcrc_alert_pw_ps = 0;
	if(IS_RDIMM || IS_LRDIMM || IS_UDIMM) {
		timing->ddr5_dimm_t_dcaw_tck = 128;
		timing->ddr5_dimm_n_dcac_m1  = 32;
	}
	// RCD
	if (IS_RDIMM || IS_LRDIMM) {
		timing->ddr5_rcd_tstab01_min_ps = 0;
		timing->ddr5_rcd_tstab01_max_ps = 3500000;
		timing->ddr5_rcd_tpdex_ps = max(10000, 16 * tck_ps);
		timing->ddr5_rcd_tcssr_ps = max(15000, 24 * tck_ps);
		timing->ddr5_rcd_tcpded2srx_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 16);
		timing->ddr5_rcd_tsrx2srx_tck = max(cinit_round_down_only_int_ddr5(10000, tck_ps), 16);
		timing->ddr5_rcd_tckoff_ps = max(15000, 24 * tck_ps);
		timing->ddr5_rcd_tckact_tck = 16;
		timing->ddr5_rcd_tcsalt_tck = 8;
		timing->ddr5_rcd_trpdx_ps = max(10000, (16*tck_ps));
		if (IS_LRDIMM) {
			timing->ddr5_tcpded_db_ps = 10000; // from DDR5DB01 Spec Rev 1.0
			timing->ddr5_rcd_tcssr_db_ps = 20000; // from DDR5DB01 Spec Rev 1.0
			timing->ddr5_rcd_tcpded2srx_db_tck = max(cinit_round_down_only_int_ddr5(15000, tck_ps), 24); // from DDR5DB01 Spec Rev 1.0
			timing->ddr5_rcd_tstab_dbcmd_ps = 0;	// TBD, defined as a max in DDR5RCD01 Spec Rev 1.0
			timing->ddr5_rcd_tstab_dbdata_ps = 4140000;	// 4.14us, defined as a max in DDR5RCD01 Spec Rev 1.0
			timing->ddr5_db_tmrrod1_tck = 8;	// from DDR5DB01 Spec Rev 1.0
			timing->ddr5_db_tmrr2nod1_tck = 16;	// from DDR5DB01 Spec Rev 1.0
		} else {
			timing->ddr5_tcpded_db_ps = 0;
			timing->ddr5_rcd_tcssr_db_ps = 0;
			timing->ddr5_rcd_tcpded2srx_db_tck = 0;
			timing->ddr5_rcd_tstab_dbcmd_ps = 0;
			timing->ddr5_db_tmrrod1_tck = 0;
			timing->ddr5_db_tmrr2nod1_tck = 0;
		}
	} else {
		timing->ddr5_rcd_tstab01_min_ps = 0;
		timing->ddr5_rcd_tpdex_ps = 0;
		timing->ddr5_rcd_tcssr_ps = 0;
		timing->ddr5_rcd_tcpded2srx_tck = 0;
		timing->ddr5_rcd_tsrx2srx_tck = 0;
		timing->ddr5_rcd_tckoff_ps = 0;
		timing->ddr5_rcd_tckact_tck = 0;
		timing->ddr5_rcd_tcsalt_tck = 0;
		timing->ddr5_rcd_trpdx_ps = 0;
		timing->ddr5_tcpded_db_ps = 0;
		timing->ddr5_rcd_tcssr_db_ps = 0;
		timing->ddr5_rcd_tcpded2srx_db_tck = 0;
		timing->ddr5_rcd_tstab_dbcmd_ps = 0;
		timing->ddr5_rcd_tstab_dbdata_ps = 0;
		timing->ddr5_db_tmrrod1_tck = 0;
		timing->ddr5_db_tmrr2nod1_tck = 0;
	}
	// Table 151 Read CRC latency Adder
	if (tck_ps < 333) // 6000 Mbps <-> 8400 Mbps
		timing->ddr5_read_crc_latency_adder = 2;
	else
		timing->ddr5_read_crc_latency_adder = 0;
	// Table 30 tCCD_L/tCCD_L_WR/tDLLK
	if (tck_ps >= 555) // 3600
		timing->ddr5_tdllk_tck = 1024;
	else if (tck_ps < 555 && tck_ps >= 500) // 3600->4000
		timing->ddr5_tdllk_tck = 1280;
	else if (tck_ps < 500 && tck_ps >= 454) // 4000->4400
		timing->ddr5_tdllk_tck = 1280;
	else if (tck_ps < 454 && tck_ps >= 384) // 4400->5200
		timing->ddr5_tdllk_tck = 1536;
	else if (tck_ps < 384 && tck_ps >= 357) // 5200->5600
		timing->ddr5_tdllk_tck = 1792;
	else if (tck_ps < 357 && tck_ps >= 333) // 5600->6000
		timing->ddr5_tdllk_tck = 1792;
	else if (tck_ps < 333 && tck_ps >= 312) // 6000->6400
		timing->ddr5_tdllk_tck = 2048;
	else if (tck_ps < 312 && tck_ps >= 294) // 6400->6800
		timing->ddr5_tdllk_tck = 2048;
	else if (tck_ps < 294 && tck_ps >= 277) // 6800->7200
		timing->ddr5_tdllk_tck = 2304;
	else if (tck_ps < 277 && tck_ps >= 263) // 7200->7600
		timing->ddr5_tdllk_tck = 2304;
	else                                    // 7600->8800
		timing->ddr5_tdllk_tck = 2560;

	// different value to DDR4 tPDM_RD/tPDM_WR
	// values observed from VIP
 	// update get_min_rd2wr_rank_switch_gap().ddr5_rcd_tpdm_rd_ps as
	// well to match if this changes
	timing->ddr5_rcd_tpdm_rd_ps = 1370 + CEIL(tck_ps,4);
	timing->ddr5_rcd_tpdm_wr_ps = 1370 + CEIL(tck_ps,4);

	timing->ddr5_rcd_tmrc_tck = 32;
	timing->ddr5_rcd_tmrc2n_tck = 16;
	timing->ddr5_rcd_tmrd_l_tck = 16;
	timing->ddr5_rcd_tmrd2n_l_tck = 24;
	timing->ddr5_rcd_tmrd_l2_tck = 32;
	timing->ddr5_rcd_tmrd2n_l2_tck = 50;

	SNPS_TRACE("Leaving");
}

// --------------------------------------------------------------------------
// Name        : ddr5_get_cas_latency()
// Description : depending on the speed grade/tck, pick a CAS latency
// Params      : speed_bin: DDR5 speed bin enum value
// Params      : tck_ps_p: Current clock cycle time
// Returns     : CAS Latency value
// --------------------------------------------------------------------------
uint32_t ddr5_get_cas_latency(SubsysHdlr_t *cfg, dwc_ddr5_speed_bin_t speed_bin, uint32_t tck_ps_p)
{
    uint32_t ddr5_cas_latency = 0;

#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
    ddrctl_error_t rslt;
    rslt = ddrctl_cinit_get_ddr5_speed_bin_cas_latency(cfg->spdData_m.ddr5_jedec_spec, speed_bin, tck_ps_p,
                                                SELECT_LOWER_CL, (uint8_t*)&ddr5_cas_latency);
    if(rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("No valid CAS latency found for speed bin %s (%d), error: %d",
                   ddrctl_cinit_get_ddr5_speed_bin_str(speed_bin), speed_bin, rslt);
        dwc_ddrctl_cinit_exit(1);
    }
#else /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    ddr5_cas_latency = ddrctl_cinit_get_ddr5_spd_cas_latency(&SPD_aux, tck_ps_p);
    if (0 == ddr5_cas_latency) {
        SNPS_ERROR("Minimum CAS Latency calculation failed");
        dwc_ddrctl_cinit_exit(1);
    }
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    SNPS_LOG("Minimum CAS Latency is %u", ddr5_cas_latency);
    return ddr5_cas_latency;
}


uint32_t dwc_cinit_get_ddr4_trfc(uint32_t capacity_mbits, uint32_t fgr_mode)
{
    SNPS_TRACE("Entering");

    uint32_t trfc_min_ps, trfc_min2_ps, trfc_min4_ps, ret;

#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
    switch (capacity_mbits) {
    case 2048:
        trfc_min_ps = 160000;
        trfc_min2_ps = 110000;
        trfc_min4_ps = 90000;
        break;
    case 4096:
        trfc_min_ps = 260000;
        trfc_min2_ps = 160000;
        trfc_min4_ps = 110000;
        break;
    case 8192:
        trfc_min_ps = 350000;
        trfc_min2_ps = 260000;
        trfc_min4_ps = 160000;
        break;
    case 16384:
        trfc_min_ps = 550000;
        trfc_min2_ps = 350000;
        trfc_min4_ps = 260000;
        break;
    default:
        SNPS_ERROR("Illegal sdram capacity %u for ddr4 passed in configuration", capacity_mbits);
        dwc_ddrctl_cinit_exit(1);
        break;
    }
#else /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    trfc_min_ps = SPD_aux.DDR4.tRFC1min_ps;
    trfc_min2_ps = SPD_aux.DDR4.tRFC2min_ps;
    trfc_min4_ps = SPD_aux.DDR4.tRFC4min_ps;
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */

    switch (fgr_mode) {
    case 2:
        ret = trfc_min4_ps;
        break;
    case 1:
        ret = trfc_min2_ps;
        break;
    case 0:
        ret = trfc_min_ps;
        break;
    default:
        SNPS_ERROR("Illegal fgr mode value %u passed in configuration", fgr_mode);
        dwc_ddrctl_cinit_exit(1);
        break;
    }

    SNPS_TRACE("Leaving");
    return ret;
}

uint32_t dwc_cinit_get_ddr4_trfc_dlr(uint32_t capacity_mbits, uint32_t fgr_mode)
{
    SNPS_TRACE("Entering");

    uint32_t trfc_dlr_ps, trfc_dlr2_ps, trfc_dlr4_ps, ret;

    //2Gb density is not supported for 3DS DDR4 wrt JEDEC
    if (capacity_mbits > 2048) {
        switch (capacity_mbits) {
        case 4096:
            trfc_dlr_ps = 90000;
            trfc_dlr2_ps = 55000;
            trfc_dlr4_ps = 40000;
            break;
        case 8192:
            trfc_dlr_ps = 120000;
            trfc_dlr2_ps = 90000;
            trfc_dlr4_ps = 55000;
            break;
        case 16384:
            trfc_dlr_ps = 120000;
            trfc_dlr2_ps = 90000;
            trfc_dlr4_ps = 55000;
            break;
        default:
            SNPS_ERROR("Illegal sdram capacity %u for 3DS ddr4 passed in configuration", capacity_mbits);
            dwc_ddrctl_cinit_exit(1);
            break;
        }
    } else {
        trfc_dlr_ps = 0;
        trfc_dlr2_ps = 0;
        trfc_dlr4_ps = 0;
    }

    switch (fgr_mode) {
    case 2:
        ret = trfc_dlr4_ps;
        break;
    case 1:
        ret = trfc_dlr2_ps;
        break;
    case 0:
        ret = trfc_dlr_ps;
        break;
    default:
        SNPS_ERROR("Illegal fgr mode value %u passed in configuration", fgr_mode);
        dwc_ddrctl_cinit_exit(1);
        break;
    }

    SNPS_TRACE("Leaving");
    return ret;
}

uint32_t dwc_cinit_get_ddr5_trfc(uint32_t capacity_mbits, uint32_t fgr_mode)
{
    uint32_t trfc_min_ps, trfc_min2_ps, ret;

#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
	// DDR5 Full Spec Draft Rev1.90 does not define the trfc related timing for 64Gb
	switch (capacity_mbits) {
        case 8192:
            trfc_min_ps = 195000;
            trfc_min2_ps = 130000;
            break;
        case 16384:
            trfc_min_ps = 295000;
            trfc_min2_ps = 160000;
            break;
        case 24576:
        case 32768:
        case 65536:
            trfc_min_ps = 410000;
            trfc_min2_ps = 220000;
            break;
        default:
            SNPS_ERROR("Illegal sdram capacity %u for ddr5 passed in configuration", capacity_mbits);
            dwc_ddrctl_cinit_exit(1);
            break;
	}
#else /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    trfc_min_ps = SPD_aux.DDR5.tRFC1_slr_min_ns * 1000;
    trfc_min2_ps = SPD_aux.DDR5.tRFC2_slr_min_ns * 1000;
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */

    switch (fgr_mode) {
        case FGR_MODE_FIXED_2X:
            ret = trfc_min2_ps;
            break;
        case FGR_MODE_FIXED_1X:
            ret = trfc_min_ps;
            break;
        default:
            SNPS_ERROR("Illegal fgr mode value %u passed in configuration", fgr_mode);
            dwc_ddrctl_cinit_exit(1);
            break;
    }

    SNPS_DEBUG("tRFC(min) = %d (0x%x) ps", ret, ret);

    return ret;
}

/** @brief method to return 3DS tRFC paramters by logical rank density
 * @param capacity_mbits rank density
 * @param fgr_mode fine grain refresh mode
 */
uint32_t dwc_cinit_get_ddr5_trfc_dlr(uint32_t capacity_mbits, uint32_t fgr_mode)
{
    uint32_t trfc1_dlr_ps, trfc2_dlr_ps, ret;

#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE
	// DDR5 Full Spec Draft Rev1.90 does not define the trfc related timing for 64Gb
	// 3DS tRFC parameters are to be rounded up to the nearest 1ns after the “tRFC*min”/3 calculation.
	switch (capacity_mbits) {
        case 8192:
            trfc1_dlr_ps = CEIL(195, 3) * 1000;
            trfc2_dlr_ps = CEIL(130, 3) * 1000;
            break;
        case 16384:
            trfc1_dlr_ps = CEIL(295, 3) * 1000;
            trfc2_dlr_ps = CEIL(160, 3) * 1000;
            break;
        case 24576:
        case 32768:
        case 65536:
            trfc1_dlr_ps = CEIL(410, 3) * 1000;
            trfc2_dlr_ps = CEIL(220, 3) * 1000;
            break;
        default:
            SNPS_ERROR("Illegal sdram capacity %u for 3DS ddr5 passed in configuration", capacity_mbits);
            dwc_ddrctl_cinit_exit(1);
            break;
	}
#else /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */
    trfc1_dlr_ps = SPD_aux.DDR5.tRFC1_dlr_min_ns * 1000;
    trfc2_dlr_ps = SPD_aux.DDR5.tRFC2_dlr_min_ns * 1000;
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE */

    switch (fgr_mode) {
        case FGR_MODE_FIXED_2X:
            ret = trfc2_dlr_ps;
            break;
        case FGR_MODE_FIXED_1X:
            ret = trfc1_dlr_ps;
            break;
        default:
            SNPS_ERROR("Illegal fgr mode value %u passed in configuration", fgr_mode);
            dwc_ddrctl_cinit_exit(1);
            break;
    }
    return ret;
}

#endif                            // DDRCTL_DDR
