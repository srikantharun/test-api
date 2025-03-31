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


#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_types_str.h"
#include "dwc_ddrctl_cinit_defines.h"

#ifdef DDRCTL_LPDDR

//Local variables to which data_rate is assigned as per tck_ps
dwc_lpddr4_data_rate_e l_lpddr4_data_rate[UMCTL2_FREQUENCY_NUM];
dwc_lpddr5_data_rate_e l_lpddr5_data_rate[UMCTL2_FREQUENCY_NUM];

/**
 * @brief Description : set the sg_tck_ps value in the hdlr->timingParams_m structure.
 * @note these are JEDEC timing value
 */
void lpddr4_set_clk_speed(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n)
{
    SNPS_TRACE("Entering");
    dwc_lpddr4_data_rate_e sg = SPD.lpddr4_data_rate;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];

	switch (sg) {
	case DWC_LPDDR4_4267:
		timing->sg_tck_ps = 469;
		break;
	case DWC_LPDDR4_3733:
		timing->sg_tck_ps = 536;
		break;
	case DWC_LPDDR4_3200:
		timing->sg_tck_ps = 625;
		break;
	case DWC_LPDDR4_2667:
		timing->sg_tck_ps = 750;
		break;
	case DWC_LPDDR4_2133:
		timing->sg_tck_ps = 938;
		break;
	case DWC_LPDDR4_1600:
		timing->sg_tck_ps = 1250;
		break;
	case DWC_LPDDR4_1066:
		timing->sg_tck_ps = 1875;
		break;
	case DWC_LPDDR4_533:
		timing->sg_tck_ps = 3760;
		break;
	default:
		SNPS_ERROR("Unknown date rate, sg = %u", sg);
		break;
	}
	timing->lpddr4_tckb = timing->sg_tck_ps;
	SNPS_TRACE("Leaving");
}

/**
 * @brief method to setup timing parameters for LPDDR4
 */
void lpddr4_set_default_timing(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n, uint32_t lpddr_mixed_pkg_en)
{
    SNPS_TRACE("Entering");
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
    // tck_ps may or may not be min JEDEC value
    uint32_t tck_ps = SPD.tck_ps[p];
    uint32_t sdram_capacity_mbits = SPD.sdram_capacity_mbits[n];
    uint32_t sdram_capacity_mbits_lp45_mp = SPD.sdram_capacity_mbits_lp45_mp[n];

    SNPS_LOG("sdram_capacity_mbits = %0u, n=%0u", sdram_capacity_mbits, n);
    SNPS_LOG("sdram_capacity_mbits_lp45_mp = %0u, n=%0u", sdram_capacity_mbits_lp45_mp, n);

    if (SPD.tck_ps[p] != timing->sg_tck_ps) {
        SNPS_LOG("tck_ps (%u ps) selected is not min JEDEC TCK value(%u)", SPD.tck_ps[p], timing->sg_tck_ps);
	}

    #ifdef MEMC_BURST_LENGTH_32
    timing->burst_length = 32;  // BL 32 - Length value supported for LPDDR4
    #else
    timing->burst_length = 16;  // BL 16 - Length value supported for LPDDR4
    #endif


    timing->lpddr4_tpbr2pbr = dwc_cinit_get_lpddr4_tpbr2pbr(sdram_capacity_mbits);
    timing->lpddr4_trfcab = dwc_cinit_get_lpddr4_trfcab(sdram_capacity_mbits);
    timing->lpddr4_trfcpb = dwc_cinit_get_lpddr4_trfcpb(sdram_capacity_mbits);
    timing->lpddr4_trfmpb = dwc_cinit_get_lpddr4_trfmpb(sdram_capacity_mbits);
    timing->lpddr4_tpbr2pbr_mp = dwc_cinit_get_lpddr4_tpbr2pbr(sdram_capacity_mbits_lp45_mp);
    timing->lpddr4_trfcab_mp = dwc_cinit_get_lpddr4_trfcab(sdram_capacity_mbits_lp45_mp);
    timing->lpddr4_trfcpb_mp = dwc_cinit_get_lpddr4_trfcpb(sdram_capacity_mbits_lp45_mp);
    timing->lpddr4_trfmpb_mp = dwc_cinit_get_lpddr4_trfmpb(sdram_capacity_mbits_lp45_mp);

    timing->lpddr4_tras_min = max(42000, 3 * tck_ps);
    timing->lpddr4_tras_max = 70200000;
    timing->lpddr4_trfiab = 3904000;
    timing->lpddr4_trfipb = 488000;
    if (IS_X8(n) || lpddr_mixed_pkg_en)
        timing->lpddr4_twtr = max(12000, 8 * tck_ps);
    else
        timing->lpddr4_twtr = max(10000, 8 * tck_ps);
    timing->lpddr4_tfaw = 40000;
    timing->lpddr4_tzqreset = max(CEIL(50000, tck_ps), 3);
    timing->lpddr4_tzqinit = CEIL(100000, tck_ps);

    timing->lpddr4_tzqcs = max(CEIL(30000, tck_ps), 8);
    timing->lpddr4_tzqcsb = max(CEIL(30000, timing->lpddr4_tckb), 8);
    timing->lpddr4_tzqclb = CEIL(1000000, timing->lpddr4_tckb);
    timing->lpddr4_tzqcl = CEIL(1000000, tck_ps);
    timing->lpddr4_tmrr = 8;
    timing->lpddr4_tmrw = max(CEIL(10000, tck_ps), 10);
    timing->lpddr4_tmrwb = max(CEIL(10000, timing->lpddr4_tckb), 10);
    timing->lpddr4_tmrd = max(CEIL(14000, tck_ps), 10);
    timing->lpddr4_tmrdb = max(CEIL(14000, timing->lpddr4_tckb), 10);

    timing->lpddr4_tcke = max(7500, tck_ps * 4);
    timing->lpddr4_tckesr = 15000;
    timing->lpddr4_tccd = 8;
    timing->lpddr4_tccd_bl32 = 16;
    timing->lpddr4_tccdmw = 32;
    timing->lpddr4_tccdmw_bl32 = 128;
    timing->lpddr4_trtp = max(7500, 8 * tck_ps);
    if (IS_X8(n) || lpddr_mixed_pkg_en)
        timing->lpddr4_twr = max(20000, 6 * tck_ps) + ((SPD.lpddr4_scl==1) ? 16000 : 0);
    else
        timing->lpddr4_twr = max(18000, 6 * tck_ps) + ((SPD.lpddr4_scl==1) ? 16000 : 0);    // x16
    timing->lpddr4_tppd = 4;
    timing->lpddr4_tdqsck = 3000;
    timing->lpddr4_tdqsck_max = 3500;
    timing->lpddr4_tdqsck_max_dr = 3600;
    timing->lpddr4_tosco = max(40000, 8 * tck_ps);

    timing->lpddr4_tdqss = 1;
    timing->lpddr4_tdqs2dq = 450;
    timing->lpddr4_tdipw_ps = (uint32_t)(ceil((tck_ps >> 1) * 0.45));
    timing->lpddr4_trcd = max(18000, 4 * tck_ps);
    timing->lpddr4_trp = max(18000, 4 * tck_ps);
    timing->lpddr4_trpa = max(21000, 4 * tck_ps);
    timing->lpddr4_trc = timing->lpddr4_tras_min + timing->lpddr4_trp;
    timing->lpddr4_tcmdcke = max(1750, 3 * tck_ps);
    timing->lpddr4_tmrwckel = max(14000, 10 * tck_ps);
    timing->lpddr4_tmrwckelb = max(14000, 10 * timing->lpddr4_tckb);
    timing->lpddr4_tckckeh = max(1750, 3 * tck_ps);
    timing->lpddr4_tckelck = max(5000, 5 * tck_ps);
    timing->lpddr4_tsr = max(15000, 3 * tck_ps);
    timing->lpddr4_todton_min = 1500;
    timing->lpddr4_tvrcg_enable = 200000;
    timing->lpddr4_tvrcg_disable = 100000;
    timing->lpddr4_derated_trcd = timing->lpddr4_trcd + 1875;
    timing->lpddr4_derated_tras_min = timing->lpddr4_tras_min + 1875;
    timing->lpddr4_derated_trp = timing->lpddr4_trp + 1875;
    timing->lpddr4_derated_trc = timing->lpddr4_tras_min + timing->lpddr4_trp + 3750;

    timing->lpddr4_txp = max(7500, 5 * tck_ps);
    switch (l_lpddr4_data_rate[0]) {    //tFAW, tRRD will be constant for the speed_bin in use
    case DWC_LPDDR4_4267:
        timing->lpddr4_tfaw = 30000;
        timing->lpddr4_trrd = max(7500, 4 * tck_ps);
        break;
    default:
        timing->lpddr4_tfaw = 40000;
        timing->lpddr4_trrd = max(10000, 4 * tck_ps);
        break;
    }
    timing->lpddr4_derated_trrd = timing->lpddr4_trrd + 1875;

    if (IS_X8(n) || lpddr_mixed_pkg_en) {
        switch (l_lpddr4_data_rate[p]) {
        case DWC_LPDDR4_4267:
            timing->lpddr4_cl = 40;
            timing->lpddr4_cl_dbi = 44;
            timing->lpddr4_nrtp = 16;
            break;
        case DWC_LPDDR4_3733:
            timing->lpddr4_cl = 36;
            timing->lpddr4_cl_dbi = 40;
            timing->lpddr4_nrtp = 14;
            break;
        case DWC_LPDDR4_3200:
            timing->lpddr4_cl = 32;
            timing->lpddr4_cl_dbi = 36;
            timing->lpddr4_nrtp = 12;
            break;
        case DWC_LPDDR4_2667:
            timing->lpddr4_cl = 26;
            timing->lpddr4_cl_dbi = 30;
            timing->lpddr4_nrtp = 10;
            break;
        case DWC_LPDDR4_2133:
            timing->lpddr4_cl = 22;
            timing->lpddr4_cl_dbi = 24;
            timing->lpddr4_nrtp = 8;
            break;
        case DWC_LPDDR4_1600:
            timing->lpddr4_cl = 16;
            timing->lpddr4_cl_dbi = 18;
            timing->lpddr4_nrtp = 8;
            break;
        case DWC_LPDDR4_1066:
            timing->lpddr4_cl = 10;
            timing->lpddr4_cl_dbi = 12;
            timing->lpddr4_nrtp = 8;
            break;
        case DWC_LPDDR4_533:
            timing->lpddr4_cl = 6;
            timing->lpddr4_cl_dbi = 6;
            timing->lpddr4_nrtp = 8;
            break;

        default:
            SNPS_ERROR("Unknown data rate, sg = %u", l_lpddr4_data_rate[p]);
            break;
        }
    } else {
        switch (l_lpddr4_data_rate[p]) {
        case DWC_LPDDR4_4267:
            timing->lpddr4_cl = 36;
            timing->lpddr4_cl_dbi = 40;
            timing->lpddr4_nrtp = 16;
            break;
        case DWC_LPDDR4_3733:
            timing->lpddr4_cl = 32;
            timing->lpddr4_cl_dbi = 36;
            timing->lpddr4_nrtp = 14;
            break;
        case DWC_LPDDR4_3200:
            timing->lpddr4_cl = 28;
            timing->lpddr4_cl_dbi = 32;
            timing->lpddr4_nrtp = 12;
            break;
        case DWC_LPDDR4_2667:
            timing->lpddr4_cl = 24;
            timing->lpddr4_cl_dbi = 28;
            timing->lpddr4_nrtp = 10;
            break;
        case DWC_LPDDR4_2133:
            timing->lpddr4_cl = 20;
            timing->lpddr4_cl_dbi = 22;
            timing->lpddr4_nrtp = 8;
            break;
        case DWC_LPDDR4_1600:
            timing->lpddr4_cl = 14;
            timing->lpddr4_cl_dbi = 16;
            timing->lpddr4_nrtp = 8;
            break;
        case DWC_LPDDR4_1066:
            timing->lpddr4_cl = 10;
            timing->lpddr4_cl_dbi = 12;
            timing->lpddr4_nrtp = 8;
            break;
        case DWC_LPDDR4_533:
            timing->lpddr4_cl = 6;
            timing->lpddr4_cl_dbi = 6;
            timing->lpddr4_nrtp = 8;
            break;

        default:
            SNPS_ERROR("Unknown speedgrade, sg = %u", l_lpddr4_data_rate[p]);
            break;
        }
    }
    if (IS_X8(n) || lpddr_mixed_pkg_en) {
        switch (timing->lpddr4_cl) {
        case 6:
            timing->lpddr4_cwl_seta = 4;
            timing->lpddr4_cwl_setb = 4;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 11 : 6;
            break;
        case 10:
            timing->lpddr4_cwl_seta = 6;
            timing->lpddr4_cwl_setb = 8;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 21 : 12;
            break;
        case 16:
            timing->lpddr4_cwl_seta = 8;
            timing->lpddr4_cwl_setb = 12;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 29 : 16;
            break;
        case 22:
            timing->lpddr4_cwl_seta = 10;
            timing->lpddr4_cwl_setb = 18;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 40 : 22;
            break;
        case 26:
            timing->lpddr4_cwl_seta = 12;
            timing->lpddr4_cwl_setb = 22;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 50 : 28;
            break;
        case 32:
            timing->lpddr4_cwl_seta = 14;
            timing->lpddr4_cwl_setb = 26;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 58 : 32;
            break;
        case 36:
            timing->lpddr4_cwl_seta = 16;
            timing->lpddr4_cwl_setb = 30;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 68 : 38;
            break;
        case 40:
            timing->lpddr4_cwl_seta = 18;
            timing->lpddr4_cwl_setb = 34;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 79 : 44;
            break;
        default:
            SNPS_ERROR("Unknown cas, lpddr4_cl = %u", timing->lpddr4_cl);
            break;
        }
    } else {
        switch (timing->lpddr4_cl) {
        case 6:
            timing->lpddr4_cwl_seta = 4;
            timing->lpddr4_cwl_setb = 4;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 11 :  6;
            break;
        case 10:
            timing->lpddr4_cwl_seta = 6;
            timing->lpddr4_cwl_setb = 8;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 19 : 10;
            break;
        case 14:
            timing->lpddr4_cwl_seta = 8;
            timing->lpddr4_cwl_setb = 12;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 29 : 16;
            break;
        case 20:
            timing->lpddr4_cwl_seta = 10;
            timing->lpddr4_cwl_setb = 18;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 38 : 20;
            break;
        case 24:
            timing->lpddr4_cwl_seta = 12;
            timing->lpddr4_cwl_setb = 22;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 46 : 24;
            break;
        case 28:
            timing->lpddr4_cwl_seta = 14;
            timing->lpddr4_cwl_setb = 26;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 56 : 30;
            break;
        case 32:
            timing->lpddr4_cwl_seta = 16;
            timing->lpddr4_cwl_setb = 30;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 64 : 34;
            break;
        case 36:
            timing->lpddr4_cwl_seta = 18;
            timing->lpddr4_cwl_setb = 34;
            timing->lpddr4_nwr = (SPD.lpddr4_scl==1) ? 75 : 40;
            break;
        default:
            SNPS_ERROR("Unknown cas, lpddr4_cl = %u", timing->lpddr4_cl);
            break;
        }
    }

    switch (l_lpddr4_data_rate[p]) {
    case DWC_LPDDR4_4267:
        timing->lpddr4_odtloff_latency_seta = 28;
        timing->lpddr4_odtloff_latency_setb = 44;
        timing->lpddr4_odtlon_latency_seta = 8;
        timing->lpddr4_odtlon_latency_setb = 24;
        timing->lpddr4_wdqson_seta = 8;
        timing->lpddr4_wdqson_setb = 24;
        timing->lpddr4_wdqsoff_seta = 36;
        timing->lpddr4_wdqsoff_setb = 52;
        break;
    case DWC_LPDDR4_3733:
        timing->lpddr4_odtloff_latency_seta = 26;
        timing->lpddr4_odtloff_latency_setb = 40;
        timing->lpddr4_odtlon_latency_seta = 6;
        timing->lpddr4_odtlon_latency_setb = 20;
        timing->lpddr4_wdqson_seta = 6;
        timing->lpddr4_wdqson_setb = 20;
        timing->lpddr4_wdqsoff_seta = 33;
        timing->lpddr4_wdqsoff_setb = 47;
        break;
    case DWC_LPDDR4_3200:
        timing->lpddr4_odtloff_latency_seta = 24;
        timing->lpddr4_odtloff_latency_setb = 36;
        timing->lpddr4_odtlon_latency_seta = 6;
        timing->lpddr4_odtlon_latency_setb = 18;
        timing->lpddr4_wdqson_seta = 6;
        timing->lpddr4_wdqson_setb = 18;
        timing->lpddr4_wdqsoff_seta = 30;
        timing->lpddr4_wdqsoff_setb = 42;
        break;
    case DWC_LPDDR4_2667:
        timing->lpddr4_odtloff_latency_seta = 22;
        timing->lpddr4_odtloff_latency_setb = 32;
        timing->lpddr4_odtlon_latency_seta = 4;
        timing->lpddr4_odtlon_latency_setb = 14;
        timing->lpddr4_wdqson_seta = 4;
        timing->lpddr4_wdqson_setb = 14;
        timing->lpddr4_wdqsoff_seta = 27;
        timing->lpddr4_wdqsoff_setb = 37;
        break;
    case DWC_LPDDR4_2133:
        timing->lpddr4_odtloff_latency_seta = 20;
        timing->lpddr4_odtloff_latency_setb = 28;
        timing->lpddr4_odtlon_latency_seta = 4;
        timing->lpddr4_odtlon_latency_setb = 12;
        timing->lpddr4_wdqson_seta = 4;
        timing->lpddr4_wdqson_setb = 12;
        timing->lpddr4_wdqsoff_seta = 24;
        timing->lpddr4_wdqsoff_setb = 32;
        break;
    case DWC_LPDDR4_1600:
        timing->lpddr4_odtloff_latency_seta = 20;
        timing->lpddr4_odtloff_latency_setb = 22;
        timing->lpddr4_odtlon_latency_seta = 1;
        timing->lpddr4_odtlon_latency_setb = 6;
        timing->lpddr4_wdqson_seta = 0;
        timing->lpddr4_wdqson_setb = 6;
        timing->lpddr4_wdqsoff_seta = 21;
        timing->lpddr4_wdqsoff_setb = 25;
        break;
    case DWC_LPDDR4_1066:
        timing->lpddr4_odtloff_latency_seta = 20;
        timing->lpddr4_odtloff_latency_setb = 22;
        timing->lpddr4_odtlon_latency_seta = 1;
        timing->lpddr4_odtlon_latency_setb = 6;
        timing->lpddr4_wdqson_seta = 0;
        timing->lpddr4_wdqson_setb = 0;
        timing->lpddr4_wdqsoff_seta = 18;
        timing->lpddr4_wdqsoff_setb = 20;
        break;
    case DWC_LPDDR4_533:
        timing->lpddr4_odtloff_latency_seta = 20;// NA in JEDEC
        timing->lpddr4_odtloff_latency_setb = 22; // NA in JEDEC
        timing->lpddr4_odtlon_latency_seta = 0;
        timing->lpddr4_odtlon_latency_setb = 0;
        timing->lpddr4_wdqson_seta = 0;
        timing->lpddr4_wdqson_setb = 0;
        timing->lpddr4_wdqsoff_seta = 18;
        timing->lpddr4_wdqsoff_setb = 20;
        break;

    default:
        SNPS_ERROR("Unknown speedgrade, sg = %u", l_lpddr4_data_rate[p]);
        break;
    }
    // calculate tzqinit
    timing->lpddr_tzqinit_min = CEIL(timing->lpddr4_tzqinit, 32);
    SNPS_TRACE("Leaving");
}

/**
 * @brief Description : set the sg_tck_ps value in the hdlr->timingParams_m structure.
 * @note these are JEDEC timing values, using data rate (WCK) and WCKCK
 * ratio the CK period is calculated.
 */
void lpddr5_set_clk_speed(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n)
{
	SNPS_TRACE("Entering");
	dwc_lpddr5_data_rate_e sg = SPD.lpddr5_data_rate;
	ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
	dwc_freq_ratio_t ratio_wckck = ddrctl_sw_get_ratio(hdlr, p);

	switch (sg) {
	case DWC_LPDDR5_9600:
		timing->sg_tck_ps = 834; //RB23053-LPDDR5X Clock Timing for 9600Mbps.pdf
		break;
	case DWC_LPDDR5_8533:
		timing->sg_tck_ps = 938; //JESD209-5B, Table 442
		break;
	case DWC_LPDDR5_7500:
		timing->sg_tck_ps = 1067;
		break;
	case DWC_LPDDR5_6400:
		timing->sg_tck_ps = 1250;
		break;
	case DWC_LPDDR5_6000:
		timing->sg_tck_ps = 1334;
		break;
	case DWC_LPDDR5_5500:
		timing->sg_tck_ps = 1454;
		break;
	case DWC_LPDDR5_4800:
		timing->sg_tck_ps = 1667;
		break;
	case DWC_LPDDR5_4267:
		timing->sg_tck_ps = 1875;
		break;
	case DWC_LPDDR5_3733:
		timing->sg_tck_ps = 2150;
		break;
	case DWC_LPDDR5_3200:
		timing->sg_tck_ps = (ratio_wckck == DWC_RATIO_WCK_CK_4_1) ? 2500 : 1250;
		break;
	case DWC_LPDDR5_2750:
		timing->sg_tck_ps = (ratio_wckck == DWC_RATIO_WCK_CK_4_1) ? 2900 : 1454; //1453 is changed to 1454, to get freq=688MHz. Reference: Bug 10981.
		break;
	case DWC_LPDDR5_2133:
		timing->sg_tck_ps = (ratio_wckck == DWC_RATIO_WCK_CK_4_1) ? 3750 : 1875;
		break;
	case DWC_LPDDR5_1600:
		timing->sg_tck_ps = (ratio_wckck == DWC_RATIO_WCK_CK_4_1) ? 5000 : 2500;
		break;
	case DWC_LPDDR5_1067:
		timing->sg_tck_ps = (ratio_wckck == DWC_RATIO_WCK_CK_4_1) ? 7520 : 3750;
		break;
	case DWC_LPDDR5_533:
		timing->sg_tck_ps = (ratio_wckck == DWC_RATIO_WCK_CK_4_1) ? 14926 : 7520;
		break;
	default:
		SNPS_ERROR("Unknown data rate, = %u", sg);
		break;
	}

	if (ratio_wckck == DWC_RATIO_WCK_CK_4_1) {
		timing->lpddr5_wck_ps = DIV_4(timing->sg_tck_ps);
	} else {
		timing->lpddr5_wck_ps = DIV_2(timing->sg_tck_ps);
	}
	SNPS_TRACE("Leaving");
}

/** @brief method to setup timing parameters for LPDDR5
 * @note these are JEDEC timing values: COMMITTEE LETTER BALLOT Item #
 * JC-42.6-18xx.xx , Date: 2018/05/14
 *
 */
void lpddr5_set_default_timing(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n, uint32_t lpddr_mixed_pkg_en)
{
    SNPS_TRACE("Entering");
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
    // tck_ps may or may not be min JEDEC value
    uint8_t ratio_factor;
    dwc_freq_ratio_t ratio;
    uint32_t tck_ps = SPD.tck_ps[p];
    uint32_t sdram_capacity_mbits = SPD.sdram_capacity_mbits[n];
    uint32_t sdram_capacity_mbits_lp45_mp = SPD.sdram_capacity_mbits_lp45_mp[n];
    // determines if x16 values should be used as x8 values applies to x16 devices if   lpddr_mixed_pkg_en=1
    uint32_t is_x16_val = IS_X16(n) && !lpddr_mixed_pkg_en;

    if (SPD.tck_ps[p] != timing->sg_tck_ps) {
        SNPS_LOG("tck_ps (%u ps) selected is not min JEDEC TCK value(%u)", SPD.tck_ps[p], timing->sg_tck_ps);
    }
    uint8_t wl_seta = (hdlr->memCtrlr_m.lpddr5_mr[p].mr3.wls == 0) ? 1 : 0;
    uint8_t dvfsc_type = hdlr->memCtrlr_m.lpddr5_mr[p].mr19.dvfsc; // 0=disabled 1=dvfsc 2=enhanced dvfsc
    uint8_t read_dbi = hdlr->memCtrlr_m.lpddr5_mr[p].mr3.read_dbi;
    uint8_t rd_lecc = hdlr->memCtrlr_m.lpddr5_mr[p].mr22.recc;
    uint8_t wr_lecc = hdlr->memCtrlr_m.lpddr5_mr[p].mr22.wecc;
    if(dvfsc_type==2 && (rd_lecc || wr_lecc)) {
        SNPS_ERROR("Violating that enahnced DVFSC feature and Link ecc feature are mutually exclusive: eDVFSC=%0d, RD link ECC=%0d, WR link ECC=%0d", dvfsc_type, rd_lecc, wr_lecc);
    }

    ratio = ddrctl_sw_get_ratio(hdlr, p);
    ratio_factor = ddrctl_sw_get_ratio_factor(hdlr, p);

	#ifdef MEMC_BURST_LENGTH_32
	timing->burst_length = 32;  // BL 32 - Length value supported for LPDDR5
	#else
	timing->burst_length = 16;  // BL 16 - Length value supported for LPDDR5
	#endif

	timing->lpddr5_trfcab_ps = dwc_cinit_get_lpddr5_trfcab(sdram_capacity_mbits, dvfsc_type);
	timing->lpddr5_trfcpb_ps = dwc_cinit_get_lpddr5_trfcpb(sdram_capacity_mbits, dvfsc_type);
	timing->lpddr5_trfcab_mp_ps = dwc_cinit_get_lpddr5_trfcab(sdram_capacity_mbits_lp45_mp, dvfsc_type);
	timing->lpddr5_trfcpb_mp_ps = dwc_cinit_get_lpddr5_trfcpb(sdram_capacity_mbits_lp45_mp, dvfsc_type);
	timing->lpddr5_trfmpb_ps = dwc_cinit_get_lpddr5_trfmpb(sdram_capacity_mbits);
	timing->lpddr5_trfmpb_mp_ps = dwc_cinit_get_lpddr5_trfmpb(sdram_capacity_mbits_lp45_mp);
	timing->lpddr5_tpbr2pbr_ps = dwc_cinit_get_lpddr5_tpbr2pbr(sdram_capacity_mbits, dvfsc_type);
	timing->lpddr5_tpbr2pbr_mp_ps = dwc_cinit_get_lpddr5_tpbr2pbr(sdram_capacity_mbits_lp45_mp, dvfsc_type);
	timing->lpddr5_tpbr2act_ps = 7500;
	// Using VIP default values for simulation.
	timing->lpddr5_wckdqo_ps = 1000;
	timing->lpddr5_wckdqo_max_ps = ((ratio_factor == 4) && ( tck_ps <=2499)) ? 1600 : 1900; //WCK to DQ output offset max value is depend on data rate; up to 3200Mbps -> tWCK2DQO_LF(max)=1900ps, over 3200Mbps ->tWCK2DQO_HF(max)=1600ps
	SNPS_LOG("ratio = %u   tck_ps = %u  lpddr5_wckdqo_max_ps = %u", ratio_factor, tck_ps, timing->lpddr5_wckdqo_max_ps);
	if((SPD.use_lpddr5x & IS_LPDDR5) && (timing->sg_tck_ps <= 1067 )) //>=7500Mbps JIRA___P80001562-414987 //need to confirm the condition
	  timing->lpddr5_wckdqi_ps = 400;
	else
	timing->lpddr5_wckdqi_ps = 500;
	timing->lpddr5_tosco = max(40000, 8 * tck_ps); // both tOSCODQI and tOSCODQO are the same value
	timing->lpddr5_trpst = (uint32_t)(2.5 * (uint32_t)(tck_ps / ratio_factor));	// 2.5 tWCK
	timing->lpddr5_tespd_ps = max(1750, 2 * tck_ps);
	timing->lpddr5_tsr_ps = max(15000, 2 * tck_ps);
	timing->lpddr5_txsr_ps = timing->lpddr5_trfcab_ps + max(7500, 2 * tck_ps);
	timing->lpddr5_tcspd_ps = 10000 + tck_ps;
	timing->lpddr5_tcmpd_ps = max(1500, 2 * tck_ps);
	timing->lpddr5_tescke_ps = max(1750, 3 * tck_ps);
	timing->lpddr5_tcmdpd_ps = 3 * tck_ps;
	timing->lpddr5_tcslck_ps = max(5000, 3 * tck_ps);
	timing->lpddr5_tckcsh_ps = 2 * tck_ps;
	timing->lpddr5_txp_ps = max(7500, 3 * tck_ps);
	timing->lpddr5_tpdxcsodton_ps = 20000; // added in JESD209-5A
	timing->lpddr5_tmrw_l_ps = 250*1000; // JESD209-5C Stretched Mode Register Write command period
	timing->lpddr5_tcsh_ps = 3000;
	timing->lpddr5_tcsl_ps = 4000;
	timing->lpddr5_tmrwpd_ps = max(14000, 6 * tck_ps);
	timing->lpddr5_tzqpd_ps = max(1750, 2 * tck_ps);
	timing->lpddr5_tpdn_ps = 10000 + tck_ps;
	timing->lpddr5_tpdn_dsm_ms = 4;
	timing->lpddr5_txsr_dsm_us = 200;	// in useconds
	timing->lpddr5_tras_min_ps = max(42000, 3 * tck_ps);
	timing->lpddr5_trefi_ps = 3906000;
	timing->lpddr5_tras_max_ps = 70200000;
	timing->lpddr5_trefipb_ps = 488000;
	if (dvfsc_type == 0) { //DVFSC disable
		timing->lpddr5_trpab_ps = max(21000, 2 * tck_ps);
		timing->lpddr5_trppb_ps = max(18000, 2 * tck_ps);
		timing->lpddr5_trcd_ps = max(18000, 2 * tck_ps);
		timing->lpddr5_trcd_write_ps = max(8000, 2 * tck_ps);
		if (ratio == DWC_RATIO_WCK_CK_4_1)
			timing->lpddr5_trbtp_ps = max(7500, 2 * tck_ps) - (2 * tck_ps);
		else
			timing->lpddr5_trbtp_ps = max(7500, 4 * tck_ps) - (4 * tck_ps);
	} else if(dvfsc_type == 1) { //DVFSC enable
		timing->lpddr5_trpab_ps = max(21000, 2 * tck_ps);
		timing->lpddr5_trppb_ps = max(18000, 2 * tck_ps);
		timing->lpddr5_trcd_ps = max(19000, 2 * tck_ps);
		timing->lpddr5_trcd_write_ps = max(9000, 2 * tck_ps);
		if (ratio == DWC_RATIO_WCK_CK_4_1)
			timing->lpddr5_trbtp_ps = max(8500, 2 * tck_ps) - (2 * tck_ps);
		else
			timing->lpddr5_trbtp_ps = max(8500, 4 * tck_ps) - (4 * tck_ps);
	} else {	// Enahnced DVFSC enable
		timing->lpddr5_trpab_ps = max(23000, 2 * tck_ps);
		timing->lpddr5_trppb_ps = max(20000, 2 * tck_ps);
		timing->lpddr5_trcd_ps = max(20000, 2 * tck_ps);
		timing->lpddr5_trcd_write_ps = max(9000, 2 * tck_ps);
		if (ratio == DWC_RATIO_WCK_CK_4_1)
			timing->lpddr5_trbtp_ps = max(8500, 2 * tck_ps) - (2 * tck_ps);
		else
			timing->lpddr5_trbtp_ps = max(8500, 4 * tck_ps) - (4 * tck_ps);
	}
	// ACTIVATE to ACTIVATE with all-bank precharge
	timing->lpddr5_trc_pab_ps = timing->lpddr5_tras_min_ps + timing->lpddr5_trpab_ps;
	// ACTIVATE to ACTIVATE with per-bank precharge
	timing->lpddr5_trc_ppb_ps = timing->lpddr5_tras_min_ps + timing->lpddr5_trppb_ps;
	if (ratio == DWC_RATIO_WCK_CK_4_1) {
		timing->lpddr5_tccd_s_tck = 2;
		timing->lpddr5_tccd_l_tck      = (SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 4 : 2;
		timing->lpddr5_tccd_l_bl32_tck = (SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 8 : 4;
		timing->lpddr5_tccd_ps = 2 * tck_ps;
	} else {
		timing->lpddr5_tccd_s_tck = 4;
		timing->lpddr5_tccd_l_tck = 4; // If WCK1:1:2 mode, 16Bank mode is always used.
		timing->lpddr5_tccd_l_bl32_tck = 8;
		timing->lpddr5_tccd_ps = 4 * tck_ps;
	}

        if (SPD.use_lpddr5x & IS_LPDDR5) {
           timing->lpddr5_trrd_s_ps = (tck_ps<938 /*data_rate == DWC_LPDDR5_9600*/) ? max(3330, 2 * tck_ps):  max(3750, 2 * tck_ps); //JESD209-5B, Table 386
           timing->lpddr5_trrd_l_ps = (tck_ps<938 /*data_rate == DWC_LPDDR5_9600*/) ? max(3330, 2 * tck_ps):  max(3750, 2 * tck_ps); //JESD209-5B, Table 386
        } else {
           timing->lpddr5_trrd_s_ps = max(5000, 2 * tck_ps);
           timing->lpddr5_trrd_l_ps = max(5000, 2 * tck_ps);
        }

           timing->lpddr5_trrd_ps = max(10000, 2 * tck_ps);     // 8Bank mode
                                                                // Didn't add this to lpddr5x check as 8B mode not supported in lpddr5x

        //timing->lpddr5_tfaw_ps = (SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 20000 : 40000; // not supported 8Bank mode for now
        if (SPD.use_lpddr5x & IS_LPDDR5) {
           timing->lpddr5_tfaw_ps =  (tck_ps<938 /*data_rate == DWC_LPDDR5_9600*/) ? 13320 : 15000;      // LPDDR5X value //JESD209-5B, Table 386
        } else {
           timing->lpddr5_tfaw_ps = 20000;      // LPDDR5 value
        }

	timing->lpddr5_trtp_ps = (ratio == DWC_RATIO_WCK_CK_4_1) ? max(7500, 2 * tck_ps) : max(7500, 4 * tck_ps);

    timing->lpddr5_derated_trcd_ps = timing->lpddr5_trcd_ps + 1875;
    timing->lpddr5_derated_trcd_write_ps = timing->lpddr5_trcd_write_ps + 1875;
    timing->lpddr5_derated_tras_min_ps = timing->lpddr5_tras_min_ps + 1875;
    timing->lpddr5_derated_trpab_ps = timing->lpddr5_trpab_ps + 1875;
    timing->lpddr5_derated_trppb_ps = timing->lpddr5_trppb_ps + 1875;
    timing->lpddr5_derated_trrd_ps = timing->lpddr5_trrd_ps + 1875;
    timing->lpddr5_derated_trcab_ps = timing->lpddr5_tras_min_ps + timing->lpddr5_trpab_ps + 3750;
    timing->lpddr5_derated_trcpb_ps = timing->lpddr5_tras_min_ps + timing->lpddr5_trppb_ps + 3750;

	if (IS_X8(n) || lpddr_mixed_pkg_en) {
		if (wr_lecc == 0) {
			timing->lpddr5_twr_ps =
				(dvfsc_type == 0) ? max(36000, 3 * tck_ps) :
				(dvfsc_type == 1) ? max(43000, 3 * tck_ps) :
				 										max(43000, 3 * tck_ps);
			timing->lpddr5_twtr_s_ps = max(8250, 4 * tck_ps);
			timing->lpddr5_twtr_l_ps = max(14000, 4 * tck_ps);
			timing->lpddr5_twtr_ps =
				(dvfsc_type == 0) ? max(14000, 4 * tck_ps) :
				(dvfsc_type == 1) ? max(21000, 4 * tck_ps) :
														max(21000, 4 * tck_ps);
		} else {
			// Link-ECC is enabled
			timing->lpddr5_twr_ps = max(40000, 3 * tck_ps);
			timing->lpddr5_twtr_s_ps = max(12250, 4 * tck_ps);
			timing->lpddr5_twtr_l_ps = max(18000, 4 * tck_ps);
			timing->lpddr5_twtr_ps = max(18000, 4 * tck_ps);
		}
	} else {
		if (wr_lecc == 0) {
			timing->lpddr5_twr_ps =
				(dvfsc_type == 0) ? max(34000, 3 * tck_ps) :
				(dvfsc_type == 1) ? max(41000, 3 * tck_ps) :
														max(41000, 3 * tck_ps);
			timing->lpddr5_twtr_s_ps = max(6250, 4 * tck_ps);
			timing->lpddr5_twtr_l_ps = max(12000, 4 * tck_ps);
			timing->lpddr5_twtr_ps =
				(dvfsc_type == 0) ? max(12000, 4 * tck_ps) :
				(dvfsc_type == 1) ? max(19000, 4 * tck_ps) :
														max(19000, 4 * tck_ps);
		} else {
			// Link-ECC is enabled
			timing->lpddr5_twr_ps = max(38000, 3 * tck_ps);
			timing->lpddr5_twtr_s_ps = max(10250, 4 * tck_ps);
			timing->lpddr5_twtr_l_ps = max(16000, 4 * tck_ps);
			timing->lpddr5_twtr_ps = max(16000, 4 * tck_ps);
		}
	}
	timing->lpddr5_tppd_tck = 2;
	timing->lpddr5_tccdmw_tck = (SPD.lpddr5_data_rate < DWC_LPDDR5_9600) ?  4 * timing->lpddr5_tccd_l_tck : 5 * timing->lpddr5_tccd_l_tck ; //JESD209-B, table 226 - tCCDMW, Masked write cmd supports only BL16 in 16B or BG mode
	timing->lpddr5_tccdmw_bl32_tck = (SPD.lpddr5_data_rate < DWC_LPDDR5_9600) ?  2.5 * timing->lpddr5_tccd_l_bl32_tck : 3 * timing->lpddr5_tccd_l_bl32_tck ; //JESD 1854.99C, table 340 - tCCDMW, Masked write cmd supports only BL16 in 16B or BG mode
	if (ratio == DWC_RATIO_WCK_CK_2_1)
		timing->lpddr5_tmrr_tck = 8;
	else
		timing->lpddr5_tmrr_tck = 4;
	timing->lpddr5_tmrw_ps = max(10000, 5 * tck_ps);
   timing->lpddr5_tmrd_ps = max(14000, 5 * tck_ps); //Max(14 ns, 5nCK) in Table 229 of JESD209-5A
    // Table 112
    timing->lpddr5_odton_min_ps = 1500;
    timing->lpddr5_odton_max_ps = dvfsc_type==2 ? 3900 : 3500;
    timing->lpddr5_odtoff_min_ps = 1500;
    timing->lpddr5_odtoff_max_ps = dvfsc_type==2 ? 3900 : 3500;
    // Table 217 (JESD209-5), Table 259 (JESD209-5A)
    timing->lpddr5_odt_rdon_min_ps = 1500;
    timing->lpddr5_odt_rdon_max_ps = dvfsc_type==2 ? 3900 : 3500;
    timing->lpddr5_odt_rdoff_min_ps = 1500;
    timing->lpddr5_odt_rdoff_max_ps = dvfsc_type==2 ? 3900 : 3500;

	timing->lpddr5_tzqreset_ps = max(50000, 3 * tck_ps);
	timing->lpddr5_tzqlat_ps = max(30000, 4 * tck_ps);
	timing->lpddr5_tzqstop_ps = 50000;	//Ref Table :104
	timing->lpddr5_tzqoff_us = 50;
	timing->lpddr5_tzqcal_ps = 1500000;	// 1.5us - bug 8257
	timing->lpddr5_tvrcg_enable_ps = 150000;
	timing->lpddr5_tvrcg_disable_ps = 100000;
	// 7.1 Effective Burst Length definition
	// here we do not account for 8B mode
	if (ratio == DWC_RATIO_WCK_CK_2_1) {
		timing->lpddr5_bl_n_min_tck = 4;
		timing->lpddr5_bl_n_max_tck = 4;
		timing->lpddr5_bl_n_min_bl32_tck = 8;
		timing->lpddr5_bl_n_max_bl32_tck = 8;
	} else {
		if (SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) {
			timing->lpddr5_bl_n_min_tck = 2;
			timing->lpddr5_bl_n_max_tck = 4;
			timing->lpddr5_bl_n_min_bl32_tck = 6;
			timing->lpddr5_bl_n_max_bl32_tck = 8;
		} else {
			timing->lpddr5_bl_n_min_tck = 2;
			timing->lpddr5_bl_n_max_tck = 2;
			timing->lpddr5_bl_n_min_bl32_tck = 4;
			timing->lpddr5_bl_n_max_bl32_tck = 4;
		}
	}

   timing->lpddr5_twckstop_ps = max(2 * tck_ps, 6000);

	if (dvfsc_type == 1) {	// DVFSC enable
		if (is_x16_val) {
			if (ratio == DWC_RATIO_WCK_CK_2_1) {
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 6;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 6;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 8 : 10;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 0 : 2;
					timing->lpddr5_wckpre_toggle_rd_tck = 7;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = 12;
					timing->lpddr5_wckenl_rd_tck = 3;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
					break;
				}
			} else {
				// x16 DWC_RATIO_WCK_CK_4_1
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 3;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 3;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 4 : 5;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 0 : 1;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = 6;
					timing->lpddr5_wckenl_rd_tck = 2;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
					break;
				}
			}
		} else {
			// X8
			if (ratio == DWC_RATIO_WCK_CK_2_1) {
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 6;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 6;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = 10;
					timing->lpddr5_wckenl_rd_tck = 2;
					timing->lpddr5_wckpre_toggle_rd_tck = 7;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 12 : 14;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 3 : 5;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
					break;
				}
			} else {
				// x8 DWC_RATIO_WCK_CK_4_1
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 3;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 3;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = 5;
					timing->lpddr5_wckenl_rd_tck = 1;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 6 : 7;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 2 : 3;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
					break;
				}
			}
		}
	} else if (dvfsc_type == 2) {	// Enhanced DVFSC enable
		if (is_x16_val) {
			if (ratio == DWC_RATIO_WCK_CK_2_1) {
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 6;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 6;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 9 : 10;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 1 : 2;
					timing->lpddr5_wckpre_toggle_rd_tck = 7;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = 13;
					timing->lpddr5_wckenl_rd_tck = 4;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				case DWC_LPDDR5_2133:
					timing->lpddr5_rl_tck = 16;
					timing->lpddr5_wckenl_rd_tck = 6;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				case DWC_LPDDR5_2750:
					timing->lpddr5_rl_tck = 20;
					timing->lpddr5_wckenl_rd_tck = 7;
					timing->lpddr5_wckpre_toggle_rd_tck = 10;
					break;
				case DWC_LPDDR5_3200:
					timing->lpddr5_rl_tck = 24;
					timing->lpddr5_wckenl_rd_tck = 11;
					timing->lpddr5_wckpre_toggle_rd_tck = 10;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
					break;
				}
			} else {
				// x16 DWC_RATIO_WCK_CK_4_1
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 3;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 3;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = 5;
					timing->lpddr5_wckenl_rd_tck = 1;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = 7;
					timing->lpddr5_wckenl_rd_tck = 3;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_2133:
					timing->lpddr5_rl_tck = 8;
					timing->lpddr5_wckenl_rd_tck = 3;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_2750:
					timing->lpddr5_rl_tck = 10;
					timing->lpddr5_wckenl_rd_tck = 4;
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				case DWC_LPDDR5_3200:
					timing->lpddr5_rl_tck = 12;
					timing->lpddr5_wckenl_rd_tck = 6;
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
					break;
				}
			}
		} else {
			// X8
			if (ratio == DWC_RATIO_WCK_CK_2_1) {
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 6;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 6;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = 10;
					timing->lpddr5_wckenl_rd_tck = 2;
					timing->lpddr5_wckpre_toggle_rd_tck = 7;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 13 : 14;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 4 : 5;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				case DWC_LPDDR5_2133:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 16 : 20;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 6 : 10;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				case DWC_LPDDR5_2750:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 20 : 24;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 7 : 11;
					timing->lpddr5_wckpre_toggle_rd_tck = 10;
					break;
				case DWC_LPDDR5_3200:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 24 : 28;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 11 : 15;
					timing->lpddr5_wckpre_toggle_rd_tck = 10;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
					break;
				}
			} else {
				// x8 DWC_RATIO_WCK_CK_4_1
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 3;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 3;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = 5;
					timing->lpddr5_wckenl_rd_tck = 1;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = 7;
					timing->lpddr5_wckenl_rd_tck = 3;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_2133:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 8 : 10;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 3 : 5;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_2750:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 10 : 12;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 4 : 6;
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				case DWC_LPDDR5_3200:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 12 : 14;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 6 : 8;
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
					break;
				}
			}
		}
	} else {
		//
		// READ LATENCIES (DVFSC disabled first)
		//
		if (is_x16_val) {
			if (ratio == DWC_RATIO_WCK_CK_2_1) {
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 6;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 6;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = 8;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 7;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = 10;
					timing->lpddr5_wckenl_rd_tck = 1;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				case DWC_LPDDR5_2133:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 12 : 14;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 2 : 4;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				case DWC_LPDDR5_2750:
					timing->lpddr5_rl_tck = 16;
					timing->lpddr5_wckenl_rd_tck = 3;
					timing->lpddr5_wckpre_toggle_rd_tck = 10;
					break;
				case DWC_LPDDR5_3200:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 18 : 20;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 5 : 7;
					timing->lpddr5_wckpre_toggle_rd_tck = 10;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
					break;
				}
			} else {
				// x16 DWC_RATIO_WCK_CK_4_1
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 3;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 3;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = 4;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = 5;
					timing->lpddr5_wckenl_rd_tck = 1;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_2133:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 6 : 7;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 1 : 2;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_2750:
					timing->lpddr5_rl_tck = 8;
					timing->lpddr5_wckenl_rd_tck = 2;
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				case DWC_LPDDR5_3200:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 9 : 10;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 3 : 4;
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				case DWC_LPDDR5_3733:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 10 : 11;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 3 : 4;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 12;
						timing->lpddr5_wckenl_rd_tck = 5;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				case DWC_LPDDR5_4267:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 12 : 13;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 4 : 5;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 13;
						timing->lpddr5_wckenl_rd_tck = 5;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 6;

                    break;
                case DWC_LPDDR5_4800:
                    if (rd_lecc == 0) {
                        timing->lpddr5_rl_tck = (read_dbi == 0) ? 13 : 14;
                        timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 5 : 6;
                    } else {
                        // Link-ECC is enabled.
                        timing->lpddr5_rl_tck = 15;
                        timing->lpddr5_wckenl_rd_tck = 7;
                    }
                    timing->lpddr5_wckpre_toggle_rd_tck = 6;

					break;
				case DWC_LPDDR5_5500:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 15 : 16;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 6 : 7;
					} else {
						timing->lpddr5_wckpre_toggle_rd_tck = 6;
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 17;
						timing->lpddr5_wckenl_rd_tck = 8;
					}
					break;
				case DWC_LPDDR5_6000:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 16 : 17;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 6 : 7;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 18;
						timing->lpddr5_wckenl_rd_tck = 8;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 7;
					break;
				case DWC_LPDDR5_6400:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 17 : 18;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 7 : 8;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 19;
						timing->lpddr5_wckenl_rd_tck = 9;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 7;
					break;
				case DWC_LPDDR5_7500:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 20 : 22;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 7 : 9;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 23;
						timing->lpddr5_wckenl_rd_tck = 10;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 9;
					break;
				case DWC_LPDDR5_8533:
					if (rd_lecc == 0) {
						// JESD209-5B,Table 201 — WCK2CK Sync AC Parameters for Read operation
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 23 : 25;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 8 : 10;
					} else {
						// Link-ECC is enabled.
						// JESD209-5B,Table 203 — WCK2CK Sync AC Parameters for Read operation
						timing->lpddr5_rl_tck = 26;
						timing->lpddr5_wckenl_rd_tck = 11;
					}
					// JESD209-5B,Table 201 — WCK2CK Sync AC Parameters for Read operation
					timing->lpddr5_wckpre_toggle_rd_tck = 10;
					break;
				case DWC_LPDDR5_9600: //tg426_9^20230303^1877.16^Micron^LPDDR5X_WCK2CK_Sync_RD_9600.pdf
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 25 : 28;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 8 : 11;
					} else {
						timing->lpddr5_rl_tck = 29;
						timing->lpddr5_wckenl_rd_tck = 12;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 11;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
					break;
				}
			}
		} else {
			// X8
			if (ratio == DWC_RATIO_WCK_CK_2_1) {
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 6;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 6;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = 8;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 7;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 10 : 12;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 1 : 3;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				case DWC_LPDDR5_2133:
					timing->lpddr5_rl_tck = 14;
					timing->lpddr5_wckenl_rd_tck = 4;
					timing->lpddr5_wckpre_toggle_rd_tck = 8;
					break;
				case DWC_LPDDR5_2750:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 16 : 18;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 3 : 5;
					timing->lpddr5_wckpre_toggle_rd_tck = 10;
					break;
				case DWC_LPDDR5_3200:
					timing->lpddr5_rl_tck = 20;
					timing->lpddr5_wckenl_rd_tck = 7;
					timing->lpddr5_wckpre_toggle_rd_tck = 10;
					break;
				default:
					SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
					break;
				}
			} else {
				// x8 DWC_RATIO_WCK_CK_4_1
				switch (l_lpddr5_data_rate[p]) {
				case DWC_LPDDR5_533:
					timing->lpddr5_rl_tck = 3;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 3;
					break;
				case DWC_LPDDR5_1067:
					timing->lpddr5_rl_tck = 4;
					timing->lpddr5_wckenl_rd_tck = 0;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_1600:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 5 : 6;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 1 : 2;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_2133:
					timing->lpddr5_rl_tck = 7;
					timing->lpddr5_wckenl_rd_tck = 2;
					timing->lpddr5_wckpre_toggle_rd_tck = 4;
					break;
				case DWC_LPDDR5_2750:
					timing->lpddr5_rl_tck = (read_dbi == 0) ? 8 : 9;
					timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 2 : 3;
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				case DWC_LPDDR5_3200:
					timing->lpddr5_rl_tck = 10;
					timing->lpddr5_wckenl_rd_tck = 4;
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				case DWC_LPDDR5_3733:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 11 : 12;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 4 : 5;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 13;
						timing->lpddr5_wckenl_rd_tck = 6;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 5;
					break;
				case DWC_LPDDR5_4267:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 13 : 14;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 5 : 6;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 14;
						timing->lpddr5_wckenl_rd_tck = 6;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 6;
					break;
				case DWC_LPDDR5_4800:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 14 : 15;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 6 : 7;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 16;
						timing->lpddr5_wckenl_rd_tck = 8;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 6;
					break;
				case DWC_LPDDR5_5500:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 16 : 17;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 7 : 8;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 18;
						timing->lpddr5_wckenl_rd_tck = 9;
					}
					timing->lpddr5_wckpre_toggle_rd_tck = 6;
					break;
				case DWC_LPDDR5_6000:
					if (rd_lecc == 0) {
						timing->lpddr5_rl_tck = (read_dbi == 0) ? 17 : 19;
						timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 7 : 9;
					} else {
						// Link-ECC is enabled.
						timing->lpddr5_rl_tck = 20;
						timing->lpddr5_wckenl_rd_tck = 10;
					}

                    timing->lpddr5_wckpre_toggle_rd_tck = 7;
                    break;
                case DWC_LPDDR5_6400:
                    if (rd_lecc == 0) {
                        timing->lpddr5_rl_tck = (read_dbi == 0) ? 18 : 20;
                        timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 8 : 10;
                    } else {
                        // Link-ECC is enabled.
                        timing->lpddr5_rl_tck = 21;
                        timing->lpddr5_wckenl_rd_tck = 11;
                    }

                    timing->lpddr5_wckpre_toggle_rd_tck = 7;
                    break;
                case DWC_LPDDR5_7500:
                    if (rd_lecc == 0) {
                        timing->lpddr5_rl_tck = (read_dbi == 0) ? 22 : 24;
                        timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 9 : 11;
                    } else {
                        // Link-ECC is enabled.
                        timing->lpddr5_rl_tck = 24;
                        timing->lpddr5_wckenl_rd_tck = 11;
                    }

                    timing->lpddr5_wckpre_toggle_rd_tck = 9;
                    break;
                case DWC_LPDDR5_8533:
                    if (rd_lecc == 0) {
                   // JESD209-5B,Table 201 — WCK2CK Sync AC Parameters for Read operation
                        timing->lpddr5_rl_tck = (read_dbi == 0) ? 25 : 26;
                        timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 10 : 11;
                    } else {
                        // Link-ECC is enabled.
                   // JESD209-5B,Table 203 — WCK2CK Sync AC Parameters for Read operation
                        timing->lpddr5_rl_tck = 28;
                        timing->lpddr5_wckenl_rd_tck = 13;
                    }

                   // JESD209-5B,Table 201 — WCK2CK Sync AC Parameters for Read operation
                    timing->lpddr5_wckpre_toggle_rd_tck = 10;
                    break;
                case DWC_LPDDR5_9600: //tg426_9^20230303^1877.16^Micron^LPDDR5X_WCK2CK_Sync_RD_9600.pdf
                    if (rd_lecc == 0) {
                       timing->lpddr5_rl_tck = (read_dbi == 0) ? 28 : 29;
                       timing->lpddr5_wckenl_rd_tck = (read_dbi == 0) ? 8 : 11;
                    } else {
                       timing->lpddr5_rl_tck = 30;
                       timing->lpddr5_wckenl_rd_tck = 12;
                    }
                    timing->lpddr5_wckpre_toggle_rd_tck = 11;
                    break;
                 default:
                    SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
                    break;
                }
            }
        }
    }

    // self checker
        if (SPD.use_lpddr5x & IS_LPDDR5) {
    CONSTRAIN_INSIDE(timing->lpddr5_rl_tck, 3, 30); //LPDDR5X, 3~30 up to 9600Mbps
        }else if (~SPD.use_lpddr5x & IS_LPDDR5) {
    CONSTRAIN_INSIDE(timing->lpddr5_rl_tck, 3, 21); //LPDDR5, 3~21 for up to 6400Mbps
        }
	//
	// WRITE LATENCIES
	//
	//if (dvfsc_type == 0) {	// Write latency doesn't change depends on dvfsc
		if (ratio == DWC_RATIO_WCK_CK_2_1) {
			// 2:1
			switch (l_lpddr5_data_rate[p]) {
			case DWC_LPDDR5_533:
				timing->lpddr5_wl_tck = 4;
				timing->lpddr5_wckenl_wr_tck = 1;
				break;
			case DWC_LPDDR5_1067:
				timing->lpddr5_wl_tck = (wl_seta) ? 4 : 6;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 0 : 2;
				break;
			case DWC_LPDDR5_1600:
				timing->lpddr5_wl_tck = (wl_seta) ? 6 : 8;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 1 : 2;
				break;
			case DWC_LPDDR5_2133:
				timing->lpddr5_wl_tck = (wl_seta) ? 8 : 10;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 2 : 4;
				break;
			case DWC_LPDDR5_2750:
				timing->lpddr5_wl_tck = (wl_seta) ? 8 : 14;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 1 : 7;
				break;
			case DWC_LPDDR5_3200:
				timing->lpddr5_wl_tck = (wl_seta) ? 10 : 16;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 3 : 9;
				break;
			default:
				SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
				break;
			}
		} else {
			// 4:1
			switch (l_lpddr5_data_rate[p]) {
			case DWC_LPDDR5_533:
				timing->lpddr5_wl_tck = 2;
				timing->lpddr5_wckenl_wr_tck = 0;
				break;
			case DWC_LPDDR5_1067:
				timing->lpddr5_wl_tck = (wl_seta) ? 2 : 3;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 0 : 1;
				break;
			case DWC_LPDDR5_1600:
				timing->lpddr5_wl_tck = (wl_seta) ? 3 : 4;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 1 : 2;
				break;
			case DWC_LPDDR5_2133:
				timing->lpddr5_wl_tck = (wl_seta) ? 4 : 5;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 1 : 2;
				break;
			case DWC_LPDDR5_2750:
				timing->lpddr5_wl_tck = (wl_seta) ? 4 : 7;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 1 : 4;
				break;
			case DWC_LPDDR5_3200:
				timing->lpddr5_wl_tck = (wl_seta) ? 5 : 8;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 2 : 5;
				break;
			case DWC_LPDDR5_3733:
				timing->lpddr5_wl_tck = (wl_seta) ? 6 : 9;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 2 : 5;
				break;
			case DWC_LPDDR5_4267:
				timing->lpddr5_wl_tck = (wl_seta) ? 6 : 11;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 2 : 7;
				break;
			case DWC_LPDDR5_4800:
				timing->lpddr5_wl_tck = (wl_seta) ? 7 : 12;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 3 : 8;
				break;
			case DWC_LPDDR5_5500:
				timing->lpddr5_wl_tck = (wl_seta) ? 8 : 14;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 3 : 9;
				break;
			case DWC_LPDDR5_6000:
				timing->lpddr5_wl_tck = (wl_seta) ? 9 : 15;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 4 : 10;
				break;
			case DWC_LPDDR5_6400:
				timing->lpddr5_wl_tck = (wl_seta) ? 9 : 16;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 4 : 11;
				break;
			case DWC_LPDDR5_7500:
				timing->lpddr5_wl_tck = (wl_seta) ? 11 : 19;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 5 : 13;
				break;
			case DWC_LPDDR5_8533:
				//JESD209-5B,Table 200 — WCK2CK Sync AC Parameters for WRITE operation
				timing->lpddr5_wl_tck = (wl_seta) ? 12 : 22;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 5 : 15;
				break;
			case DWC_LPDDR5_9600:
				//RB23067-LPDDR5X WCK2CK Sync AC Parameters for WRITE.pdf
				//JESD209-5B,Table 200 — WCK2CK Sync AC Parameters for WRITE operation
				timing->lpddr5_wl_tck = (wl_seta) ? 14 : 24;
				timing->lpddr5_wckenl_wr_tck = (wl_seta) ? 6 : 16;
				break;
			default:
				SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
				break;
			}
		}
	//}

	//
	// tWCKENL_FS
	//
	if (ratio == DWC_RATIO_WCK_CK_2_1) {
		// 2:1
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_wckenl_fs_tck = 0;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_wckenl_fs_tck = 0;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_wckenl_fs_tck = 1;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_wckenl_fs_tck = 1;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_wckenl_fs_tck = 1;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_wckenl_fs_tck = 2;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
			break;
		}
	} else {
		// 4:1
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_wckenl_fs_tck = 0;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_wckenl_fs_tck = 0;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_wckenl_fs_tck = 1;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_wckenl_fs_tck = 1;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_wckenl_fs_tck = 1;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_wckenl_fs_tck = 1;
			break;
		case DWC_LPDDR5_3733:
			timing->lpddr5_wckenl_fs_tck = 1;
			break;
		case DWC_LPDDR5_4267:
			timing->lpddr5_wckenl_fs_tck = 1;
			break;
		case DWC_LPDDR5_4800:
			timing->lpddr5_wckenl_fs_tck = 2;
			break;
		case DWC_LPDDR5_5500:
			timing->lpddr5_wckenl_fs_tck = 2;
			break;
		case DWC_LPDDR5_6000:
			timing->lpddr5_wckenl_fs_tck = 2;
			break;
		case DWC_LPDDR5_6400:
			timing->lpddr5_wckenl_fs_tck = 2;
			break;
		case DWC_LPDDR5_7500:
			timing->lpddr5_wckenl_fs_tck = 3;
			break;
		case DWC_LPDDR5_8533:
			//JESD209-5B,Table 204 — WCK2CK Sync AC Parameters for CAS(WS_FS)
			timing->lpddr5_wckenl_fs_tck = 3;
			break;
		case DWC_LPDDR5_9600:
			//RB23069-LPDDR5X WCK2CK Sync AC Parameter for CAS(WS_FS).pdf
			//JESD209-5B,Table 204 — WCK2CK Sync AC Parameters for CAS(WS_FS)
			timing->lpddr5_wckenl_fs_tck = 3;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
			break;
		}
	}

	//
	// nWR LATENCIES
	//
	if (ratio == DWC_RATIO_WCK_CK_2_1) {
		// 2:1
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_nwr = dvfsc_type>0 ? 6 : 5;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 11 : 12) : 10;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 17 : 18) : (is_x16_val ? 14 : 15);
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 22 : 23) : (is_x16_val ? 19 : 20);
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 29 : 30) : (is_x16_val ? 24 : 25);
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 33 : 35) : (is_x16_val ? 28 : 29);
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
			break;
		}
	} else {
		// 4:1
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_nwr = 3;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 6 : 6) : 5;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 9 : 9) : (is_x16_val ? 7 : 8);
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 11 : 12) : 10;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 15 : 15) : (is_x16_val ? 12 : 13);
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_nwr = dvfsc_type>0 ? (is_x16_val ? 17 : 18) : (is_x16_val ? 14 : 15);
			break;
		case DWC_LPDDR5_3733:
			timing->lpddr5_nwr = !wr_lecc ? (is_x16_val ? 16 : 17) : (is_x16_val ? 18 : 19);
			break;
		case DWC_LPDDR5_4267:
			timing->lpddr5_nwr = !wr_lecc ? (is_x16_val ? 19 : 20) : (is_x16_val ? 21 : 22);
			break;
		case DWC_LPDDR5_4800:
			timing->lpddr5_nwr = !wr_lecc ? (is_x16_val ? 21 : 22) : (is_x16_val ? 23 : 24);
			break;
		case DWC_LPDDR5_5500:
			timing->lpddr5_nwr = !wr_lecc ? (is_x16_val ? 24 : 25) : (is_x16_val ? 27 : 28);
			break;
		case DWC_LPDDR5_6000:
			timing->lpddr5_nwr = !wr_lecc ? (is_x16_val ? 26 : 28) : (is_x16_val ? 29 : 31);
			break;
		case DWC_LPDDR5_6400:
			timing->lpddr5_nwr = !wr_lecc ? (is_x16_val ? 28 : 29) : (is_x16_val ? 31 : 32);
			break;
		case DWC_LPDDR5_7500:
			timing->lpddr5_nwr = !wr_lecc ? (is_x16_val ? 32 : 34) : (is_x16_val ? 36 : 38);
			break;
		case DWC_LPDDR5_8533:
			//JESD209-5B,Table 225 — nWR Latency
			timing->lpddr5_nwr = !wr_lecc ? (is_x16_val ? 37 : 39) : (is_x16_val ? 41 : 43);
			break;
		case DWC_LPDDR5_9600:
			//RB23065-LPDDR5X extension Write Latency.pdf
			//JESD209-5B,Table 225 — nWR Latency
			timing->lpddr5_nwr = !wr_lecc ? (is_x16_val ? 41 : 44) : (is_x16_val ? 46 : 48);
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
			break;
		}
	}
	//
	// WCKPRE and WCKENL_RD
	//
	if (ratio == DWC_RATIO_WCK_CK_2_1) {
		// 2:1
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_wckpre_static_tck = 1;
			timing->lpddr5_wckpre_toggle_wr_tck = 3;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_wckpre_static_tck = 2;
			timing->lpddr5_wckpre_toggle_wr_tck = 3;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_wckpre_static_tck = 2;
			timing->lpddr5_wckpre_toggle_wr_tck = 4;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_wckpre_static_tck = 3;
			timing->lpddr5_wckpre_toggle_wr_tck = 4;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_wckpre_static_tck = 4;
			timing->lpddr5_wckpre_toggle_wr_tck = 4;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_wckpre_static_tck = 4;
			timing->lpddr5_wckpre_toggle_wr_tck = 4;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
			break;
		}
	} else {
		// 4:1
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_wckpre_static_tck = 1;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_wckpre_static_tck = 1;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_wckpre_static_tck = 1;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_wckpre_static_tck = 2;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_wckpre_static_tck = 2;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_wckpre_static_tck = 2;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_3733:
			timing->lpddr5_wckpre_static_tck = 3;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_4267:
			timing->lpddr5_wckpre_static_tck = 3;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_4800:
			timing->lpddr5_wckpre_static_tck = 3;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_5500:
			timing->lpddr5_wckpre_static_tck = 4;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_6000:
			timing->lpddr5_wckpre_static_tck = 4;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_6400:
			timing->lpddr5_wckpre_static_tck = 4;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_7500:
			timing->lpddr5_wckpre_static_tck = 5;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_8533:
			//JESD209-5B,Table 200,201,202.203,204 — WCK2CK Sync AC Parameters for WRITE operation
			timing->lpddr5_wckpre_static_tck = 6;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		case DWC_LPDDR5_9600:
			//RB23067-LPDDR5X WCK2CK Sync AC Parameters for WRITE.pdf
			//JESD209-5B,Table 200,201,202.203,204 — WCK2CK Sync AC Parameters for WRITE operation
			timing->lpddr5_wckpre_static_tck = 7;
			timing->lpddr5_wckpre_toggle_wr_tck = 2;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
			break;
		}
	}
	switch (hdlr->memCtrlr_m.lpddr5_mr[p].mr10.wck_pst) {
	case 0:
		timing->lpddr5_twck_pst_wck = 2;
		break;					// RD(2.5)
	case 1:
		timing->lpddr5_twck_pst_wck = 4;
		break;					// RD(4.5)
	case 2:
		timing->lpddr5_twck_pst_wck = 6;
		break;					// RD(6.5)
	default:
		SNPS_ERROR("Unknown wck_pst (%u) value", hdlr->memCtrlr_m.lpddr5_mr[p].mr10.wck_pst);
		break;
	}

	//nRBTP set from speed grade according to Table 201,202,203 Jedec Spec 209-5A
	//There is possibility for mismatch between nRBTP and RU(tRBTP/tCK) please see Bug13474

	//JESD209-5B, table 220
	//Case1: Read Link ECC on & DVFSC Off(MR19 OP[1:0]#=01) & Enhanced DVFSC Off(MR19 OP[1:0]#=10) ->4:1{3733~9600Mbps=same case2}
	//Case2: Read Link ECC off & DVFSC Off & Enhanced DVFSC Off
	//Case3: Read Link ECC off & DVFSC Enable & Enhanced DVFSC Off > all set to 0
	//Case4: Read Link ECC off & DVFSC Off & Enhanced DVFSC Enable -> 2:1{533:1600=0, 2133=2, 2750=3, 3200=4}///  4:1{533:1600=0, 2133=1,2750:3200=2}
	if (rd_lecc==0 && dvfsc_type == 1 ) { //case3
				timing->lpddr5_nrbtp = 0;
        }
	else if (dvfsc_type == 0 || dvfsc_type == 2) { //case1,case2,case4
		if (ratio == DWC_RATIO_WCK_CK_2_1) {
			switch (l_lpddr5_data_rate[p]) {
			case DWC_LPDDR5_533:
				timing->lpddr5_nrbtp = 0;
				break;
			case DWC_LPDDR5_1067:
				timing->lpddr5_nrbtp = 0;
				break;
			case DWC_LPDDR5_1600:
				timing->lpddr5_nrbtp = 0;
				break;
			case DWC_LPDDR5_2133:
				timing->lpddr5_nrbtp = dvfsc_type ==2 ? 2 : 0;
				break;
			case DWC_LPDDR5_2750:
				timing->lpddr5_nrbtp = dvfsc_type ==2 ? 3 : 2;
				break;
			case DWC_LPDDR5_3200:
				timing->lpddr5_nrbtp = dvfsc_type ==2 ? 4 : 2;
				break;
			default:
				SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
				break;
			}
		} else {
			// 4:1
			switch (l_lpddr5_data_rate[p]) {
			case DWC_LPDDR5_533:
				timing->lpddr5_nrbtp = 0;
				break;
			case DWC_LPDDR5_1067:
				timing->lpddr5_nrbtp = 0;
				break;
			case DWC_LPDDR5_1600:
				timing->lpddr5_nrbtp = 0;
				break;
			case DWC_LPDDR5_2133:
				timing->lpddr5_nrbtp = dvfsc_type ==2 ? 1 : 0;
				break;
			case DWC_LPDDR5_2750:
				timing->lpddr5_nrbtp = 1;
				timing->lpddr5_nrbtp = dvfsc_type ==2 ? 2 : 1;
				break;
			case DWC_LPDDR5_3200:
				timing->lpddr5_nrbtp = dvfsc_type ==2 ? 2 : 1;
				break;
			case DWC_LPDDR5_3733:
				timing->lpddr5_nrbtp = 2;
				break;
			case DWC_LPDDR5_4267:
				timing->lpddr5_nrbtp = 2;
				break;
			case DWC_LPDDR5_4800:
				timing->lpddr5_nrbtp = 3;
				break;
			case DWC_LPDDR5_5500:
				timing->lpddr5_nrbtp = 4;
				break;
			case DWC_LPDDR5_6000:
				timing->lpddr5_nrbtp = 4;
				break;
			case DWC_LPDDR5_6400:
				timing->lpddr5_nrbtp = 4;
				break;
			case DWC_LPDDR5_7500:
				timing->lpddr5_nrbtp = 6;
				break;
			case DWC_LPDDR5_8533:
				timing->lpddr5_nrbtp = 6;
				break;
			case DWC_LPDDR5_9600:
				timing->lpddr5_nrbtp = 7;
				break;
			default:
				SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
				break;
			}
		}
	}
	else {
				timing->lpddr5_nrbtp = 0;
	}

	//
	// ODTLon
	//
	if (ratio == DWC_RATIO_WCK_CK_2_1) {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 1;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 2;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 2;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 3;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 3;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 4;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
			break;
		}
	} else {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 1;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 1;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 1;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 2;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 2;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 2;
			break;
		case DWC_LPDDR5_3733:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 2;
			break;
		case DWC_LPDDR5_4267:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 3;
			break;
		case DWC_LPDDR5_4800:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 3;
			break;
		case DWC_LPDDR5_5500:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 3;
			break;
		case DWC_LPDDR5_6000:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 3;
			break;
		case DWC_LPDDR5_6400:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 3;
			break;
		case DWC_LPDDR5_7500:
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 4;
			break;
		case DWC_LPDDR5_8533:
			//JESD209-5B,Table 257 — ODTLon and ODTLoff Latency Values
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 4;
			break;
		case DWC_LPDDR5_9600:
			//RB23071-LPDDR5X ODTLon and ODTLoff Latency Values.pdf
			timing->lpddr5_odtlon_tck = timing->lpddr5_wl_tck - 5;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
			break;
		}
	}
	//BL32
	timing->lpddr5_odtlon_bl32_tck = timing->lpddr5_odtlon_tck;

	//
	// ODTLoff_RD_DQ/RDQS JESD209-5B Table 288 - 290
	//
	if (ratio == DWC_RATIO_WCK_CK_2_1) {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 1;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 2;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 2;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 4;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
			break;
		}
	} else {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 1;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 1;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 1;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 2;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 2;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 2;
			break;
		case DWC_LPDDR5_3733:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 2;
			break;
		case DWC_LPDDR5_4267:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_4800:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_5500:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_6000:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_6400:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_7500:
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 4;
			break;
		case DWC_LPDDR5_8533:
			//JESD209-5B,Table 288- 290
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 4;
			break;
		case DWC_LPDDR5_9600:
                        //ballot RB23072-LPDDR5X NT-ODT Latency Values.pdf
			timing->lpddr5_odtloff_rd_tck = timing->lpddr5_rl_tck - 5;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
			break;
		}
	}
	timing->lpddr5_odtloff_rd_bl32_tck = timing->lpddr5_odtloff_rd_tck;

	//
	// ODTLon_RD_DQ JESD209-5B Table 288 - 290
	//
	if (ratio == DWC_RATIO_WCK_CK_2_1) {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 9;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 9;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 9;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 6;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 10;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 6;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 10;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 6;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 10;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
			break;
		}
	} else {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 3;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 5;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 3;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 5;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 3;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 5;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 3;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 5;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 3;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 5;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 3;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 5;
			break;
		case DWC_LPDDR5_3733:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 3;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 7 : 5);
			break;
		case DWC_LPDDR5_4267:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 8 : 6);
			break;
		case DWC_LPDDR5_4800:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 8 : 6);
			break;
		case DWC_LPDDR5_5500:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 8 : 6);
			break;
		case DWC_LPDDR5_6000:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 8 : 6);
			break;
		case DWC_LPDDR5_6400:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 8 : 6);
			break;
		case DWC_LPDDR5_7500:
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 8;
			break;
		case DWC_LPDDR5_8533:
			//JESD209-5B,Table 288- 290
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 8;
			break;
		case DWC_LPDDR5_9600:
                        //ballot RB23072-LPDDR5X NT-ODT Latency Values.pdf
			timing->lpddr5_odtlon_rd_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_bl32_tck = timing->lpddr5_rl_tck + 8;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
			break;
		}
	}

	//
	// ODTLon_RD_RDQS JESD209-5B Table 288 - 290
	//
	if (ratio == DWC_RATIO_WCK_CK_2_1) {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 7;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 11;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 7;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 11;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 7;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 11;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 8;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 12;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 8;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 12;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 8;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 12;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
			break;
		}
	} else {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 6;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 6;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 6;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 6;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 6;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 6;
			break;
		case DWC_LPDDR5_3733:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 4;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 8 : 6);
			break;
		case DWC_LPDDR5_4267:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 9 : 7);
			break;
		case DWC_LPDDR5_4800:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 9 : 7);
			break;
		case DWC_LPDDR5_5500:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 9 : 7);
			break;
		case DWC_LPDDR5_6000:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 9 : 7);
			break;
		case DWC_LPDDR5_6400:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 9 : 7);
			break;
		case DWC_LPDDR5_7500:
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 9;
			break;
		case DWC_LPDDR5_8533:
			//JESD209-5B,Table 288- 290
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 9;
			break;
		case DWC_LPDDR5_9600:
                        //ballot RB23072-LPDDR5X NT-ODT Latency Values.pdf
			timing->lpddr5_odtlon_rd_rdqs_tck = timing->lpddr5_rl_tck + 5;
			timing->lpddr5_odtlon_rd_rdqs_bl32_tck = timing->lpddr5_rl_tck + 9;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
			break;
		}
	}
	//
	// ODTLoff_RD_RDQS JESD209-5B Table 288 - 290
	//
        //MR10[5:4,1] = 000,010,100
        uint8_t rdqs_pre_1_2 = (hdlr->memCtrlr_m.lpddr5_mr[p].mr10.rdqs_pre < 3) && (hdlr->memCtrlr_m.lpddr5_mr[p].mr10.rdqs_pre_2==0);
	if (ratio == DWC_RATIO_WCK_CK_2_1) {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 4;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 4;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 5;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 5;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 6;
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 2:1)", l_lpddr5_data_rate[p]);
			break;
		}
	} else {
		switch (l_lpddr5_data_rate[p]) {
		case DWC_LPDDR5_533:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 2;
			break;
		case DWC_LPDDR5_1067:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 2;
			break;
		case DWC_LPDDR5_1600:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 2;
			break;
		case DWC_LPDDR5_2133:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_2750:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_3200:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - 3;
			break;
		case DWC_LPDDR5_3733:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - ((rdqs_pre_1_2)? 3 : 4);
			break;
		case DWC_LPDDR5_4267:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - ((rdqs_pre_1_2)? 4 : 5);
			break;
		case DWC_LPDDR5_4800:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - ((rdqs_pre_1_2)? 4 : 5);
			break;
		case DWC_LPDDR5_5500:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - ((rdqs_pre_1_2)? 4 : 5);
			break;
		case DWC_LPDDR5_6000:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - ((rdqs_pre_1_2)? 4 : 5);
			break;
		case DWC_LPDDR5_6400:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - ((rdqs_pre_1_2)? 4 : 5);
			break;
		case DWC_LPDDR5_7500:
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - ((rdqs_pre_1_2)? 5 : 6);
			break;
		case DWC_LPDDR5_8533:
			//JESD209-5B,Table 288- 290
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - ((rdqs_pre_1_2)? 5 : 6);
			break;
		case DWC_LPDDR5_9600:
                        //ballot RB23072-LPDDR5X NT-ODT Latency Values.pdf
			timing->lpddr5_odtloff_rd_rdqs_tck = timing->lpddr5_rl_tck - ((rdqs_pre_1_2)? 6 : 7);
			break;
		default:
			SNPS_ERROR("Unknown data rate = %u (WCK:CK 4:1)", l_lpddr5_data_rate[p]);
			break;
		}
	}
	timing->lpddr5_odtloff_rd_rdqs_bl32_tck = timing->lpddr5_odtloff_rd_rdqs_tck;

    //
    // tRTW
    //
    // Programming tRTW defined in JEDEC209-5A
    // Table 327-329
    // todo prepare other pattern with separate RDQS and DQODT

	uint8_t rdqs_t_adj, same_nt_odt_adj, dfe_disable_adj;
	//todo add MR26 WCK_RDQS_training mode to if condition
	if (wr_lecc == 0 && hdlr->memCtrlr_m.lpddr5_mr[p].mr46.enh_rdqs == 0 && hdlr->memCtrlr_m.lpddr5_mr[p].mr26.dwck_rdws_train == 0)
		rdqs_t_adj = 0;
	else
		rdqs_t_adj = 1;
        SNPS_LOG("wr_lecc = %d,  mr46.enh_rdqs = %d,rdqs_t_adj = %d  ",wr_lecc, hdlr->memCtrlr_m.lpddr5_mr[p].mr46.enh_rdqs,rdqs_t_adj);
	//todo MR0[0] support
	if (hdlr->memCtrlr_m.lpddr5_mr[p].mr0.enhanced_nt_odt == 0 && rdqs_t_adj == 0)
		same_nt_odt_adj = 1; //same DQ/RDQS NT-ODT
	else
		same_nt_odt_adj = 0; //separate DQ/RDQS NT-ODT

        SNPS_LOG("mr0.enhanced_nt_odt = %d, same_nt_odt_adj = %d",hdlr->memCtrlr_m.lpddr5_mr[p].mr0.enhanced_nt_odt,same_nt_odt_adj);
        //JESD209-5B, Need to add 1nCK to tRTW in case of not “MR24 OP[2:0]=000B and MR24 OP[6:4]=000B” :(In case of DFEQL and/or DFEQU is enabled).
	if ((hdlr->memCtrlr_m.lpddr5_mr[p].mr24.dfeql ==0) && (hdlr->memCtrlr_m.lpddr5_mr[p].mr24.dfequ ==0))
		dfe_disable_adj = 0; //"MR24 OP[2:0]=000B and MR24 OP[6:4]=000B", NOT add 1nCK to tRTW
	else
		dfe_disable_adj = 1; //

        SNPS_LOG("mr24.dfequ = %d, mr24.dfeql = %d, dfe_disable_adj = %d",hdlr->memCtrlr_m.lpddr5_mr[p].mr24.dfequ,hdlr->memCtrlr_m.lpddr5_mr[p].mr24.dfeql,dfe_disable_adj);
	if (SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) {
		// BG mode
		if (hdlr->memCtrlr_m.lpddr5_mr[p].mr20.rdqs != 0) {  //MR20[1:0]==0: RDQS_t and RDQS_c disabled
			if (hdlr->memCtrlr_m.lpddr5_mr[p].mr41.nt_dq_odt == 0) {
				if (hdlr->memCtrlr_m.lpddr5_mr[p].mr11.dq_odt == 0) {
					// RDQS enable & NT-ODT disable & ODT disable
					// RL+BL/n_max+RU(tWCK2DQO(max)/tCK)-WL+1
					timing->lpddr5_trtw_tck   = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + rdqs_t_adj + dfe_disable_adj;
					timing->lpddr5_trtw_s_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + rdqs_t_adj + dfe_disable_adj;
					timing->lpddr5_trtw_bl32_tck   = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + rdqs_t_adj + dfe_disable_adj;
					timing->lpddr5_trtw_s_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + rdqs_t_adj + dfe_disable_adj;
				} else {
					// RDQS enable & NT-ODT disable & ODT enable
					// RL+BL/n_max+RU(tWCK2DQO(max)/tCK)+RD(tRPST/tCK)-ODTLon-RD(tODTon(min)/tCK)+1+1
					timing->lpddr5_trtw_tck   = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + rdqs_t_adj;
					timing->lpddr5_trtw_s_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + rdqs_t_adj;
					timing->lpddr5_trtw_bl32_tck   = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_bl32_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + rdqs_t_adj;
					timing->lpddr5_trtw_s_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_bl32_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + rdqs_t_adj;
				}
			} else {
				if (hdlr->memCtrlr_m.lpddr5_mr[p].mr11.dq_odt == 0) {
					// RDQS enable & NT-ODT enable & ODT disable
					// RL+BL/n_max+RU(tWCK2DQO(max)/tCK)-WL+1
					timing->lpddr5_trtw_tck   = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + rdqs_t_adj + dfe_disable_adj;
					timing->lpddr5_trtw_s_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + rdqs_t_adj + dfe_disable_adj;
					timing->lpddr5_trtw_bl32_tck   = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + rdqs_t_adj + dfe_disable_adj;
					timing->lpddr5_trtw_s_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + rdqs_t_adj + dfe_disable_adj;

				} else {
					// RDQS enable & NT-ODT enable & ODT enable
					// RL+BL/n_max+RU(tWCK2DQO(max)/tCK)+RD(tRPST/tCK)-ODTLon-RD(tODTon(min)/tCK)+1+1
					timing->lpddr5_trtw_tck   = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + same_nt_odt_adj;
					timing->lpddr5_trtw_s_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + same_nt_odt_adj;
					timing->lpddr5_trtw_bl32_tck   = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_bl32_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + same_nt_odt_adj;
					timing->lpddr5_trtw_s_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_bl32_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + same_nt_odt_adj;
					}
			}
		} else {
			SNPS_ERROR("RDQS cannot be disabled in BG mode MR20 = %d", hdlr->memCtrlr_m.lpddr5_mr[p].mr20.rdqs);
		}
	} else {
		// Bank mode
		if (hdlr->memCtrlr_m.lpddr5_mr[p].mr20.rdqs == 0) { //MR20[1:0]==0: RDQS_t and RDQS_c disabled
			if (hdlr->memCtrlr_m.lpddr5_mr[p].mr41.nt_dq_odt == 0) {
				if (hdlr->memCtrlr_m.lpddr5_mr[p].mr11.dq_odt == 0) {
					// RDQS disable & NT-ODT disable & ODT disable both 4:1 and 2:1
					// RL+BL/n+RU(tWCK2DQO(max)/tCK)-WL +dfe_disable_adj
					timing->lpddr5_trtw_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + dfe_disable_adj ;
					timing->lpddr5_trtw_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + dfe_disable_adj ;
				} else {
					// RDQS disable & NT-ODT disable & ODT enable both 4:1 and 2:1
					// RL+BL/n+RU(tWCK2DQO(max)/tCK)+RD(tRPST/tCK)-ODTLon-RD(tODTon(min)/tCK)+1
					timing->lpddr5_trtw_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1;
					timing->lpddr5_trtw_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_bl32_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1;
				}
			} else {
				if (hdlr->memCtrlr_m.lpddr5_mr[p].mr11.dq_odt == 0) {
					// RDQS disable & NT-ODT enable & ODT disable both 4:1 and 2:1
					// RL+BL/n+RU(tWCK2DQO(max)/tCK)-WL +dfe_disable_adj
					timing->lpddr5_trtw_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + dfe_disable_adj ;
					timing->lpddr5_trtw_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + dfe_disable_adj ;
				} else {
					// RDQS disable & NT-ODT enable & ODT enable both 4:1 and 2:1
					// RL+BL/n+RU(tWCK2DQO(max)/tCK)+RD(tRPST/tCK)-ODTLon-RD(tODTon(min)/tCK)+1
					timing->lpddr5_trtw_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1;
					timing->lpddr5_trtw_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_bl32_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1;
					}
			}
		} else {
			if (hdlr->memCtrlr_m.lpddr5_mr[p].mr41.nt_dq_odt == 0) {
				if (hdlr->memCtrlr_m.lpddr5_mr[p].mr11.dq_odt == 0) {
					// RDQS enable & NT-ODT disable & ODT disable both 4:1 and 2:1
					// RL+BL/n+RU(tWCK2DQO(max)/tCK)-WL +dfe_disable_adj
					timing->lpddr5_trtw_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + dfe_disable_adj;
                    timing->lpddr5_trtw_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + dfe_disable_adj;
					if ((ratio_factor == 4) && (rdqs_t_adj == 1)) { //RDQS_t as input
						timing->lpddr5_trtw_tck += 1;
						timing->lpddr5_trtw_bl32_tck += 1;
					}
				} else {
					// RDQS enable & NT-ODT disable & ODT enable both 4:1 and 2:1
					// RL+BL/n+RU(tWCK2DQO(max)/tCK)+RD(tRPST/tCK)-ODTLon-RD(tODTon(min)/tCK)+1
					timing->lpddr5_trtw_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1;
                    timing->lpddr5_trtw_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_bl32_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1;					
                    if ((ratio_factor == 4) && (rdqs_t_adj == 1)) { //RDQS_t as input
						timing->lpddr5_trtw_tck += 1;
						timing->lpddr5_trtw_bl32_tck += 1;
					}
				}
			} else {
				if (hdlr->memCtrlr_m.lpddr5_mr[p].mr11.dq_odt == 0) {
					// RDQS enable & NT-ODT enable & ODT disable both 4:1 and 2:1
					// RL+BL/n+RU(tWCK2DQO(max)/tCK)-WL + dfe_disable_adj
					timing->lpddr5_trtw_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + dfe_disable_adj;
                    timing->lpddr5_trtw_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - timing->lpddr5_wl_tck + dfe_disable_adj;
					if ((ratio_factor == 4) && (rdqs_t_adj == 1)) { //RDQS_t as input
						timing->lpddr5_trtw_tck += 1;
						timing->lpddr5_trtw_bl32_tck += 1;
					}
				} else {
					// RDQS enable & NT-ODT enable & ODT enable
					// [4:1] RL+BL/n+RU(tWCK2DQO(max)/tCK)+RD(tRPST/tCK)-ODTLon-RD(tODTon(min)/tCK)+1+1
					// [2:1] RL+BL/n+RU(tWCK2DQO(max)/tCK)+RD(tRPST/tCK)-ODTLon-RD(tODTon(min)/tCK)+1+2
					timing->lpddr5_trtw_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + (4 / ratio_factor) * same_nt_odt_adj;
					timing->lpddr5_trtw_bl32_tck = timing->lpddr5_rl_tck + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + (timing->lpddr5_trpst / tck_ps) - timing->lpddr5_odtlon_bl32_tck - (timing->lpddr5_odton_min_ps / tck_ps) + 1 + (4 / ratio_factor) * same_nt_odt_adj;
					}
			}
		}
		timing->lpddr5_trtw_s_tck = timing->lpddr5_trtw_tck;
		timing->lpddr5_trtw_s_bl32_tck = timing->lpddr5_trtw_bl32_tck;
	}
	//JESD209-5C:table 347: NOTE 5 Need to add 1nCK to tRTW in case of Per-pin DFE Control:MR41 OP[0]=1B: (In case of Per Pin DFE is enabled).
	if (hdlr->memCtrlr_m.lpddr5_mr[p].mr41.pdfec == 1) {
		timing->lpddr5_trtw_s_tck += 1;
		timing->lpddr5_trtw_tck   += 1;
	}


    SNPS_LOG("lpddr5_bk_bg_org = %u ,mr20.rdqs = %d, mr41.nt_dq_odt = %d, mr11.dq_odt = %d, pdfec= %d,lpddr5_trtw_tck = %d ps,lpddr5_trtw_s_tck = %d ps",SPD.lpddr5_bk_bg_org[p],hdlr->memCtrlr_m.lpddr5_mr[p].mr20.rdqs,hdlr->memCtrlr_m.lpddr5_mr[p].mr41.nt_dq_odt,hdlr->memCtrlr_m.lpddr5_mr[p].mr11.dq_odt,hdlr->memCtrlr_m.lpddr5_mr[p].mr41.pdfec, timing->lpddr5_trtw_tck, timing->lpddr5_trtw_s_tck);
    SNPS_LOG("lpddr5_trtw_bl32_tck = %d ps,lpddr5_trtw_s_bl32_tck = %d ps",timing->lpddr5_trtw_bl32_tck, timing->lpddr5_trtw_s_bl32_tck);
    SNPS_TRACE("Leaving");
}

//Map tck_ps to local variables l_lpddr5/4_data_rate and l_ddr5/4_data_rate
void dwc_cinit_map_tck_ps_to_data_rate(SubsysHdlr_t *hdlr)
{
    switch (SPD.sdram_protocol) {
        case DWC_LPDDR4:
            map_tck_ps_to_l_lpddr4_data_rate(hdlr);
            break;
        case DWC_LPDDR5:
            map_tck_ps_to_l_lpddr5_data_rate(hdlr);
            break;
        default:
            SNPS_ERROR("Protocol (%s) not supported",
                       ddrctl_sw_get_protocol_str(DDRCTL_GET_PROTOCOL(hdlr)));
            break;
    }
}

//Map tck_ps to l_lpddr4_data_rate
void map_tck_ps_to_l_lpddr4_data_rate(SubsysHdlr_t *hdlr)
{
    SNPS_TRACE("Entering");

	for (uint32_t p = 0; p < hdlr->num_pstates; p++) {
		if (RANGE(SPD.tck_ps[p], 3760, 3763))
			l_lpddr4_data_rate[p] = DWC_LPDDR4_533;
		else if (RANGE(SPD.tck_ps[p], 1875, 3759))
			l_lpddr4_data_rate[p] = DWC_LPDDR4_1066;
		else if (RANGE(SPD.tck_ps[p], 1250, 1874))
			l_lpddr4_data_rate[p] = DWC_LPDDR4_1600;
		else if (RANGE(SPD.tck_ps[p], 938, 1249))
			l_lpddr4_data_rate[p] = DWC_LPDDR4_2133;
		else if (RANGE(SPD.tck_ps[p], 750, 937))
			l_lpddr4_data_rate[p] = DWC_LPDDR4_2667;
		else if (RANGE(SPD.tck_ps[p], 625, 749))
			l_lpddr4_data_rate[p] = DWC_LPDDR4_3200;
		else if (RANGE(SPD.tck_ps[p], 536, 624))
			l_lpddr4_data_rate[p] = DWC_LPDDR4_3733;
		else if (RANGE(SPD.tck_ps[p], 469, 535))
			l_lpddr4_data_rate[p] = DWC_LPDDR4_4267; // 1/((4267/2)*10^6) = 468.71ps
		else
			SNPS_ERROR("Invalid tck_ps[%u] = %u not supported", p, SPD.tck_ps[p]);
		SNPS_LOG("tck_ps[%u] = %u ps and l_lpddr4_data_rate[%u] = %u", p, SPD.tck_ps[p], p, l_lpddr4_data_rate[p]);
	}
	SNPS_TRACE("Leaving");
}

//Map tck_ps to l_lpddr5_data_rate
void map_tck_ps_to_l_lpddr5_data_rate(SubsysHdlr_t *hdlr)
{
	for (uint32_t p = 0; p < hdlr->num_pstates; p++) {

		if (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1) {
			if (RANGE(SPD.tck_ps[p], 834, 937))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_9600; // >883.3 MHz - <=937.6 MHz
			else if (RANGE(SPD.tck_ps[p], 938, 1066))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_8533; // >937.5 MHz - <=1066.5 MHz
			else if (RANGE(SPD.tck_ps[p], 1067, 1249))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_7500; // >800 MHz - <=937.5 MHz
			else if (RANGE(SPD.tck_ps[p], 1250, 1333))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_6400; // >750 MHz - <=800 MHz
			else if (RANGE(SPD.tck_ps[p], 1334, 1453))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_6000; // >688 MHz - <=750 MHz
			else if (RANGE(SPD.tck_ps[p], 1454, 1666))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_5500; // >600 MHz - <=688 MHz
			else if (RANGE(SPD.tck_ps[p], 1667, 1874))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_4800; // >533 MHz - <=600 MHz
			else if (RANGE(SPD.tck_ps[p], 1875, 2149))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_4267; // >467 MHz - <=533 MHz
			else if (RANGE(SPD.tck_ps[p], 2150, 2499))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_3733; // >400 Mhz - <=467 MHz
			else if (RANGE(SPD.tck_ps[p], 2500, 2899))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_3200; // >344 Mhz - <=400 MHz
			else if (RANGE(SPD.tck_ps[p], 2900, 3749))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_2750; // >267 Mhz - <=344 MHz
			else if (RANGE(SPD.tck_ps[p], 3750, 4999))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_2133; // >200 Mhz - <=267 MHz
			else if (RANGE(SPD.tck_ps[p], 5000, 7519))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_1600; // >133 Mhz - <=200 MHz
			else if (RANGE(SPD.tck_ps[p], 7520, 14925))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_1067; // >67Mhz - <=133 MHz
			else if (RANGE(SPD.tck_ps[p], 14926, 200000))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_533;	// >5 MHz - <= 67 MHz
			else
				SNPS_ERROR("Invalid tck_ps[%u] = %u", p, SPD.tck_ps[p]);
		} else {
			if (RANGE(SPD.tck_ps[p], 1250, 1453))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_3200; // >688 MHz - <=800 MHz
			else if (RANGE(SPD.tck_ps[p], 1454, 1874))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_2750; // >533 MHz - <=688 MHz
			else if (RANGE(SPD.tck_ps[p], 1875, 2499))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_2133; // >400 MHz - <=533 MHz
			else if (RANGE(SPD.tck_ps[p], 2500, 3749))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_1600; // >267 MHz - <=400 MHz
			else if (RANGE(SPD.tck_ps[p], 3750, 7519))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_1067; // >133 MHz - <=267 MHz
			else if (RANGE(SPD.tck_ps[p], 7520, 100000))
				l_lpddr5_data_rate[p] = DWC_LPDDR5_533; // >10 MHz - <=133MHz
			else
				SNPS_ERROR("Invalid tck_ps[%u] = %u", p, SPD.tck_ps[p]);
		}
		SNPS_LOG("wckck ratio = %s tck_ps[%u] = %u ps and l_lpddr5_data_rate[%u] = %u", 
				 ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(hdlr, p)),
				 p, SPD.tck_ps[p], p, l_lpddr5_data_rate[p]);
	}
}

uint32_t dwc_cinit_get_lpddr4_trfcpb(uint32_t capacity_mbits)
{
    SNPS_TRACE("Entering");
    uint32_t ret = 0;

    if (capacity_mbits <= 2048)
        ret = 60000;
    if (capacity_mbits == 3072)
        ret = 90000;
    if (capacity_mbits == 4096)
        ret = 90000;
    if (capacity_mbits == 6144)
        ret = 140000;
    if (capacity_mbits == 8192)
        ret = 140000;
    if (capacity_mbits > 8192)
        ret = 190000;

    SNPS_TRACE("Leaving");
    return ret;
}

uint32_t dwc_cinit_get_lpddr4_tpbr2pbr(uint32_t capacity_mbits)
{
    SNPS_TRACE("Entering");
    uint32_t ret;

    if (capacity_mbits <= 2048)
        ret = 60000;
    else
        ret = 90000;

    SNPS_TRACE("Leaving");
    return ret;
}

uint32_t dwc_cinit_get_lpddr4_trfcab(uint32_t capacity_mbits)
{
    SNPS_TRACE("Entering");
    uint32_t ret;

    if (capacity_mbits <= 2048)
        ret = 130000;
    else if (capacity_mbits <= 4096)
        ret = 180000;
    else if (capacity_mbits <= 6144)
        ret = 280000;
    else if (capacity_mbits <= 8192)
        ret = 280000;
    else
        ret = 380000;

    SNPS_TRACE("Leaving");
    return ret;
}

/**
 * @brief helper method to return tRFMpb for LPDDR4
 */
uint32_t dwc_cinit_get_lpddr4_trfmpb(uint32_t capacity_mbits)
{
	SNPS_TRACE("Entering");
	uint32_t ret;
	if (capacity_mbits <= 2048) // 1G or 2G
		ret = 170000;    //In JESD209-4D, this is TBD
	else if (capacity_mbits == 3072) //3G
		ret = 170000;    //In JESD209-4D, this is TBD
	else if (capacity_mbits == 4096) //4G
		ret = 170000;    //In JESD209-4D, this is TBD
	else if (capacity_mbits == 6144) //6G
		ret = 170000;    //In JESD209-4D, this is TBD
	else if (capacity_mbits == 8192) //8G
		ret = 170000;
	else if (capacity_mbits == 12288)//12G
		ret = 190000;
	else if (capacity_mbits == 16384)//16G
		ret = 190000;
	else if (capacity_mbits == 24576)//24G
		ret = 260000;    //In JESD209-4D, this is TBD
	else if (capacity_mbits == 32768)//32G
		ret = 260000;    //In JESD209-4D, this is TBD
	else
		ret = 170000;			// other sizes are TBD
	SNPS_TRACE("Leaving");
	return ret;
}

uint32_t dwc_cinit_get_lpddr5_trfcab(uint32_t capacity_mbits, uint8_t dvfsc_type)
{
    SNPS_TRACE("Entering");
    uint32_t ret;

#ifdef USE_JESD209_5
    // JESD209-5: Table 189 — Refresh Requirement Parameters for BG mode or 16Bank mode
    if (capacity_mbits == 2048)
        ret = 130000;
    else if (capacity_mbits == 3072)
        ret = 180000;
    else if (capacity_mbits == 4096)
        ret = 180000;
    else if (capacity_mbits == 6144)
        ret = 280000;
    else
        ret = 280000;            // other sizes are TBD
#else /* USE_JESD209_5 */
SNPS_LOG("capacity_mbits=%u dvfsc_type=%u",capacity_mbits,dvfsc_type);
    // JESD209-5A: Table 216 — Refresh Requirement Parameters for BG mode or 16Bank mode
    if (capacity_mbits == 2048)
        ret = 130000;
    else if (capacity_mbits == 3072)
        ret = 180000;
    else if (capacity_mbits == 4096)
        ret = 180000;
    else if (capacity_mbits == 6144)
        ret = 210000;
    else if (capacity_mbits == 8192)
        ret = dvfsc_type==2 ? 230000 : 210000;
    else if (capacity_mbits == 12288)
        ret = dvfsc_type==2 ? 300000 : 280000;
    else if (capacity_mbits == 16384)//16G
        ret = dvfsc_type==2 ? 300000 : 280000;
    // ballot item# 1862.42, table Refresh requirements and RFM for LPDDR5/LPDDR5X 24Gb abd 32 Gb
    else if (capacity_mbits == 24576)//24G
        ret = dvfsc_type==2 ? 410000 : 380000;
    else if (capacity_mbits == 32768)//32G
        ret = dvfsc_type==2 ? 410000 : 380000;
    else
        ret = dvfsc_type==2 ? 410000 : 380000;            // other sizes are TBD
#endif /* USE_JESD209_5 */

    SNPS_TRACE("Leaving");
    return ret;
}

uint32_t dwc_cinit_get_lpddr5_trfcpb(uint32_t capacity_mbits, uint8_t dvfsc_type)
{
    SNPS_TRACE("Entering");
    uint32_t ret;

#ifdef USE_JESD209_5
    // JESD209-5: Table 189 — Refresh Requirement Parameters for BG mode or 16Bank mode
    if (capacity_mbits == 2048)
        ret = 60000;
    else if (capacity_mbits == 3072)
        ret = 90000;
    else if (capacity_mbits == 4096)
        ret = 90000;
    else if (capacity_mbits == 6144)
        ret = 140000;
    else
        ret = 140000;            // other sizes are TBD
#else /* USE_JESD209_5 */
    // JESD209-5A: Table 216 — Refresh Requirement Parameters for BG mode or 16Bank mode
    if (capacity_mbits == 2048) // 2G
        ret = dvfsc_type==2 ? 130000 :  60000; 	//In JESD209-5C ballot, TBD when dvfsc_type is 2
    else if (capacity_mbits == 3072) //3G
        ret = dvfsc_type==2 ? 130000 :  90000; 	//In JESD209-5C ballot, TBD when dvfsc_type is 2
    else if (capacity_mbits == 4096) //4G
        ret = dvfsc_type==2 ? 130000 :  90000; 	//In JESD209-5C ballot, TBD when dvfsc_type is 2
    else if (capacity_mbits == 6144) //6G
        ret = dvfsc_type==2 ? 130000 : 120000; 	//In JESD209-5C ballot, TBD when dvfsc_type is 2
    else if (capacity_mbits == 8192) //8G
        ret = dvfsc_type==2 ? 130000 : 120000;
    else if (capacity_mbits == 12288)//12G
        ret = dvfsc_type==2 ? 150000 : 140000;
    else if (capacity_mbits == 16384)//16G
        ret = dvfsc_type==2 ? 150000 : 140000;
    // ballot item# 1862.42 table Refresh requirements and RFM for LPDDR5/LPDDR5X 24Gb abd 32 Gb
    else if (capacity_mbits == 24576)//24G
        ret = dvfsc_type==2 ? 205000 : 190000;
    else if (capacity_mbits == 32768)//32G
        ret = dvfsc_type==2 ? 205000 : 190000;
    else
        ret = dvfsc_type==2 ? 205000 : 190000;            // other sizes are TBD
#endif /* USE_JESD209_5 */

    SNPS_TRACE("Leaving");
    return ret;
}


uint32_t dwc_cinit_get_lpddr5_tpbr2pbr(uint32_t capacity_mbits, uint8_t dvfsc_type)
{
    SNPS_TRACE("Entering");
    uint32_t ret;

    if (capacity_mbits == 2048)
        ret = dvfsc_type==2 ? 100000 : 60000;
    else
        ret = dvfsc_type==2 ? 100000 : 90000; // In JESD209-5C ballot, TBD when Enhanced DVFSC is enabled

    SNPS_TRACE("Leaving");
    return ret;
}
/**
 * @brief helper method to return tRFMpb for LPDDR5
 */
uint32_t dwc_cinit_get_lpddr5_trfmpb(uint32_t capacity_mbits)
{
	SNPS_TRACE("Entering");
	uint32_t ret;
	if (capacity_mbits == 2048) // 2G
		ret = 170000;    //In JESD209-5C ballot, this is TBD
	else if (capacity_mbits == 3072) //3G
		ret = 170000;    //In JESD209-5C ballot, this is TBD
	else if (capacity_mbits == 4096) //4G
		ret = 170000;    //In JESD209-5C ballot, this is TBD
	else if (capacity_mbits == 6144) //6G
		ret = 170000;    //In JESD209-5C ballot, this is TBD
	else if (capacity_mbits == 8192) //8G
		ret = 170000;
	else if (capacity_mbits == 12288)//12G
		ret = 190000;
	else if (capacity_mbits == 16384)//16G
		ret = 190000;
	else if (capacity_mbits == 24576)//24G
		ret = 260000;
	else if (capacity_mbits == 32768)//32G
		ret = 260000;
	else
		ret = 260000;			// other sizes are TBD
	SNPS_TRACE("Leaving");
	return ret;
}



#endif              // DDRCTL_LPDDR
