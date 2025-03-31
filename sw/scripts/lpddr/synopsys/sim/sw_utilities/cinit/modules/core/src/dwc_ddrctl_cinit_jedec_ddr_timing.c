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


#include "dwc_cinit_log.h"
#include "dwc_ddrctl_cinit_jedec_ddr_timing.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_jedec_to_cinit.h"
#include "dwc_ddrctl_cinit_jedec_ddr.h"
#include "dwc_ddrctl_cinit_jedec_lpddr.h"
#include "dwc_ddrctl_cinit_types_str.h"


void dwc_cinit_get_jedec_clk_speed(SubsysHdlr_t *cfg)
{
    uint8_t num_pstates;
    uint8_t num_channels;

#if defined(DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC)
    dwc_ddrctl_cinit_jedec_to_cinit();
#endif /* DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC */

#ifdef DWC_DDRCTL_CINIT_CPU_DPI_MODE
    num_pstates  = hdlr->num_pstates;
    num_channels = hdlr->num_dch;
#else
    num_pstates  = UMCTL2_FREQUENCY_NUM;
    num_channels = DWC_DDRCTL_DEV_CFG_NUM;
#endif

    for (int p = 0; p < num_pstates; p++) {
        for (int i = 0; i < num_channels; i++) {


            switch (DDRCTL_GET_PROTOCOL(cfg)) {
#ifdef DDRCTL_DDR
            case DWC_DDR5:
                ddr5_set_clk_speed(cfg, p, i);
                break;
            case DWC_DDR4:
                ddr4_set_clk_speed(cfg, p, i);
                break;
#endif /* DDRCTL_DDR */
#ifdef DDRCTL_LPDDR
            //Only clk_speed for p = 0 is set. For multiple p-states, the frequency will be set by 'set_mem_clks' function in 'dwc_ddrctl_sdram_base_cfg.sv'.
            //In 'set_mem_clks' we can set the discrete frequency as well. But in lpddr4_set_clk_speed or lpddr5_set_clk_speed, only specific speed-grades can be set
            case DWC_LPDDR4:
                lpddr4_set_clk_speed(cfg, p, i);
                break;
            case DWC_LPDDR5:
                lpddr5_set_clk_speed(cfg, p, i);
                break;
#endif /* DDRCTL_LPDDR */
            default:
                SNPS_ERROR("Protocol (%s) not supported",
                           ddrctl_sw_get_protocol_str(DDRCTL_GET_PROTOCOL(cfg)));
                dwc_ddrctl_cinit_exit(1);
                break;
            }
        }
    }
}

/**
 * @brief Takes a SubsysHdrl struc pointer and fills in the timing
 * parameters
 */
ddrctl_error_t dwc_cinit_ddr_set_timing(void)
{
    ddrctl_error_t rslt = DDRCTL_SUCCESS;
    uint8_t num_pstates;

    num_pstates  = hdlr->num_pstates;

    for (int p = 0; p < num_pstates; p++) {
        for (int i = 0; i < DWC_DDRCTL_DEV_CFG_NUM; i++) {
            switch (SPD.sdram_protocol) {
#ifdef DDRCTL_DDR
                case DWC_DDR4:
                    rslt = ddr4_set_default_timing(hdlr, p, i);
                    break;
                case DWC_DDR5:
                    ddr5_set_default_timing(hdlr, p, i);
                    break;
#endif /* DDRCTL_DDR */
#ifdef DDRCTL_LPDDR
                case DWC_LPDDR4:
#ifdef DDRCTL_LPDDR_MIXED_PKG
                    lpddr4_set_default_timing(hdlr, p, i, STATIC.lpddr_mixed_pkg_en);
#else
                    lpddr4_set_default_timing(hdlr, p, i, 0);
#endif /* DDRCTL_LPDDR_MIXED_PKG */
                    break;
                case DWC_LPDDR5:
#ifdef DDRCTL_LPDDR_MIXED_PKG
                    lpddr5_set_default_timing(hdlr, p, i, STATIC.lpddr_mixed_pkg_en);
#else
                    lpddr5_set_default_timing(hdlr, p, i, 0);
#endif /* DDRCTL_LPDDR_MIXED_PKG */
                    break;
#endif /* DDRCTL_LPDDR */
                default:
                    SNPS_ERROR("Protocol (%s) not supported",
                                ddrctl_sw_get_protocol_str(SPD.sdram_protocol));
                    rslt = DDRCTL_NOT_SUPPORTED;
                    break;
            }
        }
    }
    return rslt;
}

/**
 * @brief Function to get the maximum number to be used to contraint the refresh_timerX_start_value_x32 and refresh_timer_lr_offset_x32
 *  DDR4/DDR5/LPDDR4/LPDDR5 : The function return RFSHTMG0.t_refi_x1_x32 - RoundUp(RFSHTMG1.t_rfc_min/32).
 * @note per_bank_refresh is not used for DDR4/DDR5. fgr_mode is not used for LPDDR4/LPDDR5.
 *
 */
uint32_t dwc_ddrctl_cinit_get_stagger_ref_timing_max(uint32_t sdram_protocol, uint32_t capacity_mbits,
                                                     uint32_t per_bank_refresh, uint32_t fgr_mode, uint32_t tck_ps,
                                                     uint32_t ddr5_trefi_ps, uint32_t ddr5_trfc1_ps,
                                                     uint32_t ddr5_trfc2_ps, uint32_t scaled_trefi_en,
                                                     uint32_t ddr4_refresh_mode, uint32_t ddr4_refresh_range,uint32_t dvfsc_type)
{
    SNPS_TRACE("Entering");

    uint32_t trefi_x32_tck, trfc_min_x32_tck;

#ifdef DDRCTL_DDR
    uint32_t ddr4_trefi_ps = ((ddr4_refresh_mode==1) && (ddr4_refresh_range==1)) ? 3900000 : 7800000;
    //uint32_t ddr5_trefi_ps = 3900000;

	if (sdram_protocol == DWC_DDR4) {
		trefi_x32_tck = DIV_32(ddr4_trefi_ps / tck_ps);
		trefi_x32_tck = trefi_x32_tck >> fgr_mode;
		trfc_min_x32_tck = CEIL(cinit_ps_to_tck(dwc_cinit_get_ddr4_trfc(capacity_mbits, fgr_mode), tck_ps), 32);
	} else {
		trefi_x32_tck = DIV_32(ddr5_trefi_ps / tck_ps);
		trefi_x32_tck = trefi_x32_tck >> fgr_mode;
        // Formula from databook for refresh_timer_lr_offset_x32 :
        // refresh_timer*_start_value_x32 + (N-1) x refresh_timer_lr_offset_x32 + RoundUp(RFSHTMG1.t_rfc_min/32) < RFSHTMG0.t_refi_x1_x32
        // Databook also says that RFSHTMG6.refresh_timer_lr_offset_x32 needs to set to larger value than tRFC_dlr so that refreshes can be staggered as expected.
        // when using scaled trefi number eg. test_dwc_ddrctl_auto_ecs using 1.8us,  trefi_x32_tck is calculated to be very small number (eg. 'd26) if consider
        // both FGR mode and refresh rate. And this small number makes the formula hard to be satified when resolve the number for refresh_timer_lr_offset_x32.
        // It is high posssibility that refresh_timer_lr_offset_x32 is resolved to be  quite small number when use scaled refresh timing parameters.

        //consider the TCR High Temp
        trefi_x32_tck >>= 1;
		//RoundUp
		if(fgr_mode)  {
			trfc_min_x32_tck = scaled_trefi_en ? CEIL(cinit_ps_to_tck(ddr5_trfc2_ps, tck_ps), 32) : CEIL(cinit_ps_to_tck(dwc_cinit_get_ddr5_trfc(capacity_mbits, fgr_mode), tck_ps), 32);
		} else {
			trfc_min_x32_tck = scaled_trefi_en ? CEIL(cinit_ps_to_tck(ddr5_trfc1_ps, tck_ps), 32) : CEIL(cinit_ps_to_tck(dwc_cinit_get_ddr5_trfc(capacity_mbits, fgr_mode), tck_ps), 32);
		}
	}

#endif // DDRCTL_DDR
#ifdef DDRCTL_LPDDR
    uint32_t lpddr4_trefiab_ps = 3904000;
    uint32_t lpddr4_trefipb_ps = 488000;
    uint32_t lpddr5_trefiab_ps = 3906000;
    uint32_t lpddr5_trefipb_ps = 488000;

    uint32_t trfc_min_ps;

    trefi_x32_tck = (sdram_protocol == DWC_LPDDR4) ? (per_bank_refresh ? lpddr4_trefipb_ps : lpddr4_trefiab_ps) : (per_bank_refresh ? lpddr5_trefipb_ps : lpddr5_trefiab_ps);

    trefi_x32_tck = trefi_x32_tck / (32 * tck_ps);

    //consider derating is enabled. reg_derate_enable is DYN register , may change in simulation.
    if (sdram_protocol == DWC_LPDDR4)
        trefi_x32_tck = DIV_4(trefi_x32_tck);
    else
        trefi_x32_tck = DIV_8(trefi_x32_tck);

    trfc_min_ps = (sdram_protocol == DWC_LPDDR4) ? (per_bank_refresh ? dwc_cinit_get_lpddr4_trfcpb(capacity_mbits) : dwc_cinit_get_lpddr4_trfcab(capacity_mbits)) : (per_bank_refresh ? dwc_cinit_get_lpddr5_trfcpb(capacity_mbits, dvfsc_type) : dwc_cinit_get_lpddr5_trfcab(capacity_mbits, dvfsc_type));

	trfc_min_x32_tck =  (scaled_trefi_en != 0) ? CEIL(cinit_ps_to_tck(ddr5_trfc1_ps, tck_ps), 32) : CEIL(cinit_ps_to_tck(trfc_min_ps, tck_ps), 32);

#endif

    SNPS_TRACE("Leaving");

    if (trefi_x32_tck <= trfc_min_x32_tck)
        return 1;
    else
        return (trefi_x32_tck - trfc_min_x32_tck);
}

/**
 *@brief Function to return the tfc_dlr number with x32
 */
uint32_t dwc_ddrctl_cinit_get_ddr_trfc_dlr_x32_tck(uint32_t sdram_protocol, uint32_t capacity_mbits, uint32_t fgr_mode, uint32_t tck_ps, uint32_t ddr5_trfc1_ps, uint32_t ddr5_trfc2_ps, uint32_t scaled_trefi_en)
{
    uint32_t trfc_dlr_x32_tck = 0;

#ifdef DDRCTL_DDR
	if (sdram_protocol == DWC_DDR4) {
        trfc_dlr_x32_tck = DIV_32(dwc_ddrctl_cinit_get_ddr_trfc_dlr_tck(sdram_protocol, capacity_mbits, fgr_mode, tck_ps));
	} else {
		if(scaled_trefi_en) {
			trfc_dlr_x32_tck = fgr_mode ? DIV_32(CEIL(ddr5_trfc2_ps, tck_ps)) : DIV_32(CEIL(ddr5_trfc1_ps, tck_ps));

		} else {
			trfc_dlr_x32_tck = DIV_32(dwc_ddrctl_cinit_get_ddr_trfc_dlr_tck(sdram_protocol, capacity_mbits, fgr_mode, tck_ps));
		}
	}
#endif
    return trfc_dlr_x32_tck;
}


/**
 *@brief Function to return the tfc_dlr number for FGR mode switch
 */
uint32_t dwc_ddrctl_cinit_get_ddr_trfc_dlr_tck(uint32_t sdram_protocol, uint32_t capacity_mbits,
                                               uint32_t fgr_mode, uint32_t tck_ps)
{
    uint32_t tfc_dlr_tck = 0;

#ifdef DDRCTL_DDR
	if (sdram_protocol == DWC_DDR4)
		tfc_dlr_tck = cinit_ps_to_tck(dwc_cinit_get_ddr4_trfc_dlr(capacity_mbits, fgr_mode), tck_ps);
	else
		tfc_dlr_tck = CEIL(dwc_cinit_get_ddr5_trfc_dlr(capacity_mbits, fgr_mode), tck_ps);
#endif
    return tfc_dlr_tck;
}

/**
 *@brief Function to return the tfc_min number for FGR mode switch
 */
uint32_t dwc_ddrctl_cinit_get_ddr_trfc_min_tck(uint32_t sdram_protocol, uint32_t capacity_mbits,
                                               uint32_t fgr_mode, uint32_t tck_ps)
{
    uint32_t tfc_min_tck = 0;

#ifdef DDRCTL_DDR
	if (sdram_protocol == DWC_DDR4)
		tfc_min_tck = cinit_ps_to_tck(dwc_cinit_get_ddr4_trfc(capacity_mbits, fgr_mode), tck_ps);
	else
		tfc_min_tck = CEIL(dwc_cinit_get_ddr5_trfc(capacity_mbits, fgr_mode), tck_ps);
#endif
    return tfc_min_tck;
}


#ifdef CINIT_DDR5


/**
 * @brief Calculate recommended values for gap between REFab commands to be scheduled
 *        in critical refresh burst. (only in DDR5)
 *        Should be set in RFSHSET1TMG9.refab_hi_sch_gap
 *
 * @param t_rfc_min_tck     tRFC(min) value in clocks
 * @param curr_gap_tck      Current value for REFab scheduler gap
 * @param new_gap_tck       Pointer to return the recommended value for REFab scheduler gap
 * @return ddrctl_error_t   DDRCTL_SUCCESS, DDRCTL_ERROR
 */
ddrctl_error_t ddrctl_cinit_get_ddr5_refab_sch_gap_tck(uint32_t t_rfc_min_tck,
                                                       uint32_t curr_gap_tck, uint32_t *new_gap_tck)
{
    uint32_t refab_sch_gap_min;
    uint32_t refab_sch_gap_max;

    SNPS_DEBUG("Calculating Gap between REFab in critical refresh burst");

    refab_sch_gap_min  = CEIL(t_rfc_min_tck * 3, 2);
    refab_sch_gap_max  = t_rfc_min_tck * 2;

    if (refab_sch_gap_min > refab_sch_gap_max) {
        SNPS_ERROR("Min value is higher that max (%u > %u)", refab_sch_gap_min, refab_sch_gap_max);
        return DDRCTL_ERROR;
    }

    *new_gap_tck = curr_gap_tck;

    if (curr_gap_tck <= refab_sch_gap_min) {
        *new_gap_tck = refab_sch_gap_min;
    }

    if (curr_gap_tck >= refab_sch_gap_max) {
        *new_gap_tck = refab_sch_gap_max;
    }

    SNPS_DEBUG("Gap between REFab commands = %u", *new_gap_tck);

    return DDRCTL_SUCCESS;
}


/**
 * @brief Calculate recommended  Gap between REFsb commands to be scheduled in critical
 *        refresh burst. (only in DDR5)
 *        Should be set in RFSHSET1TMG9.refsb_hi_sch_gap
 *
 * @param config            Cinit configuration struct
 * @param pstate            pState selected
 * @param dev               Device selected
 * @param curr_gap_tck      Current set gap
 * @param new_gap_tck       Calculated gap
 * @return ddrctl_error_t   DDRCTL_SUCCESS, DDRCTL_ERROR
 */
ddrctl_error_t ddrctl_cinit_get_ddr5_refsb_sch_gap_tck(SubsysHdlr_t *config, uint8_t pstate, uint8_t dev,
                                                       uint32_t curr_gap_tck, uint32_t *new_gap_tck)
{
    ddrTimingParameters_t *timing;
    uint32_t tck_ps;
    uint32_t t_refsbrd_tck;
    uint32_t t_rfc_sb_tck;
    uint32_t t_refi1_tck;

    timing = &hdlr->timingParams_m[pstate][dev];
    tck_ps = config->spdData_m.tck_ps[pstate];

    SNPS_DEBUG("[pstate %d] Calculating Gap between REFsb in critical refresh burst", pstate);

    // refsb_hi_sch_gap Gap between REFsb commands to be scheduled in critical refresh burst.
    // It is recommended to program this to between RFSHSET1TMG3.t_refsbrd and RFSHSET1TMG3.t_rfcsb.
    // Also this must be less than internal used tREFI value which is determined by FGR mode,
    // the number of banks in same-bank refresh mode or TCR.

    t_refsbrd_tck = CEIL(timing->ddr5_trefsbrd_ps, tck_ps);
    t_rfc_sb_tck  = CEIL(timing->ddr5_trfcsb_ps  , tck_ps);
    t_refi1_tck   = DIV_32(CEIL(timing->ddr5_trefi1_ps , tck_ps));

    SNPS_DEBUG("Timmings: tREFSBRD=%u, tRFCsb=%u, tREFI=%u", t_refsbrd_tck, t_rfc_sb_tck, t_refi1_tck);

    if ((t_refsbrd_tck > t_rfc_sb_tck)) {
        SNPS_ERROR("Invalid timmings, tREFSBRD value is higher that tRFCsb (%u > %u)", t_refsbrd_tck, t_rfc_sb_tck);
        return DDRCTL_ERROR;
    }

    if ((t_refsbrd_tck > t_refi1_tck)) {
        SNPS_ERROR("Invalid timmings, tREFSBRD value is higher that tREFI (%u > %u)", t_refsbrd_tck, t_refi1_tck);
        return DDRCTL_ERROR;
    }

    *new_gap_tck = curr_gap_tck;

    if (curr_gap_tck <= t_refsbrd_tck) {
        *new_gap_tck = t_refsbrd_tck;
    }

    if (curr_gap_tck >= t_rfc_sb_tck) {
        *new_gap_tck = t_rfc_sb_tck;
    }

    if (curr_gap_tck >= t_refi1_tck) {
        *new_gap_tck = t_refi1_tck;
    }

    SNPS_DEBUG("[pstate %d] Gap between REFsb commands = %u", pstate, *new_gap_tck);

    return DDRCTL_SUCCESS;
}


#endif /* CINIT_DDR5 */
