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


#include "dwc_cinit_workaround_macros.h"
#include "dwc_ddrctl_cinit_pre_cfg.h"
#include "dwc_ddrctl_cinit_common_dfi_timings.h"
#include "dwc_ddrctl_cinit_lpddr54_dfi_timings.h"
#include "dwc_ddrctl_cinit_ddr54_dfi_timings.h"
#include "jedec/ddr5/cinit_ddr5_timing_utils.h"
#include "dwc_ddrctl_cinit_jedec_ddr_timing.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_defines.h"

#ifdef DDRCTL_WR_CRC_RETRY
static void cinit_cal_retry_window(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);
#endif

/**
 * @brief Do some pre-calculations before cinit_prgm_regs is called.
 */
void cinit_pre_cfg(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch)
{
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][0];

    PRE_CFG.cwl_x[p] = cinit_cal_cwlx(hdlr, p, ch, 0);
    PRE_CFG.cl[p] = cinit_cal_cl(hdlr, p, ch, 0);
#ifdef DDRCTL_TWO_TIMING_SETS_EN
#if (DWC_DDRCTL_DEV_CFG_NUM > 0)
    PRE_CFG.cwl_x_2[p] = cinit_cal_cwlx(hdlr, p, ch, 1);
    PRE_CFG.cl_2[p] = cinit_cal_cl(hdlr, p, ch, 1);

    // cwl / cl uses the bigger number when both two device configuration are used.
    if (STATIC.rank_dev_cfg_sel[ch] & STATIC.active_ranks && STATIC.rank_dev_cfg_sel[ch] != STATIC.active_ranks) {
        PRE_CFG.cwl_x[p] = max(PRE_CFG.cwl_x[p], PRE_CFG.cwl_x_2[p]);
        PRE_CFG.cwl_x_2[p] = PRE_CFG.cwl_x[p];
        PRE_CFG.cl[p] = max(PRE_CFG.cl[p], PRE_CFG.cl_2[p]);
        PRE_CFG.cl_2[p] = PRE_CFG.cl[p];
    }
    PRE_CFG.t_mrr2mpc_2[p][ch] = PRE_CFG.cl_2[p] + DIV_2(timing->burst_length) + 1;
#endif /* DWC_DDRCTL_DEV_CFG_NUM > 0 */
#endif
#ifdef DDRCTL_EXT_SBECC_AND_CRC
    cinit_cal_delay_for_ras_model(hdlr, p, ch, 0);
#endif

    dwc_ddrctl_cinit_ddr54_dfi_control_timing(hdlr, p, ch);
    dwc_ddrctl_cinit_lpddr54_dfi_control_timing(hdlr, p, ch);
    cinit_cal_pre_cfg_timing_1st_set(hdlr, p, ch, 0);
#if (DWC_DDRCTL_DEV_CFG_NUM > 0)
    cinit_cal_pre_cfg_timing_2nd_set(hdlr, p, ch, 1);
#endif /* DWC_DDRCTL_DEV_CFG_NUM > 0 */
}

void cinit_cal_pre_cfg_timing_1st_set(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
    uint8_t         bl_div2;
#ifdef DDRCTL_DDR
    uint32_t t_mod = 0;
    uint32_t txpdll = 0;
    uint32_t t_stab01_max_ps = 0;
#endif /* DDRCTL_DDR */
    uint32_t ratio;
    uint32_t tck_ps = SPD.tck_ps[p];
    uint32_t twr, tfaw, tras_max, tras_min, trtp = 0, txp, t_rc, cl_dbi = 0;
    uint32_t twtr, t_mr;
    uint32_t trcd, trp;

#ifdef DDRCTL_LPDDR
    uint32_t trcd_write;
    uint32_t trrd;
    uint32_t tdqsck_max;
    uint32_t trpst_int;
#endif /* DDRCTL_LPDDR */

    // BL/2 (Burst Length / 2)
    bl_div2 = DIV_2(timing->burst_length);

    // lookup the timing parameters based on the protocol enabled.
    switch (SPD.sdram_protocol) {
#ifdef DDRCTL_DDR
    case DWC_DDR4:
        ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
        twr = timing->ddr4_twr_ps;
        tfaw = timing->ddr4_tfaw_ps;
        tras_max = timing->ddr4_tras_max_ps;
        tras_min = timing->ddr4_tras_min_ps;
        trtp = timing->ddr4_trtp_ps;
        txp = timing->ddr4_txp_ps;
        txpdll = timing->ddr4_txpdll_ps;
        t_rc = timing->trc_ps;
        cl_dbi = timing->ddr4_tcl_rdbi_tck;
        twtr = (QDYN.ddr4_wr_preamble[p][ch]) ? timing->ddr4_twtr_l_tck + 1 : timing->ddr4_twtr_l_tck;
        PRE_CFG.twtr_s[p][ch] = (QDYN.ddr4_wr_preamble[p][ch]) ? timing->ddr4_twtr_s_tck + 1 : timing->ddr4_twtr_s_tck;
        t_mr = timing->ddr4_tmrd_tck;
        t_mod = cinit_ps_to_tck(timing->ddr4_tmod_ps, tck_ps);
        trcd = timing->trcd_ps;
        if (timing->ddr4_tccd_l_tck == 5 && QDYN.ddr4_wr_preamble[p][ch]) {
            PRE_CFG.t_ccd[p][ch] = timing->ddr4_tccd_l_tck + 1;
            SNPS_LOG("tCCD + 1 = %u", PRE_CFG.t_ccd[p][ch]);
        } else {
            PRE_CFG.t_ccd[p][ch] = timing->ddr4_tccd_l_tck;
            SNPS_LOG("tCCD = %u", PRE_CFG.t_ccd[p][ch]);
        }

        trp = timing->trp_ps;
        if (STATIC.caparity_disable_before_sr == 0)
            PRE_CFG.t_cksre[p][ch] = cinit_ps_to_tck(10000, tck_ps) + timing->ddr4_tpl_tck;
        else
            PRE_CFG.t_cksre[p][ch] = cinit_ps_to_tck(10000, tck_ps);
        PRE_CFG.t_cksrx[p][ch] = cinit_ps_to_tck(timing->ddr4_tcksrx_ps, tck_ps);
        if (STATIC.caparity_disable_before_sr == 0) {
            PRE_CFG.t_ckesr[p][ch] = cinit_ps_to_tck(timing->ddr4_tcke_ps, tck_ps) + 1 + timing->ddr4_tpl_tck;
            PRE_CFG.t_cke[p][ch] = timing->ddr4_tcke_ps + (timing->ddr4_tpl_tck * tck_ps);
        } else {
            PRE_CFG.t_ckesr[p][ch] = cinit_ps_to_tck(timing->ddr4_tcke_ps, tck_ps) + 1;
            PRE_CFG.t_cke[p][ch] = timing->ddr4_tcke_ps;
        }
        PRE_CFG.t_mrd_pda[p][ch] = cinit_ps_to_tck(10000, tck_ps);
        PRE_CFG.t_wr_mpr[p][ch] = t_mod + SPD.tAL + timing->ddr4_tpl_tck;
        // tXS_FAST
        PRE_CFG.t_xs_fast_min[p][ch] = DIV_32(((timing->ddr4_trfc_min4_ps + 10000) / tck_ps) + timing->ddr4_cal_tck + timing->ddr4_tpl_tck) + 1;
        PRE_CFG.t_xs_min[p][ch] = DIV_32(((timing->ddr4_trfc_min_ps + 10000) / tck_ps) + timing->ddr4_cal_tck + timing->ddr4_tpl_tck) + 1;
        PRE_CFG.t_xs_dll_x32[p][ch] = CEIL(timing->ddr4_txsdll_tck, 32);
        cinit_cal_ddr54_pre_cfg_timing_1st_set(hdlr, p, ch, n);
#ifdef UMCTL2_CID_EN
        if (CID_WIDTH(n) > 0) {
            if (timing->ddr4_tccd_dlr_tck == 5 && QDYN.ddr4_wr_preamble[p][ch])
                PRE_CFG.t_ccd_dlr[p][ch] = timing->ddr4_tccd_dlr_tck + 1;
            else
                PRE_CFG.t_ccd_dlr[p][ch] = timing->ddr4_tccd_dlr_tck;
            PRE_CFG.t_rrd_dlr[p][ch] = timing->ddr4_trrd_dlr_tck;
            PRE_CFG.t_faw_dlr[p][ch] = timing->ddr4_tfaw_dlr_tck;
        }


#endif /* UMCTL2_CID_EN */

        // MPSM
        PRE_CFG.t_mpx_lh[p][ch] = cinit_ps_to_tck(timing->ddr4_tmpx_lh_ps, tck_ps);
        PRE_CFG.t_mpx_s[p][ch]  = timing->ddr4_tmpx_s_tck;
        PRE_CFG.t_ckmpe[p][ch]  = cinit_ps_to_tck(timing->ddr4_tckmpe_ps, tck_ps);

        PRE_CFG.post_mpsm_gap_x32[p][ch]  = CEIL(cinit_ps_to_tck(timing->ddr4_txmpdll_ps, tck_ps), 32) + 1;

#ifndef MEMC_CMD_RTN2IDLE
        PRE_CFG.t_sync_gear[p][ch] = timing->ddr4_tsync_gear_tck;
        PRE_CFG.t_cmd_gear[p][ch] = timing->ddr4_tcmd_gear_tck;
        PRE_CFG.t_gear_setup[p][ch] = timing->ddr4_tgear_setup_tck;
        PRE_CFG.t_gear_hold[p][ch] = timing->ddr4_tgear_hold_tck;
#endif  /* MEMC_CMD_RTN2IDLE */

		break;
	case DWC_DDR5:
        ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
		twr = timing->ddr5_twr_ps;
		tras_min = timing->ddr5_tras_min_ps;
		trtp = timing->ddr5_trtp_ps;
		if (IS_RDIMM || IS_LRDIMM) {
			// For DDR5 (L)RDIMM: max (tXP, tRPDX)
			txp = max (timing->ddr5_txp_ps, timing->ddr5_rcd_trpdx_ps);
		} else {
			txp = timing->ddr5_txp_ps;
		}
		twtr = timing->ddr5_twtr_l_tck;	// consider the effect of preamble, no detail in JEDEC
		PRE_CFG.twtr_s[p][ch] = timing->ddr5_twtr_s_tck;	// consider the effect of preamble, no detail in JEDEC
		t_mr = timing->ddr5_tmrd_tck;
        t_rc = timing->trc_ps;

		trcd = timing->trcd_ps;
		PRE_CFG.t_ccd[p][ch] = timing->ddr5_tccd_l_tck;
		tfaw = CID_WIDTH(n) ? timing->ddr5_tfaw_slr_tck : timing->ddr5_tfaw_tck;
		// Adjust the t_ccd_w_s / t_ccd_r_s / t_ccd_r_l for DDR5 read / write interamble
		PRE_CFG.t_ccd_w_s[p][ch] = QDYN.wr_crc_enable ? (timing->ddr5_tccd_s_tck + hdlr->ddr5_interamble_tccd_offset.t_ccd_w_offset[p][ch] + 1) : (timing->ddr5_tccd_s_tck + hdlr->ddr5_interamble_tccd_offset.t_ccd_w_offset[p][ch]);
		PRE_CFG.t_ccd_r_s[p][ch] = QDYN.rd_crc_enable ? (timing->ddr5_tccd_s_tck + hdlr->ddr5_interamble_tccd_offset.t_ccd_r_offset[p][ch] + 1) : (timing->ddr5_tccd_s_tck + hdlr->ddr5_interamble_tccd_offset.t_ccd_r_offset[p][ch]);
		PRE_CFG.t_ccd_r_l[p][ch] = QDYN.rd_crc_enable ? (timing->ddr5_tccd_l_tck + 1) : timing->ddr5_tccd_l_tck;
		PRE_CFG.t_ccd_r_m[p][ch] = QDYN.rd_crc_enable ? (timing->ddr5_tccd_m_tck + 1) : timing->ddr5_tccd_m_tck;
#ifdef DDRCTL_DDR5CTL
#ifdef DDRCTL_LLC_4CYCSCH
	if (IS_DDR5) {
		if (timing->ddr5_tccd_l_tck < 16) {
			PRE_CFG.t_ccd_r_l[p][ch] = 16;
		}
	}
#endif /* DDRCTL_LLC_4CYCSCH */
#endif /* DDRCTL_DDR5CTL */

#ifdef UMCTL2_CID_EN
        PRE_CFG.t_rrd_dlr[p][ch] = timing->ddr5_trrd_dlr_tck;
        PRE_CFG.t_faw_dlr[p][ch] = timing->ddr5_tfaw_dlr_tck;
        PRE_CFG.t_ccd_dlr[p][ch] = timing->ddr5_tccd_s_tck;
        PRE_CFG.t_refsbrd_dlr[p][ch] = cinit_ps_to_tck(timing->ddr5_trefsbrd_dlr_ps, tck_ps);
        PRE_CFG.t_rfcsb_dlr[p][ch] = cinit_ps_to_tck(timing->ddr5_trfcsb_dlr_ps, tck_ps);
        if (IS_DDR5 && p == 0) {
            PRE_CFG.lrank_rd2rd_gap[ch] = 0;
            PRE_CFG.lrank_wr2wr_gap[ch] = 0;
            // tCCD_dlr : t_ccd_r_s + lrank_rd2rd_gap
            if (timing->ddr5_tccd_dlr_tck > timing->ddr5_tccd_s_tck) {
                PRE_CFG.lrank_rd2rd_gap[ch] = timing->ddr5_tccd_dlr_tck - timing->ddr5_tccd_s_tck;
            }

            // tCCD_WR_dlr : t_ccd_w_s + lrank_wr2wr_gap
            if (timing->ddr5_tccd_wr_dlr_tck > timing->ddr5_tccd_s_tck) {
                PRE_CFG.lrank_wr2wr_gap[ch] = timing->ddr5_tccd_wr_dlr_tck - timing->ddr5_tccd_s_tck;
            }
        }
#endif /* UMCTL2_CID_EN */

    cinit_cal_ddr54_pre_cfg_timing_1st_set(hdlr, p, ch, n);
		trp = timing->trp_ps;
		PRE_CFG.t_mrr2mpc[p][ch] = PRE_CFG.cl[p] + bl_div2 + 1;
		PRE_CFG.t_csl[p][ch] = cinit_ps_to_tck(10000, tck_ps);
		// tXSDLL==tDLLK from JEDEC
		PRE_CFG.t_xs_dll_x32[p][ch] = CEIL(timing->ddr5_tdllk_tck, 32);
		PRE_CFG.t_cksrx[p][ch] = cinit_ps_to_tck(timing->ddr5_tcksrx_ps, tck_ps);
		PRE_CFG.t_cksre[p][ch] = timing->ddr5_tcklcs_tck;
		break;
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
	case DWC_LPDDR4:
		twr = timing->lpddr4_twr;
		tfaw = timing->lpddr4_tfaw;
		tras_max = timing->lpddr4_tras_max;
		tras_min = timing->lpddr4_tras_min;
		trtp = timing->lpddr4_trtp;
		txp = timing->lpddr4_txp;
		// MR17.OP[4] - 0:ODTD-CS Enable RZQ/3, 1:ODTD-CS Disable(default)
		t_rc = timing->lpddr4_trc;
		cl_dbi = timing->lpddr4_cl_dbi;
		twtr = timing->lpddr4_twtr;
		t_mr = timing->lpddr4_tmrd;
		trcd = timing->lpddr4_trcd;
		PRE_CFG.t_ccd[p][ch] = timing->lpddr4_tccd;
		trrd = timing->lpddr4_trrd;
		trp = timing->lpddr4_trp;
		PRE_CFG.derated_t_rcd[p][ch] = cinit_ps_to_tck(timing->lpddr4_derated_trcd, tck_ps);
		PRE_CFG.derated_t_ras_min[p][ch] = cinit_ps_to_tck(timing->lpddr4_derated_tras_min, tck_ps);
		PRE_CFG.derated_t_rp[p][ch] = cinit_ps_to_tck(timing->lpddr4_derated_trp, tck_ps);
		PRE_CFG.derated_t_rrd[p][ch] = cinit_ps_to_tck(timing->lpddr4_derated_trrd, tck_ps);
		PRE_CFG.derated_t_rc[p][ch] = cinit_ps_to_tck(timing->lpddr4_derated_trc, tck_ps);
		PRE_CFG.t_cksrx[p][ch] = cinit_ps_to_tck(timing->lpddr4_tckckeh, tck_ps);
		PRE_CFG.t_cksre[p][ch] = cinit_ps_to_tck(timing->lpddr4_tckelck, tck_ps);
		
		if (timing->lpddr4_tsr < timing->lpddr4_tcke)
		    PRE_CFG.t_ckesr[p][ch] = cinit_ps_to_tck(timing->lpddr4_tcke, tck_ps);
		else
		    PRE_CFG.t_ckesr[p][ch] = cinit_ps_to_tck(timing->lpddr4_tsr, tck_ps);
		PRE_CFG.t_cke[p][ch] = timing->lpddr4_tcke;
		PRE_CFG.t_cmdcke[p][ch] = cinit_ps_to_tck(timing->lpddr4_tcmdcke, tck_ps);
		PRE_CFG.t_vrcg_enable[p][ch] = cinit_ps_to_tck(timing->lpddr4_tvrcg_enable, tck_ps);
		PRE_CFG.t_vrcg_disable[p][ch] = cinit_ps_to_tck(timing->lpddr4_tvrcg_disable, tck_ps);
		PRE_CFG.lpddr4_diff_bank_rwa2pre[p][ch] = 2;
		PRE_CFG.t_pbr2pbr[p][ch] = CEIL(timing->lpddr4_tpbr2pbr, tck_ps);
                PRE_CFG.t_pbr2pbr_mp[p][ch] = CEIL(timing->lpddr4_tpbr2pbr_mp, tck_ps);
		PRE_CFG.wl[p][ch] = (hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls == 0) ? timing->lpddr4_cwl_seta : timing->lpddr4_cwl_setb;    // write latency
		PRE_CFG.rl[p][ch] = (hdlr->memCtrlr_m.lpddr4_mr[p].mr3.read_dbi == 0) ? PRE_CFG.cl[p] : cl_dbi;    // read latency
		PRE_CFG.nwr[p][ch] = timing->lpddr4_nwr;
		PRE_CFG.nrtp[p][ch] = timing->lpddr4_nrtp;
		
		//LPDDR4: WL + 1 + BL / 2 + max(RU(7.5ns / tCK),8nCK) + nWR
		PRE_CFG.wr2mr[p][ch] = PRE_CFG.wl[p][ch] + 1 + 8 + max(CEIL(7500, tck_ps), 8) + timing->lpddr4_nwr;
		//LPDDR4: RL + BL / 2 + RU(tDQSCKmax / tCK) + RD(tRPST) + max(RU(7.5ns / tCK),8nCK) + nRTP - 8
		tdqsck_max = cinit_ps_to_tck(timing->lpddr4_tdqsck_max, SPD.tck_ps[p]);
		trpst_int = (hdlr->memCtrlr_m.lpddr4_mr[p].mr1.rd_postamble) ? 1 : 0;
		
		PRE_CFG.rd2mr[p][ch] = PRE_CFG.rl[p][ch] + 8 + tdqsck_max + trpst_int + max(CEIL(7500, tck_ps), 8) + cinit_ps_to_tck(trtp, tck_ps) - 8;
		PRE_CFG.wra2pre[p][ch] = PRE_CFG.wl[p][ch] + 8 + PRE_CFG.nwr[p][ch] + 1;
		PRE_CFG.rda2pre[p][ch] = 8 - 8 + PRE_CFG.nrtp[p][ch];
		PRE_CFG.t_osco[p][ch] = cinit_ps_to_tck(timing->lpddr4_tosco, tck_ps);
#ifdef MEMC_BURST_LENGTH_32 
		PRE_CFG.t_ccd_blx2[p][ch] = timing->lpddr4_tccd_bl32;
		PRE_CFG.wr2mr_blx2[p][ch] = PRE_CFG.wl[p][ch] + 1 + 16 + max(CEIL(7500, tck_ps), 8) + timing->lpddr4_nwr;
		PRE_CFG.rd2mr_blx2[p][ch] = PRE_CFG.rl[p][ch] + 16 + tdqsck_max + trpst_int + max(CEIL(7500, tck_ps), 8) + cinit_ps_to_tck(trtp, tck_ps) - 8;
		PRE_CFG.wra2pre_blx2[p][ch] = PRE_CFG.wl[p][ch] + 16 + PRE_CFG.nwr[p][ch] + 1;
		PRE_CFG.rda2pre_blx2[p][ch] = 16 - 8 + PRE_CFG.nrtp[p][ch];
#endif /* MEMC_BURST_LENGTH_32 */
        
		break;
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
	case DWC_LPDDR5:
		ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
		twr = timing->lpddr5_twr_ps;
		tfaw = timing->lpddr5_tfaw_ps;
		tras_max = timing->lpddr5_tras_max_ps;
		tras_min = timing->lpddr5_tras_min_ps;
        	// [JESD209-5A Table 226] If CS ODT is enabled, tPDXCSODTON needs to be applied between PDX and a valid command
        	// tXP is defined as Max(7ns, 3nCK), and tXP is set to 3nCK when data rate is very low, hence tXP can be larger than tPDXCSODTON (20 ns).
        	// [JESD209-5B] CS ODT behavior is support for LPDDR5X SDRAM if MR11.OP[7]=1. tPDXCSODTON must be removed from t_xp in this case

        	// MR17.OP[4] - 0:ODTD-CS Enable RZQ/3, 1:ODTD-CS Disable(default)
        	// MR11.OP[7] - 0:Basic CS ODT behavior (default), 1:CS ODT behavior option; always 0 for LPDDR5
        	txp = (((hdlr->memCtrlr_m.lpddr5_mr[p].mr17.odtd_cs == 0) && (hdlr->memCtrlr_m.lpddr5_mr[p].mr11.cs_odt_op == 0)) ? max(timing->lpddr5_txp_ps, timing->lpddr5_tpdxcsodton_ps) :
                                                                       timing->lpddr5_txp_ps);

		SNPS_LOG("freq = %u, txp_ps = %u (mr17.odtd_cs = %u, mr11.cs_odt_op = %u, tpdxcsodton_ps = %u, (original)txp_ps = %u, tcsh_ps = %u)",
		p, txp, hdlr->memCtrlr_m.lpddr5_mr[p].mr17.odtd_cs, hdlr->memCtrlr_m.lpddr5_mr[p].mr11.cs_odt_op, timing->lpddr5_tpdxcsodton_ps, timing->lpddr5_txp_ps, timing->lpddr5_tcsh_ps);
		trtp = timing->lpddr5_trtp_ps;
		//tRBTP = [1:1:2] Max(7.5ns,4nCK) - 4nCK [1:1:4] Max(7.5ns,2nCK) - 2nCK
		PRE_CFG.t_rbtp[p][ch] = cinit_ps_to_tck(timing->lpddr5_trtp_ps, tck_ps);
		PRE_CFG.t_rrd_s[p][ch] = CEIL(timing->lpddr5_trrd_s_ps, tck_ps);
		// tRAS + tRPpb with per-bank precharge
		t_rc = timing->lpddr5_trc_ppb_ps;
		PRE_CFG.derated_t_rc[p][ch] = cinit_ps_to_tck(timing->lpddr5_derated_trcpb_ps, tck_ps);
		PRE_CFG.derated_t_rp[p][ch] = cinit_ps_to_tck(timing->lpddr5_derated_trppb_ps, tck_ps);
		PRE_CFG.wl[p][ch] = timing->lpddr5_wl_tck;
		PRE_CFG.rl[p][ch] = timing->lpddr5_rl_tck;
		PRE_CFG.nwr[p][ch] = timing->lpddr5_nwr;
		PRE_CFG.nrbtp[p][ch] = timing->lpddr5_nrbtp;
		if (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1) {
			//JESD209-5B,Table 257 — ODTLon and ODTLoff Latency Values
			timing->lpddr5_odtloff_tck = PRE_CFG.wl[p][ch] + 5;
			timing->lpddr5_odtloff_bl32_tck = PRE_CFG.wl[p][ch] + 9;}
		else {
			timing->lpddr5_odtloff_tck = PRE_CFG.wl[p][ch] + 3;
			timing->lpddr5_odtloff_bl32_tck = PRE_CFG.wl[p][ch] + ((SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? 7 : 5); }
		trp = timing->lpddr5_trppb_ps;	// [BUG13172] precharge all bank is not supported so we can always set it to tRPpb
		twtr = timing->lpddr5_twtr_ps;
		t_mr = cinit_ps_to_tck(max((timing->lpddr5_tmrr_tck * tck_ps + timing->lpddr5_tmrw_ps), timing->lpddr5_tmrd_ps), tck_ps); // P80001562-107147: Max ((tMRR + tMRW), tMRD)
		trcd = timing->lpddr5_trcd_ps;
		trcd_write = timing->lpddr5_trcd_write_ps;
		PRE_CFG.t_ccd[p][ch] = timing->lpddr5_tccd_l_tck;
		trrd = timing->lpddr5_trrd_l_ps;	// same as lpddr5_trrd_s_ps
		PRE_CFG.derated_t_rcd[p][ch] = cinit_ps_to_tck(timing->lpddr5_derated_trcd_ps, tck_ps);
		PRE_CFG.derated_t_rcd_write[p][ch] = cinit_ps_to_tck(timing->lpddr5_derated_trcd_write_ps, tck_ps);
		PRE_CFG.derated_t_ras_min[p][ch] = cinit_ps_to_tck(timing->lpddr5_derated_tras_min_ps, tck_ps);
		PRE_CFG.derated_t_rrd[p][ch] = cinit_ps_to_tck(timing->lpddr5_derated_trrd_ps, tck_ps);
		PRE_CFG.t_cksrx[p][ch] = cinit_ps_to_tck(timing->lpddr5_tckcsh_ps, tck_ps);
		PRE_CFG.t_cksre[p][ch] = cinit_ps_to_tck(timing->lpddr5_tcslck_ps, tck_ps);
		PRE_CFG.t_ckesr[p][ch] = max(timing->lpddr5_tsr_ps, timing->lpddr5_tcspd_ps);
		PRE_CFG.t_ckesr[p][ch] = cinit_ps_to_tck(PRE_CFG.t_ckesr[p][ch], tck_ps);
		PRE_CFG.t_cke[p][ch] = timing->lpddr5_tcspd_ps;
		PRE_CFG.t_csh[p][ch] = CEIL(timing->lpddr5_tcsh_ps, tck_ps);
		PRE_CFG.t_mrw_l[p][ch] = CEIL(timing->lpddr5_tmrw_l_ps + tck_ps/2, tck_ps);

        	PRE_CFG.t_cmdcke[p][ch] = max(timing->lpddr5_tcmdpd_ps, timing->lpddr5_tescke_ps);
        	PRE_CFG.t_cmdcke[p][ch] = cinit_ps_to_tck(PRE_CFG.t_cmdcke[p][ch], tck_ps);
        	PRE_CFG.t_vrcg_enable[p][ch] = cinit_ps_to_tck(timing->lpddr5_tvrcg_enable_ps, tck_ps);
        	PRE_CFG.t_vrcg_disable[p][ch] = cinit_ps_to_tck(timing->lpddr5_tvrcg_disable_ps, tck_ps);
        	// WL + BL / n_min + 1 + nWR
        	PRE_CFG.wra2pre[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_min_tck + 1 + PRE_CFG.nwr[p][ch];
        	// BL / n_min + nRBTP
        	//PRE_CFG.rda2pre[p][ch] = CEIL(timing->lpddr5_twr_ps,tck_ps) + timing->lpddr5_bl_n_min_tck + PRE_CFG.nrbtp[p][ch];
        	PRE_CFG.rda2pre[p][ch] = timing->lpddr5_bl_n_min_tck + PRE_CFG.nrbtp[p][ch];
		#ifdef  DWC_DDRCTL_LPDDR54_OSCO_P80001562_377363
		   if (hdlr->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
		      PRE_CFG.t_osco[p][ch] = cinit_ps_to_tck(timing->lpddr5_tosco, tck_ps) + 25;
		   } else {
		      PRE_CFG.t_osco[p][ch] = cinit_ps_to_tck(timing->lpddr5_tosco, tck_ps);
		   }
		#else  // DWC_DDRCTL_LPDDR54_OSCO_P80001562_377363
        	   PRE_CFG.t_osco[p][ch] = cinit_ps_to_tck(timing->lpddr5_tosco, tck_ps);
		#endif // DWC_DDRCTL_LPDDR54_OSCO_P80001562_377363

        	PRE_CFG.t_pbr2pbr[p][ch] = cinit_ps_to_tck(timing->lpddr5_tpbr2pbr_ps, SPD.tck_ps[p]);
                PRE_CFG.t_pbr2pbr_mp[p][ch] = cinit_ps_to_tck(timing->lpddr5_tpbr2pbr_mp_ps, SPD.tck_ps[p]);
        	PRE_CFG.t_pbr2act[p][ch] = cinit_ps_to_tck(timing->lpddr5_tpbr2act_ps, SPD.tck_ps[p]);

        	PRE_CFG.max_rd_sync[p][ch] = PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_tck + timing->lpddr5_twck_pst_wck / ratio;
        	PRE_CFG.max_wr_sync[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_tck + timing->lpddr5_twck_pst_wck / ratio;
        	//int tmp = timing->lpddr5_wckenl_rd_tck * ratio;
        	//if (tmp <= 4)
        	//    SNPS_ERROR("PHY does not support zero or negative lpddr5_wckenl_rd_tck value", NULL);
        	//tmp = timing->lpddr5_wckenl_wr_tck * ratio;
        	//if (tmp <= 4)
        	//    SNPS_ERROR("PHY does not support zero or negative lpddr5_wckenl_wr_tck value", NULL);


        	// RL + RU(tWCKDQO(max)/tCK)) + BL/n_max + MAX[RU(7.5ns/tCK),4nCK] + nRBTP
        	PRE_CFG.rd2mr[p][ch] = PRE_CFG.rl[p][ch] + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + timing->lpddr5_bl_n_max_tck + max(CEIL(7500, tck_ps), 4) + PRE_CFG.nrbtp[p][ch];

		// WL + BL/n_max + MAX[RU(7.5ns/tCK),4nCK] + nWR
		PRE_CFG.wr2mr[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_tck + max(CEIL(7500, tck_ps), 4) + CEIL(timing->lpddr5_twr_ps, tck_ps);
		PRE_CFG.lpddr5_cdd = 1;	// temporary

		    PRE_CFG.ws_off2ws_fs[p][ch] = 3;
		PRE_CFG.t_wcksus[p][ch] = 4;
       		// tWCKENL_FS + tWCKPRE_Static + 2
		PRE_CFG.ws_fs2wck_sus[p][ch] = timing->lpddr5_wckenl_fs_tck + timing->lpddr5_wckpre_static_tck + 2;

        	cinit_cal_lpddr54_pre_cfg_timing_1st_set(hdlr, p, ch, 0);

        	PRE_CFG.t_pdn[p][ch] = cinit_ps_to_tck(timing->lpddr5_tpdn_ps, tck_ps);
#ifdef MEMC_BURST_LENGTH_32 
        	PRE_CFG.t_ccd_blx2[p][ch] = timing->lpddr5_tccd_l_bl32_tck;
        	PRE_CFG.t_ccd_mw_blx2[p][ch] = timing->lpddr5_tccdmw_bl32_tck;
		PRE_CFG.wra2pre_blx2[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_min_bl32_tck + 1 + PRE_CFG.nwr[p][ch];
        	PRE_CFG.rda2pre_blx2[p][ch] = timing->lpddr5_bl_n_min_bl32_tck + PRE_CFG.nrbtp[p][ch];
		PRE_CFG.rd2mr_blx2[p][ch] = PRE_CFG.rl[p][ch] + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + timing->lpddr5_bl_n_max_bl32_tck + max(CEIL(7500, tck_ps), 4) + PRE_CFG.nrbtp[p][ch];
		PRE_CFG.wr2mr_blx2[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + max(CEIL(7500, tck_ps), 4) + CEIL(timing->lpddr5_twr_ps, tck_ps);
        	PRE_CFG.max_rd_sync_blx2[p][ch] = PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + timing->lpddr5_twck_pst_wck / ratio;
        	PRE_CFG.max_wr_sync_blx2[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + timing->lpddr5_twck_pst_wck / ratio;
#endif /* MEMC_BURST_LENGTH_32 */

        break;
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */
    default:
        SNPS_ERROR("sdram type %u not yet supported", SPD.sdram_protocol);
        dwc_ddrctl_cinit_exit(1);
        break;
    }
    PRE_CFG.cl_dbi[p] = cl_dbi;
	if(IS_DDR5) {
		PRE_CFG.twr[p][ch] = twr / tck_ps; // round down
    } else {
		PRE_CFG.twr[p][ch] = cinit_ps_to_tck(twr, tck_ps);
    }

#ifdef DDRCTL_DDR
    if (IS_DDR4) {
        // ddr4_wr_preamble = 1 is only valid for DDR4-2400/2666/2933/3200
        // geardown_mode = 1 is selected for Speed Grade    2666/2933/3200
        // When speed grade is 2933/3200, ddr4_wr_preamble and geardown_mode are constrained not to be 1 at the same time as the tWR/tRTP will go outside the valid range described in the JEDEC-4C
        // When speed grade is 2666, the default tWR/tRTP is 20/10, so when ddr4_wr_preamble and geardown_mode are both enabled, that default value will becomes to "tWR/tRTP + 2 + 2" to satisfied the requirements
        //                           -  when ddr4_wr_preamble is enabled, tWR is incresed by one or two, and the final incremented value must be an even number
        //                           -  when geardown_mode is enabled, tWR and tRTP both must be even numbers
		PRE_CFG.twr[p][ch] = (PRE_CFG.twr[p][ch] % 2) ?  ((QDYN.ddr4_wr_preamble[p][ch]) ? PRE_CFG.twr[p][ch] + 1 : PRE_CFG.twr[p][ch]) : ((QDYN.ddr4_wr_preamble[p][ch] && QDYN.geardown_mode[ch] ) ? PRE_CFG.twr[p][ch] + 4 : ( (QDYN.ddr4_wr_preamble[p][ch]) ? PRE_CFG.twr[p][ch] + 2 : PRE_CFG.twr[p][ch]));

		// ensure twr is an even number as not supported otherwise
		PRE_CFG.twr[p][ch] = (PRE_CFG.twr[p][ch] % 2) ? PRE_CFG.twr[p][ch] + 1 : PRE_CFG.twr[p][ch];
	}
	else if (IS_DDR5) {
		PRE_CFG.twr[p][ch] = (PRE_CFG.twr[p][ch] % 6) ? (PRE_CFG.twr[p][ch] + 6 - PRE_CFG.twr[p][ch] % 6) : PRE_CFG.twr[p][ch];
    }

    SNPS_LOG("tWR = %u", PRE_CFG.twr[p][ch]);

    PRE_CFG.txpdll[p][ch] = cinit_ps_to_tck(txpdll, tck_ps);
#endif /* DDRCTL_DDR */
	if (IS_DDR4 || IS_DDR5)
		PRE_CFG.twtr[p][ch] = twtr;
	else
		PRE_CFG.twtr[p][ch] = cinit_ps_to_tck(twtr, tck_ps);

	if (IS_DDR4) {
		PRE_CFG.t_rtp[p][ch] = PRE_CFG.twr[p][ch] / 2;
	} else {
		PRE_CFG.t_rtp[p][ch] = cinit_ps_to_tck(trtp, tck_ps);
		if (IS_DDR5) {
			if (PRE_CFG.t_rtp[p][ch] == 13 || PRE_CFG.t_rtp[p][ch] == 16 || PRE_CFG.t_rtp[p][ch] == 19 || PRE_CFG.t_rtp[p][ch] == 22) {
				PRE_CFG.t_rtp[p][ch]++;
			}
		}
	}

#ifdef DDRCTL_LPDDR
    // Only use RD(tODTon(min) / tCK) for LPDDR4
    PRE_CFG.odton_min[p][ch] = timing->lpddr4_todton_min / tck_ps;
#endif /* DDRCTL_LPDDR */

    if (!IS_DDR5)
        PRE_CFG.tfaw[p][ch] = cinit_ps_to_tck(tfaw, tck_ps);
    else
        PRE_CFG.tfaw[p][ch] = tfaw;
    if (!(IS_DDR5)) {
        PRE_CFG.t_ras_max[p][ch] = DIV_1024(tras_max / tck_ps);
        if (PRE_CFG.t_ras_max[p][ch] > 255)
            PRE_CFG.t_ras_max[p][ch] = 255;
        if (PRE_CFG.t_ras_max[p][ch] == 0) {
            SNPS_LOG("t_ras_max cannot be 0, setting to 1", NULL);
            PRE_CFG.t_ras_max[p][ch] = 1;
        }
    }
    PRE_CFG.t_ras_min[p][ch] = cinit_ps_to_tck(tras_min, tck_ps);
    PRE_CFG.txp[p][ch] = CEIL(txp, tck_ps);
    PRE_CFG.t_rc[p][ch] = cinit_ps_to_tck(t_rc, tck_ps);

#ifdef DDRCTL_DDR
    //MEMC_DDR5
    if (IS_DDR5 && (IS_RDIMM|| IS_LRDIMM)) {
        PRE_CFG.t_pd[p][ch] = max(cinit_ps_to_tck(timing->ddr5_tpd_ps, tck_ps), cinit_ps_to_tck(timing->ddr5_rcd_tpdex_ps, tck_ps));
        // RCD Parameters
        if (IS_LRDIMM) {
                // max of
                // ddr5_rcd_tstab01_max_ps,
                // ddr5_rcd_tstab_dbcmd_ps,
                // ddr5_rcd_tstab_dbdata_ps - ddr5_txs_ps
                t_stab01_max_ps = max(timing->ddr5_rcd_tstab01_max_ps,timing->ddr5_rcd_tstab_dbcmd_ps);
                t_stab01_max_ps = max(t_stab01_max_ps,
                                      (timing->ddr5_rcd_tstab_dbdata_ps - timing->ddr5_txs_ps));

                PRE_CFG.t_stab01[p][ch] = cinit_ps_to_tck(t_stab01_max_ps, tck_ps);

                PRE_CFG.t_cssr[p][ch] = cinit_ps_to_tck(max(timing->ddr5_rcd_tcssr_ps,timing->ddr5_rcd_tcssr_db_ps), tck_ps);
                PRE_CFG.t_cpded2srx[p][ch] = max(timing->ddr5_rcd_tcpded2srx_tck,timing->ddr5_rcd_tcpded2srx_db_tck);
        } else {

                PRE_CFG.t_stab01[p][ch] = cinit_ps_to_tck(timing->ddr5_rcd_tstab01_max_ps, tck_ps);
                PRE_CFG.t_cssr[p][ch] = cinit_ps_to_tck(timing->ddr5_rcd_tcssr_ps, tck_ps);
                PRE_CFG.t_cpded2srx[p][ch] = timing->ddr5_rcd_tcpded2srx_tck;
        }
        PRE_CFG.t_srx2srx[p][ch] = max((timing->ddr5_rcd_tsrx2srx_tck), (16 + cinit_ps_to_tck(timing->ddr5_tcsh_srexit_ps, tck_ps)));
        PRE_CFG.t_ckoff[p][ch] = cinit_ps_to_tck(timing->ddr5_rcd_tckoff_ps, tck_ps);
        PRE_CFG.t_ckact[p][ch] = timing->ddr5_rcd_tckact_tck;
        PRE_CFG.t_csalt[p][ch] = timing->ddr5_rcd_tcsalt_tck;
    } else {
        PRE_CFG.t_pd[p][ch] = cinit_ps_to_tck(timing->ddr5_tpd_ps, tck_ps);
    }
    PRE_CFG.t_mpsmx[p][ch] = cinit_ps_to_tck(timing->ddr5_tmpsmx_ps, tck_ps);
    PRE_CFG.t_mpdpxact[p][ch] = cinit_ps_to_tck(timing->ddr5_tmpdpdact_ps, tck_ps);

    PRE_CFG.t_pda_latch[p][ch] = cinit_ps_to_tck(timing->ddr5_tpda_latch_min_ps, tck_ps);
    PRE_CFG.t_pda_delay[p][ch] = cinit_ps_to_tck(timing->ddr5_tpda_delay_ps, tck_ps);
    PRE_CFG.t_pda_dqs_delay[p][ch] = cinit_ps_to_tck(timing->ddr5_tpda_dqs_delay_min_ps, tck_ps);
    PRE_CFG.t_pda_s[p][ch] = timing->ddr5_tpda_s_tck;
    PRE_CFG.t_pda_h[p][ch] = timing->ddr5_tpda_h_tck;


    if (IS_LRDIMM) {
        PRE_CFG.t_cpded[p][ch] = cinit_ps_to_tck(max(timing->ddr5_tcpded_ps,timing->ddr5_tcpded_db_ps), tck_ps);
    } else {
        PRE_CFG.t_cpded[p][ch] = cinit_ps_to_tck(timing->ddr5_tcpded_ps, tck_ps);
    }
    PRE_CFG.t_casrx[p][ch] = cinit_ps_to_tck(timing->ddr5_tcasrx_ps, tck_ps);
    PRE_CFG.t_csh_srexit[p][ch] = cinit_ps_to_tck(timing->ddr5_tcsh_srexit_ps, tck_ps);
    PRE_CFG.t_csl_srexit[p][ch] = timing->ddr5_tcsl_srexit_tck;

    PRE_CFG.t_mpc_cs[p][ch] = timing->ddr5_tmpc_cs_min_tck;

	PRE_CFG.t_mpc_setup[p][ch] = timing->ddr5_tmc_mpc_setup_tck;
	PRE_CFG.t_mpc_hold[p][ch] = timing->ddr5_tmc_mpc_hold_tck;
	PRE_CFG.t_ccd_w[p][ch] = timing->ddr5_tccd_l_wr_tck;
	PRE_CFG.t_ccd_w_m[p][ch] = timing->ddr5_tccd_m_wr_tck;
	PRE_CFG.t_wr2rd_dpr[p][ch] = bl_div2 + QDYN.wr_crc_enable;
	PRE_CFG.t_rd2wr_dpr[p][ch] = bl_div2 + QDYN.rd_crc_enable;

	if (IS_DDR5) {
		PRE_CFG.t_xs_min[p][ch] = DIV_32(cinit_ps_to_tck(timing->ddr5_txs_ps, tck_ps)) + 1;
	}

	PRE_CFG.t_ccd_w2[p][ch] = timing->ddr5_tccd_l_wr2_tck;

#ifdef DDRCTL_DDR5CTL
#ifdef DDRCTL_LLC_4CYCSCH
	if (IS_DDR5) {
		if (timing->ddr5_tccd_l_tck < 16) {
			PRE_CFG.t_ccd_r_l[p][ch] = 16;
		}
	}
#endif /* DDRCTL_LLC_4CYCSCH */
#endif /* DDRCTL_DDR5CTL */

#endif /* DDRCTL_DDR */

#ifdef MEMC_LPDDR2
    PRE_CFG.tINITTMG1[ch] = 100;
    PRE_CFG.tINIT2 = 5;
    PRE_CFG.tINIT3 = 200;
    PRE_CFG.tINIT4[p] = DIV_32(10000000 / (tck_ps * MEMC_FREQ_RATIO));
    if (((10000000 / (tck_ps * MEMC_FREQ_RATIO)) % 32) != 0)
        PRE_CFG.tINIT4[p]++;

    PRE_CFG.tINITTMG3[ch] = DIV_1024(10000000 / (tck_ps * MEMC_FREQ_RATIO));
    if (((10000000 / (tck_ps * MEMC_FREQ_RATIO)) % 1024) != 0)
        PRE_CFG.tINITTMG3[ch]++;
#endif /* MEMC_LPDDR2 */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        PRE_CFG.t_mrw[p][ch] = timing->lpddr4_tmrwckel / tck_ps;
        if (PRE_CFG.t_mrw[p][ch] < timing->lpddr4_tmrw)
            PRE_CFG.t_mrw[p][ch] = timing->lpddr4_tmrw;
    }
#endif /* IS_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        uint32_t tmrwpd = cinit_ps_to_tck(timing->lpddr5_tmrwpd_ps, tck_ps);
        uint32_t tmrw = cinit_ps_to_tck(timing->lpddr5_tmrw_ps, tck_ps);

        PRE_CFG.t_mrw[p][ch] = max(tmrw, tmrwpd);
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR5
    if (IS_DDR5)
        PRE_CFG.t_mrw[p][ch] = timing->ddr5_tmrw_tck;
#endif  // CINIT_DDR5
#endif /* DDRCTL_DDR */

    PRE_CFG.t_mr[p][ch] = t_mr;

#ifdef DDRCTL_DDR
    PRE_CFG.t_mod[p][ch] = t_mod;
    // min is 12 cycles.
    if (PRE_CFG.t_mod[p][ch] < 12)
        PRE_CFG.t_mod[p][ch] = 12;
    if (hdlr->memCtrlr_m.ddr4_mr[p].mr4.cal != 0) {
        uint32_t cal_cycles;

        cal_cycles = get_cal_cycles(hdlr->memCtrlr_m.ddr4_mr[p].mr4.cal);
        PRE_CFG.t_mr[p][ch] += cal_cycles;
        PRE_CFG.t_mod[p][ch] += cal_cycles;
    }
    if (timing->ddr4_tpl_tck != 0)
        PRE_CFG.t_mod[p][ch] += timing->ddr4_tpl_tck;
#endif /* DDRCTL_DDR */

    PRE_CFG.t_rcd[p][ch] = cinit_ps_to_tck(trcd, tck_ps);
    {
        uint32_t rcd_min = 2;

        if (PRE_CFG.t_rcd[p][ch] > SPD.tAL && (PRE_CFG.t_rcd[p][ch] - SPD.tAL) > rcd_min)
            PRE_CFG.t_rcd[p][ch] = PRE_CFG.t_rcd[p][ch] - SPD.tAL;
        else
            PRE_CFG.t_rcd[p][ch] = rcd_min;
#ifdef DDRCTL_DDR
#ifdef CINIT_DDR5
        ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[p];
        if (IS_DDR5 && mregs->mr2.ddr5_2n_mode == 0) {
            // For DDR5 2N mode, it is recommended to set this value as multiple of
            // MEMC_FREQ_RATIO to improve the performance.
            while (PRE_CFG.t_rcd[p][ch] % MEMC_FREQ_RATIO != 0) {
                PRE_CFG.t_rcd[p][ch]++;
            }
        }
#endif  // CINIT_DDR5
#endif /* DDRCTL_DDR */
    }

#ifdef DDRCTL_DDR
    PRE_CFG.t_rrd[p][ch] = timing->trrd_l_tck;
#else /* DDRCTL_DDR */
    PRE_CFG.t_rrd[p][ch] = cinit_ps_to_tck(trrd, tck_ps);
#endif /* DDRCTL_DDR */

    PRE_CFG.t_rp[p][ch] = cinit_ps_to_tck(trp, tck_ps);


    PRE_CFG.t_cke[p][ch] = cinit_ps_to_tck(PRE_CFG.t_cke[p][ch], tck_ps);
    if (IS_LPDDR4 && PRE_CFG.t_ckesr[p][ch] > PRE_CFG.t_cke[p][ch])
        PRE_CFG.t_cke[p][ch] = PRE_CFG.t_ckesr[p][ch];

#ifdef DDRCTL_LPDDR
    PRE_CFG.t_rc[p][ch] = cinit_ps_to_tck(t_rc, tck_ps);
#endif
#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
	if(IS_DDR4) {
		PRE_CFG.t_rc[p][ch] = cinit_ps_to_tck(t_rc, tck_ps);
	}
#endif
#ifdef CINIT_DDR5
	if(IS_DDR5) {
		PRE_CFG.t_rc[p][ch] = PRE_CFG.t_rp[p][ch] + PRE_CFG.t_ras_min[p][ch];
	}
#endif
#endif

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        // check write latency set
        PRE_CFG.odtloff[p][ch] = (hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls == 0) ? timing->lpddr4_odtloff_latency_seta : timing->lpddr4_odtloff_latency_setb;
        PRE_CFG.odtlon[p][ch] = (hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls == 0) ? timing->lpddr4_odtlon_latency_seta : timing->lpddr4_odtlon_latency_setb;

    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        PRE_CFG.odtlon[p][ch] = timing->lpddr5_odtlon_tck;
        PRE_CFG.odtloff[p][ch] = timing->lpddr5_odtloff_tck;
        //BL32
        PRE_CFG.odtlon_blx2[p][ch] = timing->lpddr5_odtlon_bl32_tck;
        PRE_CFG.odtloff_blx2[p][ch] = timing->lpddr5_odtloff_bl32_tck;
    }

    PRE_CFG.t_rcd_write[p][ch] = cinit_ps_to_tck(trcd_write, tck_ps);
    {
        uint32_t rcd_write_min = 2; //Table 392 JESD209-B

        if (PRE_CFG.t_rcd_write[p][ch] > rcd_write_min)
            PRE_CFG.t_rcd_write[p][ch] = PRE_CFG.t_rcd_write[p][ch];
        else
            PRE_CFG.t_rcd_write[p][ch] = rcd_write_min;
    }
#endif  /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_LPDDR
    PRE_CFG.wdqspreext[p][ch] = PRE_CFG.cwl_x[p] - ((hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls == 0) ? timing->lpddr4_wdqson_seta : timing->lpddr4_wdqson_setb);
#endif /* DDRCTL_LPDDR */

    cinit_cal_rd2wr(hdlr, p, ch, n);


    if (hdlr->ddrPhyType_m == DWC_LPDDR4X_MULTIPHY)
        cinit_cal_lpddr4x_multiphy_dfi_timings(hdlr, p, ch);
    else if (hdlr->ddrPhyType_m == DWC_LPDDR54_PHY)
        cinit_cal_lpddr54_dfi_timings(hdlr, p, ch);
    else if (hdlr->ddrPhyType_m == DWC_DDR54_PHY_V2)
        cinit_cal_ddr54_dfi_timings(hdlr, p, ch, n);
    else if (hdlr->ddrPhyType_m == DWC_DDR54_PHY)
        cinit_cal_ddr54_dfi_timings(hdlr, p, ch, n);
    else if (hdlr->ddrPhyType_m == DWC_LPDDR5X4_PHY)
        cinit_cal_lpddr54_dfi_timings(hdlr, p, ch);
    else if (hdlr->ddrPhyType_m == DWC_DDR5_PHY)
        cinit_cal_ddr54_dfi_timings(hdlr, p, ch, n);
    else {
        SNPS_ERROR("Unknown PhyType to calculate dfi_timing parameters", NULL);
        dwc_ddrctl_cinit_exit(1);
    }

    if (IS_RDIMM || IS_LRDIMM)
        PRE_CFG.cmd_lat_adder[p][ch] = (tck_ps < 833) ? 2 : 1;
    cinit_cal_wr2rd(hdlr, p, ch, n);
#ifdef DDRCTL_LPDDR_MIXED_PKG
    cinit_encode_wr_recovery(hdlr, p, ch, n, STATIC.lpddr_mixed_pkg_en);
    cinit_encode_rl_wl(hdlr, p, ch, n, STATIC.lpddr_mixed_pkg_en);
#else 
    cinit_encode_wr_recovery(hdlr, p, ch, n, 0);
    cinit_encode_rl_wl(hdlr, p, ch, n, 0);
#endif /* DDRCTL_LPDDR_MIXED_PKG */

#ifdef DDRCTL_DDR
    cinit_encode_cas_latency(hdlr, p, n);
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        cinit_encode_cas_write_latency(hdlr, p);
        if (hdlr->memCtrlr_m.ddr4_mr[p].mr2.write_crc && hdlr->memCtrlr_m.ddr4_mr[p].mr5.data_mask)
            cinit_encode_write_cmd_latency(hdlr, p, n);
    }
#endif  // CINIT_DDR4
#ifdef CINIT_DDR5
    if (IS_DDR5)
        cinit_encode_ddr5_trtp_latency(hdlr, p, ch);
#endif  // CINIT_DDR5
    cinit_encode_tccd_l_latency(hdlr, p, ch);
    cinit_pasctl(hdlr, ch);
#endif /* DDRCTL_DDR */

#ifdef MEMC_NUM_RANKS_GT_1
    cinit_cal_rd2wr_dr(hdlr, p, ch, n);
    cinit_cal_wr2rd_dr(hdlr, p, ch, n);
    cinit_cal_diff_rank_rd_gap(hdlr, p, ch, n);
    cinit_cal_diff_rank_wr_gap(hdlr, p, ch, n);
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef DDRCTL_LPDDR
    cinit_cal_mrr2rdwr(hdlr, p, ch, n);
#endif /* DDRCTL_LPDDR */



#ifdef DDRCTL_WR_CRC_RETRY
    cinit_cal_retry_window(hdlr, p, ch, n);
#endif //DDRCTL_WR_CRC_RETRY

#ifdef CINIT_DDR5
    // Adjust refab_hi_sch_gap/refsb_hi_sch_gap to recommended values
    if (IS_DDR5) {
        ddrctl_error_t  rslt;
        uint32_t trfc_min_tck = CEIL(hdlr->timingParams_m[p][n].ddr5_trfc_fgr_ps, tck_ps);
        rslt = ddrctl_cinit_get_ddr5_refab_sch_gap_tck(trfc_min_tck, PRE_CFG.refab_hi_sch_gap[p][ch],
                                                       &PRE_CFG.refab_hi_sch_gap[p][ch]);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("[Pstate %u][Ch %u] Calculation of REFab gap failed", p, ch);
            dwc_ddrctl_cinit_exit(1);
        }
        rslt = ddrctl_cinit_get_ddr5_refsb_sch_gap_tck(hdlr, p, n, PRE_CFG.refsb_hi_sch_gap[p][ch],
                                                       &PRE_CFG.refsb_hi_sch_gap[p][ch]);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("[Pstate %u][Ch %u] Calculation of REFsb gap failed", p, ch);
            dwc_ddrctl_cinit_exit(1);
        }
        SNPS_DEBUG("[Pstate %u][Ch %u] ref_hi_sch_gap refab %d", p, ch, PRE_CFG.refab_hi_sch_gap[p][ch]);
        SNPS_DEBUG("[Pstate %u][Ch %u] ref_hi_sch_gap refsb %d", p, ch, PRE_CFG.refsb_hi_sch_gap[p][ch]);
    }
#endif  // CINIT_DDR5

    SNPS_TRACE("Leaving");
}

void cinit_cal_pre_cfg_timing_2nd_set(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
#ifdef DDRCTL_TWO_TIMING_SETS_EN
#ifdef CINIT_DDR5
    uint8_t                 bl_div2;
    uint32_t                tck_ps = SPD.tck_ps[p];
    ddrctl_error_t          rslt;
    ddrTimingParameters_t   *timing = &hdlr->timingParams_m[p][n];

    // BL/2 (Burst Length / 2)
    bl_div2 = DIV_2(timing->burst_length);

    if (IS_DDR5 && DWC_DDRCTL_DEV_CFG_NUM == 2) {
        ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[p];
        uint32_t ddr5_eq1_rd2pre, ddr5_eq2_rd2pre;
        uint32_t rd_dqs_offset = cinit_get_ddr5_t_rd_dqs_offset(hdlr, p);
        uint32_t tWPRE = cinit_get_ddr5_twpre(hdlr, p);
        uint32_t ratio;

        ratio = ddrctl_sw_get_ratio_factor(hdlr, p);

        PRE_CFG.twr_2[p][ch] = cinit_ps_to_tck(timing->ddr5_twr_ps, tck_ps);
        PRE_CFG.twr_2[p][ch] = (PRE_CFG.twr_2[p][ch] % 6) ? (PRE_CFG.twr_2[p][ch] + 6 - PRE_CFG.twr_2[p][ch] % 6) : PRE_CFG.twr_2[p][ch];

        PRE_CFG.twtr_2[p][ch] = timing->ddr5_twtr_l_tck;
        PRE_CFG.twtr_s_2[p][ch] = timing->ddr5_twtr_s_tck;

        PRE_CFG.t_rtp_2[p][ch] = cinit_ps_to_tck(timing->ddr5_trtp_ps, tck_ps);
        PRE_CFG.t_rp_2[p][ch] = cinit_ps_to_tck(timing->trp_ps, tck_ps);

        PRE_CFG.wr2pre_2[p][ch] = PRE_CFG.cwl_x_2[p] + bl_div2 + PRE_CFG.twr_2[p][ch] + QDYN.wr_crc_enable + CEIL(timing->ddr5_tdqs2dq_ps, tck_ps);
        PRE_CFG.tfaw_2[p][ch] = CID_WIDTH(n) ? timing->ddr5_tfaw_slr_tck : timing->ddr5_tfaw_tck;
        PRE_CFG.t_ras_min_2[p][ch] = cinit_ps_to_tck(timing->ddr5_tras_min_ps, tck_ps);

        ddr5_eq1_rd2pre = PRE_CFG.t_rtp_2[p][ch];
        ddr5_eq2_rd2pre = PRE_CFG.cl_2[p] + bl_div2 - PRE_CFG.t_rp_2[p][ch];
        PRE_CFG.rd2pre_2[p][ch] = max(ddr5_eq1_rd2pre, ddr5_eq2_rd2pre);

		PRE_CFG.t_rc_2[p][ch] = PRE_CFG.t_ras_min_2[p][ch] + PRE_CFG.t_rp_2[p][ch];
		PRE_CFG.rd2wr_2[p][ch] = PRE_CFG.cl_2[p] + bl_div2 + 2 + tWPRE + ((mregs->mr8.rd_postamble) ? 1 : 0) + QDYN.rd_crc_enable - rd_dqs_offset - PRE_CFG.cwl_x_2[p];
		if (IS_LRDIMM) {
			// For DDR5 LRDIMM, add ddr5_rcd_tpdm_wr_ps + ddr5_rcd_tpdm_rd_ps
			PRE_CFG.rd2wr_2[p][ch]+=CEIL((timing->ddr5_rcd_tpdm_wr_ps + timing->ddr5_rcd_tpdm_rd_ps), SPD.tck_ps[p]);
		}
		PRE_CFG.wr2rd_2[p][ch] = PRE_CFG.cwl_x_2[p] + bl_div2 + QDYN.wr_crc_enable + PRE_CFG.twtr_2[p][ch] + CEIL(timing->ddr5_tdqs2dq_ps, tck_ps);
		PRE_CFG.t_wr2rd_m_2[p][ch] = PRE_CFG.cwl_x_2[p] + bl_div2 + QDYN.wr_crc_enable + timing->ddr5_twtr_m_tck + CEIL(timing->ddr5_tdqs2dq_ps, tck_ps);
		PRE_CFG.t_mr_2[p][ch] = timing->ddr5_tmrd_tck;
		PRE_CFG.t_rcd_2[p][ch] = cinit_ps_to_tck(timing->trcd_ps, tck_ps);
		if (mregs->mr2.ddr5_2n_mode == 0) {
			// For DDR5 2N mode, it is recommended to set this value as multiple of
			// MEMC_FREQ_RATIO to improve the performance.
			PRE_CFG.t_rcd_2[p][ch] = ((PRE_CFG.t_rcd_2[p][ch] + MEMC_FREQ_RATIO -1) / MEMC_FREQ_RATIO) * MEMC_FREQ_RATIO;
		}
		PRE_CFG.t_rrd_2[p][ch] = timing->trrd_l_tck;
		PRE_CFG.t_rrd_s_2[p][ch] = timing->trrd_s_tck;
		PRE_CFG.wr2rd_s_2[p][ch] = PRE_CFG.cwl_x_2[p] + bl_div2 + QDYN.wr_crc_enable + PRE_CFG.twtr_s_2[p][ch] + CEIL(timing->ddr5_tdqs2dq_ps, tck_ps);
		PRE_CFG.t_ccd_w2_2[p][ch] = timing->ddr5_tccd_l_wr2_tck;
		PRE_CFG.t_ppd_2[p][ch] = timing->ddr5_tppd_tck;
		PRE_CFG.t_wr2rd_dpr_2[p][ch] = bl_div2 + QDYN.wr_crc_enable;
		PRE_CFG.t_rd2wr_dpr_2[p][ch] = bl_div2 + QDYN.rd_crc_enable;
		PRE_CFG.t_ccd_w_s_2[p][ch] = QDYN.wr_crc_enable ? (timing->ddr5_tccd_s_tck + hdlr->ddr5_interamble_tccd_offset.t_ccd_w_offset[p][ch] + 1) : (timing->ddr5_tccd_s_tck + hdlr->ddr5_interamble_tccd_offset.t_ccd_w_offset[p][ch]);
		PRE_CFG.t_ccd_r_s_2[p][ch] = QDYN.rd_crc_enable ? (timing->ddr5_tccd_s_tck + hdlr->ddr5_interamble_tccd_offset.t_ccd_r_offset[p][ch] + 1) : (timing->ddr5_tccd_s_tck + hdlr->ddr5_interamble_tccd_offset.t_ccd_r_offset[p][ch]);
		PRE_CFG.t_ccd_w_2[p][ch] = timing->ddr5_tccd_l_wr_tck;
		PRE_CFG.t_ccd_w_m_2[p][ch] = timing->ddr5_tccd_m_wr_tck;
		PRE_CFG.t_ccd_r_2[p][ch] = QDYN.rd_crc_enable ? (timing->ddr5_tccd_l_tck + 1) : timing->ddr5_tccd_l_tck;
		PRE_CFG.t_ccd_r_m_2[p][ch] = QDYN.rd_crc_enable ? (timing->ddr5_tccd_m_tck + 1) : timing->ddr5_tccd_m_tck;
		PRE_CFG.t_refi_x1_x32_2[p][ch] = DIV_32(timing->ddr5_trefi1_ps / tck_ps);
		PRE_CFG.t_rfc_min_2[p][ch] = CEIL(timing->ddr5_trfc_fgr_ps, tck_ps);
		PRE_CFG.t_refsbrd_2[p][ch] = CEIL(timing->ddr5_trefsbrd_ps, tck_ps);
		PRE_CFG.t_rfcsb_2[p][ch] = cinit_ps_to_tck(timing->ddr5_trfcsb_ps, tck_ps);
		PRE_CFG.t_zq_short_nop_2[p][ch] = cinit_ps_to_tck(timing->ddr5_tzqlat_ps, tck_ps);
		PRE_CFG.t_zq_long_nop_2[p][ch] = cinit_ps_to_tck(timing->ddr5_tzqcal_ps, tck_ps);
		PRE_CFG.t_xs_x32_2[p][ch] = DIV_32(cinit_ps_to_tck(timing->ddr5_txs_ps, tck_ps)) + 1;

#ifdef DDRCTL_DDR5CTL
#ifdef DDRCTL_LLC_4CYCSCH
	if (IS_DDR5) {
		if (timing->ddr5_tccd_l_tck < 16) {
			PRE_CFG.t_ccd_r_2[p][ch] = 16;
		}
	}
#endif /* DDRCTL_LLC_4CYCSCH */
#endif /* DDRCTL_DDR5CTL */



#ifdef UMCTL2_CID_EN
		PRE_CFG.t_ccd_dlr_2[p][ch] = timing->ddr5_tccd_s_tck;
		PRE_CFG.t_rrd_dlr_2[p][ch] = timing->ddr5_trrd_dlr_tck;
		PRE_CFG.t_faw_dlr_2[p][ch] = timing->ddr5_tfaw_dlr_tck;
		PRE_CFG.t_wr2rd_dlr_2[p][ch] = PRE_CFG.cwl_x_2[p] + bl_div2 + QDYN.wr_crc_enable + PRE_CFG.twtr_s_2[p][ch] + CEIL(timing->ddr5_tdqs2dq_ps, tck_ps);
		PRE_CFG.t_rd2wr_dlr_2[p][ch] = PRE_CFG.cl_2[p] + bl_div2 + 2 + tWPRE + (mregs->mr8.rd_postamble ? 1 : 0) + QDYN.rd_crc_enable - rd_dqs_offset - PRE_CFG.cwl_x_2[p];
		if (IS_LRDIMM) {
			// For DDR5 LRDIMM, add ddr5_rcd_tpdm_wr_ps + ddr5_rcd_tpdm_rd_ps
			PRE_CFG.t_rd2wr_dlr_2[p][ch]+=CEIL((timing->ddr5_rcd_tpdm_wr_ps + timing->ddr5_rcd_tpdm_rd_ps), SPD.tck_ps[p]);
		}
		PRE_CFG.t_rfc_min_dlr_2[p][ch] = CEIL(timing->ddr5_trfc_dlr_fgr_ps, tck_ps);
		PRE_CFG.t_rfcsb_dlr_2[p][ch] = cinit_ps_to_tck(timing->ddr5_trfcsb_dlr_ps, tck_ps);
		PRE_CFG.t_refsbrd_dlr_2[p][ch] = cinit_ps_to_tck(timing->ddr5_trefsbrd_dlr_ps, tck_ps);
#endif
    }

    // Adjust refab_hi_sch_gap/refsb_hi_sch_gap to recommended values
    if (IS_DDR5) {
        uint32_t trfc_min_tck = CEIL(hdlr->timingParams_m[p][n].ddr5_trfc_fgr_ps, tck_ps);
        rslt = ddrctl_cinit_get_ddr5_refab_sch_gap_tck(trfc_min_tck, PRE_CFG.refab_hi_sch_gap_2[p][ch],
                                                       &PRE_CFG.refab_hi_sch_gap_2[p][ch]);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("[Pstate %u][Ch %u] Calculation of REFab gap failed", p, ch);
            dwc_ddrctl_cinit_exit(1);
        }
        rslt = ddrctl_cinit_get_ddr5_refsb_sch_gap_tck(hdlr, p, n, PRE_CFG.refsb_hi_sch_gap_2[p][ch],
                                                       &PRE_CFG.refsb_hi_sch_gap_2[p][ch]);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("[Pstate %u][Ch %u] Calculation of REFsb gap failed", p, ch);
            dwc_ddrctl_cinit_exit(1);
        }
        SNPS_DEBUG("[Pstate %u][Ch %u] ref_hi_sch_gap refab %d", p, ch, PRE_CFG.refab_hi_sch_gap[p][ch]);
        SNPS_DEBUG("[Pstate %u][Ch %u] ref_hi_sch_gap refsb %d", p, ch, PRE_CFG.refsb_hi_sch_gap[p][ch]);
    }

#endif
#endif
}

/** @brief Calculate CWL adjusted.
 * for DDR4 write preamble, CWL is increased by 2 if VIRL_DDR4_WR_PREAMBLE == 2
 */
uint32_t cinit_cal_cwlx(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
    uint32_t cwlx = 0;

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        uint32_t tcwl_tck;

        SNPS_LOG("p = %u, memCtrlr_mr4_wr_preamble = %u", p, hdlr->memCtrlr_m.ddr4_mr[p].mr4.wr_preamble);
        SNPS_LOG("SPD.use_ddr4_tcwl_1st_set = %u", SPD.use_ddr4_tcwl_1st_set);
        tcwl_tck = (SPD.use_ddr4_tcwl_1st_set) ? timing->ddr4_tcwl_1st_set_tck : timing->ddr4_tcwl_2nd_set_tck;
        SNPS_LOG("tcwl_tck = %u", tcwl_tck);

        if (QDYN.ddr4_wr_preamble[p][ch] && SPD.use_ddr4_tcwl_1st_set)
            tcwl_tck = tcwl_tck + 2;

        cwlx = tcwl_tck;
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        cwlx = timing->ddr5_tcwl_tck;
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        if (hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls == 0)
            cwlx = timing->lpddr4_cwl_seta;
        else
            cwlx = timing->lpddr4_cwl_setb;
    }
#endif
#endif /* DDRCTL_LPDDR */

    return cwlx;
}

/** @brief Calculate CL read latency
 */
uint32_t cinit_cal_cl(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    SNPS_TRACE("Entering");
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
    uint32_t cl = 0;

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4)
        cl = timing->ddr4_tcl_tck;
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5)
        cl = timing->ddr5_tcl_tck;
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4)
        cl = timing->lpddr4_cl;
#endif
#endif /* DDRCTL_LPDDR */

    SNPS_TRACE("Leaving");
    return cl;
}

/**
 * @brief function to pre-calculate wr2rd
 */
void cinit_cal_wr2rd(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
    uint8_t  bl_div2;
    uint32_t tck_ps = SPD.tck_ps[p];

    // BL/2 (Burst Length / 2)
    bl_div2 = DIV_2(timing->burst_length);

#ifdef DDRCTL_DDR
    if (IS_DDR4) {
        uint32_t twtr_l_crc_dm, twtr_s_crc_dm;

        twtr_l_crc_dm = (QDYN.wr_crc_enable == 1 && QDYN.dm_en[ch] == 1) ? timing->ddr4_twtr_l_crc_dm_tck : 0;
        twtr_s_crc_dm = (QDYN.wr_crc_enable == 1 && QDYN.dm_en[ch] == 1) ? timing->ddr4_twtr_s_crc_dm_tck : 0;
        // System_W2R DDR4: CWL + PL + BL/2 + tWTR_L (same bank group)
        // System_W2R DDR4: CWL + PL + BL/2 + tWTR_S (different bank group)
        uint32_t system_wr2rd = PRE_CFG.cwl_x[p] + timing->ddr4_tpl_tck + bl_div2;

        PRE_CFG.wr2rd[p][ch]   = system_wr2rd + twtr_l_crc_dm + PRE_CFG.twtr[p][ch];
        PRE_CFG.wr2rd_s[p][ch] = system_wr2rd + twtr_s_crc_dm + PRE_CFG.twtr_s[p][ch];

    }
    if (IS_DDR5) {
        PRE_CFG.wr2rd[p][ch] = PRE_CFG.cwl_x[p] + bl_div2 + QDYN.wr_crc_enable + PRE_CFG.twtr[p][ch] + CEIL(timing->ddr5_tdqs2dq_ps, tck_ps);
        PRE_CFG.wr2rd_s[p][ch] = PRE_CFG.cwl_x[p] + bl_div2 + QDYN.wr_crc_enable + PRE_CFG.twtr_s[p][ch] + CEIL(timing->ddr5_tdqs2dq_ps, tck_ps);
        PRE_CFG.t_wr2rd_m[p][ch] = PRE_CFG.cwl_x[p] + bl_div2 + QDYN.wr_crc_enable + timing->ddr5_twtr_m_tck + CEIL(timing->ddr5_tdqs2dq_ps, tck_ps);


#ifdef UMCTL2_CID_EN
        PRE_CFG.t_wr2rd_dlr[p][ch] = PRE_CFG.cwl_x[p] + bl_div2 + QDYN.wr_crc_enable + PRE_CFG.twtr_s[p][ch] + CEIL(timing->ddr5_tdqs2dq_ps, tck_ps);
#endif /* UMCTL2_CID_EN */
   }
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
    if (IS_LPDDR4) {
        // LPDDR4 WDQS Extension
        // ODT OFF case, ODT ON case
        // WL + 1 + BL/2 + RU(tWTR/tCK)
        PRE_CFG.wr2rd[p][ch] = PRE_CFG.cwl_x[p] + PRE_CFG.twtr[p][ch] + 8 + 1;
#ifdef MEMC_BURST_LENGTH_32 
        PRE_CFG.wr2rd_blx2[p][ch] = PRE_CFG.cwl_x[p] + PRE_CFG.twtr[p][ch] + 16 + 1;
#endif /* MEMC_BURST_LENGTH_32 */
    }
    if (IS_LPDDR5) {
        uint8_t dvfsc_type = hdlr->memCtrlr_m.lpddr5_mr[p].mr19.dvfsc;
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
        if (dvfsc_type==0) { //DVFSC disable
            // wr2rd = WL + BL/n_max + RU(tWTR_L/tCK)
            PRE_CFG.wr2rd[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_twtr_l_ps, tck_ps);
        } else { // DVFSC or Enhanced DVFSC enable (16B mode only)
            // wr2rd = WL + BL/n_max + RU(tWTR/tCK)
            PRE_CFG.wr2rd[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_twtr_ps, tck_ps);
        }
        // WL + BL/n_min + RU(tWTR_S/tCK)
        PRE_CFG.wr2rd_s[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_twtr_s_ps, tck_ps);
#ifdef MEMC_BURST_LENGTH_32 
        if (dvfsc_type==0) { //DVFSC disable
            // wr2rd = WL + BL/n_max + RU(tWTR_L/tCK)
            PRE_CFG.wr2rd_blx2[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_twtr_l_ps, tck_ps);
        } else { //DVFSC enable
            // wr2rd = WL + BL/n_max + RU(tWTR/tCK)
            PRE_CFG.wr2rd_blx2[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_twtr_ps, tck_ps);
        }
        // WL + BL/n_min + RU(tWTR_S/tCK)
        /// @note see bugzilla 7142, using BL/n_max for now in wr2rd_s
        PRE_CFG.wr2rd_s_blx2[p][ch] = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_twtr_s_ps, tck_ps);
#endif /* MEMC_BURST_LENGTH_32 */
    }
#endif /* DDRCTL_LPDDR */
}

void ddrctl_cinit_ddr4_cmd_read_to_write(SubsysHdlr_t *hdlr, uint8_t pstate, uint8_t ch, uint8_t dev)
{
    uint32_t system_rd2wr;
    uint32_t cl = PRE_CFG.cl[pstate];
    uint8_t  bl_div2;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[pstate][dev];

#ifdef CINIT_DDR4
    if (IS_DDR4) {
        if (1 == hdlr->memCtrlr_m.ddr4_mr[pstate].mr5.read_dbi) {
            cl = PRE_CFG.cl_dbi[pstate];
        } else {
            cl = PRE_CFG.cl[pstate];
        }
        bl_div2 = DIV_2(timing->burst_length);

        system_rd2wr = SPD.tAL + cl + bl_div2 + 1;
        PRE_CFG.rd2wr[pstate][ch] = system_rd2wr + (QDYN.ddr4_wr_preamble[pstate][ch] ? 2 : 1) - (SPD.tAL + PRE_CFG.cwl_x[pstate]);
        if (IS_LRDIMM) {
            //    From DDR4DB02 Spec Rev 0.95
            // TRDWR= tPDM_RD + tPDM_WR + tWRPRE + tRPRE/2 + BL/2 + 2.7 + (CL - CWL)

            // In this point we will calculate only the part tPDM_RD + tPDM_WR + 2.7
            // Since we cannot do floating operations, we multiply all by 10
            // (tPDM_RD ps * 10)/tck_ps + (tPDM_WR ps * 10)/tck_ps + (2.7 * 10) ->
            //                  ceil(((tPDM_RD ps * 10) + (tPDM_WR ps * 10) + (2.7 * 10 * tck_ps)) / tck_ps)
            uint32_t parcial_rd2wr = (timing->ddr4_rcd_tpdm_wr_ps * 10) + (timing->ddr4_rcd_tpdm_rd_ps * 10) + (27 * SPD.tck_ps[pstate]);
            parcial_rd2wr = CEIL(parcial_rd2wr, SPD.tck_ps[pstate] * 10);
            PRE_CFG.rd2wr[pstate][ch] += parcial_rd2wr;
        }
        SNPS_LOG("pstate = %u cl = %u burst_rdwr = %u ddr4_wr_preamble = %u cwl_x = %u tAL = %u", pstate, cl, bl_div2,
                 QDYN.ddr4_wr_preamble[pstate][ch], PRE_CFG.cwl_x[pstate], SPD.tAL);
        SNPS_LOG("[%d] rd2wr = %d ", pstate, PRE_CFG.rd2wr[pstate][ch]);
    }
#endif /* CINIT_DDR4 */
}

/** @brief function to pre-calculate rd2wr
 */
void cinit_cal_rd2wr(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    if (IS_DDR4) {
        ddrctl_cinit_ddr4_cmd_read_to_write(hdlr, p, ch, n);
        return;
    }

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        uint32_t trpst_int;
        uint32_t tdqsck_max;
        uint32_t lpddr4_wdqson;
        uint8_t  bl_div2;
        ddrTimingParameters_t *timing;
        timing = &hdlr->timingParams_m[p][n];
        // BL/2 (Burst Length / 2)
        bl_div2 = DIV_2(timing->burst_length);
        trpst_int = (hdlr->memCtrlr_m.lpddr4_mr[p].mr1.rd_postamble) ? 1 : 0;
        tdqsck_max = cinit_ps_to_tck(timing->lpddr4_tdqsck_max, SPD.tck_ps[p]);
        lpddr4_wdqson = (hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls == 0) ? timing->lpddr4_wdqson_seta : timing->lpddr4_wdqson_setb;

        // LPDDR4 WDQS Extension (PHY Databook)
        // ODT OFF case
        // RL + RU(tDQSCK.max/tCK) + BL/2 + RD(tRPST) - WDQS_on + 2
        PRE_CFG.rd2wr[p][ch] = SPD.tAL + PRE_CFG.cl[p] + tdqsck_max + 8 + trpst_int - lpddr4_wdqson + 2;

        // ODT ON case
        // RL + RU(tDQSCK.max/tCK) + BL/2 + RD(tRPST) - ODTLon - RD(tODTon.min/tCK) + 6
        PRE_CFG.rd2wr_odt[p][ch] = SPD.tAL + PRE_CFG.cl[p] + tdqsck_max + 8 + trpst_int - PRE_CFG.odtlon[p][ch] - PRE_CFG.odton_min[p][ch] + 6;
#ifdef MEMC_BURST_LENGTH_32
        PRE_CFG.rd2wr_blx2[p][ch] = SPD.tAL + PRE_CFG.cl[p] + tdqsck_max + 16 + trpst_int - lpddr4_wdqson + 2;
	PRE_CFG.rd2wr_odt_blx2[p][ch] = SPD.tAL + PRE_CFG.cl[p] + tdqsck_max + 16 + trpst_int - PRE_CFG.odtlon_blx2[p][ch] - PRE_CFG.odton_min[p][ch] + 6;
#endif /* MEMC_BURST_LENGTH_32 */
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        ddrTimingParameters_t *timing;
        timing = &hdlr->timingParams_m[p][n];
        PRE_CFG.rd2wr[p][ch] = timing->lpddr5_trtw_tck;
        PRE_CFG.rd2wr_s[p][ch] = timing->lpddr5_trtw_s_tck;
#ifdef MEMC_BURST_LENGTH_32 
        PRE_CFG.rd2wr_blx2[p][ch] =   timing->lpddr5_trtw_bl32_tck;
        PRE_CFG.rd2wr_s_blx2[p][ch] = timing->lpddr5_trtw_s_bl32_tck;
#endif /* MEMC_BURST_LENGTH_32 */
    }
#endif /* CINIT_LPDDR5 */
#endif /* MEMC_LPDDR4 */

#ifdef DDRCTL_DDR

#ifdef CINIT_DDR5
    if (IS_DDR5) {
        ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[p];
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
        uint32_t rd_dqs_offset = cinit_get_ddr5_t_rd_dqs_offset(hdlr, p);
        uint32_t tWPRE = cinit_get_ddr5_twpre(hdlr, p);
        uint8_t  bl_div2;
        bl_div2 = DIV_2(timing->burst_length);
        PRE_CFG.rd2wr[p][ch] = PRE_CFG.cl[p] + bl_div2 + 2 + tWPRE + ((mregs->mr8.rd_postamble) ? 1 : 0) + QDYN.rd_crc_enable - rd_dqs_offset - PRE_CFG.cwl_x[p];
        if (QDYN.rd_crc_enable)
            PRE_CFG.rd2wr[p][ch] += timing->ddr5_read_crc_latency_adder;

        if (IS_LRDIMM) {
            // For DDR5 LRDIMM, add ddr5_rcd_tpdm_wr_ps + ddr5_rcd_tpdm_rd_ps
            PRE_CFG.rd2wr[p][ch]+=CEIL((timing->ddr5_rcd_tpdm_wr_ps + timing->ddr5_rcd_tpdm_rd_ps), SPD.tck_ps[p]);
        }
#ifdef UMCTL2_CID_EN
        PRE_CFG.t_rd2wr_dlr[p][ch] = PRE_CFG.cl[p] + bl_div2 + 2 + tWPRE + (mregs->mr8.rd_postamble ? 1 : 0) + QDYN.rd_crc_enable - rd_dqs_offset - PRE_CFG.cwl_x[p];
        if (IS_LRDIMM) {
            // For DDR5 LRDIMM, add ddr5_rcd_tpdm_wr_ps + ddr5_rcd_tpdm_rd_ps
            PRE_CFG.t_rd2wr_dlr[p][ch]+=CEIL((timing->ddr5_rcd_tpdm_wr_ps + timing->ddr5_rcd_tpdm_rd_ps), SPD.tck_ps[p]);
        }

		if (QDYN.rd_crc_enable)
			PRE_CFG.t_rd2wr_dlr[p][ch] += timing->ddr5_read_crc_latency_adder;

#endif /* UMCTL2_CID_EN */
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */
}

#ifdef MEMC_NUM_RANKS_GT_1
/** @brief function to pre-calculate rd2wr_dr
 */
void cinit_cal_rd2wr_dr(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    SNPS_TRACE("Entering");

#ifdef DDRCTL_LPDDR
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
    uint32_t tck_ps = SPD.tck_ps[p];
    uint8_t ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
    uint32_t enhanced_nt_odt = hdlr->memCtrlr_m.lpddr5_mr[p].mr0.enhanced_nt_odt;    //MR0 OP[0] 0:support same DQ/RDQS NT-ODT timing, 1:support separate DQ/RDQS NT-ODT timing
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        // (RL + BL/n_min + RU(tWCK2DQO(max)/tCK) - ODTLon - RD(tODTon(min)/tCK) + 1) + tphy_wckcsgap + LP5 CDD                         - JESD209-5A Table 349
        PRE_CFG.rd2wr_dr_wck_on_odt[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - PRE_CFG.odtlon[p][ch] - timing->lpddr5_odton_min_ps / tck_ps + 1) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

        // (RL + BL/n_max + RU((tWCKPST -0.5*tWCK)/tCK) - min[(ODTLon + RD(tODTon(min)/tCK)), tWCKENL_WR]) + tphy_wckcsgap + LP5 CDD    - JESD209-5A Table 351
        PRE_CFG.rd2wr_dr_odt[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - min(PRE_CFG.odtlon[p][ch] + timing->lpddr5_odton_min_ps / tck_ps, timing->lpddr5_wckenl_wr_tck)) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

        // (RL + BL/n_min + RU(tWCK2DQO(max)/tCK) + RU((tRPST -0.5*tWCK)/tCK) - WL) + tphy_wckcsgap + LP5 CDD                           - JESD209-5A Table 350
        PRE_CFG.rd2wr_dr_wck_on[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_min_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + CEIL(timing->lpddr5_twck_pst_wck, ratio) - PRE_CFG.wl[p][ch]) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

        // (RL + BL/n_max + RU((tWCKPST -0.5*tWCK)/tCK) - tWCKENL_WR) + tphy_wckcsgap + LP5 CDD                                         - JESD209-5A Table 351
        PRE_CFG.rd2wr_dr[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_wr_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

	if (QDYN.wr_link_ecc_enable[p][ch] == 1 || (enhanced_nt_odt == 0 && hdlr->memCtrlr_m.lpddr5_mr[p].mr11.nt_odt))   { //check wr_link_ecc_enable for both rd2wr and wr2rd at P80001562-369272
		// In case of Link ECC enabled, an additional RU((tRPST-0.5*tWCK)/tCK) delay should be added because RDQS_t is used for ECC parity input. JESD209-5A Table 349 NOTE 4
		// In case of MR0 OP[0]=0B (Same DQ & RDQS NT-ODT timing) and/or Link ECC ON, an additional RU((tRPST-0.5*tWCK)/tCK) delay should be added. JESD209-5A Table 353 NOTE 2
		PRE_CFG.rd2wr_dr_wck_on_odt[p][ch] += CEIL(timing->lpddr5_twck_pst_wck, ratio);
	}
	if (QDYN.wr_link_ecc_enable[p][ch]) {//check wr_link_ecc_enable for both rd2wr and wr2rd at P80001562-369272
		// If Link ECC enabled,         an additional RU((tRPST-0.5*tWCK)/tCK) delay should be added because RDQS_t is used for ECC parity input. JESD209-5A Table 350 NOTE 5
		PRE_CFG.rd2wr_dr_wck_on[p][ch]     += CEIL(timing->lpddr5_twck_pst_wck, ratio);
	}
#ifdef MEMC_BURST_LENGTH_32
        // (RL + BL/n_min + RU(tWCK2DQO(max)/tCK) - ODTLon - RD(tODTon(min)/tCK) + 1) + tphy_wckcsgap + LP5 CDD                         - JESD209-5A Table 349
        PRE_CFG.rd2wr_dr_wck_on_odt_blx2[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - PRE_CFG.odtlon_blx2[p][ch] - timing->lpddr5_odton_min_ps / tck_ps + 1) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

        // (RL + BL/n_max + RU((tWCKPST -0.5*tWCK)/tCK) - min[(ODTLon + RD(tODTon(min)/tCK)), tWCKENL_WR]) + tphy_wckcsgap + LP5 CDD    - JESD209-5A Table 351
        PRE_CFG.rd2wr_dr_odt_blx2[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - min(PRE_CFG.odtlon_blx2[p][ch] + timing->lpddr5_odton_min_ps / tck_ps, timing->lpddr5_wckenl_wr_tck)) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

        // (RL + BL/n_min + RU(tWCK2DQO(max)/tCK) + RU((tRPST -0.5*tWCK)/tCK) - WL) + tphy_wckcsgap + LP5 CDD                           - JESD209-5A Table 350
        PRE_CFG.rd2wr_dr_wck_on_blx2[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_min_bl32_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + CEIL(timing->lpddr5_twck_pst_wck, ratio) - PRE_CFG.wl[p][ch]) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

        // (RL + BL/n_max + RU((tWCKPST -0.5*tWCK)/tCK) - tWCKENL_WR) + tphy_wckcsgap + LP5 CDD                                         - JESD209-5A Table 351
        PRE_CFG.rd2wr_dr_blx2[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_wr_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

	if (QDYN.wr_link_ecc_enable[p][ch] == 1 || (enhanced_nt_odt == 0 && hdlr->memCtrlr_m.lpddr5_mr[p].mr11.nt_odt))   { //check wr_link_ecc_enable for both rd2wr and wr2rd at P80001562-369272
		// In case of Link ECC enabled, an additional RU((tRPST-0.5*tWCK)/tCK) delay should be added because RDQS_t is used for ECC parity input. JESD209-5A Table 349 NOTE 4
		// In case of MR0 OP[0]=0B (Same DQ & RDQS NT-ODT timing) and/or Link ECC ON, an additional RU((tRPST-0.5*tWCK)/tCK) delay should be added. JESD209-5A Table 353 NOTE 2
		PRE_CFG.rd2wr_dr_wck_on_odt_blx2[p][ch] += CEIL(timing->lpddr5_twck_pst_wck, ratio);
	}
	if (QDYN.rd_link_ecc_enable[p][ch]) {
		// If Link ECC enabled,         an additional RU((tRPST-0.5*tWCK)/tCK) delay should be added because RDQS_t is used for ECC parity input. JESD209-5A Table 350 NOTE 5
		PRE_CFG.rd2wr_dr_wck_on_blx2[p][ch]     += CEIL(timing->lpddr5_twck_pst_wck, ratio);
	}
#endif 
	} else
#endif
#endif /* MEMC_LPDDR4 */
    {
        PRE_CFG.rd2wr_dr[p][ch] = PRE_CFG.rd2wr[p][ch];
    }
    SNPS_TRACE("Leaving");
}
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef MEMC_NUM_RANKS_GT_1
/** @brief function to pre-calculate wr2rd_dr
 */
void cinit_cal_wr2rd_dr(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    SNPS_TRACE("Entering");

#ifdef DDRCTL_LPDDR
	uint32_t tck_ps = SPD.tck_ps[p];
	uint8_t ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
	ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];

#ifdef CINIT_LPDDR5
	if (IS_LPDDR5) {
		int wr2rd_dr, wr2rd_dr_bl32;
		uint32_t trpre_wck = hdlr->memCtrlr_m.lpddr5_mr[p].mr10.rdqs_pre > 3 ? 6 : 4;
		uint32_t enhanced_nt_odt = hdlr->memCtrlr_m.lpddr5_mr[p].mr0.enhanced_nt_odt;    //MR0 OP[0] 0:support same DQ/RDQS NT-ODT timing, 1: support separate DQ/RDQS NT-ODT timing
		// (ODTLoff + RU(tODToff(max)/tCK) - RL) + tphy_wckcsgap + LP5 CDD                                                    - JESD209-5A Table 349
		wr2rd_dr = PRE_CFG.odtloff[p][ch] + CEIL(timing->lpddr5_odtoff_max_ps, tck_ps) - PRE_CFG.rl[p][ch];
		PRE_CFG.wr2rd_dr_wck_on_odt[p][ch] = max(0, wr2rd_dr) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

		// (WL + BL/n_max + max[RU(tODToff(max)/ tCK), RU((tWCKPST -0.5*tWCK)/tCK)] - tWCKENL_RD) + tphy_wckcsgap + LP5 CDD   - JESD209-5A Table 351
		wr2rd_dr = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_tck + max(CEIL(timing->lpddr5_odtoff_max_ps, tck_ps), CEIL(timing->lpddr5_twck_pst_wck, ratio)) - timing->lpddr5_wckenl_rd_tck;
		PRE_CFG.wr2rd_dr_odt[p][ch] = max(0, wr2rd_dr) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
		// (WL + BL/n_min + 1 - RL) + tphy_wckcsgap + LP5 CDD                                                                 - JESD209-5A Table 350
		wr2rd_dr = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_min_tck + 1 - PRE_CFG.rl[p][ch];
		PRE_CFG.wr2rd_dr_wck_on[p][ch] = max(0, wr2rd_dr) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
		// (WL + BL/n_max + RU((tWCKPST -0.5*tWCK)/tCK) - tWCKENL_RD) + tphy_wckcsgap + LP5 CDD                               - JESD209-5A Table 352
		wr2rd_dr = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_rd_tck;
		PRE_CFG.wr2rd_dr[p][ch] = max(0, wr2rd_dr) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

		if (QDYN.wr_link_ecc_enable[p][ch] == 1 || (enhanced_nt_odt == 0 && hdlr->memCtrlr_m.lpddr5_mr[p].mr11.nt_odt))   {//check wr_link_ecc_enable for both rd2wr and wr2rd at P80001562-369272
			// In case of Link ECC enabled, an additional RU(tRPRE/tCK) delay should be added because RDQS_t is used for ECC parity input. JESD209-5A Table 349 NOTE 5
			// In case of MR0 OP[0]=0B (Same DQ & RDQS NT-ODT timing) and/or Link ECC ON, an additional RU(tRPRE/tCK) delay should be added.JESD209-5A Table 353 NOTE 5
			PRE_CFG.wr2rd_dr_wck_on_odt[p][ch] += CEIL(trpre_wck, ratio);
		}
		if (QDYN.wr_link_ecc_enable[p][ch]) {//check wr_link_ecc_enable for both rd2wr and wr2rd at P80001562-369272
			// If Link ECC enabled,         an additional RU(tRPRE/tCK) delay should be added because RDQS_t is used for ECC parity input. JESD209-5A Table 350 NOTE 6
			PRE_CFG.wr2rd_dr_wck_on[p][ch]     += CEIL(trpre_wck, ratio);
		}
#ifdef MEMC_BURST_LENGTH_32
		// (ODTLoff + RU(tODToff(max)/tCK) - RL) + tphy_wckcsgap + LP5 CDD                                                    - JESD209-5A Table 349
		wr2rd_dr_bl32 = PRE_CFG.odtloff_blx2[p][ch] + CEIL(timing->lpddr5_odtoff_max_ps, tck_ps) - PRE_CFG.rl[p][ch];
		PRE_CFG.wr2rd_dr_wck_on_odt_blx2[p][ch] = max(0, wr2rd_dr_bl32) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

		// (WL + BL/n_max + max[RU(tODToff(max)/ tCK), RU((tWCKPST -0.5*tWCK)/tCK)] - tWCKENL_RD) + tphy_wckcsgap + LP5 CDD   - JESD209-5A Table 351
		wr2rd_dr_bl32 = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + max(CEIL(timing->lpddr5_odtoff_max_ps, tck_ps), CEIL(timing->lpddr5_twck_pst_wck, ratio)) - timing->lpddr5_wckenl_rd_tck;
		PRE_CFG.wr2rd_dr_odt_blx2[p][ch] = max(0, wr2rd_dr_bl32) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
		// (WL + BL/n_min + 1 - RL) + tphy_wckcsgap + LP5 CDD                                                                 - JESD209-5A Table 350
		wr2rd_dr_bl32 = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_min_bl32_tck + 1 - PRE_CFG.rl[p][ch];
		PRE_CFG.wr2rd_dr_wck_on_blx2[p][ch] = max(0, wr2rd_dr_bl32) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
		// (WL + BL/n_max + RU((tWCKPST -0.5*tWCK)/tCK) - tWCKENL_RD) + tphy_wckcsgap + LP5 CDD                               - JESD209-5A Table 352
		wr2rd_dr_bl32 = PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_rd_tck;
		PRE_CFG.wr2rd_dr_blx2[p][ch] = max(0, wr2rd_dr_bl32) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;

		if (QDYN.wr_link_ecc_enable[p][ch] == 1 || (enhanced_nt_odt == 0 && hdlr->memCtrlr_m.lpddr5_mr[p].mr11.nt_odt))   {//check wr_link_ecc_enable for both rd2wr and wr2rd at P80001562-369272
			// In case of Link ECC enabled, an additional RU(tRPRE/tCK) delay should be added because RDQS_t is used for ECC parity input. JESD209-5A Table 349 NOTE 5
			// In case of MR0 OP[0]=0B (Same DQ & RDQS NT-ODT timing) and/or Link ECC ON, an additional RU(tRPRE/tCK) delay should be added.JESD209-5A Table 353 NOTE 5
			PRE_CFG.wr2rd_dr_wck_on_odt_blx2[p][ch] += CEIL(trpre_wck, ratio);
		}
		if (QDYN.wr_link_ecc_enable[p][ch]) {
			// If Link ECC enabled,         an additional RU(tRPRE/tCK) delay should be added because RDQS_t is used for ECC parity input. JESD209-5A Table 350 NOTE 6
			PRE_CFG.wr2rd_dr_wck_on_blx2[p][ch]     += CEIL(trpre_wck, ratio);
		}
#endif 
	}
#endif // CINIT_LPDDR5
#ifdef CINIT_LPDDR4
	if (IS_LPDDR4) {

		uint32_t lpddr4_wdqsoff = (hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls == 0) ? timing->lpddr4_wdqsoff_seta : timing->lpddr4_wdqsoff_setb;

      /*
         JEDEC Standard No. 209-4C
         Table 90::tDQSCK.min = 1.5ns
         Table 89::tRPRE      = 1.8 tck
		   LPDDR4 : Max(4, WDQS_off - (RL + RD(tDQSCK.min/tCK) - RU(tRPRE/tCK) ) + 8)
      */
		PRE_CFG.wr2rd_dr[p][ch] = max(4, lpddr4_wdqsoff  - (PRE_CFG.rl[p][ch] + 1500/tck_ps - CEIL(18,10)) + 8 );
		SNPS_LOG("wr2rd_dr = %u p = %u ch = %u lpddr4_wdqsoff = %u ",PRE_CFG.wr2rd_dr[p][ch], p, ch,lpddr4_wdqsoff );
#ifdef MEMC_BURST_LENGTH_32
		PRE_CFG.wr2rd_dr_blx2[p][ch] = max(4, lpddr4_wdqsoff  - (PRE_CFG.rl[p][ch] + 1500/tck_ps - CEIL(18,10)) + 16 );
		SNPS_LOG("wr2rd_dr_blx2 = %u p = %u ch = %u lpddr4_wdqsoff = %u ",PRE_CFG.wr2rd_dr_blx2[p][ch], p, ch,lpddr4_wdqsoff );
#endif 
	}

#endif // CINIT_LPDDR4
#endif /* MEMC_LPDDR4 */


#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
        uint32_t              read_dbi = hdlr->memCtrlr_m.ddr4_mr[p].mr5.read_dbi;
        uint32_t              cl;
        uint8_t               rd_preamble;
        uint8_t               wr_preamble;
        uint8_t               bl_div2;

        cl = (read_dbi == 1) ? PRE_CFG.cl_dbi[p] : PRE_CFG.cl[p];
        rd_preamble = hdlr->memCtrlr_m.ddr4_mr[p].mr4.rd_preamble + 1; // 0 = 1 nCK 1 = 2 nCK
        wr_preamble = QDYN.ddr4_wr_preamble[p][ch] + 1; // 0 = 1 nCK 1 = 2 nCK
        // BL/2 (Burst Length / 2)
        bl_div2 = DIV_2(timing->burst_length);
        /*DDR4 : WL + BL/2 - RL + WR_POSTAMBLE + RD_PREAMBLE */
        /* JEDEC JESD79-4C: Chapter 4.25.6 Read and Write Command Interval
         *  Minimum Read after Write:  CWL + WBL / 2 + tWTR_S (ddr4_twtr_s_tck)
                                 CAS Write Latency  + Write burst length /2 + */
        // WL (write latency)       = CWL + AL + PL
        // WL (write burst latency) = AL + CWL
        // RL (read latency)        = AL + PL + CL

        //         // CWL + PL + BL/2 + tWTR_S (different bank group)

        // System WR2RD_DR = WL + BL/2 - RL + WR_POSTAMBLE + RD_PREAMBLE
        // wr2rd_dr = System WR2RD_DR + 5 + max(0, CDD_WR_R[i]_R[j]) (Different physical ranks)
        PRE_CFG.wr2rd_dr[p][ch] = PRE_CFG.cwl_x[p] + timing->ddr4_tpl_tck + bl_div2 - (SPD.tAL + cl) +
                                  wr_preamble + rd_preamble;
        PRE_CFG.wr2rd_dr[p][ch] = PRE_CFG.wr2rd_dr[p][ch] + 5;
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        PRE_CFG.wr2rd_dr[p][ch] = PRE_CFG.wr2rd[p][ch];
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */
    SNPS_TRACE("Leaving");
}
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef MEMC_NUM_RANKS_GT_1
/** @brief function to pre-calculate diff_rank_rd_gap
 */
void cinit_cal_diff_rank_rd_gap(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
        uint8_t ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
        uint32_t trpre_wck = hdlr->memCtrlr_m.lpddr5_mr[p].mr10.rdqs_pre > 3 ? 6 : 4;
        uint32_t trpst_wck = hdlr->memCtrlr_m.lpddr5_mr[p].mr10.rdqs_pst == 0 ? 0 : hdlr->memCtrlr_m.lpddr5_mr[p].mr10.rdqs_pst == 1 ? 2 : 4;
        // (BL/n_min + 1 + RU((tRPST + tRPRE - 0.5*tWCK)/tCK)) + tphy_wckcsgap + LP5 CDD            - JESD209-5A Table 349
        PRE_CFG.diff_rank_rd_gap_wck_on_odt[p][ch] = (timing->lpddr5_bl_n_min_tck + 1 + CEIL(trpst_wck + trpre_wck, ratio)) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (RL + BL/n_max + RU((tWCKPST - 0.5*tWCK)/tCK) - tWCKENL_RD) + tphy_wckcsgap + LP5 CDD    - JESD209-5A Table 351
        PRE_CFG.diff_rank_rd_gap_odt[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_rd_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (BL/n_min + 1 + RU((tRPST + tRPRE - 0.5*tWCK)/tCK)) + tphy_wckcsgap + LP5 CDD            - JESD209-5A Table 350
        PRE_CFG.diff_rank_rd_gap_wck_on[p][ch] = (timing->lpddr5_bl_n_min_tck + 1 + CEIL(trpst_wck + trpre_wck, ratio)) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (RL + BL/n_max + RU((tWCKPST - 0.5*tWCK)/tCK) - tWCKENL_RD) + tphy_wckcsgap + LP5 CDD    - JESD209-5A Table 352
        PRE_CFG.diff_rank_rd_gap[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_rd_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        //ODTLon_RD - ODTLoff_RD, or ODTLon_RD_RDQS - ODTLoff_RD_RDQS if MR0[0]=1                   - JESD209-5A Table 353
	PRE_CFG.diff_rank_rd_gap_wck_on_dq_odt_nt_odt[p][ch] = (hdlr->memCtrlr_m.lpddr5_mr[p].mr0.enhanced_nt_odt == 1) ? (timing->lpddr5_odtlon_rd_tck - timing->lpddr5_odtloff_rd_tck)
                                                                                                                    : (timing->lpddr5_odtlon_rd_rdqs_tck - timing->lpddr5_odtloff_rd_rdqs_tck);
#ifdef MEMC_BURST_LENGTH_32
        // (BL/n_min + 1 + RU((tRPST + tRPRE - 0.5*tWCK)/tCK)) + tphy_wckcsgap + LP5 CDD            - JESD209-5A Table 349
        PRE_CFG.diff_rank_rd_gap_wck_on_odt_blx2[p][ch] = (timing->lpddr5_bl_n_min_bl32_tck + 1 + CEIL(trpst_wck + trpre_wck, ratio)) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (RL + BL/n_max + RU((tWCKPST - 0.5*tWCK)/tCK) - tWCKENL_RD) + tphy_wckcsgap + LP5 CDD    - JESD209-5A Table 351
        PRE_CFG.diff_rank_rd_gap_odt_blx2[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_rd_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (BL/n_min + 1 + RU((tRPST + tRPRE - 0.5*tWCK)/tCK)) + tphy_wckcsgap + LP5 CDD            - JESD209-5A Table 350
        PRE_CFG.diff_rank_rd_gap_wck_on_blx2[p][ch] = (timing->lpddr5_bl_n_min_bl32_tck + 1 + CEIL(trpst_wck + trpre_wck, ratio)) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (RL + BL/n_max + RU((tWCKPST - 0.5*tWCK)/tCK) - tWCKENL_RD) + tphy_wckcsgap + LP5 CDD    - JESD209-5A Table 352
        PRE_CFG.diff_rank_rd_gap_blx2[p][ch] = (PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_rd_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        //ODTLon_RD - ODTLoff_RD, or ODTLon_RD_RDQS - ODTLoff_RD_RDQS if MR0[0]=1                   - JESD209-5A Table 353
	PRE_CFG.diff_rank_rd_gap_wck_on_dq_odt_nt_odt_blx2[p][ch] = (hdlr->memCtrlr_m.lpddr5_mr[p].mr0.enhanced_nt_odt == 1) ? (timing->lpddr5_odtlon_rd_bl32_tck - timing->lpddr5_odtloff_rd_bl32_tck)
                                                                                                                    : (timing->lpddr5_odtlon_rd_rdqs_bl32_tck - timing->lpddr5_odtloff_rd_rdqs_bl32_tck);
#endif
    }
#endif
#endif /* MEMC_LPDDR4 */
#ifdef CINIT_DDR4
#if MEMC_NUM_RANKS > 1
    /*                                         BL/2                  + 1 if Read preamble mode = 2nCK */
        PRE_CFG.diff_rank_rd_gap[p][ch] = DIV_2(hdlr->timingParams_m[p][n].burst_length) +
                                          hdlr->memCtrlr_m.ddr4_mr[p].mr4.rd_preamble + 4;
#endif /* MEMC_NUM_RANKS */
#endif /* CINIT_DDR4 */
}
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef MEMC_NUM_RANKS_GT_1
/** @brief function to pre-calculate diff_rank_wr_gap
 */
void cinit_cal_diff_rank_wr_gap(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR5
    uint32_t tck_ps = SPD.tck_ps[p];
    uint8_t ratio = ddrctl_sw_get_ratio_factor(hdlr, p);

    if (IS_LPDDR5) {
        // (ODTLoff + RU(tODToff(max)/tCK) - ODTLon) + tphy_wckcsgap + LP5 CDD                    - JESD209-5A Table 349
        PRE_CFG.diff_rank_wr_gap_wck_on_odt[p][ch] = (PRE_CFG.odtloff[p][ch] + CEIL(timing->lpddr5_odtoff_max_ps, tck_ps) - PRE_CFG.odtlon[p][ch]) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (WL + BL/n_max + max[RU(tODToff(max)/ tCK), RU((tWCKPST -0.5*tWCK)/tCK)] - tWCKENL_WR) + tphy_wckcsgap + LP5 CDD  - JESD209-5A Table 351
        PRE_CFG.diff_rank_wr_gap_odt[p][ch] = (PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_tck + max(CEIL(timing->lpddr5_odtoff_max_ps, tck_ps), CEIL(timing->lpddr5_twck_pst_wck, ratio)) - timing->lpddr5_wckenl_wr_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (BL/n_min + 1) + tphy_wckcsgap + LP5 CDD                                               - JESD209-5A Table 350
        PRE_CFG.diff_rank_wr_gap_wck_on[p][ch] = (timing->lpddr5_bl_n_min_tck + 1) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (WL + BL/n_max + RU((tWCKPST -0.5*tWCK)/tCK) - tWCKENL_WR) + tphy_wckcsgap + LP5 CDD   - JESD209-5A Table 352
        PRE_CFG.diff_rank_wr_gap[p][ch] = (PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_wr_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (ODTLoff + RU(tODToff(max)/tCK) - ODTLon) + tphy_wckcsgap + LP5 CDD                    - JESD209-5A Table 353 - Same Table 353
        PRE_CFG.diff_rank_wr_gap_wck_on_dq_odt_nt_odt[p][ch]= (PRE_CFG.odtloff[p][ch] + CEIL(timing->lpddr5_odtoff_max_ps, tck_ps) - PRE_CFG.odtlon[p][ch]) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
#ifdef MEMC_BURST_LENGTH_32
        // (ODTLoff + RU(tODToff(max)/tCK) - ODTLon) + tphy_wckcsgap + LP5 CDD                    - JESD209-5A Table 349
        PRE_CFG.diff_rank_wr_gap_wck_on_odt_blx2[p][ch] = (PRE_CFG.odtloff_blx2[p][ch] + CEIL(timing->lpddr5_odtoff_max_ps, tck_ps) - PRE_CFG.odtlon_blx2[p][ch]) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (WL + BL/n_max + max[RU(tODToff(max)/ tCK), RU((tWCKPST -0.5*tWCK)/tCK)] - tWCKENL_WR) + tphy_wckcsgap + LP5 CDD  - JESD209-5A Table 351
        PRE_CFG.diff_rank_wr_gap_odt_blx2[p][ch] = (PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + max(CEIL(timing->lpddr5_odtoff_max_ps, tck_ps), CEIL(timing->lpddr5_twck_pst_wck, ratio)) - timing->lpddr5_wckenl_wr_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (BL/n_min + 1) + tphy_wckcsgap + LP5 CDD                                               - JESD209-5A Table 350
        PRE_CFG.diff_rank_wr_gap_wck_on_blx2[p][ch] = (timing->lpddr5_bl_n_min_bl32_tck + 1) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (WL + BL/n_max + RU((tWCKPST -0.5*tWCK)/tCK) - tWCKENL_WR) + tphy_wckcsgap + LP5 CDD   - JESD209-5A Table 352
        PRE_CFG.diff_rank_wr_gap_blx2[p][ch] = (PRE_CFG.wl[p][ch] + timing->lpddr5_bl_n_max_bl32_tck + CEIL(timing->lpddr5_twck_pst_wck, ratio) - timing->lpddr5_wckenl_wr_tck) + PRE_CFG.tphy_wckcsgap / ratio + PRE_CFG.lpddr5_cdd;
        // (ODTLoff + RU(tODToff(max)/tCK) - ODTLon) + tphy_wckcsgap + LP5 CDD                    - JESD209-5A Table 353 - Same Table 353
        PRE_CFG.diff_rank_wr_gap_wck_on_dq_odt_nt_odt_blx2[p][ch]= PRE_CFG.diff_rank_wr_gap_wck_on_dq_odt_nt_odt[p][ch];
#endif 
    }
#endif /* CINIT_LPDDR5 */
#endif /* CINIT_LPDDR */

#ifdef CINIT_DDR4
#if MEMC_NUM_RANKS > 1
    /*                                         BL/2               + 1 if Write preamble mode 2 nCK+ 1 if CRC enable */
    PRE_CFG.diff_rank_wr_gap[p][ch] = DIV_2(timing->burst_length) + QDYN.ddr4_wr_preamble[p][ch] + QDYN.wr_crc_enable + 4;
#endif /* MEMC_NUM_RANKS */
#endif /* CINIT_DDR4 */

}
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef DDRCTL_LPDDR
void cinit_cal_mrr2rdwr(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    SNPS_TRACE("Entering");
    uint32_t cl = PRE_CFG.cl[p];
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];

    uint32_t tdqsck_max;
    uint32_t tck_ps = SPD.tck_ps[p];
    uint8_t ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
    uint8_t  bl_div2;

    tdqsck_max = cinit_ps_to_tck(timing->lpddr4_tdqsck_max, SPD.tck_ps[p]);
    if (IS_LPDDR5) {
        // MRR to RD
        // RL + BL/n_max + RD(tWCKPST/tCK) + 2
        PRE_CFG.mrr2rd[p][ch] = PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_tck + timing->lpddr5_twck_pst_wck / ratio + 2;

#ifdef USE_JESD209_5
        // MRR to WR
        // RL + BL/n_max + RU(tWCKDQO(max)/tCK) - WL + 2
        // JESD209-5: Table 279 - MRR/MRW Timing Constraints: DQ ODT is Disable
        PRE_CFG.mrr2wr[p][ch] = PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) - PRE_CFG.wl[p][ch] + 2;
#else /* USE_JESD209_5 */
        // MRR to WR
        // tRTW + 2
        // JESD209-5A: Table 345 - MRR/MRW Timing Constraints: DQ ODT and NT-ODT is Disable
        PRE_CFG.mrr2wr[p][ch] = timing->lpddr5_trtw_tck + 2;
#endif /* USE_JESD209_5 */

#ifdef USE_JESD209_5
        // RL + RU(tWCKDQO(max)/tCK) + BL/n_max-ODTLon - RD(tODTon(min)/tCK) + 2
        // JESD209-5: Table 280 - MRR/MRW Timing Constraints: DQ ODT is Enable
        PRE_CFG.mrr2wr_odt[p][ch] = PRE_CFG.rl[p][ch] + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + timing->lpddr5_bl_n_max_tck - timing->lpddr5_odtlon_tck - timing->lpddr5_odton_min_ps / tck_ps + 2;
#else /* USE_JESD209_5 */
        // tRTW + 2
        // JESD209-5A: Table 346, 347 - MRR/MRW Timing Constraints
        PRE_CFG.mrr2wr_odt[p][ch] = timing->lpddr5_trtw_tck + 2;
#endif /* USE_JESD209_5 */

#ifdef USE_JESD209_5
        // MRR to MRW
        // RL + BL/n_max + RU(tWCKDQO(max)/tCK) + 2
        // JESD209-5: Table 279, 280 - MRR/MRW Timing Constraints
        PRE_CFG.mrr2mrw[p][ch] = PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_tck + CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps) + 2;
#else /* USE_JESD209_5 */
        // RL + BL/n_max + Max[RU(tWCKDQO(max)/tCK), RD(tWCKPST(max)/tCK)] + 2
        // JESD209-5A: Table 345, 346 - MRR/MRW Timing Constraints
        PRE_CFG.mrr2mrw[p][ch] = PRE_CFG.rl[p][ch] + timing->lpddr5_bl_n_max_tck + max(CEIL(timing->lpddr5_wckdqo_max_ps, tck_ps), timing->lpddr5_twck_pst_wck / ratio) + 2;
        if (hdlr->memCtrlr_m.lpddr5_mr[p].mr11.dq_odt > 0 && hdlr->memCtrlr_m.lpddr5_mr[p].mr41.nt_dq_odt > 0) {
            // For the case where DQ ODT is Enable and NT-ODT Enable
            // JESD209-5A: Table 347 - MRR/MRW Timing Constraints: DQ ODT is Enable and NT-ODT Enable
            if (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1) {
                // CKR=4:1: RL+BL/n_max+Max[RU(tWCKDQO(max)/tCK),RD(tWCKPST(max)/tCK)]+RU(ODT_RDon(max))+2
                //          = PRE_CFG.mrr2mrw[p][ch] + RU(ODT_RDon(max))
                PRE_CFG.mrr2mrw[p][ch] +=  CEIL(timing->lpddr5_odt_rdon_max_ps, tck_ps);
            } else {
                // CKR=2:1: RL+BL/n_max+Max[RU(tWCKDQO(max)/tCK),RD(tWCKPST(max)/tCK)]+RU(ODT_RDon(max))+3
                //          = PRE_CFG.mrr2mrw[p][ch] + RU(ODT_RDon(max)) + 1
                PRE_CFG.mrr2mrw[p][ch] += (CEIL(timing->lpddr5_odt_rdon_max_ps, tck_ps) + 1);
            }
        }
#endif /* USE_JESD209_5 */
    } else {
        // MRR to RD
        // tMRR
        PRE_CFG.mrr2rd[p][ch] = timing->lpddr4_tmrr;

        // BL/2 (Burst Length / 2)
        bl_div2 = DIV_2(timing->burst_length);

        // MRR to WR
        // RL + RU(tDQSCK(max)/tCK) + BL/2 + 3 - WL
        PRE_CFG.mrr2wr[p][ch] = (SPD.tAL + cl + bl_div2 + tdqsck_max + 3 - (SPD.tAL + PRE_CFG.cwl_x[p])) + PRE_CFG.wdqspreext[p][ch];

        // RL + RU(tDQSCK(max)/tCK) + BL/2 + 3 - ODTLon - RD(tODTon(min)/tCK)
        PRE_CFG.mrr2wr_odt[p][ch] = (SPD.tAL + cl + bl_div2 + tdqsck_max + 3 - PRE_CFG.odton[p][ch] - PRE_CFG.odton_min[p][ch]) + PRE_CFG.wdqspreext[p][ch];

        // MRR to MRW
        // RL + RU(tDQSCK(max)/tCK) + BL/2+ 3
        PRE_CFG.mrr2mrw[p][ch] = (SPD.tAL + cl + bl_div2 + tdqsck_max + 3);
    }
    SNPS_TRACE("Leaving");
}
#endif /* MEMC_LPDDR4 */

/** @brief Convert a timing parameter from ps to TCK cycles.
 *@param timing parameter in picoseconds
 *@param TCK clock period in picoseconds
 *@returns number of TCK cycles (rounded up).
 * @note For DDR5 TCK is rounded down and JEDEC formula =  roundup (Timing * 0.997/ (round down tCK))
 */
uint32_t cinit_ps_to_tck(uint32_t param_ps, uint32_t tck_ps)
{
    uint32_t tck_cycles;
#ifdef DDRCTL_DDR
#ifdef CINIT_DDR5
	  tck_cycles = cinit_round_down_only_int_ddr5(param_ps, tck_ps);
#else
	  tck_cycles = param_ps / tck_ps;
	  if (param_ps % tck_ps != 0)
		  tck_cycles++;
#endif // CINIT_DDR5
#else
	tck_cycles = param_ps / tck_ps;
	if (param_ps % tck_ps != 0)
		tck_cycles++;
#endif // DDRCTL_DDR
	return tck_cycles;
}

uint8_t get_cal_cycles(uint8_t cal_mode)
{
    uint8_t cycles;

    switch (cal_mode) {
    case 0:
        cycles = 0;
        break;
    case 1:
        cycles = 3;
        break;
    case 2:
        cycles = 4;
        break;
    case 3:
        cycles = 5;
        break;
    case 4:
        cycles = 6;
        break;
    case 5:
        cycles = 8;
        break;
    default:
        SNPS_ERROR("cal_mode = %u not yet supported", cal_mode);
        dwc_ddrctl_cinit_exit(1);
        break;
    }
    return cycles;
}

/**
 * @brief function to encode write recovery parameters for write to
 * mode register.
 */
void cinit_encode_wr_recovery(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n, uint32_t lpddr_mixed_pkg_en)
{
    SNPS_TRACE("Entering");
#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
        uint32_t twr_tck;
        uint32_t tck_ps = SPD.tck_ps[p];
        lpddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.lpddr4_mr[p];

        twr_tck = CEIL(timing->lpddr4_twr, tck_ps);
        if (twr_tck == 11 || twr_tck == 15 || twr_tck == 27 || twr_tck == 29 || twr_tck == 39 || twr_tck == 43) {
            twr_tck++;
        }
        SNPS_LOG("Encode Write Recover, tWR %u, tWR tCK %u",timing->lpddr4_twr, twr_tck);
        // TODO twr_tck == 8 & x16 => 10, x8 => 12
        if (IS_X16(n) && !lpddr_mixed_pkg_en) {
            if(SPD.lpddr4_scl!=1) {
              if (twr_tck <= 6) {
                  mregs->mr1.wr_recovery = 0;
              } else if (RANGE(twr_tck, 7, 10)) {
                  mregs->mr1.wr_recovery = 1;
              } else if (RANGE(twr_tck, 11, 16)) {
                  mregs->mr1.wr_recovery = 2;
              } else if (RANGE(twr_tck, 17, 20)) {
                  mregs->mr1.wr_recovery = 3;
              } else if (RANGE(twr_tck, 21, 24)) {
                  mregs->mr1.wr_recovery = 4;
              } else if (RANGE(twr_tck, 25, 30)) {
                  mregs->mr1.wr_recovery = 5;
              } else if (RANGE(twr_tck, 31, 34)) {
                  mregs->mr1.wr_recovery = 6;
              } else if (RANGE(twr_tck, 35, 40)) {
                  mregs->mr1.wr_recovery = 7;
              } else {
                  SNPS_ERROR("Illegal wr_recovery value %u passed in configuration!", twr_tck);
                  dwc_ddrctl_cinit_exit(1);
              }
            } else { //SPD.lpddr4_scl=2'b01
              if (twr_tck <= 11) {
                  mregs->mr1.wr_recovery = 0;
              } else if (RANGE(twr_tck, 12, 19)) {
                  mregs->mr1.wr_recovery = 1;
              } else if (RANGE(twr_tck, 20, 29)) {
                  mregs->mr1.wr_recovery = 2;
              } else if (RANGE(twr_tck, 30, 38)) {
                  mregs->mr1.wr_recovery = 3;
              } else if (RANGE(twr_tck, 39, 46)) {
                  mregs->mr1.wr_recovery = 4;
              } else if (RANGE(twr_tck, 47, 56)) {
                  mregs->mr1.wr_recovery = 5;
              } else if (RANGE(twr_tck, 57, 64)) {
                  mregs->mr1.wr_recovery = 6;
              } else if (RANGE(twr_tck, 65, 75)) {
                  mregs->mr1.wr_recovery = 7;
              } else {
                  SNPS_ERROR("Illegal wr_recovery value %u passed in configuration!", twr_tck);
                  dwc_ddrctl_cinit_exit(1);
              }
            }
        } else { //Byte mode
            if(SPD.lpddr4_scl!=1) {
              if (twr_tck <= 6)
                  mregs->mr1.wr_recovery = 0;
              else if (RANGE(twr_tck, 7, 12))
                  mregs->mr1.wr_recovery = 1;
              else if (RANGE(twr_tck, 13, 16))
                  mregs->mr1.wr_recovery = 2;
              else if (RANGE(twr_tck, 17, 22))
                  mregs->mr1.wr_recovery = 3;
              else if (RANGE(twr_tck, 23, 28))
                  mregs->mr1.wr_recovery = 4;
              else if (RANGE(twr_tck, 29, 32))
                  mregs->mr1.wr_recovery = 5;
              else if (RANGE(twr_tck, 33, 38))
                  mregs->mr1.wr_recovery = 6;
              else if (RANGE(twr_tck, 39, 44))
                  mregs->mr1.wr_recovery = 7;
              else {
                  SNPS_ERROR("Illegal wr_recovery value %u passed in configuration!", twr_tck);
                  dwc_ddrctl_cinit_exit(1);
              }
            } else { //SPD.lpddr4_scl=2'b01
              if (twr_tck <= 11) {
                  mregs->mr1.wr_recovery = 0;
              } else if (RANGE(twr_tck, 12, 21)) {
                  mregs->mr1.wr_recovery = 1;
              } else if (RANGE(twr_tck, 22, 29)) {
                  mregs->mr1.wr_recovery = 2;
              } else if (RANGE(twr_tck, 30, 40)) {
                  mregs->mr1.wr_recovery = 3;
              } else if (RANGE(twr_tck, 41, 50)) {
                  mregs->mr1.wr_recovery = 4;
              } else if (RANGE(twr_tck, 51, 58)) {
                  mregs->mr1.wr_recovery = 5;
              } else if (RANGE(twr_tck, 59, 68)) {
                  mregs->mr1.wr_recovery = 6;
              } else if (RANGE(twr_tck, 69, 79)) {
                  mregs->mr1.wr_recovery = 7;
              } else {
                  SNPS_ERROR("Illegal wr_recovery value %u passed in configuration!", twr_tck);
                  dwc_ddrctl_cinit_exit(1);
              }
            }
        }
        SNPS_LOG("mr1.wr_recovery = 0x%x", mregs->mr1.wr_recovery);
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
        uint32_t twr_tck;
        uint32_t tck_ps = SPD.tck_ps[p];
        lpddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.lpddr5_mr[p];

		twr_tck = CEIL(timing->lpddr5_twr_ps, tck_ps);
		uint8_t dvfsc_type = hdlr->memCtrlr_m.lpddr5_mr[p].mr19.dvfsc;
		uint8_t wr_lecc = hdlr->memCtrlr_m.lpddr5_mr[p].mr22.wecc;
		// encoding taken from JESD209-5A spec ;
		if (IS_X16(n) && !lpddr_mixed_pkg_en) {
			if (dvfsc_type == 0 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
				if (timing->lpddr5_nwr == 5)
					mregs->mr2.nwr = 0;
				else if (timing->lpddr5_nwr == 10)
					mregs->mr2.nwr = 1;
				else if (timing->lpddr5_nwr == 14)
					mregs->mr2.nwr = 2;
				else if (timing->lpddr5_nwr == 19)
					mregs->mr2.nwr = 3;
				else if (timing->lpddr5_nwr == 24)
					mregs->mr2.nwr = 4;
				else if (timing->lpddr5_nwr == 28)
					mregs->mr2.nwr = 5;
				else {
					SNPS_ERROR("Illegal lpddr5_nwr value %u passed in configuration!", timing->lpddr5_nwr);
                    dwc_ddrctl_cinit_exit(1);
                }
			} else if (dvfsc_type == 0 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
				// x16, w/o DVFSC, 4:1
				if (wr_lecc == 0) {
					if (timing->lpddr5_nwr == 3)
						mregs->mr2.nwr = 0;
					else if (timing->lpddr5_nwr == 5)
						mregs->mr2.nwr = 1;
					else if (timing->lpddr5_nwr == 7)
						mregs->mr2.nwr = 2;
					else if (timing->lpddr5_nwr == 10)
						mregs->mr2.nwr = 3;
					else if (timing->lpddr5_nwr == 12)
						mregs->mr2.nwr = 4;
					else if (timing->lpddr5_nwr == 14)
						mregs->mr2.nwr = 5;
					else if (timing->lpddr5_nwr == 16)
						mregs->mr2.nwr = 6;
					else if (timing->lpddr5_nwr == 19)
						mregs->mr2.nwr = 7;
					else if (timing->lpddr5_nwr == 21)
						mregs->mr2.nwr = 8;
					else if (timing->lpddr5_nwr == 24)
						mregs->mr2.nwr = 9;
					else if (timing->lpddr5_nwr == 26)
						mregs->mr2.nwr = 10;
					else if (timing->lpddr5_nwr == 28)
						mregs->mr2.nwr = 11;
					else if (timing->lpddr5_nwr == 32)
						mregs->mr2.nwr = 12;
					else if (timing->lpddr5_nwr == 37)
						//JESD209-5B Table 225 — nWR Latency
						mregs->mr2.nwr = 13;
					else if (timing->lpddr5_nwr == 41)
						// ballot RB23065-LPDDR5X extension Write Latency.pdf
						mregs->mr2.nwr = 14;
					else {
						SNPS_ERROR("Illegal lpddr5_nwr value %u passed in configuration!", timing->lpddr5_nwr);
                        dwc_ddrctl_cinit_exit(1);
                    }
				} else {
					if (timing->lpddr5_nwr == 18)
						mregs->mr2.nwr = 6; //As DRAM need not to support Link ECC below 3200 speed_bin, minimum speed_bin can be taken as 3201.
					else if (timing->lpddr5_nwr == 21)
						mregs->mr2.nwr = 7;
					else if (timing->lpddr5_nwr == 23)
						mregs->mr2.nwr = 8;
					else if (timing->lpddr5_nwr == 27)
						mregs->mr2.nwr = 9;
					else if (timing->lpddr5_nwr == 29)
						mregs->mr2.nwr = 10;
					else if (timing->lpddr5_nwr == 31)
						mregs->mr2.nwr = 11;
					else if (timing->lpddr5_nwr == 36)
						mregs->mr2.nwr = 12;
					else if (timing->lpddr5_nwr == 41)
						//JESD209-5B Table 225 — nWR Latency
						mregs->mr2.nwr = 13;
					else if (timing->lpddr5_nwr == 46) //9600Mbps
						mregs->mr2.nwr = 14;
					else {
						SNPS_ERROR("Illegal lpddr5_nwrvalue %u passed in configuration!", timing->lpddr5_nwr);
                        dwc_ddrctl_cinit_exit(1);
                    }
				}
			} else if (dvfsc_type == 1 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
				// x16, w/ DVFSC, 2:1
                if (timing->lpddr5_nwr == 6)
                    mregs->mr2.nwr = 0;
                else if (timing->lpddr5_nwr == 11)
                    mregs->mr2.nwr = 1;
                else if (timing->lpddr5_nwr == 17)
                    mregs->mr2.nwr = 2;
                else
                    SNPS_ERROR("Illegal lpddr5_nwrvalue %u passed in configuration!", timing->lpddr5_nwr);
			} else if (dvfsc_type == 1 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
				// x16, w/ DVFSC, 4:1
                if (timing->lpddr5_nwr == 3)
                    mregs->mr2.nwr = 0;
                else if (timing->lpddr5_nwr == 6)
                    mregs->mr2.nwr = 1;
                else if (timing->lpddr5_nwr == 9)
                    mregs->mr2.nwr = 2;
                else
                    SNPS_ERROR("Illegal lpddr5_nwrvalue %u passed in configuration!", timing->lpddr5_nwr);
			} else if (dvfsc_type == 2 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
				// x16, w/ eDVFSC, 2:1
                if (timing->lpddr5_nwr == 6)
                    mregs->mr2.nwr = 0;
                else if (timing->lpddr5_nwr == 11)
                    mregs->mr2.nwr = 1;
                else if (timing->lpddr5_nwr == 17)
                    mregs->mr2.nwr = 2;
                else if (timing->lpddr5_nwr == 22)
                    mregs->mr2.nwr = 3;
                else if (timing->lpddr5_nwr == 29)
                    mregs->mr2.nwr = 4;
                else if (timing->lpddr5_nwr == 33)
                    mregs->mr2.nwr = 5;
                else
                    SNPS_ERROR("Illegal lpddr5_nwrvalue %u passed in configuration!", timing->lpddr5_nwr);
			} else if (dvfsc_type == 2 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
				// x16, w/ eDVFSC, 4:1
                if (timing->lpddr5_nwr == 3)
                    mregs->mr2.nwr = 0;
                else if (timing->lpddr5_nwr == 6)
                    mregs->mr2.nwr = 1;
                else if (timing->lpddr5_nwr == 9)
                    mregs->mr2.nwr = 2;
                else if (timing->lpddr5_nwr == 11)
                    mregs->mr2.nwr = 3;
                else if (timing->lpddr5_nwr == 15)
                    mregs->mr2.nwr = 4;
                else if (timing->lpddr5_nwr == 17)
                    mregs->mr2.nwr = 5;
                else
                    SNPS_ERROR("Illegal lpddr5_nwrvalue %u passed in configuration!", timing->lpddr5_nwr);
			} else {
                SNPS_ERROR("Unexpected DVFSC (%d) and wckck ratio (%s) combination.", dvfsc_type,
                           ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(hdlr, p)));
			}
		} else { // x8 byte mode
			if (dvfsc_type == 0 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
				// x8, w/o DVFSC, 2:1
				if (timing->lpddr5_nwr == 5)
					mregs->mr2.nwr = 0;
				else if (timing->lpddr5_nwr == 10)
					mregs->mr2.nwr = 1;
				else if (timing->lpddr5_nwr == 15)
					mregs->mr2.nwr = 2;
				else if (timing->lpddr5_nwr == 20)
					mregs->mr2.nwr = 3;
				else if (timing->lpddr5_nwr == 25)
					mregs->mr2.nwr = 4;
				else if (timing->lpddr5_nwr == 29)
					mregs->mr2.nwr = 5;
				else {
					SNPS_ERROR("Illegal lpddr5_nwr value %u passed in configuration!", timing->lpddr5_nwr);
                    dwc_ddrctl_cinit_exit(1);
                }
			} else if (dvfsc_type == 0 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
				// x8, w/o DVFSC, 4:1
				if (wr_lecc == 0) {
					if (timing->lpddr5_nwr == 3)
						mregs->mr2.nwr = 0;
					else if (timing->lpddr5_nwr == 5)
						mregs->mr2.nwr = 1;
					else if (timing->lpddr5_nwr == 8)
						mregs->mr2.nwr = 2;
					else if (timing->lpddr5_nwr == 10)
						mregs->mr2.nwr = 3;
					else if (timing->lpddr5_nwr == 13)
						mregs->mr2.nwr = 4;
					else if (timing->lpddr5_nwr == 15)
						mregs->mr2.nwr = 5;
					else if (timing->lpddr5_nwr == 17)
						mregs->mr2.nwr = 6;
					else if (timing->lpddr5_nwr == 20)
						mregs->mr2.nwr = 7;
					else if (timing->lpddr5_nwr == 22)
						mregs->mr2.nwr = 8;
					else if (timing->lpddr5_nwr == 25)
						mregs->mr2.nwr = 9;
					else if (timing->lpddr5_nwr == 28)
						mregs->mr2.nwr = 10;
					else if (timing->lpddr5_nwr == 29)
						mregs->mr2.nwr = 11;
					else if (timing->lpddr5_nwr == 34)
						mregs->mr2.nwr = 12;
					else if (timing->lpddr5_nwr == 39)
						//JESD209-5B Table 225 — nWR Latency
						mregs->mr2.nwr = 13;
					else if (timing->lpddr5_nwr == 44) //9600Mbps
						mregs->mr2.nwr = 14;
					else {
						SNPS_ERROR("Illegal lpddr5_nwr value %u passed in configuration!", timing->lpddr5_nwr);
                        dwc_ddrctl_cinit_exit(1);
                    }
				} else {
					if (timing->lpddr5_nwr == 19)
						mregs->mr2.nwr = 6;
					else if (timing->lpddr5_nwr == 22)
						mregs->mr2.nwr = 7;
					else if (timing->lpddr5_nwr == 24)
						mregs->mr2.nwr = 8;
					else if (timing->lpddr5_nwr == 28)
						mregs->mr2.nwr = 9;
					else if (timing->lpddr5_nwr == 31)
						mregs->mr2.nwr = 10;
					else if (timing->lpddr5_nwr == 32)
						mregs->mr2.nwr = 11;
					else if (timing->lpddr5_nwr == 38)
						mregs->mr2.nwr = 12;
					else if (timing->lpddr5_nwr == 43)
						//JESD209-5B Table 225 — nWR Latency
						mregs->mr2.nwr = 13;
					else if (timing->lpddr5_nwr == 48)
						mregs->mr2.nwr = 14; //9600Mbps
					else {
						SNPS_ERROR("Illegal lpddr5_nwr value %u passed in configuration!", timing->lpddr5_nwr);
                        dwc_ddrctl_cinit_exit(1);
                    }
				}
			} else if (dvfsc_type == 1 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
				// x8, w DVFSC, 2:1
                if (timing->lpddr5_nwr == 6)
                    mregs->mr2.nwr = 0;
                else if (timing->lpddr5_nwr == 12)
                    mregs->mr2.nwr = 1;
                else if (timing->lpddr5_nwr == 18)
                    mregs->mr2.nwr = 2;
                else
                    SNPS_ERROR("Illegal lpddr5_nwr value %u passed in configuration!", timing->lpddr5_nwr);
			} else if (dvfsc_type == 1 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
				// x8, w DVFSC, 4:1
                if (timing->lpddr5_nwr == 3)
                    mregs->mr2.nwr = 0;
                else if (timing->lpddr5_nwr == 6)
                    mregs->mr2.nwr = 1;
                else if (timing->lpddr5_nwr == 9)
                    mregs->mr2.nwr = 2;
                else
                    SNPS_ERROR("Illegal lpddr5_nwr value %u passed in configuration!", timing->lpddr5_nwr);
			} else if (dvfsc_type == 2 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
				// x8, w eDVFSC, 2:1
                if (timing->lpddr5_nwr == 6)
                    mregs->mr2.nwr = 0;
                else if (timing->lpddr5_nwr == 12)
                    mregs->mr2.nwr = 1;
                else if (timing->lpddr5_nwr == 18)
                    mregs->mr2.nwr = 2;
                else if (timing->lpddr5_nwr == 23)
                    mregs->mr2.nwr = 3;
                else if (timing->lpddr5_nwr == 30)
                    mregs->mr2.nwr = 4;
                else if (timing->lpddr5_nwr == 35)
                    mregs->mr2.nwr = 5;
                else
                    SNPS_ERROR("Illegal lpddr5_nwr value %u passed in configuration!", timing->lpddr5_nwr);
			} else if (dvfsc_type == 2 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
				// x8, w eDVFSC, 4:1
                if (timing->lpddr5_nwr == 3)
                    mregs->mr2.nwr = 0;
                else if (timing->lpddr5_nwr == 6)
                    mregs->mr2.nwr = 1;
                else if (timing->lpddr5_nwr == 9)
                    mregs->mr2.nwr = 2;
                else if (timing->lpddr5_nwr == 12)
                    mregs->mr2.nwr = 3;
                else if (timing->lpddr5_nwr == 15)
                    mregs->mr2.nwr = 4;
                else if (timing->lpddr5_nwr == 18)
                    mregs->mr2.nwr = 5;
                else
                    SNPS_ERROR("Illegal lpddr5_nwr value %u passed in configuration!", timing->lpddr5_nwr);
			}
			SNPS_LOG("nWR twr_tck = %u, mregs->mr2.nwr = %u", twr_tck, mregs->mr2.nwr);
		}
	}
#endif /* CINIT_LPDDR5 */
#endif /* MEMC_LPDDR4 */

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[p];
        uint32_t twr_tck = PRE_CFG.twr[p][ch];

        switch (twr_tck) {
        case 10:
            mregs->mr0.wr_recovery = 0;
            break;
        case 12:
            mregs->mr0.wr_recovery = 1;
            break;
        case 14:
            mregs->mr0.wr_recovery = 2;
            break;
        case 16:
            mregs->mr0.wr_recovery = 3;
            break;
        case 18:
            mregs->mr0.wr_recovery = 4;
            break;
        case 20:
            mregs->mr0.wr_recovery = 5;
            break;
        case 22:
            mregs->mr0.wr_recovery = 7;
            break;
        case 24:
            mregs->mr0.wr_recovery = 6;
            break;
        case 26:
            mregs->mr0.wr_recovery = 8;
            break;
        default:
            SNPS_ERROR("Illegal wr_recovery value %u passed in configuration!", twr_tck);
            dwc_ddrctl_cinit_exit(1);
            break;
        }
        SNPS_LOG("mr0.wr_recovery = 0x%x", mregs->mr0.wr_recovery);
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[p];
        uint32_t twr_tck = PRE_CFG.twr[p][ch];

		if (twr_tck % 6 != 0)
			twr_tck = twr_tck + 6 - twr_tck % 6;
		switch (twr_tck) {
		case 48:
			mregs->mr6.wr_recovery = 0;
			break;
		case 54:
			mregs->mr6.wr_recovery = 1;
			break;
		case 60:
			mregs->mr6.wr_recovery = 2;
			break;
		case 66:
			mregs->mr6.wr_recovery = 3;
			break;
		case 72:
			mregs->mr6.wr_recovery = 4;
			break;
		case 78:
			mregs->mr6.wr_recovery = 5;
			break;
		case 84:
			mregs->mr6.wr_recovery = 6;
			break;
		case 90:
			mregs->mr6.wr_recovery = 7;
			break;
		case 96:
			mregs->mr6.wr_recovery = 8;
			break;
		// wr_recovery value is aligned to VIP version T-2022.06-2 / JEDEC REV185 for speedbin higher than 6400
		case 102:
			mregs->mr6.wr_recovery = 9;
			break;
		case 108:
			mregs->mr6.wr_recovery = 10;
			break;
		case 114:
			mregs->mr6.wr_recovery = 11;
			break;
		case 120:
			mregs->mr6.wr_recovery = 12;
			break;
		case 126:
			mregs->mr6.wr_recovery = 13;
			break;
      case 132:
			mregs->mr6.wr_recovery = 14;
			break;
		default:
			SNPS_ERROR("Illegal wr_recovery value %u passed in configuration!", twr_tck);
            dwc_ddrctl_cinit_exit(1);
			break;
		}
		SNPS_LOG("mr6.wr_recovery = 0x%x", mregs->mr6.wr_recovery);
	}
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */
    SNPS_TRACE("Leaving");
}

/**
 * @brief Function to encode mr0 CAS latency.
 * @note see JESD79-4B table 3
 */
void cinit_encode_cas_latency(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n)
{
    SNPS_TRACE("Entering");

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[p];
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
        uint32_t cas_latency = (hdlr->memCtrlr_m.ddr4_mr[p].mr5.read_dbi) ? timing->ddr4_tcl_rdbi_tck : timing->ddr4_tcl_tck;

        switch (cas_latency) {
        case 9:
            mregs->mr0.cl = 0;
            break;
        case 10:
            mregs->mr0.cl = 1;
            break;
        case 11:
            mregs->mr0.cl = 2;
            break;
        case 12:
            mregs->mr0.cl = 3;
            break;
        case 13:
            mregs->mr0.cl = 4;
            break;
        case 14:
            mregs->mr0.cl = 5;
            break;
        case 15:
            mregs->mr0.cl = 6;
            break;
        case 16:
            mregs->mr0.cl = 7;
            break;
        case 17:
            mregs->mr0.cl = 13;
            break;
        case 18:
            mregs->mr0.cl = 8;
            break;
        case 19:
            mregs->mr0.cl = 14;
            break;
        case 20:
            mregs->mr0.cl = 9;
            break;
        case 21:
            mregs->mr0.cl = 15;
            break;
        case 22:
            mregs->mr0.cl = 10;
            break;
        case 23:
            mregs->mr0.cl = 12;
            break;
        case 24:
            mregs->mr0.cl = 11;
            break;
        case 25:
            mregs->mr0.cl = 16;
            break;
        case 26:
            mregs->mr0.cl = 17;
            break;
        case 27:
            mregs->mr0.cl = 18;
            break;
        case 28:
            mregs->mr0.cl = 19;
            break;
        case 30:
            mregs->mr0.cl = 21;
            break;
        case 32:
            mregs->mr0.cl = 23;
            break;
        default:
            SNPS_ERROR("Illegal cl value %u passed in configuration!", cas_latency);
            dwc_ddrctl_cinit_exit(1);
            break;
        }
    SNPS_LOG("mr0.cl = 0x%x", mregs->mr0.cl);
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[p];
        uint32_t cas_latency = PRE_CFG.cl[p];

        if( (cas_latency % 2 ==0) && (cas_latency <= 90) && (cas_latency >= 22) ) {
            mregs->mr0.cl = cas_latency/2 -11 ;
        } else {
            SNPS_ERROR("Illegal cl value %u passed in configuration!", cas_latency);
            dwc_ddrctl_cinit_exit(1);
        }
        SNPS_LOG("mr0.cl = 0x%x", mregs->mr0.cl);
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */
    SNPS_TRACE("Leaving");
}

/**
 * @brief Function to encode mr2 CAS write latency.
 * @note see JEDEC79-4B table 7.
 */
void cinit_encode_cas_write_latency(SubsysHdlr_t *hdlr, uint32_t p)
{
    SNPS_TRACE("Entering");

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[p];

        switch (PRE_CFG.cwl_x[p]) {
        case 9:
            mregs->mr2.cwl = 0;
            break;
        case 10:
            mregs->mr2.cwl = 1;
            break;
        case 11:
            mregs->mr2.cwl = 2;
            break;
        case 12:
            mregs->mr2.cwl = 3;
            break;
        case 14:
            mregs->mr2.cwl = 4;
            break;
        case 16:
            mregs->mr2.cwl = 5;
            break;
        case 18:
            mregs->mr2.cwl = 6;
            break;
        case 20:
            mregs->mr2.cwl = 7;
            break;
        default:
            SNPS_ERROR("Illegal cwl value %u passed in configuration!", PRE_CFG.cwl_x[p]);
            dwc_ddrctl_cinit_exit(1);
            break;
        }
        SNPS_LOG("mr2.cwl = 0x%x", mregs->mr2.cwl);
    }
#endif
#endif /* DDRCTL_DDR */

    SNPS_TRACE("Leaving");
}

/*
 * @brief Function to encode mr6 tccd_l latency.
 * @note see JEDEC79-4B 14
 */
void cinit_encode_tccd_l_latency(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch)
{
    SNPS_TRACE("Entering");

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[p];

        SNPS_LOG("PRE_CFG.t_ccd[%u][%u] = %u", p, ch, PRE_CFG.t_ccd[p][ch]);
        switch (PRE_CFG.t_ccd[p][ch]) {
        case 4:
            mregs->mr6.tccd_l = 0;
            break;
        case 5:
            mregs->mr6.tccd_l = 1;
            break;
        case 6:
            mregs->mr6.tccd_l = 2;
            break;
        case 7:
            mregs->mr6.tccd_l = 3;
            break;
        case 8:
            mregs->mr6.tccd_l = 4;
            break;
        default:
            SNPS_ERROR("Illegal tccd_l value %u passed in configuration!", PRE_CFG.t_ccd[p][ch]);
            dwc_ddrctl_cinit_exit(1);
            break;
        }
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[p];

        switch (PRE_CFG.t_ccd[p][ch]) {
        case 8:
            mregs->mr13.tccd_l = 0;
            break;
        case 9:
            mregs->mr13.tccd_l = 1;
            break;
        case 10:
            mregs->mr13.tccd_l = 2;
            break;
        case 11:
            mregs->mr13.tccd_l = 3;
            break;
        case 12:
            mregs->mr13.tccd_l = 4;
            break;
        case 13:
            mregs->mr13.tccd_l = 5;
            break;
        case 14:
            mregs->mr13.tccd_l = 6;
            break;
        case 15:
            mregs->mr13.tccd_l = 7;
            break;
        case 16:
            mregs->mr13.tccd_l = 8;
            break;
        case 17:
            mregs->mr13.tccd_l = 9;
            break;
        case 18:
            mregs->mr13.tccd_l = 10;
            break;
        case 19:
            mregs->mr13.tccd_l = 11;
            break;
        case 20:
            mregs->mr13.tccd_l = 12;
            break;
        case 21:
            mregs->mr13.tccd_l = 13;
            break;
        case 22:
            mregs->mr13.tccd_l = 14;
            break;
        default:
            SNPS_ERROR("Illegal tccd_l value %u passed in configuration!", PRE_CFG.t_ccd[p][ch]);
            dwc_ddrctl_cinit_exit(1);
            break;
        }
        SNPS_LOG("mr13.tccd_l = 0x%x", mregs->mr13.tccd_l);
    }
#endif /* CINIT_DDR5 */
#endif /* DDRCTL_DDR */

    SNPS_TRACE("Leaving");
}

/**
 * @brief Function to encode write cmd latency when CRC and DM are enabled.
 * @note see JEDEC79-4B table 9.
 */
void cinit_encode_write_cmd_latency(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n)
{
    SNPS_TRACE("Entering");

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[p];
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];

        switch (timing->ddr4_wcl_tck) {
        case 4:
            mregs->mr3.wcl = 0;
            break;
        case 5:
            mregs->mr3.wcl = 1;
            break;
        case 6:
            mregs->mr3.wcl = 2;
            break;
        default:
            SNPS_ERROR("Illegal wcl value %u passed in configuration!", timing->ddr4_wcl_tck);
            dwc_ddrctl_cinit_exit(1);
            break;
        }
        SNPS_LOG("mr3.wcl = 0x%0x", mregs->mr3.wcl);
    }
#endif
#endif /* DDRCTL_DDR */

    SNPS_TRACE("Leaving");
}

/**
 * @brief Function to encode mr2 rl_wl value.
 * @note see JESD209-4C table 28-1 and table 28-2
 */
void cinit_encode_rl_wl(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n, uint32_t lpddr_mixed_pkg_en)
{
    SNPS_TRACE("Entering");

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
        lpddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.lpddr4_mr[p];
        uint32_t read_dbi = hdlr->memCtrlr_m.lpddr4_mr[p].mr3.read_dbi;
        uint32_t rl = (read_dbi) ? PRE_CFG.cl_dbi[p] : PRE_CFG.cl[p];
        uint32_t wl = (hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls == 0) ? timing->lpddr4_cwl_seta : timing->lpddr4_cwl_setb;    // write latency
        uint32_t mr2_rl, mr2_wl;
        uint32_t rl_row, wl_row;
        // determines if x16 values should be used as x8 values applies to x16 devices if   lpddr_mixed_pkg_en=1
        uint32_t is_x16_val = IS_X16(n) && !lpddr_mixed_pkg_en;

        SNPS_LOG("rl = %u, wl = %u read_dbi = %u, x16 = %u, lpddr_mixed_pkg_en = %u, wls = %u", rl, wl, read_dbi, IS_X16(n), lpddr_mixed_pkg_en, hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls);
        rl_row = cinit_get_rl_row(rl, is_x16_val, read_dbi);
        wl_row = cinit_get_wl_row(wl, is_x16_val, hdlr->memCtrlr_m.lpddr4_mr[p].mr2.wls);
        mr2_rl = rl_row;
        mr2_wl = wl_row;
        mregs->mr2.rl_wl = (mr2_wl << 3) | mr2_rl;
        SNPS_LOG("mr2.rl_wl = 0x%x", mregs->mr2.rl_wl);
        CONSTRAIN_INSIDE(mregs->mr2.rl_wl, 0, 0x3f);    // 6 bits
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        cinit_encode_lpddr5_rl_wl(hdlr, p, ch, n, lpddr_mixed_pkg_en);
    }
#endif /* CINIT_LPDDR5 */
#endif /* MEMC_LPDDR4 */

    SNPS_TRACE("Leaving");
}

/** @brief Implement a lookup table for nRTP, the row number is the
 * lookup index
 * @note see JESD209-4C table 28-1 and table 28-2.
 * For nRTP x16 and x8 are the same
 */
uint32_t cinit_get_nrtp(uint8_t row)
{
    SNPS_TRACE("Entering");
    uint32_t ret;
    static const uint32_t nrtp[8] = { 8, 8, 8, 8, 10, 12, 14, 16 };

    ret = nrtp[row];
    SNPS_TRACE("Leaving");
    return ret;
}

// define a helper macro for the next few functions.
#define FIND_VAL_IN_ARRAY(_val, _array) \
    for (i = 0; i < sizeof(_array); i++) { \
        if (_array[i] == _val) { \
            ret = i; break; \
        } \
    } \

uint32_t cinit_get_rl_row(uint8_t rl, uint8_t x16, uint8_t dbi)
{
    SNPS_TRACE("Entering");
    uint32_t ret, i;
    static const uint32_t x16_rl_nodbi[8] = { 6, 10, 14, 20, 24, 28, 32, 36 };
    static const uint32_t x16_rl_dbi[8] = { 6, 12, 16, 22, 28, 32, 36, 40 };

    static const uint32_t x8_rl_nodbi[8] = { 6, 10, 16, 22, 26, 32, 36, 40 };
    static const uint32_t x8_rl_dbi[8] = { 6, 12, 18, 24, 30, 36, 40, 44 };

    ret = 0;
    if (x16 == 1) {
        if (dbi == 1)
            FIND_VAL_IN_ARRAY(rl, x16_rl_dbi)
        else
            FIND_VAL_IN_ARRAY(rl, x16_rl_nodbi)
    } else {
        // x8
        if (dbi == 1)
            FIND_VAL_IN_ARRAY(rl, x8_rl_dbi)
        else
            FIND_VAL_IN_ARRAY(rl, x8_rl_nodbi)
    }
    if (ret > 8) {
        SNPS_ERROR("rl = %u, x16 = %u, dbi = %u is invalid", rl, x16, dbi);
        dwc_ddrctl_cinit_exit(1);
    }

    SNPS_TRACE("Leaving");
    return ret;
}

/** @brief */
uint32_t cinit_get_wl_row(uint8_t wl, uint8_t x16, uint8_t wls)
{
    SNPS_TRACE("Entering");
    uint32_t ret, i;
    static const uint32_t x16_wl_seta[8] = { 4, 6, 8, 10, 12, 14, 16, 18 };
    static const uint32_t x16_wl_setb[8] = { 4, 8, 12, 18, 22, 26, 30, 34 };
    // values look the same
    static const uint32_t x8_wl_seta[8] = { 4, 6, 8, 10, 12, 14, 16, 18 };
    static const uint32_t x8_wl_setb[8] = { 4, 8, 12, 18, 22, 26, 30, 34 };

    ret = 0;
    if (x16 == 1) {
        if (wls == 1)
            FIND_VAL_IN_ARRAY(wl, x16_wl_setb)
        else
            FIND_VAL_IN_ARRAY(wl, x16_wl_seta)
    } else {
        if (wls == 1) {
            FIND_VAL_IN_ARRAY(wl, x8_wl_setb)
        } else {
            if (wls == 1)
                FIND_VAL_IN_ARRAY(wl, x8_wl_setb)
            else
                FIND_VAL_IN_ARRAY(wl, x8_wl_seta)
        }
    }
    if (ret > 8) {
        SNPS_ERROR("wl = %u, x16 = %u, wls = %u is invalid", wl, x16, wls);
        dwc_ddrctl_cinit_exit(1);
    }

    SNPS_TRACE("Leaving");
    return ret;
}

/**
 * @brief method to return the min value for t_xsr.
 * This is used by simulation env to set the min value in a SV constraint.
 */
uint32_t dwc_cinit_get_min_t_xsr(SubsysHdlr_t *hdlr, uint32_t tck_ps, uint32_t dvfsc_type)
{
    SNPS_TRACE("Entering");
    uint32_t ret = 0;

#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        uint32_t trfcab_i = dwc_cinit_get_lpddr4_trfcab(SPD.sdram_capacity_mbits[0]);
        uint32_t trfcab_mp_i = dwc_cinit_get_lpddr4_trfcab(SPD.sdram_capacity_mbits_lp45_mp[0]);
        uint32_t lpddr4_txsr_ps;
        uint32_t trfcab;

        // calculate largest trfcab from trfcab/trfacab_mp and assign it totrfcab
        if (trfcab_mp_i>trfcab_i) {
		trfcab = trfcab_mp_i;
        } else {
		trfcab = trfcab_i;
        }
        lpddr4_txsr_ps = max((trfcab + 7500), 2 * tck_ps);
        ret = cinit_ps_to_tck(lpddr4_txsr_ps, tck_ps);
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        uint32_t trfcab_i, trfcab_mp_i, trfcab, lpddr5_txsr_ps;

        trfcab_i = dwc_cinit_get_lpddr5_trfcab(SPD.sdram_capacity_mbits[0], dvfsc_type);
        trfcab_mp_i = dwc_cinit_get_lpddr5_trfcab(SPD.sdram_capacity_mbits_lp45_mp[0], dvfsc_type);

        // calculate largest trfcab from trfcab/trfacab_mp and assign it totrfcab
        if (trfcab_mp_i>trfcab_i) {
		trfcab = trfcab_mp_i;
        } else {
		trfcab = trfcab_i;
        }
        lpddr5_txsr_ps = max(7500, 2 * tck_ps) + trfcab;
        ret = cinit_ps_to_tck(lpddr5_txsr_ps, tck_ps);
    }
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */

    SNPS_TRACE("Leaving");
    return ret;
}

uint32_t dwc_cinit_get_min_t_xp(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n)
{
    SNPS_TRACE("Entering");
    uint32_t ret = 0;

#ifdef DDRCTL_LPDDR
	ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];

	if (IS_LPDDR4)
		ret = timing->lpddr4_txp;
	if (IS_LPDDR5) {
		// [JESD209-5A Table 226] If CS ODT is enabled, tPDXCSODTON needs to be applied between PDX and a valid command
		// tXP is defined as Max(7ns, 3nCK), which is smaller than tPDXCSODTON (20 ns)
                // [JESD209-5B] CS ODT behavior is support for LPDDR5X SDRAM if MR11.OP[7]=1. tPDXCSODTON must be removed from t_xp in this case
		// MR17.OP[4] - 0:ODTD-CS Enable RZQ/3, 1:ODTD-CS Disable(default)
                // MR11.OP[7] - 0:Basic CS ODT behavior (default), 1:CS ODT behavior option; always 0 for LPDDR5
		ret = (((hdlr->memCtrlr_m.lpddr5_mr[p].mr17.odtd_cs == 0) && (hdlr->memCtrlr_m.lpddr5_mr[p].mr11.cs_odt_op == 0))? max(timing->lpddr5_txp_ps, timing->lpddr5_tpdxcsodton_ps) :
		                                                               timing->lpddr5_txp_ps);
	#ifdef DWC_DDRCTL_P80001562_84420
		ret += timing->lpddr5_tcsh_ps;
	#endif /* DWC_DDRCTL_P80001562_84420 */
	}
	SNPS_LOG("freq = %u, txp_ps = %u (mr17.odtd_cs = %u, mr11.cs_odt_op = %u, tpdxcsodton_ps = %u, txp_ps = %u, tcsh_ps = %u)",
	p, ret, hdlr->memCtrlr_m.lpddr5_mr[p].mr17.odtd_cs, hdlr->memCtrlr_m.lpddr5_mr[p].mr11.cs_odt_op, timing->lpddr5_tpdxcsodton_ps, timing->lpddr5_txp_ps, timing->lpddr5_tcsh_ps);
#endif /* DDRCTL_LPDDR */

    SNPS_TRACE("Leaving");
    return ret;
}

/** @brief method to encode MR1 OP[7:4] for LPDDR5 */
void cinit_encode_lpddr5_rl_wl(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n, uint32_t lpddr_mixed_pkg_en)
{
    SNPS_TRACE("Entering");

#ifdef DDRCTL_LPDDR
    uint32_t wl = hdlr->memCtrlr_m.pre_cfg.wl[p][ch];
    uint8_t wl_op = 0, rl_nrtp;
    uint8_t enhanced_dvfsc_enable = (hdlr->memCtrlr_m.lpddr5_mr[p].mr19.dvfsc == 2) ? 1 : 0;
    uint8_t wl_seta = (hdlr->memCtrlr_m.lpddr5_mr[p].mr3.wls == 0) ? 1 : 0;
    uint32_t tck_ps = SPD.tck_ps[p];
    uint32_t is_x16_val = IS_X16(n) && !lpddr_mixed_pkg_en;


	SNPS_LOG("wl = %u, x16 = %u, wl_seta = %u, wckck ratio[%u] = %s",
              wl, IS_X16(n), wl_seta, p, ddrctl_sw_get_ratio_str(ddrctl_sw_get_ratio(hdlr, p)));
	if (wl_seta && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
		switch (wl) { //Set-A encodings
		case 4:
			if (tck_ps >= 7520) //lp5_data_rate = [ >40 : <=533] Mbps
				wl_op = 0;
			else if (tck_ps < 7520 && tck_ps >= 3750) //lp5_data_rate = [>533 : <=1067] Mbps
				wl_op = 1;
			break;
		case 6:
			wl_op = 2;
			break;
		case 8:
			if (tck_ps < 2500 && tck_ps >= 1875) //lp5_data_rate = [>1600 : <=2133] Mbps
				wl_op = 3;
			else if (tck_ps < 1875 && tck_ps >= 1454) //lp5_data_rate = [>2133 : <=2750] Mbps
				wl_op = 4;
			break;
		case 10:
			wl_op = 5;
			break;
		default:
			wl_op = 0;
			break;
		}
	} else if (!wl_seta && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
		switch (wl) { //Set-B encodings
		case 4:
			wl_op = 0;
			break;
		case 6:
			wl_op = 1;
			break;
		case 8:
			wl_op = 2;
			break;
		case 10:
			wl_op = 3;
			break;
		case 14:
			wl_op = 4;
			break;
		case 16:
			wl_op = 5;
			break;
		default:
			wl_op = 0;
			break;
		}
	} else if (wl_seta && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
		switch (wl) { //Set-A encodings
		case 2:
			if (tck_ps >= 14926) //lp5_data_rate = [>40 : <=533] Mbps
				wl_op = 0;
			else if (tck_ps < 14926 && tck_ps >= 7520) //lp5_data_rate = [>533 : <=1067] Mbps
				wl_op = 1;
			break;
		case 3:
			wl_op = 2;
			break;
		case 4:
			if (tck_ps < 5000 && tck_ps >= 3750) //lp5_data_rate = [>1600 : <=2133] Mbps
				wl_op = 3;
			else if (tck_ps < 3750 && tck_ps >= 2900) //lp5_data_rate = [>2133 : <=2750] Mbps
				wl_op = 4;
			break;
		case 5:
			wl_op = 5;
			break;
		case 6:
			if (tck_ps < 2500 && tck_ps >= 2150) //lp5_data_rate = [>3200 : <=3733] Mbps
				wl_op = 6;
			else if (tck_ps < 2150 && tck_ps >= 1875)	//lp5_data_rate = [>3733 : <=4267] Mbps
				wl_op = 7;
			break;
		case 7:
			wl_op = 8;
			break;
		case 8:
			wl_op = 9;
			break;
		case 9:
			if (tck_ps < 1454 && tck_ps >= 1334) //lp5_data_rate = [>5500 : <=6000] Mbps
				wl_op = 10;
			else if (tck_ps < 1334 && tck_ps >= 1250)	//lp5_data_rate = [>6000 : <=6400] Mbps
				wl_op = 11;
			break;
		case 11:
			wl_op = 12;
			break;
		case 12:
			wl_op = 13;
			break;
		case 14:
			//ballot RB23065-LPDDR5X extension Write Latency.pdf
			wl_op = 14;
			break;
		default:
			wl_op = 0;
			break;
		}
	} else if (!wl_seta && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
		switch (wl) { //Set-B encodings
		case 2:
			wl_op = 0;
			break;
		case 3:
			wl_op = 1;
			break;
		case 4:
			wl_op = 2;
			break;
		case 5:
			wl_op = 3;
			break;
		case 7:
			wl_op = 4;
			break;
		case 8:
			wl_op = 5;
			break;
		case 9:
			wl_op = 6;
			break;
		case 11:
			wl_op = 7;
			break;
		case 12:
			wl_op = 8;
			break;
		case 14:
			wl_op = 9;
			break;
		case 15:
			wl_op = 10;
			break;
		case 16:
			wl_op = 11;
			break;
		case 19:
			wl_op = 12;
			break;
		case 22:
			wl_op = 13;
			break;
		case 24:
			//ballot RB23065-LPDDR5X extension Write Latency.pdf
			wl_op = 14;
			break;
		default:
			wl_op = 0;
			break;
		}
	} else {
		SNPS_ERROR("Setting not yet supported for wl_op", NULL);
        dwc_ddrctl_cinit_exit(1);
	}
	hdlr->memCtrlr_m.lpddr5_mr[p].mr1.write_latency = wl_op;
	uint8_t read_dbi = hdlr->memCtrlr_m.lpddr5_mr[p].mr3.read_dbi;
	uint8_t rd_lecc = hdlr->memCtrlr_m.lpddr5_mr[p].mr22.recc;
    uint8_t dvfsc_type = hdlr->memCtrlr_m.lpddr5_mr[p].mr19.dvfsc;

    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];

	// Next encode mr2.rl_nrtp //JESD209-5B,Table 220
	if (is_x16_val && dvfsc_type == 0 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
		if (read_dbi == 0) { //set0
			if (timing->lpddr5_rl_tck == 6)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 8)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 10)
				rl_nrtp = 2;
			else if (timing->lpddr5_rl_tck == 12)
				rl_nrtp = 3;
			else if (timing->lpddr5_rl_tck == 16)
				rl_nrtp = 4;
			else if (timing->lpddr5_rl_tck == 18)
				rl_nrtp = 5;
			else
				rl_nrtp = 0;
		} else {
			// DBI-RD enabled //Set1
			if (timing->lpddr5_rl_tck == 6)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 8)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 10)
				rl_nrtp = 2;
			else if (timing->lpddr5_rl_tck == 14)
				rl_nrtp = 3;
			else if (timing->lpddr5_rl_tck == 16)
				rl_nrtp = 4;
			else if (timing->lpddr5_rl_tck == 20)
				rl_nrtp = 5;
			else
				rl_nrtp = 0;
		}
	} else if (is_x16_val && dvfsc_type == 0 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) { //Set0
#ifdef USE_JESD209_5
        SNPS_LOG("Using JESD209_5 MR2 encoding timing->lpddr5_rl_tck = %u", timing->lpddr5_rl_tck);
        rl_nrtp = 0;
        if (timing->lpddr5_rl_tck == 3)
            rl_nrtp = 0;
        else if (timing->lpddr5_rl_tck == 4)
            rl_nrtp = 1;
        else if (timing->lpddr5_rl_tck == 5)
            rl_nrtp = 2;
        else if (timing->lpddr5_rl_tck == 6)
            rl_nrtp = 3;
        else if (timing->lpddr5_rl_tck == 8)
            rl_nrtp = 4;
        else if (timing->lpddr5_rl_tck == 9)
            rl_nrtp = 5;
        else if (timing->lpddr5_rl_tck == 10)
            rl_nrtp = 6;
        else if (timing->lpddr5_rl_tck == 12)
            rl_nrtp = 7;
        else if (timing->lpddr5_rl_tck == 13)
            rl_nrtp = 8;
        else if (timing->lpddr5_rl_tck == 15)
            rl_nrtp = 9;
        else if (timing->lpddr5_rl_tck == 16)
            rl_nrtp = 10;
        else if (timing->lpddr5_rl_tck == 17)
            rl_nrtp = 11;
        else if (timing->lpddr5_rl_tck == 20)
            rl_nrtp = 12;
        else if (timing->lpddr5_rl_tck == 23)
            rl_nrtp = 13;
        else if (timing->lpddr5_rl_tck == 24)
            rl_nrtp = 14;
        else {
            SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
            dwc_ddrctl_cinit_exit(1);
        }
#else
        if (read_dbi == 0) { //JDES209-5B, Table 220 ,Set0
            if (rd_lecc == 0) {
                rl_nrtp = 0;
                if (timing->lpddr5_rl_tck == 3)
                    rl_nrtp = 0;
                else if (timing->lpddr5_rl_tck == 4)
                    rl_nrtp = 1;
                else if (timing->lpddr5_rl_tck == 5)
                    rl_nrtp = 2;
                else if (timing->lpddr5_rl_tck == 6)
                    rl_nrtp = 3;
                else if (timing->lpddr5_rl_tck == 8)
                    rl_nrtp = 4;
                else if (timing->lpddr5_rl_tck == 9)
                    rl_nrtp = 5;
                else if (timing->lpddr5_rl_tck == 10)
                    rl_nrtp = 6;
                else if (timing->lpddr5_rl_tck == 12)
                    rl_nrtp = 7;
                else if (timing->lpddr5_rl_tck == 13)
                    rl_nrtp = 8;
                else if (timing->lpddr5_rl_tck == 15)
                    rl_nrtp = 9;
                else if (timing->lpddr5_rl_tck == 16)
                    rl_nrtp = 10;
                else if (timing->lpddr5_rl_tck == 17)
                    rl_nrtp = 11;
                else if (timing->lpddr5_rl_tck == 20)
                    rl_nrtp = 12;
                else if (timing->lpddr5_rl_tck == 23)
                    rl_nrtp = 13;
                //ballot tg426_9^20230221^1862.05B^Micron^LPDDR5X_RL_9600.pdf
                else if (timing->lpddr5_rl_tck == 25)
                    rl_nrtp = 14;
                else {
                    SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
                    dwc_ddrctl_cinit_exit(1);
                }
            } else {//JDES209-5B, Table 222 ,Set0
                switch (timing->lpddr5_rl_tck) {
                case 12:
                    rl_nrtp = 6;
                    break;
                case 13:
                    rl_nrtp = 7;
                    break;
                case 15:
                    rl_nrtp = 8;
                    break;
                case 17:
                    rl_nrtp = 9;
                    break;
                case 18:
                    rl_nrtp = 10;
                    break;
                case 19:
                    rl_nrtp = 11;
                    break;
                case 23:
                    rl_nrtp = 12;
                    break;
                case 26:
                    rl_nrtp = 13;
                    break;
                //ballot tg426_9^20230221^1862.05B^Micron^LPDDR5X_RL_9600.pdf
                case 29:
                    rl_nrtp = 14;
                    break;
                default:
                    rl_nrtp = 0;
                    SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
                    dwc_ddrctl_cinit_exit(1);
                    break;
                }
            }
        } else {
            // DBI-RD enabled //Set1
            rl_nrtp = 0;
            if (timing->lpddr5_rl_tck == 3)
                rl_nrtp = 0;
            else if (timing->lpddr5_rl_tck == 4)
                rl_nrtp = 1;
            else if (timing->lpddr5_rl_tck == 5)
                rl_nrtp = 2;
            else if (timing->lpddr5_rl_tck == 7)
                rl_nrtp = 3;
            else if (timing->lpddr5_rl_tck == 8)
                rl_nrtp = 4;
            else if (timing->lpddr5_rl_tck == 10)
                rl_nrtp = 5;
            else if (timing->lpddr5_rl_tck == 11)
                rl_nrtp = 6;
            else if (timing->lpddr5_rl_tck == 13)
                rl_nrtp = 7;
            else if (timing->lpddr5_rl_tck == 14)
                rl_nrtp = 8;
            else if (timing->lpddr5_rl_tck == 16)
                rl_nrtp = 9;
            else if (timing->lpddr5_rl_tck == 17)
                rl_nrtp = 10;
            else if (timing->lpddr5_rl_tck == 18)
                rl_nrtp = 11;
            else if (timing->lpddr5_rl_tck == 22)
                rl_nrtp = 12;
            else if (timing->lpddr5_rl_tck == 25)
                rl_nrtp = 13;
            //ballot tg426_9^20230221^1862.05B^Micron^LPDDR5X_RL_9600.pdf
            else if (timing->lpddr5_rl_tck == 28)
                rl_nrtp = 14;
            else {
                SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
                dwc_ddrctl_cinit_exit(1);
            }
        }
#endif /* USE_JESD209_5 */
	} else if (!is_x16_val && dvfsc_type==0 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
		if (read_dbi == 0) { //Set0
			if (timing->lpddr5_rl_tck <= 6)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 8)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 10)
				rl_nrtp = 2;
			else if (timing->lpddr5_rl_tck == 14)
				rl_nrtp = 3;
			else if (timing->lpddr5_rl_tck == 16)
				rl_nrtp = 4;
			else if (timing->lpddr5_rl_tck == 20)
				rl_nrtp = 5;
			else
				rl_nrtp = 0;
		} else {
			// DBI-RD enabled //Set1
			if (timing->lpddr5_rl_tck <= 6)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 8)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 12)
				rl_nrtp = 2;
			else if (timing->lpddr5_rl_tck == 14)
				rl_nrtp = 3;
			else if (timing->lpddr5_rl_tck == 18)
				rl_nrtp = 4;
			else if (timing->lpddr5_rl_tck == 20)
				rl_nrtp = 5;
			else
				rl_nrtp = 0;
		}
	} else if (!is_x16_val && dvfsc_type==0 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
		if (read_dbi == 0) { //JESD209-5B, Table 220 — Read Latencies for Read Link ECC off case (DVFSC disabled)
			if (rd_lecc == 0) { //Set1
				switch (timing->lpddr5_rl_tck) {
				case 3:
					rl_nrtp = 0;
					break;
				case 4:
					rl_nrtp = 1;
					break;
				case 5:
					rl_nrtp = 2;
					break;
				case 7:
					rl_nrtp = 3;
					break;
				case 8:
					rl_nrtp = 4;
					break;
				case 10:
					rl_nrtp = 5;
					break;
				case 11:
					rl_nrtp = 6;
					break;
				case 13:
					rl_nrtp = 7;
					break;
				case 14:
					rl_nrtp = 8;
					break;
				case 16:
					rl_nrtp = 9;
					break;
				case 17:
					rl_nrtp = 10;
					break;
				case 18:
					rl_nrtp = 11;
					break;
				case 22:
					rl_nrtp = 12;
					break;
				case 25:
					rl_nrtp = 13;
					break;
                                //ballot tg426_9^20230221^1862.05B^Micron^LPDDR5X_RL_9600.pdf
				case 28:
					rl_nrtp = 14;
					break;
				default:
					rl_nrtp = 0;
					break;
				}
			} else { //JESD209-5B,Table 222 — Read Latencies for Read Link ECC on case (DVFSC disabled) //Set1
				switch (timing->lpddr5_rl_tck) {
				case 13:
					rl_nrtp = 6;
					break;
				case 14:
					rl_nrtp = 7;
					break;
				case 16:
					rl_nrtp = 8;
					break;
				case 18:
					rl_nrtp = 9;
					break;
				case 20:
					rl_nrtp = 10;
					break;
				case 21:
					rl_nrtp = 11;
					break;
				case 24:
					rl_nrtp = 12;
					break;
				case 28:
					rl_nrtp = 13;
					break;
				// ballot tg426_9^20230221^1862.05B^Micron^LPDDR5X_RL_9600.pdf
				case 30:
					rl_nrtp = 14;
					break;
				default:
					rl_nrtp = 0;
					break;
				}
			}
		} else {
			// DBI-RD enabled //JESD209-5B, Table 220 — Read Latencies for Read Link ECC off case (DVFSC disabled) //Set2
			switch (timing->lpddr5_rl_tck) {
			case 3:
				rl_nrtp = 0;
				break;
			case 4:
				rl_nrtp = 1;
				break;
			case 6:
				rl_nrtp = 2;
				break;
			case 7:
				rl_nrtp = 3;
				break;
			case 9:
				rl_nrtp = 4;
				break;
			case 10:
				rl_nrtp = 5;
				break;
			case 12:
				rl_nrtp = 6;
				break;
			case 14:
				rl_nrtp = 7;
				break;
			case 15:
				rl_nrtp = 8;
				break;
			case 17:
				rl_nrtp = 9;
				break;
			case 19:
				rl_nrtp = 10;
				break;
			case 20:
				rl_nrtp = 11;
				break;
			case 24:
				rl_nrtp = 12;
				break;
			case 26:
				rl_nrtp = 13;
				break;
                        //ballot tg426_9^20230221^1862.05B^Micron^LPDDR5X_RL_9600.pdf
			case 29:
				rl_nrtp = 14;
				break;
			default:
				rl_nrtp = 0;
				break;
			}
		}
	} else if (is_x16_val && dvfsc_type == 1 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
		if (read_dbi == 0) { //JESD209-5B, Table 221 — Read Latencies for Read Link ECC off case (DVFSC enabled) //Set0
			if (timing->lpddr5_rl_tck == 6)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 8)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 12)
				rl_nrtp = 2;
			else
				rl_nrtp = 0;
		} else {
			// DBI-RD enabled
			if (timing->lpddr5_rl_tck == 6)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 10)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 12)
				rl_nrtp = 2;
			else
				rl_nrtp = 0;
		}
	} else if (is_x16_val && dvfsc_type == 1 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
		if (read_dbi == 0) {
			rl_nrtp = 0;
			if (timing->lpddr5_rl_tck <= 3)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 4)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 6)
				rl_nrtp = 2;
			else {
				SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
                dwc_ddrctl_cinit_exit(1);
            }
		} else {
			// DBI-RD enabled
			rl_nrtp = 0;
			if (timing->lpddr5_rl_tck <= 3)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 5)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 6)
				rl_nrtp = 2;
			else {
				SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
                dwc_ddrctl_cinit_exit(1);
            }
		}
	} else if (!is_x16_val && (dvfsc_type == 1) && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
		if (read_dbi == 0) {
			if (timing->lpddr5_rl_tck <= 6)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 10)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 12)
				rl_nrtp = 2;
			else
				rl_nrtp = 0;
		} else {
			// DBI-RD enabled
			if (timing->lpddr5_rl_tck <= 6)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 10)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 14)
				rl_nrtp = 2;
			else
				rl_nrtp = 0;
		}
	} else if (!is_x16_val && dvfsc_type == 1 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
		if (read_dbi == 0) {
			if (timing->lpddr5_rl_tck == 3)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 5)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 6)
				rl_nrtp = 2;
			else
				rl_nrtp = 0;
		} else {
			// DBI-RD enabled
			if (timing->lpddr5_rl_tck == 3)
				rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 5)
				rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 7)
				rl_nrtp = 2;
			else
				rl_nrtp = 0;
		}
	} else if (dvfsc_type == 2 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_2_1)) {
        // JESD209-5C, Table 227 — Read Latencies for Read Link ECC off case (DVFSC disabled and Enhanced DVFS enabled)
        uint8_t set = !is_x16_val + read_dbi;
		if (set == 0) { 
			     if (timing->lpddr5_rl_tck == 6)    rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 9)    rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 13)   rl_nrtp = 2;
			else if (timing->lpddr5_rl_tck == 16)   rl_nrtp = 3;
			else if (timing->lpddr5_rl_tck == 20)   rl_nrtp = 4;
			else if (timing->lpddr5_rl_tck == 24)   rl_nrtp = 5;
			else                                    SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
		} else if (set == 1) {
			     if (timing->lpddr5_rl_tck == 6)    rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 10)   rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 13)   rl_nrtp = 2;
			else if (timing->lpddr5_rl_tck == 16)   rl_nrtp = 3;
			else if (timing->lpddr5_rl_tck == 20)   rl_nrtp = 4;
			else if (timing->lpddr5_rl_tck == 24)   rl_nrtp = 5;
			else                                    SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
		} else if (set == 2) {
			     if (timing->lpddr5_rl_tck == 6)    rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 10)   rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 14)   rl_nrtp = 2;
			else if (timing->lpddr5_rl_tck == 20)   rl_nrtp = 3;
			else if (timing->lpddr5_rl_tck == 24)   rl_nrtp = 4;
			else if (timing->lpddr5_rl_tck == 28)   rl_nrtp = 5;
			else                                    SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
		} else {
			SNPS_ERROR("eDVFSC: Setting not yet supported", NULL);
			dwc_ddrctl_cinit_exit(1);
		}
	} else if (dvfsc_type == 2 && (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_WCK_CK_4_1)) {
        // JESD209-5C, Table 227 — Read Latencies for Read Link ECC off case (DVFSC disabled and Enhanced DVFS enabled)
        uint8_t set = !is_x16_val + read_dbi;
		if (set == 0 || set == 1) { 
			     if (timing->lpddr5_rl_tck == 3)    rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 5)    rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 7)    rl_nrtp = 2;
			else if (timing->lpddr5_rl_tck == 8)    rl_nrtp = 3;
			else if (timing->lpddr5_rl_tck == 10)   rl_nrtp = 4;
			else if (timing->lpddr5_rl_tck == 12)   rl_nrtp = 5;
			else                                    SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
		} else if (set == 2) {
			     if (timing->lpddr5_rl_tck == 3)    rl_nrtp = 0;
			else if (timing->lpddr5_rl_tck == 5)    rl_nrtp = 1;
			else if (timing->lpddr5_rl_tck == 7)    rl_nrtp = 2;
			else if (timing->lpddr5_rl_tck == 10)   rl_nrtp = 3;
			else if (timing->lpddr5_rl_tck == 12)   rl_nrtp = 4;
			else if (timing->lpddr5_rl_tck == 14)   rl_nrtp = 5;
			else                                    SNPS_ERROR("Default case for rl_nrtp should not be reached", NULL);
		} else {
			SNPS_ERROR("eDVFSC: Setting not yet supported", NULL);
			dwc_ddrctl_cinit_exit(1);
		}
	} else {
		SNPS_ERROR("Setting not yet supported", NULL);
        dwc_ddrctl_cinit_exit(1);
	}
	hdlr->memCtrlr_m.lpddr5_mr[p].mr2.rl_nrtp = rl_nrtp;
	SNPS_LOG("mr2.rl_nrtp = %u", hdlr->memCtrlr_m.lpddr5_mr[p].mr2.rl_nrtp);
#endif /* MEMC_LPDDR4 */
    SNPS_TRACE("Leaving");
}

/** @brief function to pre-calculate DFI timings such as dfi_t_rddata_en
 * and dfi_tphy_wrlat.
 * @note Only supports ddrPhyType_m = DWC_LPDDR4X_MULTIPHY
 */
void cinit_cal_lpddr4x_multiphy_dfi_timings(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch)
{
#ifdef DDRCTL_LPDDR
    uint32_t dfi_rl_sub;
    uint32_t dfi_wl_sub;
    uint32_t trddata_en_pipe, tphy_wrlat_pipe;
    uint32_t dfi_t_rddata_en_int, dfi_tphy_wrlat_int;

    // values here come from DWC LPDDR4 multiPHY V2 databook.
    dfi_rl_sub = 5;
    dfi_wl_sub = 5;

    trddata_en_pipe = 2 * (hdlr->phy_timing_params.pipe_dfi_misc - hdlr->phy_timing_params.pipe_dfi_rd);
    tphy_wrlat_pipe = 2 * (hdlr->phy_timing_params.pipe_dfi_misc - hdlr->phy_timing_params.pipe_dfi_wr);

    dfi_t_rddata_en_int = PRE_CFG.cl[p] + SPD.tAL - dfi_rl_sub;
    dfi_tphy_wrlat_int = PRE_CFG.cwl_x[p] + SPD.tAL - dfi_wl_sub;

    if (IS_LPDDR4) {
        if (hdlr->memCtrlr_m.lpddr4_mr[p].mr3.read_dbi == 1) {
            PRE_CFG.dfi_t_rddata_en[p][ch] = dfi_t_rddata_en_int - (PRE_CFG.cl[p] - PRE_CFG.cl_dbi[p]) + trddata_en_pipe;
        } else {
            PRE_CFG.dfi_t_rddata_en[p][ch] = dfi_t_rddata_en_int + trddata_en_pipe;
        }
        PRE_CFG.dfi_tphy_wrlat[p][ch] = dfi_tphy_wrlat_int + tphy_wrlat_pipe + 1;
    }

    // Specific to PHY Type 6,7,8
    PRE_CFG.dfi_t_dram_clk_disable[p][ch] = 5 + (2 * hdlr->phy_timing_params.pipe_dfi_misc) - 2;
    PRE_CFG.dfi_t_dram_clk_enable[p][ch] = 5 + (2 * hdlr->phy_timing_params.pipe_dfi_misc);
#endif
}

#ifdef DDRCTL_DDR
/* EXT is the setting of csrExtendPhdTime.
 * would have the value 2 for ddr5 if refer to c code in dwc_ddrphy_phyinit_progCsrSkipTrain
 *
 *if (memCK_freq >=  800) { DllGainIV = 0x03; DllGainTV = 0x05; wdExtendPhdTime = 0x01;}
 *if (memCK_freq >= 1200) { DllGainIV = 0x03; DllGainTV = 0x05; wdExtendPhdTime = 0x02;}
 *if (memCK_freq >= 1800) { DllGainIV = 0x03; DllGainTV = 0x06; wdExtendPhdTime = 0x02;}
 *if (memCK_freq >= 2200) { DllGainIV = 0x03; DllGainTV = 0x07; wdExtendPhdTime = 0x02;}
 *if (memCK_freq >= 2400) { DllGainIV = 0x04; DllGainTV = 0x07; wdExtendPhdTime = 0x02;}
 */

/** @brief emulated method for EXT value used in dfi_t_ctrlup_max calculation.
 * @note actual value for EXT is training dependent.
 */
uint32_t dwc_ddrctl_cinit_cal_ddr54_ext(SubsysHdlr_t *hdlr, uint32_t p)
{
    SNPS_TRACE("Entering");
    uint32_t ext = 3;
    SNPS_TRACE("Exiting");
    return ext;
}
#endif /* DDRCTL_DDR */

/** @brief method to calculate rd_min_gap based on ddr5 mr8 read pre/post_ample setting */
uint32_t cinit_cal_ddr5_rd_min_gap(SubsysHdlr_t *hdlr)
{
    SNPS_TRACE("Entering");
    uint32_t rd_min_gap = 0;
#ifdef DDRCTL_DDR
    ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[0];
    uint32_t t_rd_preamble, t_rd_postample;

    if (mregs->mr8.rd_preamble == 0)
        t_rd_preamble = 1;
    else if (RANGE(mregs->mr8.rd_preamble, 1, 2))
        t_rd_preamble = 2;
    else if (mregs->mr8.rd_preamble == 3)
        t_rd_preamble = 3;
    else if (mregs->mr8.rd_preamble == 4)
        t_rd_preamble = 4;
    else {
        SNPS_ERROR("Illegal mr8.rd_preamble value %u passed in configuration!", mregs->mr8.rd_preamble);
        dwc_ddrctl_cinit_exit(1);
    }

    switch (mregs->mr8.rd_postamble) {
    case 0:
        t_rd_postample = 1;
        break;
    case 1:
        t_rd_postample = 2;
        break;
    default:
        SNPS_ERROR("Illegal mr8.rd_postamble value %u passed in configuration!", mregs->mr8.rd_postamble);
        dwc_ddrctl_cinit_exit(1);
        break;
    }
    rd_min_gap = t_rd_preamble + t_rd_postample;

#endif /* DDRCTL_DDR */
    SNPS_TRACE("Leaving");
    return rd_min_gap;
}

/** @brief method to calculate wr_min_gap based on ddr5 mr8 write pre/post_ample setting */
uint32_t cinit_cal_ddr5_wr_min_gap(SubsysHdlr_t *hdlr)
{
    SNPS_TRACE("Entering");
    uint32_t wr_min_gap = 0;
#ifdef DDRCTL_DDR
    ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[0];
    uint32_t t_wr_postample;
    uint32_t t_wr_preamble = cinit_get_ddr5_twpre(hdlr, 0);

    switch (mregs->mr8.wr_postamble) {
    case 0:
        t_wr_postample = 1;
        break;
    case 1:
        t_wr_postample = 2;
        break;
    default:
        SNPS_ERROR("Illegal mr8.wr_postamble value %u passed in configuration!", mregs->mr8.wr_postamble);
        dwc_ddrctl_cinit_exit(1);
        break;
    }
    wr_min_gap = t_wr_preamble + t_wr_postample;

#endif /* MEMC_DDR5 */
    SNPS_TRACE("Leaving");
    return wr_min_gap;
}

/** @brief method to get twpre bsed on ddr5 mr8 write preamble setting */
uint32_t cinit_get_ddr5_twpre(SubsysHdlr_t *hdlr, uint32_t p)
{
    SNPS_TRACE("Entering");
    uint8_t t_wr_preamble = 0;
#ifdef DDRCTL_DDR
    ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[p];

    switch (mregs->mr8.wr_preamble) {
    case 1:
        t_wr_preamble = 2;
        break;
    case 2:
        t_wr_preamble = 3;
        break;
    case 3:
        t_wr_preamble = 4;
        break;
    default:
        SNPS_ERROR("Illegal mr8.wr_preamble value %u passed in configuration!", mregs->mr8.wr_preamble);
        dwc_ddrctl_cinit_exit(1);
        break;
    }
#endif
    SNPS_TRACE("Leaving");
    return t_wr_preamble;
}

/** @brief method to get twpre bsed on ddr5 mr40 read DQS offset setting */
uint32_t cinit_get_ddr5_t_rd_dqs_offset(SubsysHdlr_t *hdlr, uint32_t p)
{
    SNPS_TRACE("Entering");
    uint8_t t_rd_dqs_offset = 0;
#ifdef DDRCTL_DDR
    ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[p];

    switch (mregs->mr40.rd_dqs_offset) {
    case 0:
        t_rd_dqs_offset = 0;
        break;
    case 1:
        t_rd_dqs_offset = 1;
        break;
    case 2:
        t_rd_dqs_offset = 2;
        break;
    case 3:
        t_rd_dqs_offset = 3;
        break;
    default:
        SNPS_ERROR("Illegal mr4.rd_dqs_offset value %u passed in configuration!", mregs->mr40.rd_dqs_offset);
        dwc_ddrctl_cinit_exit(1);
        break;
    }
#endif
    SNPS_TRACE("Leaving");
    return t_rd_dqs_offset;
}

/** @brief method to encode ddr5 tRTP latency */
void cinit_encode_ddr5_trtp_latency(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch)
{
    SNPS_TRACE("Entering");
#ifdef DDRCTL_DDR
    ddr5_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr5_mr[p];
    uint32_t t_rtp = PRE_CFG.t_rtp[p][dch];

    SNPS_LOG("t_rtp = %u ", t_rtp);

    if (t_rtp == 13 || t_rtp == 16 || t_rtp == 19 || t_rtp == 22)
        t_rtp++;
    switch (t_rtp) {
    case 12:
        mregs->mr6.trtp = 0;
        break;
    case 14:
        mregs->mr6.trtp = 1;
        break;
    case 15:
        mregs->mr6.trtp = 2;
        break;
    case 17:
        mregs->mr6.trtp = 3;
        break;
    case 18:
        mregs->mr6.trtp = 4;
        break;
    case 20:
        mregs->mr6.trtp = 5;
        break;
    case 21:
        mregs->mr6.trtp = 6;
        break;
    case 23:
        mregs->mr6.trtp = 7;
        break;
    case 24:
    case 25: // At 6400 VIP seems to RD(7500/tck)
        mregs->mr6.trtp = 8;
        break;
    // trtp number aligned to VIP version T-2022.06-2 for speedbin higher than 6400
    case 26:
        mregs->mr6.trtp = 9;
        break;
    case 27:
        mregs->mr6.trtp = 10;
        break;
    case 29:
        mregs->mr6.trtp = 11;
        break;
    case 30:
        mregs->mr6.trtp = 12;
        break;
    case 32:
        mregs->mr6.trtp = 13;
        break;
    case 33:
        mregs->mr6.trtp = 14;
        break;
    default:
        SNPS_ERROR("Illegal mr6.trtp value %u passed in configuration!", t_rtp);
        dwc_ddrctl_cinit_exit(1);
        break;
    }
    SNPS_LOG("mr6.trtp[%u] = %u ", p, mregs->mr6.trtp);
#endif
    SNPS_TRACE("Leaving");
}

#ifdef DDRCTL_DDR
/** @brief map system requirements for DDR5 maintanence commands to PASCTL8
 * The method maps the higher system requirements to PAS implementation registers which control
 * the microcode in PAS_DU block.
 */
void cinit_pasctl(SubsysHdlr_t *hdlr, uint32_t dch)
{
    SNPS_TRACE("Entering");
    ddr5_pasdu_en_t *pasdu_en = &hdlr->ddr5_pasdu_en;
    uint32_t rank;

    // TCR and DQS OSC
    for (uint32_t ii = 0; ii < SPD.num_ranks; ii = ii + 1) {
        // Expected the DU rank activities should be enabled for rank 0 and rank 2 for 2 DIMM, single rank per DIMM case
        if (SPD.num_ranks_per_dimm == 1 && SPD.num_ranks == 2 && ii == 1)
            rank = ii + 1;
        else
            rank = ii;

        if (pasdu_en->tcr_dqsosc_en[dch][rank] == 1) {
            switch (rank) {
            case 0: // rank 0
                DYN.rank_blk1_en[dch] = 1;
                DYN.rank_blk5_en[dch] = 1;
                break;
            case 1: // rank 1
                DYN.rank_blk9_en[dch] = 1;
                DYN.rank_blk13_en[dch] = 1;
                break;
            case 2: // rank 2
                DYN.rank_blk17_en[dch] = 1;
                DYN.rank_blk21_en[dch] = 1;
                break;
            case 3: // rank 3
                DYN.rank_blk25_en[dch] = 1;
                DYN.rank_blk29_en[dch] = 1;
                break;
            }
        }
    }
    // HW ZQCAL
    if (pasdu_en->all_rank_zqcal_en[dch] == 1) {
        // ALL RANKS
        DYN.glb_blk0_en[dch] = 1;
        DYN.glb_blk4_en[dch] = 1;
    } else {
        // PER RANK
        for (uint32_t ii = 0; ii < SPD.num_ranks; ii = ii + 1) {
            // Expected the DU rank activities should be enabled for rank 0 and rank 2 for 2 DIMM, single rank per DIMM case
            if (SPD.num_ranks_per_dimm == 1 && SPD.num_ranks == 2 && ii == 1)
                rank = ii + 1;
            else
                rank = ii;

            if (pasdu_en->per_rank_zqcal_en[dch][rank] == 1) {
                switch (rank) {
                case 0: // rank 0
                    DYN.rank_blk0_en[dch] = 1;    // ZQCAL start
                    DYN.rank_blk4_en[dch] = 1;    // ZQCAL latch
                    break;
                case 1: // rank 1
                    DYN.rank_blk8_en[dch] = 1;    // ZQCAL start
                    DYN.rank_blk12_en[dch] = 1;    // ZQCAL latch
                    break;
                case 2: // rank 2
                    DYN.rank_blk16_en[dch] = 1;    // ZQCAL start
                    DYN.rank_blk20_en[dch] = 1;    // ZQCAL latch
                    break;
                case 3: // rank 3
                    DYN.rank_blk24_en[dch] = 1;    // ZQCAL start
                    DYN.rank_blk28_en[dch] = 1;    // ZQCAL latch
                    break;
                }
            }
        }
    }
    // CTLUPD
    if (pasdu_en->ctlupd_en[dch] == 1)
        DYN.glb_blk1_en[dch] = 1;

    // ECS
    for (uint32_t ii = 0; ii < SPD.num_ranks; ii = ii + 1) {
        // Expected the DU rank activities should be enabled for rank 0 and rank 2 for 2 DIMM, single rank per DIMM case
        if (SPD.num_ranks_per_dimm == 1 && SPD.num_ranks == 2 && ii == 1)
            rank = ii + 1;
        else
            rank = ii;

        if (pasdu_en->per_rank_ecs_en[dch][rank] == 1) {
            switch (rank) {
            case 0: // rank 0
                DYN.rank_blk6_en[dch] = 1;
                break;
            case 1: // rank 1
                DYN.rank_blk14_en[dch] = 1;
                break;
            case 2: // rank 2
                DYN.rank_blk22_en[dch] = 1;
                break;
            case 3: // rank 3
                DYN.rank_blk30_en[dch] = 1;
                break;
            }
        }
    }
    SNPS_TRACE("Leaving");
}

#endif /* DDRCTL_DDR */

#ifdef DDRCTL_DDR

/**
 * @brief Do some pre-calculations before cinit_prgm_regs is called
 * related to mrr_des1/mrr_des2 and mrr_des_timing_unii_sel
 * Loops thou all pstates as timings are only per channel only
 * so need to choose the maximum case for all freq/pstates within a
 * channel
 */
void cinit_pre_cfg_mrr_des(SubsysHdlr_t *hdlr, uint32_t ch, uint32_t total_num_pstates)
{
	uint32_t tck_ps;
	uint32_t mrr_des_freq_ratio;
	uint32_t mrr_des_rank_switch_gap_unit_sel;
	uint32_t mrr_des_wr_bl_div2;
	uint32_t mrr_des_rd_bl_div2;
	uint32_t mrr_des_max_t_wr2rd_gap;
	uint32_t mrr_des_max_t_rd2wr_gap;
	uint32_t mrr_des_max_t_rd2rd_gap;
	uint32_t mrr_des_db_rl_r;
	uint32_t mrr_des_t_pdm_rd;
	uint32_t mrr_des_tmrrod1_sel;
	uint32_t mrr_des_eqn_A;
	uint32_t mrr_des_eqn_B;
	uint32_t mrr_des_eqn_C;
	uint32_t mrr_des_eqn_D;
	uint32_t mrr_des_max_eqn_AorB;
	uint32_t mrr_des_max_eqn_BorC;
	uint32_t mrr_des_max_eqn_BorCorD;
	uint32_t mrr_des2_tmrd;
	uint32_t mrr_des_timing_unit_sel;
	uint32_t mrr_des_timing_unit;
	uint32_t ci_mrr_des1_stored;
	uint32_t ci_mrr_des1_int;
	uint32_t ci_mrr_des2_stored;
	uint32_t ci_mrr_des2_int;
	ddrTimingParameters_t *timing;

	SNPS_TRACE("Entering");

	// initialize before loop through pstates(p)
	ci_mrr_des1_stored = 0;
	ci_mrr_des2_stored = 0;

	// loops thorugh for all pstates and keeps track of largest
        // value (can be >=16) in:
        // - ci_mrr_des1_stored
        // - ci_mrr_des2_stored
	for (uint32_t p = 0; p < total_num_pstates; p++) {
		timing = &hdlr->timingParams_m[p][0]; // uses timingParams_m[p][0]
		tck_ps = SPD.tck_ps[p];

		// setting of:
		// - mrr_des_timing_unit_sel
		// - mrr_des1
		// - mrr_des2
		// eqnA = ( (max(t_wr2rd_gap*)<<rank_switch_gap_unit_sel) + WR_BL/2 + FREQ_RATIO - 1 ) / FREQ_RATIO
		// eqnB = ( (max(t_rd2wr_gap*)<<rank_switch_gap_unit_sel) + RD_BL/2 + FREQ_RATIO - 1 ) / FREQ_RATIO
		// eqnC = ( (max(t_rd2rd_gap*)<<rank_switch_gap_unit_sel)     + RD_BL/2 + FREQ_RATIO - 1 ) / FREQ_RATIO
		// eqnD = ( (DB_RL + tPDM_RD + tMRR(2N)OD1)                   + RD_BL/2 + FREQ_RATIO - 1 ) / FREQ_RATIO
		// Note, eqn_D only applies for LRDIMM, so is 0 otherwise
		if (IS_DDR5) {
			mrr_des_freq_ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
			mrr_des_rank_switch_gap_unit_sel = QDYN.rank_switch_gap_unit_sel[ch];

			mrr_des_wr_bl_div2 = DIV_2(timing->burst_length) + QDYN.wr_crc_enable;
			mrr_des_rd_bl_div2 = DIV_2(timing->burst_length) + QDYN.rd_crc_enable;
            mrr_des2_tmrd = CEIL(timing->ddr5_tmrd_tck, mrr_des_freq_ratio);

			if (IS_LRDIMM) {
				mrr_des_db_rl_r         = PRE_CFG.cl[p] + QDYN.rd_crc_enable;
				mrr_des_t_pdm_rd        = CEIL(timing->ddr5_rcd_tpdm_rd_ps,tck_ps);
				mrr_des_tmrrod1_sel     = (hdlr->memCtrlr_m.ddr5_mr[p].mr2.ddr5_2n_mode==0) ? timing->ddr5_db_tmrr2nod1_tck : timing->ddr5_db_tmrrod1_tck;
			} else {
				mrr_des_db_rl_r         = 0;
				mrr_des_t_pdm_rd        = 0;
				mrr_des_tmrrod1_sel     = 0;
			}


			mrr_des_max_t_wr2rd_gap = max(QDYN.t_wr2rd_gap_r0r1[p][ch], QDYN.t_wr2rd_gap_r1r0[p][ch]);
			mrr_des_max_t_rd2wr_gap = max(QDYN.t_rd2wr_gap_r0r1[p][ch], QDYN.t_rd2wr_gap_r1r0[p][ch]);
			mrr_des_max_t_rd2rd_gap = max(QDYN.t_rd2rd_gap_r0r1[p][ch], QDYN.t_rd2rd_gap_r1r0[p][ch]);

			if ((STATIC.active_ranks==0xf) || (STATIC.active_ranks==0x5)) {
				mrr_des_max_t_wr2rd_gap = max(QDYN.t_wr2rd_gap_r0r2[p][ch], mrr_des_max_t_wr2rd_gap);
				mrr_des_max_t_wr2rd_gap = max(QDYN.t_wr2rd_gap_r2r0[p][ch], mrr_des_max_t_wr2rd_gap);

				mrr_des_max_t_rd2wr_gap = max(QDYN.t_rd2wr_gap_r0r2[p][ch], mrr_des_max_t_rd2wr_gap);
				mrr_des_max_t_rd2wr_gap = max(QDYN.t_rd2wr_gap_r2r0[p][ch], mrr_des_max_t_rd2wr_gap);

				mrr_des_max_t_rd2rd_gap = max(QDYN.t_rd2rd_gap_r0r2[p][ch], mrr_des_max_t_rd2rd_gap);
				mrr_des_max_t_rd2rd_gap = max(QDYN.t_rd2rd_gap_r2r0[p][ch], mrr_des_max_t_rd2rd_gap);

				// now check if r2 applies or not
				// (does not apply for active_ranks=0x5)
				if (STATIC.active_ranks==0xf) {
					mrr_des_max_t_wr2rd_gap = max(QDYN.t_wr2rd_gap_r1r2[p][ch], mrr_des_max_t_wr2rd_gap);
					mrr_des_max_t_wr2rd_gap = max(QDYN.t_wr2rd_gap_r2r1[p][ch], mrr_des_max_t_wr2rd_gap);

					mrr_des_max_t_rd2wr_gap = max(QDYN.t_rd2wr_gap_r1r2[p][ch], mrr_des_max_t_rd2wr_gap);
					mrr_des_max_t_rd2wr_gap = max(QDYN.t_rd2wr_gap_r2r1[p][ch], mrr_des_max_t_rd2wr_gap);

					mrr_des_max_t_rd2rd_gap = max(QDYN.t_rd2rd_gap_r1r2[p][ch], mrr_des_max_t_rd2rd_gap);
					mrr_des_max_t_rd2rd_gap = max(QDYN.t_rd2rd_gap_r2r1[p][ch], mrr_des_max_t_rd2rd_gap);
				}
			}
			// now check for r3
			if (STATIC.active_ranks==0xf) {
				mrr_des_max_t_wr2rd_gap = max(QDYN.t_wr2rd_gap_r1r3[p][ch], mrr_des_max_t_wr2rd_gap);
				mrr_des_max_t_wr2rd_gap = max(QDYN.t_wr2rd_gap_r3r1[p][ch], mrr_des_max_t_wr2rd_gap);
				mrr_des_max_t_wr2rd_gap = max(QDYN.t_wr2rd_gap_r2r3[p][ch], mrr_des_max_t_wr2rd_gap);
				mrr_des_max_t_wr2rd_gap = max(QDYN.t_wr2rd_gap_r3r2[p][ch], mrr_des_max_t_wr2rd_gap);

				mrr_des_max_t_rd2wr_gap = max(QDYN.t_rd2wr_gap_r1r3[p][ch], mrr_des_max_t_rd2wr_gap);
				mrr_des_max_t_rd2wr_gap = max(QDYN.t_rd2wr_gap_r3r1[p][ch], mrr_des_max_t_rd2wr_gap);
				mrr_des_max_t_rd2wr_gap = max(QDYN.t_rd2wr_gap_r2r3[p][ch], mrr_des_max_t_rd2wr_gap);
				mrr_des_max_t_rd2wr_gap = max(QDYN.t_rd2wr_gap_r3r2[p][ch], mrr_des_max_t_rd2wr_gap);

				mrr_des_max_t_rd2rd_gap = max(QDYN.t_rd2rd_gap_r1r3[p][ch], mrr_des_max_t_rd2rd_gap);
				mrr_des_max_t_rd2rd_gap = max(QDYN.t_rd2rd_gap_r3r1[p][ch], mrr_des_max_t_rd2rd_gap);
				mrr_des_max_t_rd2rd_gap = max(QDYN.t_rd2rd_gap_r2r3[p][ch], mrr_des_max_t_rd2rd_gap);
				mrr_des_max_t_rd2rd_gap = max(QDYN.t_rd2rd_gap_r3r2[p][ch], mrr_des_max_t_rd2rd_gap);

			}

			mrr_des_eqn_A = (
                                 (mrr_des_max_t_wr2rd_gap<<mrr_des_rank_switch_gap_unit_sel)
                                 + mrr_des_wr_bl_div2
                                 + mrr_des_freq_ratio
                                 - 1
                                 )
                                 / mrr_des_freq_ratio;
			mrr_des_eqn_B = (
                                 (mrr_des_max_t_rd2wr_gap<<mrr_des_rank_switch_gap_unit_sel)
                                 + mrr_des_rd_bl_div2
                                 + mrr_des_freq_ratio
                                 - 1
                                 )
                                 / mrr_des_freq_ratio;
			mrr_des_eqn_C = (
                                 (mrr_des_max_t_rd2rd_gap<<mrr_des_rank_switch_gap_unit_sel)

                                 + mrr_des_rd_bl_div2
                                 + mrr_des_freq_ratio
                                 - 1
                                 )
                                 / mrr_des_freq_ratio;

			mrr_des_eqn_D =  (
                                 (mrr_des_db_rl_r + mrr_des_t_pdm_rd + mrr_des_tmrrod1_sel)

                                 + mrr_des_rd_bl_div2
                                 + mrr_des_freq_ratio
                                 - 1
                                 )
                                 / mrr_des_freq_ratio;


			mrr_des_max_eqn_AorB = max(mrr_des_eqn_A, mrr_des_eqn_B);
			mrr_des_max_eqn_BorC = max(mrr_des_eqn_B, mrr_des_eqn_C);
			mrr_des_max_eqn_BorCorD = max(mrr_des_max_eqn_BorC, mrr_des_eqn_D);

			ci_mrr_des1_int = mrr_des_max_eqn_AorB;
			ci_mrr_des2_int = max(mrr_des_max_eqn_BorCorD, mrr_des2_tmrd);
		} else {
		// DDR4
			ci_mrr_des1_int = 0;
			ci_mrr_des2_int = 0;
		} // DDR5/DDR4


		// at end of pstate(p) loop, check if calculated value is higher
		// than stored value
		// then update stored value,
		// otherwise, do nothing, stored value stays the same
		// do this for both:
		// - ci_mrr_des1_stored
		// - ci_mrr_des2_stored
		if (ci_mrr_des1_int>ci_mrr_des1_stored) {
			ci_mrr_des1_stored = ci_mrr_des1_int;
		} else {
                        // do nothing, stored value does not change
		}


		if (ci_mrr_des2_int>ci_mrr_des2_stored) {
			ci_mrr_des2_stored = ci_mrr_des2_int;
		} else {
			// do nothing, stored value does not change
		}

	} // end of pstate(p) for loop

	// at end of all pstates, largest value of
        // ci_mrr_des1_stored
        // ci_mrr_des2_stored
        // is found, and can be >=16, even though registers are only 4 bits
	// if relevant eqns are >31 -> mrr_des_timing_unit_sel=2 is needed
	// if relevant eqns are >16 -> mrr_des_timing_unit_sel=1 is needed
	// else                     -> mrr_des_timing_unit_sel=0 is needed
	if ((ci_mrr_des1_stored>=31) || (ci_mrr_des2_stored>=31)) {
		mrr_des_timing_unit_sel = 2;
        mrr_des_timing_unit = 4;
	} else if ((ci_mrr_des1_stored>=16) || (ci_mrr_des2_stored>=16)) {
		mrr_des_timing_unit_sel = 1;
        mrr_des_timing_unit = 2;
	} else {
		mrr_des_timing_unit_sel = 0;
        mrr_des_timing_unit = 1;
	}

	PRE_CFG.mrr_des_timing_unit_sel[ch] = mrr_des_timing_unit_sel;
	PRE_CFG.ci_mrr_des1[ch]             = CEIL(ci_mrr_des1_stored, mrr_des_timing_unit);
	PRE_CFG.ci_mrr_des2[ch]             = CEIL(ci_mrr_des2_stored, mrr_des_timing_unit);

	SNPS_TRACE("Leaving");
}

#endif // DDRCTL_DDR

#ifdef DDRCTL_WR_CRC_RETRY
static void cinit_cal_retry_window(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
  uint32_t n_cmd_dly;
  uint32_t tpdm_rcd;
  uint32_t talert_rcd;
  uint32_t n_cmd_dly_ras_model;
  uint32_t wl = 0;
  uint32_t tcrc_alert;
  uint32_t tinternal_delay_wr_crc;

  uint32_t ratio;
  uint32_t tck_ps = SPD.tck_ps[p];
  uint32_t tphy_rdlat_min;
  uint32_t talert_latency_sync;
  uint32_t talert_latency_async;
  uint32_t talert_latency;
#ifdef CINIT_DDR5
  uint32_t todt_extra_ddr5;
#endif
  uint8_t latency_synchronizer_async;
  uint8_t latency_synchronizer;
  uint8_t tinternal_delay_min;
  uint8_t tinternal_delay_extra;
  uint8_t tinternal_delay;
  uint8_t l_retry_add_rd_lat;
  uint8_t l_rd_path_delay_tck;
  uint8_t bl_div2;
  ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];

  ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
#ifdef DDRCTL_CAPAR_RETRY
  // 3-BL16 worth of dfi_rddata beats could be corrupted
  PRE_CFG.extra_rd_retry_window[p][ch] = 48 / 2 / ratio;
#endif

  // tphy_rdlat(min) : temporary value TODO
  tphy_rdlat_min = 10 * ratio;
  // alert_latency_sync is from PHY:
  // DDR5/4 PHY:
  //   DFI 1:2 : talert_latency_sync = 15 + DFIMISC)
  //   DFI 1:4 : talert_latency_sync = 0.5 * (15 + DFIMISC) + 1
  // DDR5 PHY: 16. Unit is DFI clock
#ifdef DDR5_PHY
  talert_latency_sync = 16;
#else
    talert_latency_sync = 15 + hdlr->phy_timing_params.pipe_dfi_misc;
    if (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_1_4) {
        talert_latency_sync = DIV_2(talert_latency_sync) + 1;
    }

#endif
  SNPS_LOG("talert_latency_sync=%u", talert_latency_sync);
  // PHY has 0 latency in async_mode=1 (synchronizer delay is handled by latency_synchronizer_async)
  talert_latency_async = 0;
  SNPS_LOG("talert_latency_async=%u", talert_latency_async);

  // select between async and sync for talert_latency based on
  // dfi_alert_async_mode
  talert_latency = (STATIC.dfi_alert_async_mode) ? talert_latency_async : talert_latency_sync;
  SNPS_LOG("talert_latency=%u", talert_latency);

  // dwc_ddrphy_alert_async_n is async so has no latency itself
  // Set to bcm21 depth + 1 (for missampling)
  latency_synchronizer_async = UMCTL2_ASYNC_DDRC_N_SYNC + 1;
  SNPS_LOG("UMCTL2_ASYNC_DDRC_N_SYNC=%u, talert_latency_async=%u", UMCTL2_ASYNC_DDRC_N_SYNC, talert_latency_async);

  // apply synchronizer latency only if async_mode=1
  latency_synchronizer = (STATIC.dfi_alert_async_mode) ? latency_synchronizer_async : 0;
  SNPS_LOG("latency_synchronizer=%u", latency_synchronizer);

  // tinternal_delay_min : value from SIM
  tinternal_delay_min = 7;

  // random factor passed from higher level
  tinternal_delay_extra = hdlr->capar_retry_window_internal_delay_extra;

  // total tinternal_delay
  tinternal_delay = tinternal_delay_min + tinternal_delay_extra;

  SNPS_LOG("tinternal_delay_min=%u,capar_retry_window_internal_delay_extra=%u,tinternal_delay_extra=%u", tinternal_delay_min, hdlr->capar_retry_window_internal_delay_extra, tinternal_delay_extra);
  SNPS_LOG("tinternal_delay=%u", tinternal_delay);
  cinit_cal_ddr54_pre_cfg_timing_1st_set(hdlr, p, ch, n);

#ifdef DDRCTL_CAPAR_RETRY
#ifdef CINIT_DDR5
  if (IS_DDR5) {
      // max (ODTLon_WL_offset) +  1 tCK RTT_PARK + max (ODTLoff_WL_offset) =  3 tCK + 1 + 3 tCK = 7 tCK
      todt_extra_ddr5 = 7;

      // tctrl_delay + 4 + talert_latency + internal delay + latency_synchronizer
      // talert_latency : gotten from PHY
      // value of internal delay incl randomization factor
      // latency_synchronizer (if PHY is in asynchronous mode
      // todt_extra_ddr5 - max (ODTLon_WL_offset) +  1 tCK RTT_PARK + max (ODTLoff_WL_offset)
      PRE_CFG.capar_retry_window[p][ch] = CEIL((QDYN.dfi_t_ctrl_delay[p][ch] + 4), ratio) + talert_latency + tinternal_delay + latency_synchronizer + todt_extra_ddr5 + DYN.t_wr_crc_alert_pw_min[p][ch] / ratio;
    }
#endif /* CINIT_DDR5 */
#ifdef CINIT_DDR4
  if (IS_DDR4) {
      if (IS_RDIMM || IS_LRDIMM) {
          // tctrl_delay + tPDM + tPAR_ALERT_UNKNOWN + tPAR_ALERT_ON +
          // talert_latency + internal delay + latency_synchronizer
          // tPDM : 1.67ns + tCK/4
          // tPAR_ALERT_UNKNOWN : PL
          // tPAR_ALERT_ON : PL + 6ns
          // talert_latency : gotten from PHY
          // value of internal delay incl randomization factor
          // latency_synchronizer (if PHY is in asynchronous mode)
          PRE_CFG.capar_retry_window[p][ch] = CEIL((QDYN.dfi_t_ctrl_delay[p][ch] + cinit_ps_to_tck(1670 + DIV_4(tck_ps), tck_ps) + timing->ddr4_tpl_tck + timing->ddr4_tpl_tck + cinit_ps_to_tck(6000, tck_ps)), ratio) + talert_latency + tinternal_delay + latency_synchronizer + DYN.t_wr_crc_alert_pw_min[p][ch] / ratio;
      } else {
          // tctrl_delay + tPAR_ALERT_UNKNOWN + tPAR_ALERT_ON + talert_latency + internal delay + latency_synchronizer (if PHY is in asynchronous mode)
          PRE_CFG.capar_retry_window[p][ch] = CEIL((QDYN.dfi_t_ctrl_delay[p][ch] + timing->ddr4_tpl_tck + timing->ddr4_tpl_tck + cinit_ps_to_tck(6000, tck_ps)), ratio) + talert_latency + tinternal_delay + latency_synchronizer + DYN.t_wr_crc_alert_pw_min[p][ch] / ratio;
      }
  }
#endif /* CINIT_DDR4 */

  //SNPS_LOG("capar_retry_window=%u, extra_rd_retry_window=%u", PRE_CFG.capar_retry_window[p][ch], PRE_CFG.extra_rd_retry_window[p][ch]);
  //SNPS_LOG("Ceil(dfi_t_rddata_en+tphy_rdlat_min, ratio)=%u", CEIL((PRE_CFG.dfi_t_rddata_en[p][ch] + tphy_rdlat_min), ratio));

#ifdef DDRCTL_EXT_SBECC_AND_CRC
  SNPS_LOG("rd_path_delay of RAS model=%u", hdlr->rd_path_delay);
  //SNPS_LOG("ratio                 =%u", ratio);
  l_rd_path_delay_tck = hdlr->rd_path_delay;
#else
  l_rd_path_delay_tck = 0;
#endif
  //SNPS_LOG("l_rd_path_delay_tck=%u", l_rd_path_delay_tck);

  // trddata_en + tphy_rdlat + rd_path_delay < PHY's unguaranteed period + capar_retry_window
  if ((CEIL((PRE_CFG.dfi_t_rddata_en[p][ch] + tphy_rdlat_min), ratio) + l_rd_path_delay_tck) > (PRE_CFG.extra_rd_retry_window[p][ch] + PRE_CFG.capar_retry_window[p][ch])) {
      PRE_CFG.retry_add_rd_lat_en[p][ch] = 0;
      l_retry_add_rd_lat = 0;
  } else {
      PRE_CFG.retry_add_rd_lat_en[p][ch] = 1;
      l_retry_add_rd_lat = PRE_CFG.extra_rd_retry_window[p][ch] + PRE_CFG.capar_retry_window[p][ch] - CEIL((PRE_CFG.dfi_t_rddata_en[p][ch] + tphy_rdlat_min), ratio) - l_rd_path_delay_tck;
  }

  // check for overflow and set to max value supported
  if(DDRCTL_RETRY_MAX_ADD_RD_LAT > 0) {
      if (l_retry_add_rd_lat + 1 > DDRCTL_RETRY_MAX_ADD_RD_LAT) {
          SNPS_LOG("WARNING: l_retry_add_rd_lat=%u is too large for configured DDRCTL_RETRY_MAX_ADD_RD_LAT=%u due to tinternal_delay_extra=%u", l_retry_add_rd_lat, DDRCTL_RETRY_MAX_ADD_RD_LAT, tinternal_delay_extra);
          l_retry_add_rd_lat = DDRCTL_RETRY_MAX_ADD_RD_LAT - 1;
          SNPS_LOG("WARNING: Overriding to l_retry_add_rd_lat=%u, max supported value", l_retry_add_rd_lat);
      }

  } else {
      l_retry_add_rd_lat = 0;
  }

  PRE_CFG.retry_add_rd_lat[p][ch] = l_retry_add_rd_lat;

#endif /* DDRCTL_CAPAR_RETRY */

  // Following is for the calculation of t_wr_crc_retry_window
  // 1. n_cmd_delay: command delay from internal scheduler to DFI interface. Unit is DFI clock.
  // ddr4: 2+MEMC_REG_DFI_OUT; ddr5: 1+MEMC_REG_DFI_OUT.
  n_cmd_dly =
#ifdef MEMC_REG_DFI_OUT
              MEMC_REG_DFI_OUT  +
#endif
              (IS_DDR5?1:2);
  SNPS_LOG("command delay = %u", n_cmd_dly);
  // 2. tctrl_delay. QDYN.dfi_t_ctrl_delay[p][ch]. Unit is DFI clock.

  // 3. talert_latency is from PHY. Unit is DFI clock.
  // same with vaue of capar_retry_window

  // 4. latency_synchronizer: UMCTL2_ASYNC_DDRC_SYNC+1. Unit is DFI clock.
  // same with vaue of capar_retry_window

  // 5.PCB routing delay(SI simulation resut(worst case))
  // unknown

  // 6. n_alert_dly_cpe: 1. Unit is DFI clock

  // 7. n_alert_dly_err: DYN.t_wr_crc_alert_pw_min. Unit is DFI PHY clock

  // 8. tPDM for DDR4/5 RCD. DDR4 RCD: 1.3ns; DDR5 1.25ns. Unit is DFI PHY clock.
  tpdm_rcd = (IS_RDIMM || IS_LRDIMM)? ((IS_DDR4) ? cinit_ps_to_tck(1300, tck_ps) : cinit_ps_to_tck(1250, tck_ps)): 0 ;
  SNPS_LOG("tpdm_rcd = %u", tpdm_rcd);

  // 9. talert for DDR4/5 RCD: 2ns. Unit is DFI PHY clock.
  talert_rcd = (IS_RDIMM || IS_LRDIMM)? (cinit_ps_to_tck(2000, tck_ps)): 0;
  SNPS_LOG("talert_rcd = %u", talert_rcd);

  // 10. WL. Unit is DFI PHY clock.
  if( IS_DDR4 ) {
    wl = cinit_cal_cwlx(hdlr, p, ch, 0) + timing->ddr4_tpl_tck + SPD.tAL; //CWL+AL+tPL
  }
  if( IS_DDR5 ) {
    wl = cinit_cal_cwlx(hdlr, p, ch, 0);// CWL
  }
  SNPS_LOG("wl = %u", wl);
  // 11. BL/2. Unit is DFI PHY clock.
  bl_div2 =  DIV_2(timing->burst_length);
  SNPS_LOG("bl_div2 = %u", bl_div2);

  // 12. tcrc_alert: max=13ns.  Unit is DFI PHY clock.
  tcrc_alert = cinit_ps_to_tck(13000, tck_ps);
  SNPS_LOG("tcrc_alert = %u", tcrc_alert);

  // 13. command delay of DFI RAS box. Unit is DFI clock.
#ifdef DDRCTL_EXT_SBECC_AND_CRC
  n_cmd_dly_ras_model = hdlr->dfi_ras_model_cmd_delay;
#else
  n_cmd_dly_ras_model = 0;
#endif
  SNPS_LOG("n_cmd_dly_ras_model = %u", n_cmd_dly_ras_model);
  // 14.extra delay for t_wr_crc_retry_window.
  tinternal_delay_wr_crc = hdlr-> wr_crc_retry_window_internal_delay_extra;
  SNPS_LOG("tinternal_delay_wr_crc = %u", tinternal_delay_wr_crc);

  // t_wr_crc_retry_window: Unit is DFI clock.
  PRE_CFG.t_wr_crc_retry_window[p][ch] = n_cmd_dly + QDYN.dfi_t_ctrl_delay[p][ch] + talert_latency + latency_synchronizer + 1 + n_cmd_dly_ras_model+ tinternal_delay_wr_crc
                                       + CEIL((DYN.t_wr_crc_alert_pw_min[p][ch] + tpdm_rcd + talert_rcd + wl + bl_div2 + tcrc_alert) , ratio);
  SNPS_LOG("t_wr_crc_retry_window = %u", PRE_CFG.t_wr_crc_retry_window[p][ch]);
}
#endif //DDRCTL_WR_CRC_RETRY

#ifdef DDRCTL_EXT_SBECC_AND_CRC
/** @brief function for calculating command delay and adjust tphy_wrlat&tphy_wrdata when ras model exists */
void cinit_cal_delay_for_ras_model(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n)
{
    SNPS_TRACE("Entering");
    uint32_t DFI_WL_SUB = 0, tphy_wrlat_pipe;
    uint32_t dfi_tphy_wrlat_int;
    uint32_t ratio;
    uint32_t ac_in_pipe, dx_in_pipe;
    uint32_t tck_ps = SPD.tck_ps[p];
    uint32_t freq_mhz = CEIL(1000000,tck_ps);

    ratio = ddrctl_sw_get_ratio_factor(hdlr, p);
#ifdef CINIT_DDR5
	if (IS_DDR5) {
      if (hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
        DFI_WL_SUB = 13;
	  } else {
#ifdef DWC_PUB_RID_GE330
		DFI_WL_SUB = 13;
#else /* DWC_PUB_RID_GE330 */
		DFI_WL_SUB = 9;
#endif /* DWC_PUB_RID_GE330 */
	  } 
    }
#endif /* CINIT_DDR5 */

	dfi_tphy_wrlat_int = PRE_CFG.cwl_x[p] + SPD.tAL - DFI_WL_SUB;	//for 2n mode, +1 (required by the PHY databook) has been considered by the controller RTL, there is no need to add one here

  if (hdlr->ddrPhyType_m == DWC_DDR5_PHY) { 
    #ifdef DWC_PHYINIT_RID_GE202211
    if (ratio==2) {
      if ((tck_ps>=312) && (tck_ps<476)) {
        dx_in_pipe = ratio*3;
        ac_in_pipe = ratio*1;
      } else {
        dx_in_pipe = ratio*1 ;
        ac_in_pipe = ratio*0;
      }
    } else {
      if ((tck_ps>=227) && (tck_ps<625)) {
        dx_in_pipe = ratio*1;
        ac_in_pipe = ratio*0;
      } else {
        dx_in_pipe = ratio*0;
        ac_in_pipe = ratio*0;
      }
    }
    #else
	   dx_in_pipe = (freq_mhz>ratio*1200) ? ratio*3 : ratio*1;
	   ac_in_pipe = (freq_mhz>ratio*1200) ? ratio*1 : ratio*0;
    #endif
    tphy_wrlat_pipe = ratio * (hdlr->phy_timing_params.pipe_dfi_misc - hdlr->phy_timing_params.pipe_dfi_wr); 
	} else {
	 dx_in_pipe = 0;
	 ac_in_pipe = 0;
   tphy_wrlat_pipe = 2 * (hdlr->phy_timing_params.pipe_dfi_misc - hdlr->phy_timing_params.pipe_dfi_wr);
	}

    #ifdef CINIT_DDR5
	if (IS_DDR5) {
		ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
        if(hdlr->ddrPhyType_m == DWC_DDR5_PHY) {
          if (IS_RDIMM || IS_LRDIMM) {
            PRE_CFG.dfi_tphy_wrlat[p][dch] = dfi_tphy_wrlat_int + (ac_in_pipe - dx_in_pipe - tphy_wrlat_pipe) + hdlr->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd;
          } else {
            PRE_CFG.dfi_tphy_wrlat[p][dch] = dfi_tphy_wrlat_int + (ac_in_pipe - dx_in_pipe - tphy_wrlat_pipe);
          }
        } else {
	      if (IS_RDIMM || IS_LRDIMM) {
		  	PRE_CFG.dfi_tphy_wrlat[p][dch] = dfi_tphy_wrlat_int + tphy_wrlat_pipe + hdlr->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd;
	      } else {
			PRE_CFG.dfi_tphy_wrlat[p][dch] = dfi_tphy_wrlat_int + tphy_wrlat_pipe;
		  }
        }
	}
#endif /* CINIT_DDR5 */

  hdlr->phy_timing_params.dfi_tphy_wrdata = (IS_DDR5) ? 6 : 2;
  PRE_CFG.dfi_tphy_wrdata[p][dch] = hdlr->phy_timing_params.dfi_tphy_wrdata;
  // Latch the original calculated val as we'll need this for the VIP
  hdlr->tphy_wrlat_org[p] = PRE_CFG.dfi_tphy_wrlat[p][dch];
  hdlr->tphy_wrdata_org[p] = PRE_CFG.dfi_tphy_wrdata[p][dch];
  // Override the calculated value if requested by the SV code
  if (hdlr->en_dfi_ras_model == 1) {

      // Additional command delay is needed when the encryption delay is bigger than tphy_wrlat.
      if (hdlr->wr_path_delay > (PRE_CFG.dfi_tphy_wrlat[p][dch]/ratio)) {
        hdlr->dfi_ras_model_cmd_delay = (hdlr->wr_path_delay - (PRE_CFG.dfi_tphy_wrlat[p][dch]/ratio));
      }
      hdlr->del_tphy_wrlat = hdlr->del_tphy_wrlat - hdlr->dfi_ras_model_cmd_delay;

      // The minimum value of tphy_wrlat should be bigger than 6.
      // For previous step to calculate del_tphy_wrlat can't guarntee (org tphy_wrlat - del_tphy_wrlat*ratio)<7.
      // Using while loop to increase dfi_ras_model_cmd_delay and decrease del_tphy_wrlat until new tphy_wrlat_org>=7. 
      while((hdlr->tphy_wrlat_org[p] - hdlr->del_tphy_wrlat*ratio)<7) {
          hdlr->del_tphy_wrlat = hdlr->del_tphy_wrlat -1;
          hdlr->dfi_ras_model_cmd_delay = hdlr->dfi_ras_model_cmd_delay +1;
      }

	    // Controller will be programmed with a smaller value
	  	PRE_CFG.dfi_tphy_wrlat[p][dch]  = ((PRE_CFG.dfi_tphy_wrlat[p][dch] - hdlr->del_tphy_wrlat*ratio)>=ratio) ?
                                         (PRE_CFG.dfi_tphy_wrlat[p][dch] - hdlr->del_tphy_wrlat*ratio) :
                                         (PRE_CFG.dfi_tphy_wrlat[p][dch]%ratio);
      PRE_CFG.dfi_tphy_wrdata[p][dch] = ((PRE_CFG.dfi_tphy_wrdata[p][dch] - hdlr->del_tphy_wrdata*ratio)>=ratio) ?
                                         (PRE_CFG.dfi_tphy_wrdata[p][dch] - hdlr->del_tphy_wrdata*ratio) :
                                         (PRE_CFG.dfi_tphy_wrdata[p][dch]%ratio);


      if((PRE_CFG.dfi_tphy_wrlat[p][dch]+PRE_CFG.dfi_tphy_wrdata[p][dch])<13) {
        SNPS_ERROR("minimum tphy_wrlat+tphy_wrdata should be bigger than 13, dfi_tphy_wrlat=%u, dfi_tphy_wrdata=%u", PRE_CFG.dfi_tphy_wrlat[p][dch], PRE_CFG.dfi_tphy_wrdata[p][dch]);
        dwc_ddrctl_cinit_exit(1);
      }
	}

}

#endif
