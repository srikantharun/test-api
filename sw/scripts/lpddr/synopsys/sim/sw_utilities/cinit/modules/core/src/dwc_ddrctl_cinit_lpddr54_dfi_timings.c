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
#include "dwc_ddrctl_cinit_lpddr54_dfi_timings.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_defines.h"


/** @brief method to caluclate DFI timing parameters
 * Based on information from DesignWare Cores LPDDR54 PHY, PUB 1.0 Design Specification V1.2
 * PclkPtrInitVal default value should be 5 UI which is 2.5 MEMCLKs
 */
void cinit_cal_lpddr54_dfi_timings(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch)
{
    SNPS_TRACE("Entering");
#ifdef DDRCTL_LPDDR
    uint32_t tck_ps = SPD.tck_ps[p];
    uint32_t DFI_WL_SUB;
    uint32_t DFI_RL_SUB;
    uint32_t freq_mhz = CEIL(1000000,tck_ps);
    dwc_freq_ratio_t ratio;
    ratio = ddrctl_sw_get_ratio(hdlr, p);
   
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        // where WL = DRAM_WL + AL + PL + tDQSSnom (tDQSSnom= 1tck)
        // PRE_CFG.dfi_tphy_wrlat[p][ch] = PRE_CFG.cwl_x[p] + 1 - DFI_WL_SUB ;
        if (hdlr->ddrPhyType_m == DWC_LPDDR54_PHY) {
            // DFI_WL_SUB = 5 when (core_ddrc_core_clk < = 800 Mhz)
            // DFI_WL_SUB = 7 when (core_ddrc_core_clk > 800 Mhz)
            if ((tck_ps * ddrctl_sw_get_ratio_factor(hdlr, p)) < 1250) {
                DFI_WL_SUB = 7;
            } else {
                DFI_WL_SUB = 5;
            }
        } else {
            DFI_WL_SUB = 5;
        }
        DFI_RL_SUB = 5;
        PRE_CFG.dfi_tphy_wrlat[p][ch] = PRE_CFG.cwl_x[p] + 1 - DFI_WL_SUB;
        // trddata_en = RL-5
        // where 1. RL = DRAM_RL + AL + PL
        if (hdlr->memCtrlr_m.lpddr4_mr[p].mr3.read_dbi == 1)
            PRE_CFG.dfi_t_rddata_en[p][ch] = PRE_CFG.cl[p] - DFI_RL_SUB - (PRE_CFG.cl[p] - PRE_CFG.cl_dbi[p]);
        else
            PRE_CFG.dfi_t_rddata_en[p][ch] = PRE_CFG.cl[p] - DFI_RL_SUB;
    }
#endif /* CINIT_LPDDR4 */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        uint32_t ratio_factor;
        uint32_t freq_mhz = CEIL(1000000,tck_ps);

        ratio_factor = ddrctl_sw_get_ratio_factor(hdlr, p);

        DFI_WL_SUB = 5;
        if (hdlr->ddrPhyType_m == DWC_LPDDR54_PHY) {
            DFI_RL_SUB = 5;
        } else {
            if (ratio_factor == 2) {
                DFI_RL_SUB = 5;
            } else { 
                DFI_RL_SUB = (tck_ps < 2500) ? 13 : 5 ;
            }
        }

		PRE_CFG.dfi_tphy_wrlat[p][ch] = (PRE_CFG.wl[p][ch] * ratio_factor) - DFI_WL_SUB;
		PRE_CFG.dfi_t_rddata_en[p][ch] = (PRE_CFG.rl[p][ch] * ratio_factor) - DFI_RL_SUB;
		// Section 6.7 of LP54 PHY databook for Low Frequency Support
		// tphy_rdcslat will automatically increase by same number of cycles.
		if (ratio_factor == 4 && freq_mhz <= 133) {
			PRE_CFG.dfi_t_rddata_en[p][ch] += 4;
			PRE_CFG.dfi_tphy_wrlat[p][ch] += 4;
		} else if (ratio_factor == 2 && (freq_mhz > 267) && (freq_mhz <= 688)) {
			PRE_CFG.dfi_t_rddata_en[p][ch] += 2;
			PRE_CFG.dfi_tphy_wrlat[p][ch] += 2;
		} else if (ratio_factor == 2 && (freq_mhz <= 267)) {
			PRE_CFG.dfi_t_rddata_en[p][ch] += 4;
			PRE_CFG.dfi_tphy_wrlat[p][ch] += 4;
		}
	}
#endif /* CINIT_LPDDR5 */
	/** @brief Table 5-11 of phy databook 1.01a, unit : DFI clock */
	PRE_CFG.dfi_t_dram_clk_disable[p][ch] = QDYN.dfi_t_ctrl_delay[p][ch];
	PRE_CFG.dfi_t_dram_clk_enable[p][ch] = QDYN.dfi_t_ctrl_delay[p][ch];
	// Table 5-9 DFI Low Power control timing parameters
	hdlr->phy_timing_params.dfi_tlp_resp = 2 + hdlr->phy_timing_params.pipe_dfi_misc; // same for 1:2 and 1:4 modes
	hdlr->phy_timing_params.dfi_tlp_data_wakeup = 2 + hdlr->phy_timing_params.pipe_dfi_misc;
	hdlr->phy_timing_params.dfi_tphy_wrdata = 2;
  // LPDDR5X/5/4X PUB databook: t_ctrlupd_min = 2 + MISC*2 + csrCtrlUpdReqDelay
  // LPDDR5/4X/4 PUB databook:  t_ctrlupd_min = 1 + MISC + csrCtrlUpdReqDelay
	if (hdlr->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
    hdlr->phy_timing_params.dfi_t_ctrlup_min = 2 + 2*hdlr->phy_timing_params.pipe_dfi_misc;
	} else {
    hdlr->phy_timing_params.dfi_t_ctrlup_min = 1 + hdlr->phy_timing_params.pipe_dfi_misc;
	}
    #ifdef LPDDR45_DQSOSC_EN
	hdlr->phy_timing_params.dfi_t_ctrlup_min += 11; // see P80001562-381184. ctrlupd_req and ack delay is expanded csrCtrlUpdReqDelay cycles
    #endif

	// LPDDR5X/5/4X PUB databook: t_ctrlupd_max = 25 + MISC*2 + (csrCtrlUpAckDly + csrCtrlUpdReqD) 
	// LPDDR5X/5/4X PUB databook: t_ctrlupd_max = 25 + MISC + (csrCtrlUpAckDly + csrCtrlUpdReqD) 
	// DFIUPDTMG0.dfi_t_ctrlup_max description in the programming guide says: Lowest value to assign to this variable is 0x40
  uint32_t t_ctrlup_max_default;
  if (hdlr->ddrPhyType_m == DWC_LPDDR5X4_PHY) {
	  t_ctrlup_max_default = 25 + 2*hdlr->phy_timing_params.pipe_dfi_misc;
  } else {
	  t_ctrlup_max_default = 25 + hdlr->phy_timing_params.pipe_dfi_misc;
  }
    #ifdef LPDDR45_DQSOSC_EN
	t_ctrlup_max_default += 11 + 11;  // see P80001562-381184. ctrlupd_req and ack delay is expanded csrCtrlUpdReqDelay + csrCtrlUpdAckDelay cycles
    #endif
	uint32_t core_dfi_clk_ratio = IS_LPDDR5 ? 1 : ddrctl_sw_get_ratio_factor(hdlr, p);
	#ifdef DDRCTL_PPT2
		typedef enum tag_ppt2_latency_e {
			DWC_PPT2_500 = 1,
			DWC_PPT2_1000,
			DWC_PPT2_NOT_APPLICABLE
		} ppt2_latency_e;
		// PPT2 completes within 500ns if the datarate is >=3200Mbps. 1000ns if >=1600Mbps. Otherwise not applicable.
        // PPT2 config may be used only for PPT2 override. In that case latency doesn't need to be modified but modified here for ease as no harm
		ppt2_latency_e ppt2_latency =
			(IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=2500) 	? DWC_PPT2_500  :	  // LPDDR5 >=3200Mbps
			(IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=5000) 	? DWC_PPT2_1000 :	  // LPDDR5 >=1600Mbps
			(IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_2_1) && tck_ps<=1250) 	? DWC_PPT2_500  :	  // LPDDR5 >=3200Mbps
			(IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_2_1) && tck_ps<=2500) 	? DWC_PPT2_1000 :	  // LPDDR5 >=1600Mbps
			(IS_LPDDR4                                          && tck_ps<=625)   ? DWC_PPT2_500  :	  // LPDDR4 >=3200Mbps
			(IS_LPDDR4                                          && tck_ps<=1250)  ? DWC_PPT2_1000	:	  // LPDDR4 >=1600Mbps
			                                                                        DWC_PPT2_NOT_APPLICABLE;  // <1600Mbps

        uint32_t tdfi_ctrlupd_type_1_ps =    (ppt2_latency==DWC_PPT2_500) ? 500*1000 : 1000*1000;
        uint32_t tmp_ctrlup_max = (cinit_ps_to_tck(tdfi_ctrlupd_type_1_ps, tck_ps) + core_dfi_clk_ratio - 1) / core_dfi_clk_ratio;    // dfi_t_ctrlup_max unit is DFI clock cycles
        if (ppt2_latency==DWC_PPT2_NOT_APPLICABLE) tmp_ctrlup_max = t_ctrlup_max_default;                        // PPT2 is not applicable hence always ctrlupd_req is sent with ctrlupd_type==0. Apply existing constraint.
        if (p==0 || hdlr->phy_timing_params.dfi_t_ctrlup_max < tmp_ctrlup_max) {                                 // Set the largest (safest) dfi_t_ctrlup_max among all pstates
            hdlr->phy_timing_params.dfi_t_ctrlup_max = tmp_ctrlup_max;
        }
        SNPS_LOG("PPT2: For freq = %u, ppt2_latency = %d, dfi_t_ctrlup_max = %u ", p, (int)ppt2_latency, tmp_ctrlup_max);
    #else
        hdlr->phy_timing_params.dfi_t_ctrlup_max = t_ctrlup_max_default;
    #endif


    // Burst DFI contrl update request
    uint32_t t_dfi_upd_interval_ns =
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=834) ? 2500 :    //LPDDR5-9600  //JIRA___P80001562-357900 temporary value for 9600Mbps case. 
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=938) ? 2500 :    //LPDDR5-8533
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=1067) ? 2800 :   //LPDDR5-7500
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=1250) ? 3300 :   //LPDDR5-6400
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=1334) ? 3500 :   //LPDDR5-6000
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=1454) ? 3900 :   //LPDDR5-5500
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=1667) ? 3100 :   //LPDDR5-4800
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=1875) ? 3500 :   //LPDDR5-4267
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=2150) ? 4000 :   //LPDDR5-3733
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=2500) ? 3200 :   //LPDDR5-3200
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=2900) ? 3700 :   //LPDDR5-2750
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=3750) ? 4800 :   //LPDDR5-2133
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=5000) ? 4100 :   //LPDDR5-1600
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=7520) ? 6100 :   //LPDDR5-1067
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_4_1) && tck_ps<=14926) ? 12200 : //LPDDR5-533
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_2_1) && tck_ps<=1250) ? 3200 :   //LPDDR5-3200
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_2_1) && tck_ps<=1454) ? 3700 :   //LPDDR5-2750
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_2_1) && tck_ps<=1875) ? 4800 :   //LPDDR5-2133
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_2_1) && tck_ps<=2500) ? 4100 :   //LPDDR5-1600
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_2_1) && tck_ps<=3750) ? 6100 :   //LPDDR5-1067 
      (IS_LPDDR5 && (ratio==DWC_RATIO_WCK_CK_2_1) && tck_ps<=7520) ? 12200 :  //LPDDR5-533 
      (IS_LPDDR4                                     && tck_ps<=469)  ? 3500 :	  //LPDDR4-4267
      (IS_LPDDR4                                     && tck_ps<=536)  ? 4000 :	  //LPDDR4-3733
      (IS_LPDDR4                                     && tck_ps<=625) ? 3200 :   //LPDDR4-3200
      (IS_LPDDR4                                     && tck_ps<=750) ? 3700 :   //LPDDR4-2750
      (IS_LPDDR4                                     && tck_ps<=938) ? 4800 :   //LPDDR4-2133
      (IS_LPDDR4                                     && tck_ps<=1250) ? 4100 :  //LPDDR4-1600
      (IS_LPDDR4                                     && tck_ps<=1875) ? 6100 :  //LPDDR4-1067
      (IS_LPDDR4                                     && tck_ps<=3760) ? 12200 : //LPDDR4-533
                                                                                0;      // No match case-> set maximum, but it is not expected

    uint32_t tmp_ctrlupd_burst_interval_ps = (cinit_ps_to_tck(t_dfi_upd_interval_ns*1000, tck_ps) + core_dfi_clk_ratio - 1) / core_dfi_clk_ratio;
    hdlr->phy_timing_params.dfi_t_ctrlupd_burst_interval_x8[p] = (t_dfi_upd_interval_ns==0) ? 511 : min(CEIL(tmp_ctrlupd_burst_interval_ps,8),511);
    SNPS_LOG("Core VDD change: For freq = %u, dfi_upd_interval_ns = %d, dfi_t_ctrlupd_burst_interval_x8 = %u ", p, (int)t_dfi_upd_interval_ns, hdlr->phy_timing_params.dfi_t_ctrlupd_burst_interval_x8[p]);

#endif
    SNPS_TRACE("Leaving");
}
void cinit_cal_lpddr54_pre_cfg_timing_1st_set(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n)
{
    SNPS_TRACE("Entering");
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[p][n];
#ifdef DDRCTL_LPDDR
#ifdef CINIT_LPDDR5
    uint8_t ratio_factor;
    dwc_freq_ratio_t ratio;
    uint32_t freq_mhz;
    uint32_t tck_ps = SPD.tck_ps[p];

    ratio = ddrctl_sw_get_ratio(hdlr, p);
    ratio_factor = ddrctl_sw_get_ratio_factor(hdlr, p);
    freq_mhz = CEIL(1000000,tck_ps);

    //PRE_CFG.dfi_twck_en_rd[p][ch] = (timing->lpddr5_wckenl_rd_tck == 0) ? 0 : (timing->lpddr5_wckenl_rd_tck * ratio_factor) - 4;
    //PRE_CFG.dfi_twck_en_wr[p][ch] = (timing->lpddr5_wckenl_wr_tck == 0) ? 0 : (timing->lpddr5_wckenl_wr_tck * ratio_factor) - 4;
    //PRE_CFG.dfi_twck_en_fs[p][ch] = (timing->lpddr5_wckenl_fs_tck == 0) ? 0 : (timing->lpddr5_wckenl_fs_tck * ratio_factor) - 4;

    PRE_CFG.dfi_twck_en_rd[p][ch] = (timing->lpddr5_wckenl_rd_tck * ratio_factor) - 4;
    PRE_CFG.dfi_twck_en_wr[p][ch] = (timing->lpddr5_wckenl_wr_tck * ratio_factor) - 4;
    PRE_CFG.dfi_twck_en_fs[p][ch] = (timing->lpddr5_wckenl_fs_tck * ratio_factor) - 4;

    // LPDDR5X/5/4X utility PUB data-book states dfi_twck_dis is "tWCKPST - 4" for WCK ON=0 and "Max[RU(tWCKPST), RU(tWCKSTOP/tWCK)] - 3" or "RU(tCSLCK/tWCK) - 3" for WCK ON=1
      PRE_CFG.dfi_twck_dis[p][ch] = (QDYN.wck_on[ch] == 1) ? (max(CEIL((timing->lpddr5_twckstop_ps * ratio_factor), tck_ps),
                                                                  //(timing->lpddr5_twck_pst_wck + 1),
                                                                  CEIL((timing->lpddr5_tcslck_ps * ratio_factor), tck_ps)
                                                                 ) - 3) :
                                                             (timing->lpddr5_twck_pst_wck + 1 - 4);
		//PRE_CFG.dfi_twck_fast_toggle[p][ch] = 4; // LPDDR54 utility PUB data-book
		PRE_CFG.dfi_twck_fast_toggle[p][ch] = (ratio == DWC_RATIO_WCK_CK_2_1) ? 0 : 4;
		PRE_CFG.dfi_twck_toggle[p][ch] = timing->lpddr5_wckpre_static_tck * ratio_factor;
		PRE_CFG.dfi_twck_toggle_cs[p][ch] = 0;

		// temporary value : max(tWCK_PST, (BL/n_max - BL/n_min + RU(tWCK_PST/tCK)) * ratio_factor)
		// See https://ca09sg-mantis.internal.synopsys.com/production/current/view.php?id = 38917
		// LPDDR54 utility PUB data-book states dfi_twck_toggle_post is always "(BL/n_max - BL/n_min) * ratio_factor + tWCK_PST"
		//PRE_CFG.dfi_twck_toggle_post[p][ch] = (QDYN.wck_on[ch] == 1) ? timing->lpddr5_twck_pst_wck : (SPD.lpddr5_bk_bg_org[p] == DWC_LPDDR5_4BK_4BG) ? (timing->lpddr5_bl_n_max_tck - timing->lpddr5_bl_n_min_tck + timing->lpddr5_twck_pst_wck / ratio_factor) * ratio_factor : timing->lpddr5_twck_pst_wck;
		PRE_CFG.dfi_twck_toggle_post[p][ch] = (timing->lpddr5_bl_n_max_tck - timing->lpddr5_bl_n_min_tck) * ratio_factor + timing->lpddr5_twck_pst_wck + 1;

		PRE_CFG.dfi_twck_toggle_post_rd[p][ch] = PRE_CFG.dfi_twck_toggle_post[p][ch] + 8;

		// Section 6.7 of LP54 PHY databook for Low Frequency Support
		SNPS_LOG("PRE dfi_twck_en_rd = %u", PRE_CFG.dfi_twck_en_rd[p][ch]);
		// PHY parameter
		PRE_CFG.tphy_wckcsgap = (ratio == DWC_RATIO_WCK_CK_2_1) ? 3 * 2 : 1 * 4;

    // PUB specification version 1.10a
    // 7.8 LPDDR5 Low Frequency Support.
		if (ratio_factor == 4 && freq_mhz <= 133) { 
			SNPS_LOG("Adjusting PHY parameters for 1:4 freq ratio CK freq <= 133Mhz, freq_mhz =%u",freq_mhz);
			QDYN.dfi_t_ctrl_delay[p][ch] += 1;	// tctrl_delay is increased by 1 DFICLK
			PRE_CFG.dfi_twck_en_rd[p][ch] += 4;	// dfi_twck_en_rd is increased by 4 WCK
			PRE_CFG.dfi_twck_en_wr[p][ch] += 4;	// dfi_twck_en_wr is increased by 4 WCK
			PRE_CFG.dfi_twck_en_fs[p][ch] += 4;
			PRE_CFG.dfi_twck_dis[p][ch] += 4;
		} else if (ratio_factor == 2 && (freq_mhz > 267) && (freq_mhz <= 688)) {
			SNPS_LOG("Adjusting PHY parameters for 1:2 freq ratio 267 < CK freq <= 688 Mhz, freq_mhz =%u",freq_mhz);
			QDYN.dfi_t_ctrl_delay[p][ch] += 1;	// tctrl_delay is increased by 1 DFICLK
			PRE_CFG.dfi_twck_en_rd[p][ch] += 2;	// dfi_twck_en_rd is increased by 2 WCK
			PRE_CFG.dfi_twck_en_wr[p][ch] += 2;	// dfi_twck_en_wr is increased by 2 WCK
			PRE_CFG.dfi_twck_en_fs[p][ch] += 2;
			PRE_CFG.dfi_twck_dis[p][ch] += 2;
		} else if (ratio_factor == 2 && (freq_mhz <= 267)) {
			SNPS_LOG("Adjusting PHY parameters for 1:2 freq ratio CK freq <= 267Mhz, freq_mhz =%u",freq_mhz);
			QDYN.dfi_t_ctrl_delay[p][ch] += 2;	// tctrl_delay is increased by 2 DFICLK
			PRE_CFG.dfi_twck_en_rd[p][ch] += 4;	// dfi_twck_en_rd is increased by 4 WCK
			PRE_CFG.dfi_twck_en_wr[p][ch] += 4;	// dfi_twck_en_wr is increased by 4 WCK
			PRE_CFG.dfi_twck_en_fs[p][ch] += 4;
			PRE_CFG.dfi_twck_dis[p][ch] += 4;
			SNPS_LOG("dfi_twck_en_rd = %u", PRE_CFG.dfi_twck_en_rd[p][ch]);
		}

        if (ratio_factor == 4)
            PRE_CFG.dfi_twck_delay[p][ch] = QDYN.dfi_t_ctrl_delay[p][ch] * 4 + 8 + 4;    // Max across all Bytes(csrTxWckDly[10:6]/2)
        else if (ratio_factor == 2)
            PRE_CFG.dfi_twck_delay[p][ch] = QDYN.dfi_t_ctrl_delay[p][ch] * 2 + 8 + 2;    // Max across all Bytes(csrTxWckDly[10:6]/2)

    SNPS_TRACE("Leaving");
#endif /* CINIT_LPDDR5 */
#endif /* DDRCTL_LPDDR */
}


/**
 * @brief function to setup the register field values for dfitmg4
 */
#ifdef DDRCTL_LPDDR
void dwc_ddrctl_cinit_lpddr54_prgm_REGB_FREQ_DFITMG4(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFITMG4_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg4,
        &REGB_FREQ_CH1(freq).dfitmg4
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.dfi_twck_en_rd[freq][ch] = PRE_CFG.dfi_twck_en_rd[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_twck_en_rd, ch, freq);

    QDYN.dfi_twck_en_wr[freq][ch] = PRE_CFG.dfi_twck_en_wr[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_twck_en_wr, ch, freq);

    QDYN.dfi_twck_dis[freq][ch] = PRE_CFG.dfi_twck_dis[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_twck_dis, ch, freq);

#ifdef MEMC_NUM_RANKS_GT_1
    QDYN.dfi_twck_en_fs[freq][ch] = PRE_CFG.dfi_twck_en_fs[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_twck_en_fs, ch, freq);
#endif /* MEMC_NUM_RANKS_GT_1 */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG4, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dfitmg5
 */
#ifdef DDRCTL_LPDDR
void dwc_ddrctl_cinit_lpddr54_prgm_REGB_FREQ_DFITMG5(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFITMG5_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg5,
        &REGB_FREQ_CH1(freq).dfitmg5
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN.dfi_twck_fast_toggle[freq][ch] = PRE_CFG.dfi_twck_fast_toggle[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_twck_fast_toggle, ch, freq);

    QDYN.dfi_twck_toggle[freq][ch] = PRE_CFG.dfi_twck_toggle[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_twck_toggle, ch, freq);

    QDYN.dfi_twck_toggle_cs[freq][ch] = PRE_CFG.dfi_twck_toggle_cs[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_twck_toggle_cs, ch, freq);

    QDYN.dfi_twck_toggle_post[freq][ch] = PRE_CFG.dfi_twck_toggle_post[freq][ch];
    QDYN_CFG_MATRIX(ptr, dfi_twck_toggle_post, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG5, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dfitmg6
 */
#ifdef MEMC_LPDDR5X
void dwc_ddrctl_cinit_lpddr54_prgm_REGB_FREQ_DFITMG6(uint32_t freq, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DFITMG6_t *const ptr[2] = {
        &REGB_FREQ_CH0(freq).dfitmg6,
        &REGB_FREQ_CH1(freq).dfitmg6
    };
    uint32_t tmp = ptr[ch]->value;

    if ((CFG->ddrPhyType_m == DWC_LPDDR5X4_PHY) &&
        (ddrctl_sw_get_ratio(CFG, freq) == DWC_RATIO_WCK_CK_4_1) &&
        (SPD.tck_ps[freq] < 2500)) {
      QDYN.dfi_twck_toggle_post_rd_en[freq][ch] = 1;
      QDYN.dfi_twck_toggle_post_rd[freq][ch]    = PRE_CFG.dfi_twck_toggle_post_rd[freq][ch];
    } else {
      QDYN.dfi_twck_toggle_post_rd_en[freq][ch] = 0;
      QDYN.dfi_twck_toggle_post_rd[freq][ch]    = 0;
    }
    QDYN_CFG_MATRIX(ptr, dfi_twck_toggle_post_rd_en, ch, freq);
    QDYN_CFG_MATRIX(ptr, dfi_twck_toggle_post_rd, ch, freq);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFITMG6, ptr[ch]->value);

    SNPS_TRACE("Leaving");
}
#endif /* MEMC_LPDDR5X */

/** @brief method to implement Table 5-1 of phy databook, DFI clock (unit) for either LP54 PHY */
void dwc_ddrctl_cinit_lpddr54_dfi_control_timing(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch)
{
#ifdef DDRCTL_LPDDR
	uint32_t PclkPtrinitVal  = 2; //Refer to P80001562-170875, assume by default value 2
	uint32_t Trained_AcTxDly = 0;

	if (IS_LPDDR4) {
		//1:4 mode:  RU[([(PclkPtrinitVal[3:0]+ 1)/2]+5.5 +Trained_AcTxDly)/4]
		//1:2 mode:  RU[([(PclkPtrinitVal[3:0]+ 1)/2]+3.5 +Trained_AcTxDly)/2]
		if (ddrctl_sw_get_ratio(hdlr, p) == DWC_RATIO_1_4) { // 1:4 mode
			PRE_CFG.dfi_t_ctrl_delay_memclk[p][ch] = CEIL((PclkPtrinitVal + 1) + 11, 2) + Trained_AcTxDly; //optimize formula for CEIL 
			QDYN.dfi_t_ctrl_delay[p][ch] = CEIL( PRE_CFG.dfi_t_ctrl_delay_memclk[p][ch], 4); //optimize formula for CEIL 
      } else {
			PRE_CFG.dfi_t_ctrl_delay_memclk[p][ch] = CEIL((PclkPtrinitVal + 1) + 7, 2) + Trained_AcTxDly; //optimize formula for CEIL
			QDYN.dfi_t_ctrl_delay[p][ch] = CEIL( PRE_CFG.dfi_t_ctrl_delay_memclk[p][ch], 2); //optimize formula for CEIL
      }
	}
	else if (IS_LPDDR5) {
		// [(PclkPtrinitVal[3:0]+ 1)/8]+1.75 +Trained_AcTxDly
		QDYN.dfi_t_ctrl_delay[p][ch] = CEIL((PclkPtrinitVal+1) + 14, 8) + Trained_AcTxDly; // optimize formula for CEIL
	}
#endif
}

