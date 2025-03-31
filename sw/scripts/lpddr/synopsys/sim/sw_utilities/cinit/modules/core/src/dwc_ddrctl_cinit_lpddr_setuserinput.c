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
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_defines.h"

#ifdef DDRCTL_LPDDR
/** @brief method to apply user options from defconfig file to CINIT structures.
 * Some mode registers are automatically set so that they match the controller
 * settings
 * */
void dwc_ddrctl_cinit_lpddr_setuserinput(void)
{
	dwc_cinit_set_operational_clk_period(CFG);
	// No need to make dram_caw, dram_raw etc selectable via KConfig.
	// the values are fixed from JEDEC
	// Doing the decode and assignment here

	CFG->disable_fsp_op = 0;
	STATIC.dual_channel_en = 0;
	// automatically set MR registers that MUST be align to controller
	// settings
	for (uint32_t p=0; p < CFG->num_pstates; p++) {
		LPDDR4_MR[p].mr3.read_dbi = QDYN.rd_dbi_en[0];
		LPDDR4_MR[p].mr3.write_dbi = QDYN.wr_dbi_en[0];
		if ( SPD.tck_ps[p] < 625)
			LPDDR4_MR[p].mr3.wr_postamble = 1;
		else
			LPDDR4_MR[p].mr3.wr_postamble = 0;
		LPDDR4_MR[p].mr13.dmd = (QDYN.dm_en[0] == 1) ? 0 : 1;
		if ( CFG->num_pstates > 1) {
			LPDDR4_MR[p].mr13.fsp_op = 1;
			LPDDR4_MR[p].mr13.fsp_wr = 1;
		}
		LPDDR4_MR[p].mr23.dqs_interval = QDYN.dqsosc_runtime;
		LPDDR5_MR[p].mr3.read_dbi = QDYN.rd_dbi_en[0];
		LPDDR5_MR[p].mr3.write_dbi = QDYN.wr_dbi_en[0];
		if (SPD.lpddr5_bk_bg_org[0] == DWC_LPDDR5_4BK_4BG)
			LPDDR5_MR[p].mr3.bk_bg_org = 0;
		else
			LPDDR5_MR[p].mr3.bk_bg_org = 2;
		LPDDR5_MR[p].mr13.dmd = (QDYN.dm_en[0] == 1) ? 0 : 1;
		if(ddrctl_sw_get_ratio(CFG, p) == DWC_RATIO_WCK_CK_4_1 ) {
			LPDDR5_MR[p].mr18.ckr = 0;
		} else {
			LPDDR5_MR[p].mr18.ckr = 1;
		}
		if (SPD.tck_ps[p] < (625 * ddrctl_sw_get_ratio_factor(CFG, p))) {
			LPDDR5_MR[p].mr18.wck_fm = 1;
		} else {
			LPDDR5_MR[p].mr18.wck_fm = 0;
		}
		LPDDR5_MR[p].mr18.wck_on = QDYN.wck_on[0];
		LPDDR5_MR[p].mr22.wecc = QDYN.wr_link_ecc_enable[p][0];
		LPDDR5_MR[p].mr22.recc = QDYN.rd_link_ecc_enable[p][0];
		LPDDR5_MR[p].mr37.wck2dqi_runtime = QDYN.dqsosc_runtime;
		LPDDR5_MR[p].mr40.wck2dqo_runtime = QDYN.wck2dqo_runtime;
		// JIRA P80001562-233234 checker for PHY firmware requirement.
#ifdef CINIT_LPDDR4
		if ((LPDDR4_MR[p].mr12.vref_ca == 0) && (LPDDR4_MR[p].mr11.ca_odt == 0)) {
		    SNPS_ERROR("PHY requirement: if MR12 CA VREF is 0, MR11 CA ODT cannot be 0.");
		}
#endif // CINIT_LPDDR4
#ifdef CINIT_LPDDR5
		if ((LPDDR5_MR[p].mr12.vref_ca == 0) && (LPDDR5_MR[p].mr11.ca_odt == 0)) {
		    SNPS_ERROR("PHY requirement: if MR12 CA VREF is 0, MR11 CA ODT cannot be 0.");
		}
#endif // CINIT_LPDDR5

	}
	CFG->HdtCtrl = 0xC8;
	// dwc_cinit_phyinit_setuserinput_lpddr54 has unnecessary dependence on
	// this variable lpddr4_pop_support
	CFG->lpddr4_pop_support = 1;
	CFG->dfi1_exists = 1;
}
#endif // DDRCTL_LPDDR
