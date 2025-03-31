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


#include "dwc_ddrctl_cinit_common_sequences.h"
#include "dwc_ddrctl_cinit_ddr_sequences.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_phy_training.h"
#include "phy/sinit_phy_utils.h"
#include "sinit_types.h"
#include "physetup.h"
#include "cinit_port_util.h"
#include "cinit_status.h"
#include "phy/ddr54/sinit_ddrphy54_regmap.h"
#include "jedec/ddr5/cinit_ddr5_types.h"
#include "jedec/ddr5/cinit_ddr5_timing_utils.h"
#include "ctrl_words/ddr5/cinit_ddr5_ctrl_words.h"
#include "ctrl_words/ddr4/ddrctl_sw_ddr4_ctrl_words.h"
#include "mode_regs/ddr5/ddrctl_sw_ddr5_mode_regs.h"
#include "mode_regs/ddr4/ddrctl_sw_ddr4_mode_regs.h"
#include "sw_cmd_intf/ddr5/cinit_ddr5_sw_cmd.h"

#ifdef DDRCTL_DDR
 /**
  * @defgroup DDRSwSeqGrp DDR software sequences
  * This section groups together software sequences and methods that are used in
  * DDR controllers.
  * @{
  */

/**
 * @brief Software Clock Removal Sequence
 */
bool dwc_ddrctl_cinit_sw_seq_clocks_disable(void)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t selfref_type = 0;
    PWRCTL_t *const ptrPWRCTL[2]   = {
            &REGB_DDRC_CH0.pwrctl,
            &REGB_DDRC_CH1.pwrctl
    };
    ZQCTL2_t *const ptrZQCTL2 = &REGB_DDRC_CH0.zqctl2;

    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_DISABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports disable failed");
        return false;
    }

    /** -# Disable the Scubber for all channels and wait until is idle
     * This is only required if SBR is instantiated
     */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_DISABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber disable failed");
        return false;
    }

    DFIUPD0_t *const ptrDFIUPD0 = &REGB_DDRC_CH0.dfiupd0;
    DQSOSCCFG0_t *const ptrDQSOSCCFG0 = &REGB_DDRC_CH0.dqsosccfg0;
    DERATECTL6_t *const ptrDERATECTL6 = &REGB_DDRC_CH0.deratectl6;

    /** - disable automatic controller updates and ZQCAL */
    ptrZQCTL2->value = dwc_ddrctl_cinit_io_read32 (REGB_DDRC_CH_OFFSET(0) + ZQCTL2);
    ptrDFIUPD0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0 );
    if (IS_DDR5)
      ptrDERATECTL6->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6);

    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_pre_qdyn_write");
        return false;
    }
    ptrDFIUPD0->dis_auto_ctrlupd = 1;
    ptrDFIUPD0->dis_auto_ctrlupd_srx = 1;
    ptrZQCTL2->dis_srx_zqcl = 1;
    ptrDERATECTL6->dis_mrr4_tcr_srx = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0, ptrDFIUPD0->value);
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2, ptrZQCTL2->value);
    if (IS_DDR5)
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6, ptrDERATECTL6->value);

    ptrDQSOSCCFG0->dis_dqsosc_srx = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0, ptrDQSOSCCFG0->value);

    if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_post_qdyn_write");
        return false;
    }

    /** -# Write ‘1’ to PWRCTL.selfref_sw Causes the system to move to Self Refresh state. */
    /** -#
     * * In DDR5, since clock will be removed,PWRTL.en_dfi_dram_clk_disable must be
     * * set to 1'b1 before this step;
     * */
    /** -#
     * * In DDR5 RDIMM, DIMMCTL.dimm_selfref_clock_stop_mode must be set to 1'b1 before this step.
     */

#ifdef CINIT_DDR5
    if (IS_DDR5) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptrPWRCTL[ch]->en_dfi_dram_clk_disable = 1;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
        }
        if (IS_RDIMM) {
            REGB_DDRC_CH0.dimmctl.dimm_selfref_clock_stop_mode = 1;
        }
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DIMMCTL, REGB_DDRC_CH0.dimmctl.value);
#ifdef DDRCTL_SINGLE_INST_DUALCH
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DIMMCTL, REGB_DDRC_CH0.dimmctl.value);
#endif
    }
#endif

#ifdef CINIT_DDR4
    if (DDR4_MR[0].mr2.auto_self_ref  != 0) {
        /** - if DDR4 LP ASR is enabled then disable it before going into selfref */
        if (dwc_ddrctl_cinit_seq_set_ddr4_mr2_asr(false) == false) {
            SNPS_ERROR("Error in seq_set_ddr4_mr2_asr ");
            return false;
    }
    }
#endif // CINIT_DDR4

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptrPWRCTL[ch]->selfref_sw = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
    }

    /** -# Poll STAT.selfref_type= 2’b10 Waits until Self Refresh state is entered. */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        uint32_t active_ranks = STATIC.active_ranks;
        selfref_type =  (active_ranks == 0xF) ? 0xaa : (active_ranks == 0x3) ? 0xa  : (active_ranks == 0x1) ? 0x2  : 0x0;
    }
#endif
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        selfref_type = 0x2;
    }
#endif
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_selfref_type(DWC_DDRCTL_MAX_APB_POLLING, ch, selfref_type) == false) {
            SNPS_ERROR("Error in seq_poll_selfref_type");
            return false;
    }
    }

    /** -# Remove AXI clock */
    if (IS_ARB_CONFIG) {
        dwc_ddrctl_cinit_io_set_axi_clk(false);
    }
    /** -#  Remove DDRC controller clock */
    dwc_ddrctl_cinit_io_set_ddrc_clk(false);

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief Enable clocks sequence
 */
bool dwc_ddrctl_cinit_sw_seq_clocks_enable(void)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    ZQCTL2_t *const ptrZQCTL2 = &REGB_DDRC_CH0.zqctl2;

    /** -#  Enable AXI clock */
    if (IS_ARB_CONFIG) {
        dwc_ddrctl_cinit_io_set_axi_clk(true);
    }

    /** -# Enable DDRC controller clock It is recommended for DDR4 to re-enable generation of PHY initiated Update requests (dfi_phyupd_req). If using a Synopsys PHY, this can be done through the PUB’s DSGCR.PUREN.  */
    dwc_ddrctl_cinit_io_set_ddrc_clk(true);

    /** -#  Write ‘0’ to pwrctl.selfref_sw Cause system to exit from self-refresh state. */

    PWRCTL_t *const ptrPWRCTL[2]   = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptrPWRCTL[ch]->selfref_sw = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
    }

    /** -#  Poll STAT.selfref_type = 2’b00 Wait until self-refresh state is exited. */

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_selfref_type(DWC_DDRCTL_MAX_APB_POLLING, ch, 0) == false) {
            SNPS_ERROR("Error in seq_poll_selfref_type");
            return false;
        }
    }
    /// - Wait for normal operation mode
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, ch, 1) == false) {
            SNPS_ERROR("Error in seq_poll_operating_mode");
            return false;
        }
    }
    /** - re-enable controller updates and other controller settings such as dis_auto_ctrlupd_srx, dis_srx_zqcl, dis_mrr4_tcr_srx. */
    DQSOSCCFG0_t *const ptrDQSOSCCFG0 = &REGB_DDRC_CH0.dqsosccfg0;
    DFIUPD0_t *const ptrDFIUPD0 = &REGB_DDRC_CH0.dfiupd0;
    DERATECTL6_t *const ptrDERATECTL6 = &REGB_DDRC_CH0.deratectl6;

    ptrZQCTL2->value = dwc_ddrctl_cinit_io_read32 (REGB_DDRC_CH_OFFSET(0) + ZQCTL2);
    ptrDFIUPD0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0 );
    if (IS_DDR5)
        ptrDERATECTL6->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6);
    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_pre_qdyn_write");
        return false;
    }
    ptrDFIUPD0->dis_auto_ctrlupd = QDYN.dis_auto_ctrlupd;
    ptrDFIUPD0->dis_auto_ctrlupd_srx = QDYN.dis_auto_ctrlupd_srx;
    ptrZQCTL2->dis_srx_zqcl = QDYN.dis_srx_zqcl;
    ptrDERATECTL6->dis_mrr4_tcr_srx = QDYN.dis_mrr4_tcr_srx;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0, ptrDFIUPD0->value);
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2, ptrZQCTL2->value);
    if (IS_DDR5)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6, ptrDERATECTL6->value);

    ptrDQSOSCCFG0->dis_dqsosc_srx = QDYN.dis_dqsosc_srx;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0, ptrDQSOSCCFG0->value);

    if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_post_qdyn_write");
        return false;
    }
#ifdef CINIT_DDR4
    if (DDR4_MR[0].mr2.auto_self_ref  != 0) {
        /** - if DDR4 LP ASR is enabled then Restore LP ASR after manually exiting selfref */
        if (dwc_ddrctl_cinit_seq_set_ddr4_mr2_asr(true) == false) {
            SNPS_ERROR("Error in seq_set_ddr4_mr2_asr ");
            return false;
        }
    }
#endif // CINIT_DDR4

    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports enable failed");
        return false;
    }

    /** -# Enable the Scubber for all channels
     * This is only required if SBR is instantiated
     */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_ENABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber enable failed");
        return false;
    }
    return true;
}

/**
 * @brief Disable power sequence
 */
bool dwc_ddrctl_cinit_sw_seq_power_disable(void)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t selfref_type = 0;
    PWRCTL_t *ptr_pwrctl[2] = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };

    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_DISABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports disable failed");
        return false;
    }

    /** -# Disable the Scubber for all channels and wait until is idle
     * This is only required if SBR is instantiated
     */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_DISABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber disable failed");
        return false;
    }

#ifdef CINIT_DDR4
    if (DDR4_MR[0].mr2.auto_self_ref  != 0) {
        /** - if DDR4 LP ASR is enabled then disable it before going into selfref */
        if (dwc_ddrctl_cinit_seq_set_ddr4_mr2_asr(false) == false) {
            SNPS_ERROR("Error in seq_set_ddr4_mr2_asr ");
            return false;
        }
    }
#endif // CINIT_DDR4

    /** -# Write ‘1’ to pwrctl.selfref_sw Causes the system to move to Self Refresh state. */
    /** -#
     * In DDR5, since clock will be removed,PWRTL.en_dfi_dram_clk_disable must be
     * set to 1'b1 before this step;
     */
    /** -#
     * In DDR5 RDIMM, dimmctl.dimm_selfref_clock_stop_mode must be set to 1'b1 before this step.
     */

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptr_pwrctl[ch]->en_dfi_dram_clk_disable = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        if (IS_RDIMM) {
            REGB_DDRC_CH0.dimmctl.dimm_selfref_clock_stop_mode = 1;
        }
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DIMMCTL, REGB_DDRC_CH0.dimmctl.value);
#ifdef DDRCTL_SINGLE_INST_DUALCH
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DIMMCTL, REGB_DDRC_CH0.dimmctl.value);
#endif
    }
#endif
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->selfref_sw = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }

    /** -# Poll STAT.selfref_type= 2’b10 Waits until Self Refresh state is entered. */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        uint32_t active_ranks = STATIC.active_ranks;
        selfref_type =  (active_ranks == 0xF) ? 0xaa : (active_ranks == 0x3) ? 0xa  : (active_ranks == 0x1) ? 0x2  : 0x0;
    }
#endif
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        selfref_type = 0x2;
    }
#endif
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_selfref_type(DWC_DDRCTL_MAX_APB_POLLING, ch, selfref_type) == false) {
            SNPS_ERROR("Error in seq_poll_selfref_type");
            return false;
    }
    }

    /** -#  Place IOs in retention mode Refer to relevant PHY databook for more information. */

    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_pre_qdyn_write");
        return false;
    }
    REGB_DDRC_CH0.dfiupd0.dis_auto_ctrlupd = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0, REGB_DDRC_CH0.dfiupd0.value);
    if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_post_qdyn_write");
        return false;
    }

    if (dwc_ddrctl_cinit_phy_lp3_io_retention(true) == false) {
        SNPS_ERROR("Error in phy_lp3_io_retention");
        return false;
    }

    if (IS_ARB_CONFIG) {
        dwc_ddrctl_cinit_io_set_axi_clk(false);
        dwc_ddrctl_cinit_io_aresetn(false);
    }

    /** -#  DDRC controller clock core_ddrc_core_clk can be stopped*/
    dwc_ddrctl_cinit_io_set_ddrc_clk(false);

    /** -#  Drive low RESETn to the PHY */
    /** -#  Remove power */
    dwc_ddrctl_cinit_io_power(false);

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief Enable power sequence
 */
bool dwc_ddrctl_cinit_sw_seq_power_enable(void)
{
    SNPS_TRACE("Entering");
    ddrctl_error_t   rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;

    /** -# Enable Power */
    dwc_ddrctl_cinit_io_power(true);

    /** -# Enable DDRC controller clock core_ddrc_core_clk */
    dwc_ddrctl_cinit_io_set_ddrc_clk(true);

    /** -# Reset controller/PHY by driving core_ddrc_rstn = 1’b0, aresetn_n = 1’b0, presetn = ’b0 */
    dwc_ddrctl_cinit_io_presetn(false);
    dwc_ddrctl_cinit_io_ddrc_rstn(0);
#ifdef UMCTL2_INCL_ARB_OR_CHB
    dwc_ddrctl_cinit_io_aresetn(0);
#endif /* UMCTL2_INCL_ARB_OR_CHB*/

    /** -# Remove APB reset, presetn = 1’b1, and reprogram the registers to pre-power removal values */
    dwc_ddrctl_cinit_io_wait_pclk(10);
    dwc_ddrctl_cinit_io_presetn(true);
    dwc_ddrctl_cinit_io_wait_ddrc_clk(128);
    //the controller has been reset so reset register structure
    dwc_cinit_reg_defaults(hdlr);

    /** -# Program INITTMG0.skip_dram_init = 2’b11 Skips the DRAM initialization routine and starts up in self-refresh mode.  */
    if (dwc_ddrctl_cinit_seq_set_skip_dram_init(3) == false) {
        SNPS_ERROR("Error in seq_set_skip_dram_init");
        return false;
    }

    // set QDYN.skip_dram_init so dwc_ddrctl_cinit_seq_initialize_ctrl_regs will not overwrite value of 3
    QDYN.skip_dram_init[0] = 3;

    /** -# Programs pwrctl.selfref_sw = 1’b1 Keeps the controller in self-refresh mode.*/
    /** -#
     * In DDR5, program dqsosccfg0.dis_dqsosc_srx to 1'b1 and zqctl2.dis_srx_zqcl to 1'b1.
     */
    /** -#
     * In DDR5 RDIMM, since clock is removed after power removal, dimmctl.dimm_selfref_clock_stop_mode must be set to 1'b1 before this step
     * in Self Refresh, In DDR5 (L)RDIMM, the value of PWRTL.en_dfi_dram_clk_disable need to be same as DIMMCTL.dimm_selfref_clock_stop_mode. JIRA:P80001562-347531
     */

    PWRCTL_t *const ptrPWRCTL[2]   = {
            &REGB_DDRC_CH0.pwrctl,
            &REGB_DDRC_CH1.pwrctl
    };
#ifdef CINIT_DDR5

    if (IS_DDR5) {
        if (IS_RDIMM || IS_LRDIMM) {
          for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptrPWRCTL[ch]-> en_dfi_dram_clk_disable = 1;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
          }
          REGB_DDRC_CH0.dimmctl.dimm_selfref_clock_stop_mode = 1;
        }
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DIMMCTL, REGB_DDRC_CH0.dimmctl.value);
        #ifdef DDRCTL_SINGLE_INST_DUALCH
          dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DIMMCTL, REGB_DDRC_CH0.dimmctl.value);
        #endif

        /* quasi dynamic write */
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        REGB_DDRC_CH0.dqsosccfg0.dis_dqsosc_srx = 1;
        QDYN.dis_dqsosc_srx = 1;
        REGB_DDRC_CH0.zqctl2.dis_srx_zqcl = 1;
        QDYN.dis_srx_zqcl = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0, REGB_DDRC_CH0.dqsosccfg0.value);
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2, REGB_DDRC_CH0.zqctl2.value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
    }
#endif

    DQSOSCCFG0_t *const ptrDQSOSCCFG0 = &REGB_DDRC_CH0.dqsosccfg0;
    ZQCTL2_t *const ptrZQCTL2 = &REGB_DDRC_CH0.zqctl2;

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptrPWRCTL[ch]->selfref_sw = 1;
        DYN.selfref_sw[ch] = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
    }

    /** -# Program DFIMISC.dfi_init_complete_en to 1’b0 PHY initialization needs to be rerun so set to ’0’ until initialization complete.  This step is only required for DDR4.
     */
    DFIMISC_t *const ptrDFIMISC = &REGB_DDRC_CH0.dfimisc;

    if (IS_DDR4) {
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        ptrDFIMISC->dfi_init_complete_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIMISC, ptrDFIMISC->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
    }

    /** -# Remove the controller reset core_ddrc_rstn = 1’b1 aresetn_n = 1’b1 */
    dwc_ddrctl_cinit_io_ddrc_rstn(0);
#ifdef UMCTL2_INCL_ARB_OR_CHB
    dwc_ddrctl_cinit_io_aresetn(0);
#endif /* UMCTL2_INCL_ARB_OR_CHB*/

    SNPS_LOG("initialize the controller register map again");

    /*  Re-initialize the controller register map */
    if (dwc_ddrctl_cinit_seq_initialize_ctrl_regs() == false) {
        SNPS_ERROR("Error in seq_initialize_ctrl_regs");
        return false;
    }
    /*  Release core_rst_n to the controller */
    dwc_ddrctl_cinit_io_ddrc_rstn(true);
#ifdef UMCTL2_INCL_ARB_OR_CHB
    /* de-assert aresetn */
    dwc_ddrctl_cinit_io_aresetn(true);
#endif /* UMCTL2_INCL_ARB_OR_CHB*/
    /** -# Run PHY initialization/training as required, including removing
     * the IOs from retention mode including steps below Refer
     * to the relevant PHY databook for more information.
     */
    if (dwc_ddrctl_cinit_phy_lp3_io_retention(false) == false) {
        SNPS_ERROR("Error in phy_lp3_io_retention");
        return false;
    }
    // load uCode needed for DDR5
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        dwc_ddrctl_cinit_prgm_ucode(CFG);
        dwc_ddrctl_cinit_prgm_cfgbuf(CFG);
    }
#endif
    DFIUPD0_t *const ptrDFIUPD0 = &REGB_DDRC_CH0.dfiupd0;
    DERATECTL6_t *const ptrDERATECTL6 = &REGB_DDRC_CH0.deratectl6;
    if (IS_DDR5)
        ptrDERATECTL6->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6);
    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_pre_qdyn_write");
        return false;
    }

    ptrDFIUPD0->dis_auto_ctrlupd = 1;
    ptrDFIUPD0->dis_auto_ctrlupd_srx = 1;
    ptrDERATECTL6->dis_mrr4_tcr_srx = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0, ptrDFIUPD0->value);
    if (IS_DDR5)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6, ptrDERATECTL6->value);

    if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_post_qdyn_write");
        return false;
    }

    if (dwc_ddrctl_cinit_pre_phyinit() == false) {
        SNPS_ERROR("Error in pre_phyinit");
        return false;
    }

    /** -# PWRTL.en_dfi_dram_clk_disable and DIMMCTL.dimm_selfref_clock_stop_mode must be set to 1 and kept to be 1 till selfref exit sequence is completed. JIRA:P80001562-347531*/
    if (IS_DDR5) {
        if (IS_RDIMM || IS_LRDIMM) {
            for (uint32_t ch = 0; ch < num_ddrc; ch++) {
              ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
              ptrPWRCTL[ch]-> en_dfi_dram_clk_disable = 1;
              dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
            }
            REGB_DDRC_CH0.dimmctl.dimm_selfref_clock_stop_mode = 1;
        }
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DIMMCTL, REGB_DDRC_CH0.dimmctl.value);
        #ifdef DDRCTL_SINGLE_INST_DUALCH
          dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DIMMCTL, REGB_DDRC_CH0.dimmctl.value);
        #endif
    }

    if (DDRCTL_SUCCESS != dwc_ddrctl_cinit_phyinit(CFG, DDRCTL_TRUE)) {
        SNPS_ERROR("Error in phyinit");
        return false;
    }
    if (dwc_ddrctl_cinit_post_phyinit() == false) {
        SNPS_ERROR("Error in post_phyinit");
        return false;
    }
#ifdef CINIT_DDR4
    if (IS_DDR4) {
    /** -# Below substeps for DDR4 only */
    /** -#
     * Program dfimisc.dfi_frequency as required. Refer to PHY databook for more details
     */
    /** -#
     * Set dfimisc.dfi_init_start to ‘1’
     */

        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        ptrDFIMISC->dfi_init_start = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIMISC, ptrDFIMISC->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }

    /** -#
     * Set dfimisc.dfi_init_start to ‘0’.
     */

        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        ptrDFIMISC->dfi_init_start = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIMISC, ptrDFIMISC->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }

    /** -#
     * Program dfimisc.dfi_init_complete_en to 1'b1 Indicates to controller
     * that PHY has completed re-training/initialization. This step is only required for DDR4.
     */
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        ptrDFIMISC->dfi_init_complete_en = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIMISC, ptrDFIMISC->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
    }
#endif
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        /** -# Below substeps for DDR5 only */
        /** -#
         * Set CSn to LOW of all ranks of all channels through software command interface command FORCE_CS.
         */
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            rslt = cinit_ddr5_send_reset_control(hdlr, (ddrctl_channel_t)ch, DDRCTL_DISABLE, SW_CTRL_LAST_CMD);
            if (rslt != DDRCTL_SUCCESS) {
                SNPS_ERROR("Error in Send reset control exit");
                return false;
            }
        }

        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            rslt = cinit_ddr5_send_force_cs(hdlr, (ddrctl_channel_t)ch, 0xf, 0, SW_CTRL_LAST_CMD);
            if (rslt != DDRCTL_SUCCESS) {
                SNPS_ERROR("Error in Send Force CS reset");
                return false;
            }
        }

        /** -#
         * Set REGB_DDRC_CH0.pasctl37.dch_sync_mode to ‘1’. This enables
         * dfi_init_start and dfi_init_complete to assert and de-assert
         * at the same time on both channels. (Dual Channel only)
         */
        if (num_ddrc == 2) {
            if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(1) == false) {
                SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
                return false;
            }
        }

        /** -#
         * Program dfi_frequency to target frequency value and dfi_init_start_set
         * to '1' in software command interface command DFIFC (dfi_frequency/dfi_freq_ratio/
         * dfi_init_start_set). This will set dfi_init_start to '1' at the DFI interface.
         * If dual channel is enabled, this step is only needed on software command interface
         * of Channel 0, since REGB_DDRC_CH0.pasctl37.dch_sync_mode has been set to ‘1’.
         */
        rslt = cinit_ddr5_send_dfi_freq_chg_ctrl(hdlr, DDRCTL_CHANNEL_0, 1, 0,
                                                 MEMC_FREQ_RATIO, 0, 0, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Error in Send Force CS reset");
            return false;
        }


        /** -#
         * Set dfi_init_start_clear to '1' and dfi_init_start_set to '0' in software
         * command interface command DFIFC (dfi_init_start_clear) to inform PHY to prepare
         * for normal operation. This will set dfi_init_start to '0' at the DFI interface.
         * If dual channel is enabled, this step is only needed software command interface
         * of Channel 0, since REGB_DDRC_CH0.pasctl37.dch_sync_mode has been set to ‘1’.
         */
        rslt = cinit_ddr5_send_dfi_freq_chg_ctrl(hdlr, DDRCTL_CHANNEL_0, 0, 1, MEMC_FREQ_RATIO,
                                                 0, 0, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Error in Send Force CS reset");
            return false;
        }

        /** -#
         * Set REGB_DDRC_CH0.pasctl37.dch_sync_mode to ‘0’. (Dual Channel only)
         */
        if (num_ddrc == 2) {
            if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(0) == false) {
                SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
                return false;
            }
        }
    }
#endif  // CINIT_DDR5
    /** -# Program pwrctl.selfref_sw = 1’b0 trigger self-refresh exit */
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptrPWRCTL[ch]->selfref_sw = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
    }

    /** -# Poll STAT.selfref_type = 2’b00 Wait until self-refresh state is exited.  */
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_selfref_type(DWC_DDRCTL_MAX_APB_POLLING, ch, 0) == false) {
            SNPS_ERROR("Error in seq_poll_selfref_type");
            return false;
    }
    }

    /** -# Poll STAT.operating_mode for Normal Mode entry In DDR5, poll STAT.operating_mode = 3'b000 */
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
#ifdef CINIT_DDR4
        if (IS_DDR4) {
            if (dwc_ddrctl_cinit_seq_poll_operating_mode(2 * DWC_DDRCTL_MAX_APB_POLLING, ch, 1) == false) {
                SNPS_ERROR("Error in seq_poll_operating_mode");
                return false;
        }
        }
#endif
#ifdef CINIT_DDR5
        if (IS_DDR5) {
            if (dwc_ddrctl_cinit_seq_poll_operating_mode(2 * DWC_DDRCTL_MAX_APB_POLLING, ch, 0) == false) {
                SNPS_ERROR("Error in seq_poll_operating_mode");
                return false;
            }
        }
#endif
    }

    /** -# Program dqsosccfg0.dis_dqsosc_srx to 1'b0 if necessary and
     * zqctl2.dis_srx_zqcl to 1'b0 if necessary This step is only required for DDR5.
     */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        if (IS_DDR5)
            ptrDERATECTL6->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6);
        /* quasi dynamic write */
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        REGB_DDRC_CH0.dqsosccfg0.dis_dqsosc_srx = 0;
        REGB_DDRC_CH0.zqctl2.dis_srx_zqcl = 0;
	ptrDERATECTL6->dis_mrr4_tcr_srx = QDYN.dis_mrr4_tcr_srx;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0, REGB_DDRC_CH0.dqsosccfg0.value);
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2, REGB_DDRC_CH0.zqctl2.value);
	if (IS_DDR5)
	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6, ptrDERATECTL6->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
    }
    }
    /** -# Program pasctl0.init_done to 1'b1 This step is only required for DDR5.*/
    if (IS_DDR5) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            if (dwc_ddrctl_cinit_ddr5_init_done(1, ch) == false) {
                SNPS_ERROR("Error in ddr5_init_done");
                return false;
        }
    }
    }
#endif
    /** -# Send MRW to all ranks of all channels through software command interface
     * command MRW to update MR45, its value should be aligned with DQSOSCRUNTIME.dqsosc_runtime
     * This step is only required for DDR5.  "Of all channels" only applies to dual channel configurations.
     */
    uint32_t active_ranks = REGB_DDRC_CH0.mstr0.active_ranks;


    /** -# Program DQSOSCCFG0.dis_dqsosc_srx to 1'b0 if necessary and
     * ZQCTL2.dis_srx_zqcl to 1'b0 if necessary This step is only required for DDR5.
     */
    /* quasi dynamic write */
    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_pre_qdyn_write");
        return false;
    }
    ptrDQSOSCCFG0->dis_dqsosc_srx = 0;
    ptrZQCTL2->dis_srx_zqcl = 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0, ptrDQSOSCCFG0->value);
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2, ptrZQCTL2->value);
    if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_post_qdyn_write");
        return false;
    }
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        // TODO: config the address value, it should be 0x45
        rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 45, ddrctl_sw_get_ddr5_mode_reg(hdlr, 0, 45), DDRCTL_FALSE,
                                    DDRCTL_FALSE, active_ranks, SW_CTRL_LAST_CMD);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Error in seq_ddr5_send_mrw");
            return false;
        }
    }
#endif

#ifdef CINIT_DDR4
    if (DDR4_MR[0].mr2.auto_self_ref  != 0) {
        /** - if DDR4 LP ASR is enabled then Restore LP ASR after manually exiting selfref as part of power removal sequence */
        if (dwc_ddrctl_cinit_seq_set_ddr4_mr2_asr(true) == false) {
            SNPS_ERROR("Error in seq_set_ddr4_mr2_asr ");
            return false;
    }
    }
#endif // CINIT_DDR4

    /// - memory sub-system is now ready, enable hif interface
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_set_opctrl1(0, 0, ch) == false) {
            SNPS_ERROR("Error in seq_set_opctrl1");
            return false;
    }
    }

    /** -# Write PCTRL.port_en = 1 AXI ports are no longer blocked from taking transactions.*/
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports enable failed");
        return false;
    }

    /** -# Enable the Scubber for all channels
     * This is only required if SBR is instantiated
     */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_ENABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber enable failed");
        return false;
    }

    //Restore back the dis_auto_ctrlupd value as this would have been set
    //to 1 in power_removal/re-enable
    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_pre_qdyn_write");
        return false;
    }
    ptrDFIUPD0->dis_auto_ctrlupd = QDYN.dis_auto_ctrlupd;
    ptrDFIUPD0->dis_auto_ctrlupd_srx = QDYN.dis_auto_ctrlupd_srx;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0, ptrDFIUPD0->value);

    ZQCTL2_t        * ptr_zqctl2 = &REGB_DDRC_CH0.zqctl2;

    ptr_zqctl2->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2);
    ptr_zqctl2->dis_srx_zqcl = QDYN.dis_srx_zqcl;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2, ptr_zqctl2->value);

    //restore the register value dis_dqsosc_srx
    ptrDQSOSCCFG0->value = dwc_ddrctl_cinit_io_read32 (REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0);
    ptrDQSOSCCFG0->dis_dqsosc_srx = QDYN.dis_dqsosc_srx;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0, ptrDQSOSCCFG0->value);

    if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_post_qdyn_write");
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
}


/**
 * @brief Execute Maximum Power Saving Mode entry sequence
 *
 * @param target_rank   Target rank
 *
 * @return true
 * @return false
 */
bool dwc_ddrctl_cinit_sw_seq_mpsm_ddr5_entry(uint8_t target_rank)
{
    ddrctl_error_t   rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t active_ranks = REGB_DDRC_CH0.mstr0.active_ranks;
    uint32_t ch;
    // Target rank selected will be 1st Rank
    uint8_t non_target_rank = active_ranks & 0xe;


    /** -# Stop sending read/write traffic to those ranks on which current MPSM entry process is performed
     * (target ranks).
     */
    /** -# Stop sending scrubbing traffic to target ranks. */
    /** -# Wait until all pending transactions to target ranks are completed. Make sure all transactions from
     * system and scrubber are finished.
     */

    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_DISABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports disable failed");
        return false;
    }

    /** -# Disable the Scubber for all channels and wait until is idle
     * This is only required if SBR is instantiated
     */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_DISABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber disable failed");
        return false;
    }

    /** -#Disable global maintenance calibration activities of all channels through pasctl7.glb_blk7_en ~
     * glb_blk0_en, then poll corresponding bits in stat2.glb_blk_events_ongoing to '0'.
     */
    for (ch = 0; ch < num_ddrc; ch++) {
        rslt = ddrctl_sw_cinit_global_maint_calibr(ch, 0x0, DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Disable global maintenance calibration activities failed");
            return false;
        }
    }

    /** -# Disable rank maintenance calibration activities of all ranks of all channels through:
     * rank 0 related registers are in pasctl8.rank_blk0_en ~ rank_blk7_en,
     * rank 1 related registers are in pasctl8.rank_blk8_en ~ rank_blk15_en,
     * rank 2 related registers are in pasctl8.rank_blk16_en ~ rank_blk23_en,
     * rank 3 related registers are in pasctl8.rank_blk24_en ~ rank_blk31_en.
     * Then poll corresponding bits in stat3.rank_blk_events_ongoing to '0'.
     */

    for (ch = 0; ch < num_ddrc; ch++) {
        rslt = ddrctl_sw_cinit_rank_maint_calibr(ch, 0x0, DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Disable rank maintenance calibration activities failed");
            return false;
        }
    }

    /** -# Disable dequeue to all ranks of all channels through software command
     * interface command DisDqRef w/ DisRefType set to ‘0’.
     */

    uint8_t ranks = 0xf;

    for (ch = 0; ch < num_ddrc; ch++) {
        rslt = cinit_ddr5_send_disable_dq_refresh(hdlr, (ddrctl_channel_t)ch, ~ranks, ~ranks, 0, 0,
                                                  SW_CMD_DISDQREF_TYPE_PAUSE, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Send Disable De-Queue Refresh command failed");
            return false;
        }
    }


    /** -# Send PREAB to all logical ranks of all ranks of all channels through software command interface
     * command PRE
     */

    rslt = cinit_ddr5_send_preab(hdlr);
                if (rslt != DDRCTL_SUCCESS) {
                    SNPS_ERROR("Send PREab command failed");
        return rslt;
    }

    /** -# Flush REFAB to all ranks of all channels through software command interface command REF_FLUSH.
     * This will send all accumulated postponed refreshes to the ranks.
     */

    for (ch = 0; ch < num_ddrc; ch++) {
        rslt = cinit_ddr5_send_ref_flush(hdlr, (ddrctl_channel_t)ch, ranks);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Error in REF flush command");
            return false;
        }
    }

    /** -# Pause refresh to all ranks of all channels through software command interface command DisDqRef w/
     * DisRefType set to ‘1’.
     */
    for (ch = 0; ch < num_ddrc; ch++) {

        rslt = cinit_ddr5_send_disable_dq_refresh(hdlr, (ddrctl_channel_t) ch, 0, 0, 0, 0,
                                                  SW_CMD_DISDQREF_TYPE_PAUSE, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Error in Disable De-Queue Refresh command");
            return false;
        }
    }

    /** -# Send MPSME to target ranks through software command interface command MRW.
     * Target ranks will be put into MPSM IDLE state.
     */
    uint8_t mr_value;
    DDR5_MR[0].mr2.mpsm = 1;
    mr_value = ddrctl_sw_get_ddr5_mode_reg(hdlr, 0, 2);

    rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 2, mr_value, DDRCTL_FALSE, DDRCTL_FALSE,
                               target_rank, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in seq_ddr5_send_mrw");
        return false;
    }

    /** -# Send REFes to all non-target ranks of all channels through software command interface command REF.
     * They can act as pull-in refreshes to build up more margin.
     */

    rslt = cinit_ddr5_send_refab(hdlr, non_target_rank, DDRCTL_CHANNEL_0);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Send REFAB to all ranks of all channels Error");
        return false;
    }

    /** -# Resume refresh to all non-target ranks of all channels through software command interface command
     * DisDqRef w/ DisRefType set to ‘0’.
     */

    for (ch = 0; ch < num_ddrc; ch++) {

        rslt = cinit_ddr5_send_disable_dq_refresh(hdlr, (ddrctl_channel_t)ch, 0, 0, 0, 0,
                                                  SW_CMD_DISDQREF_TYPE_PAUSE, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Error in Disable De-Queue Refresh command");
            return false;
        }
    }

    /** -# Enable dequeue to all non-target ranks of all channels through software command interface command
     * DisDqRef.
     */

    for (ch = 0; ch < num_ddrc; ch++) {

        rslt = cinit_ddr5_send_disable_dq_refresh(hdlr, (ddrctl_channel_t)ch, 0, ~non_target_rank,
                                                  0, ~non_target_rank, SW_CMD_DISDQREF_TYPE_PAUSE, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Error in Disable De-Queue Refresh command");
            return false;
        }
    }

    SNPS_TRACE("Leaving");
    return true;
}


/**
 * @brief Execute Maximum Power Saving Mode exit sequence
 *
 * @param target_rank
 * @return true
 * @return false
 */
bool dwc_ddrctl_cinit_sw_seq_mpsm_ddr5_exit(uint8_t target_rank)
{
    ddrctl_error_t  rslt;
    ddrctl_sw_cmd_last_t last_cmd_info;
    uint8_t         num_ddrc = cinit_get_num_channels_enable();
    uint8_t         ch;
    uint8_t         rank;
    uint8_t         rank_bit;
    uint8_t         rank_target_iter;
    uint8_t         port;
    uint32_t        store_rank_maint_calibr[num_ddrc];
    uint8_t         store_glob_maint_calibr[num_ddrc];

    /**
     * <ol>
     * <li> Ensure that all active ranks are not in any low power mode (auto power-down,
     * auto/software/hardware self-refresh) through PWRCTL.powerdown_en, PWRCTL.selfref_en,
     * PWRCTL.selfref_sw, HWLPCTL.hw_lp_en, STAT.operating_mode
     */
    SNPS_LOG("[1] Verify that all ranks are in Normal Power mode");
    if (cinit_verify_normal_op_mode(DDRCTL_CHANNEL_ALL) == DDRCTL_FALSE) {
        SNPS_ERROR("Error System is not in normal operation mode");
        return DDRCTL_ERROR;
    }

    /**
     * <li> Disable global maintenance calibration activities
     *        - disable pasctl7[7, 0] for all channels
     *        - poll corresponding bits in stat2.glb_blk_events_ongoing to '0'
     */
    SNPS_LOG("[2] Disable global maintenance calibration activities of all channels");
    for (ch = 0; ch < num_ddrc; ch++) {
        store_glob_maint_calibr[ch] = ddrctl_sw_cinit_get_global_maint_calibr(ch);
        rslt = ddrctl_sw_cinit_global_maint_calibr(ch, 0x0, DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Disable global maintenance calibration activities failed");
            return false;
        }
    }

    /**
     * <li> Disable rank maintenance calibration activities of all ranks of all channels
     *   - set pasctl8 to 0 for the corresponding ranks
     *      - rank 0 related registers are in pasctl8[ 7,  0]
     *      - rank 1 related registers are in pasctl8[15,  8]
     *      - rank 2 related registers are in pasctl8[23, 16]
     *      - rank 3 related registers are in pasctl8[31, 24]
     *   - poll corresponding bits in stat3.rank_blk_events_ongoing to '0'
     */
    SNPS_LOG("[3] Disable rank maintenance calibration activities of all ranks of all channels");
    for (ch = 0; ch < num_ddrc; ch++) {
        store_rank_maint_calibr[ch] = ddrctl_sw_cinit_get_rank_maint_calibr(ch);
        rslt = ddrctl_sw_cinit_rank_maint_calibr(ch, 0x0, DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Disable rank maintenance calibration activities failed");
            return false;
        }
    }

    last_cmd_info = SW_CTRL_NOT_LAST_CMD;
    rank_target_iter = target_rank;

    /**
     * <li> Exit MPSM for all target ranks one by one through the following sub-sequence
     */
    SNPS_LOG("[4] Exit MPSM for all target ranks one by one through the following sub-sequence");
    for (rank = 0; rank < 4; rank++) {
        if (SNPS_GET_BIT(rank_target_iter, rank) != 1) {
            continue; // Bit not set
        }
        rank_bit = 1 << rank;
        SNPS_SET_BIT(rank_target_iter, rank, 0);

        /**
         *   a. Send MPSMX to target ranks through the software command interface command MRW
         */
        SNPS_LOG("[4.a] Send MPSMX to rank %d through the software command interface command MRW", rank);
        uint8_t mr_value;
        DDR5_MR[0].mr2.mpsm = 0;
        mr_value = ddrctl_sw_get_ddr5_mode_reg(hdlr, 0, 2);

        rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_ALL, 2, mr_value, DDRCTL_FALSE, DDRCTL_FALSE,
                                rank_bit, last_cmd_info);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Error in seq_ddr5_send_mrw");
            return false;
        }

        /**
         *   b. Send MPSMX_Done to target ranks through software command interface command OP_CTRL
         *      Target ranks will be out of MPSM IDLE state
         */
        SNPS_LOG("[4.b] Send MPSMX_Done to rank %d through software command interface command OP_CTRL", rank);
        rslt = cinit_ddr5_send_op_ctrl(hdlr, DDRCTL_CHANNEL_ALL, 0, 0, 0, rank_bit, 0, 0, last_cmd_info);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Send Operation Control command failed");
            return false;
        }

        /**
         *   c. Send TCR update to target ranks through software command interface command MRR 0x4
         */
        SNPS_LOG("[4.c] Send TCR update to rank %d through software command interface command MRR 0x4", rank);
        rslt = cinit_ddr5_send_mrr(hdlr, DDRCTL_CHANNEL_ALL, rank, 0x4, DDRCTL_FALSE,
                                DDRCTL_DISABLE, DDRCTL_ENABLE, DDRCTL_ENABLE, last_cmd_info);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Error sending MRR");
            return false;
        }

        // Check if this is the last rank to send the last command
        if (rank_target_iter == 0) {
            last_cmd_info = SW_CTRL_LAST_CMD;
        }

        /**
         *   d. Resume refresh to target ranks through software command interface command DisDqRef
         */
        SNPS_LOG("[4.d] Resume refresh to rank %d through software command interface command DisDqRef", rank);
        rslt = cinit_ddr5_send_disable_dq_refresh(hdlr, DDRCTL_CHANNEL_ALL, rank_bit, rank_bit, 0, 0,
                                                  SW_CMD_DISDQREF_TYPE_PAUSE, last_cmd_info);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Error in Send Disable Dequeue Refresh command");
            return false;
        }
    }

    /**
     * <li> Enable rank maintenance calibration activities of active ranks if necessary
     */
    SNPS_LOG("[5] Enable rank maintenance calibration activities of active ranks if necessary");
    for (ch = 0; ch < num_ddrc; ch++) {
        rslt = ddrctl_sw_cinit_rank_maint_calibr(ch, store_rank_maint_calibr[ch], DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Enable rank maintenance calibration activities failed");
            return false;
        }
    }

    /**
     * <li> Enable global maintenance calibration activities if necessary
     */
    SNPS_LOG("[6] Enable global maintenance calibration activities if necessary");
    for (ch = 0; ch < num_ddrc; ch++) {
        rslt = ddrctl_sw_cinit_global_maint_calibr(ch, store_glob_maint_calibr[ch], DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Enable global maintenance calibration activities failed");
            return false;
        }
    }

    /**
     * <li> Enable low power activities to target or other ranks through pwrctl.powerdown_en, pwrctl.selfref_en,
     *  pwrctl.selfref_sw, and HWLPCTL.hw_lp_en if necessary
     */
    SNPS_LOG("[7] Enable low power activities to target or other ranks if necessary");

    /**
     * <li> Enable dequeue to target ranks through software command interface command DisDqRef
     */
    SNPS_LOG("[8] Enable dequeue to target ranks through software command interface command DisDqRef");

    /**
     * <li> Enable AXI ports
     */
    SNPS_LOG("[9] Enable ports");
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports disable failed");
        return rslt;
    }

    /**
     * <li> Enable ECC scrubber if desired, only required if ECC scrubber instantiated
     * </ol>
     */
    SNPS_LOG("[10] Enable sending scrubbing traffic to target ranks if necessary");
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_ENABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber enable failed");
        return false;
    }
    return true;
}

bool dwc_ddrctl_cinit_sw_seq_mpsm_ddr4_entry(void)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t ch;
    PWRCTL_t *const ptrPWRCTL[2] = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };

    /** -#
    * Set PCTRL.port_en to '0' to block the AXI ports from taking any transactions, then poll
    * PSTAT.rd_port_busy_n to '0' and PSTAT.wr_port_busy_n to '0'. Wait until all AXI ports are
    * idle.
    */
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_DISABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports disable failed");
        return false;
    }

    /** -# Disable the Scubber for all channels and wait until is idle
     * This is only required if SBR is instantiated
     */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_DISABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber disable failed");
        return false;
    }

    /** -#
     * Set OPCTRL1.dis_hif to '1', so that no new commands are accepted by the controller, then poll
     * OPCTRLCAM.dbg_wr_q_empty to '1', OPCTRLCAM.wr_data_pipeline_empty to '1',
     * OPCTRLCAM.dbg_rd_q_empty to '1', and OPCTRLCAM.rd_data_pipeline_empty to '1'.
     */

    for (ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_set_opctrl1(0, 1, ch) == false) {
            SNPS_ERROR("Error in seq_set_opctrl1");
            return false;
    }
    }
    if (dwc_ddrctl_cinit_seq_wait_opctrlcam_empty(DWC_DDRCTL_MAX_APB_POLLING) == false) {
        SNPS_ERROR("Error in seq_wait_opctrlcam_empty");
        return false;
    }

    for (ch = 0; ch < num_ddrc; ch++) {
        ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptrPWRCTL[ch]->selfref_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
    }

    REGB_DDRC_CH0.rfshctl0.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + RFSHCTL0);
    REGB_DDRC_CH0.rfshctl0.dis_auto_refresh = 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + RFSHCTL0, REGB_DDRC_CH0.rfshctl0.value);;

    REGB_DDRC_CH0.mstr3.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + MSTR3);

    /** -# If geardown enabled, go into SSR and  set geardown_mode=0 */
    if (REGB_DDRC_CH0.mstr3.geardown_mode != 0) {

        for (ch = 0; ch < num_ddrc; ch++) {
            ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptrPWRCTL[ch]->selfref_sw = 1;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
            if (dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, ch, 3) == false) {
                SNPS_ERROR("Error in seq_poll_operating_mode");
                return false;
        }
        }

          SNPS_LOG("Setting mstr3.geardown_mode->0",NULL);

        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        REGB_DDRC_CH0.mstr3.geardown_mode = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + MSTR3, REGB_DDRC_CH0.mstr3.value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }

        for (ch = 0; ch < num_ddrc; ch++) {
            ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptrPWRCTL[ch]->selfref_sw = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
        }
     }

    //Wait for normal operation mode
    for (ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, ch, 1) == false) {
            SNPS_ERROR("Error in seq_poll_operating_mode");
            return false;
        }
    }


    /** -# Start MPSM entry using pwrctl.mpsm_en=1 */
    for (ch = 0; ch < num_ddrc; ch++) {
        ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptrPWRCTL[ch]->mpsm_en = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
    }

    //Wait for Operating Mode = 'b1xx; MPSM Mode (DDR4 only)
    for (ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, ch, 6) == false) {
            SNPS_ERROR("Error in seq_poll_operating_mode");
            return false;
    }
    }

    SNPS_TRACE("Leaving");
    return true;
}

bool dwc_ddrctl_cinit_sw_seq_mpsm_ddr4_exit(void)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t ch;
    PWRCTL_t *const ptrPWRCTL[2] = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };

    /** -# Once the DDRCTL puts the DDR SDRAM devices in maximum power saving mode, the DDRCTL
    *      automatically exits maximum power saving mode when pwrctl.mpsm_en is reset to ’0’.
    **/

    for (ch = 0; ch < num_ddrc; ch++) {
        ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptrPWRCTL[ch]->mpsm_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
    }

    /** -# wait for normal operation mode */
    for (ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, ch, 1) == false) {
            SNPS_ERROR("Error in seq_poll_operating_mode");
            return false;
    }
    }

    /** -# After exiting Maximum Power Saving Mode, Geardown must be enabled back by using Self-Refresh, if it
    *     was disabled before MPSM Entry.
    **/
    /** -# After setting PWRCTL_.mpsm_en to ’0’, put SDRAM in Self-Refresh mode by setting ptrPWRCTL[ch]->selfref_
    *     sw to ’1’ and polling STAT.operating_mode.
    **/
    /** -# Enable back Geardown Mode by setting mstr3.geardown_mode back to ’1’. */
    /** -# Wake SDRAM up from Self-Refresh by setting ptrPWRCTL[ch]->selfref_sw to ’0’ and polling STAT.operating_
    *     mode. (Geardown is enabled immediately after Self-Refresh Exit)
    **/
    for (ch = 0; ch < num_ddrc; ch++) {
        if(QDYN.geardown_mode[ch]) {

            if (dwc_ddrctl_cinit_seq_enter_sw_selfref(ch) == false) {
                SNPS_ERROR("Error in seq_enter_sw_selfref");
                return false;
            }

            if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_pre_qdyn_write");
                return false;
            }
            REGB_DDRC_CH0.mstr3.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + MSTR3);
            REGB_DDRC_CH0.mstr3.geardown_mode = 1;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + MSTR3, REGB_DDRC_CH0.mstr3.value);
            if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_post_qdyn_write");
                return false;
            }

            ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptrPWRCTL[ch]->selfref_sw = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
            if (dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, ch, 1) == false) {
                SNPS_ERROR("Error in seq_poll_operating_mode");
                return false;
            }

        }
    }

    /** -# Set dis_hif=0 to enable back the traffic */
    for (ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_set_opctrl1(0, 0, ch) == false) {
            SNPS_ERROR("Error in seq_set_opctrl1");
            return false;
        }
    }

    /** -# Write PCTRL.port_en = 1 AXI ports are no longer blocked from taking transactions.*/
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports enable failed");
        return false;
    }

    /** -# Enable the Scubber for all channels
     * This is only required if SBR is instantiated
     */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_ENABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber enable failed");
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
}


/**
 * @brief Disable maximum power saving sequence
 */
bool dwc_ddrctl_cinit_sw_seq_max_power_saving_disable(void)
{
    bool rslt = false;
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        rslt = dwc_ddrctl_cinit_sw_seq_mpsm_ddr4_exit();
    }
#endif
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        uint8_t target_rank = 1;
        rslt = dwc_ddrctl_cinit_sw_seq_mpsm_ddr5_exit(target_rank);
    }
#endif
    return rslt;
}

/**
 * @brief Enable maximum power saving sequence
 */
bool dwc_ddrctl_cinit_sw_seq_max_power_saving_enable(void)
{
    bool rslt = false;
    SNPS_TRACE("Entering");
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        rslt = dwc_ddrctl_cinit_sw_seq_mpsm_ddr4_entry();
    }
#endif
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        rslt = dwc_ddrctl_cinit_sw_seq_mpsm_ddr5_entry(1);
    }
#endif

    SNPS_TRACE("Leaving");
    return rslt;
}


/**
 * @brief Change clock frequencies sequence
 * @note Not yet implemented
 */

inline bool dwc_ddrctl_cinit_sw_seq_change_clock_frequency(void)
{
#if defined(MEMC_DDR4) || defined(MEMC_DDR5)
    return true;
#else /* MEMC_DDR4 || MEMC_DDR5 */
    return false;
#endif /* MEMC_DDR4 || MEMC_DDR5 */
}


/**
 * @brief Sequence to put PHY into LP3/IO Retention
 * @param enter_retention - true:Enter IO retention , false:Exit IO retention
 */
bool dwc_ddrctl_cinit_phy_lp3_io_retention(bool enter_retention)
{
    SNPS_TRACE("Entering");
    uint8_t  dfi_phymstr_en;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    ddrctl_error_t   rslt;

    if (enter_retention == true) {
        SNPS_LOG("Enter LP3/IO retention flow");

      if (IS_DDR4) {
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) { //0x1f
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        REGB_DDRC_CH0.dfimisc.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DFIMISC);
        REGB_DDRC_CH0.dfimisc.dfi_frequency = 0x1f; /*  PHY Deep Sleep / Retention Enable */
        REGB_DDRC_CH0.dfimisc.dfi_init_complete_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIMISC, REGB_DDRC_CH0.dfimisc.value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }

        /* disable PHYMSTR - avoid PHYMSTR in parallel with frequency change procedure */
        REGB_DDRC_CH0.dfiphymstr.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DFIPHYMSTR);
        dfi_phymstr_en = REGB_DDRC_CH0.dfiphymstr.dfi_phymstr_en;
        REGB_DDRC_CH0.dfiphymstr.dfi_phymstr_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIPHYMSTR, REGB_DDRC_CH0.dfiphymstr.value);

        /* quasi dynamic write to set dfimisc.dfi_init_start */
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        REGB_DDRC_CH0.dfimisc.dfi_init_start = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIMISC, REGB_DDRC_CH0.dfimisc.value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
        /* wait for dfi_init complete to go low */
        if (dwc_ddrctl_cinit_seq_poll_dfi_init_complete(0, 5 * DWC_DDRCTL_MAX_APB_POLLING, 0) == false) {
            SNPS_ERROR("Error in seq_poll_dfi_init_complete");
            return false;
        }
        /* quasi dynamic write to set dfimisc.dfi_init_start=0 */
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        REGB_DDRC_CH0.dfimisc.dfi_init_start = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIMISC, REGB_DDRC_CH0.dfimisc.value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
        /* wait for dfi_init complete to go high */
        if (dwc_ddrctl_cinit_seq_poll_dfi_init_complete(1, 5 * DWC_DDRCTL_MAX_APB_POLLING, 0) == false) {
            SNPS_ERROR("Error in seq_poll_dfi_init_complete");
            return false;
        }
      }

        if(IS_DDR5) {
            /* set PASCTL37.dch_sync_mode to 1 */
            if (num_ddrc == 2) {
             if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(1) == false) {
                 SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
                 return false;
             }
            }
           /* execute DFIFC cmd to set dfi_init_start to 1 */
            rslt = cinit_ddr5_send_dfi_freq_chg_ctrl(hdlr, DDRCTL_CHANNEL_0, 1, 0,
                                                 MEMC_FREQ_RATIO, 0x1f, 0, SW_CTRL_LAST_CMD);
            if (rslt != DDRCTL_SUCCESS) {
                SNPS_ERROR("Error happens when sending DFIFC cmd to set dfi_init_start");
                return false;
            }

           /* execute DFIFC cmd to clear dfi_init_start */
            rslt = cinit_ddr5_send_dfi_freq_chg_ctrl(hdlr, DDRCTL_CHANNEL_0, 0, 1, MEMC_FREQ_RATIO,
                                                    0x1f, 0, SW_CTRL_LAST_CMD);
            if (rslt != DDRCTL_SUCCESS) {
                SNPS_ERROR("Error happens when sending DFIFC cmd to clear dfi_init_start");
                return false;
            }

           /* set PASCTL37.dch_sync_mode to 0 */
            if (num_ddrc == 2) {
                if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(0) == false) {
                    SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
                    return false;
                }
            }
        }

        if (IS_DDR4) {
          /* put dfi_phymstr_en back to original value */
          REGB_DDRC_CH0.dfiphymstr.dfi_phymstr_en = dfi_phymstr_en;
          dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIPHYMSTR, REGB_DDRC_CH0.dfiphymstr.value);
        }

        SNPS_LOG("LP3/IO retention entered");
    } else {
        SNPS_LOG("Exit LP3/IO retention");

        /* Program dfimisc.dfi_init_complete_en to 0 */
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        REGB_DDRC_CH0.dfimisc.dfi_init_complete_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIMISC, REGB_DDRC_CH0.dfimisc.value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }

        SNPS_LOG("LP3/IO retention exited");
    }

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to poll cmdstat.cmd_rslt.
 * @param timeout_us - max apd read time
 * @param size of the value
 * @param position - lsb start bit position of value in cmd_rslt
 * @param Value - Expected value
 */
bool dwc_ddrctl_cinit_seq_poll_cmd_rslt(uint32_t timeout_us, uint8_t  size, uint8_t position, uint32_t value)
{
    SNPS_TRACE("Entering");
    uint32_t actual_val;

    // wait for cmdstat.cmd_rslt
    REGB_DDRC_CH0.cmdstat.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + CMDSTAT);
    actual_val = (((REGB_DDRC_CH0.cmdstat.cmd_rslt) & DWC_DDRCTL_BITMASK(((size + position) - 1), position)) >> (position));

    SNPS_LOG("ptrCMDSTAT->cmd_rslt=%0x actual_val = %u", REGB_DDRC_CH0.cmdstat.value, actual_val);

    for (uint32_t rd_cnt = timeout_us; actual_val != value ; rd_cnt--) {
        if (!rd_cnt) {
            SNPS_ERROR("Polling timeout, ptrCMDSTAT.cmd_rslt[%u:%u] = %u, waiting for cmd_rslt[%u:%u]=%u", ((size + position) - 1), position, actual_val, ((size + position) - 1), position, value);
            return false;
        }
        REGB_DDRC_CH0.cmdstat.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + CMDSTAT);
        actual_val = (((REGB_DDRC_CH0.cmdstat.cmd_rslt) & DWC_DDRCTL_BITMASK(((size + position) - 1), position)) >> (position));
        SNPS_LOG("ptrCMDSTAT->cmd_rslt=%0x actual_val = %u", REGB_DDRC_CH0.cmdstat.value, actual_val);
    }
    if (REGB_DDRC_CH0.cmdstat.cmd_err) {
        SNPS_ERROR("ptrCMDSTAT[0]->cmd_err set");
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to perform any steps before calling phyinit.
 * @detail in particular any automatic HW low power must be blocked.
 */
bool dwc_ddrctl_cinit_pre_phyinit(void)
{
    SNPS_TRACE("Entering");
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    PWRCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };
    DFIMISC_t *const ptrDFIMISC = &REGB_DDRC_CH0.dfimisc;
    RFSHCTL0_t *const ptrRFSHCTL0 = &REGB_DDRC_CH0.rfshctl0;
    DFIUPD0_t *const ptrDFIUPD0 = &REGB_DDRC_CH0.dfiupd0;
    DERATECTL6_t *const ptrDERATECTL6 = &REGB_DDRC_CH0.deratectl6;
    uint32_t num_dwc_ddrctl=1;

#ifdef CINIT_DDR5
#ifdef DDRCTL_SINGLE_INST_DUALCH
    num_dwc_ddrctl=2; // two controller instances
#endif // DDRCTL_SINGLE_INST_DUALCH
#endif

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr[ch]->powerdown_en = 0;
        ptr[ch]->en_dfi_dram_clk_disable = 0;
        ptr[ch]->selfref_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr[ch]->value);
    }
    for (uint32_t ch = 0; ch < num_dwc_ddrctl; ch++) {
	    /// - disable auto refresh before training
	    ptrRFSHCTL0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0);
	    ptrRFSHCTL0->dis_auto_refresh = 1;
	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0 ,ptrRFSHCTL0->value);

	    /// - In DDR5, program DQSOSCCFG0.dis_dqsosc_srx to 1'b1 and ZQCTL2.dis_srx_zqcl to 1'b1.
	    DQSOSCCFG0_t *const ptrDQSOSCCFG0 = &REGB_DDRC_CH0.dqsosccfg0;
	    ZQCTL2_t *const ptrZQCTL2 = &REGB_DDRC_CH0.zqctl2;

	    ptrDQSOSCCFG0->value = dwc_ddrctl_cinit_io_read32 (REGB_DDRC_CH_OFFSET(ch) + DQSOSCCFG0);
	    ptrZQCTL2->value = dwc_ddrctl_cinit_io_read32 (REGB_DDRC_CH_OFFSET(ch) + ZQCTL2);
	    if (IS_DDR5)
	        ptrDERATECTL6->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6);

	    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
		    SNPS_LOG("Error in seq_pre_qdyn_write");
		    return false;
	    }

	    ptrDQSOSCCFG0->dis_dqsosc_srx = 1;
	    ptrZQCTL2->dis_srx_zqcl = 1;
	    ptrDFIUPD0->dis_auto_ctrlupd = 1;
	    ptrDFIUPD0->dis_auto_ctrlupd_srx = 1;
	    ptrDERATECTL6->dis_mrr4_tcr_srx = 1;

	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DQSOSCCFG0, ptrDQSOSCCFG0->value);
	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL2, ptrZQCTL2->value);
	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptrDFIUPD0->value);
	    if (IS_DDR5)
	        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6, ptrDERATECTL6->value);

	    if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
		    SNPS_LOG("Error in seq_post_qdyn_write");
		    return false;
	    }

	    // qdyn write to set DFIMISC.dfi_init_complete_en to 0
	    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
		    SNPS_LOG("Error in seq_pre_qdyn_write");
		    return false;
	    }
	    ptrDFIMISC->dfi_init_complete_en = 0;
#ifdef CINIT_DDR4
	    ptrDFIMISC->dfi_reset_n = 1;
#endif // CINIT_DDR4
	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptrDFIMISC->value);
	    if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
		    SNPS_LOG("Error in seq_post_qdyn_write");
		    return false;
	    }
    }
    /** -  Disable any VIP checkers for PHY training (simulation only). */
    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING)
        dwc_ddrctl_cinit_io_training_chk_enable(0);
    SNPS_TRACE("Leaving");
    return true;
}


/**
 * @brief method call after PHY training has completed
 */
bool dwc_ddrctl_cinit_post_phyinit(void)
{
    RFSHCTL0_t *const ptrRFSHCTL0 = &REGB_DDRC_CH0.rfshctl0;
    uint32_t num_dwc_ddrctl=1;

#ifdef CINIT_DDR5
#ifdef DDRCTL_SINGLE_INST_DUALCH
    num_dwc_ddrctl=2; // two controller instances
#endif // DDRCTL_SINGLE_INST_DUALCH
#endif
#ifdef PHYINIT
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        // Directly access PHY registers here
        // MicroContMuxSel
        physetup_io_write16(MICROCONTMUXSEL, MICROCONTMUXSEL_CSR_CONTROL_DISABLE);
        // Disable the DFIPHYUPD issued by PHY as the request is issued by DDRC for DDR5
        physetup_io_write16(0x20021, 0);
        if (IS_NODIMM) {
            // see BUGZILLA_13372
            physetup_io_write16(0x180aa, 0); // PptCtlStatic::NoX4onUpperNibbleTg0/1/2/3=0
            physetup_io_write16(0x190aa, 0); // PptCtlStatic::NoX4onUpperNibbleTg0/1/2/3=0
        }
        // MicroContMuxSel
        physetup_io_write16(MICROCONTMUXSEL, MICROCONTMUXSEL_CSR_CONTROL_ENABLE);
        // MicroContMuxSel
         physetup_io_write16(MICROCONTMUXSEL, MICROCONTMUXSEL_CSR_CONTROL_DISABLE);
        // Setting PGCR.DfiCtrlRxFifoRst to 1
        // This register must be set for the rolling order of read commands.
	if (CFG->ddrPhyType_m == DWC_DDR5_PHY) {
		physetup_io_write16(0x80022,0x2);
		physetup_io_write16(0x81022,0x2);
		physetup_io_write16(0x82022,0x2);
		physetup_io_write16(0x83022,0x2);
		physetup_io_write16(0x84022,0x2);
		physetup_io_write16(0x88022,0x2);
		physetup_io_write16(0x89022,0x2);
		physetup_io_write16(0x8a022,0x2);
		physetup_io_write16(0x8b022,0x2);
		physetup_io_write16(0x8c022,0x2);
	} else {
          physetup_io_write16(0x20005, 0x0006);
	}
        // MicroContMuxSel
        physetup_io_write16(MICROCONTMUXSEL, MICROCONTMUXSEL_CSR_CONTROL_ENABLE);
    }
#endif  // CINIT_DDR5
#endif /* PHYINIT*/

    // if PHY training then apply training result here
    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING ) {
        // Disable the MicroController control of the CSR BUS
        physetup_io_write16(MICROCONTMUXSEL, MICROCONTMUXSEL_CSR_CONTROL_DISABLE);

        if (CFG->phy_training == DWC_PHY_TRAINING) {
            //TODO: DDR5 PHY apply training results is not supported yet. JIRA: P80001562-317970
            if (( CFG->ddrPhyType_m == DWC_DDR54_PHY ) || ( CFG->ddrPhyType_m == DWC_DDR54_PHY_V2 )) {
                if (dwc_ddrctl_cinit_apply_training() == false) {
                    SNPS_ERROR("Error in apply_training");
                    return false;
                }
            }
        }
    }

#ifdef CINIT_DDR5
    if (IS_DDR5) {
        if (IS_UDIMM) {
          // Force ECC DBYTE8/9[7:4] to 'hf after training completes, WORKAROUND: BUGZILLA_13372_uppernibble_x_workaround, JIRA:P80001562-346171
          ddr5_udimm_force_ECC_DBYTE();
        }
    }
#endif  // CINIT_DDR5

    for (uint32_t ch = 0; ch < num_dwc_ddrctl; ch++) {
	    /// - Re-apply auto refresh setting
	    ptrRFSHCTL0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0);
	    ptrRFSHCTL0->dis_auto_refresh = DYN.dis_auto_refresh;
	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0, ptrRFSHCTL0->value);
    }

    /** -  Re-enable any VIP checkers after PHY training */
    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING)
        dwc_ddrctl_cinit_io_training_chk_enable(1);

    return true;
}

/** @brief method to apply training results to the controller
 */
bool dwc_ddrctl_cinit_apply_training(void)
{
    SNPS_TRACE("Entering");

#ifdef CINIT_DDR4
    if (IS_DDR4) {
        if (dwc_ddrctl_apply_training_ddr4() == false) {
            SNPS_ERROR("Error Apply train failed");
            return false;
        }
    }
#endif

#ifdef CINIT_DDR5
    if (IS_DDR5) {
        if (dwc_ddrctl_apply_training_ddr5() == false) {
            SNPS_ERROR("Error Apply train failed");
            return false;
        }
    }
#endif

    SNPS_TRACE("Leaving");
    return true;
}


/**
 * @brief method to perform ddr5 1N/2N mode switch during initialization.
 * @note does nothing in 1:2 mode
 */
bool dwc_ddrctl_cinit_ddr5_1N_2N_mode_init(void)
{
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    ddrctl_status_t ddr5_2n_mode;
    ddrctl_error_t rslt;

    if (2 == MEMC_FREQ_RATIO) {
        return true;
    }

    if (0 == DDR5_MR[0].mr2.ddr5_2n_mode) {
        ddr5_2n_mode = DDRCTL_ENABLE;
    } else {
        ddr5_2n_mode = DDRCTL_DISABLE;
    }

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        rslt = cinit_ddr5_send_ctl_dfi_2n_mode(hdlr, (ddrctl_channel_t)ch, ddr5_2n_mode,
                                               SW_CTRL_LAST_CMD);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Error in seq_ddr5_send_mrw");
            return false;
        }
    }

    return true;
}

/**
 * @brief method to set quasi dynamic register pasctl0.init_done
 * @param init_done value to set
 * @param ch channel number
 */
bool dwc_ddrctl_cinit_ddr5_init_done(uint32_t init_done, uint32_t ch)
{
    SNPS_TRACE("Entering");
    uint32_t lcl_ch=0;
#ifdef CINIT_DDR5
#ifdef DDRCTL_SINGLE_INST_DUALCH
    if (ch==1)
        lcl_ch = 1;
#endif
#endif

    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(lcl_ch) == false) {
        SNPS_ERROR("Error in seq_pre_qdyn_write");
        return false;
    }
    REGB_DDRC_CH0.pasctl0.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PASCTL0);
    REGB_DDRC_CH0.pasctl0.init_done = init_done;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL0, REGB_DDRC_CH0.pasctl0.value);
    if (dwc_ddrctl_cinit_seq_post_qdyn_write(lcl_ch) == false) {
        SNPS_ERROR("Error in seq_post_qdyn_write");
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to set pasctl37.dch_sync_mode
 * @param mode value to set
 */
bool dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(uint32_t mode)
{
    SNPS_TRACE("Entering");
#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
    REGB_DDRC_CH0.pasctl37.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + PASCTL37);
    REGB_DDRC_CH0.pasctl37.dch_sync_mode = mode;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + PASCTL37, REGB_DDRC_CH0.pasctl37.value);
#endif // DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to use SCI to send MPC command
 * @{
 */
bool dwc_ddrctl_cinit_seq_ddr5_mpc(void)
{
    ddrTimingParameters_t   *timing = &hdlr->timingParams_m[0][0];
    ddrctl_status_t         multi_cyc_cs = DDRCTL_ENABLE;
    ddrctl_error_t          rslt;
    uint8_t                 i;
    uint8_t                 op[6];
    uint8_t                 active_ranks_map;
    uint32_t t_mpc_delay_ns = (timing->ddr5_tmpc_delay_tck * SPD.tck_ps[0]) / 1000;


    if (CFG->phy_training == DWC_PHY_TRAINING) {
      multi_cyc_cs = DDRCTL_DISABLE;
    } else {
      if ((IS_LRDIMM) || ((IS_RDIMM) && (0 == DDR5_MR[0].mr2.ddr5_2n_mode))) {
          multi_cyc_cs = DDRCTL_DISABLE;
      } else {
          multi_cyc_cs = DDRCTL_ENABLE;
      }
    }

    active_ranks_map = REGB_DDRC_CH0.mstr0.active_ranks;

    /// - MPC tCCD/tDLLK
    op[0] = 0x8 << 4 | DDR5_MR[0].mr13.tccd_l;
    /// -  MPC DLL RESET
    op[1] = 0x2;
    /// -  MPC ZQSTART
    op[2] = 0x5;
    /// - MPC ZQLAT
    op[3] = 0x4;
    /// -  MPC 1N/2N mode
    op[4] = (DDR5_MR[0].mr2.ddr5_2n_mode == 1) ? 0x9 : 0x8;
    /// - MPC RTT PARK
    op[5] = (0xb << 3) | (DDR5_MR[0].mr34.rtt_park);

    for (i = 0; i < sizeof(op); i++) {
        rslt = cinit_ddr5_send_mpc(hdlr, DDRCTL_CHANNEL_0, DDRCTL_FALSE, op[i], DDRCTL_DISABLE,
                                   active_ranks_map, multi_cyc_cs, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Send MPC command failed");
            return false;
        }

        // If ZQSTART or ZQLAT command wait
        if (0x4 == op[i]){
            dwc_ddrctl_cinit_io_nsleep(timing->ddr5_tzqlat_ps / 1000);
        }
        else if (0x5 == op[i]) {
            dwc_ddrctl_cinit_io_nsleep(timing->ddr5_tzqcal_ps / 1000);
        } else {
           dwc_ddrctl_cinit_io_nsleep(t_mpc_delay_ns);
        }

    }

    return true;
    /// @}
}

/**
 * @brief DDR5 NODIMM/UDIMM DRAM initialization when PHY is in skip training
 */
bool dwc_ddrctl_cinit_seq_ddr5_dram_initialization(void)
{
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[0][0];
    ddrctl_error_t rslt;

    // set dch_sync_mode to 1
    if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(1) == false) {
        SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
        return false;
    }
    // wait tINIT4
    dwc_ddrctl_cinit_io_usleep(timing->ddr5_tinit4_us);
    // NOP command for a minimum of tINIT5

    //Force CS Low
    rslt = cinit_ddr5_send_force_cs(hdlr, DDRCTL_CHANNEL_0, 0xf, 0x0, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("[Ch %u] Send Force Chip Select reset to all ranks", 0);
        return false;
    }

    dwc_ddrctl_cinit_io_usleep(1);

    //Release Force CS Low
    rslt = cinit_ddr5_send_force_cs(hdlr, DDRCTL_CHANNEL_0, 0, 0xf, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("[Ch %u] Send Force Chip Select reset to all ranks", 0);
        return false;
    }

    // wait min of tXPR=tRFC1
    dwc_ddrctl_cinit_io_nsleep(timing->ddr5_trfc1_ps/1000);
    // send MPC commands
    if (dwc_ddrctl_cinit_seq_ddr5_mpc() == false) {
        SNPS_ERROR("Error in seq_ddr5_mpc");
        return false;
    }
    // program MR registers through SCI commands
    if (dwc_ddrctl_cinit_seq_ddr5_prm_mr() == false) {
        SNPS_ERROR("Error in seq_ddr5_prm_mr");
        return false;
    }
    // set dch_sync_mode to 0
    if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(0) == false) {
        SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
        return false;
    }

    return true;
}

/**
 * @brief method to initialize DDR5 RCD via software command interface
 * @{
 */
bool dwc_ddrctl_cinit_seq_ddr5_dimm_initialization(void)
{
    ddrTimingParameters_t   *timing;
    ddrctl_error_t          rslt;
    ddrctl_bool_t           dual_die_pkg;
    ddrctl_bool_t           ctrl_word;
    uint32_t                op;
    uint32_t                t_mrc_ns;
    uint32_t                t_mrd_l2_ns;
    uint8_t                 active_ranks_map;
    uint8_t                 sg_id;
    uint8_t                 fg_sg_id;
    uint32_t                t_tstab_max_ns;

    active_ranks_map = 0xf;
    ctrl_word = DDRCTL_TRUE;
    dual_die_pkg = DDRCTL_FALSE;
    timing = &hdlr->timingParams_m[0][0];

    /// - Wait tstab01 before sending MR commands
    t_tstab_max_ns = timing->ddr5_rcd_tstab01_max_ps/1000;
    // DWC_DDRCTL_P80001562_279642_WORKAROUND manually wait for tstab01 before MR commands
    dwc_ddrctl_cinit_io_nsleep(t_tstab_max_ns);

    /// - Calculate the tMRC delays
    t_mrc_ns = (DDR5_MR[0].mr2.ddr5_2n_mode == 0) ? timing->ddr5_rcd_tmrc_tck : timing->ddr5_rcd_tmrc2n_tck;
    t_mrc_ns = (t_mrc_ns * SPD.tck_ps[0]) / 1000;

    t_mrd_l2_ns = (DDR5_MR[0].mr2.ddr5_2n_mode == 0) ? timing->ddr5_rcd_tmrd_l2_tck : timing->ddr5_rcd_tmrd2n_l2_tck;
    t_mrd_l2_ns = (t_mrd_l2_ns * SPD.tck_ps[0]) / 1000;

    /// - RW04 Release CH_A QRST_A
    op = 0x6; // Release CH_A QRST_A
    rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 4, op, ctrl_word, dual_die_pkg, active_ranks_map, SW_CTRL_NOT_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in seq_ddr5_send_mrw");
        return false;
    }

    /// - Add the tMRC delay between RCD control word access to RW04 and next dram cmd
    dwc_ddrctl_cinit_io_nsleep(t_mrc_ns);

    /// - RW04 Release CH_B QRST_B
    op = 0x8; // Release CH_B QRST_B
    rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 4, op, ctrl_word, dual_die_pkg, active_ranks_map, SW_CTRL_NOT_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in seq_ddr5_send_mrw");
        return false;
    }

    /// - Add the tMRC delay between RCD control word access to RW04 and next dram cmd
    dwc_ddrctl_cinit_io_nsleep(t_mrc_ns);

    /// - RW01 Unlock DRAM I/F
    op =  DDR5_CW.rw01.alert_n_reenable << 7 | DDR5_CW.rw01.alert_n_assertion  << 6 | 1 << 1 | DDR5_CW.rw01.parity_check;
    if (IS_LRDIMM) {
        op = op | 1 << 3; // Unlock Data Buffer: RDIMM->0, LRDIMM->1
    }

    rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 1, op, ctrl_word, dual_die_pkg, active_ranks_map, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in seq_ddr5_send_mrw");
        return false;
    }

    /// - set dch_sync_mode to 1
    if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(1) == false) {
        SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
        return false;
    }
    /// - Send 1 NOP to RCD to Release QCS
    dwc_ddrctl_cinit_io_nsleep(t_mrd_l2_ns);
    rslt = cinit_ddr5_send_nop(hdlr, DDRCTL_CHANNEL_0, 1, active_ranks_map, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in seq_ddr5_send_mrw");
        return false;
    }

    /// - wait tSRX2SRX use DRAMSET1TMG28.t_srx2srx for FREQ0 to wait the correct
    // number of core clk cycles
    dwc_ddrctl_cinit_io_wait_ddrc_clk(QDYN.t_srx2srx[0][0]);
    /// - wait tINIT4
    dwc_ddrctl_cinit_io_usleep(timing->ddr5_tinit4_us);

    /// - NOP command for a minimum of tINIT5
    // Force CS Low
    rslt = cinit_ddr5_send_force_cs(hdlr, DDRCTL_CHANNEL_0, 0xf, 0x0, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("[Ch %u] Send Force Chip Select reset to all ranks", 0);
        return false;
    }

    dwc_ddrctl_cinit_io_usleep(1);

    //Release Force CS Low
    rslt = cinit_ddr5_send_force_cs(hdlr, DDRCTL_CHANNEL_0, 0, 0xf, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("[Ch %u] Send Force Chip Select reset to all ranks", 0);
        return false;
    }

    /// - wait min of tXPR=tRFC1
    dwc_ddrctl_cinit_io_nsleep(timing->ddr5_trfc1_ps/1000);

    /// - send MPC commands
    if (dwc_ddrctl_cinit_seq_ddr5_mpc() == false) {
        SNPS_ERROR("Error in seq_ddr5_mpc");
        return false;
    }

    /// - program MR registers through SCI commands
    if (dwc_ddrctl_cinit_seq_ddr5_prm_mr() == false) {
        SNPS_ERROR("Error in seq_ddr5_prm_mr");
        return false;
    }

    /// - RW11  for latency_adder_nladd_to_all_dram_cmd
    uint32_t active_ranks = REGB_DDRC_CH0.mstr0.active_ranks;


    op = DDR5_CW.rw11.latency_adder_nladd_to_all_dram_cmd;
    rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 0x11, op, ctrl_word, dual_die_pkg, active_ranks_map, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in seq_ddr5_send_mrw");
        return false;
    }

    /// - Add the delay between RCD control word access to RW11 and RW09
    dwc_ddrctl_cinit_io_nsleep(t_mrd_l2_ns);
    /// - RW09
    uint32_t rw09;

    if (SPD.num_dimm == active_ranks) {
        if (IS_LRDIMM) {
            // OP_CODE[3]: LRDIMM enabled,OP_CODE[2]: Disable DCS1_n & QxCS1_n pins for 1 rank dimm
            rw09 = 0x4;
        } else {
            // OP_CODE[3]: RDIMM  enabled, OP_CODE[2]: Disable DCS1_n & QxCS1_n pins for 1 rank dimm
            rw09 = 0xc;
        }
    } else {
        if (IS_LRDIMM) {
            // OP_CODE[3]: LRDIMM enabled
            rw09 = 0x0;
        } else {
            // OP_CODE[3]: RDIMM  enabled
            rw09 = 0x8;
        }
    }
    rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 0x09, rw09, ctrl_word, dual_die_pkg, active_ranks_map, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in seq_ddr5_send_mrw");
        return false;
    }

    dwc_ddrctl_cinit_io_nsleep(t_mrd_l2_ns);

    if ((SPD.num_dimm == active_ranks) && (IS_LRDIMM)) {
        // RW80
        op = 0x20; // OP_CODE[5]: Rank1 disabled
        rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 0x80, op, ctrl_word, dual_die_pkg, active_ranks_map, SW_CTRL_LAST_CMD);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Error in seq_ddr5_send_mrw");
            return false;
        }
    }

    dwc_ddrctl_cinit_io_nsleep(t_mrd_l2_ns);

    /// - RW05 - program operating speed
    dwc_ddr5_speed_grade_t speed_grade;
    uint32_t tck_ps = hdlr->spdData_m.tck_ps[0];
    speed_grade = cinit_ddr5_get_speedgrade_from_tck_avg_min(tck_ps);
    rslt = cinit_ddr5_get_rw05_speed_grade_id(speed_grade, &sg_id);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in get_rw05_speed_grade_id");
        return false;
    }
    rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 0x05, sg_id, ctrl_word, dual_die_pkg, active_ranks_map, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in seq_ddr5_send_mrw");
        return false;
    }

    dwc_ddrctl_cinit_io_nsleep(t_mrd_l2_ns);

    /// - RW06 - program fine granularity operating speed
    rslt = cinit_ddr5_get_rw85_fine_grain_speed_grade_id(tck_ps, &fg_sg_id);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in get_rw85_fine_grain_speed_grade_id");
        return false;
    }
    rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, 0x06, fg_sg_id, ctrl_word, dual_die_pkg, active_ranks_map, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Error in seq_ddr5_send_mrw");
        return false;
    }

    dwc_ddrctl_cinit_io_nsleep(t_mrd_l2_ns);

    // set dch_sync_mode to 0
    if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(0) == false) {
        SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
   /// @}
}

/** @brief method to program DRAM mode registers when using PHY skip training.
 * @{
 */
bool dwc_ddrctl_cinit_seq_ddr5_prm_mr(void)
{
    ddrctl_error_t   rslt;
    uint8_t active_ranks = REGB_DDRC_CH0.mstr0.active_ranks;
    uint8_t i;
    uint8_t addr;
    uint8_t mr_addr_array[] = {0, 2, 4, 5, 6, 8, 15, 34, 35, 37, 38, 40, 45, 50, 52};
    /// MR0, MR2, MR4, MR5, MR6, MR8, MR15, MR34, MR35, MR37, MR38, MR40, MR45, MR50, MR51, MR52

    /// - Setup the MR address/data pairs then loop though the MR settings
    for (i = 0; i < sizeof(mr_addr_array); i++) {
        addr = mr_addr_array[i];
        rslt = cinit_ddr5_send_mrw(hdlr, DDRCTL_CHANNEL_0, addr,
                                    ddrctl_sw_get_ddr5_mode_reg(hdlr, 0, addr),
                                    DDRCTL_FALSE, DDRCTL_FALSE,
                                    active_ranks, SW_CTRL_LAST_CMD);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Error in seq_ddr5_send_mrw");
            return false;
        }
    }
    /// - set dch_sync_mode to 0
    if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(0) == false) {
        SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
        return false;
    }
    return true;
    /// @}  // end brief
}



/** @brief DDR4 DRAM initialization. Only used for RDIMM or LRDIMM
 * When DWC_PHY_SKIP_TRAINING is enabled the Controller will initialize the DRAM
 * MR registers but software must take case of DDR4-RCD control words.
 * To access RCD MR7 is used and address is encoded in the mr_data
 * @note this method is for SKIP training mode only and therefore only programs
 * what is necessary for simulation.
 * @{
 */
bool dwc_ddrctl_cinit_seq_ddr4_dram_initialization(void)
{
    SNPS_TRACE("Entering");
    ddrctl_error_t rslt;
    uint32_t mr_address = 0;
    uint32_t mr_data = 0;
    uint32_t mr_rank = 1;
    uint32_t dimm_type = 0;
    uint32_t cs_mode = 0;
    uint32_t alert_n_reenable = 1;
    uint32_t alert_n_assertion = 1;
    uint32_t nladd;
    uint8_t  op_speed;
    MRCTRL0_t * prt_mrctrl0 = &REGB_DDRC_CH0.mrctrl0;

    /// - RC0A
    mr_address = 0xa;
    rslt = ddrctl_sw_get_ddr4_cw_op_speed_id(hdlr, 0, &op_speed);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Operating Speed id for %d not found", SPD.tck_ps[0]);
        dwc_ddrctl_cinit_exit(1);
    }
    mr_data = mr_address << 4 | op_speed;
    if (dwc_ddrctl_cinit_seq_ddr4_send_mrw(0x7, mr_data, mr_rank, 0) == false) {
        SNPS_ERROR("Error in seq_ddr4_send_mrw");
        return false;
    }
    /// - RC0D
    mr_data = 0;
    mr_address = 0xd;
    dimm_type = (IS_LRDIMM) ? 0 : 1;
    // 0 DIRECT_DUALCS_MODE 1 - DIRECT_QUADCS_MODE
    mr_data = 0;
    cs_mode = (STATIC.active_ranks > 3) ? 1 : 0;
    mr_data = mr_address << 4 | STATIC.dimm_addr_mirr_en << 3 | dimm_type << 2 | cs_mode;
    if (dwc_ddrctl_cinit_seq_ddr4_send_mrw(0x7, mr_data, mr_rank, 0) == false) {
        SNPS_ERROR("Error in seq_ddr4_send_mrw");
        return false;
    }
    /// - RC0F
    mr_data = 0;
    mr_address = 0xf;
    /// - encode adder latency
    switch (DDR4_CW.rc0f.latency_adder_nladd_to_all_dram_cmd) {
    case 0:
        nladd = 4;
        break;
    case 1:
        nladd = 0;
        break;
    case 2:
        nladd = 1;
        break;
    case 3:
        nladd = 2;
        break;
    default:
        nladd = 3;
        break;
    }
    mr_data = mr_address << 4 | nladd;
    if (dwc_ddrctl_cinit_seq_ddr4_send_mrw(0x7, mr_data, mr_rank, 0) == false) {
        SNPS_ERROR("Error in seq_ddr4_send_mrw");
        return false;
    }
    /// - RC0E
    mr_data = 0;
    mr_address = 0xe;
    mr_data = mr_address << 4 | alert_n_reenable << 3 | alert_n_assertion << 2 | STATIC.parity_enable;
    if (dwc_ddrctl_cinit_seq_ddr4_send_mrw(0x7, mr_data, mr_rank, 0) == false) {
        SNPS_ERROR("Error in seq_ddr4_send_mrw");
        return false;
    }
    /// - RC3X
    mr_data = 0;
    mr_address = 0x3;
    mr_data = mr_address << 8 | dwc_ddrctl_cinit_get_rcx3_fg_op_speed();
    if (dwc_ddrctl_cinit_seq_ddr4_send_mrw(0x7, mr_data, mr_rank, 0) == false) {
        SNPS_ERROR("Error in seq_ddr4_send_mrw");
        return false;
    }

    /// - setting sw_init_int low when RCD programming is completed
    prt_mrctrl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + MRCTRL0);
    prt_mrctrl0->sw_init_int = 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + MRCTRL0, prt_mrctrl0->value);

    SNPS_TRACE("Leaving");
    return true;
    /// @}
}



/**
 * @brief method to send DDR4 MRW from APB
 * @param mr_addr mode register address
 * @param mr_data mode register data
 * @param mr_rank mode register rank
 * @param ch channel number
 * @{
 */
bool dwc_ddrctl_cinit_seq_ddr4_send_mrw(uint32_t mr_addr, uint32_t mr_data, uint32_t mr_rank, uint32_t ch)
{
    SNPS_TRACE("Entering");
    MRCTRL0_t *const ptrMRCTRL0[2] = {
        &REGB_DDRC_CH0.mrctrl0,
        &REGB_DDRC_CH1.mrctrl0
    };

    /** - make sure MRSTAT.mr_wr_busy is 0 */
    if (dwc_ddrctl_cinit_seq_poll_mr_wr_busy(0, ch, DWC_DDRCTL_MAX_APB_POLLING) == false) {
        SNPS_ERROR("Error in seq_poll_mr_wr_busy");
        return false;
    }

    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL1, mr_data);

    ptrMRCTRL0[ch]->mr_type = 0; // 0 - MR write, 1 - MR read
    ptrMRCTRL0[ch]->mr_rank = mr_rank;
    ptrMRCTRL0[ch]->sw_init_int = 1;
    ptrMRCTRL0[ch]->mr_addr = mr_addr;
    ptrMRCTRL0[ch]->mr_wr = 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL0, ptrMRCTRL0[ch]->value);
    // if LRDIMM follow databook requirement
    // see 9.1.1 Overview of Mode Register Reads and Writes
    if (IS_LRDIMM) {
        if (dwc_ddrctl_cinit_seq_set_opctrl1(1, 0, ch) == false) {
            SNPS_ERROR("Error in seq_set_opctrl1");
            return false;
        }
        // TODO dis_auto_zq=0
    }

    /** - trigger the MR write */
    ptrMRCTRL0[ch]->mr_wr = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL0, ptrMRCTRL0[ch]->value);

    if (dwc_ddrctl_cinit_seq_poll_mr_wr_busy(0, ch, DWC_DDRCTL_MAX_APB_POLLING) == false) {
        SNPS_ERROR("Error in seq_poll_mr_wr_busy");
        return false;
    }
    if (IS_LRDIMM) {
        if (dwc_ddrctl_cinit_seq_set_opctrl1(0, 0, ch) == false) {
            SNPS_ERROR("Error in seq_set_opctrl1");
            return false;
    }
    }

    SNPS_TRACE("Leaving");
    return true;
    /// @}
}

/**
 * @brief DWC_ddrctl initialization sequence entry point for DDR4/DDR5.
 * Prior to invoking this sequence the CINIT and PHYINT structures must be setup.
 * This can be done by calling dwc_ddrctl_cinit_main and dwc_ddrctl_cinit_begin
 * methods.
 * @{
 */
bool dwc_ddrctl_cinit_seq_initialization(void)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t num_dwc_ddrctl=1;

    PWRCTL_t *const ptrPWRCTL[2]   = {
            &REGB_DDRC_CH0.pwrctl,
            &REGB_DDRC_CH1.pwrctl
    };

#ifdef CINIT_DDR5
#ifdef DDRCTL_SINGLE_INST_DUALCH
	num_dwc_ddrctl=2; // two controller instances
#endif // DDRCTL_SINGLE_INST_DUALCH
#endif // CINIT_DDR5

	/// - Perform power on reset and enable clocks
    if (dwc_ddrctl_cinit_seq_pwr_on_rst() == false) {
        SNPS_ERROR("Error in seq_pwr_on_rst");
        return false;
    }
    /// - initialize the controller register map
    if (dwc_ddrctl_cinit_seq_initialize_ctrl_regs() == false) {
        SNPS_ERROR("Error in seq_initialize_ctrl_regs");
        return false;
    }
    if (IS_DDR5) {
        if (CFG->phy_training == DWC_PHY_SKIP_TRAINING) {
			if (dwc_ddrctl_cinit_seq_set_skip_dram_init(1) == false) {
				SNPS_LOG("Error in seq_set_skip_dram_init");
				return false;
			}
        }
        else {
			if (dwc_ddrctl_cinit_seq_set_skip_dram_init(3) == false) {
				SNPS_LOG("Error in seq_set_skip_dram_init");
				return false;
			}
            if (IS_RDIMM || IS_LRDIMM) {
                DIMMCTL_t *const ptrDIMMCTL = &REGB_DDRC_CH0.dimmctl;

			for (uint32_t ch = 0; ch < num_dwc_ddrctl; ch++) {
				ptrDIMMCTL->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DIMMCTL);
				ptrDIMMCTL->dimm_selfref_clock_stop_mode = 1;
				dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DIMMCTL, ptrDIMMCTL->value);
			}
			}
			for (uint32_t ch = 0; ch < num_ddrc; ch++) {
				ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
				ptrPWRCTL[ch]->selfref_sw = 1;
				dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
			}
		}
    }
    if (IS_DDR4) {
        if (CFG->phy_training == DWC_PHY_SKIP_TRAINING) {
            if (dwc_ddrctl_cinit_seq_set_skip_dram_init(0) == false) {
                SNPS_ERROR("Error in seq_set_skip_dram_init");
                return false;
	    }
	}
        else {
            if (dwc_ddrctl_cinit_seq_set_skip_dram_init(3) == false) {
                SNPS_ERROR("Error in seq_set_skip_dram_init");
                return false;
            }
            for (uint32_t ch = 0; ch < num_ddrc; ch++) {
                ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
                ptrPWRCTL[ch]->selfref_sw = 1;
                dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
        }
	}
    }

    /// - release core_rst_n to the controller
    dwc_ddrctl_cinit_io_ddrc_rstn(true);
#ifdef UMCTL2_INCL_ARB_OR_CHB
    /// - de-assert aresetn
    dwc_ddrctl_cinit_io_aresetn(true);
#endif /* UMCTL2_INCL_ARB_OR_CHB */
    /// - load uCode needed for DDR5
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        dwc_ddrctl_cinit_io_wait_ddrc_clk(1); // required for simulation only (if backdoor APB writes is enabled)
        dwc_ddrctl_cinit_prgm_ucode(CFG);
        dwc_ddrctl_cinit_prgm_cfgbuf(CFG);
    }
#endif
    /// - Perform PHY initialization sequence.
    if (dwc_ddrctl_cinit_pre_phyinit() == false) {
        SNPS_ERROR("Error in pre_phyinit");
        return false;
    }
    if (DDRCTL_SUCCESS != dwc_ddrctl_cinit_phyinit(CFG, DDRCTL_FALSE)) {
        SNPS_ERROR("Error in phyinit");
        return false;
    }
    if (dwc_ddrctl_cinit_post_phyinit() == false) {
        SNPS_ERROR("Error in post_phyinit");
        return false;
    }

    /// - perform DDR5 1N/2N mode setting.
    if (IS_DDR5) {
        if (dwc_ddrctl_cinit_ddr5_1N_2N_mode_init() == false) {
            SNPS_ERROR("Error in dwc_ddrctl_cinit_ddr5_1N_2N_mode_init");
            return false;
        }
    }
    if (IS_DDR5) {
        // use SCI to perform DFI initialization
        if (dwc_ddrctl_cinit_seq_ddr5_dfi_initialization() == false) {
            SNPS_ERROR("Error in seq_ddr5_dfi_initialization");
            return false;
        }
    } else {
        /// - Initialize the PHY to mission mode by performing a DFI initialization sequence per the DFI specification.
        if (dwc_ddrctl_cinit_seq_dfi_initialization() == false) {
            SNPS_ERROR("Error in seq_dfi_initialization");
            return false;
        }
    }
    // reapply mission mode settings
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        dwc_ddrctl_cinit_prgm_REGB_DDRC_PWRCTL(ch);
    }

    /// - Perform SDRAM initialization if skip_training enabled.
    if (CFG->phy_training == DWC_PHY_SKIP_TRAINING) {
        if (IS_DDR5) {
            if (IS_RDIMM ||  IS_LRDIMM) {
                if (dwc_ddrctl_cinit_seq_ddr5_dimm_initialization() == false) {
                    SNPS_ERROR("Error in seq_ddr5_dimm_initialization");
                    return false;
                }
            }
            else {
                if (dwc_ddrctl_cinit_seq_ddr5_dram_initialization() == false) {
                    SNPS_ERROR("Error in seq_ddr5_dram_initialization");
                    return false;
                }
            }
        }
        if (IS_DDR4) {
            if (IS_RDIMM || IS_LRDIMM) {
                if (dwc_ddrctl_cinit_seq_ddr4_dram_initialization() == false) {
                    SNPS_ERROR("Error in seq_ddr4_dram_initialization");
                    return false;
                }
            }
        }
    }

    /// - set init_done==1 for DDR5
    if (IS_DDR5) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            if (dwc_ddrctl_cinit_seq_poll_operating_mode(2 * DWC_DDRCTL_MAX_APB_POLLING, ch, 0) == false) {
                SNPS_ERROR("Error in seq_poll_operating_mode");
                return false;
            }
            if (dwc_ddrctl_cinit_ddr5_init_done(1, ch) == false) {
                SNPS_ERROR("Error in ddr5_init_done");
                return false;
            }
        }
    }

    /// - poll for normal operating mode
    if (dwc_ddrctl_cinit_seq_poll_operating_mode(2 * DWC_DDRCTL_MAX_APB_POLLING, 0, 1) == false) {
        SNPS_ERROR("Error in seq_poll_operating_mode");
        return false;
    }

    /** - re-apply controller updates setting which was disabled in dwc_ddrctl_cinit_pre_phyinit */
    DQSOSCCFG0_t *const ptrDQSOSCCFG0 = &REGB_DDRC_CH0.dqsosccfg0;

    DFIUPD0_t *const ptrDFIUPD0 = &REGB_DDRC_CH0.dfiupd0;
    DERATECTL6_t *const ptrDERATECTL6 = &REGB_DDRC_CH0.deratectl6;

    ptrDFIUPD0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0 );
    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_pre_qdyn_write");
        return false;
    }
    ptrDQSOSCCFG0->value = dwc_ddrctl_cinit_io_read32 (REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0);
    ptrDQSOSCCFG0->dis_dqsosc_srx = QDYN.dis_dqsosc_srx;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0, ptrDQSOSCCFG0->value);

    ptrDFIUPD0->dis_auto_ctrlupd = QDYN.dis_auto_ctrlupd;
    ptrDFIUPD0->dis_auto_ctrlupd_srx = QDYN.dis_auto_ctrlupd_srx;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0, ptrDFIUPD0->value);
    ZQCTL2_t        * ptr_zqctl2 = &REGB_DDRC_CH0.zqctl2;

    ptr_zqctl2->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2);
    ptr_zqctl2->dis_srx_zqcl = QDYN.dis_srx_zqcl;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2, ptr_zqctl2->value);

    if (IS_DDR5) {
        ptrDERATECTL6->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6);
        ptrDERATECTL6->dis_mrr4_tcr_srx = QDYN.dis_mrr4_tcr_srx;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6, ptrDERATECTL6->value);
    }

    if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_post_qdyn_write");
        return false;
    }
#ifdef DDRCTL_SECURE
    rslt = ddrctl_sinit_ime_config(CFG);
    if(DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("IME configuration failed");
        return false;
    }
#endif // DDRCTL_SECURE

    /// - memory sub-system is now read, enable hif interface
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_set_opctrl1(0, 0, ch) == false) {
            SNPS_ERROR("Error in seq_set_opctrl1");
            return false;
	    }
    }

    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports enable failed");
        return false;
    }

    return true;
    /// @}
}


/** @brief utility method to enable/disable DDR4 auto self refresh mode.
 *  @param asr boolean if true sends QDYN.emr2 to DDR4 MR4, else mr2[7:6] set to 0 */
bool dwc_ddrctl_cinit_seq_set_ddr4_mr2_asr(bool asr)
{
    SNPS_TRACE("Entering");
#ifdef CINIT_DDR4
    if(asr) {
        uint32_t mr_data = 0;
        uint32_t mr_rank = STATIC.active_ranks;
        uint32_t mr_address = 0x2;
        uint32_t mr2 = QDYN.emr2[0][0];

        SNPS_LOG("Restore LP ASR after manually exiting selfref",NULL);
        mr_data = mr_address << 4 | mr2;
        if (dwc_ddrctl_cinit_seq_ddr4_send_mrw(0x2, mr_data, mr_rank, 0) == false) {
            SNPS_ERROR("Error in seq_ddr4_send_mrw");
            return false;
        }
    }
    else {
        uint32_t mr_data = 0;
        uint32_t mr_rank = STATIC.active_ranks;
        uint32_t mr_address = 0x2;
        uint32_t mr2 = 0;
        ddr4_mode_registers_t *mregs = &hdlr->memCtrlr_m.ddr4_mr[0];

        SNPS_LOG("Disable LP ASR before manually going into selfref",NULL);
        mr2 |= (mregs->mr2.write_crc & 0x00000001) << 12;        // mr2[12]
        mr2 |= (mregs->mr2.rtt_wr & 0x00000007) << 9;            // mr2[11:9]
        mr2 |= (0x0 & 0x00000003) << 6;        // mr2[7:6]
        mr2 |= (mregs->mr2.cwl & 0x00000007) << 3;            // mr2[5:3]
        mr_data = mr_address << 4 | mr2;
        if (dwc_ddrctl_cinit_seq_ddr4_send_mrw(0x2, mr_data, mr_rank, 0) == false) {
            SNPS_ERROR("Error in seq_ddr4_send_mrw");
            return false;
    }
    }
#endif // CINIT_DDR4
    SNPS_TRACE("Leaving");
    return true;
}


/** @brief method to perform DFI initialization using software command
 * interface.
 * */
bool dwc_ddrctl_cinit_seq_ddr5_dfi_initialization(void) {
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    ddrctl_error_t   rslt;

    SNPS_LOG("Begin DDR5 DFI initialization sequence ",NULL);

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        rslt = cinit_ddr5_send_reset_control(hdlr, (ddrctl_channel_t)ch, DDRCTL_DISABLE, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Error in Send reset control exit");
            return false;
        }
    }
    /** -#
     * Set CSn to LOW of all ranks of all channels through software command interface command FORCE_CS.
     */
    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            rslt = cinit_ddr5_send_force_cs(hdlr, (ddrctl_channel_t) ch, 0xf, 0, SW_CTRL_LAST_CMD);
            if (rslt != DDRCTL_SUCCESS) {
                SNPS_ERROR("Error in Send Force CS reset");
                return false;
            }
        }
    }

    /** -#
     * Set REGB_DDRC_CH0.pasctl37.dch_sync_mode to ‘1’. This enables
     * dfi_init_start and dfi_init_complete to assert and de-assert
     * at the same time on both channels. (Dual Channel only)
     */
    if (num_ddrc == 2) {
        if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(1) == false) {
            SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
            return false;
        }
    }
    /** -#
     *  This will set dfi_init_start to '1' at the DFI interface.
     * If dual channel is enabled, this step is only needed software command interface
     * of Channel 0, since REGB_DDRC_CH0.pasctl37.dch_sync_mode has been set to ‘1’.
     */

    rslt = cinit_ddr5_send_dfi_freq_chg_ctrl(hdlr, DDRCTL_CHANNEL_0, 1, 0,
                                             MEMC_FREQ_RATIO, 0, 0, SW_CTRL_LAST_CMD);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Error in Send DFI dfi_init_start");
        return false;
    }


    /// -# release dfi_init_start back to 0
    rslt = cinit_ddr5_send_dfi_freq_chg_ctrl(hdlr, DDRCTL_CHANNEL_0, 0, 1,
                                             MEMC_FREQ_RATIO, 0, 0, SW_CTRL_LAST_CMD);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Error in clearing dfi_init_start  ");
        return false;
    }


    /** -#
     * Set REGB_DDRC_CH0.pasctl37.dch_sync_mode to ‘0’. (Dual Channel only)
     */
    if (num_ddrc == 2) {
        if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(0) == false) {
            SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
            return false;
        }
    }

    return true;
}
/// @} // end DDRSwSeqGrp
#endif

