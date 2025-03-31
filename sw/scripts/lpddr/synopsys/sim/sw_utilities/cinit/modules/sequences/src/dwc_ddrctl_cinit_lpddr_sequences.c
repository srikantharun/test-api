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
#include "dwc_ddrctl_cinit_lpddr_sequences.h"
#include "dwc_ddrctl_cinit_helpers.h"

#include "dwc_ddrctl_cinit.h"

#include "dwc_ddrctl_cinit_types.h"
#include "cinit_port_util.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_util.h"
#include "physetup.h"
#include "phy/sinit_phy_utils.h"
#include "sinit_types.h"

 /**
  * @defgroup LPDDRSwSeqGrp LPDDR software sequences
  * This section groups together software sequences and methods that are used in
  * LPDDR54 controllers.
  * @{
  */

#ifdef DDRCTL_LPDDR
/** @brief A convenience method to access the LPDDR5/4 SDRAM mode registers
 * @{
 */
bool dwc_ddrctl_cinit_seq_mr_access(bool is_rd,uint32_t mr_address, uint32_t mr_data, uint32_t rank, bool sw_init_int, uint32_t ch)
{
    SNPS_TRACE("Entering");
    MRCTRL0_t *ptr_mrctrl0[2] = {
         &REGB_DDRC_CH0.mrctrl0,
         &REGB_DDRC_CH1.mrctrl0
    };

    MRCTRL1_t *ptr_mrctrl1[2] = {
         &REGB_DDRC_CH0.mrctrl1,
         &REGB_DDRC_CH1.mrctrl1
    };
    MRRDATA0_t *ptr_mrrdata0[2] = {
         &REGB_DDRC_CH0.mrrdata0,
         &REGB_DDRC_CH1.mrrdata0
    };
    SNPS_LOG("mr_address=%u mr_data=%u", mr_address, mr_data);
    /** - make sure MRSTAT.mr_wr_busy is 0 */
    if (dwc_ddrctl_cinit_seq_poll_mr_wr_busy(0, ch, DWC_DDRCTL_MAX_APB_POLLING) == false) {
        SNPS_ERROR("Error in seq_poll_mr_wr_busy");
        return false;
    }
    /** - clear mrr_done if we are trying to do a read */
    ptr_mrctrl0[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL0);
    if (is_rd == true) {
        ptr_mrctrl0[ch]->mrr_done_clr = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL0, ptr_mrctrl0[ch]->value);
    }

    ptr_mrctrl0[ch]->mr_wr = 0;
    ptr_mrctrl0[ch]->mrr_done_clr = 0;
    ptr_mrctrl0[ch]->mr_rank = rank;
    ptr_mrctrl0[ch]->sw_init_int = sw_init_int;
    ptr_mrctrl0[ch]->mr_type = (is_rd == true) ? 1 : 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL0, ptr_mrctrl0[ch]->value);

    ptr_mrctrl1[ch]->mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(mr_address, 8, 8) |
                               DWC_DDRCTL_SETREGBITFIELDSHIFT(mr_data, 8, 0);
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL1, ptr_mrctrl1[ch]->value);


    /** - hit the mrctrl0->mr_wr bit to start to access. */
    ptr_mrctrl0[ch]->mr_wr = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL0, ptr_mrctrl0[ch]->value);

    if (dwc_ddrctl_cinit_seq_poll_mr_wr_busy(0, ch, DWC_DDRCTL_MAX_APB_POLLING) == false) {
        SNPS_ERROR("Error in seq_poll_mr_wr_busy");
        return false;
    }
    if (is_rd == true) {
 //       SNPS_ERROR("MRR not yet supported",NULL);
      ptr_mrrdata0[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + MRRDATA0);
    }

    SNPS_TRACE("Leaving");
    return true;
    /// @}
}

/**
 * @brief method to perform any steps before calling phyinit.
 * @detail in particular any automatic HW low power must be blocked.
 */
bool dwc_ddrctl_cinit_pre_phyinit(void)
{
    SNPS_TRACE("Entering");
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t freq =0;
    PWRCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };
    DFIMISC_t *const ptrDFIMISC = &REGB_DDRC_CH0.dfimisc;
    RFSHCTL0_t *const ptrRFSHCTL0 = &REGB_DDRC_CH0.rfshctl0;
    ZQCTL0_t         * ptr_zqctl0 = &REGB_DDRC_CH0.zqctl0;
    ZQCTL2_t        * ptr_zqctl2 = &REGB_DDRC_CH0.zqctl2;
    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr[ch]->powerdown_en = 0;
        ptr[ch]->en_dfi_dram_clk_disable = 0;
        ptr[ch]->selfref_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr[ch]->value);
        /// - disable auto refresh before training
        ptrRFSHCTL0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0);
        ptrRFSHCTL0->dis_auto_refresh = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0 ,ptrRFSHCTL0->value);
        /// - Disable auto ZQCAL during training
        ptr_zqctl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0);
        ptr_zqctl0->dis_auto_zq = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0, ptr_zqctl0->value);
    }
#ifdef DDRCTL_PPT2
    /// - Disable ppt2_en for frequency 0 during training.
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        DFIUPDTMG2_t *const ptrDFIUPDTMG2 = &REGB_FREQ_CH0(0).dfiupdtmg2;
	ptrDFIUPDTMG2->value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(0, ch) + DFIUPDTMG2);
	ptrDFIUPDTMG2->ppt2_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, ch) + DFIUPDTMG2, ptrDFIUPDTMG2->value);
    }
#endif // DDRCTL_PPT2
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_pre_qdyn_write");
                return false;
        }
        ptr_zqctl2->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL2);
        ptr_zqctl2->dis_srx_zqcl = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL2, ptr_zqctl2->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_post_qdyn_write");
                return false;
        }

        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_pre_qdyn_write");
                return false;
        }
        ptrDFIMISC->dfi_init_complete_en = 0;
        /* dfi_reset_n should be set before PHY initialization */
        ptrDFIMISC->dfi_reset_n = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptrDFIMISC->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_post_qdyn_write");
                return false;
        }
    }
    /// - disable dqsosc_enable before phy training

    DQSOSCCTL0_t *const ptrDQSOSCCTL0[2] = {
        &REGB_FREQ_CH0(freq).dqsoscctl0,
        &REGB_FREQ_CH1(freq).dqsoscctl0
    };

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptrDQSOSCCTL0[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, ch) + DQSOSCCTL0);
        ptrDQSOSCCTL0[ch]->dqsosc_enable = 0;
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DQSOSCCTL0, ptrDQSOSCCTL0[ch]->value);
    }

    DERATECTL0_t *const ptrDERATECTL0 = &REGB_DDRC_CH0.deratectl0;

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        /// -# disable derating DQSOSC
        ptrDERATECTL0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0);
        ptrDERATECTL0->derate_enable = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0, ptrDERATECTL0->value);
        /** -  Disable any VIP checkers for PHY training */
        if (CFG->phy_training != DWC_PHY_SKIP_TRAINING)
            dwc_ddrctl_cinit_io_training_chk_enable(ch);
    }
    SNPS_TRACE("Leaving");
    return true;
}

/** @brief method to apply training results to the controller
 * @note Not yet implemented
 */
bool dwc_ddrctl_cinit_apply_training(void)
{
    SNPS_TRACE("Entering");
    // TBD
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method call after PHY training has completed
 */
bool dwc_ddrctl_cinit_post_phyinit(void)
{
    SNPS_TRACE("Entering");
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    // using frequency0 values here
    uint32_t freq =0;
    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    /// - reapply mission mode settings
    /*for (uint32_t ch = 0; ch < num_ddrc; ch++)*/
    /*dwc_ddrctl_cinit_prgm_REGB_DDRC_PWRCTL(ch);*/

    DQSOSCCTL0_t *const ptrDQSOSCCTL0[2] = {
        &REGB_FREQ_CH0(freq).dqsoscctl0,
        &REGB_FREQ_CH1(freq).dqsoscctl0
    };

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptrDQSOSCCTL0[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, ch) + DQSOSCCTL0);
        ptrDQSOSCCTL0[ch]->dqsosc_enable = DYN.dqsosc_enable[freq][ch];
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DQSOSCCTL0, ptrDQSOSCCTL0[ch]->value);
    }

    DERATECTL0_t *const ptrDERATECTL0 = &REGB_DDRC_CH0.deratectl0;

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptrDERATECTL0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0);
        ptrDERATECTL0->derate_enable = DYN.derate_enable;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0, ptrDERATECTL0->value);
    }

    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING ) {
        // Set PHY CSR MicroContMuxSel to 0x0
        physetup_io_write16(0xd0000, 0x0);

        // if PHY training then apply training result here
        if (CFG->phy_training == DWC_PHY_TRAINING) {
            dwc_ddrctl_cinit_apply_training();
        }
    }

    SNPS_TRACE("Leaving");
    return true;
}

/** @brief Power removal sequence
 * @{
 */
bool dwc_ddrctl_cinit_sw_seq_power_disable(void)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t selfref_type;
    PWRCTL_t *ptr_pwrctl[2] = {
            &REGB_DDRC_CH0.pwrctl,
            &REGB_DDRC_CH1.pwrctl
        };
    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    /** -# : Disable all AXI ports from taking anymore transactions. */
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

    /** -# Set dis_auto_ctrlupd to 1 to avoid ctrl updates during the request for
     * the PHY to enter retention.
     * Note this will be clear when power is removed.
     * */
    {
        DFIUPD0_t *const ptr = &REGB_DDRC_CH0.dfiupd0;

        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0 );
            dwc_ddrctl_cinit_seq_pre_qdyn_write(ch);
            ptr->dis_auto_ctrlupd = 1;
            ptr->dfi_phyupd_en = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptr->value);
            dwc_ddrctl_cinit_seq_post_qdyn_write(ch);
        }
    }
    /** -# For LPDDR5: In Background Calibration mode, before entering Power-down mode,
     * the calibration shall be halted by setting ZQ Stop when VDDQ is going to be powered off. */
    if (IS_LPDDR5) {
        if(!dwc_ddrctl_cinit_seq_lpddr5_halt_zqcal())
            return false;
    }
    /** -# Write ‘1’ to PWRCTL.selfref_sw Causes the system to move to Self Refresh state.*/
    PWRCTL_t *const ptrPWRCTL[2]   = {
            &REGB_DDRC_CH0.pwrctl,
            &REGB_DDRC_CH1.pwrctl
    };

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptr_pwrctl[ch]->selfref_sw = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }
    /** -# Poll stat.selfref_type= 2’b10 Waits until Self Refresh state is entered. */
    selfref_type = 0x2;
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_selfref_type(DWC_DDRCTL_MAX_APB_POLLING, ch, selfref_type) == false) {
            SNPS_ERROR("Error in seq_poll_selfref_type");
            return false;
        }
    }
    /** -# Place IOs in retention mode Refer to relevant PHY databook for more information. */
    if (dwc_ddrctl_cinit_phy_lp3_io_retention(true) == false) {
        SNPS_ERROR("Error in phy_lp3_io_retention");
        return false;
    }
    /** -# Drive low RESETn to the PHY */
    if (IS_ARB_CONFIG) {
        dwc_ddrctl_cinit_io_set_axi_clk(false);
    dwc_ddrctl_cinit_io_aresetn(false);
    }
    /** -# Remove DDRC controller clock */
    dwc_ddrctl_cinit_io_set_ddrc_clk(false);
    /** -# Remove power */
    dwc_ddrctl_cinit_io_power(false);
    SNPS_TRACE("Leaving");
    return true;
}

/** @brief Power re-enable sequence.
 * Upon exit from this sequence the controller should be in normal mode
 * @{
 */
bool dwc_ddrctl_cinit_sw_seq_power_enable(void)
{
    SNPS_TRACE("Entering");
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    RFSHCTL0_t      * ptr_rfshctl0 = &REGB_DDRC_CH0.rfshctl0;
    PWRCTL_t *ptr_pwrctl[2] = {
            &REGB_DDRC_CH0.pwrctl,
            &REGB_DDRC_CH1.pwrctl
        };
    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    /** -# Enable Power */
    dwc_ddrctl_cinit_io_power(true);
    /** -# Restore the DDRC controller clocks */
    if (IS_ARB_CONFIG) {
        dwc_ddrctl_cinit_io_set_axi_clk(true);
        dwc_ddrctl_cinit_io_aresetn(true);
    }
    dwc_ddrctl_cinit_io_set_ddrc_clk(true);

    /** -# Reset controller/PHY by driving core_ddrc_rstn = 1’b0, aresetn_n = 1’b0, presetn = ’b0 */
    dwc_ddrctl_cinit_io_presetn(false);
    dwc_ddrctl_cinit_io_ddrc_rstn(0);
#ifdef UMCTL2_INCL_ARB
    dwc_ddrctl_cinit_io_aresetn(0);
#endif /* UMCTL2_INCL_ARB */
    dwc_ddrctl_cinit_io_wait_pclk(10);
    /** -# Remove APB reset, presetn = 1’b1, and reprogram the registers to pre-power removal values */
    dwc_ddrctl_cinit_io_presetn(true);
    dwc_ddrctl_cinit_io_wait_ddrc_clk(128);
    // the controller has been reset so reset register structure
    dwc_cinit_reg_defaults(hdlr);


    /** -# Program INITTMG0.skip_dram_init = 2’b11 Skips the DRAM initialization routine and starts up in self-refresh mode. */
    if (dwc_ddrctl_cinit_seq_set_skip_dram_init(3) == false) {
        SNPS_ERROR("Error in seq_set_skip_dram_init");
        return false;
    }
    // set QDYN.skip_dram_init so dwc_ddrctl_cinit_seq_initialize_ctrl_regs will not over
    // write value of 3
    QDYN.skip_dram_init[0] = 3;

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      ptr_rfshctl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0);
      ptr_rfshctl0->dis_auto_refresh = 1;
      DYN.dis_auto_refresh = 1;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0, ptr_rfshctl0->value);
    }

    /** -#    Programs ptr_pwrctl[ch]->selfref_sw = 1’b1
    Keeps the controller in self-refresh mode.
    */

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptr_pwrctl[ch]->selfref_sw = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
        DYN.selfref_sw[ch] = 1;
    }

    /** -# Remove the controller reset core_ddrc_rstn = 1’b1 aresetn_n = 1’b1 */
    dwc_ddrctl_cinit_io_ddrc_rstn(0);
#ifdef UMCTL2_INCL_ARB
    dwc_ddrctl_cinit_io_aresetn(0);
#endif /* UMCTL2_INCL_ARB */
    SNPS_LOG("initialize the controller register map again",NULL);
    /** -# re-initialize the controller register map */
    if (dwc_ddrctl_cinit_seq_initialize_ctrl_regs() == false) {
        SNPS_ERROR("Error in seq_initialize_ctrl_regs");
        return false;
    }
    /** -# release core_rst_n to the controller */
    dwc_ddrctl_cinit_io_ddrc_rstn(true);
#ifdef UMCTL2_INCL_ARB
    /** -# de-assert aresetn */
    dwc_ddrctl_cinit_io_aresetn(true);
#endif /* UMCTL2_INCL_ARB */

    /** -#
    Run PHY initialization/training as required, including removing the IOs
    from retention mode including steps below
    Refer to the relevant PHY databook for more information.
    */
    if (dwc_ddrctl_cinit_phy_lp3_io_retention(false) == false) {
        SNPS_ERROR("Error in phy_lp3_io_retention");
        return false;
    }

    if (dwc_ddrctl_cinit_pre_phyinit() == false) {
        SNPS_ERROR("Error in pre_phyinit");
        return false;
    }
    if (DDRCTL_SUCCESS != dwc_ddrctl_cinit_phyinit(CFG, DDRCTL_TRUE)) {
        SNPS_ERROR("Error in phyinit");
        return false;
    }
    if (dwc_ddrctl_cinit_post_phyinit() == false) {
        SNPS_ERROR("Error in post_phyinit");
        return false;
    }

    // load MRW Buffer needed for LPDDR5X
#ifdef DDRCTL_HWFFC_EXT_AND_LPDDR5X
    SNPS_TRACE("Programming HWFFC MRW Buffer");
    dwc_ddrctl_cinit_prgm_hwffcmrw(CFG);
#endif

    /** -# Initialize the PHY to mission mode by performing a DFI initialization sequence per the DFI specification.*/
    if (dwc_ddrctl_cinit_seq_dfi_initialization() == false) {
        SNPS_ERROR("Error in seq_dfi_initialization");
        return false;
    }
    /** -  Re-enable any VIP checkers after PHY training */
    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING)
        dwc_ddrctl_cinit_io_training_chk_enable(1);

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_rfshctl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0);
        ptr_rfshctl0->dis_auto_refresh = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0, ptr_rfshctl0->value);
    }

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->selfref_sw = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
        DYN.selfref_sw[ch] = 0;
    }
    uint32_t selfref_type = 0x0;

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_selfref_type(DWC_DDRCTL_MAX_APB_POLLING, ch, selfref_type) == false) {
            SNPS_ERROR("Error in seq_poll_selfref_type");
            return false;
        }
    }
    /** -# poll for normal operating mode */
    if (dwc_ddrctl_cinit_seq_poll_operating_mode(2 * DWC_DDRCTL_MAX_APB_POLLING, 0, 1) == false) {
        SNPS_ERROR("Error in seq_poll_operating_mode");
        return false;
    }
    /** -# For LPDDR5: resume ZQ calibration background process. */
#ifdef CINIT_LPDDR5
    if (IS_LPDDR5) {
        if(!dwc_ddrctl_cinit_seq_lpddr5_resume_zqcal()) {
            SNPS_ERROR("Error in dwc_ddrctl_cinit_seq_lpddr5_resume_zqcal");
            return false;
        }
    }
#endif
    /// - memory sub-system is now ready, enable hif interface
    for (uint32_t ch = 0; ch < num_ddrc; ch++){
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
 * @brief DWC_ddrctl initialization sequence entry point for LPDDR4/LPDDR5.
 * @{
 */
bool dwc_ddrctl_cinit_seq_initialization(void)
{
    ddrctl_error_t  rslt;
    uint8_t set_skip_dram_init;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    PWRCTL_t *const ptrPWRCTL[2]   = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };
    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

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
    set_skip_dram_init = (CFG->phy_training == DWC_PHY_SKIP_TRAINING) ? 1 : 3;
    if (dwc_ddrctl_cinit_seq_set_skip_dram_init(set_skip_dram_init) == false) {
        SNPS_ERROR("Error in seq_set_skip_dram_init");
        return false;
    }
    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptrPWRCTL[ch]->selfref_sw = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
    }
    }
    /// - release core_rst_n to the controller
    dwc_ddrctl_cinit_io_ddrc_rstn(true);
#ifdef UMCTL2_INCL_ARB
    /// - de-assert aresetn
    dwc_ddrctl_cinit_io_aresetn(true);
#endif /* UMCTL2_INCL_ARB */

    // derate_enable
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

    // load MRW Buffer needed for LPDDR5X
#ifdef DDRCTL_HWFFC_EXT_AND_LPDDR5X
    SNPS_TRACE("Programming HWFFC MRW Buffer");
    dwc_ddrctl_cinit_prgm_hwffcmrw(CFG);
#endif

    /// - Initialize the PHY to mission mode by performing a DFI initialization sequence per the DFI specification.
    if (dwc_ddrctl_cinit_seq_dfi_initialization() == false) {
        SNPS_ERROR("Error in seq_dfi_initialization");
        return false;
    }
    /** -  Re-enable any VIP checkers after PHY training */
    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING)
        dwc_ddrctl_cinit_io_training_chk_enable(1);

    if (CFG->phy_training == DWC_PHY_SKIP_TRAINING) {
        if (IS_LPDDR4) {
            if (dwc_ddrctl_cinit_seq_lpddr4_dram_initialization() == false) {
                SNPS_ERROR("Error in seq_lpddr4_dram_initialization");
                return false;
            }
        } else {
            if (dwc_ddrctl_cinit_seq_lpddr5_dram_initialization() == false) {
                SNPS_ERROR("Error in seq_lpddr5_dram_initialization");
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
    DFIUPD0_t *const ptrDFIUPD0 = &REGB_DDRC_CH0.dfiupd0;

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptrDFIUPD0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0 );
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_pre_qdyn_write");
                return false;
        }
        ptrDFIUPD0->dis_auto_ctrlupd = QDYN.dis_auto_ctrlupd;
        ptrDFIUPD0->dis_auto_ctrlupd_srx = QDYN.dis_auto_ctrlupd_srx;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptrDFIUPD0->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_post_qdyn_write");
                return false;
        }

        ZQCTL0_t         * ptr_zqctl0 = &REGB_DDRC_CH0.zqctl0;

        ptr_zqctl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0);
        ptr_zqctl0->dis_auto_zq = DYN.dis_auto_zq;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0, ptr_zqctl0->value);

        ZQCTL2_t        * ptr_zqctl2 = &REGB_DDRC_CH0.zqctl2;

        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_pe_qdyn_write");
                return false;
        }
        ptr_zqctl2->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL2);
        ptr_zqctl2->dis_srx_zqcl = QDYN.dis_srx_zqcl;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL2, ptr_zqctl2->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_post_qdyn_write");
                return false;
        }

        RFSHCTL0_t *const ptrRFSHCTL0 = &REGB_DDRC_CH0.rfshctl0;

        ptrRFSHCTL0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0);
        ptrRFSHCTL0->dis_auto_refresh = DYN.dis_auto_refresh;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0 ,ptrRFSHCTL0->value);

        ptrPWRCTL[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        DYN_CFG_ARRAY(ptrPWRCTL, powerdown_en, ch);
        DYN_CFG_ARRAY(ptrPWRCTL, selfref_en, ch);
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptrPWRCTL[ch]->value);
    }
#ifdef DDRCTL_PPT2
    /// - Re-apply DYN.ppt2_en setting for frequency 0.
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        DFIUPDTMG2_t *const ptrDFIUPDTMG2 = &REGB_FREQ_CH0(0).dfiupdtmg2;
	ptrDFIUPDTMG2->value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(0, ch) + DFIUPDTMG2);
	ptrDFIUPDTMG2->ppt2_en = DYN.ppt2_en[0];
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(0, ch) + DFIUPDTMG2, ptrDFIUPDTMG2->value);
    }
#endif // DDRCTL_PPT2

    /// - memory sub-system is now ready, enable hif interface
    for (uint32_t ch = 0; ch < num_ddrc; ch++)
        dwc_ddrctl_cinit_seq_set_opctrl1(0, 0, ch);

    /// - enable all application ports
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports enable failed");
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
    /** @} */ // end brief
}

/** @brief method to perform LPDDR DRAM initialization.
 * @{
 */
bool dwc_ddrctl_cinit_seq_lpddr4_dram_initialization(void)
{
    SNPS_TRACE("Entering");
    bool is_rd = false;
    uint32_t mr_address;
    uint32_t mr_data;
    uint32_t rank;
    bool sw_init_int = false;
    uint32_t ch = 0;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      /** - MR13 */
      rank = REGB_DDRC_CH0.mstr0.active_ranks;
      if(rank==0)
          rank = 1;
      mr_address = 13;
      mr_data = REGB_FREQ_CH0(0).initmr1.emr3;
      if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
          SNPS_ERROR("Error in seq_mr_access");
          return false;
      }
      /** - MR1 */
      mr_address = 1;
      mr_data = REGB_FREQ_CH0(0).initmr0.mr;
      if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
          SNPS_ERROR("Error in seq_mr_access");
          return false;
      }
      /** - MR2 */
      mr_address = 2;
      mr_data = REGB_FREQ_CH0(0).initmr0.emr;
      if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
          SNPS_ERROR("Error in seq_mr_access");
          return false;
      }
      /** - MR3 */
      mr_address = 3;
      mr_data = REGB_FREQ_CH0(0).initmr1.emr2;
      if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
          SNPS_ERROR("Error in seq_mr_access");
          return false;
      }
    }
    /** - MR23 */
    SNPS_TRACE("Leaving");
    return true;
    /// @}
}

/** @brief method to perform LPDDR5 DRAM initialization when using SKIP training
 * mode.
 * @{
 */
bool dwc_ddrctl_cinit_seq_lpddr5_dram_initialization(void)
{
    SNPS_TRACE("Entering");
    bool is_rd = false;
    uint32_t mr_address;
    uint32_t mr_data;
    uint32_t rank;
    bool sw_init_int = false;
    uint32_t ch = 0;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;

    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    rank = REGB_DDRC_CH0.mstr0.active_ranks;
    if(rank==0)
        rank = 1;

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        /** - MR18 */
        mr_address = 18;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr18.wck_odt, 3, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr18.wck_fm, 1, 3) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr18.wck_on, 1, 4) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr18.wck2ck_leveling, 1, 6) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr18.ckr, 1, 7);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR1 */
        mr_address = 1;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr1.ck_mode, 1, 3) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr1.write_latency, 4, 4);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR2 */
        mr_address = 2;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr2.rl_nrtp, 4, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr2.nwr, 4, 4);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR3 */
        mr_address = 3;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr3.pdds, 3, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr3.bk_bg_org, 2, 3) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr3.wls, 1, 5) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr3.read_dbi, 1, 6) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr3.write_dbi, 1, 7);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR10 */
        mr_address = 10;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr10.rdqs_pst_mode, 1, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr10.rdqs_pre_2, 1, 1) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr10.wck_pst, 2, 2) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr10.rdqs_pre, 2, 4) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr10.rdqs_pst, 2, 6);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR11 */
        mr_address = 11;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr11.dq_odt, 3, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr11.nt_odt, 1, 3) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr11.ca_odt, 3, 4);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR12 */
        mr_address = 12;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr12.vref_ca, 7, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr12.vbs, 1, 7);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR13 */
        mr_address = 13;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr13.thermal_offset, 2, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr13.vro, 1, 2) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr13.dmd, 1, 5) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr13.dual_vdd2, 1, 7);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR14 */
        mr_address = 14;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr14.vref_dq, 7, 0);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR15 */
        mr_address = 15;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr15.vref_dq, 7, 0);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR17 */
        mr_address = 17;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr17.soc_odt, 3, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr17.odtd_ck, 1, 3) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr17.odtd_cs, 1, 4) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr17.odtd_ca, 1, 5) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr17.odtd, 2, 6);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR19 */
        mr_address = 19;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr19.dvfsq, 2, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr19.dvfsc, 2, 3);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR20 */
        mr_address = 20;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr20.rdqs, 2, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr20.wck_mode, 2, 2);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR22 */
        mr_address = 22;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr22.wecc, 2, 4) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr22.recc, 2, 6);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR23 */
        mr_address = 23;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr23.pasr_mask, 8, 0);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR25 */
        mr_address = 25;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr25.ck_bus_term, 1, 4) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr25.ca_bus_term, 1, 5) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr25.parc, 1, 6);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR28 */
        mr_address = 28;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr28.zq_reset, 1, 0) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr28.zq_stop, 1, 1) |
            DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr28.zq_int, 2, 2);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR37 */
        mr_address = 37;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr37.wck2dqi_runtime, 8, 0);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR40 */
        mr_address = 40;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr40.wck2dqo_runtime, 8, 0);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR41 */
        mr_address = 41;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr41.nt_dq_odt, 3, 5) |
                  DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr41.edvfsc_odt_support, 1, 3) |
                  DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr41.dvfsc_edvfsc_support, 2, 1)|
                  DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr41.pdfec, 1, 0);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
        /** - MR46 */
        mr_address = 46;
        mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr46.enh_rdqs, 1, 0)|
                  DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr46.fifo_rdqs_training, 1, 2);
        if (dwc_ddrctl_cinit_seq_mr_access(is_rd, mr_address, mr_data, rank, sw_init_int, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
    }
    SNPS_TRACE("Leaving");
    return true;
    /// @}
}

/**
 * @brief method to enter Deep Sleep Mode (LPDDR5).
 * on exit the controller should be in DSM mode.
 * @param ch channel number
 * @param freq active frequency number
 * @{
 */
bool dwc_ddrctl_cinit_seq_enter_dsm(uint32_t ch, uint32_t freq)
{
    ddrctl_error_t  rslt;
    PWRCTL_t *ptr_pwrctl[2] = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };
    DQSOSCCTL0_t *const ptr_dqsoscctl0[2] = {
        &REGB_FREQ_CH0(freq).dqsoscctl0,
        &REGB_FREQ_CH1(freq).dqsoscctl0
    };

    /** - block all transactions from the application */
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_DISABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports disable failed");
        return false;
    }

        /** - Disable auto PD/SR/DQSOSC */
    ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
    ptr_pwrctl[ch]->powerdown_en = 0;
    ptr_pwrctl[ch]->selfref_en = 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);

    ptr_dqsoscctl0[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, ch) + DQSOSCCTL0);
    ptr_dqsoscctl0[ch]->dqsosc_enable = 0;
    dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DQSOSCCTL0, ptr_dqsoscctl0[ch]->value);
        /** - Wait for stat.dqsosc_state=0 (IDLE) in case it had started before we disabled it */
    if (dwc_ddrctl_cinit_seq_poll_dqsosc_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0) == false) {
        SNPS_ERROR("Error in seq_poll_dqsosc_state");
        return false;
    }
        /** - Set pwrctl[ch]->dsm_en = 1 */
    ptr_pwrctl[ch]->dsm_en = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
        /** - Wait for stat.selfref_state = 0x4 (Deep Sleep Mode) */
    if (dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x4) == false) {
        SNPS_ERROR("Error in seq_poll_selfref_state");
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
    /// @}
}

/**
 * @brief method to exit Deep Sleep Mode (LPDDR5).
 * on exit the controller should be in normal operating mode.
 * @param ch channel number
 * @param freq active frequency number
 * @{
 */
bool dwc_ddrctl_cinit_seq_exit_dsm(uint32_t ch, uint32_t freq)
{
    ddrctl_error_t  rslt;
    PWRCTL_t *ptr_pwrctl[2] = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };
    DQSOSCCTL0_t *const ptr_dqsoscctl0[2] = {
        &REGB_FREQ_CH0(freq).dqsoscctl0,
        &REGB_FREQ_CH1(freq).dqsoscctl0
    };
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[0][0];

    ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        /** - Set pwrctl[ch]->selfref_sw = 1 */
    ptr_pwrctl[ch]->selfref_sw = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
        /** - Set pwrctl[ch]->dsm_en = 0 */
    ptr_pwrctl[ch]->dsm_en = 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
        /** - wait for stat.selfref_state = 0x2 (selfref powerdown) */
    if (dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x2) == false) {
        SNPS_ERROR("Error in seq_poll_selfref_state");
        return false;
    }
    /** - wait tXDSM_XP */
    dwc_ddrctl_cinit_io_usleep(timing->lpddr5_txsr_dsm_us);
        /** - Set pwrctl[ch]->selfref_sw = 0 */
    ptr_pwrctl[ch]->selfref_sw = 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
        /** - wait for stat.selfref_state = 0 */
    if (dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x0) == false) {
        SNPS_ERROR("Error in seq_poll_selfref_state");
        return false;
    }

        /** - unblock the application from sending in transactions */
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports enable failed");
        return false;
    }

        /** - Restore PWRCTL using values from initialization */
    ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
    DYN_CFG_ARRAY(ptr_pwrctl, powerdown_en, ch);
    DYN_CFG_ARRAY(ptr_pwrctl, selfref_en, ch);
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
        /** - Restore DQSOSCCTL0 using values from initialization */
    ptr_dqsoscctl0[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, ch) + DQSOSCCTL0);
    ptr_dqsoscctl0[ch]->dqsosc_enable = DYN.dqsosc_enable[ch][freq];
    dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DQSOSCCTL0, ptr_dqsoscctl0[ch]->value);
    SNPS_TRACE("Leaving");
    return true;
    /// @}
}

/** @brief method to poll stat.selfref_state
 */
bool dwc_ddrctl_cinit_seq_poll_selfref_state(uint32_t max_apb_reads, uint32_t ch, uint32_t state)
{
    SNPS_TRACE("Entering");
    bool rslt;

    rslt = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + STAT, STAT_SELFREF_STATE_BIT_OFFSET,
                                   STAT_SELFREF_STATE_MASK, state, max_apb_reads, 0);

    if (rslt == false) {
        SNPS_ERROR("Polling timeout, stat.selfref_state=%u, waiting for selfref_state=%u",
                    dwc_ddrctl_cinit_io_read_field(REGB_DDRC_CH_OFFSET(ch) + STAT,
                                   STAT_SELFREF_STATE_BIT_OFFSET, STAT_SELFREF_STATE_MASK), state);
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
}

/** @brief method to poll dqsoscstat0.dqsosc_state */
bool dwc_ddrctl_cinit_seq_poll_dqsosc_state(uint32_t max_apb_reads, uint32_t ch, uint32_t state)
{
    SNPS_TRACE("Entering");
    bool rslt;

    rslt = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + DQSOSCSTAT0, DQSOSCSTAT0_DQSOSC_STATE_BIT_OFFSET,
                                   DQSOSCSTAT0_DQSOSC_STATE_MASK, state, max_apb_reads, 0);

    if (rslt == false) {
        SNPS_ERROR("Polling timeout, stat.dqsosc_state=%u, waiting for dqsosc_state=%u",
                    dwc_ddrctl_cinit_io_read_field(REGB_DDRC_CH_OFFSET(ch) + DQSOSCSTAT0,
                                   DQSOSCSTAT0_DQSOSC_STATE_BIT_OFFSET, DQSOSCSTAT0_DQSOSC_STATE_MASK), state);
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
}

/** @brief method to poll a register field as long as the read value is equal with expected value */
bool dwc_ddrctl_cinit_seq_wait_operating_mode(uint32_t timer, uint32_t ch, uint32_t exp_val)
{
   STAT_t *stat_p[2] = {
      &REGB_DDRC_CH0.stat,
      &REGB_DDRC_CH1.stat
   };
   do {
      stat_p[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + STAT);
      timer --;
      if(timer > 0) {
         dwc_ddrctl_cinit_io_wait_pclk(0);
      } else {
         return false;
      }
   } while (stat_p[ch]->operating_mode == exp_val);
   return true;
}

/**
 * @brief Software Clock Removal Sequence
 * @{
 */
bool dwc_ddrctl_cinit_sw_seq_clocks_disable(void)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t selfref_type;
    PWRCTL_t *ptr_pwrctl[2] = {
            &REGB_DDRC_CH0.pwrctl,
            &REGB_DDRC_CH1.pwrctl
        };

    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    /** -# Write ‘0’ to PCTRL.port_en Blocks AXI port from taking anymore transactions. */
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

    /** -# Set dis_auto_ctrlupd to 1 to avoid ctrl updates during the request for clock removal
     * Note this will be clear when clock is removed.
     * */
    {
        DFIUPD0_t *const ptr = &REGB_DDRC_CH0.dfiupd0;

        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0 );
            dwc_ddrctl_cinit_seq_pre_qdyn_write(ch);
            ptr->dis_auto_ctrlupd = 1;
            ptr->dfi_phyupd_en = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptr->value);
            dwc_ddrctl_cinit_seq_post_qdyn_write(ch);
        }
    }


    /** -#  Write ‘1’ to pwrctl[ch]->selfref_sw Causes the system to move to Self Refresh state. */
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptr_pwrctl[ch]->selfref_sw = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }
    /** -# Poll stat.selfref_type= 2’b10 Waits until Self Refresh state is entered. */
    selfref_type = 0x2;
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_selfref_type(DWC_DDRCTL_MAX_APB_POLLING, ch, selfref_type) == false) {
            SNPS_ERROR("Error in seq_poll_selfref_type");
            return false;
        }
    }

    /** -# Remove AXI clock */
    if (IS_ARB_CONFIG)
        dwc_ddrctl_cinit_io_set_axi_clk(false);
    /** -# Remove DDRC controller clock */
    dwc_ddrctl_cinit_io_set_ddrc_clk(false);

    SNPS_TRACE("Leaving");
    return true;
    /// @}
}

/**
 * @brief Enable clocks sequence
 */
bool dwc_ddrctl_cinit_sw_seq_clocks_enable(void)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    PWRCTL_t *ptr_pwrctl[2] = {
            &REGB_DDRC_CH0.pwrctl,
            &REGB_DDRC_CH1.pwrctl
        };

    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    /* 1 Enable AXI clock */
    if (IS_ARB_CONFIG)
        dwc_ddrctl_cinit_io_set_axi_clk(true);

    /*
    2 Enable DDRC controller clock
    It is recommended for DDR4 to re-enable generation of PHY initiated
    Update requests (dfi_phyupd_req). If using a Synopsys PHY, this can
    be done through the PUB’s DSGCR.PUREN.
    */
    dwc_ddrctl_cinit_io_set_ddrc_clk(true);

    /* 3 Write ‘0’ to pwrctl[ch]->selfref_sw Cause system to exit from self-refresh state. */

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptr_pwrctl[ch]->selfref_sw = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }

    /* 4 Poll stat.selfref_type = 2’b00 Wait until self-refresh state is exited. */

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_selfref_type(DWC_DDRCTL_MAX_APB_POLLING, ch, 0) == false) {
            SNPS_ERROR("Error in seq_poll_selfref_type");
            return false;
        }
    }
    /** - Restore controller updates setting which was disabled */
    {
        DFIUPD0_t *const ptr = &REGB_DDRC_CH0.dfiupd0;

        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0 );
            dwc_ddrctl_cinit_seq_pre_qdyn_write(ch);
            ptr->dis_auto_ctrlupd = QDYN.dis_auto_ctrlupd;
            ptr->dfi_phyupd_en = STATIC.dfi_phyupd_en;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptr->value);
            dwc_ddrctl_cinit_seq_post_qdyn_write(ch);
        }
    }

    /* 5 Write ‘1’ to PCTRL.port_en AXI ports are no longer blocked from taking transactions. */
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports enable failed");
        return false;
    }

    /* 6 Enable the Scubber for all channels */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_ENABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber enable failed");
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief Sequence to put PHY into LP3/IO Retention
 * @param enter_retention - true:Enter IO retention , false:Exit IO retention
 */
bool dwc_ddrctl_cinit_phy_lp3_io_retention(bool enter_retention)
{
    SNPS_TRACE("Entering");
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    DFIMISC_t * ptr_dfimisc = &REGB_DDRC_CH0.dfimisc;
    DFIPHYMSTR_t * ptr_dfiphymstr = &REGB_DDRC_CH0.dfiphymstr;
    uint8_t dfi_phymstr_en;

    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    if(enter_retention) {
        SNPS_LOG("Enter LP3/IO retention flow",NULL);

        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {         //0x1f
                SNPS_ERROR("Error in seq_pre_qdyn_write");
                return false;
            }
            ptr_dfimisc->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC);
            ptr_dfimisc->dfi_frequency = 0x1f; /*  PHY Deep Sleep / Retention Enable */
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
            if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_post_qdyn_write");
                return false;
            }

            if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_pre_qdyn_write");
                return false;
            }
            ptr_dfimisc->dfi_init_complete_en = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);

            if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_post_qdyn_write");
                return false;
            }
        }

        /* disable PHYMSTR - avoid PHYMSTR in parallel with frequency change procedure */
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptr_dfiphymstr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIPHYMSTR);
            dfi_phymstr_en = ptr_dfiphymstr->dfi_phymstr_en;
            ptr_dfiphymstr->dfi_phymstr_en = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIPHYMSTR, ptr_dfiphymstr->value);
            /* quasi dynamic write to set ptr_dfimisc->dfi_init_start */
            if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_pre_qdyn_write");
                return false;
            }
            ptr_dfimisc->dfi_init_start = 1;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
            if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_post_qdyn_write");
                return false;
            }
            /* wait for dfi_init complete to go low */
            if (dwc_ddrctl_cinit_seq_poll_dfi_init_complete(0, 5 * DWC_DDRCTL_MAX_APB_POLLING, 0) == false) {
                SNPS_LOG("Error in dwc_ddrctl_cinit_seq_poll_dfi_init_complete");
                return false;
            }
            /* quasi dynamic write to set dfimisc->dfi_init_complete_en */
            if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_pre_qdyn_write");
                return false;
            }
            ptr_dfimisc->dfi_init_start = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
            if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_post_qdyn_write");
                return false;
            }
            /* wait for dfi_init complete to go high */
            if( dwc_ddrctl_cinit_seq_poll_dfi_init_complete(1, 5 * DWC_DDRCTL_MAX_APB_POLLING, ch) == false) {
                SNPS_LOG("Error in dwc_ddrctl_cinit_seq_poll_dfi_init_complete");
                return false;
            }
        }

        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            SNPS_LOG("LP3/IO retention entered",NULL);
            /* put dfi_phymstr_en back to original value */
            ptr_dfiphymstr->dfi_phymstr_en = dfi_phymstr_en;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIPHYMSTR, ptr_dfiphymstr->value);

            ptr_dfimisc->dfi_init_complete_en = 0;
            if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_pre_qdyn_write");
                return false;
            }
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
            if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_post_qdyn_write");
                return false;
            }
        }
    } else {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            SNPS_LOG("Exit LP3/IO retention",NULL);

            /* Program dfimisc->dfi_init_complete_en to 0 */
            if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_pre_qdyn_write");
                return false;
            }
            ptr_dfimisc->dfi_init_complete_en = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
            if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                SNPS_ERROR("Error in seq_post_qdyn_write");
                return false;
            }
        }
    }

    SNPS_TRACE("Leaving");
    return true;
}

/** @brief set MR29 OP[1] to halt all background calibration. */
bool dwc_ddrctl_cinit_seq_lpddr5_halt_zqcal(void)
{
    SNPS_TRACE("Entering");
    uint32_t mr_address;
    uint32_t mr_data;
    uint32_t rank;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;

    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    mr_address = 28;
    mr_data = 2; // ZQ Stop
    rank = REGB_DDRC_CH0.mstr0.active_ranks;
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      if (dwc_ddrctl_cinit_seq_mr_access(0, mr_address, mr_data, rank, 0, ch) == false) {
          SNPS_ERROR("Error in seq_mr_access");
          return false;
      }
    }
    SNPS_TRACE("Leaving");
    return true;
}

/** @brief restore MR28 to settings before power removal. */
bool dwc_ddrctl_cinit_seq_lpddr5_resume_zqcal(void)
{
    SNPS_TRACE("Entering");
    uint32_t mr_address;
    uint32_t mr_data;
    uint32_t rank;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;

    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    mr_address = 28;
    mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr28.zq_reset, 1, 0) |
        DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr28.zq_stop, 1, 1) |
        DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr28.zq_int, 2, 2);
    rank = REGB_DDRC_CH0.mstr0.active_ranks;
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_mr_access(0, mr_address, mr_data, rank, 0, ch) == false) {
            SNPS_ERROR("Error in seq_mr_access");
            return false;
        }
    }
    SNPS_TRACE("Leaving");
    return true;
}

/** @brief method to perform clock frequency sequence using frequency set point
 */
bool dwc_ddrctl_cinit_seq_swffc_with_fsp(uint32_t target_freq)
{
    ddrctl_error_t  rslt;
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t relock_only = 1; // control whether to retrain or relock only
    uint32_t prev_derate_enable;
    uint32_t prev_dis_auto_ctrlupd;
    uint32_t prev_dfi_phyupd_en;
    uint32_t prev_dis_auto_zq;
    uint32_t prev_dfi_phymstr_en;
    uint32_t prev_powerdown_en;
    uint32_t prev_en_dfi_dram_clk_disable;
    uint32_t prev_selfref_en;
    PWRCTL_t *ptr_pwrctl[2] = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };
    DERATECTL0_t    * ptr_deratectl0 = &REGB_DDRC_CH0.deratectl0;
    DFIUPD0_t         * ptr_dfiupd0 = &REGB_DDRC_CH0.dfiupd0;
    ZQCTL0_t         * ptr_zqctl0 = &REGB_DDRC_CH0.zqctl0;
    DFIPHYMSTR_t    * ptr_dfiphymstr = &REGB_DDRC_CH0.dfiphymstr;
    DFIMISC_t       * ptr_dfimisc = &REGB_DDRC_CH0.dfimisc;
    MSTR2_t          * ptr_mstr2 = &REGB_DDRC_CH0.mstr2;
    ZQCTL2_t        * ptr_zqctl2 = &REGB_DDRC_CH0.zqctl2;
    DFILPCFG0_t     * ptr_dfilpcfg0 = &REGB_DDRC_CH0.dfilpcfg0;
    RFSHCTL0_t      * ptr_rfshctl0 = &REGB_DDRC_CH0.rfshctl0;

    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    if (target_freq >= hdlr->num_pstates) {
        SNPS_ERROR("target_freq requested %0d is greater than number of supported frequencies %0d", target_freq, hdlr->num_pstates);
        return false;
    }

    /** - block all transactions from the application */
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

        /** -# wait for the controller to be idle */
    if (dwc_ddrctl_cinit_seq_wait_ctrlr_idle(DWC_DDRCTL_MAX_APB_POLLING) == false) {
        SNPS_ERROR("Error in seq_wait_ctrlr_idle");
        return false;
    }
        /** -# disable derating DQSOSC and controller update */
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_deratectl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0);
        prev_derate_enable = ptr_deratectl0->derate_enable;
        ptr_deratectl0->derate_enable = 0;
        ptr_deratectl0->derate_mr4_pause_fc = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0, ptr_deratectl0->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_dfiupd0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0);
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        prev_dis_auto_ctrlupd = ptr_dfiupd0->dis_auto_ctrlupd;
        prev_dfi_phyupd_en = ptr_dfiupd0->dfi_phyupd_en;
        ptr_dfiupd0->dis_auto_ctrlupd = 1;
        ptr_dfiupd0->dfi_phyupd_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptr_dfiupd0->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_zqctl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0);
        prev_dis_auto_zq = ptr_zqctl0->dis_auto_zq;
        ptr_zqctl0->dis_auto_zq = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0, ptr_zqctl0->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_dfiphymstr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIPHYMSTR);
        prev_dfi_phymstr_en = ptr_dfiphymstr->dfi_phymstr_en;
        ptr_dfiphymstr->dfi_phymstr_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIPHYMSTR, ptr_dfiphymstr->value);
    }

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        prev_powerdown_en = ptr_pwrctl[ch]->powerdown_en;
        prev_en_dfi_dram_clk_disable = ptr_pwrctl[ch]->en_dfi_dram_clk_disable;
        prev_selfref_en = ptr_pwrctl[ch]->selfref_en;
        ptr_pwrctl[ch]->powerdown_en = 0;
        ptr_pwrctl[ch]->en_dfi_dram_clk_disable = 0;
        ptr_pwrctl[ch]->selfref_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_poll_dqsosc_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0) == false) {
            SNPS_ERROR("Error in seq_poll_dqsosc_state");
            return false;
        }
    }
    /** -# poll for normal operating mode */
    if (dwc_ddrctl_cinit_seq_poll_operating_mode(2 * DWC_DDRCTL_MAX_APB_POLLING, 0, 1) == false) {
        SNPS_ERROR("Error in seq_poll_operating_mode");
        return false;
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_dfilpcfg0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFILPCFG0);
        ptr_dfilpcfg0->dfi_lp_data_req_en = 0;
        ptr_dfilpcfg0->dfi_lp_en_sr = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFILPCFG0, ptr_dfilpcfg0->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptr_pwrctl[ch]->stay_in_selfref = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_enter_sw_selfref(ch) == false) {
            SNPS_ERROR("Error in seq_enter_sw_selfref");
            return false;
        }
    }
    /** -# In LPDDR4, set  ptr_pwrctl[ch]->stay_in_selfref  to 0 to enter 'Self-refresh power-down' and poll stat.selfref_state = 2'b10.
     * This indicates the controller entered into self-refresh power-down state.*/
#ifdef CINIT_LPDDR4
    if (IS_LPDDR4) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptr_pwrctl[ch]->stay_in_selfref = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            if (dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x2) == false) {
                SNPS_ERROR("Error in seq_poll_selfref_state");
                return false;
            }
        }
    }
#endif
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        ptr_dfimisc->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC);
        ptr_dfimisc->dfi_init_complete_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
    }

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_dfimisc->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC);
        // toggle the dfi_freq_fsp pin to switch FSP-OP
        ptr_dfimisc->dfi_freq_fsp = (ptr_dfimisc->dfi_freq_fsp == 0) ? 1 : 0;
        ptr_dfimisc->dfi_frequency = (relock_only << 4) | target_freq;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        /** -# quasi dynamic write to set ptr_dfimisc->dfi_init_start */
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        ptr_dfimisc->dfi_init_start = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
        if (dwc_ddrctl_cinit_seq_poll_dfi_init_complete(0, 5 * DWC_DDRCTL_MAX_APB_POLLING,ch) == false) {
            SNPS_ERROR("Error in seq_poll_dfi_init_complete");
            return false;
        }
    }
    /** -# change the clock frequency to the controller */
    dwc_ddrctl_cinit_io_switch_clk(target_freq);
    /** -#  Program  mstr2->target_frequency  to the  target_frequency  value */
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_mstr2->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + MSTR2);
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        ptr_mstr2->target_frequency = target_freq;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MSTR2, ptr_mstr2->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_rfshctl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0);
        // write inverse to toggle
        ptr_rfshctl0->refresh_update_level = ~(ptr_rfshctl0->refresh_update_level);
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0, ptr_rfshctl0->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        /** -# quasi dynamic write to set dfimisc->dfi_init_start */
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        ptr_dfimisc->dfi_init_start = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
    }
    /** -# restore dfi_phyupd_en */

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_dfiupd0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0);
        ptr_dfiupd0->dfi_phyupd_en = STATIC.dfi_phyupd_en;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptr_dfiupd0->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        /** -# wait for PHY to assert dfi_init_complete */
        if (dwc_ddrctl_cinit_seq_poll_dfi_init_complete(1, 5 * DWC_DDRCTL_MAX_APB_POLLING, ch) == false) {
            SNPS_ERROR("Error in seq_poll_dfi_init_complete");
            return false;
        }
        /** -#   Set  dfimisc->dfi_init_complete_en  to '1', to indicate to the controller that PHY finished frequency change*/
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_dfimisc->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC);
        ptr_dfimisc->dfi_init_complete_en = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
    }

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_zqctl2->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL2);
        ptr_zqctl2->dis_srx_zqcl =1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL2, ptr_zqctl2->value);
    }
    if (IS_LPDDR4) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptr_pwrctl[ch]->stay_in_selfref = 1;
            ptr_pwrctl[ch]->selfref_sw = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            /** - Wait for stat.selfref_state = 0x3  */
            if (dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x3) == false) {
                SNPS_ERROR("Error in seq_poll_selfref_state");
                return false;
            }
            /** - issue ZQ calibration command  */
            dwc_ddrctl_cinit_seq_lpddr_sw_zqcal(ch);
            ptr_pwrctl[ch]->stay_in_selfref = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            if (dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x0) == false) {
                SNPS_ERROR("Error in seq_poll_selfref_state");
                return false;
            }
        }
    } else {
        // LPDDR5
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            if (dwc_ddrctl_cinit_seq_lpddr_sw_zqcal(ch) == false) {
                SNPS_ERROR("Error in seq_lpddr_sw_zqcal");
                return false;
            }
            ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptr_pwrctl[ch]->selfref_sw = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            ptr_pwrctl[ch]->stay_in_selfref = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            if (dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x0) == false) {
                SNPS_ERROR("Error in seq_poll_selfref_state");
                return false;
            }
        }
    }
    /** -# Program the controller registers back to their default values, which were disabled prior to frequency change. */
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_deratectl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0);
        ptr_deratectl0->derate_enable = prev_derate_enable;
        ptr_deratectl0->derate_mr4_pause_fc = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0, ptr_deratectl0->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_dfiupd0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0);
        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_pre_qdyn_write");
            return false;
        }
        ptr_dfiupd0->dis_auto_ctrlupd = prev_dis_auto_ctrlupd;
        ptr_dfiupd0->dfi_phyupd_en = prev_dfi_phyupd_en;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptr_dfiupd0->value);
        if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
            SNPS_ERROR("Error in seq_post_qdyn_write");
            return false;
        }
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_zqctl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0);
        ptr_zqctl0->dis_auto_zq = prev_dis_auto_zq;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0, ptr_zqctl0->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_dfiphymstr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIPHYMSTR);
        ptr_dfiphymstr->dfi_phymstr_en = prev_dfi_phymstr_en;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIPHYMSTR, ptr_dfiphymstr->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptr_pwrctl[ch]->powerdown_en = prev_powerdown_en;
        ptr_pwrctl[ch]->en_dfi_dram_clk_disable = prev_en_dfi_dram_clk_disable;
        ptr_pwrctl[ch]->selfref_en = prev_selfref_en;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }
    /// - memory sub-system is now ready again, enable hif interface
    for (uint32_t ch = 0; ch < num_ddrc; ch++)
      dwc_ddrctl_cinit_seq_set_opctrl1(0, 0, ch);

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        prev_powerdown_en = ptr_pwrctl[ch]->powerdown_en;
        prev_en_dfi_dram_clk_disable = ptr_pwrctl[ch]->en_dfi_dram_clk_disable;
        prev_selfref_en = ptr_pwrctl[ch]->selfref_en;
        ptr_pwrctl[ch]->powerdown_en = 0;
        ptr_pwrctl[ch]->en_dfi_dram_clk_disable = 0;
        ptr_pwrctl[ch]->selfref_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        dwc_ddrctl_cinit_seq_poll_dqsosc_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0);
    }
    /** -# poll for normal operating mode */
    dwc_ddrctl_cinit_seq_poll_operating_mode(2 * DWC_DDRCTL_MAX_APB_POLLING, 0, 1);
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        DFILPCFG0_t *const ptr = &REGB_DDRC_CH0.dfilpcfg0;
        ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFILPCFG0);
        ptr->dfi_lp_data_req_en = 0;
        ptr->dfi_lp_en_sr = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFILPCFG0, ptr->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        ptr_pwrctl[ch]->stay_in_selfref = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        dwc_ddrctl_cinit_seq_enter_sw_selfref(ch);
    }
    /** -# In LPDDR4, set  PWRCTL.stay_in_selfref  to 0 to enter 'Self-refresh power-down' and poll STAT.selfref_state = 2'b10.
     * This indicates the controller entered into self-refresh power-down state.*/
    if (IS_LPDDR4) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptr_pwrctl[ch]->stay_in_selfref = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x2);
        }
    }

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
	if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
            SNPS_LOG("Error in seq_pre_qdyn_write");
            return false;
	}
	ptr_dfimisc->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC);
	ptr_dfimisc->dfi_init_complete_en = 0;
	dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
	if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
            SNPS_LOG("Error in seq_post_qdyn_write");
            return false;
	}
    }


    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        // toggle the dfi_freq_fsp pin to switch FSP-OP
        ptr_dfimisc->dfi_freq_fsp = (ptr_dfimisc->dfi_freq_fsp == 0) ? 1 : 0;
        ptr_dfimisc->dfi_frequency = (relock_only << 4) | target_freq;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
    }

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
	/** -# quasi dynamic write to set DFIMISC.dfi_init_start */
	if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
            SNPS_LOG("Error in seq_pre_qdyn_write");
            return false;
	}
	ptr_dfimisc->dfi_init_start = 1;
	dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
	dwc_ddrctl_cinit_seq_post_qdyn_write(ch);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
	dwc_ddrctl_cinit_seq_poll_dfi_init_complete(0, 5 * DWC_DDRCTL_MAX_APB_POLLING, ch);
    }
	/** -# change the clock frequency to the controller */
	dwc_ddrctl_cinit_io_switch_clk(target_freq);
	/** -#  Program  MSTR2.target_frequency  to the  target_frequency  value */
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
		MSTR2_t *const ptr = &REGB_DDRC_CH0.mstr2;

		ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + MSTR2);
		if(dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                   SNPS_LOG("Error in seq_pre_qdyn_write");
                   return false;
		}
		ptr->target_frequency = target_freq;
		dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MSTR2, ptr->value);
		if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                   SNPS_LOG("Error in seq_post_qdyn_write");
                   return false;
		}
	}
	RFSHCTL0_t *const ptr = &REGB_DDRC_CH0.rfshctl0;
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {

		ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0);
		// write inverse to toggle
		ptr->refresh_update_level = ~ptr->refresh_update_level;
		dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RFSHCTL0, ptr->value);
	}
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
	    /** -# quasi dynamic write to set DFIMISC.dfi_init_start */
	    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                       SNPS_LOG("Error in seq_pre_qdyn_write");
                       return false;
	    }
	    ptr_dfimisc->dfi_init_start = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
	    if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
                       SNPS_LOG("Error in seq_post_qdyn_write");
                       return false;
	    }
        }
	/** -# restore dfi_phyupd_en */

        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
          	DFIUPD0_t *const ptr = &REGB_DDRC_CH0.dfiupd0;

		ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0);
		ptr->dfi_phyupd_en = STATIC.dfi_phyupd_en;
		dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptr->value);
	}
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
	    /** -# wait for PHY to assert dfi_init_complete */
	    dwc_ddrctl_cinit_seq_poll_dfi_init_complete(1, 5 * DWC_DDRCTL_MAX_APB_POLLING, ch);
	    /** -#   Set  DFIMISC.dfi_init_complete_en  to '1', to indicate to the controller that PHY finished frequency change*/
	    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
                SNPS_LOG("Error in seq_pre_qdyn_write");
                return false;
	    }
        }
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptr_dfimisc->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC);
            ptr_dfimisc->dfi_init_complete_en = 1;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, ptr_dfimisc->value);
            if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
            	SNPS_LOG("Error in seq_post_qdyn_write");
                    return false;
            }
        }


    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        ptr_zqctl2->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL2);
        ptr_zqctl2->dis_srx_zqcl =1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL2, ptr_zqctl2->value);
    }

    if (IS_LPDDR4) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptr_pwrctl[ch]->stay_in_selfref = 1;
            ptr_pwrctl[ch]->selfref_sw = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            /** - Wait for STAT.selfref_state = 0x3  */
            dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x3);
            /** - issue ZQ calibration command  */
            dwc_ddrctl_cinit_seq_lpddr_sw_zqcal(ch);
            ptr_pwrctl[ch]->stay_in_selfref = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x0);
        }
    } else {
        // LPDDR5
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            dwc_ddrctl_cinit_seq_lpddr_sw_zqcal(ch);
            ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
            ptr_pwrctl[ch]->selfref_sw = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            ptr_pwrctl[ch]->stay_in_selfref = 0;
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
            dwc_ddrctl_cinit_seq_poll_selfref_state(DWC_DDRCTL_MAX_APB_POLLING, ch, 0x0);
        }
    }
    /** -# Program the controller registers back to their default values, which were disabled prior to frequency change. */
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {

        ptr_deratectl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0);
        ptr_deratectl0->derate_enable = prev_derate_enable;
        ptr_deratectl0->derate_mr4_pause_fc = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0, ptr_deratectl0->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {

	ptr_dfiupd0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0);
	if (dwc_ddrctl_cinit_seq_pre_qdyn_write(ch) == false) {
		SNPS_LOG("Error in seq_pre_qdyn_write");
		return false;
	}
	ptr_dfiupd0->dis_auto_ctrlupd = prev_dis_auto_ctrlupd;
	ptr_dfiupd0->dfi_phyupd_en = prev_dfi_phyupd_en;
	dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, ptr_dfiupd0->value);
	if (dwc_ddrctl_cinit_seq_post_qdyn_write(ch) == false) {
		SNPS_LOG("Error in seq_post_qdyn_write");
		return false;
	}
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
	ptr_zqctl0->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0);
	ptr_zqctl0->dis_auto_zq = prev_dis_auto_zq;
	dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0, ptr_zqctl0->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
    	ptr_dfiphymstr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIPHYMSTR);
    	ptr_dfiphymstr->dfi_phymstr_en = prev_dfi_phymstr_en;
    	dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIPHYMSTR, ptr_dfiphymstr->value);
    }
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
    	ptr_pwrctl[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
    	ptr_pwrctl[ch]->powerdown_en = prev_powerdown_en;
    	ptr_pwrctl[ch]->en_dfi_dram_clk_disable = prev_en_dfi_dram_clk_disable;
    	ptr_pwrctl[ch]->selfref_en = prev_selfref_en;
    	dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr_pwrctl[ch]->value);
    }
    /// - memory sub-system is now ready again, enable hif interface
    for (uint32_t ch = 0; ch < num_ddrc; ch++)
    	dwc_ddrctl_cinit_seq_set_opctrl1(0, 0, ch);
    
    /// - enable all application ports
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports enable failed");
        return false;
    }

    return true;
}

/** @brief method for ZQ Calibration Commands using direct software request */
bool dwc_ddrctl_cinit_seq_lpddr_sw_zqcal(uint32_t ch)
{
    SNPS_TRACE("Entering");
    OPCTRLCMD_t * ptr_opctrlcmd = &REGB_DDRC_CH0.opctrlcmd;
    ptr_opctrlcmd->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + OPCTRLCMD);
    ptr_opctrlcmd->zq_calib_short = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRLCMD, ptr_opctrlcmd->value);
    if (dwc_ddrctl_cinit_seq_poll_zq_calib_short_busy(0, ch, DWC_DDRCTL_MAX_APB_POLLING) == false) {
        SNPS_ERROR("Error in seq_poll_zq_calib_short_busy");
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
}

/** @brief method to poll opctrlstat.zq_calib_short_busy */
bool dwc_ddrctl_cinit_seq_poll_zq_calib_short_busy(uint32_t value, uint32_t ch, uint32_t max_apb_reads)
{
    SNPS_TRACE("Entering");
    bool rslt;

    rslt = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + OPCTRLSTAT, OPCTRLSTAT_ZQ_CALIB_SHORT_BUSY_BIT_OFFSET,
                                   OPCTRLSTAT_ZQ_CALIB_SHORT_BUSY_MASK, value, max_apb_reads, 0);

    if (rslt == false) {
        SNPS_ERROR("Polling timeout, opctrlstat.zq_calib_short_busy=%u, waiting for zq_calib_short_busy=%u",
                    dwc_ddrctl_cinit_io_read_field(REGB_DDRC_CH_OFFSET(ch) + OPCTRLSTAT,
                            OPCTRLSTAT_ZQ_CALIB_SHORT_BUSY_BIT_OFFSET, OPCTRLSTAT_ZQ_CALIB_SHORT_BUSY_MASK), value);
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
}


/** @brief method to change RFM level*/
bool dwc_ddrctl_cinit_sw_seq_change_rfm_level(uint32_t rfm_level)
{
    SNPS_TRACE("Entering");
    uint8_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t apb_cnt;
    uint32_t mr_address;
    uint32_t mr_data;
    uint16_t raa_mult;
    uint16_t raa_imt;
    uint16_t raa_rfm;
    bool sw_init_int = false;
    uint32_t pwrctl_ini[2];
    uint32_t hwlpctl_ini[2];

    OPCTRL1_t *const opctrl1_ptr[2]  = {
	    &REGB_DDRC_CH0.opctrl1,
	    &REGB_DDRC_CH1.opctrl1
    };
    PWRCTL_t *const pwrctl_ptr[2] = {
	    &REGB_DDRC_CH0.pwrctl,
	    &REGB_DDRC_CH1.pwrctl
    };
    HWLPCTL_t *const hwlpctl_ptr[2] = {
	    &REGB_DDRC_CH0.hwlpctl,
	    &REGB_DDRC_CH1.hwlpctl
    };
    RFMSTAT_t *const rfmstat_ptr = &REGB_DDRC_CH0.rfmstat;
    RFMMOD0_t *const rfmmod0_ptr = &REGB_DDRC_CH0.rfmmod0;
    MRRDATA0_t *const mrrdata0_ptr[2] = {
       &REGB_DDRC_CH0.mrrdata0,
       &REGB_DDRC_CH1.mrrdata0
    };

    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    /** @brief step_1. disable low-power on both channels */
    for (uint8_t ch = 0; ch < num_ddrc; ch++) {
        hwlpctl_ptr[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + HWLPCTL);
        pwrctl_ptr[ch]->value  = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        hwlpctl_ini[ch] = hwlpctl_ptr[ch]->value;
        pwrctl_ini[ch]  = pwrctl_ptr[ch]->value;
        hwlpctl_ptr[ch]->hw_lp_en = 0;
        pwrctl_ptr[ch]->selfref_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, pwrctl_ptr[ch]->value);
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + HWLPCTL, hwlpctl_ptr[ch]->value);
    }

    /** @brief step_2. poll STAT.operating_mode=1 3 times in a row - specific mentioned in programming guide */
    for (uint8_t cnt = 0; cnt < 3; cnt++) {
       if (dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, 0, 1) == false) {
           SNPS_ERROR("Error in seq_poll_operating_mode");
           return false;
       }
    }

    /** @brief step_3a. disable HIF commands */
    for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      opctrl1_ptr[ch]->dis_hif = 1;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRL1, opctrl1_ptr[ch]->value);
    }

    /** @brief step_3b. poll OPCTRLCAM.dbg_wr_q_empty=1, OPCTRLCAM.wr_data_pipeline_empty=1 - wait OPCTRLCAM empty */
    if(dwc_ddrctl_cinit_seq_wait_opctrlcam_empty(DWC_DDRCTL_MAX_APB_POLLING) == false) {
      SNPS_ERROR("Error in waiting OPCTRLCAM empty");
      return false;
    }

    /** @brief step_4. poll RFMSTAT.rank_raa_cnt_gt0=0 for 8*tREFI (worst case) */
    apb_cnt=0;
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      do {
         rfmstat_ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + RFMSTAT);
         if (apb_cnt == DWC_DDRCTL_MAX_APB_POLLING) {
            SNPS_ERROR("Polling timeout RFMSTAT.rank_raa_cnt_gt0, current value=%u", rfmstat_ptr->rank_raa_cnt_gt0);
            return false;
         }
         apb_cnt++;
      } while (rfmstat_ptr->rank_raa_cnt_gt0 != 0);
    }

    /** @brief step_5. change RFM level by sending MRW commands to MR57 using MCTRL0 and MCTRL1 */
    mr_address = 57;
    LPDDR5_MR[0].mr57.arfm = (rfm_level & 0x00000003); //rfm_leven is 2 bit value
    mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr57.raa_dec, 2, 0) |
              DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr57.rfm_sb, 2, 2)  |
              DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr57.rfm_sbc, 2, 4) |
              DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr57.arfm, 2, 6);
    for (uint8_t ch = 0; ch < num_ddrc; ch++) {
       if (dwc_ddrctl_cinit_seq_mr_access(0, mr_address, mr_data, 1, sw_init_int, ch) == false) {
          SNPS_ERROR("Error in seq_mr_access: MRW to MR57");
          return false;
       }
    }

    /** @brief step_6. read RAAIMT, RAAMULT, RAADEC by sending MRR commands to MR27 using MCTRL0 and MCTRL1 */
    mr_address = 27;
    mr_data = DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr27.raa_rfm, 1, 0) |
              DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr27.raa_imt, 5, 1) |
              DWC_DDRCTL_SETREGBITFIELDSHIFT(LPDDR5_MR[0].mr27.raa_mult, 2, 6);
    for (uint8_t ch = 0; ch < num_ddrc; ch++) {
       if (dwc_ddrctl_cinit_seq_mr_access(1, mr_address, mr_data, 1, sw_init_int, ch) == false) {
          SNPS_ERROR("Error in seq_mr_access: MRW to MR57");
          return false;
       }
    }

    /** @brief step_7. Program RFMOD0.raaimt/raadec/raamult/rfm_rm_thr with MRRDATA0 values available from previous step (MRR) */
    for (uint8_t ch = 0; ch < num_ddrc; ch++) {
       mrrdata0_ptr[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + MRRDATA0);
    }
    rfmmod0_ptr->raaimt = ((mrrdata0_ptr[0]->value) >> 1);
    rfmmod0_ptr->raadec = LPDDR5_MR[0].mr57.raa_dec;
    rfmmod0_ptr->raamult = ((mrrdata0_ptr[0]->value) >> 6);
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RFMMOD0, rfmmod0_ptr->value);
    }

    /** @Brief step_8. enable HIF commands */
    for (uint8_t ch = 0; ch < num_ddrc; ch++) {
       opctrl1_ptr[ch]->dis_hif = 0;
       dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRL1, opctrl1_ptr[ch]->value);
    }

    /** @brief step_9. restore PWRCTL/HWLPCTL to previous values */
    for (uint8_t ch = 0; ch < num_ddrc; ch++) {
       hwlpctl_ptr[ch]->value = hwlpctl_ini[ch];
       pwrctl_ptr[ch]->value  = pwrctl_ini[ch];
       dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, pwrctl_ptr[ch]->value);
       dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + HWLPCTL, hwlpctl_ptr[ch]->value);
    }

    return true;
}

/** @brief method to initiate sefl refresh while retrain PPT2*/
bool dwc_ddrctl_cinit_sw_seq_selfref_with_retrain_ppt2(void)
{
   ddrctl_error_t  rslt;
   uint8_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
   uint8_t apb_cnt;
   uint32_t timer=0;
   uint32_t freq =0;
   uint32_t hwlpctl_ini[2];
   uint32_t pwrctl_ini[2];
   uint8_t port_en[UMCTL2_A_NPORTS];
   uint32_t dfilpcfg0_ini;
   bool res;
   bool sw_init_int = false;
   DFIUPDTMG2_t *const DFIUPDTMG2_ptr[2] = {
		&REGB_FREQ_CH0(freq).dfiupdtmg2,
		&REGB_FREQ_CH1(freq).dfiupdtmg2
	};
   PWRCTL_t *const pwrctl_ptr[2] = {
      &REGB_DDRC_CH0.pwrctl,
      &REGB_DDRC_CH1.pwrctl
   };
   HWLPCTL_t *const hwlpctl_ptr[2] = {
	   &REGB_DDRC_CH0.hwlpctl,
	   &REGB_DDRC_CH1.hwlpctl
   };
   OPCTRL1_t *const opctrl1_ptr[2]  = {
	   &REGB_DDRC_CH0.opctrl1,
	   &REGB_DDRC_CH1.opctrl1
   };
   DERATECTL0_t *const deratectl0_ptr = &REGB_DDRC_CH0.deratectl0;
   DFIUPD0_t    *const dfiupd0_ptr = &REGB_DDRC_CH0.dfiupd0;
   DFILPCFG0_t  *const dfilpcfg0_ptr = &REGB_DDRC_CH0.dfilpcfg0;
   OPCTRLCMD_t  *const opctrlcmd_ptr[2] = {
      &REGB_DDRC_CH0.opctrlcmd,
      &REGB_DDRC_CH1.opctrlcmd
   };
   STAT_t       *const stat_ptr[2] = {
      &REGB_DDRC_CH0.stat,
      &REGB_DDRC_CH1.stat
   };
   DFIMISC_t *const dfimisc_ptr = &REGB_DDRC_CH0.dfimisc;
   ZQCTL0_t  *const zqctl0_ptr  = &REGB_DDRC_CH0.zqctl0;
   PPT2CTRL0_t *const ppt2ctrl0_ptr = &REGB_DDRC_CH0.ppt2ctrl0;
   PPT2STAT0_t *const ppt2stat0_ptr = &REGB_DDRC_CH0.ppt2stat0;

    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY


   /** @brief step 1: set DFIUPDTMG2.ppt2_en=1 */
	for (uint32_t ch = 0; ch < num_ddrc; ch++) {
		DFIUPDTMG2_ptr[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, ch) + DFIUPDTMG2);
      if(DFIUPDTMG2_ptr[ch]->ppt2_en == 0) {
         DFIUPDTMG2_ptr[ch]->ppt2_en = 1;
         dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, ch) + DFIUPDTMG2, DFIUPDTMG2_ptr[ch]->value);
      }
	}

   /** @brief step 2: disable low-power on both channels */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
        hwlpctl_ptr[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + HWLPCTL);
        pwrctl_ptr[ch]->value  = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
        hwlpctl_ini[ch] = hwlpctl_ptr[ch]->value;
        pwrctl_ini[ch]  = pwrctl_ptr[ch]->value;
        hwlpctl_ptr[ch]->hw_lp_en = 0;
        pwrctl_ptr[ch]->selfref_en = 0;
        pwrctl_ptr[ch]->powerdown_en = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, pwrctl_ptr[ch]->value);
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + HWLPCTL, hwlpctl_ptr[ch]->value);
   }

   /** @brief step 3: poll STAT.operating_mode=1 3 times in a row - specific mentioned in 2.4.5 from programming guide */
   for (uint8_t cnt = 0; cnt < 3; cnt++) {
       if (dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, 0, 1) == false) {
           SNPS_ERROR("Error in seq_poll_operating_mode");
           return false;
       }
   }

   /** @brief step 4: set PCTRl.port_en=0 to block AXI ports; poll PSTAT_rd_port_busy=0/wr_port_busy=0 */
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_DISABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports disable failed");
        return false;
    }

    /** -# @brief step 5: Disable the Scubber for all channels and wait until is idle
     * This is only required if SBR is instantiated
     */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_DISABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber disable failed");
        return false;
    }

   /** @brief step_6a: disable HIF commands */
    for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      opctrl1_ptr[ch]->dis_hif = 1;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRL1, opctrl1_ptr[ch]->value);
    }

    /** @brief step_6b. poll OPCTRLCAM.dbg_wr_q_empty=1, OPCTRLCAM.wr_data_pipeline_empty=1 - wait OPCTRLCAM empty */
    if(dwc_ddrctl_cinit_seq_wait_opctrlcam_empty(DWC_DDRCTL_MAX_APB_POLLING) == false) {
      SNPS_ERROR("Error in waiting OPCTRLCAM empty");
      return false;
    }

   /** @brief step_7: if derate_enable=1, pause automatic MRR to MR4 */
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
	deratectl0_ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0);
	if(deratectl0_ptr->derate_enable == 1) {
		deratectl0_ptr->derate_mr4_pause_fc = 1;
		dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0, deratectl0_ptr->value);
         }
    }

   /** @brief step_8: if DFIUPD0.disable_auto_ctrlupd=0, set DFIUPD0.disable_auto_ctrlupd=1 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
       dfiupd0_ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0);
       if(dfiupd0_ptr->dis_auto_ctrlupd == 0) {
          dfiupd0_ptr->dis_auto_ctrlupd = 1;
          dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, dfiupd0_ptr->value);
       }
   }

   /** @brief step_9: issue DFI update request manually */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      opctrlcmd_ptr[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + OPCTRLCMD);
      opctrlcmd_ptr[ch]->ctrlupd = 1;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRLCMD, opctrlcmd_ptr[ch]->value);

      //step 9b: poll OPCTRLSTAT.ctrlupd_busy=0
      res = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + OPCTRLSTAT, OPCTRLSTAT_CTRLUPD_BUSY_BIT_OFFSET,
                                 OPCTRLSTAT_CTRLUPD_BUSY_MASK, 0, DWC_DDRCTL_MAX_APB_POLLING, 0);
      if(res == false) {
         SNPS_ERROR("Error in poll OPCTRLSTAT.ctrlupd_busy=0");
         return false;
      }
   }

   /** @brief step_10a. if dfi_lp_en_sr=1, set dfo_lp_en_sr=0, retain DFILPCFG0 value to be restored later */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
       dfilpcfg0_ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFILPCFG0);
       dfilpcfg0_ini = dfilpcfg0_ptr->value;
       if(dfilpcfg0_ptr->dfi_lp_en_sr == 1) {
          dfilpcfg0_ptr->dfi_lp_en_sr = 0;
          dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFILPCFG0, dfilpcfg0_ptr->value);
       }
   }
   /** @brief step_10b: poll DFISTAT.dfi_lp_ctrl_ack_stat=0 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
       res = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + DFISTAT, DFISTAT_DFI_LP_CTRL_ACK_STAT_BIT_OFFSET,
                                       DFISTAT_DFI_LP_CTRL_ACK_STAT_MASK, 0, DWC_DDRCTL_MAX_APB_POLLING, 0);
       if(res == false) {
          SNPS_ERROR("Error in poll DFISTAT.dfi_lp_ctrl_ack_stat=0");
          return false;
       }
   }


   /** @brief step_11. if dfi_lp_data_req_en=1, set dfi_lp_data_req_en_sr=0 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      dfilpcfg0_ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFILPCFG0);
      if(dfilpcfg0_ptr->dfi_lp_data_req_en == 1) {
         dfilpcfg0_ptr->dfi_lp_data_req_en = 0;
         dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFILPCFG0, dfilpcfg0_ptr->value);
      }
   }

   /** @brief step_11b: poll DFISTAT.dfi_lp_ctrl_ack_stat=0 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
       res = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + DFISTAT, DFISTAT_DFI_LP_CTRL_ACK_STAT_BIT_OFFSET,
                                       DFISTAT_DFI_LP_CTRL_ACK_STAT_MASK, 0, DWC_DDRCTL_MAX_APB_POLLING, 0);
       if(res == false) {
          SNPS_ERROR("Error in poll DFISTAT.dfi_lp_ctrl_ack_stat=0");
          return false;
       }
   }

   /** @brief step_12. set PWRCTL.en_dfi_dram_clk_disable=0 */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      pwrctl_ptr[ch]->value  = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
      pwrctl_ptr[ch]->en_dfi_dram_clk_disable = 0;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, pwrctl_ptr[ch]->value);
   }

   /** @brief step_13. enter self refresh by set PWRCTL.selfref=1, poll for operating mode=3 */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      pwrctl_ptr[ch]->selfref_sw = 1;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, pwrctl_ptr[ch]->value);
      if (dwc_ddrctl_cinit_seq_poll_operating_mode(2 * DWC_DDRCTL_MAX_APB_POLLING, ch, 3) == false) {
        SNPS_ERROR("Error in seq_poll_operating_mode");
        return false;
      }
   }

   /** @brief step_14. check STAT.selfref_type = 2 */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      res = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + STAT, STAT_SELFREF_TYPE_BIT_OFFSET,
                                   STAT_SELFREF_TYPE_MASK, 2, DWC_DDRCTL_MAX_APB_POLLING, 0);
      if(res == false) {
         SNPS_ERROR("Timeout error for polling STAT.selfref_type=%u", stat_ptr[ch]->selfref_type);
      }
   }

   /** @brief step_15. set OPCTRL1.dis_dq=1, poll OPCTRLCAM.wr/rd_data_pipeline_empty=1 */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      opctrl1_ptr[ch]->dis_dq = 1;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRL1, opctrl1_ptr[ch]->value);
   }
   if(dwc_ddrctl_cinit_seq_wait_opctrlcam_empty(DWC_DDRCTL_MAX_APB_POLLING) == false) {
      SNPS_ERROR("Error in waiting OPCTRLCAM empty");
      return false;
   }

   /** @brief step_16. set DFIMISC.dfi_init_complete_en=0 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      dfimisc_ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC);
      dfimisc_ptr->dfi_init_complete_en=0;
      dfimisc_ptr->dfi_frequency = DFI_FREQ_23;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, dfimisc_ptr->value);
   }

   /** @brief step_18. wait a no. of cycles */
   dwc_ddrctl_cinit_io_wait_ddrc_clk(DWC_DDRCTL_LPDDR5_SW_SREF_PPT2_DELAY);

   /** @brief step_19. stop PHY pipelines */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      dfimisc_ptr->dfi_init_start = 1;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, dfimisc_ptr->value);
   }

   /** @brief step_20. poll  DFISTAT.dfi_init_complete=1 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      res = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + DFISTAT, DFISTAT_DFI_INIT_COMPLETE_BIT_OFFSET,
                                      DFISTAT_DFI_INIT_COMPLETE_MASK, 1, DWC_DDRCTL_MAX_APB_POLLING, 0);
      if(res == false) {
         SNPS_ERROR("Error in poll DFISTAT.dfi_init_complete=0");
         return false;
      }
   }

   /** @brief step_21. initiate re-lock PLLs and calibrate ZQ/Delay-Lines */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
     dfimisc_ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC);
     dfimisc_ptr->dfi_init_start=0;
     dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, dfimisc_ptr->value);
   }

   /** @brief step_22. poll  DFISTAT.dfi_init_complete=1 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      res = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + DFISTAT, DFISTAT_DFI_INIT_COMPLETE_BIT_OFFSET,
                                      DFISTAT_DFI_INIT_COMPLETE_MASK, 1, DWC_DDRCTL_MAX_APB_POLLING, 0);
      if(res == false) {
         SNPS_ERROR("Error in poll DFISTAT.dfi_init_complete=1");
         return false;
      }
   }

   /** @brief step_23. set DFIMISC.dfi_init_complete_en=1 (Ctrl finished retraining) */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      dfimisc_ptr->dfi_init_complete_en=1;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, dfimisc_ptr->value);
   }


   /** @brief step_24. start burst PPT2 process */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      zqctl0_ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0);
      if(zqctl0_ptr->dis_auto_zq == 0) {
         zqctl0_ptr->dis_auto_zq = 1;
         dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0, zqctl0_ptr->value);
      }
   }

   /** @brief step_25. set PPT2CTRL0.ppt2_burst=1 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      ppt2ctrl0_ptr->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PPT2CTRL0);
      ppt2ctrl0_ptr->ppt2_burst = 1;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PPT2CTRL0, ppt2ctrl0_ptr->value);
   }

   /** @brief step_26. Exit Self-Refresh */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      pwrctl_ptr[ch]->value  = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
      pwrctl_ini[ch]  = pwrctl_ptr[ch]->value;
      pwrctl_ptr[ch]->selfref_sw = 0;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, pwrctl_ptr[ch]->value);
      res = dwc_ddrctl_cinit_seq_wait_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, ch, 3);
      if(res == false) {
         SNPS_ERROR("Timeout error for polling STAT.operating_mode=%u, !=2'b11", stat_ptr[ch]->operating_mode);
      }
   }

   /** @brief step_27. Wait for PPT2 to complete */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      res = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + PPT2STAT0, PPT2STAT0_PPT2_BURST_BUSY_BIT_OFFSET,
                                    PPT2STAT0_PPT2_BURST_BUSY_MASK, 0, 10*DWC_DDRCTL_MAX_APB_POLLING, 0);
      if(res == false) {
         SNPS_ERROR("Error in poll PPT2STAT.ppt2_burst_busy=0");
         return false;
      }
   }

   /** @brief step_28. reset ZQCTL0.dis_auto_zq=0 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      if(zqctl0_ptr->dis_auto_zq == 1) {
         zqctl0_ptr->dis_auto_zq = 0;
         dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL0, zqctl0_ptr->value);
      }
   }

   /** @brief step_29. restore DFILPCFG0 to it's value prior to step_10*/
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      dfilpcfg0_ptr->value = dfilpcfg0_ini;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFILPCFG0, dfilpcfg0_ptr->value);
   }

   /** @brief step_30. set OPCTRL1.dis_dq=0 */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      opctrl1_ptr[ch]->dis_dq = 0;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRL1, opctrl1_ptr[ch]->value);
   }

   /** @brief step_31/32. Enable HIF */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      opctrl1_ptr[ch]->dis_hif = 0;
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRL1, opctrl1_ptr[ch]->value);
   }

   /** @brief step_33. reset DERATECTL0.derate_mr4_pause_fc=0 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      if(deratectl0_ptr->derate_mr4_pause_fc == 1) {
      	deratectl0_ptr->derate_mr4_pause_fc = 0;
      	dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL0, deratectl0_ptr->value);
      }
   }

   /** @brief step_34. reset DFIUPD0.dis_auto_ctrlupd=0 */
   for (uint32_t ch = 0; ch < num_ddrc; ch++) {
      if(dfiupd0_ptr->dis_auto_ctrlupd == 1) {
         dfiupd0_ptr->dis_auto_ctrlupd = 0;
         dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIUPD0, dfiupd0_ptr->value);
      }
   }

   /** @brief step_35/36: enable low-power on both channels if was disabled */
   for (uint8_t ch = 0; ch < num_ddrc; ch++) {
      hwlpctl_ptr[ch]->value = hwlpctl_ini[ch];
      pwrctl_ptr[ch]->value = pwrctl_ini[ch];
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, pwrctl_ptr[ch]->value);
      dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + HWLPCTL, hwlpctl_ptr[ch]->value);
   }

   /** @brief step_37. enable AXI ports and scrubber */
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports disable failed");
        return false;
    }

    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_ENABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber enable failed");
        return false;
    }

   return true;
}


/// @} // end LPDDRSwSeqGrp
#endif /* DDRCTL_LPDDR */
