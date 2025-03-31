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
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_cinit_log.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "sw_cmd_intf/ddr5/cinit_ddr5_sw_cmd.h"
#include "phy/sinit_phy_utils.h"
#include "physetup.h"
#include "cinit_status.h"
#include "cinit_port_util.h"
#include "dwc_ddrctl_cinit_types_str.h"

/** @defgroup SwSeqCommonGrp Common software methods/sequences
 * This section groups together software sequences and methods that are common to both DDR54 and LPDDR54 controllers.
 * @{
 */

/**
 * @brief method to control power on reset.
 * This method implements cold reset/power up sequence.
 * The PHY requires PwrOkIn signal is low and Reset signal is high at time 0.
 */
bool dwc_ddrctl_cinit_seq_pwr_on_rst(void)
{
    SNPS_TRACE("Entering");
    dwc_ddrctl_cinit_io_power(false);
    /// - Apply resets
    dwc_ddrctl_cinit_io_presetn(false);
    dwc_ddrctl_cinit_io_ddrc_rstn(0);
    if (IS_ARB_CONFIG)
        dwc_ddrctl_cinit_io_aresetn(0);
    /// - Enable clocks
    // dwc_ddrctl_cinit_io_set_pclk(1); // UVM_TB always enables PCLK
    // from time 0ns.
    dwc_ddrctl_cinit_io_set_ddrc_clk(true);
    dwc_ddrctl_cinit_io_wait_ddrc_clk(10);
    dwc_ddrctl_cinit_io_power(true);
    if (IS_ARB_CONFIG)
        dwc_ddrctl_cinit_io_set_axi_clk(true);
    /// - wait for stable clk
    dwc_ddrctl_cinit_io_wait_pclk(4);
    /// - release PRESETn
    dwc_ddrctl_cinit_io_presetn(true);
    /// - allow 128 cycles for synchronization
    dwc_ddrctl_cinit_io_wait_ddrc_clk(128);
    SNPS_TRACE("Leaving");
    return true;
}


/**
 * @brief method to poll stat register for operating mode.
 */
bool dwc_ddrctl_cinit_seq_poll_operating_mode(uint32_t timeout_us, uint32_t ch, uint32_t mode)
{
    SNPS_TRACE("Entering");
    bool rslt;

    rslt = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + STAT, STAT_OPERATING_MODE_BIT_OFFSET,
                                   STAT_OPERATING_MODE_MASK, mode, timeout_us, 0);

    if (rslt == false) {
        SNPS_ERROR("Polling timeout,CH = %u  STAT.operating_mode=%u, waiting for operating_mode=%u", ch,
                    dwc_ddrctl_cinit_io_read_field(REGB_DDRC_CH_OFFSET(ch) + STAT,
                                   STAT_OPERATING_MODE_BIT_OFFSET, STAT_OPERATING_MODE_MASK), mode);
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to poll stat register for selfref_type.
 */
bool dwc_ddrctl_cinit_seq_poll_selfref_type(uint32_t timeout_us, uint32_t ch, uint32_t selfref_type)
{
    SNPS_TRACE("Entering");
    bool rslt;

    rslt = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + STAT, STAT_SELFREF_TYPE_BIT_OFFSET,
                                   STAT_SELFREF_TYPE_MASK, selfref_type, timeout_us, 0);

    if (rslt == false) {
        SNPS_ERROR("Polling timeout, CH = %u STAT.selfref_type=%u, waiting for selfref_type=%u", ch,
                    dwc_ddrctl_cinit_io_read_field(REGB_DDRC_CH_OFFSET(ch) + STAT,
                                   STAT_SELFREF_TYPE_BIT_OFFSET, STAT_SELFREF_TYPE_MASK), selfref_type);
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to poll dfistat.dfi_init_complete
 * @param value to wait for
 * @param max_apb_reads maximum number of times to read the register before
 * timing out
 */
bool dwc_ddrctl_cinit_seq_poll_dfi_init_complete(uint32_t value, uint32_t max_apb_reads, uint32_t ch)
{
    SNPS_TRACE("Entering");
    bool rslt;

    rslt = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + DFISTAT, DFISTAT_DFI_INIT_COMPLETE_BIT_OFFSET,
                                   DFISTAT_DFI_INIT_COMPLETE_MASK, value, max_apb_reads, 0);

    if (rslt == false) {
        SNPS_ERROR("Polling timeout, DFISTAT.dfi_init_complete=%u, waiting for dfi_init_complete=%u ch=%u",
            dwc_ddrctl_cinit_io_read_field(REGB_DDRC_CH_OFFSET(ch) + DFISTAT, DFISTAT_DFI_INIT_COMPLETE_BIT_OFFSET,
                                           DFISTAT_DFI_INIT_COMPLETE_MASK), value, ch);
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to poll swstat.sw_done_ack
 * @param value to wait for
 * @param max_apb_reads maximum number of times to read the register before
 */
bool dwc_ddrctl_cinit_seq_poll_sw_done_ack(uint32_t value, uint32_t max_apb_reads, uint32_t ch)
{
    SNPS_TRACE("Entering");
    bool rslt;

    rslt = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + SWSTAT, SWSTAT_SW_DONE_ACK_BIT_OFFSET,
                                   SWSTAT_SW_DONE_ACK_MASK, value, max_apb_reads, 0);

    if (rslt == false) {
        SNPS_ERROR("Polling timeout SWSTAT.sw_done_ack=%u waiting for sw_done_ack=%u, ch=%u",
                    dwc_ddrctl_cinit_io_read_field(REGB_DDRC_CH_OFFSET(ch) + SWSTAT, SWSTAT_SW_DONE_ACK_BIT_OFFSET,
                                                   SWSTAT_SW_DONE_ACK_MASK), value, ch);
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to initialize the PHY to mission mode by performing a DFI initialization sequence per the DFI specification.
 * @{
 */
bool dwc_ddrctl_cinit_seq_dfi_initialization(void)
{
    uint32_t        num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    uint32_t        num_dwc_ddrctl=1;
    bool            rslt_bool;

#ifdef CINIT_DDR5
    ddrctl_error_t  rslt;
#ifdef DDRCTL_SINGLE_INST_DUALCH
    num_dwc_ddrctl=2; // two controller instances
#endif // DDRCTL_SINGLE_INST_DUALCH
    /** -# Below substeps for DDR5 only */
    /** -# release the dfi_reset_n before dfi_init_start/dfi_init_complete handshake */

    rslt = cinit_ddr5_send_reset_control(hdlr, DDRCTL_CHANNEL_ALL, DDRCTL_DISABLE, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Send SRE to all ranks of all channels Error");
        return false;
    }

#endif // CINIT_DDR5
#ifdef LPDDR_2MC1PHY
    num_ddrc = 2;
    num_dwc_ddrctl=2;
#endif // LPDDR_2MC1PHY
    for (uint32_t ch = 0; ch < num_dwc_ddrctl; ch++) {
        /// - quasi dynamic write to set dfimisc.dfi_init_start
        rslt_bool = dwc_ddrctl_cinit_seq_pre_qdyn_write(ch);
        if (false == rslt_bool) {
            SNPS_LOG("Error in seq_pre_qdyn_write");
            return false;
        }

        REGB_DDRC_CH0.dfimisc.dfi_init_start = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, REGB_DDRC_CH0.dfimisc.value);

        rslt_bool = dwc_ddrctl_cinit_seq_post_qdyn_write(ch);
        if (false == rslt_bool) {
            SNPS_LOG("Error in seq_post_qdyn_write");
            return false;
        }
    }

    for (uint32_t ch = 0; ch < num_dwc_ddrctl; ch++) {
        /// - wait for dfi_init complete
        rslt_bool = dwc_ddrctl_cinit_seq_poll_dfi_init_complete(1, 5 * DWC_DDRCTL_MAX_APB_POLLING, ch);
        if(false == rslt_bool) {
            SNPS_LOG("Error in seq_poll_dfi_init_complete");
            return false;
        }
    }

    for (uint32_t ch = 0; ch < num_dwc_ddrctl; ch++) {
        /// - quasi dynamic write to set dfimisc.dfi_init_complete_en
        rslt_bool =  dwc_ddrctl_cinit_seq_pre_qdyn_write(ch);
        if (false == rslt_bool) {
            SNPS_LOG("Error in seq_pre_qdyn_write");
            return false;
        }

        REGB_DDRC_CH0.dfimisc.dfi_init_start = 0;
        REGB_DDRC_CH0.dfimisc.dfi_init_complete_en = 1;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIMISC, REGB_DDRC_CH0.dfimisc.value);

        rslt_bool = dwc_ddrctl_cinit_seq_post_qdyn_write(ch);
        if (false == rslt_bool) {
            SNPS_LOG("Error in seq_post_qdyn_write");
            return false;
        }
    }

    if (CFG->phy_training == DWC_PHY_SKIP_TRAINING || IS_DDR4) {
        if ((CINIT_IS_RDIMM(hdlr) == DDRCTL_TRUE) || (CINIT_IS_LRDIMM(hdlr) == DDRCTL_TRUE)) {
            SNPS_LOG("Wait until tSTAB %d", QDYN.t_stab_x32[0][0]);
            dwc_ddrctl_cinit_io_wait_pclk(QDYN.t_stab_x32[0][0] * 32);
        }
    }

    /// - exit SW selfref
    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING) {
        for (uint32_t ch = 0; ch < num_ddrc; ch++) {
            rslt_bool = dwc_ddrctl_cinit_seq_exit_sw_selfref(ch);
            if (false == rslt_bool) {
                SNPS_LOG("Error in seq_exit_sw_selfref");
                return false;
            }
        }
    }
    return true;
    /// @}
}

/**
 * @brief method to set swctl.sw_done to 0.
 * @param ch channel number
 * @note channel number if only applicable when DDRCTL_SINGLE_INST_DUALCH is set
 */
bool dwc_ddrctl_cinit_seq_pre_qdyn_write(uint8_t ch)
{
    SNPS_TRACE("Entering");
    SWCTL_t * swctl = &REGB_DDRC_CH0.swctl;

    swctl->sw_done = 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + SWCTL, swctl->value);
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to set swctl.sw_done and wait for swstat.sw_done_ack.
 * @param ch channel number
 * @note channel number if only applicable when DDRCTL_SINGLE_INST_DUALCH is set
 */
bool dwc_ddrctl_cinit_seq_post_qdyn_write(uint8_t ch)
{
    SNPS_TRACE("Entering");
    SWCTL_t * swctl = &REGB_DDRC_CH0.swctl;

    swctl->sw_done = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + SWCTL, swctl->value);
    if (dwc_ddrctl_cinit_seq_poll_sw_done_ack(1, DWC_DDRCTL_MAX_APB_POLLING, ch) == false) {
        SNPS_LOG("Error in seq_poll_sw_done_ack");
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to enter software self refresh.
 * @param ch channel number
 */
bool dwc_ddrctl_cinit_seq_enter_sw_selfref(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PWRCTL_t pwrctl;
    uint32_t operating_mode;

    // perform RMW to pwrctl.selfref_sw
    pwrctl.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
    pwrctl.selfref_sw = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, pwrctl.value);
    operating_mode = 3; // all ranks in selfref
    if (dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, ch, operating_mode) == false) {
        SNPS_ERROR("Error in seq_poll_operating_mode");
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to exit software self refresh.
 * @param ch channel number
 */
bool dwc_ddrctl_cinit_seq_exit_sw_selfref(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PWRCTL_t pwrctl;
    bool ret;

    pwrctl.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL);
    pwrctl.selfref_sw = 0;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, pwrctl.value);
    if (IS_DDR5) {
        ret = dwc_ddrctl_cinit_seq_poll_selfref_type(DWC_DDRCTL_MAX_APB_POLLING, ch, 0);
    } else {
        // wait for normal operation mode
        ret = dwc_ddrctl_cinit_seq_poll_operating_mode(DWC_DDRCTL_MAX_APB_POLLING, ch, 1);
    }
    SNPS_TRACE("Leaving");
    return ret;
}

/**
 * @brief method to set inittmg0.skip_dram_init in both channels
 */
bool dwc_ddrctl_cinit_seq_set_skip_dram_init(uint32_t skp)
{
    SNPS_TRACE("Entering");
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;
    INITTMG0_t inittmg0;
    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        inittmg0.value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + INITTMG0);
        inittmg0.skip_dram_init = skp;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + INITTMG0, inittmg0.value);
    }
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to wait until the CAM debug signal indicate that it is empty
 * @param max_apb_reads maximum number of times to read the register before
 */
bool dwc_ddrctl_cinit_seq_wait_opctrlcam_empty(uint32_t max_apb_reads)
{
    ddrctl_error_t  rslt;
    uint32_t        mask;
    uint32_t        expected;
    uint8_t         num_channels;
    uint8_t         channel;
    uint8_t         offset;

    num_channels = (STATIC.dual_channel_en == 1) ? 2 : 1;
    offset = 0;
    mask  = OPCTRLCAM_DBG_RD_Q_EMPTY_MASK;
    mask |= OPCTRLCAM_DBG_WR_Q_EMPTY_MASK;
    mask |= OPCTRLCAM_RD_DATA_PIPELINE_EMPTY_MASK;
    mask |= OPCTRLCAM_WR_DATA_PIPELINE_EMPTY_MASK;
    expected = mask;

    for (channel = 0; channel < num_channels; channel++) {
        rslt = cinit_poll_bitfield(REGB_DDRC_CH_OFFSET(channel) + OPCTRLCAM, offset, mask,
                                   expected, max_apb_reads, 0);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Polling timeout, REGB_DDRC_CH%u.opctrlcam, current value=0x%08x", channel,
                        dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(channel) + OPCTRLCAM));
            return false;
        }
    }
    return true;
}

/**
 * @brief wait until the controller is idle
 * @param max_apb_reads maximum number of times to read the register before
 */
bool dwc_ddrctl_cinit_seq_wait_ctrlr_idle(uint32_t max_apb_reads)
{
    if (ddrctl_cinit_wait_ports_idle(max_apb_reads) != DDRCTL_SUCCESS) {
        SNPS_ERROR("Error in seq_wait_pstat_not_busy");
        return false;
    }

    if (dwc_ddrctl_cinit_seq_wait_opctrlcam_empty(max_apb_reads) == false) {
        SNPS_ERROR("Error in seq_wait_opctrlcam_empty");
        return false;
    }

    return true;
}


/**
 * @brief method to set dis_dq and dis_hif
 * @param dis_dq value for dis_dq
 * @param dis_hif value for dis_hif
 * @param ch channel number
 */
bool dwc_ddrctl_cinit_seq_set_opctrl1(uint8_t dis_dq, uint8_t dis_hif, uint8_t ch)
{
    SNPS_TRACE("Entering");
    OPCTRL1_t *const ptr[2] = {
        &REGB_DDRC_CH0.opctrl1,
        &REGB_DDRC_CH1.opctrl1
    };
    ptr[ch]->value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + OPCTRL1);
    ptr[ch]->dis_dq = dis_dq;
    ptr[ch]->dis_hif = dis_hif;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRL1, ptr[ch]->value);
    SNPS_TRACE("Leaving");
    return true;
}

/** @brief method to poll mrstat
 * @param value to wait for
 * @param ch channel number
 * @param max_apb_reads maximum number of times to read the register before timing out
 */
bool dwc_ddrctl_cinit_seq_poll_mr_wr_busy(uint32_t value, uint32_t ch, uint32_t max_apb_reads)
{
    SNPS_TRACE("Entering");
    bool rslt;

    rslt = dwc_ddctl_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + MRSTAT, MRSTAT_MR_WR_BUSY_BIT_OFFSET,
                                   MRSTAT_MR_WR_BUSY_MASK, value, max_apb_reads, 0);

    if (rslt == false) {
        SNPS_ERROR("Polling timeout, mrstat.mr_wr_busy=%u, waiting for mr_wr_busy=%u",
                    dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + MRSTAT), value);
        return false;
    }
    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief method to begin programming all the controller registers
 */
bool dwc_ddrctl_cinit_seq_initialize_ctrl_regs(void)
{
    SNPS_TRACE("Entering");
    uint32_t num_ddrc = (STATIC.dual_channel_en == 1) ? 2 : 1;

    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        DYN.dis_hif[ch] = 1;
        DYN.dis_dq[ch] = 1;
    }
    #ifdef  LPDDR_2MC1PHY
      num_ddrc = 2;
    #endif // LPDDR_2MC1PHY
    dwc_cinit_setup_mmap();
    // enable dis_dq, keep dis_hif set
    for (uint32_t ch = 0; ch < num_ddrc; ch++) {
        if (dwc_ddrctl_cinit_seq_set_opctrl1(0, 1, ch) == false) {
            SNPS_ERROR("Error in seq_set_opctrl1");
            return false;
        }
    }
    SNPS_TRACE("Leaving");
    return true;
}


/**
 * @brief method to poll the PHY PUB to wait until firmware is ready
 *
 * @return ddrctl_error_t
 *
 * @note SMbus programming required for DDR5 RCD, implementation of the custom
 *       function dwc_ddrctl_cinit_custom_io_smbus_write is required
 */
ddrctl_error_t dwc_ddrctl_cinit_wait_fw_done()
{
    pub_msg_id_t    pub_msg_id;
    sinit_error_t   rslt;
    uint16_t        smbus_msg;
    uint16_t        smbus_info;
    ddrctl_bool_t   training_done = DDRCTL_FALSE;

    SNPS_LOG("Wait for Firmware Train");
    do {
        rslt = sinit_phy_get_maillbox_msg(DWC_DDRCTL_CINIT_MLBX_TIMEOUT, &pub_msg_id);
        if (SINIT_SUCCESS != rslt) {
            SNPS_ERROR("Mailbox message read failed");
            return DDRCTL_ERROR;
        }

        SNPS_LOG("Firmware Msg received: %s (0x%x)", ddrctl_cinit_pub_msg_str(pub_msg_id), pub_msg_id);

        if ((IS_DDR5) && (PUB_MSG_SMBUS_REQUEST == pub_msg_id)) {

            rslt = sinit_phy_get_smbus_request(DWC_DDRCTL_CINIT_MLBX_TIMEOUT, &smbus_msg, &smbus_info);
            if (SINIT_SUCCESS != rslt) {
                SNPS_ERROR("Mailbox read SMBus request failed");
                return DDRCTL_ERROR;
            }
            /// - SMBus requests to write RCD CW
            if (dwc_ddrctl_cinit_io_smbus_write(0, smbus_msg, smbus_info) == false) {
                SNPS_ERROR("Error in io SMBus write");
                return DDRCTL_ERROR;
            }
            SNPS_LOG("SMBus Request completed");
            continue;
        }

        if (pub_msg_id == PUB_MSG_TRAINING_COMPLETE_FAILED) {
            return DDRCTL_PHY_TRAIN_FAILED;

        }

        if (pub_msg_id == PUB_MSG_TRAINING_COMPLETE_PASSED) {
            training_done = DDRCTL_TRUE;
        }
    } while (DDRCTL_FALSE == training_done);

    SNPS_LOG("Firmware Train done");

    return DDRCTL_SUCCESS;
}


ddrctl_error_t dwc_ddrctl_cinit_phyinit(SubsysHdlr_t *cfg, ddrctl_bool_t in_restore_power_seq)
{
#ifdef PHYINIT
    ddrctl_error_t  rslt;
    ddrctl_bool_t   run_restore_seq;

    physetup_log_open();

    rslt = physetup_config_init(cfg);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("PHYINIT config init failed, %d", rslt);
        return rslt;
    }

    // set active channel for TB PVE only
    dwc_ddrctl_set_pub_channel_active(0); // simulation only

    if (DDRCTL_TRUE == in_restore_power_seq) {
        switch (cfg->ddrPhyType_m) {
            case DWC_DDR54_PHY:
            case DWC_DDR54_PHY_V2:
            case DWC_LPDDR4X_MULTIPHY:
                run_restore_seq = DDRCTL_FALSE;
                break;
            case DWC_LPDDR54_PHY:
                if (IS_LPDDR5) {
                    run_restore_seq = DDRCTL_TRUE;
                } else {
                    run_restore_seq = DDRCTL_FALSE;
                }
                break;
            case DWC_LPDDR5X4_PHY:
            case DWC_DDR5_PHY:
                run_restore_seq = DDRCTL_TRUE;
                break;
            default:
                SNPS_ERROR("Unknown PHY type, %d", cfg->ddrPhyType_m);
                return DDRCTL_NOT_SUPPORTED;
        }
    } else {
        run_restore_seq = DDRCTL_FALSE;
    }


    if (DDRCTL_TRUE == run_restore_seq) {
        rslt = physetup_restore_sequence(cfg);
    } else {
        rslt = physetup_sequence(cfg);
    }

    if (DDRCTL_SUCCESS != rslt) {
        return rslt;
    }

    dwc_ddrctl_set_pub_channel_active(0); // simulation only

    SNPS_LOG("PHYINIT: sequence done");
#endif /* PHYINIT */

    return DDRCTL_SUCCESS;
}

/** @} */
