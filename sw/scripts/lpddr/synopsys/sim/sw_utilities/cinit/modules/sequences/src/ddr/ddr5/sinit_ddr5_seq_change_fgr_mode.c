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
#include "dwc_ddrctl_cinit_jedec_ddr_timing.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_phy_training.h"
#include "sw_cmd_intf/ddr5/cinit_ddr5_sw_cmd.h"
#include "mode_regs/ddr5/ddrctl_sw_ddr5_mode_regs.h"
#include "cinit_port_util.h"
#include "cinit_status.h"
#include "dwc_ddrctl_cinit_defines.h"
#include "cinit_port_util.h"

#ifdef DDRCTL_DDR
 /**
  * @defgroup DDRSwSeqGrp DDR software sequences
  * This section groups together software sequences and methods that are used in
  * DDR controllers.
  * @{
  */

#ifdef CINIT_DDR5
static ddrctl_error_t get_ref_adjs_cmds_delay(SubsysHdlr_t *config, uint32_t *max_delay)
{
    uint8_t device;
    uint8_t ref_delay;

    *max_delay = 0;

    for (device = 0; device < DWC_DDRCTL_DEV_CFG_NUM; device++) {
        switch (config->spdData_m.sdram_capacity_mbits[device]) {
            case DDRCTL_8GB:
                ref_delay = 22;
#ifdef DWC_DDRCTL_P80001562_230105_WORKAROUND
                ref_delay += 30;
#endif
                break;
            case DDRCTL_16GB:
                ref_delay = 45;
#ifdef DWC_DDRCTL_P80001562_230105_WORKAROUND
                ref_delay += 35;
#endif
                break;
            case DDRCTL_24GB:
            case DDRCTL_32GB:
            case DDRCTL_64GB:
                ref_delay = 64;
#ifdef DWC_DDRCTL_P80001562_230105_WORKAROUND
                ref_delay += 60;
#endif
                break;
            default:
                SNPS_LOG("SDRAM Capacity not supported %d", config->spdData_m.sdram_capacity_mbits);
                return DDRCTL_NOT_SUPPORTED;
        }
        *max_delay = max((*max_delay), ref_delay);
    }

    return DDRCTL_SUCCESS;
}
#endif

/**
 * @brief **Change Fine Granularity Refresh mode (only for DDR5)**
 *
 */
ddrctl_error_t dwc_ddrctl_cinit_sw_seq_ddr5_fgr_mode(SubsysHdlr_t *config, ddrctl_fgr_mode_t fgr_mode)
{
#ifdef CINIT_DDR5
    ddrctl_fgr_mode_t   curr_fgr_mode;
    ddrctl_error_t      rslt;
    uint32_t            t_rfc_min;
    uint32_t            t_rfc_min_dlr;
    uint32_t            refab_hi_sch_gap;
    uint8_t             channel;
    uint32_t            reg_value;
    uint32_t            field_value;
    uint32_t            max_delay;
    uint8_t             port;
    uint8_t             mr_value;
    uint8_t             num_channels;
    uint8_t             active_ranks_map = cinit_get_active_ranks_map();
    uint8_t             num_ranks = cinit_get_number_ranks();
    uint8_t             num_active_lranks = cinit_get_active_logical_ranks();
    uint8_t             freq;
    uint8_t             freq_ratio;
    uint8_t             rank;
    uint8_t             pstate = 0;
    uint32_t            store_rank_maint_calibr[DWC_DDRCTL_NUM_CHANNEL];
    uint8_t             store_glob_maint_calibr[DWC_DDRCTL_NUM_CHANNEL];

    num_channels = cinit_get_num_channels_enable();
    freq_ratio = ddrctl_sw_get_ratio_factor(config, 0);

    reg_value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + RFSHMOD1);
    curr_fgr_mode = (ddrctl_fgr_mode_t) SNPS_READ_FIELD(reg_value, RFSHMOD1_FGR_MODE);

    //Capture the current pState
    if(UMCTL2_FREQUENCY_NUM > 1) {
        reg_value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + MSTR2);
        pstate    = SNPS_READ_FIELD(reg_value, MSTR2_TARGET_FREQUENCY);
    }

    SNPS_LOG("Fine Granularity Refresh mode set to 0x%x, changing to 0x%x", curr_fgr_mode, fgr_mode);

    /**
     * <ol>
     * <li>
     * Before starting frequency change flow, ensure all ranks of all channels are not in any low power mode
     * (auto power-down, auto/software/hardware self-refresh, MPSM) through pwrctl.powerdown_en,
     * pwrctl.selfref_en, pwrctl.selfref_sw, HWLPCTL.hw_lp_en, STAT.operating_mode
     */
    SNPS_LOG("[1] Verify all ranks of all channels in Normal Power mode");
    if (cinit_verify_normal_op_mode(DDRCTL_CHANNEL_ALL) == DDRCTL_FALSE) {
        SNPS_ERROR("Error System is not in normal operation mode");
        return DDRCTL_ERROR;
    }

    /**
     * <li>
     * Stop sending read/write traffic and scrubbing traffic to all ranks of all channels. Wait until all pending
     * transactions are completed. Make sure all transactions from system and scrubber are finished
     */
    SNPS_LOG("[2] Stop sending read/write traffic and scrubbing traffic to all ranks of all channels");

    /**
     *   a. Disable all ports
     *      Set PCTRL.port_en to '0' to block the AXI ports from taking any transactions, then poll
     *      PSTAT.rd_port_busy_n to '0' and PSTAT.wr_port_busy_n to '0'. Wait until all AXI ports are idle
     */
    SNPS_LOG("[2.a] Disable all ports");
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_DISABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports disable failed");
        return rslt;
    }

    SNPS_LOG("[2.b] Disable scrubber");
    /**
     *    b. Disable the Scubber for all channels and wait until is idle
     *       This is only required if SBR is instantiated
     */
    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_DISABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scrubber disable failed");
        return false;
    }

    /**
     *   c. Disable HIF and empty queues
     *      Set OPCTRL1.dis_hif to '1', so that no new commands are accepted by the controller, then poll:
     *      - OPCTRLCAM.dbg_wr_q_empty to '1'
     *      - OPCTRLCAM.wr_data_pipeline_empty to '1'
     *      - OPCTRLCAM.dbg_rd_q_empty to '1'
     *      - OPCTRLCAM.rd_data_pipeline_empty to '1'
     */
    SNPS_LOG("[2.c] Disable HIF and empty queues");
    for (channel = 0; channel < num_channels; channel++) {
        if (dwc_ddrctl_cinit_seq_set_opctrl1(0, 1, channel) == false) {
            SNPS_ERROR("Disable HIF failed");
            return DDRCTL_ERROR;
        }
    }

    if (dwc_ddrctl_cinit_seq_wait_opctrlcam_empty(DWC_DDRCTL_MAX_APB_POLLING) == false) {
        SNPS_ERROR("Timeout waiting for HIF queues go empty");
        return DDRCTL_ERROR;
    }

    for (channel = 0; channel < num_channels; channel++) {
        /**
         * <li> Disable global maintenance calibration activities
         *        - disable pasctl7.glb_blk0_en ~ glb_blk7_en on all channels
         *        - poll corresponding bits in stat2.glb_blk_events_ongoing to '0'
         */
        SNPS_LOG("[3] Disable global maintenance calibration activities");
        store_glob_maint_calibr[channel] = ddrctl_sw_cinit_get_global_maint_calibr(channel);
        rslt = ddrctl_sw_cinit_global_maint_calibr(channel, 0x0, DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Global maintenance calibration disable failed");
            return false;
        }

        /**
         * <li> Disable rank maintenance calibration activities of all ranks of all channels
         *   - set pasctl8 to 0
         *   - poll corresponding bits in stat3.rank_blk_events_ongoing to '0'
         */
        SNPS_LOG("[4, 5] Disable rank maintenance calibration activities");
        store_rank_maint_calibr[channel] = ddrctl_sw_cinit_get_rank_maint_calibr(channel);
        rslt = ddrctl_sw_cinit_rank_maint_calibr(channel, 0x0, DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Ranks maintenance calibration disable failed");
            return false;
        }
    }

    /**
     * <li> Disable dequeue and pause refresh to all ranks of all channels through software command
     * interface command DisDqRef w/ DisRefType set to ‘0’
     */
    SNPS_LOG("[6] Disable dequeue and pause refresh");
    rslt = cinit_ddr5_send_disable_dq_refresh(config, DDRCTL_CHANNEL_ALL, 0xF, 0, 0, 0,
                                              SW_CMD_DISDQREF_TYPE_PAUSE, SW_CTRL_LAST_CMD);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Error in Disable De-Queue Refresh command");
        return rslt;
    }
    dwc_ddrctl_cinit_io_nsleep(10);

    /**
     * <li> Send PREAB to all logical ranks of all ranks of all channels through software command interface
     * command PRE. If CA parity retry feature is enabled, cmdctl.cmd_seq_ongoing must be set to '1' for
     * each software command interface command in the sequence until the last one
     */
    SNPS_LOG("[7] Send PREAB");
    rslt = cinit_ddr5_send_preab(config);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Send PREab command failed");
        return rslt;
    }

    /**
     * <li> Flush REFAB to all ranks of all channels through software command interface command REF_FLUSH.
     * This will send all accumulated postponed refreshes to the ranks
     */
    SNPS_LOG("[8] Flush REFAB");
    rslt = cinit_ddr5_send_ref_flush(config, DDRCTL_CHANNEL_ALL, active_ranks_map);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Error in REF flush command");
        return rslt;
    }

    /**
     * <li> Pause refresh to all ranks of all channels through software command interface command DisDqRef w/
     * DisRefType set to ‘0’
     */
    SNPS_LOG("[9] Pause refresh");
    rslt = cinit_ddr5_send_disable_dq_refresh(config, DDRCTL_CHANNEL_ALL, 0, 0, active_ranks_map, 0,
                                              SW_CMD_DISDQREF_TYPE_PAUSE, SW_CTRL_LAST_CMD);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Error in Disable De-Queue Refresh command");
        return rslt;
    }
    dwc_ddrctl_cinit_io_nsleep(10);

    /**
     * <li> Send MRW4 to all ranks of all channels through software command interface command MRW to
     * update target FGR mode (MR4:OP[4])
     */
    SNPS_LOG("[10] Send MRW4");

    for (channel = 0; channel < num_channels; channel++) {
        switch (fgr_mode) {
            case FGR_MODE_FIXED_1X:
                config->memCtrlr_m.ddr5_mr[channel].mr4.refresh_trfc_mode = 0;
                break;
            case FGR_MODE_FIXED_2X:
                config->memCtrlr_m.ddr5_mr[channel].mr4.refresh_trfc_mode = 1;
                break;
            default:
                SNPS_ERROR("Error in seq_ddr5_send_mrw");
                return rslt;
        }
        mr_value = ddrctl_sw_get_ddr5_mode_reg(config, channel, 4);
        rslt = cinit_ddr5_send_mrw(config, channel, 4, mr_value, DDRCTL_FALSE, DDRCTL_FALSE,
                                active_ranks_map, SW_CTRL_LAST_CMD);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Error in seq_ddr5_send_mrw");
            return rslt;
        }
    }

    SNPS_LOG("[11] Automatic ECS, not yet implemented");


    /**
     * <li> Send REFAB to all ranks of all channels through software command interface command REF. They can
     * act as pull-in refreshes to build up more margin
     */
    SNPS_LOG("[12] Send REFAB");
    rslt = get_ref_adjs_cmds_delay(config, &max_delay);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Calculating REFAB commands delay failed");
        return rslt;
    }

    rslt = cinit_ddr5_send_refab(config, active_ranks_map, max_delay);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Send REFAB to all ranks of all channels Error");
        return rslt;
    }

    t_rfc_min = dwc_cinit_get_ddr5_trfc(SPD.sdram_capacity_mbits[0], fgr_mode)/1000;
    SNPS_LOG("Wait tRFC(min) = %u", t_rfc_min);
    dwc_ddrctl_cinit_io_nsleep(t_rfc_min);


    /**
     * <li> Send SRE to all ranks of all channels through software command interface command SR_CTRL
     */
    SNPS_LOG("[13] Send SRE");
    rslt = cinit_ddr5_send_self_refresh_control(config, DDRCTL_CHANNEL_ALL, active_ranks_map,
                                                SW_CMD_SR_CTRL_FC_SRE_CMD, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Send SRE to all ranks of all channels Error");
        return rslt;
    }

    /**
     * <li> Set REGB_DDRC_CH0.pasctl37.dch_sync_mode to ‘1’ (Dual Channel only)
     */
    if (num_channels == 2) {
        SNPS_LOG("[14] Set REGB_DDRC_CH0.pasctl37.dch_sync_mode to 1");
        if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(1) == false) {
            SNPS_ERROR("Error in seq_ddr5_dch_sync_mode");
            return DDRCTL_ERROR;
        }
    }

    /**
     * <li> Wait until tCPDED is satisfied from corresponding SRE commands
     */
    SNPS_LOG("[15] Wait until tCPDED is satisfied from corresponding SRE commands");
    dwc_ddrctl_cinit_io_wait_ddrc_clk(QDYN.t_cpded[0][0]/freq_ratio);

    /**
     * <li> Set CSn to low of all ranks of all channels through software command interface command FORCE_CS
     */
    SNPS_LOG("[16] Set CSn to low");
    for (channel = 0; channel < num_channels; channel++) {
        // Force CS Low to all ranks
        rslt = cinit_ddr5_send_force_cs(config, (ddrctl_channel_t)channel,
                                        active_ranks_map, 0, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Error in Send Force CS reset");
            return rslt;
        }

        /**  a. For RDIMM/LRDIMM, need to also toggle dfi_dram_clk_disable. Do this by:
         *     - Send DFICLK with dfi_clk_disable_set=1 via SCI to set dfi_dram_clk_disable=1
         *     - Send DFICLK with dfi_clk_disable_clr=1 via SCI to set dfi_dram_clk_disable=0
         */
        if ((CINIT_IS_RDIMM(config) == DDRCTL_TRUE) || (CINIT_IS_LRDIMM(config) == DDRCTL_TRUE)) {
            rslt = cinit_ddr5_send_dfi_clock_ctrl(config, (ddrctl_channel_t)channel, DDRCTL_DISABLE,
                                                  active_ranks_map, SW_CTRL_LAST_CMD);
            if (DDRCTL_SUCCESS != rslt) {
                SNPS_ERROR("[Ch %u] Send DFI clock control disable to all ranks Error", channel);
                return rslt;
            }
            rslt = cinit_ddr5_send_dfi_clock_ctrl(config, (ddrctl_channel_t)channel, DDRCTL_ENABLE,
                                                  active_ranks_map, SW_CTRL_LAST_CMD);
            if (DDRCTL_SUCCESS != rslt) {
                SNPS_ERROR("[Ch %u] Send DFI clock control enable Error", channel);
                return rslt;
            }
        }
    }

    /**
     * <li> Program tRFC related registers rfshctl0.fgr_mode, rfshset1tmg1.t_rfc_min and
     * rfshset1tmg2.t_rfc_min_dlr to target values.
     * Update RFSHSET1TMG9.refab_hi_sch_gap and RFSHSET1TMG9.refsb_hi_sch_gap accordingly
     */
    SNPS_LOG("[19] Program tRFC related registers");
    for (freq = 0; freq < hdlr->num_pstates; freq++) {
        for (channel = 0; channel < num_channels; channel++) {

            // Calcule and set tRFC(min)
            t_rfc_min = dwc_ddrctl_cinit_get_ddr_trfc_min_tck(SPD.sdram_protocol, SPD.sdram_capacity_mbits[0],
                                                              fgr_mode, SPD.tck_ps[freq]);
            SNPS_LOG("[PState %u][Ch %u] Set tRFC(min) = %d (0x%x) tck", freq, channel, t_rfc_min, t_rfc_min);

            reg_value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, channel) + RFSHSET1TMG1);

            SNPS_WRITE_FIELD(reg_value, RFSHSET1TMG1_T_RFC_MIN, t_rfc_min);
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, channel) + RFSHSET1TMG1, reg_value);

            // Calcule and set Gap between REFab commands
            reg_value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, channel) + RFSHSET1TMG9);
            refab_hi_sch_gap = SNPS_READ_FIELD(reg_value, RFSHSET1TMG9_REFAB_HI_SCH_GAP);

            rslt = ddrctl_cinit_get_ddr5_refab_sch_gap_tck(t_rfc_min, refab_hi_sch_gap, &refab_hi_sch_gap);
            if (DDRCTL_SUCCESS != rslt) {
                SNPS_ERROR("[PState %u][Ch %u] Calculation of REFab gap failed", freq, channel);
                return rslt;
            }
            SNPS_LOG("[PState %u][Ch %u] Set Gap between REFab cmds = %d (0x%x) tck", freq, channel,
                     refab_hi_sch_gap, refab_hi_sch_gap);
            SNPS_WRITE_FIELD(reg_value, RFSHSET1TMG9_REFAB_HI_SCH_GAP, refab_hi_sch_gap);
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, channel) + RFSHSET1TMG9, reg_value);

#ifdef UMCTL2_CID_EN
            // Calcule and set tRFC_dlr(min)
            t_rfc_min_dlr = dwc_ddrctl_cinit_get_ddr_trfc_dlr_tck(SPD.sdram_protocol, SPD.sdram_capacity_mbits[0],
                                                              fgr_mode, SPD.tck_ps[freq]);
            SNPS_LOG("[PState %u][Ch %u] Set tRFC_dlr(min) = %d (0x%x)", freq, channel, t_rfc_min_dlr, t_rfc_min_dlr);

            reg_value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, channel) + RFSHSET1TMG2);
            SNPS_WRITE_FIELD(reg_value, RFSHSET1TMG2_T_RFC_MIN_DLR, t_rfc_min_dlr);
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, channel) + RFSHSET1TMG2, reg_value);
#endif // MEMC_LPDDR4_OR_UMCTL2_CID_EN

#ifdef DDRCTL_TWO_TIMING_SETS_EN
#if (DWC_DDRCTL_DEV_CFG_NUM > 0)
            // Calcule and set tRFC(min) Dev 1
            t_rfc_min = dwc_ddrctl_cinit_get_ddr_trfc_min_tck(SPD.sdram_protocol, SPD.sdram_capacity_mbits[1],
                                                              fgr_mode, SPD.tck_ps[freq]);
            SNPS_LOG("[PState %u][Ch %u] Set Dev 1 tRFC(min) = %d (0x%x)", freq, channel, t_rfc_min, t_rfc_min);

            reg_value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, channel) + RFSHSET2TMG1);
            SNPS_WRITE_FIELD(reg_value, RFSHSET2TMG1_T_RFC_MIN_2, t_rfc_min);
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, channel) + RFSHSET2TMG1, reg_value);

            // Calcule and set Gap between REFab commands Dev 1
            rslt = ddrctl_cinit_get_ddr5_refab_sch_gap_tck(t_rfc_min, refab_hi_sch_gap, &refab_hi_sch_gap);
            if (DDRCTL_SUCCESS != rslt) {
                SNPS_ERROR("[PState %u][Ch %u] Calculation of REFab gap failed", freq, channel);
                return rslt;
            }
            SNPS_LOG("[PState %u][Ch %u] Set Dev 1 Gap between REFab cmds = %d (0x%x)", freq, channel,
                      refab_hi_sch_gap, refab_hi_sch_gap);

            reg_value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, channel) + RFSHSET2TMG9);
            SNPS_WRITE_FIELD(reg_value, RFSHSET2TMG9_REFAB_HI_SCH_GAP_2, refab_hi_sch_gap);
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, channel) + RFSHSET2TMG9, reg_value);

#ifdef UMCTL2_CID_EN
            // Calcule and set tRFC_dlr(min) Dev 1
            t_rfc_min_dlr = dwc_ddrctl_cinit_get_ddr_trfc_dlr_tck(SPD.sdram_protocol, SPD.sdram_capacity_mbits[1],
                                                              fgr_mode, SPD.tck_ps[freq]);
            SNPS_LOG("[PState %u][Ch %u] Set Dev 1 tRFC_dlr(min) = %d (0x%x)",
                     freq, channel, t_rfc_min_dlr, t_rfc_min_dlr);

            reg_value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(freq, channel) + RFSHSET2TMG2);
            SNPS_WRITE_FIELD(reg_value, RFSHSET2TMG2_T_RFC_MIN_DLR_2, t_rfc_min_dlr);
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(freq, channel) + RFSHSET2TMG2, reg_value);
#endif // MEMC_LPDDR4_OR_UMCTL2_CID_EN
#endif /* DWC_DDRCTL_DEV_CFG_NUM > 0 */
#endif
        }
    }

    SNPS_LOG("Insert 1xTrefi2 window");
    if (0 == fgr_mode) { //Fixed 1x (Normal mode)
        dwc_ddrctl_cinit_io_nsleep(config->timingParams_m[0][0].ddr5_trefi1_ps/1000);
    } else {
        dwc_ddrctl_cinit_io_nsleep(config->timingParams_m[0][0].ddr5_trefi2_ps/1000);
    }

    if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_pre_qdyn_write");
        return DDRCTL_ERROR;
    }

    SNPS_LOG("Change FGR mode from %d to %d", curr_fgr_mode, fgr_mode);
    reg_value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + RFSHMOD1);
    SNPS_WRITE_FIELD(reg_value, RFSHMOD1_FGR_MODE, fgr_mode);
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + RFSHMOD1, reg_value);

    if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
        SNPS_ERROR("Error in seq_post_qdyn_write");
        return DDRCTL_ERROR;
    }

    /**
     * <li> Change RFSHMOD0.refresh_burst mode accordingly if necessary
     */

    /**
     * <li> Change RFSHMOD1.same_bank_refresh mode accordingly if necessary
     */


    SNPS_LOG("[20] 	For Automatic ECS mode change (Not yet implemented):" \
             "a. Program the Automatic ECS related registers ECSCTL.auto_ecs_refab_en," \
             "ECSSET1TMG0.t_refi_ecs_offset_x1_x32, and ECSSET1TMG0.t_ecs_int_x1024." \
             "b. When enabling Automatic ECS mode, if REFsb only mode is used "\
             "(RFSHMOD1.same_bank_refresh == 1), change it to REFab only mode or " \
             "mixed Refresh mode (RFSHMOD1.same_bank_refresh == 0 or 2)");

    /**
     * <li> Toggle rfshctl0.refresh_update_level to allow the new refresh-related register values to propagate
     * to refresh logic
     */
    SNPS_LOG("[21] Toggle rfshctl0.refresh_update_level");
    reg_value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + RFSHCTL0);
    field_value = SNPS_READ_FIELD(reg_value, RFSHCTL0_REFRESH_UPDATE_LEVEL);
    SNPS_WRITE_FIELD(reg_value, RFSHCTL0_REFRESH_UPDATE_LEVEL, ~field_value);
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + RFSHCTL0, reg_value);

    /**
     * <li> Wait until tCSL or tCSSR, depending on current scenario, is satisfied from corresponding SRE commands
     */
    SNPS_LOG("[22] Wait until tCSL or tCSSR");
    if ((CINIT_IS_RDIMM(config) == DDRCTL_TRUE) || (CINIT_IS_LRDIMM(config) == DDRCTL_TRUE)) {
        SNPS_LOG("\tWait until tCSSR %d nCK", QDYN.t_cssr[0][0]/freq_ratio);
        dwc_ddrctl_cinit_io_wait_ddrc_clk(QDYN.t_cssr[0][0]/freq_ratio);
    } else {
        SNPS_LOG("\tWait until tCSL %d nCK", QDYN.t_csl[0][0]/freq_ratio);
        dwc_ddrctl_cinit_io_wait_ddrc_clk(QDYN.t_csl[0][0]/freq_ratio);
    }

    if (cinit_dual_channel_enable() == DDRCTL_TRUE) {
        /**
         * <li> Set CSn to high of all ranks of all channels through software command interface command FORCE_CS (Dual Channel-RDIMM only)
         */
        if ((CINIT_IS_RDIMM(config) == DDRCTL_TRUE) || (CINIT_IS_LRDIMM(config) == DDRCTL_TRUE)) {
            SNPS_LOG("[24] Set CSn to high");
            for (channel = 0; channel < num_channels; channel++) {
                    //Force CSn to high to all ranks
                rslt = cinit_ddr5_send_force_cs(config, channel, 0, active_ranks_map, SW_CTRL_LAST_CMD);
                if (DDRCTL_SUCCESS != rslt) {
                    SNPS_LOG("[Ch %u] Send Force Chip Select reset to all ranks of all channels Error", channel);
                    return rslt;
                }
            }
        }

        /**
         * <li> Set REGB_DDRC_CH0.pasctl37.dch_sync_mode to ‘0’ (Dual Channel only)
         */
        SNPS_LOG("[25] Set REGB_DDRC_CH0.pasctl37.dch_sync_mode to 0");
        if (dwc_ddrctl_cinit_seq_ddr5_dch_sync_mode(0) == false) {
            SNPS_LOG("Error in seq_ddr5_dch_sync_mode");
            return DDRCTL_ERROR;
        }

        /**
         * <li> Wait until tSTAB01 is satisfied from CSn set to high (Dual Channel-RDIMM only)
         */
        SNPS_LOG("[26] Wait until tSTAB01 %d nCK", (QDYN.t_stab_x32[0][0] * 32) / freq_ratio);

        dwc_ddrctl_cinit_io_wait_ddrc_clk((QDYN.t_stab_x32[0][0] * 32) / freq_ratio);
    }

    /**
     * <li>  Pause refresh to all ranks through software command interface command DisDqRef
     */
    SNPS_LOG("[27] Resume automatic refresh to all ranks");
    for (channel = 0; channel < num_channels; channel++) {
        rslt = cinit_ddr5_send_disable_dq_refresh(config, (ddrctl_channel_t)channel, 0, 0, active_ranks_map, 0,
                                                  SW_CMD_DISDQREF_TYPE_BLOCK, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_LOG("Error in Send Disable Dequeue Refresh command");
            return rslt;
        }
        dwc_ddrctl_cinit_io_nsleep(10);
    }


    /**
     * <li> Send SRX to all ranks of all channels through software command interface command SR_CTRL
     */
    SNPS_LOG("[28] Send SRX");
    rslt = cinit_ddr5_send_self_refresh_control(config, DDRCTL_CHANNEL_ALL, active_ranks_map,
                                                SW_CMD_SR_CTRL_FC_SREF_SRX_CMD, SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_LOG("Send SRE to all ranks of all channels Error");
        return rslt;
    }

    /**
     * <li> Wait until tXS is satisfied from corresponding SRX commands
     */
    SNPS_LOG("[29] Wait until tXS, tXSDLL");
    dwc_ddrctl_cinit_io_wait_ddrc_clk((QDYN.t_xs_x32[0][0] * 32) / freq_ratio); //tXS
    dwc_ddrctl_cinit_io_wait_ddrc_clk(2048 / freq_ratio); //tXSDLL max

    /**
     * <li> Send SRX_Done_tXS to all ranks of all channels through software command interface command
     * OP_CTRL
     */
    SNPS_LOG("[30] Send SRX_Done_tXS");
    rslt = cinit_ddr5_send_op_ctrl(config, DDRCTL_CHANNEL_ALL, 0, active_ranks_map, 0, 0, 0, 0,
                                   SW_CTRL_LAST_CMD);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_LOG("Error in Send Operation Control command");
        return rslt;
    }

    /**
     * <li> Send a make-up refresh-all-bank to all ranks of all channels through software command interface command REF
     */
    SNPS_LOG("[31] Send REFab command: make-up refresh-all-bank to all ranks of all channels");
    rslt = cinit_ddr5_send_refab(config, active_ranks_map, 0);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_LOG("Error sending REF ab command");
        return rslt;
    }

    /**
     * <li> Resume refresh to all ranks of all channels through software command
     * interface command by setting DisDqRefw/DisRefType to ‘0’
     */
    SNPS_LOG("[32] Resume refresh to all ranks of all channels");
    rslt = cinit_ddr5_send_disable_dq_refresh(config, DDRCTL_CHANNEL_ALL, 0, 0, active_ranks_map, 0,
                                                SW_CMD_DISDQREF_TYPE_PAUSE, SW_CTRL_LAST_CMD);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_LOG("Error in Send Disable Dequeue Refresh command");
        return rslt;
    }

    /**
     * <li> Perform controller update to all channels through software command interface command DFIUPD
     */
    SNPS_LOG("[33] Perform controller update");
    rslt = cinit_ddr5_send_dfi_ctrlupd(config, DDRCTL_CHANNEL_ALL, DDRCTL_ENABLE, DDRCTL_DISABLE, 0, SW_CTRL_LAST_CMD);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_LOG("Error in Send Disable Dequeue Refresh command");
        return rslt;
    }

    /**
     * <li> Make sure tXSDLL is satisfied from corresponding SRX commands
     */
    SNPS_LOG("[34] Make sure tXSDLL is satisfied from corresponding SRX commands");
    dwc_ddrctl_cinit_io_wait_ddrc_clk((QDYN.t_xs_dll_x32[0][0] * 32) / freq_ratio);

    /**
     * <li> Send SRX_Done_tXSDLL to all ranks of all channels through software command interface command OP_CTRL
     */
    SNPS_LOG("[35] Send SRX_Done_tXSDLL");
    for (channel = 0; channel < num_channels; channel++) {
        rslt = cinit_ddr5_send_op_ctrl(config, (ddrctl_channel_t)channel, active_ranks_map, 0, 0, 0, 0, 0,
                                       SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_LOG("Error in Send Operation Control command");
            return rslt;
        }
    }

    /**
     * <li> Send Software Command MRR to read MRR4 to all ranks of all channels to check refresh
     *      rate according to temperature for each device
     *
     *   Only supported from version 1.41_lca02
     */
    SNPS_LOG("[36] Send Software Command MRR to read MRR4");
    for (rank = 3; rank <= 3; rank--) {
        if (SNPS_GET_BIT(active_ranks_map, rank) != 1) {
            continue; // Bit not set
        }
        rslt = cinit_ddr5_send_mrr(config, DDRCTL_CHANNEL_ALL, rank, 0x4, DDRCTL_FALSE,
                                   DDRCTL_DISABLE, DDRCTL_ENABLE, DDRCTL_ENABLE, SW_CTRL_LAST_CMD);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Error sending MRR to address 0x4");
            return false;
        }
    }

    /**
     * <li> Enable dequeue to all ranks through software command interface command DisDqRef
     */
    SNPS_LOG("[37] Enable dequeue");
    for (channel = 0; channel < num_channels; channel++) {
        rslt = cinit_ddr5_send_disable_dq_refresh(config, (ddrctl_channel_t)channel, 0, active_ranks_map, 0, 0,
                                                  SW_CMD_DISDQREF_TYPE_PAUSE, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_LOG("Error in Send Disable Dequeue Refresh command");
            return rslt;
        }
    }

    /**
     * <li> Enable global/rank maintenance calibration activities if necessary
     */
    SNPS_LOG("[38] Enable global/rank maintenance calibration activities");
    for (channel = 0; channel < num_channels; channel++) {
        rslt = ddrctl_sw_cinit_global_maint_calibr(channel, store_glob_maint_calibr[channel],
                                                   DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Enable global maintenance calibration activities failed");
            return false;
        }
    }


    for (channel = 0; channel < num_channels; channel++) {
        rslt = ddrctl_sw_cinit_rank_maint_calibr(channel, store_rank_maint_calibr[channel],
                                                 DWC_DDRCTL_MAX_APB_POLLING);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("Enable rank maintenance calibration activities failed");
            return false;
        }
    }

    /**
     * <li> Enable HIF commands by setting OPCTRL1.dis_hif to '0'
     */
    SNPS_LOG("[39] Enable HIF commands");
    for (channel = 0; channel < num_channels; channel++) {
        if (dwc_ddrctl_cinit_seq_set_opctrl1(0, 0, channel) == false) {
            SNPS_LOG("Error in seq_set_opctrl1");
            return DDRCTL_ERROR;
        }
    }

    /**
     * <li> Set PCTRL.port_en to '1' and SBRCTL.scrub_en to '1' to enable new traffics from AXI ports and scrubber
     */
    SNPS_LOG("[40] Enable ports and ECC scrubber");
    rslt = ddrctl_cinit_ctrl_ports(DDRCTL_ENABLE, DWC_DDRCTL_MAX_APB_POLLING);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Ports enable failed");
        return rslt;
    }

    rslt = ddrctl_cinit_scrubber_enable(DDRCTL_CHANNEL_ALL, DDRCTL_ENABLE);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("Scubber enable failed");
        return rslt;
    }

#endif /* CINIT_DDR5 */

    return DDRCTL_SUCCESS;
}

/// @} // end DDRSwSeqGrp
#endif  // DDRCTL_DDR

