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

#include "sw_cmd_intf/ddr5/cinit_ddr5_sw_cmd.h"
#include "sw_cmd_intf/ddr5/cinit_ddr5_sw_cmd_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_util.h"
#include "cinit_status.h"
#include "dwc_cinit_log.h"

#define TIME_BETWEEN_SW_STATUS_CHECKS   0

#define SW_CMD_LOG_ID   " "

#define MAX_POLLING_WAIT_SW_CMD (2 * DWC_DDRCTL_MAX_APB_POLLING)


static ddrctl_error_t _ddr5_wait_sw_cmd_done(uint8_t channel, ddrctl_bool_t channel_sync,
                                             ddrctl_ddr5_sw_cmd_intf_t cmd_code,
                                             uint32_t max_apb_reads);

/**
 * @brief Sends a command by the software command interface
 *
 * @param cfg           CINIT configuration
 * @param cmd_code      Software Command Interface code
 * @param cmd_ctrl      Software Command Interface code control
 * @param sw_cmd_ch     Channels to send the command
 * @param ranks         Ranks
 * @param multi_cyc_cs  Enable/disable multi-cycle cs assertion for MPC DDR command.
 *                      If enabled, controller will send multiple MPC command to DRAM, if disabled,
 *                      command interface send only one MPC DDR command
 * @param last_cmd      Last command in the command sequence. Software can send a sequence of commands
 *                      to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
static ddrctl_error_t _ddr5_send_sw_cmd(SubsysHdlr_t *cfg, ddrctl_ddr5_sw_cmd_intf_t cmd_code,
                               uint32_t cmd_ctrl, ddrctl_channel_t sw_cmd_ch, uint8_t ranks,
                               ddrctl_status_t multi_cyc_cs, ddrctl_sw_cmd_last_t last_cmd)
{
    ddrctl_error_t  rslt;
    ddrctl_bool_t   channel_sync;
    uint32_t        cmdcfg;
    uint32_t        cmdctl;
    uint8_t         channel_last;
    uint8_t         channel;

    rslt = DDRCTL_ERROR; // makes sure if no command is sent it will report error
    channel_sync = DDRCTL_FALSE;

    if (DDRCTL_CHANNEL_ALL == sw_cmd_ch) {
        if ((cinit_dual_channel_enable() == DDRCTL_TRUE) &&
            (cinit_is_dual_channel_sync_enable() == DDRCTL_FALSE)) {
            channel = 0;
            channel_last = 1;
        } else {
            channel = 0;
            channel_last = 0;
            channel_sync = DDRCTL_TRUE;
        }
    } else {
        channel = sw_cmd_ch;
        channel_last = sw_cmd_ch;
    }

    for (; channel <= channel_last; channel++) {

        SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %u] Send %s cmd: 0x%05x", channel,
                   ddrctl_cinit_get_ddr5_sw_cmd_str(cmd_code), cmd_ctrl);

        // CMDCFG as some fields that are not dynamic, we read to maintain that registes value
        //      PDE_ODT_CTRL, PD_MRR_NT_ODT, CMD_TIMER_X32, CTRLUPD_RETRY_THR
        cmdcfg = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(channel) + CMDCFG);

        SNPS_WRITE_FIELD(cmdcfg, CMDCFG_MRR_GRP_SEL, ranks);

        // Only applicable to MPC
        SNPS_WRITE_FIELD(cmdcfg, CMDCFG_MULTI_CYC_CS_EN, (DDRCTL_ENABLE == multi_cyc_cs) ? 1 : 0);

        SNPS_WRITE_FIELD(cmdcfg, CMDCFG_CMD_TYPE, 0);

        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(channel) + CMDCFG, cmdcfg);

        cmdctl = 0;
        SNPS_WRITE_FIELD(cmdctl, CMDCTL_CMD_SEQ_LAST, last_cmd);
        SNPS_WRITE_FIELD(cmdctl, CMDCTL_CMD_CTRL, cmd_ctrl);
        SNPS_WRITE_FIELD(cmdctl, CMDCTL_CMD_CODE, cmd_code);

        // depends on the CA parity retry
#ifdef DDRCTL_CAPAR_RETRY
        if(1 == cfg->memCtrlr_m.static_cfg.capar_retry_enable[0]) {
            SNPS_WRITE_FIELD(cmdctl, CMDCTL_CMD_SEQ_ONGOING, last_cmd);
        }
#endif /* DDRCTL_CAPAR_RETRY */

        if(UMCTL2_P_ASYNC_EN){
            SNPS_WRITE_FIELD(cmdctl, CMDCTL_CMD_START, 0);
            dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(channel) + CMDCTL, cmdctl);
        }

        SNPS_WRITE_FIELD(cmdctl, CMDCTL_CMD_START, 1);
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(channel) + CMDCTL, cmdctl);

        // poll status
        rslt = _ddr5_wait_sw_cmd_done(channel, channel_sync, cmd_code, MAX_POLLING_WAIT_SW_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("[Ch %u] Send %s cmd failed: %d", channel,
                        ddrctl_cinit_get_ddr5_sw_cmd_str(cmd_code), rslt);
            return rslt;
        }
    }
    return rslt;
}


/**
 * @brief Wait for the software command to complete
 *
 * @param channel       Channel to check for command done
 * @param channel_sync  Channel synchronization enable/disable
 * @param cmd_code      Software Command Interface code
 * @param max_apb_reads Number of reads before timeout
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
static ddrctl_error_t _ddr5_wait_sw_cmd_done(uint8_t channel, ddrctl_bool_t channel_sync,
                                             ddrctl_ddr5_sw_cmd_intf_t cmd_code,
                                             uint32_t max_apb_reads)
{
    ddrctl_error_t   rslt;

    rslt = cinit_poll_bitfield(REGB_DDRC_CH_OFFSET(channel) + CMDCTL,
                               CMDCTL_CMD_START_BIT_OFFSET, CMDCTL_CMD_START_MASK, 0,
                               max_apb_reads, TIME_BETWEEN_SW_STATUS_CHECKS);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Polling CMDCTL register for CMD_START failed");
        return rslt;
    }

    rslt = cinit_poll_bitfield(REGB_DDRC_CH_OFFSET(channel) + CMDSTAT,
                               CMDSTAT_CMD_DONE_BIT_OFFSET, CMDSTAT_CMD_DONE_MASK, 1,
                               max_apb_reads, TIME_BETWEEN_SW_STATUS_CHECKS);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Polling CMDCTL register for CMD_DONE failed");
        return rslt;
    }

    if (cmd_code == SW_CTRL_INTF_DFIUPD) {
        rslt = cinit_poll_bitfield(REGB_DDRC_CH_OFFSET(channel) + CMDSTAT,
                                   CMDSTAT_CMD_RSLT_DFIUPD_DONE_BIT_OFFSET,
                                   CMDSTAT_CMD_RSLT_DFIUPD_DONE_MASK, 1,
                                   MAX_POLLING_WAIT_SW_CMD, TIME_BETWEEN_SW_STATUS_CHECKS);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Polling CMDCTL register for DFIUPD_DONE failed");
            return rslt;
        }

        // If channel sync is enable we need to check also the "other channel done result"
        if ((channel_sync == DDRCTL_TRUE)) {
            rslt = cinit_poll_bitfield(REGB_DDRC_CH_OFFSET(channel) + CMDSTAT,
                                       CMDSTAT_CMD_RSLT_DFIUPD_CH_S_DONE_BIT_OFFSET,
                                       CMDSTAT_CMD_RSLT_DFIUPD_CH_S_DONE_MASK, 1,
                                       MAX_POLLING_WAIT_SW_CMD, TIME_BETWEEN_SW_STATUS_CHECKS);
            if (DDRCTL_SUCCESS != rslt) {
                SNPS_ERROR("Polling CMDCTL register for DFIUPD_DONE in other channel failed");
                return rslt;
            }
        }
    }

    if (cmd_code == SW_CTRL_INTF_DFIFC) {
        rslt = cinit_poll_bitfield(REGB_DDRC_CH_OFFSET(channel) + CMDSTAT,
                                   CMDSTAT_CMD_RSLT_DFIFC_DONE_BIT_OFFSET,
                                   CMDSTAT_CMD_RSLT_DFIFC_DONE_MASK, 1,
                                   MAX_POLLING_WAIT_SW_CMD, TIME_BETWEEN_SW_STATUS_CHECKS);

        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Polling CMDCTL register for DFIFC_DONE failed");
            return rslt;
        }

        // If channel sync is enable we need to check also the "other channel done result"
        if ((channel_sync == DDRCTL_TRUE)) {
            rslt = cinit_poll_bitfield(REGB_DDRC_CH_OFFSET(channel) + CMDSTAT,
                                       CMDSTAT_CMD_RSLT_DFIFC_CH_S_DONE_BIT_OFFSET,
                                       CMDSTAT_CMD_RSLT_DFIFC_CH_S_DONE_MASK, 1,
                                       MAX_POLLING_WAIT_SW_CMD, TIME_BETWEEN_SW_STATUS_CHECKS);

            if (DDRCTL_SUCCESS != rslt) {
                SNPS_ERROR("Polling CMDCTL register for DFIFC_DONE in other channel failed");
                return rslt;
            }
        }
    }

    return DDRCTL_SUCCESS;
}


/**
 * @brief Method to send a DDR5 Mode Register Write command (MRW) via software command interface
 *
 * @param cfg               CINIT configuration
 * @param channel           Channels to send the command
 * @param address           Mode register address
 * @param data              Data to write
 * @param ctrl_word         Command control
 * @param dual_die_pkg      Dual die pkg / monolithic
 * @param active_ranks_map  Active Ranks map
 * @param last_cmd          Last command in the command sequence. Software can send a sequence of commands
 *                          to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_mrw(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                   uint8_t address, uint8_t data, ddrctl_bool_t ctrl_word,
                                   ddrctl_bool_t dual_die_pkg, uint8_t active_ranks_map,
                                   ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "Send Mode Reg Write: MR%0d=0x%x (Control Word=%s, Dual die pkg=%s)",
               address, data, ddrctl_bool_to_str(ctrl_word), ddrctl_bool_to_str(dual_die_pkg));

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRW_MR_ADDR, address);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRW_OP, data);

    if (DDRCTL_TRUE == ctrl_word) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRW_CW, 1);
    }

    if (DDRCTL_TRUE == dual_die_pkg) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRW_DDPID, 1);
    }

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRW_CS_N, ~active_ranks_map);

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_MRW, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send a DDR5 Mode Register Read command (MRR) via software command interface
 *
 * @param cfg           CINIT configuration
 * @param channel       Channels to send the command
 * @param rank_num      Rank to send the command
 * @param address       Mode register address
 * @param dual_die_pkg  Dual die pkg / monolithic
 * @param phy_snoop     DDR PHY to snoop MRR results
 * @param pause_ref     Pause target rank refresh
 * @param tcr_update    Update hardware TCR
 * @param last_cmd      Last command in the command sequence. Software can send a sequence of commands
 *                      to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_mrr(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                   uint8_t rank_num, uint8_t address, ddrctl_bool_t dual_die_pkg,
                                   ddrctl_status_t phy_snoop, ddrctl_status_t pause_ref,
                                   ddrctl_status_t tcr_update, ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %d, Rank %d] Read: MR%0d (Dual die pkg=%s, PHY snoop=%s, Pause Ref=%s)",
               channel, rank_num, address, ddrctl_bool_to_str(dual_die_pkg), ddrctl_status_to_str(phy_snoop),
               ddrctl_status_to_str(pause_ref));

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRR_MR_ADDR, address);

    if (DDRCTL_ENABLE == tcr_update) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRR_TCR, 1);
    }

    if (DDRCTL_TRUE == dual_die_pkg) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRR_DDPID, 1);
    }

    if (DDRCTL_ENABLE == phy_snoop) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRR_PHY_SNOOP_EN, 1);
    }

    if (DDRCTL_ENABLE == pause_ref) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRR_PAUSE_REF_EN, 1);
    }

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MRR_RANK_NUM, rank_num);

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_MRR, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send DDR Self Refresh Control command (SR_CTRL) to control Self-Refresh entry
 *       and exit per rank
 *
 * @param cfg               CINIT configuration
 * @param channel           Channels to send the command
 * @param active_ranks_map  Active Ranks map
 * @param cmd_type          Self Refresh Control command type SRX/SRE
 * @param last_cmd          Last command in the command sequence. Software can send a sequence of commands
 *                          to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_self_refresh_control(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                                    uint8_t active_ranks_map,
                                                    cinit_sw_cmd_sr_ctrl_type_t cmd_type,
                                                    ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send Self Refresh Control: %s Ranks 0x%x",
               ddrctl_sw_channel_str(channel), ddrctl_sw_cmd_sr_ctrl_type_str(cmd_type),
               active_ranks_map);

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_SR_CTRL_FC, cmd_type);

    if (cmd_type == SW_CMD_SR_CTRL_FC_SREF_SRX_CMD) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_SR_CTRL_SRX, active_ranks_map);
    } else {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_SR_CTRL_SRE, active_ranks_map);
    }

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_SR_CTRL, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send DDR Reset Control command (RST_CTRL)
 *
 * @param cfg       CINIT configuration
 * @param channel   Channels to send the command
 * @param status    Reset Control enter/exit
 * @param last_cmd  Last command in the command sequence. Software can send a sequence of commands
 *                  to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_reset_control(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                             ddrctl_status_t status, ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send Reset Control: %s", ddrctl_sw_channel_str(channel),
               ddrctl_status_to_str(status));

    if (DDRCTL_ENABLE == status) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_RST_CTRL_RSTE, 1);
    } else {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_RST_CTRL_RSTX, 1);
    }

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_RST_CTRL, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send DDR MPC command (MPC) sent to the ranks selected by CSn
 *
 * @param cfg               CINIT configuration
 * @param channel           Channels to send the command
 * @param dual_die_pkg      Dual die pkg / monolithic
 * @param op                Op code
 * @param pause_ref         Pause Refresh Enable/Disable
 * @param active_ranks_map  Active Ranks map
 * @param multi_cyc_cs      Multi-cycle Enable/Disable
 * @param last_cmd          Last command in the command sequence. Software can send a sequence of commands
 *                          to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_mpc(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                   ddrctl_bool_t dual_die_pkg, uint8_t op, ddrctl_status_t pause_ref,
                                   uint8_t active_ranks_map, ddrctl_status_t multi_cyc_cs,
                                   ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send MPC: OP=0x%02x (Ranks 0x%x, Pause Refresh=%s, Dual die pkg=%s)",
               ddrctl_sw_channel_str(channel), op, active_ranks_map,
               ddrctl_status_to_str(pause_ref), ddrctl_bool_to_str(dual_die_pkg));

    if (DDRCTL_TRUE == dual_die_pkg) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MPC_DDPID, 1);
    }

    if (DDRCTL_ENABLE == pause_ref) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MPC_PAUSE_REF_EN, 1);
    }

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MPC_OP, op);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_MPC_CS_N, (~active_ranks_map));

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_MPC, cmd_ctrl, channel, 0, multi_cyc_cs, last_cmd);
}


/**
 * @brief Method to send DDR Precharge All Bank command (PRE)
 *      It will send the command for all channels and ranks
 *
 * @param cfg   CINIT configuration
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_preab(SubsysHdlr_t *cfg)
{
    ddrctl_sw_cmd_last_t    last_cmd = SW_CTRL_NOT_LAST_CMD;
    ddrctl_error_t          rslt;
    uint32_t                cmd_ctrl = 0;
    uint8_t                 active_logic_ranks;
    uint8_t                 logic_rank;
    uint8_t                 active_ranks_map;
    uint8_t                 num_ranks;
    uint8_t                 rank;
    uint8_t                 number_of_channels;
    uint8_t                 channel;
    uint8_t                 count;

    number_of_channels = cinit_get_num_channels_enable();
    num_ranks          = cinit_get_number_ranks();
    active_ranks_map   = cinit_get_active_ranks_map();
    active_logic_ranks = cinit_get_active_logical_ranks();
    count = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "Send Refresh All Banks cmd: lranks=0x%x, Ranks 0x%x",
               active_logic_ranks, active_ranks_map);

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_PRE_TYPE, SW_CMD_PRE_TYPE_PREAB);

    for (channel = 0; channel < number_of_channels; channel++) {
        for (rank = 0; rank < 4; rank++) {
            if (SNPS_GET_BIT(active_ranks_map, rank) != 1) {
                continue; // Bit not set
            }
            count++;
            SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_PRE_CS_N, (~(1 << rank)));

            for(logic_rank = 0; logic_rank < active_logic_ranks; logic_rank++) {
                //Check for last Software command
                if((count == num_ranks) && (logic_rank == (active_logic_ranks - 1))) {
                    last_cmd = SW_CTRL_LAST_CMD;
                }

                SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_PRE_CID, logic_rank);

                rslt = _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_PRE, cmd_ctrl, channel,
                                         0, DDRCTL_DISABLE, last_cmd);
                if (rslt != DDRCTL_SUCCESS) {
                    SNPS_ERROR("Send PREab command failed");
                    return rslt;
                }
            }
        }
    }
    return DDRCTL_SUCCESS;
}


/**
 * @brief Method to send Refresh All Bank command (REF)
 *
 * @param cfg           CINIT configuration
 * @param ranks_map     Active Ranks map
 * @param cmd_int_ns    Inteval between command in nanoseconds
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_refab(SubsysHdlr_t *cfg, uint8_t ranks_map, uint32_t cmd_int_ns)
{
    ddrctl_error_t  rslt;
    uint32_t        cmd_ctrl = 0;
    uint8_t         active_l_ranks;
    uint8_t         l_rank;

    active_l_ranks = cinit_get_active_logical_ranks();

    SNPS_DEBUG(SW_CMD_LOG_ID "Send Refresh All Banks cmd: lranks=0x%x, Ranks 0x%x (Int time %u)",
               active_l_ranks, ranks_map, cmd_int_ns);

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_REF_CS_N, ~ranks_map); // active low
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_REF_TYPE, SW_CMD_REF_TYPE_REFAB);

    for (l_rank = 0; l_rank < active_l_ranks; l_rank++) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_REF_CID, l_rank);

        if (0 != cmd_int_ns) {
            dwc_ddrctl_cinit_io_nsleep(cmd_int_ns);
        }

        rslt = _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_REF, cmd_ctrl, DDRCTL_CHANNEL_ALL,
                                 0, DDRCTL_DISABLE, SW_CTRL_LAST_CMD);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_ERROR("[Ch ALL] Refresh All Banks cmd failed for logical rank %u", l_rank);
            return rslt;
        }
    }

    return DDRCTL_SUCCESS;
}


/**
 * @brief Method to send continuous NOP to particular Ranks (NOP)
 *
 * @param cfg               CINIT configuration
 * @param channel           Channels to send the command
 * @param count             Numberof NOPs to send (1 - 4096)
 * @param active_ranks_map  Active Ranks map
 * @param last_cmd          Last command in the command sequence. Software can send a sequence of commands
 *                          to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_nop(SubsysHdlr_t *cfg, ddrctl_channel_t channel, uint16_t count,
                                   uint8_t active_ranks_map, ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    if ((0 == count) || ((count - 1) >= (SW_CMD_NOP_COUNT_MASK >> SW_CMD_NOP_COUNT_BIT_OFFSET))) {
        SNPS_ERROR(SW_CMD_LOG_ID "Invalied number of NOPs to sent %d", count);
        return DDRCTL_PARAM_ERROR;
    }

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send NOPs cmd: count=%d, Ranks 0x%x",
               ddrctl_sw_channel_str(channel), count, active_ranks_map);

    // Configuring 0 will send one NOP
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_NOP_COUNT, count - 1);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_NOP_CS_N, ~active_ranks_map);

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_NOP, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send Disable De-Queue Refresh command (DisDqRef)
 *
 * @param cfg               CINIT configuration
 * @param channel           Channels to send the command
 * @param dq_set            Rank to Disable De-Queue Set
 * @param dq_reset          Rank to Disable De-Queue Reset
 * @param refresh_set       Rank to Disable Refresh Set
 * @param refresh_reset     Rank to Disable Refresh reset
 * @param refresh_type      Rank to Disable Refresh Type
 * @param last_cmd          Last command in the command sequence. Software can send a sequence of commands
 *                          to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_disable_dq_refresh(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                                  uint8_t dq_set, uint8_t dq_reset, uint8_t refresh_set,
                                                  uint8_t refresh_reset,
                                                  cinit_sw_cmd_disdqref_type_t refresh_type,
                                                  ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send Disable De-Queue Refresh cmd",
               ddrctl_sw_channel_str(channel));
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tDisable De-Queue Set 0x%x", dq_set);
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tDisable De-Queue Reset 0x%x", dq_reset);
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tDisable Refresh Set 0x%x", refresh_set);
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tDisable Refresh reset 0x%x", refresh_reset);
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tDisable Refresh Type %s",
               ddrctl_sw_cmd_disdqref_type_str(refresh_type));

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DISDQREF_DIS_DQ_SET, dq_set);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DISDQREF_DIS_DQ_RESET, dq_reset);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DISDQREF_DIS_REF_SET, refresh_set);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DISDQREF_DIS_REF_RESET, refresh_reset);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DISDQREF_DIS_REF_TYPE, refresh_type);

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_DISDQREF, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send Force and release corresponding CSn command (FORCE_CS)
 *
 * @param cfg           CINIT configuration
 * @param channel       Channels to send the command
 * @param cs_force      CS to force, when bit[i] is ‘1’, CSn[i] will be reset to ‘0’
 * @param cs_release    CS to release, when bit[i] is ‘1’, CSn[i] will be set to ‘1’
 * @param last_cmd      Last command in the command sequence. Software can send a sequence of commands
 *                      to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_force_cs(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                        uint8_t cs_force, uint8_t cs_release, ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send Force Chip Select cmd: Force 0x%04x Release 0x%04x",
               ddrctl_sw_channel_str(channel), cs_force, cs_release);

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_FORCE_CS_CSE, cs_force);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_FORCE_CS_CSX, cs_release);

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_FORCECS, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send Operation control command (OP_CTRL)
 *
 * @param cfg                   CINIT configuration
 * @param channel               Channels to send the command
 * @param srx_done_txsdll       Write 1 to the enabled control bits to generate one-cycle pulse signal to
 *                              tell controller the tXSDLL timers expire for corresponding PRANKs.
 * @param srx_done_txs          Write 1 to the enabled control bit to generate one-cycle pulse signal to
 *                              tell controller the tXS timers expire for corresponding PRANKs
 * @param pdx_done              Write 1 to enabled control bit to generate one-cycle pulse signal to tell
 *                              controller the PDX control sequence is done
 * @param mpsmx_done            Write 1 to enabled control bit to generate one-cycle pulse signal to tell
 *                              controller the MPSMX control sequence is done
 * @param non_target_odt_en     Non-target ODT control enable. When this bit is set to ’1’, enable the
 *                              non-target ODT for the corresponding rank
 * @param non_target_odt_dis    Non-target ODT control disable. When this bit is set to ’1’, disable the
 *                              non-target ODT for the corresponding rank
 * @param last_cmd              Last command in the command sequence. Software can send a sequence of commands
 *                              to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_op_ctrl(SubsysHdlr_t *cfg, ddrctl_channel_t channel, uint8_t srx_done_txsdll,
                                       uint8_t srx_done_txs, uint8_t pdx_done, uint8_t mpsmx_done,
                                       uint8_t non_target_odt_en, uint8_t non_target_odt_dis,
                                       ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send Operation Control cmd:", ddrctl_sw_channel_str(channel));
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tSRX_DONE_TXSDLL 0x%x", srx_done_txsdll);
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tSRX_DONE_TXS    0x%x", srx_done_txs);
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tPDX_DONE        0x%x", pdx_done);
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tSRX_MPSMX_DONE  0x%x", mpsmx_done);
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tNON_TARGET_EN   0x%x", non_target_odt_en);
    SNPS_DEBUG(SW_CMD_LOG_ID "\t\tNON_TARGET_DIS  0x%x", non_target_odt_dis);

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_OP_CTRL_SRX_DONE_TXSDLL, srx_done_txsdll);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_OP_CTRL_SRX_DONE_TXS, srx_done_txs);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_OP_CTRL_PDX_DONE, pdx_done);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_OP_CTRL_MPSMX_DONE, mpsmx_done);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_EN, non_target_odt_en);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_DIS, non_target_odt_dis);

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_OPCTRL, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send DFI Controller Update command (DFIUPD)
 *
 * @param cfg           CINIT configuration
 * @param channel       Channels to send the command
 * @param upd_request   Update request Enable/Disable
 * @param upd_retry     Update retry Enable/Disable
 * @param last_cmd      Last command in the command sequence. Software can send a sequence of commands
 *                      to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_dfi_ctrlupd(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                       ddrctl_status_t upd_request, ddrctl_status_t upd_retry,
                                       uint8_t num_retries, ddrctl_sw_cmd_last_t last_cmd)
{
    ddrctl_error_t  rslt;
    uint32_t        cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send DFI Controller update cmd: request %s, retry %s (count %d)",
               ddrctl_sw_channel_str(channel), ddrctl_status_to_str(upd_request),
               ddrctl_status_to_str(upd_retry), num_retries);

    if (DDRCTL_ENABLE == upd_request) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFIUPD_CTRL_UPD_REQ_SET, upd_request);
    }

    if (DDRCTL_ENABLE == upd_retry) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFIUPD_CTRL_UPD_RETRY_EN, upd_retry);
    }

    rslt = _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_DFIUPD, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);

    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("[Ch %u] Send DFI Controller Update cmd failed", channel);
    }

    return rslt;
}


/**
 * @brief Method to send DFI Frequency Change command (DFIFC)
 *
 * @param cfg           CINIT configuration
 * @param channel       Channels to send the command
 * @param init_start    When this bit is ‘1’, set dfi_init_start of DFI Frequency Change interface
 * @param init_clear    When this bit is ‘1’, clear dfi_init_start of DFI Frequency Change interface
 * @param freq_ratio    Frequence ratio of DFI Frequency Change Interface
 * @param freq          Frequency of DFI Frequency Change Interface
 * @param freq_fsp      Frequency FSP of DFI Frequency Change Interface. Support up to 64 FSPs
 * @param last_cmd      Last command in the command sequence. Software can send a sequence of commands
 *                      to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_dfi_freq_chg_ctrl(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                                 uint8_t init_start, uint8_t init_clear, uint8_t freq_ratio,
                                                 uint8_t freq, uint8_t freq_fsp, ddrctl_sw_cmd_last_t last_cmd)
{
    ddrctl_error_t  rslt;
    uint32_t        cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send DFI Frequency Change cmd: set %d, clear %d, ratio %d, freq %d, freq_fsp %d",
               ddrctl_sw_channel_str(channel), init_start, init_clear, freq_ratio, freq, freq_fsp);

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFIFC_DFI_INIT_START_SET, init_start);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFIFC_DFI_INIT_START_CLEAR, init_clear);

    if (2 == freq_ratio) {
        freq_ratio = 1;
    } else
    if (4 == freq_ratio) {
        freq_ratio = 2;
    } else {
        freq_ratio = 0;
    }

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFIFC_DFI_FREQ_RATIO, freq_ratio);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFIFC_DFI_FREQUENCY, freq);
    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFIFC_DFI_FREQ_FSP, freq_fsp);

    rslt = _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_DFIFC, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);

    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("[Ch %s] Send DFI frequence change cmd failed", ddrctl_sw_channel_str(channel));
    }

    return rslt;
}


/**
 * @brief Method to send DFI clock disable control command (DFICLK)
 *
 * @param cfg               CINIT configuration
 * @param channel           Channels to send the command
 * @param status            Enable/Disable
 * @param active_ranks_map  Active Ranks map
 * @param last_cmd          Last command in the command sequence. Software can send a sequence of commands
 *                          to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_dfi_clock_ctrl(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                              ddrctl_status_t status, uint8_t active_ranks_map,
                                              ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send DFI Clock control %s cmd (Ranks 0x%04x)",
               ddrctl_sw_channel_str(channel), ddrctl_status_to_str(status), active_ranks_map);

    if (DDRCTL_ENABLE == status) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFICLK_DISABLE_CLEAR, 1);
    } else {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFICLK_DISABLE_SET, 1);
    }

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFICLK_CS_N, ~active_ranks_map);

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_DFICLK, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send Command to control the dfi_2n_mode output to DDR PHY (DFI_2N_MODE)
 *
 * @param cfg       CINIT configuration
 * @param channel   Channels to send the command
 * @param status    Enable/Disable
 * @param last_cmd  Last command in the command sequence. Software can send a sequence of commands
 *                  to DDR without any interrupt
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_ctl_dfi_2n_mode(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                               ddrctl_status_t status, ddrctl_sw_cmd_last_t last_cmd)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send Control DFI 2nd mode %s)",
               ddrctl_sw_channel_str(channel), ddrctl_status_to_str(status));

    if (DDRCTL_ENABLE == status) {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFI_2N_MODE_SET, 1);
    } else {
        SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_DFI_2N_MODE_CLEAR, 1);
    }

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_DFI_2N_MODE, cmd_ctrl, channel, 0, DDRCTL_DISABLE, last_cmd);
}


/**
 * @brief Method to send Flush all postponed refreshes command (REF_FLUSH)
 *
 * @note REF_FLUSH can not be used in the middle of atomic SCI sequences. In other
 *       words, the software command interface command issued before REF_FLUSH
 *       should have CMDCTL.cmd_seq_last set to '1'.
 *
 * @param cfg               CINIT configuration
 * @param channel           Channels to send the command
 * @param active_ranks_map  Active Ranks map
 *
 * @retval #DDRCTL_SUCCESS  Success
 * @retval #DDRCTL_ERROR    Unexpected error
 * @retval #DDRCTL_TIMEOUT  Timeout error
 */
ddrctl_error_t cinit_ddr5_send_ref_flush(SubsysHdlr_t *cfg, ddrctl_channel_t channel,
                                         uint8_t active_ranks_map)
{
    uint32_t cmd_ctrl = 0;

    SNPS_DEBUG(SW_CMD_LOG_ID "[Ch %s] Send Flush all postponed refreshes (Ranks 0x%04x)",
               ddrctl_sw_channel_str(channel), active_ranks_map);

    SNPS_WRITE_FIELD(cmd_ctrl, SW_CMD_REF_FLUSH_CS_N, ~active_ranks_map);

    return _ddr5_send_sw_cmd(cfg, SW_CTRL_INTF_REF_FLUSH, cmd_ctrl, channel, 0,
                             DDRCTL_DISABLE, SW_CTRL_LAST_CMD);
}
