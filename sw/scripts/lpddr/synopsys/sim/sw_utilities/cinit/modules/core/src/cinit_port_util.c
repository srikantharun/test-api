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

#include "cinit_port_util.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_reg_map_macros.h"

#define TIME_BETWEEN_STATUS_CHECKS   20


void _cinit_port_enable(uint8_t port_num, ddrctl_status_t status)
{
#if DDRCTL_HIF_SBR_EN == 0
    uint32_t pctrl = 0;

    // This register only has the PORT_EN field, no read need
    SNPS_WRITE_FIELD(pctrl, PCTRL_PORT_EN, status);

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port_num) + PCTRL, pctrl);
#endif /* DDRCTL_HIF_SBR_EN == 0 */
}

/**
 * @brief Wait until all ports are in idle state
 *
 * @param timeout   number of trys until timeout
 *
 * @return ddrctl_error_t 
 */
ddrctl_error_t ddrctl_cinit_wait_ports_idle(uint32_t timeout)
{
#ifdef UMCTL2_INCL_ARB_OR_CHB
    ddrctl_error_t  rslt;
    const uint8_t   ports_offset = 0;
    const uint32_t  ports_mask   = 0xFFFFFFFF; // check all ports

    rslt = cinit_poll_bitfield(REGB_ARB_PORT_OFFSET(0) + PSTAT, ports_offset, ports_mask, 0,
                               timeout, TIME_BETWEEN_STATUS_CHECKS);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Waiting all ports to be idle timeout, final port status 0x%08x (PSTAT)",
                    dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + PSTAT));
        return rslt;
    }
#endif /* UMCTL2_INCL_ARB_OR_CHB */
    return DDRCTL_SUCCESS;
}


/**
 * @brief Enable/disable the ports
 *
 * @param port_num  port to be enable/disable
 * @param status    enable/disable
 * @param timeout   number of trys until timeout
 *
 * @return ddrctl_error_t
 */
ddrctl_error_t ddrctl_cinit_ctrl_ports(ddrctl_status_t status, uint32_t timeout)
{
#ifdef DDRCTL_ARB_OR_CHB_OR_HIF_SBR_EN_1
#if DDRCTL_HIF_SBR_EN == 0
    ddrctl_error_t  rslt;
    uint8_t         port;
    const uint8_t   ports_offset = 0;
    const uint32_t  ports_mask = 0xFFFFFFFF;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        _cinit_port_enable(port, status);
    }

    if (DDRCTL_DISABLE == status) {
        return ddrctl_cinit_wait_ports_idle(timeout);
    }
#endif /* DDRCTL_HIF_SBR_EN == 0 */
#endif /* DDRCTL_ARB_OR_CHB_OR_HIF_SBR_EN_1 */
    return DDRCTL_SUCCESS;
}


/**
 * @brief Wait until the scrubber for the channel is idle
 * 
 * @param channel   channel number
 * @param timeout   number of trys until timeout
 * @return ddrctl_error_t 
 */
static ddrctl_error_t _cinit_wait_scrubber_idle(ddrctl_channel_t channel, uint32_t timeout)
{
#ifdef UMCTL2_SBR_EN
    ddrctl_error_t  rslt;
    uint32_t        mask;
    const uint8_t   bit_offset = 0; // bit offset can be 0 since we check for 0 in the mask

    mask = 0;

    if ((DDRCTL_CHANNEL_0 == channel) || (DDRCTL_CHANNEL_ALL == channel)) {
        mask |= SBRSTAT_SCRUB_BUSY_MASK;
    }
    if ((DDRCTL_CHANNEL_1 == channel) || 
        ((DDRCTL_CHANNEL_ALL == channel) && (cinit_dual_channel_enable() == DDRCTL_TRUE))) {
        mask |= SBRSTAT_SCRUB_BUSY_DCH1_MASK;;
    }

    rslt = cinit_poll_bitfield(REGB_ARB_PORT_OFFSET(0) + SBRSTAT, bit_offset, mask, 0, timeout, 0);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_ERROR("[Ch %d] Wait scrubber idle timeout, status %u", channel,
                    dwc_ddrctl_cinit_io_read_field(REGB_ARB_PORT_OFFSET(0) + SBRSTAT, bit_offset, mask));
    }
    return rslt;
#else
    return DDRCTL_SUCCESS;
#endif /* UMCTL2_SBR_EN */
}


/**
 * @brief Method to enable/disable the scrubber
 * 
 * @param channel   channel number
 * @param status    enable/disable
 * @return ddrctl_error_t 
 */
ddrctl_error_t ddrctl_cinit_scrubber_enable(ddrctl_channel_t channel, ddrctl_status_t status)
{
#ifdef UMCTL2_SBR_EN_1
    uint32_t value;

    value = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRCTL);

    if ((DDRCTL_CHANNEL_0 == channel) || (DDRCTL_CHANNEL_ALL == channel)) {
        SNPS_WRITE_FIELD(value, SBRCTL_SCRUB_EN, status);
        // This bitfield must be accessed separately from the other bitfields in this register
        dwc_ddrctl_cinit_io_write32(REGB_ARB_PORT_OFFSET(0) + SBRCTL, value);
    }
    if ((DDRCTL_CHANNEL_1 == channel) ||
        ((DDRCTL_CHANNEL_ALL == channel) && (cinit_dual_channel_enable() == DDRCTL_TRUE))) {
        SNPS_WRITE_FIELD(value, SBRCTL_SCRUB_EN_DCH1, status);
        // This bitfield must be accessed separately from the other bitfields in this register
        dwc_ddrctl_cinit_io_write32(REGB_ARB_PORT_OFFSET(0) + SBRCTL, value);
    }

    if (DDRCTL_DISABLE == status) {
        return _cinit_wait_scrubber_idle(channel, DWC_DDRCTL_MAX_APB_POLLING);
    }
#endif /* UMCTL2_SBR_EN_1 */
    return DDRCTL_SUCCESS;
}


/**
 * @brief method to return the state of the global maintain calibration operations
 *
 * @param ch        channel number
 * @return uint8_t  status of the 8 global calibration operations
 */
uint8_t ddrctl_sw_cinit_get_global_maint_calibr(uint8_t ch)
{
    return (uint8_t) dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PASCTL7);
}


/**
 * @brief method to set the state of global maintain calibration operations
 *
 * @param ch                channel number
 * @param value             value to be set
 * @param timeout           timeout counter
 * @return ddrctl_error_t   DDRCTL_SUCCESS, DDRCTL_TIMEOUT
 */
ddrctl_error_t ddrctl_sw_cinit_global_maint_calibr(uint8_t ch, uint8_t value, uint32_t timeout)
{
    ddrctl_error_t rslt;

    REGB_DDRC_CH0.pasctl7.value = (uint32_t)value;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL7, value);

    if (value != 0) {
        return DDRCTL_SUCCESS;
    }

    rslt = cinit_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + STAT2,
                               STAT2_GLB_BLK_EVENTS_ONGOING_BIT_OFFSET,
                               STAT2_GLB_BLK_EVENTS_ONGOING_MASK, 0, timeout, 0);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Polling timeout, stat2.glb_blk_events_ongoing=%u, waiting for glb_blk_events_ongoing=%u",
                    dwc_ddrctl_cinit_io_read_field(REGB_DDRC_CH_OFFSET(ch) + STAT2,
                                                   STAT2_GLB_BLK_EVENTS_ONGOING_BIT_OFFSET,
                                                   STAT2_GLB_BLK_EVENTS_ONGOING_MASK), value);
    }

    return rslt;
}


/**
 * @brief method to set the state of rank maintain calibration operations
 *
 * @param ch            channel number
 * @return uint32_t     status of all rank calibration operations
 */
uint32_t ddrctl_sw_cinit_get_rank_maint_calibr(uint8_t ch)
{
    return dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + PASCTL8);
}


/**
 * @brief method to controll enable/disable rank maintain calibration operations
 *
 * @param ch                channel number
 * @param value             value to be set
 * @param timeout           timeout counter
 * @return ddrctl_error_t   DDRCTL_SUCCESS, DDRCTL_TIMEOUT
 */
ddrctl_error_t ddrctl_sw_cinit_rank_maint_calibr(uint8_t ch, uint8_t value, uint32_t timeout)
{
    ddrctl_error_t rslt;

    REGB_DDRC_CH0.pasctl8.value = value;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL8, value);

    if (value != 0) {
        return DDRCTL_SUCCESS;
    }

    rslt = cinit_poll_bitfield(REGB_DDRC_CH_OFFSET(ch) + STAT3,
                               STAT3_RANK_BLK_EVENTS_ONGOING_BIT_OFFSET,
                               STAT3_RANK_BLK_EVENTS_ONGOING_MASK, 0, timeout, 0);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Polling timeout, stat3.=%u, waiting for =%u",
                    dwc_ddrctl_cinit_io_read_field(REGB_DDRC_CH_OFFSET(ch) + STAT3,
                                                   STAT3_RANK_BLK_EVENTS_ONGOING_BIT_OFFSET,
                                                   STAT3_RANK_BLK_EVENTS_ONGOING_MASK), value);
    }

    return rslt;
}

