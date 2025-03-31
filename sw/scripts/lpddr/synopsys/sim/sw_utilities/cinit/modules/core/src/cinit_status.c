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

#include "cinit_status.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"


#define STAT_OP_MODE_NORMAL  0x01

ddrctl_bool_t cinit_dual_channel_enable()
{
    uint32_t value;
#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
    value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + CHCTL);
    value = SNPS_READ_FIELD(value, CHCTL_DUAL_CHANNEL_EN);
#else
    value = 0;
#endif
    if (value == 1) {
        return DDRCTL_TRUE;
    }
    return DDRCTL_FALSE;
}

uint8_t cinit_get_num_channels_enable()
{
    if (cinit_dual_channel_enable() == DDRCTL_TRUE) {
        return 2;
    }
    return 1;
}


ddrctl_bool_t cinit_is_dual_channel_sync_enable()
{
    uint32_t value;
#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
    value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + PASCTL37);
    value = SNPS_READ_FIELD(value, PASCTL37_DCH_SYNC_MODE);
#else
    value = 0;
#endif
    if (value == 1) {
        return DDRCTL_TRUE;
    }
    return DDRCTL_FALSE;
}

uint8_t cinit_get_active_logical_ranks()
{
#ifdef UMCTL2_CID_EN
    uint32_t value;
    value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + MSTR0);
    value = SNPS_READ_FIELD(value, MSTR0_ACTIVE_LOGICAL_RANKS);
    return (uint8_t) (1 << value);
#else
    return 1;
#endif
}


uint8_t cinit_get_active_ranks_map()
{
    uint32_t value;
    value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(0) + MSTR0);
    value = SNPS_READ_FIELD(value, MSTR0_ACTIVE_RANKS);
    return (uint8_t)value;
}


uint8_t cinit_get_number_ranks()
{
    uint8_t active_ranks;
    uint8_t count = 0;
    uint8_t i;

    active_ranks = cinit_get_active_ranks_map();
    for (i = 0; i < 4; i++) {
        if (SNPS_GET_BIT(active_ranks, i) == 1) {
            count++;
        }
    }
    return count;
}


ddrctl_bool_t cinit_verify_normal_op_mode(ddrctl_channel_t channel_ctrl)
{
    uint32_t reg_value;
    uint8_t  field;
    uint8_t  num_channels;
    uint8_t  channel;
    uint8_t  channel_last;

    if (DDRCTL_CHANNEL_ALL == channel_ctrl) {
        channel = 0;
        if ((cinit_dual_channel_enable() == DDRCTL_TRUE)) {
            channel_last = 1;
        } else {
            channel_last = 0;
        }
    } else {
        channel      = (uint8_t) channel_ctrl;
        channel_last = (uint8_t) channel_ctrl;
    }

    for (; channel <= channel_last; channel++) {

        reg_value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(channel) + STAT);
        field = SNPS_READ_FIELD(reg_value, STAT_OPERATING_MODE);
        if (STAT_OP_MODE_NORMAL != field) {
            SNPS_DEBUG("[Ch %u] Operation mode is not in normal mode 0x%x", channel, field);
            return DDRCTL_FALSE;
        }

        reg_value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(channel) + PWRCTL);
        field = SNPS_READ_FIELD(reg_value, PWRCTL_SELFREF_SW);
        if (0 != field) {
            SNPS_DEBUG("[Ch %u] Software Entry set to Self Refresh mode (PWRCTL=0x%x)", channel, reg_value);
            return DDRCTL_FALSE;
        }

        field = SNPS_READ_FIELD(reg_value, PWRCTL_POWERDOWN_EN);
        if (0 != field) {
            SNPS_DEBUG("[Ch %u] Power-Down enable on ranks 0x%x (PWRCTL=0x%x)", channel, field, reg_value);
            return DDRCTL_FALSE;
        }

        field = SNPS_READ_FIELD(reg_value, PWRCTL_SELFREF_EN);
        if (0 != field) {
            SNPS_DEBUG("[Ch %u] Self Refresh enable on ranks 0x%x (PWRCTL=0x%x)", channel, field, reg_value);
            return DDRCTL_FALSE;
        }

        reg_value = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(channel) + HWLPCTL);
        field = SNPS_READ_FIELD(reg_value, HWLPCTL_HW_LP_EN);
        if (0 != field) {
            SNPS_DEBUG("[Ch %u] Hardware Low Power enable (HWLPCTL=0x%x)", channel, reg_value);
            return DDRCTL_FALSE;
        }
    }

    return DDRCTL_TRUE;
}

