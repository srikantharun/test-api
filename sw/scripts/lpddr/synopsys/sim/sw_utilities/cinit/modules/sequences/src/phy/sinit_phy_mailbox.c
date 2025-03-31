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


#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_util.h"
#include "phy/sinit_phy_utils.h"
#include "sinit_types.h"
#include "phy/sinit_phy_types.h"
#include "physetup.h"
#include "phy/ddr54/sinit_ddrphy54_regmap.h"


static inline sinit_error_t _phy_poll_maillbox(uint32_t expt_value, uint32_t timeout)
{
    uint16_t uct_shadow;
    uint16_t msg_status;
    uint32_t counter = 0;

    do {
        uct_shadow = physetup_io_read16(UCTSHADOWREGS);
        msg_status = SNPS_READ_FIELD(uct_shadow, UCTSHADOWREGS_UCTWRITEPROTSHADOW);
        if (expt_value == msg_status) {
            return SINIT_SUCCESS;
        }

        // send a pub read every 50ns
        dwc_ddrctl_cinit_io_nsleep(50);
        counter++;
    } while (counter < timeout);

    return SINIT_TIMEOUT;
}


/** @brief Poll PUB firmware Mailbox message.
 *
 */
sinit_error_t _phy_get_maillbox_msg(phy_mailbox_mode_t mode, uint32_t timeout, uint32_t * fw_msg)
{
    SNPS_LOG("Entering");
    uint16_t        uct_shadow;
    uint16_t        msg_status;
    sinit_error_t   rslt;

    rslt = _phy_poll_maillbox(PHY_MAILBOX_MSG_AVAILABLE, timeout);
    if (SINIT_SUCCESS != rslt) {
        SNPS_ERROR("Mailbox message check timeout");
        goto mailbox_exit;
    }

    /// - read the message
    *fw_msg = physetup_io_read16(UCTWRITEONLYSHADOW);
    if (mode == PHY_MAILBOX_MODE_32) {
        *fw_msg |= physetup_io_read16(UCTDATWRITEONLYSHADOW) << 16;
    }

    physetup_io_write16(DCTWRITEPROT, 0);

    rslt = _phy_poll_maillbox(PHY_MAILBOX_MSG_EMPTY, timeout);
    if (SINIT_SUCCESS != rslt) {
        SNPS_ERROR("Mailbox message acknowledge failed");
        rslt = SINIT_ERROR;
        goto mailbox_exit;
    }
    physetup_io_write16(DCTWRITEPROT, 1);

mailbox_exit:
    SNPS_TRACE("Leaving");
    return rslt;
}

/** @brief Poll PUB firmware Mailbox message.
 *
 */
sinit_error_t sinit_phy_get_maillbox_msg(uint32_t timeout, pub_msg_id_t *pub_msg_id)
{
    sinit_error_t   rslt;
    uint32_t        inter_fw_msg;

    rslt = _phy_get_maillbox_msg(PHY_MAILBOX_MODE_16, timeout, &inter_fw_msg);
    if (SINIT_SUCCESS != rslt) {
        return rslt;
    }

    if (PUB_MSG_START_STREAMING_MESSAGE_MODE == inter_fw_msg) {
        rslt = sinit_phy_print_streaming_msg(timeout);
    }

    *pub_msg_id = (pub_msg_id_t)inter_fw_msg;

    return rslt;
}

/** @brief Poll PUB firmware Mailbox message.
 *
 */
sinit_error_t sinit_phy_print_streaming_msg(uint32_t timeout)
{
    uint32_t msg;
    uint16_t msg_params;
    uint16_t msg_index;
    uint32_t *params_list;
    uint16_t i;
    uint16_t msg_status;
    sinit_error_t rslt;

    rslt = _phy_get_maillbox_msg(PHY_MAILBOX_MODE_32, timeout, &msg);
    if (SINIT_SUCCESS != rslt) {
        goto stream_exit;
    }

    msg_params = SNPS_READ_FIELD(msg, PHY_MSG_PARAMS);
    msg_index  = SNPS_READ_FIELD(msg, PHY_MSG_INDEX);

    if (msg_params > 0) {
        params_list = (uint32_t*) calloc(msg_params, sizeof(uint32_t));

        if (NULL == params_list) {
            rslt = SINIT_MEMORY_ERROR;
            goto stream_exit;
        }

        for (i = 0; i < msg_params; i++) {
            rslt = _phy_get_maillbox_msg(PHY_MAILBOX_MODE_32, timeout, &(params_list[i]));
            if (SINIT_SUCCESS != rslt) {
                goto clean_and_exit;
            }
        }
    }

    SNPS_LOG("Streaming message received: idx 0x%04x 0x%04x", msg_index, msg_params);
    for (i = 0; i < msg_params; i++) {
        SNPS_LOG("0x%08x", params_list[i]);
    }

clean_and_exit:
    if (msg_params > 0) {
        free(params_list);
    }

stream_exit:
    return rslt;
}

/** @brief Poll PUB firmware Mailbox message.
 *
 */
sinit_error_t sinit_phy_get_smbus_request( uint32_t timeout, uint16_t *smbus_msg, uint16_t *smbus_info)
{
    SNPS_LOG("Entering");
    uint32_t        msg;
    sinit_error_t   rslt;

    rslt = _phy_get_maillbox_msg(PHY_MAILBOX_MODE_32, timeout, &msg);
    if (SINIT_SUCCESS != rslt) {
        goto smbus_exit;
    }

    *smbus_msg = SNPS_READ_FIELD(msg, PHY_SMBUS_MSG);
    *smbus_info = SNPS_READ_FIELD(msg, PHY_SMBUS_INFO);

smbus_exit:
    SNPS_TRACE("Leaving");
    return rslt;
}
