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


/**
 * @detail The purpose of the functions in this file are to take the setting passed in structures in SubsysHdlr_t
 * and apply them to each of the registers in the IME memory map.
 * After each function is called a 32-bit value is ready to be written into the controller register map.
 * No APB bus cycles are actually executed by calling this methods.
 */

#include "dwc_ddrctl_cinit.h"
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_util.h"


/**
 * @brief function to setup the register field values for IME_KEY_LOAD_IRQ_EN
 */
static void _prgm_regb_ime_key_load_irq_en(SubsysHdlr_t *cfg, uint8_t channel)
{
#ifdef DDRCTL_SECURE
    IME_KEY_LOAD_IRQ_EN_t *const ptr[2] = {
        &REGB_IME_CH0.ime_key_load_irq_en,
        &REGB_IME_CH1.ime_key_load_irq_en
    };
    uint32_t reg_val = ptr[channel]->value;

    SNPS_WRITE_FIELD(reg_val, IME_KEY_LOAD_IRQ_EN_KEY_DONE_EN,
                     cfg->memCtrlr_m.static_cfg.key_done_en[channel]);
    SNPS_WRITE_FIELD(reg_val, IME_KEY_LOAD_IRQ_EN_KEY_MISS_ERR_EN,
                     cfg->memCtrlr_m.static_cfg.key_miss_err_en[channel]);
    SNPS_WRITE_FIELD(reg_val, IME_KEY_LOAD_IRQ_EN_KEY_COLLISION_ERR_EN,
                     cfg->memCtrlr_m.static_cfg.key_collision_err_en[channel]);
    SNPS_WRITE_FIELD(reg_val, IME_KEY_LOAD_IRQ_EN_REG_PARITY_ERR_EN,
                     cfg->memCtrlr_m.static_cfg.reg_parity_err_en[channel]);
    SNPS_WRITE_FIELD(reg_val, IME_KEY_LOAD_IRQ_EN_GLBL,
                     cfg->memCtrlr_m.static_cfg.glbl[channel]);

    if (reg_val != ptr[channel]->value) {
        dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) +
                                           IME_KEY_LOAD_IRQ_EN, reg_val);
    }
#endif /* DDRCTL_SECURE */
}

/**
 * @brief iterate through all IME registers setting up a 32-bit value to
 * be programmed into each writable register.
 */
void dwc_ddrctl_cinit_prgm_REGB_IME(void)
{
    uint8_t channel;
    for (channel = 0; channel < CFG->num_dch; channel++) {
        _prgm_regb_ime_key_load_irq_en(CFG, channel);
    }
}

