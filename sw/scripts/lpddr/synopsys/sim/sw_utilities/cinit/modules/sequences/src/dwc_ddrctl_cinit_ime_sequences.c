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
#include "cinit_status.h"

#ifdef DDRCTL_SECURE

/** @defgroup SwSeqIMEGrp IME software methods/sequences
 * This section groups together software sequences and methods that are common to the integrated memory encryption engine.
 * @{
 */

#define IME_REGION_ADDRESS_OFFSET  16


void ddrctl_ime_program_key_swap(SubsysHdlr_t *cinit_cfg)
{
    uint8_t         num_channels;
    uint8_t         channel;
    uint8_t         region;
    uint16_t        dyn_swap_en_bitmap;

    dyn_swap_en_bitmap = 0;
    num_channels  = cinit_get_num_channels_enable(cinit_cfg);

    for (channel = 0; channel < num_channels; channel++) {
        for (region = 0; region < DWC_IME_NUM_REGIONS; region++) {
            if (cinit_cfg->ime_cfg[channel].region[region].key_swap_enable == 1) {
                dyn_swap_en_bitmap = dyn_swap_en_bitmap | (1 << region);
            }
        }
    }

    dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_KEY_RMW_SWAP_EN,
                                       dyn_swap_en_bitmap);
}


/**
 * @brief Function to program the IME regions address mapping
 * 
 * @param cinit_cfg     CINIT configuration structure
 * @param channel       Channel to load the key
 * @param region        Region to load the key
 */
void ddrctl_ime_program_region_addr(SubsysHdlr_t *cinit_cfg, uint8_t channel, uint8_t region)
{
#ifdef DWC_IME_REGION_ADDR_EN
    uint16_t region_offset;
    ddrctl_ime_region_t *region_cfg;

    region_offset = IME_REGION_ADDRESS_OFFSET * region;
    region_cfg = &(cinit_cfg->ime_cfg[channel].region[region]);

    SNPS_LOG("[Ch %d][Region %d] Address: low = 0x%llx; high = 0x%llx",
             channel, region, region_cfg->address_start, region_cfg->address_end);

    dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_REGION0_ADDR_LOW_31_0   +
                                       region_offset, region_cfg->address_start & 0xffffffff );
    dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_REGION0_ADDR_LOW_63_32  +
                                       region_offset, region_cfg->address_start >> 32);
    dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_REGION0_ADDR_HIGH_31_0  +
                                       region_offset, region_cfg->address_end & 0xffffffff );
    dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_REGION0_ADDR_HIGH_63_32 +
                                       region_offset, region_cfg->address_end >> 32 );
#endif // DWC_IME_REGION_ADDR_EN
}


/**
 * @brief Function to load the IME CKey and TKey
 * 
 * @param cinit_cfg     CINIT configuration structure
 * @param channel       Channel to load the key
 * @param region        Region to load the key
 * @param slot          key selector (Primary of Secondary)
 * @return ddrctl_error_t 
 */
ddrctl_error_t dwc_ddrctl_cinit_ime_key_loading(SubsysHdlr_t *cinit_cfg, uint8_t channel,
                                                uint8_t region, uint8_t slot)
{
    ddrctl_error_t  rslt;
    uint32_t        irq_stat;
    uint32_t        load_ctrl;
    uint32_t        key_data[IME_MAX_KEY_DWORD_SIZE];
    uint8_t         index;
    ddrctl_ime_region_t *region_cfg;

    region_cfg = &(cinit_cfg->ime_cfg[channel].region[region]);

    // Ensure there is no pending interrupt before key loading
    //     The fiedls in IME_KEY_LOAD_IRQ_STAT register are clear on write.
    //     Write back the read value to clear the pending IRQs. If the clear fails, exit.
    irq_stat = dwc_ddrctl_cinit_io_secure_read32(REGB_IME_CH_OFFSET(channel) + IME_KEY_LOAD_IRQ_STAT);
    if (irq_stat != 0) {
        dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_KEY_LOAD_IRQ_STAT, irq_stat);
        irq_stat = dwc_ddrctl_cinit_io_secure_read32(REGB_IME_CH_OFFSET(channel) + IME_KEY_LOAD_IRQ_STAT);
        if (irq_stat != 0) {
            SNPS_ERROR("[Ch %d] Interrupts pending IME_KEY_LOAD_IRQ_STAT = 0x%0x", channel, irq_stat);
            return DDRCTL_ERROR;
        }
    }

    /// Get and program CKey
    ddrctl_user_custom_get_key(region_cfg->c_key_id[slot], cinit_cfg->ime_cfg[channel].key_size, key_data);
    for (index = 0; index < cinit_cfg->ime_cfg[channel].key_size; index++) {
        SNPS_LOG("[Ch %d][Region %d] Loading IME c_key[%u]=0x%x", channel, region, index, key_data[index]);
        dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_CKEY_0 + index*4, key_data[index]);
    }

#ifndef DWC_IME_ECB_EN
    /// Get and program CKey
    ddrctl_user_custom_get_key(region_cfg->t_key_id[slot], cinit_cfg->ime_cfg[channel].key_size, key_data);
    for (index = 0; index < cinit_cfg->ime_cfg[channel].key_size; index++) {
        SNPS_LOG("[Ch %d][Region %d] Loading IME t_key[%u]=0x%x", channel, region, index, key_data[index]);
        dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_TKEY_0 + index*4, key_data[index]);
    }
#endif

    /// - Load keys if busy is not set
    rslt = dwc_ddctl_secure_poll_bitfield(REGB_IME_CH_OFFSET(channel) + IME_KEY_LOAD_STAT,
                                          IME_KEY_LOAD_STAT_BUSY_BIT_OFFSET,
                                          IME_KEY_LOAD_STAT_BUSY_MASK, 0,
                                          DWC_DDRCTL_MAX_APB_POLLING, 0);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("[Ch %d][Region %d] Key load failed, busy bit still active", channel, region);
        return DDRCTL_TIMEOUT;
    }

    load_ctrl = dwc_ddrctl_cinit_io_secure_read32(REGB_IME_CH_OFFSET(channel) + IME_KEY_LOAD_CTRL);
    SNPS_WRITE_FIELD(load_ctrl, IME_KEY_LOAD_CTRL_KEY_IDX, region);
    SNPS_WRITE_FIELD(load_ctrl, IME_KEY_LOAD_CTRL_KEY_SLOT_SEL, slot);
    SNPS_WRITE_FIELD(load_ctrl, IME_KEY_LOAD_CTRL_KEY_SZ, cinit_cfg->ime_cfg[channel].key_size);
    dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_KEY_LOAD_CTRL, load_ctrl);

    rslt = dwc_ddctl_secure_poll_bitfield(REGB_IME_CH_OFFSET(channel) + IME_KEY_LOAD_STAT,
                                          IME_KEY_LOAD_STAT_BUSY_BIT_OFFSET,
                                          IME_KEY_LOAD_STAT_BUSY_MASK, 0,
                                          DWC_DDRCTL_MAX_APB_POLLING, 0);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("[Ch %d][Region %d] Key installation failed, busy bit still active", channel, region);
        return DDRCTL_TIMEOUT;
    }

    /// - Check that there is no pending interrupt other than key_done after key loading completed
    irq_stat = dwc_ddrctl_cinit_io_secure_read32(REGB_IME_CH_OFFSET(channel) + IME_KEY_LOAD_IRQ_STAT);
    if (irq_stat != IME_KEY_LOAD_IRQ_STAT_KEY_DONE_MASK) {
        SNPS_ERROR("[Ch %d] Pending interrupts KEY_LOAD_IRQ_STAT = 0x%0x", channel, irq_stat);
        return DDRCTL_ERROR;
    }

    return DDRCTL_SUCCESS;
}


/**
 * @brief Method to check the result of the IME BIST (Built-In Self-Test)
 * 
 * @param channel 
 * @return ddrctl_error_t 
 */
ddrctl_error_t ddrctl_cinit_ime_bist_test_status(uint32_t channel)
{
    ddrctl_error_t  rslt;
    uint32_t        test_stat;

#ifdef DWC_IME_FIPS_TEST_MODE_EN

    /// - Wait for ime_wrch_self_test_stat.done set
    rslt = dwc_ddctl_secure_poll_bitfield(REGB_IME_CH_OFFSET(channel) + IME_WRCH_SELF_TEST_STAT,
                                          IME_WRCH_SELF_TEST_STAT_WRCH_ST_DONE_BIT_OFFSET,
                                          IME_WRCH_SELF_TEST_STAT_WRCH_ST_DONE_MASK, 1, 
                                          DWC_DDRCTL_MAX_APB_POLLING, 0);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("[Ch %d] Timeout, waiting for write test done status", channel);
        return DDRCTL_ERROR;
    }
    /// - Check status of wrch_st_fail
    test_stat = dwc_ddrctl_cinit_io_secure_read32(REGB_IME_CH_OFFSET(channel) + IME_WRCH_SELF_TEST_STAT);
    if (SNPS_READ_FIELD(test_stat, IME_WRCH_SELF_TEST_STAT_WRCH_ST_FAIL) == 1) {
        SNPS_ERROR("[Ch %d] Write test status indicate fail. 0x%08x", channel, test_stat);
        return DDRCTL_ERROR;
    }

    // Clear status register writing one (W1C fields)
    test_stat = IME_WRCH_SELF_TEST_STAT_WRCH_ST_DONE_MASK |
                IME_WRCH_SELF_TEST_STAT_WRCH_ST_FAIL_MASK | 
                IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_1_MASK;
    dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_WRCH_SELF_TEST_STAT, test_stat);

    /// - Wait for ime_rdch_self_test_stat.done set
    rslt = dwc_ddctl_secure_poll_bitfield(REGB_IME_CH_OFFSET(channel) + IME_RDCH_SELF_TEST_STAT,
                                          IME_RDCH_SELF_TEST_STAT_RDCH_ST_DONE_BIT_OFFSET,
                                          IME_RDCH_SELF_TEST_STAT_RDCH_ST_DONE_MASK, 1, 
                                          DWC_DDRCTL_MAX_APB_POLLING, 0);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("[Ch %d] Timeout, waiting for read test done status", channel);
        return DDRCTL_ERROR;
    }
    /// - Check status of rdch_st_fail
    test_stat = dwc_ddrctl_cinit_io_secure_read32(REGB_IME_CH_OFFSET(channel) + IME_RDCH_SELF_TEST_STAT);
    if (SNPS_READ_FIELD(test_stat, IME_RDCH_SELF_TEST_STAT_RDCH_ST_FAIL) == 1) {
        SNPS_ERROR("[Ch %d] Read test status indicate fail. 0x%08x", channel, test_stat);
        return DDRCTL_ERROR;
    }

    // Clear status register writing one (W1C fields)
    test_stat = IME_RDCH_SELF_TEST_STAT_RDCH_ST_DONE_MASK | 
                IME_RDCH_SELF_TEST_STAT_RDCH_ST_FAIL_MASK |
                IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_1_MASK;
    dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_RDCH_SELF_TEST_STAT, test_stat);

#endif
    return DDRCTL_SUCCESS;
}


ddrctl_error_t ddrctl_sinit_ime_config(SubsysHdlr_t *cinit_cfg)
{
    ddrctl_error_t  rslt;
    uint8_t         num_channels;
    uint8_t         channel;
    uint16_t        region;
    uint32_t        ime_status;

    num_channels  = cinit_get_num_channels_enable(cinit_cfg);

    for (channel = 0; channel < num_channels; channel++) {
        if (cinit_cfg->ime_cfg[channel].enable == 0) {
            SNPS_INFO("[Ch %d] Inline Memory Encryption disable", channel);
            continue;
        }

        ime_status = dwc_ddrctl_cinit_io_secure_read32(REGB_DDRC_CH_OFFSET(channel) + DDRCTL_IMESTAT0);
        if (SNPS_READ_FIELD(ime_status, DDRCTL_IMESTAT0_IME_FORCE_DISABLED) == 1) {
            SNPS_WARN("[Ch %d] Inline Memory Encryption force disabled", channel);
            continue;
        }

        // Allow IME configuration
        ddrctl_user_custom_set_io_ctrl(channel, DDRCTL_IO_IME_CFG_LOCK, DDRCTL_DISABLE);
        ddrctl_user_custom_set_io_ctrl(channel, DDRCTL_IO_IME_CFG_KEY_LOCK, DDRCTL_DISABLE);

        rslt = ddrctl_cinit_ime_bist_test_status(channel);
        if(DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("[Ch %u]IME Build in test failed", channel);
            return rslt;
        }

        // Enable Inline Memory Encryption feature
        dwc_ddrctl_cinit_io_secure_write32(REGB_DDRC_CH_OFFSET(channel) + DDRCTL_IMECFG0, 1);

#if DWC_IME_LATENCY_OPTION == 1
        dwc_ddrctl_cinit_io_secure_write32(REGB_IME_CH_OFFSET(channel) + IME_GLOBAL_KEY_SIZE,
                                           cinit_cfg->ime_cfg[channel].key_size);
#endif

#if DWC_IME_RMW_KEY_SWAP_EN
        ddrctl_ime_program_key_swap(cinit_cfg);
#endif

        for (region = 0; region < DWC_IME_NUM_REGIONS ; region++) {
            ddrctl_ime_program_region_addr(cinit_cfg, channel, region);

            rslt = dwc_ddrctl_cinit_ime_key_loading(cinit_cfg, channel, region, 0);
            if(DDRCTL_SUCCESS != rslt) {
                SNPS_ERROR("[Ch %u][Region %u][Slot %u] IME key load failed ", channel, region, 0);
                return rslt;
            }
#ifdef DDRCTL_IME_KEY_SWAP_EN
            rslt = dwc_ddrctl_cinit_ime_key_loading(cinit_cfg, channel, region, 1);
            if(DDRCTL_SUCCESS != rslt) {
                SNPS_ERROR("[Ch %u][Region %u][Slot %u] IME key load failed ", channel, region, 1);
                return rslt;
            }
#endif // DDRCTL_IME_KEY_SWAP_EN
        }

        /// - ensure ime lock ports are set to 1 after configuration is finished
        ddrctl_user_custom_set_io_ctrl(channel, DDRCTL_IO_IME_CFG_LOCK, DDRCTL_ENABLE);
        ddrctl_user_custom_set_io_ctrl(channel, DDRCTL_IO_IME_CFG_KEY_LOCK, DDRCTL_ENABLE);
    }
    return DDRCTL_SUCCESS;
}



// TODO on demand BIST
/// @} // end SwSeqIMEGrp
#endif // DDRCTL_SECURE
