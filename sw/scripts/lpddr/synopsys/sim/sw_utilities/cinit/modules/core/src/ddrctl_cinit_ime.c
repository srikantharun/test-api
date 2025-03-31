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


#include "ddrctl_cinit_ime.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "cinit_status.h"

/** @brief method to preconfigure structures for the IME module.
 * It is expected that customers will have their own secure framework for fetching encryption keys.
 * This is example for simulation in Synopsys testbench.
 * */
void ddrctl_cinit_ime_region_auto_calc(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_SECURE
    uint8_t  channel;
    uint8_t  region;
    uint64_t region_size;
    uint64_t address_space;
    ddrctl_ime_region_t *region_cfg;

    address_space = (1ULL << cinit_cfg->spdData_m.total_address_bits);
    region_size   = address_space / DWC_IME_NUM_REGIONS;

    SNPS_INFO("Total address space = 0x%llx", address_space);
    SNPS_INFO("Creating %d regions of 0x%llx", DWC_IME_NUM_REGIONS, region_size);

    for (channel = 0; channel < cinit_cfg->num_dch; channel++) {
        for (region = 0; region < DWC_IME_NUM_REGIONS; region++) {
            region_cfg = &(cinit_cfg->ime_cfg[channel].region[region]);
            region_cfg->address_start = region_size * region;
            region_cfg->address_end   = (region_size * (region + 1)) - 1;
        }
    }
#endif // DDRCTL_SECURE
}

void ddrctl_cinit_ime_cfg_log(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_SECURE
    uint8_t  channel;
    uint8_t  region;
    uint8_t  slot;
    ddrctl_ime_region_t *region_cfg;

    SNPS_INFO("########################################");
    SNPS_INFO("# In-line Memory Encryption config");

    for (channel = 0; channel < cinit_cfg->num_dch; channel++) {
        SNPS_INFO("[Ch %u] In-line Memory Encryption %s", channel,
                  (cinit_cfg->ime_cfg[channel].enable == 1) ? "Enable" : "Disable");

        if (cinit_cfg->ime_cfg[channel].enable == 0) {
            continue;
        }

        SNPS_INFO("[Ch %u] Key Size %d bits", channel,
                  (cinit_cfg->ime_cfg[channel].key_size == IME_KEY_SZ_128) ? 128 : 256);

        for (region = 0; region < DWC_IME_NUM_REGIONS; region++) {
            region_cfg = &(cinit_cfg->ime_cfg[channel].region[region]);

            SNPS_INFO("[Ch %u][Region %u] Address Range 0x%llx - 0x%llx", channel,
                      region, region_cfg->address_start, region_cfg->address_end);

            for (slot = 0; slot < IME_MAX_KEY_SLOTS; slot++) {
                SNPS_INFO("[Ch %u][Region %u][Slot %u] c_key %u t_key %u", channel,
                          region, slot, region_cfg->c_key_id[slot],
                          region_cfg->t_key_id[slot]);
            }
        }
    }
#endif // DDRCTL_SECURE
}
