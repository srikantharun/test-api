
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



#include "dwc_ddrctl_cinit_kconfig_headers.h"
#include "dwc_ddrctl_kconfig_mem_addr.h"
#include "dwc_ddrctl_cinit_defines.h"


static ddrctl_error_t _mem_addr_ddr4(ddrSpdData_t *config, uint8_t device);

static ddrctl_error_t _mem_addr_ddr5(ddrSpdData_t *config, uint8_t device);

static ddrctl_error_t _mem_addr_lpddr4(ddrSpdData_t *config, uint8_t device);

static ddrctl_error_t _mem_addr_lpddr5(ddrSpdData_t *config, uint8_t device);



ddrctl_error_t ddrctl_kconfig_mem_addr(SubsysHdlr_t *config, uint8_t device)
{
    ddrSpdData_t *memcfg;
    ddrctl_error_t rslt;

    memcfg = &(config->spdData_m);
    rslt = DDRCTL_SUCCESS;

    switch (memcfg->sdram_protocol) {
        case DWC_DDR4:
            rslt = _mem_addr_ddr4(memcfg, device);
            break;
        case DWC_DDR5:
            rslt = _mem_addr_ddr5(memcfg, device);
            break;
        case DWC_LPDDR4:
            rslt = _mem_addr_lpddr4(memcfg, device);
            break;
        case DWC_LPDDR5:
            rslt = _mem_addr_lpddr5(memcfg, device);
            break;
        default:
            SNPS_ERROR("DDR Protocol %d not supported", memcfg->sdram_protocol);
            return DDRCTL_NOT_SUPPORTED;
    }
    memcfg->address_mode[0]=DWC_DDRCTL_CINIT_ADDRESS_MODE_DEV0;
#if DWC_DDRCTL_CINIT_ADDRESS_MODE_DEV0_CONFIG
    if (0 == device) {
        memcfg->dram_caw[device] = DWC_DDRCTL_CINIT_COL_ADDRESSES_0;
        memcfg->dram_raw[device] = DWC_DDRCTL_CINIT_ROW_ADDRESSES_0;
        memcfg->dram_baw[device] = DWC_DDRCTL_CINIT_BANK_ADDRESS_0;
        memcfg->dram_bgw[device] = DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_0;
    }
#endif // DWC_DDRCTL_CINIT_ADDRESS_MODE_DEV0_CONFIG
#if DWC_DDRCTL_CINIT_ADDRESS_MODE_DEV1_CONFIG
#if DWC_DDRCTL_DEV_CFG_NUM > 1
    memcfg->address_mode[1]=DWC_DDRCTL_CINIT_ADDRESS_MODE_DEV1;
    if (1 == device) {
        memcfg->dram_caw[device] = DWC_DDRCTL_CINIT_COL_ADDRESSES_1;
        memcfg->dram_raw[device] = DWC_DDRCTL_CINIT_ROW_ADDRESSES_1;
        memcfg->dram_baw[device] = DWC_DDRCTL_CINIT_BANK_ADDRESS_1;
        memcfg->dram_bgw[device] = DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_1;
    }
#endif /* DWC_DDRCTL_DEV_CFG_NUM > 1 */
#endif // DWC_DDRCTL_CINIT_ADDRESS_MODE_DEV1_CONFIG

    return rslt;
}


static ddrctl_error_t _mem_addr_ddr4(ddrSpdData_t *memcfg, uint8_t device)
{
    memcfg->dram_caw[device] = 10;
    memcfg->dram_baw[device] = 2;

    switch (memcfg->sdram_capacity_mbits[device]) {
        case DDRCTL_2GB:
            memcfg->dram_raw[device] = 15;
            break;
        case DDRCTL_4GB:
            memcfg->dram_raw[device] = 16;
            break;
        case DDRCTL_8GB:
            memcfg->dram_raw[device] = 17;
            break;
        case DDRCTL_16GB:
            memcfg->dram_raw[device] = 18;
            break;
        default:
            SNPS_ERROR("SDRAM capacity not supported %d", memcfg->sdram_capacity_mbits[device]);
            return DDRCTL_NOT_SUPPORTED;
    }

    switch (memcfg->sdram_width_bits[device]) {
        case 4:
            memcfg->dram_bgw[device] = 2;
            break;
        case 8:
            memcfg->dram_bgw[device] = 2;
            memcfg->dram_raw[device] = memcfg->dram_raw[device] - 1;
            break;
        case 16:
            memcfg->dram_bgw[device] = 1;
            memcfg->dram_raw[device] = memcfg->dram_raw[device] - 1;
            break;
        default:
            SNPS_ERROR("SDRAM width not supported %d", memcfg->sdram_width_bits[device]);
            return DDRCTL_NOT_SUPPORTED;
    }

    return DDRCTL_SUCCESS;
}


static ddrctl_error_t _mem_addr_ddr5(ddrSpdData_t * memcfg, uint8_t device)
{
    switch (memcfg->sdram_width_bits[device]) {
        case 4:
            memcfg->dram_caw[device] = 11;
            memcfg->dram_bgw[device] = 3;
            break;
        case 8:
            memcfg->dram_caw[device] = 10;
            memcfg->dram_bgw[device] = 3;
            break;
        case 16:
            memcfg->dram_caw[device] = 10;
            memcfg->dram_bgw[device] = 2;
            break;
        default:
            SNPS_ERROR("SDRAM width not supported %d", memcfg->sdram_width_bits[device]);
            return DDRCTL_NOT_SUPPORTED;
    }

    if (memcfg->sdram_capacity_mbits[device] == DDRCTL_8GB) {
        memcfg->dram_baw[device] = 1;
    } else {
        memcfg->dram_baw[device] = 2;
    }

    switch (memcfg->sdram_capacity_mbits[device]) {
        case DDRCTL_8GB:
        case DDRCTL_16GB:
            memcfg->dram_raw[device] = 16;
            break;
        case DDRCTL_24GB:
        case DDRCTL_32GB:
            memcfg->dram_raw[device] = 17;
            break;
        case DDRCTL_64GB:
            memcfg->dram_raw[device] = 18;
            break;
        default:
            SNPS_ERROR("SDRAM capacity not supported %d", memcfg->sdram_capacity_mbits[device]);
            return DDRCTL_NOT_SUPPORTED;
    }

    return DDRCTL_SUCCESS;
}



static ddrctl_error_t _mem_addr_lpddr4(ddrSpdData_t * memcfg, uint8_t device)
{
    memcfg->dram_caw[device] = 10;
    memcfg->dram_baw[device] = 3;
    memcfg->dram_raw[device] = 14;
    if (memcfg->sdram_capacity_mbits[device] <= DDRCTL_4GB )
        memcfg->dram_raw[device] = 15;
    else if (memcfg->sdram_capacity_mbits[device] <= DDRCTL_8GB)
        memcfg->dram_raw[device] = 16;
    else if (memcfg->sdram_capacity_mbits[device] <= DDRCTL_16GB)
        memcfg->dram_raw[device] = 16;

    return DDRCTL_SUCCESS;
}

static ddrctl_error_t _mem_addr_lpddr5(ddrSpdData_t * memcfg, uint8_t device)
{ 
    memcfg->dram_caw[device] = 10;
    memcfg->dram_baw[device] = 2;
    memcfg->dram_bgw[device] = 2;
    memcfg->dram_raw[device] = 13;
#ifdef CINIT_LPDDR5
    if (memcfg->lpddr5_bk_bg_org[device] == 0) {
        // 4BK_4BG
        memcfg->dram_baw[device] = 2;
        memcfg->dram_bgw[device] = 2;
    } else if (memcfg->lpddr5_bk_bg_org[device] == 2) {
        // 16BK
        memcfg->dram_baw[device] = 3;
        memcfg->dram_bgw[device] = 0;
    }
#endif
    // 16DQ
    if (memcfg->sdram_capacity_mbits[device] <= DDRCTL_4GB ) {
        memcfg->dram_raw[device] = 14;
    } else if (memcfg->sdram_capacity_mbits[device] <= DDRCTL_8GB) {
        memcfg->dram_raw[device] = 15;
    } else if (memcfg->sdram_capacity_mbits[device] <= DDRCTL_16GB) {
        memcfg->dram_raw[device] = 16;
    } else if (memcfg->sdram_capacity_mbits[device] <= DDRCTL_32GB) {
        memcfg->dram_raw[device] = 17;
    }
    // if 8DQ plus 1
    if (memcfg->sdram_width_bits[device] == 8) {
        memcfg->dram_baw[device]++;
        memcfg->dram_raw[device]++;
    }
    return DDRCTL_SUCCESS;
}

