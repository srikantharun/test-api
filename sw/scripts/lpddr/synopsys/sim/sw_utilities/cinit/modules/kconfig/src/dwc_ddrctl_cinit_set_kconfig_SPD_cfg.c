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
#include "dwc_ddrctl_cinit_set_kconfig_SPD_cfg.h"
#include "dwc_ddrctl_cinit_set_kconfig_spd_jedec.h"
#include "ddrctl_kconfig_types.h"
#include "dwc_ddrctl_kconfig_mem_addr.h"


static ddrctl_error_t dwc_ddrctl_cinit_set_kconfig_SPD_cfg(void);


static ddrctl_error_t ddrctl_kconfig_get_protocol(uint8_t cfg, ddrSpdData_t *mem_cfg)
{
    switch (cfg) {
        case DDRCTL_KCONFIG_DDR4:
            mem_cfg->sdram_protocol = DWC_DDR4;
            break;
        case DDRCTL_KCONFIG_DDR5:
             mem_cfg->sdram_protocol = DWC_DDR5;
            break;
        case DDRCTL_KCONFIG_LPDDR4:
             mem_cfg->sdram_protocol = DWC_LPDDR4;
            mem_cfg->use_lpddr4x = 0;
            break;
        case DDRCTL_KCONFIG_LPDDR4X:
            mem_cfg->sdram_protocol = DWC_LPDDR4;
            mem_cfg->use_lpddr4x = 1;
            break;
        case DDRCTL_KCONFIG_LPDDR5:
            mem_cfg->sdram_protocol = DWC_LPDDR5;
            mem_cfg->use_lpddr5x = 0;
            break;
        case DDRCTL_KCONFIG_LPDDR5X:
            mem_cfg->sdram_protocol = DWC_LPDDR5;
            mem_cfg->use_lpddr5x = 1;
            break;
        default:
            SNPS_ERROR("Invalid DDR Protocol %d", cfg);
            return DDRCTL_NOT_SUPPORTED;
    }
    return DDRCTL_SUCCESS;
}

ddrctl_error_t dwc_ddrctl_cinit_set_kconfig_memory(void)
{
    ddrctl_error_t  rslt = DDRCTL_SUCCESS;
    ddrSpdData_t   *mem_cfg = &(hdlr->spdData_m);
    uint8_t         device;

    rslt = ddrctl_kconfig_get_protocol(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL, mem_cfg);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("SDRAM Protocol %u not supported", DWC_DDRCTL_CINIT_SDRAM_PROTOCOL);
        return DDRCTL_NOT_SUPPORTED;
    }

#if !defined(DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC)

    mem_cfg->module_type = (dwc_sdram_module_type)DWC_DDRCTL_CINIT_MODULE_TYPE;
    mem_cfg->sdram_capacity_mbits[0] = DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBITS_0;
    mem_cfg->sdram_width_bits[0] = DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_0;
    mem_cfg->cid_width[0] = DWC_DDRCTL_CINIT_CID_WIDTH_0;

#if DWC_DDRCTL_DEV_CFG_NUM > 1
    mem_cfg->sdram_capacity_mbits[1] = DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBITS_1;
    mem_cfg->sdram_width_bits[1] = DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_1;
    mem_cfg->cid_width[1] = DWC_DDRCTL_CINIT_CID_WIDTH_1;
#endif // DWC_DDRCTL_DEV_CFG_NUM

    for (device = 0; device < DWC_DDRCTL_DEV_CFG_NUM; device++) {
        rslt = ddrctl_kconfig_mem_addr(hdlr, device);
        if (DDRCTL_SUCCESS != rslt) {
            SNPS_ERROR("Address configuration failed for device %d", device);
            return rslt;
        }
    }

    mem_cfg->num_ranks = DWC_DDRCTL_CINIT_NUM_RANKS;
    mem_cfg->num_ranks_per_dimm = DWC_DDRCTL_CINIT_NUM_RANKS_PER_DIMM;

#if defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC)
    switch (mem_cfg->sdram_protocol) {
        case DWC_DDR5:
            cinit_kconfig_mem_expert_ddr5_cfg();
            break;
        case DWC_DDR4:
            cinit_kconfig_mem_expert_ddr4_cfg();
            break;
        default:
            SNPS_ERROR("sdram_protocol = %u not yet supported", mem_cfg->sdram_protocol);
            break;
    }
#endif

#if defined(DWC_DDRCTL_CINIT_CUSTOM_TCK) || defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC)
    //CFG->enable_non_jedec_tck = 1;

    mem_cfg->tck_ps[0] = DWC_DDRCTL_CINIT_TCK_PS_0;
#if NUM_PSTATES > 1
    mem_cfg->tck_ps[1] = DWC_DDRCTL_CINIT_TCK_PS_1;
#endif /* NUM_PSTATES > 1 */
#if NUM_PSTATES > 2
    mem_cfg->tck_ps[2] = DWC_DDRCTL_CINIT_TCK_PS_2;
#endif /* NUM_PSTATES > 2 */
#if NUM_PSTATES > 3
    mem_cfg->tck_ps[3] = DWC_DDRCTL_CINIT_TCK_PS_3;
#endif /* NUM_PSTATES > 3 */
#if NUM_PSTATES > 4
    mem_cfg->tck_ps[4] = DWC_DDRCTL_CINIT_TCK_PS_4;
#endif /* NUM_PSTATES > 4 */
#if NUM_PSTATES > 5
    mem_cfg->tck_ps[5] = DWC_DDRCTL_CINIT_TCK_PS_5;
#endif /* NUM_PSTATES > 5 */
#if NUM_PSTATES > 6
    mem_cfg->tck_ps[6] = DWC_DDRCTL_CINIT_TCK_PS_6;
#endif /* NUM_PSTATES > 6 */
#if NUM_PSTATES > 7
    mem_cfg->tck_ps[7] = DWC_DDRCTL_CINIT_TCK_PS_7;
#endif /* NUM_PSTATES > 7 */
#if NUM_PSTATES > 8
    mem_cfg->tck_ps[8] = DWC_DDRCTL_CINIT_TCK_PS_8;
#endif /* NUM_PSTATES > 8 */
#if NUM_PSTATES > 9
    mem_cfg->tck_ps[9] = DWC_DDRCTL_CINIT_TCK_PS_9;
#endif /* NUM_PSTATES > 9 */
#if NUM_PSTATES > 10
    mem_cfg->tck_ps[10] = DWC_DDRCTL_CINIT_TCK_PS_10;
#endif /* NUM_PSTATES > 10 */
#if NUM_PSTATES > 11
    mem_cfg->tck_ps[11] = DWC_DDRCTL_CINIT_TCK_PS_11;
#endif /* NUM_PSTATES > 11 */
#if NUM_PSTATES > 12
    mem_cfg->tck_ps[12] = DWC_DDRCTL_CINIT_TCK_PS_12;
#endif /* NUM_PSTATES > 12 */
#if NUM_PSTATES > 13
    mem_cfg->tck_ps[13] = DWC_DDRCTL_CINIT_TCK_PS_13;
#endif /* NUM_PSTATES > 13 */
#if NUM_PSTATES > 14
    mem_cfg->tck_ps[14] = DWC_DDRCTL_CINIT_TCK_PS_14;
#endif /* NUM_PSTATES > 14 */

#else // defined(DWC_DDRCTL_CINIT_CUSTOM_TCK) || defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC)
    CFG->enable_non_jedec_tck = 0;
#endif // defined(DWC_DDRCTL_CINIT_CUSTOM_TCK) || defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC)

    dwc_ddrctl_cinit_set_kconfig_SPD_cfg();
#endif // !defined(DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC)
    return rslt;
}


/**
 * @brief Function to set SPD confguration values from Kconfig.
 */
static ddrctl_error_t dwc_ddrctl_cinit_set_kconfig_SPD_cfg(void)
{

#if defined(DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE)
#if defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR4)
    SPD.ddr4_sg = DWC_DDRCTL_CINIT_DDR4_SPEED_GRADE;
    SPD.use_ddr4_tcwl_1st_set = DWC_DDRCTL_CINIT_USE_DDR4_TCWL1ST_SET;
    SPD.tAL = DWC_DDRCTL_CINIT_TAL;
#endif /* DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR4 */

#if defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5)
    SPD.ddr5_speed_bin[0] = (dwc_ddr5_speed_bin_t)DWC_DDRCTL_CINIT_DDR5_SPEED_GRADE_0;
#if DDRCTL_NUM_ADDR_MAP > 1
    SPD.ddr5_speed_bin[1] = (dwc_ddr5_speed_bin_t)DWC_DDRCTL_CINIT_DDR5_SPEED_GRADE_1;
#endif /* DDRCTL_NUM_ADDR_MAP */
#endif /* DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5 */

#if defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR4) || defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR4X)
    SPD.lpddr4_data_rate = DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE;
#endif /* defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR4) || defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR4X) */

#if defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR5) || defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR5X)
    SPD.lpddr5_data_rate = DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE;
#endif /* defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR5) || defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR5X) */

#endif /* defined(DWC_DDRCTL_CINIT_SPD_STATIC_SPEED_GRADE) */
    return DDRCTL_SUCCESS;
}

