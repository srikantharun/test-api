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
 * and apply them to each of the registers in the controller memory map.
 * After each function is called a 32-bit value is ready to be written into the controller register map.
 * No APB bus cycles are actually executed by calling this methods.
 */

#include "dwc_ddrctl_cinit.h"
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"

/**
 * @brief function to setup the register field values for ADDRMAP0
 */
#ifdef UMCTL2_DATA_CHANNEL_INTERLEAVE_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP0(void)
{
    SNPS_TRACE("Entering");
    ADDRMAP0_t *const ptr = &REGB_ADDR_MAP0.addrmap0;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, addrmap_dch_bit0);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + ADDRMAP0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_DATA_CHANNEL_INTERLEAVE_EN_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP0(void)
{
};
#endif /* UMCTL2_DATA_CHANNEL_INTERLEAVE_EN_1 */

/**
 * @brief function to setup the register field values for ADDRMAP1
 */
#ifdef MEMC_NUM_RANKS_GT_1
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP1(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP1_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap1,
        &REGB_ADDR_MAP1.addrmap1
    };
    uint32_t tmp = ptr[amap]->value;

#ifdef MEMC_NUM_RANKS_GT_2
    STATIC_CFG_ARRAY(ptr, addrmap_cs_bit1, amap);
#endif /* MEMC_NUM_RANKS_GT_2 */

    STATIC_CFG_ARRAY(ptr, addrmap_cs_bit0, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP1, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP1, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_NUM_RANKS_GT_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP1(uint32_t amap)
{
};
#endif /* MEMC_NUM_RANKS_GT_1 */

/**
 * @brief function to setup the register field values for ADDRMAP2
 */
#ifdef UMCTL2_CID_WIDTH_GT_0
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP2(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP2_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap2,
        &REGB_ADDR_MAP1.addrmap2
    };
    uint32_t tmp = ptr[amap]->value;

#ifdef UMCTL2_CID_WIDTH_GT_1
    STATIC_CFG_ARRAY(ptr, addrmap_cid_b1, amap);
#endif /* UMCTL2_CID_WIDTH_GT_1 */

#ifdef UMCTL2_CID_WIDTH_GT_2
    STATIC_CFG_ARRAY(ptr, addrmap_cid_b2, amap);
#endif /* UMCTL2_CID_WIDTH_GT_2 */

#ifdef UMCTL2_CID_WIDTH_GT_3
    STATIC_CFG_ARRAY(ptr, addrmap_cid_b3, amap);
#endif /* UMCTL2_CID_WIDTH_GT_3 */

    STATIC_CFG_ARRAY(ptr, addrmap_cid_b0, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP2, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP2, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_CID_WIDTH_GT_0 */
static inline void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP2(uint32_t amap)
{
};
#endif /* UMCTL2_CID_WIDTH_GT_0 */

/**
 * @brief function to setup the register field values for ADDRMAP3
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP3(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP3_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap3,
        &REGB_ADDR_MAP1.addrmap3
    };
    uint32_t tmp = ptr[amap]->value;

#ifdef DDRCTL_LPDDR
    STATIC_CFG_ARRAY(ptr, addrmap_bank_b2, amap);
#endif /* DDRCTL_LPDDR */

    STATIC_CFG_ARRAY(ptr, addrmap_bank_b1, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_bank_b0, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP3, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP3, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for ADDRMAP4
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP4(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP4_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap4,
        &REGB_ADDR_MAP1.addrmap4
    };
    uint32_t tmp = ptr[amap]->value;

#ifdef DDRCTL_DDR
    STATIC_CFG_ARRAY(ptr, addrmap_bg_b2, amap);
#endif /* DDRCTL_DDR */

    STATIC_CFG_ARRAY(ptr, addrmap_bg_b1, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_bg_b0, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP4, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP4, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for ADDRMAP5
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP5(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP5_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap5,
        &REGB_ADDR_MAP1.addrmap5
    };
    uint32_t tmp = ptr[amap]->value;

    STATIC_CFG_ARRAY(ptr, addrmap_col_b10, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_col_b9, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_col_b8, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_col_b7, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP5, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP5, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for ADDRMAP6
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP6(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP6_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap6,
        &REGB_ADDR_MAP1.addrmap6
    };
    uint32_t tmp = ptr[amap]->value;

    STATIC_CFG_ARRAY(ptr, addrmap_col_b6, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_col_b5, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_col_b4, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_col_b3, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP6, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP6, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for ADDRMAP7
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP7(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP7_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap7,
        &REGB_ADDR_MAP1.addrmap7
    };
    uint32_t tmp = ptr[amap]->value;

    STATIC_CFG_ARRAY(ptr, addrmap_row_b17, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b16, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b15, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b14, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP7, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP7, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for ADDRMAP8
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP8(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP8_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap8,
        &REGB_ADDR_MAP1.addrmap8
    };
    uint32_t tmp = ptr[amap]->value;

    STATIC_CFG_ARRAY(ptr, addrmap_row_b13, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b12, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b11, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b10, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP8, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP8, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for ADDRMAP9
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP9(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP9_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap9,
        &REGB_ADDR_MAP1.addrmap9
    };
    uint32_t tmp = ptr[amap]->value;

    STATIC_CFG_ARRAY(ptr, addrmap_row_b9, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b8, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b7, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b6, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP9, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP9, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for ADDRMAP10
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP10(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP10_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap10,
        &REGB_ADDR_MAP1.addrmap10
    };
    uint32_t tmp = ptr[amap]->value;

    STATIC_CFG_ARRAY(ptr, addrmap_row_b5, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b4, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b3, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b2, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP10, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP10, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for ADDRMAP11
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP11(uint32_t amap)
{
    SNPS_TRACE("Entering");
    ADDRMAP11_t *const ptr[2] = {
        &REGB_ADDR_MAP0.addrmap11,
        &REGB_ADDR_MAP1.addrmap11
    };
    uint32_t tmp = ptr[amap]->value;

    STATIC_CFG_ARRAY(ptr, addrmap_row_b1, amap);

    STATIC_CFG_ARRAY(ptr, addrmap_row_b0, amap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[amap]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + ADDRMAP11, ptr[amap]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(amap) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP11, ptr[amap]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH

    }
    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for ADDRMAP12
 */
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP12(void)
{
    SNPS_TRACE("Entering");
    ADDRMAP12_t *const ptr = &REGB_ADDR_MAP0.addrmap12;
    uint32_t tmp = ptr->value;
    uint32_t nonbinary_device_density_chk_en;

#ifdef DDRCTL_LPDDR_MIXED_PKG 
        STATIC_CFG(ptr, lpddr_mixed_pkg_x16_size);
        STATIC_CFG(ptr, lpddr_mixed_pkg_en);
#endif /* DDRCTL_LPDDR_MIXED_PKG  */

#ifdef DDRCTL_BANK_HASH 
	STATIC_CFG(ptr, bank_hash_en);
#endif /* DDRCTL_BANK_HASH  */

	STATIC_CFG(ptr, nonbinary_device_density);
#ifdef DDRCTL_LPDDR_MIXED_PKG
	nonbinary_device_density_chk_en = (ptr->lpddr_mixed_pkg_en==1) ? 0 : 1;
#else /* DDRCTL_LPDDR_MIXED_PKG */
	nonbinary_device_density_chk_en = 1;
#endif /* DDRCTL_LPDDR_MIXED_PKG  */

	// check if non binary memory is selected that nonbinary_device_density
	// is programmed to non-zero value
	if (IS_LPDDR5 && nonbinary_device_density_chk_en
			  && (SPD.sdram_capacity_mbits[0] == 3072
			  || SPD.sdram_capacity_mbits[0] == 6144
			  || SPD.sdram_capacity_mbits[0] == 12288
			  || SPD.sdram_capacity_mbits[0] == 24576)) {
		CONSTRAIN_NE(ptr->nonbinary_device_density, 0);
	}

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + ADDRMAP12, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + REG_GROUP_DDRC_CH_SIZE + ADDRMAP12, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for LUTCFG
 */
#ifdef DDRCTL_LUT_ADDRMAP
static void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUTCFG(void)
{
    SNPS_TRACE("Entering");
    ADDRMAPLUTCFG_t *const ptr = &REGB_ADDR_MAP0.addrmaplutcfg;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, addrmap_lut_max_active_hif_addr_offset);

    STATIC_CFG(ptr, addrmap_lut_bit1_valid);

    STATIC_CFG(ptr, addrmap_lut_bit1);

    STATIC_CFG(ptr, addrmap_lut_bit0_valid);

    STATIC_CFG(ptr, addrmap_lut_bit0);

    STATIC_CFG(ptr, addrmap_lut_rank_type);

    STATIC_CFG(ptr, addrmap_use_lut_cs);

    STATIC_CFG(ptr, addrmap_lut_bypass);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + ADDRMAPLUTCFG, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + REG_GROUP_DDRC_CH_SIZE + ADDRMAPLUTCFG, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LUT_ADDRMAP */
static inline void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUTCFG(void)
{
};
#endif /* DDRCTL_LUT_ADDRMAP */

/**
 * @brief function to setup the register field values for LUTCTRL
 */
#ifdef DDRCTL_LUT_ADDRMAP
void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUTCTRL(uint32_t cfg_addr, uint32_t data0, uint32_t data1)
{
    SNPS_TRACE("Entering");
    ADDRMAPLUTCTRL_t *const ptr = &REGB_ADDR_MAP0.addrmaplutctrl;

    ptr->addrmap_lut_rw_type = 1; // write
    ptr->addrmap_lut_addr = cfg_addr;
    ptr->addrmap_lut_wdata1 = data1;
    ptr->addrmap_lut_wdata0 = data0;

    if(UMCTL2_P_ASYNC_EN){
        ptr->addrmap_lut_rw_start = 0;
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + ADDRMAPLUTCTRL, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + REG_GROUP_DDRC_CH_SIZE + ADDRMAPLUTCTRL, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    ptr->addrmap_lut_rw_start = 1;
    dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + ADDRMAPLUTCTRL, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_ADDR_MAP_OFFSET(0) + REG_GROUP_DDRC_CH_SIZE + ADDRMAPLUTCTRL, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LUT_ADDRMAP */
inline void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUTCTRL(uint32_t cfg_addr, uint32_t data0, uint32_t data1)
{
};
#endif /* DDRCTL_LUT_ADDRMAP */

/**
 * @brief write contents of lut entry
 */
#ifdef DDRCTL_LUT_ADDRMAP
void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUT_entry(SubsysHdlr_t *hdlr)
{
    SNPS_TRACE("Entering");
    uint32_t lut_address = 0;
    uint32_t lut_wdata0 = 0;
    uint32_t lut_wdata1 = 0;
    // write lut ctrl contents
    if (!REGB_ADDR_MAP0.addrmaplutcfg.addrmap_lut_bypass) { // lut takes effect
        for (uint32_t lut_index = 0; lut_index < DWC_DDRCTL_MAX_LUT_ENTRIES; lut_index += 2) {
            lut_address = lut_index;
            lut_wdata0 = CFG->lut_entry[lut_index];
            lut_wdata1 = CFG->lut_entry[lut_index + 1];

            dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUTCTRL(lut_address, lut_wdata0, lut_wdata1);
        }
    }
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LUT_ADDRMAP */
inline void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUT_entry(SubsysHdlr_t *hdlr)
{
};
#endif /* DDRCTL_LUT_ADDRMAP */

/**
 * @brief iterate through all AMAP registers setting up a 32-bit value to
 * be programmed into each writable register.
 */
void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP(void)
{
    SNPS_TRACE("Entering");
    /* Only applies to register bank ADDR_MAP0 */
    dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP0();
    dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP12();

    for (uint32_t amap = 0; amap < hdlr->num_amap; amap++) {
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP1(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP2(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP3(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP4(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP5(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP6(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP7(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP8(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP9(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP10(amap);
        dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_ADDRMAP11(amap);
    }
    dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUTCFG();
    SNPS_TRACE("Leaving");
}

