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
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_defines.h"

/**
 * @brief local function to get the Bank address setting for 
 *  MSTR0.BANK_CONFIG and MSTR1.BANK_CONFIG_2 fields from the
 *  configured bank address width
 * 
 * @param bank_addr_width   Memory module bank number
 * @return uint8_t 
 */
static uint8_t _get_mstr_bank_config(uint8_t bank_addr_width)
{
    switch (bank_addr_width) {
        case DDRCTL_BANK_NUMBER_2:
            return 0;
        case DDRCTL_BANK_NUMBER_4:
            return 1;
        case DDRCTL_BANK_NUMBER_8:
            return 2;
        default:
        SNPS_ERROR("Number of banks not supported %d", SPD.dram_baw[0]);
        dwc_ddrctl_cinit_exit(DDRCTL_NOT_SUPPORTED);
    }
    return 0;
}

/**
 * @brief function to setup the register field values for mstr0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR0(void)
{
    MSTR0_t *const ptr = &REGB_DDRC_CH0.mstr0;
    uint32_t tmp = ptr->value;
    mctl_t *memCtrlr = &hdlr->memCtrlr_m;
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[0][0];

#ifdef DDRCTL_DDR
    if (IS_X4(0))
        ptr->device_config = 0;
    else if (IS_X8(0))
        ptr->device_config = 1;
    else if (IS_X16(0))
        ptr->device_config = 2;
#endif /* DDRCTL_DDR */

#ifdef MEMC_NUM_RANKS_GT_1
    STATIC_CFG(ptr, active_ranks);
    CONSTRAIN_NE(ptr->active_ranks, 0);
    CONSTRAIN_NE(ptr->active_ranks, 2);
#endif /* MEMC_NUM_RANKS_GT_1 */

    ptr->active_logical_ranks = CINIT_GET_LRANKS(hdlr, 0);

    SNPS_WRITE_FIELD(ptr->value, MSTR0_BURST_RDWR, DIV_2(timing->burst_length));

    if (IS_LPDDR4 || IS_LPDDR5) {
#ifdef MEMC_BURST_LENGTH_32
	CONSTRAIN_EQ(SNPS_READ_FIELD(ptr->value, MSTR0_BURST_RDWR), 0x10);
#else
        CONSTRAIN_EQ(SNPS_READ_FIELD(ptr->value, MSTR0_BURST_RDWR), 0x8);
#endif /* MEMC_BURST_LENGTH_32 */
    }

    if (IS_DDR5) {
        CONSTRAIN_EQ(SNPS_READ_FIELD(ptr->value, MSTR0_BURST_RDWR), 0x8);
    }

    if (IS_DDR4) {
        CONSTRAIN_EQ(SNPS_READ_FIELD(ptr->value, MSTR0_BURST_RDWR), 0x4);
    }

    STATIC.burst_rdwr = ptr->burst_rdwr;
#ifdef MEMC_DDR3_OR_4
    if (IS_DDR4) {
        if (QDYN.dll_off_mode == 1)
            ptr->dll_off_mode = 1;
        else
            ptr->dll_off_mode = 0;
    } else {
        ptr->dll_off_mode = 0;
    }
#endif /* MEMC_DDR3_OR_4 */

    if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL)
        ptr->data_bus_width = 0;
    else if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_HALF)
        ptr->data_bus_width = 1;
    else
        ptr->data_bus_width = 2;

    STATIC.data_bus_width = ptr->data_bus_width;
#ifndef MEMC_CMD_RTN2IDLE
    if (IS_DDR5 || IS_LPDDR4 || IS_LPDDR5) {
        ptr->en_2t_timing_mode = 0;
    } else {
        STATIC_CFG(ptr, en_2t_timing_mode);
    }
#endif /* !MEMC_CMD_RTN2IDLE */

#ifdef DDRCTL_DDR
    STATIC_CFG(ptr, burstchop);
#endif /* DDRCTL_DDR */

#ifndef UMCTL2_INCL_ARB
    {
        if (IS_LPDDR4)
            ptr->burst_mode = 0;
        else
            STATIC_CFG(ptr, burst_mode);
    }
#endif /* !UMCTL2_INCL_ARB */

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        if (SPD.dram_bgw[0] == 3)
            ptr->bg_config = 2;
        else if (SPD.dram_bgw[0] == 2)
            ptr->bg_config = 1;
        else
            ptr->bg_config = 0;

        STATIC.bg_config = ptr->bg_config;

        CONSTRAIN_MAX(ptr->bg_config, 2);

        SNPS_WRITE_FIELD(ptr->value, MSTR0_BANK_CONFIG, _get_mstr_bank_config(SPD.dram_baw[0]));

        STATIC.bank_config = ptr->bank_config;
    }
#endif  // CINIT_DDR5
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
    if (IS_LPDDR5)
        STATIC.lpddr5 = 1;
    else
        STATIC.lpddr5 = 0;

    STATIC_CFG(ptr, lpddr5);

    if (SPD.use_lpddr5x & IS_LPDDR5) {
        STATIC.lpddr5x = 1;
    } else {
        STATIC.lpddr5x = 0;
    }
    STATIC_CFG(ptr, lpddr5x);
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
    ptr->ddr5 = IS_DDR5;
    STATIC.ddr5 = 1;
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
    if (IS_LPDDR4)
        STATIC.lpddr4 = 1;
    else
        STATIC.lpddr4 = 0;

    STATIC_CFG(ptr, lpddr4);
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
    ptr->ddr4 = IS_DDR4;
    STATIC.ddr4 = 1;
#endif /* DDRCTL_DDR */
	if (IS_DDR5 && STATIC.dual_channel_en && MEMC_DRAM_DATA_WIDTH > 40) {
		// FBW is not supported in DDR5 dual channel mode when MEMC_DRAM_DATA_WIDTH is greater than 40.
		CONSTRAIN_INSIDE(ptr->data_bus_width, 1, 2);
	}
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + MSTR0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + MSTR0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
}

/**
 * @brief function to setup the register field values for mstr1
 */
#ifdef DDRCTL_TWO_DEV_CFG_OR_DDR4_MRAM_EN
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR1(void)
{
    SNPS_TRACE("Entering");
    MSTR1_t *const ptr = &REGB_DDRC_CH0.mstr1;
    uint32_t tmp = ptr->value;

#ifdef DDRCTL_DDR
#ifdef DDRCTL_TWO_DEV_CFG_EN
#if    DWC_DDRCTL_DEV_CFG_NUM > 1
        if (IS_X4(1))
            ptr->device_config_2 = 0;
        else if (IS_X8(1))
            ptr->device_config_2 = 1;
        else if (IS_X16(1))
            ptr->device_config_2 = 2;

        if (SPD.dram_bgw[1] == 3)
            ptr->bg_config_2 = 2;
        else if (SPD.dram_bgw[1] == 2)
            ptr->bg_config_2 = 1;
        else
            ptr->bg_config_2 = 0;

        CONSTRAIN_MAX(ptr->bg_config_2, 2);

        SNPS_WRITE_FIELD(ptr->value, MSTR1_BANK_CONFIG_2, _get_mstr_bank_config(SPD.dram_baw[1]));
#endif
#endif
#endif

#ifdef UMCTL2_CID_EN
#ifdef DDRCTL_TWO_DEV_CFG_EN
#if    DWC_DDRCTL_DEV_CFG_NUM > 1
        ptr->active_logical_ranks_2 = CID_WIDTH(1);
        CONSTRAIN_MAX(ptr->active_logical_ranks_2, 4);
#endif
#endif
#endif

#ifdef UMCTL2_DDR4_MRAM_EN
        STATIC_CFG(ptr, rank_tmgreg_sel);
#endif

#ifdef UMCTL2_HET_RANK_RFC
        STATIC_CFG(ptr, rfc_tmgreg_sel);
#endif

#ifdef UMCTL2_DDR4_MRAM_EN
#ifdef UMCTL2_HET_RANK_RFC
        STATIC_CFG(ptr, alt_addmap_en);
#endif
#endif

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + MSTR1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + MSTR1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_DDR4_MRAM_EN && DDRCTL_TWO_DEV_CFG_OR_DDR4_MRAM_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR1(void)
{
};
#endif /* UMCTL2_DDR4_MRAM_EN && DDRCTL_TWO_DEV_CFG_OR_DDR4_MRAM_EN */

/**
 * @brief function to setup the register field values for mstr2
 */
#ifdef UMCTL2_FREQUENCY_NUM_GT_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR2(void)
{
    SNPS_TRACE("Entering");
    MSTR2_t *const ptr = &REGB_DDRC_CH0.mstr2;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, target_frequency);
    CONSTRAIN_MAX(ptr->target_frequency, 3);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + MSTR2, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + MSTR2, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_FREQUENCY_NUM_GT_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR2(void)
{
};
#endif /* UMCTL2_FREQUENCY_NUM_GT_1 */

/**
 * @brief function to setup the register field values for mstr3
 */
#ifdef DDRCTL_TWO_DEV_CFG__OR__DDR4_NO_CMD_RTN2IDLE
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR3(uint32_t ch)
{
    SNPS_TRACE("Entering");
    MSTR3_t *const ptr[2] = {
        &REGB_DDRC_CH0.mstr3,
        &REGB_DDRC_CH1.mstr3
    };
    uint32_t tmp = ptr[ch]->value;

#ifndef MEMC_CMD_RTN2IDLE
#ifdef CINIT_DDR4
    if (IS_DDR4)
        QDYN_CFG_ARRAY(ptr, geardown_mode, ch);
#endif  // CINIT_DDR4
#endif /* !MEMC_CMD_RTN2IDLE */

#ifdef DDRCTL_TWO_DEV_CFG_EN
#if    DWC_DDRCTL_DEV_CFG_NUM > 1
    STATIC_CFG_ARRAY(ptr, rank_dev_cfg_sel, ch);
#endif
#endif
#ifdef DDRCTL_TWO_TIMING_SETS_EN
    STATIC.rank_tmgset_sel[ch] = STATIC.rank_dev_cfg_sel[ch];
    STATIC_CFG_ARRAY(ptr, rank_tmgset_sel, ch);
#endif

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MSTR3, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_TWO_DEV_CFG__OR__DDR4_NO_CMD_RTN2IDLE  */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR3(uint32_t ch)
{
};
#endif /* DDRCTL_TWO_DEV_CFG__OR__DDR4_NO_CMD_RTN2IDLE */

/**
 * @brief function to setup the register field values for pasctl1
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL1(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL1_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl1,
        &REGB_DDRC_CH1.pasctl1
    };
    uint32_t tmp = ptr[ch]->value;
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        DYN_CFG_ARRAY(ptr, act2rda_cnt_mask, ch);

#ifdef MEMC_FREQ_RATIO_2
        DYN_CFG_ARRAY(ptr, blk_act_en, ch);
#endif /* MEMC_FREQ_RATIO_2 */

#ifdef DDRCTL_GAP_CTRL
        DYN_CFG_ARRAY(ptr, rd_min_gap, ch);
        CONSTRAIN_MAX(ptr->rd_min_gap, 15);

        DYN_CFG_ARRAY(ptr, wr_min_gap, ch);
        CONSTRAIN_MAX(ptr->wr_min_gap, 15);
#endif /* DDRCTL_GAP_CTRL */

        STATIC_CFG_ARRAY(ptr, pre_ab_enable, ch);

#ifdef DDRCTL_PRESB_EN
        STATIC_CFG_ARRAY(ptr, pre_sb_enable, ch);
#endif /* DDRCTL_PRESB_EN */

        DYN_CFG_ARRAY(ptr, fixed_pre_pri_sel, ch);

        DYN_CFG_ARRAY(ptr, dyn_pre_pri_dis, ch);

        QDYN_CFG_ARRAY(ptr, speculative_ref_pri_sel, ch);

        QDYN_CFG_ARRAY(ptr, selfref_wo_ref_pending, ch);

        STATIC_CFG_ARRAY(ptr, pre_slot_config, ch);

	QDYN_CFG_ARRAY(ptr, rank_switch_gap_unit_sel, ch);

	QDYN.mrr_des_timing_unit_sel[ch] = PRE_CFG.mrr_des_timing_unit_sel[ch];
	QDYN_CFG_ARRAY(ptr, mrr_des_timing_unit_sel, ch);
	}

#endif  // CINIT_DDR5
#ifdef DDRCTL_CA_PARITY
    QDYN_CFG_ARRAY(ptr, dfi_alert_assertion_mode, ch);
#endif /* DDRCTL_CA_PARITY */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL1, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL1(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl3
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH) && defined(MEMC_NUM_RANKS_GT_1)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL3(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL3_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl3,
        &REGB_DDRC_CH1.pasctl3
    };
    uint32_t tmp = ptr[ch]->value;
#ifdef CINIT_DDR5
    if (IS_DDR5 && (IS_RDIMM || IS_LRDIMM || IS_UDIMM)) {
        ddrTimingParameters_t *timing = &hdlr->timingParams_m[0][0];

        if (SPD.num_dimm == 2)
            ptr[ch]->dimm_dcaw_en = 3;
        else
            ptr[ch]->dimm_dcaw_en = 1;
        QDYN_CFG_ARRAY(ptr, dimm_n_dcac_m1, ch);
        QDYN.dimm_t_dcaw[ch] = timing->ddr5_dimm_t_dcaw_tck;
		// reg_dimm_t_dcaw programmed with JEDEC value plus MEMC_FREQ_RATIO
        QDYN.dimm_t_dcaw[ch] += MEMC_FREQ_RATIO;
        QDYN_CFG_ARRAY(ptr, dimm_t_dcaw, ch);

        if (CID_WIDTH(0)) {
            QDYN_CFG_ARRAY(ptr, enable_trfc_dpr, ch);
            CONSTRAIN_MAX(ptr[ch]->enable_trfc_dpr, 4);
        }
    }
#endif
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL3, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH && MEMC_NUM_RANKS_GT_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL3(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH && MEMC_NUM_RANKS_GT_1 */

/**
 * @brief function to setup the register field values for dfimisc
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIMISC(void)
{
    SNPS_TRACE("Entering");
    DFIMISC_t *const ptr = &REGB_DDRC_CH0.dfimisc;
    uint32_t tmp = ptr->value;

#ifdef DDRCTL_LPDDR
  DYN_CFG(ptr, dfi_freq_fsp);
#endif /* DDRCTL_LPDDR */

    QDYN_CFG(ptr, dfi_frequency);

#ifdef DDRCTL_DDR
    QDYN_CFG(ptr, dis_dyn_adr_tri);
#endif /* DDRCTL_DDR */

    QDYN_CFG(ptr, dfi_init_start);

	QDYN_CFG(ptr, dfi_reset_n);

#ifdef DDRCTL_LPDDR
    STATIC_CFG(ptr, dfi_channel_mode);
#endif /* DDRCTL_LPDDR */

#ifdef UMCTL2_SHARED_AC
    // In SharedAC RDIMM mode, the dfi_dram_clk_disable must be shared by two channels.
#ifdef CINIT_DDR4
    if (IS_DDR4 && STATIC.dual_channel_en)
        STATIC_CFG(ptr, share_dfi_dram_clk_disable);
#endif
#endif /* UMCTL2_SHARED_AC */

    STATIC_CFG(ptr, dfi_data_cs_polarity);

#ifdef MEMC_DDR4_OR_LPDDR4
#ifdef DDRCTL_DDR4_OR_LPDDR
	STATIC_CFG(ptr, phy_dbi_mode);
#endif //DDRCTL_DDR4_OR_LPDDR
#endif /* MEMC_DDR4_OR_LPDDR4 */

    QDYN_CFG(ptr, dfi_init_complete_en);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIMISC, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DFIMISC, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dfiphymstr
 */
#ifdef DDRCTL_DDR4_OR_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIPHYMSTR(void)
{
    SNPS_TRACE("Entering");
    DFIPHYMSTR_t *const ptr = &REGB_DDRC_CH0.dfiphymstr;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dfi_phymstr_en);

    STATIC_CFG(ptr, dfi_phymstr_blk_ref_x32);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIPHYMSTR, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DFIPHYMSTR, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIPHYMSTR(void)
{
};
#endif

/**
 * @brief function to setup the register field values for dfiupd0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIUPD0(void)
{
    SNPS_TRACE("Entering");
    DFIUPD0_t *const ptr = &REGB_DDRC_CH0.dfiupd0;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, dis_auto_ctrlupd);

    QDYN_CFG(ptr, dis_auto_ctrlupd_srx);

    STATIC_CFG(ptr, ctrlupd_pre_srx);

    STATIC_CFG(ptr, dfi_phyupd_en);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIUPD0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DFIUPD0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for rfshctl0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_RFSHCTL0(void)
{
    SNPS_TRACE("Entering");
    RFSHCTL0_t *const ptr = &REGB_DDRC_CH0.rfshctl0;
    uint32_t tmp = ptr->value;

#ifdef UMCTL2_DDR4_MRAM_EN
    STATIC_CFG(ptr, rank_dis_refresh);
#endif /* UMCTL2_DDR4_MRAM_EN */

#ifdef MEMC_DDR5
#ifdef UMCTL2_CID_EN
  QDYN_CFG(ptr, ref_3ds_burst_limit_thr);
  QDYN_CFG(ptr, ref_3ds_burst_limit_en);
#endif /* UMCTL2_CID_EN */
#endif /* MEMC_DDR5 */

	DYN_CFG(ptr, refresh_update_level);

    DYN_CFG(ptr, dis_auto_refresh);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + RFSHCTL0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + RFSHCTL0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for rfshmod0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_RFSHMOD0(void)
{
    SNPS_TRACE("Entering");
    RFSHMOD0_t *const ptr = &REGB_DDRC_CH0.rfshmod0;
    uint32_t tmp = ptr->value;

#ifdef DDRCTL_LPDDR
	STATIC_CFG(ptr, per_bank_refresh);
	STATIC_CFG(ptr, per_bank_refresh_opt_en);
    STATIC_CFG(ptr, fixed_crit_refpb_bank_en);
        STATIC_CFG(ptr, auto_refab_en);
#endif /* DDRCTL_LPDDR */

    DYN_CFG(ptr, refresh_burst);
    if (IS_DDR4) {
        // refresh_burst, ptr->refresh_timer_start_value_x32, STATIC.mrctrl0.pda_en
        // Fixed 4x
        if (QDYN.fgr_mode == 2) {
            // Need to ensure that a phy update, coming near the end of a refresh burst, does not cause a tRFCmax violation
            // Calculate maximum time for a phy update, divide by tREFI4 (= 7.8/ 4 us) to find how many tREFI4 periods are needed for
            // a phy update. The refresh burst should then be a maximum of 32 - that number.
            CONSTRAIN_MAX(ptr->refresh_burst, 31);
            // Fixed 2x
        } else if (QDYN.fgr_mode == 1) {
            // Need to ensure that a phy update, coming near the end of a refresh burst, does not cause a tRFCmax violation
            // Calculate maximum time for a phy update, divide by tREFI2 (= 7.8/ 2 us) to find how many tREFI2 periods are needed for
            // a phy update. The refresh burst should then be a maximum of 16 - that number.
            CONSTRAIN_MAX(ptr->refresh_burst, 15);
            // Fixed 1x
        } else {
            // Need to ensure that a phy update, coming near the end of a refresh burst, does not cause a tRFCmax violation
            // Calculate maximum time for a phy update, divide by tREFI (= 7.8us) to find how many tREFI periods are needed for
            // a phy update. The refresh burst should then be a maximum of 7 - that number.
            CONSTRAIN_MAX(ptr->refresh_burst, 7);
        }
    } else if (IS_LPDDR4 || IS_LPDDR5) {
        if (0 == STATIC.per_bank_refresh) {
            // Need to ensure that a phy update, coming near the end of a refresh burst, does not cause a tRFCmax violation
            // Calculate maximum time for a phy update, divide by tREFIab to find how many tREFIab periods are needed for
            // a phy update. The refresh burst should then be a maximum of 8 - that number.
            CONSTRAIN_MAX(ptr->refresh_burst, 7);
        }
    } else {
        // Need to ensure that a phy update, coming near the end of a refresh burst, does not cause a tRFCmax violation
        // Calculate maximum time for a phy update, divide by tREFI (= 7.8us) to find how many tREFI periods are needed for
        // a phy update. The refresh burst should then be a maximum of 8 - that number.
        CONSTRAIN_MAX(ptr->refresh_burst, 7);
    }

#ifdef DDRCTL_DDR
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        DYN_CFG(ptr, refresh_burst_2x);
        CONSTRAIN_MAX(ptr->refresh_burst_2x, 7);
        DYN_CFG(ptr, mixed_refsb_hi_thr);
    }
#endif  // CINIT_DDR5
#endif /* DDRCTL_DDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + RFSHMOD0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + RFSHMOD0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for rfshmod1
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_RFSHMOD1(void)
{
    SNPS_TRACE("Entering");
    RFSHMOD1_t *const ptr = &REGB_DDRC_CH0.rfshmod1;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, fgr_mode);
    CONSTRAIN_MAX(ptr->fgr_mode, 2);
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        QDYN_CFG(ptr, same_bank_refresh);
        CONSTRAIN_MAX(ptr->same_bank_refresh, 2);

        QDYN_CFG(ptr, tcr_refab_thr);
    }
#endif
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + RFSHMOD1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + RFSHMOD1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_RFSHMOD1(void)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register filed value for RFMMOD0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_RFMMOD0(void)
{
#ifdef DDRCTL_LPDDR_RFM
	SNPS_TRACE("Entering");
	RFMMOD0_t *const ptr = &REGB_DDRC_CH0.rfmmod0;
	uint32_t tmp = ptr->value;
	QDYN_CFG(ptr, rfmth_rm_thr);
	QDYN_CFG(ptr, raadec);
	QDYN_CFG(ptr, raamult);
	QDYN_CFG(ptr, raaimt);
#ifdef DDRCTL_LPDDR_RFMSBC
	STATIC_CFG(ptr, rfmsbc);
#endif /*DDRCTL_LPDDR_RFMSBC */
	QDYN_CFG(ptr, rfm_en);

	if (tmp != ptr->value) {
		dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + RFMMOD0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + RFMMOD0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
	}

	SNPS_TRACE("Leaving");

#endif /*DDRCTL_LPDDR_RFM*/
}
/**
 * @brief function to setup the register filed value for RFMMOD1
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_RFMMOD1(void)
{
#ifdef DDRCTL_LPDDR_RFM
	SNPS_TRACE("Entering");
	RFMMOD1_t *const ptr = &REGB_DDRC_CH0.rfmmod1;
	uint32_t tmp = ptr->value;
	DYN_CFG(ptr, init_raa_cnt);

	if (tmp != ptr->value) {
		dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + RFMMOD1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + RFMMOD1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
	}

	SNPS_TRACE("Leaving");
#endif  /*DDRCTL_LPDDR_RFM*/
}
/**
 * @brief function to setup the register field values for ZQCTL0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ZQCTL0(void)
{
    SNPS_TRACE("Entering");
    ZQCTL0_t *const ptr = &REGB_DDRC_CH0.zqctl0;
    uint32_t tmp = ptr->value;

    DYN_CFG(ptr, dis_auto_zq);

#ifdef DDRCTL_DDR
    STATIC_CFG(ptr, dis_mpsmx_zqcl);
#endif /* DDRCTL_DDR */

    STATIC_CFG(ptr, zq_resistor_shared);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ZQCTL0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ZQCTL0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for zqctl2
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ZQCTL2(void)
{
    SNPS_TRACE("Entering");
    ZQCTL2_t *const ptr = &REGB_DDRC_CH0.zqctl2;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, dis_srx_zqcl);
    #ifdef UMCTL2_HWFFC_EN
    QDYN_CFG(ptr, dis_srx_zqcl_hwffc);
    #endif
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ZQCTL2, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ZQCTL2, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for sched0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED0(void)
{
    SNPS_TRACE("Entering");
    SCHED0_t *const ptr = &REGB_DDRC_CH0.sched0;
    uint32_t tmp = ptr->value;

#if defined(UMCTL2_VPRW_EN) && defined(MEMC_ENH_RDWR_SWITCH)
    QDYN_CFG(ptr, opt_vprw_sch);
#endif /* UMCTL2_VPRW_EN && MEMC_ENH_RDWR_SWITCH */

#ifdef MEMC_ENH_RDWR_SWITCH
    QDYN_CFG(ptr, dis_speculative_act);
    QDYN_CFG(ptr, w_starve_free_running);    
#endif /* MEMC_ENH_RDWR_SWITCH */

#ifdef DDRCTL_LPDDR
    QDYN_CFG(ptr, prefer_read);
#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_OPT_ACT_LAT
	QDYN_CFG(ptr, opt_act_lat);
#endif /* DDRCTL_OPT_ACT_LAT */

#ifdef DDRCTL_P80001562_91319
    STATIC_CFG(ptr, en_count_every_wr);
#endif /* DDRCTL_P80001562_91319 */
#ifndef MEMC_NO_OF_RD_ENTRY_GT128
    QDYN_CFG(ptr, lpr_num_entries);
#endif

#ifdef MEMC_USE_RMW
    QDYN_CFG(ptr, autopre_rmw);
#endif /* MEMC_USE_RMW */

#ifdef DDRCTL_LLC_4CYCSCH
#ifdef MEMC_NTT_UPD_PRE
	QDYN_CFG(ptr, dis_prefer_col_by_pre);
#endif /* MEMC_NTT_UPD_PRE */
#endif /* DDRCTL_LLC_4CYCSCH */

#ifdef DDRCTL_LLC_4CYCSCH
	QDYN_CFG(ptr, dis_prefer_col_by_act);
#endif /* DDRCTL_LLC_4CYCSCH */

#ifdef MEMC_NTT_UPD_PRE
	QDYN_CFG(ptr, dis_opt_ntt_by_pre);
#endif /* MEMC_NTT_UPD_PRE */

#ifdef MEMC_NTT_UPD_ACT
    QDYN_CFG(ptr, dis_opt_ntt_by_act);
#endif /* MEMC_NTT_UPD_ACT */

#ifdef MEMC_ENH_RDWR_SWITCH
    QDYN_CFG(ptr, opt_wrcam_fill_level);
#endif /* MEMC_ENH_RDWR_SWITCH */

#ifdef MEMC_RDWR_SWITCH_POL_SEL
    QDYN_CFG(ptr, rdwr_switch_policy_sel);
#endif /* MEMC_RDWR_SWITCH_POL_SEL */

    QDYN_CFG(ptr, pageclose);

#ifdef MEMC_INLINE_ECC
    QDYN_CFG(ptr, dis_opt_wrecc_collision_flush);
#endif /* MEMC_INLINE_ECC */

    STATIC_CFG(ptr, prefer_write);

#ifdef DDRCTL_LPDDR
    STATIC_CFG(ptr, lpddr4_opt_act_timing);
    STATIC_CFG(ptr, lpddr5_opt_act_timing);
#endif /* DDRCTL_LPDDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + SCHED0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + SCHED0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for hwlpctl
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_HWLPCTL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    HWLPCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.hwlpctl,
        &REGB_DDRC_CH1.hwlpctl
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, hw_lp_en, ch);

    STATIC_CFG_ARRAY(ptr, hw_lp_exit_idle_en, ch);

#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
    STATIC_CFG_ARRAY(ptr, hw_lp_ctrl, ch);
#endif /* DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH*/

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + HWLPCTL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for hwlpctl2
 */
#if defined(UMCTL2_INCL_ARB_OR_CHB) && defined(MEMC_DDR5)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_HWLPCTL2(uint32_t ch)
{
    SNPS_TRACE("Entering");
    HWLPCTL2_t *const ptr[2] = {
        &REGB_DDRC_CH0.hwlpctl2,
        &REGB_DDRC_CH1.hwlpctl2
    };
    uint32_t tmp = ptr[ch]->value;

    STATIC_CFG_ARRAY(ptr, cactive_in_mask, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + HWLPCTL2, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_INCL_ARB_OR_CHB && MEMC_DDR5 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_HWLPCTL2(uint32_t ch)
{
};
#endif /* UMCTL2_INCL_ARB_OR_CHB && MEMC_DDR5 */

#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CLKGATECTL(void)
{
    SNPS_TRACE("Entering");
    CLKGATECTL_t *const ptr = &REGB_DDRC_CH0.clkgatectl;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, bsm_clk_on);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + CLKGATECTL, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + CLKGATECTL, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CLKGATECTL(void)
{
};
#endif

/**
 * @brief function to setup the register field values for deratectl0
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL0(void)
{
    SNPS_TRACE("Entering");
    DERATECTL0_t *const ptr = &REGB_DDRC_CH0.deratectl0;
    uint32_t tmp = ptr->value;

    DYN_CFG(ptr, derate_enable);

    STATIC_CFG(ptr, lpddr4_refresh_mode);

    DYN_CFG(ptr, derate_mr4_pause_fc);

    DYN_CFG(ptr, dis_trefi_x6x8);

    STATIC_CFG(ptr, dis_trefi_x0125);

    STATIC_CFG(ptr, use_slow_rm_in_low_temp);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DERATECTL0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL0(void)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for rankctl
 */
#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_RANKCTL(void)
{
    SNPS_TRACE("Entering");
    RANKCTL_t *const ptr = &REGB_DDRC_CH0.rankctl;
    uint32_t tmp = ptr->value;

#ifdef UMCTL2_CID_EN
    STATIC_CFG(ptr, max_logical_rank_wr);

    STATIC_CFG(ptr, max_logical_rank_rd);
#endif /* UMCTL2_CID_EN */

#ifdef MEMC_NUM_RANKS_GT_1
    STATIC_CFG(ptr, max_rank_wr);

    STATIC_CFG(ptr, max_rank_rd);
#endif /* MEMC_NUM_RANKS_GT_1 */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + RANKCTL, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + RANKCTL, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_NUM_LRANKS_TOTAL_GT_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_RANKCTL(void)
{
};
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_1 */

/**
 * @brief function to setup the register field values for deratectl1
 */
#ifdef DDRCTL_DDR_OR_MEMC_LPDDR4
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL1(void)
{
    SNPS_TRACE("Entering");
    DERATECTL1_t *const ptr = &REGB_DDRC_CH0.deratectl1;
    uint32_t tmp = ptr->value;
    mctl_t *memCtrlr = &hdlr->memCtrlr_m;
    uint32_t rank0_dev_idx = STATIC.rank_dev_cfg_sel[0] & 0x1;

    if (IS_DDR5) {//DDR5
        STATIC_CFG(ptr,active_derate_byte_rank0);
    } else { //LPDDR
        if (IS_X16(rank0_dev_idx)) {
            if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL) {
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank0 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank0 = 0x05;
                    break;
                case 64:
                    ptr->active_derate_byte_rank0 = 0x55;
                    break;
                }
            } else {//HBW
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank0 = 0x01;
                break;
                case 32:
                    ptr->active_derate_byte_rank0 = 0x01;
                break;
                case 64:
                    ptr->active_derate_byte_rank0 = 0x05;
                break;
                }
            }
        } else if (IS_X8(rank0_dev_idx)) {
            // byte mode
            if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL) {
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank0 = 0x03;
                    break;
                case 32:
                    ptr->active_derate_byte_rank0 = 0x0f;
                    break;
                case 64:
                    ptr->active_derate_byte_rank0 = 0xff;
                    break;
                }
            } else { // HBW
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank0 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank0 = 0x03;
                    break;
                case 64:
                    ptr->active_derate_byte_rank0 = 0x0f;
                    break;
                }
            }
        } else {
            //X4
            ptr->active_derate_byte_rank0 = 0;
        }
    }

#ifdef DDRCTL_LPDDR
    if (DYN.derate_enable) {
        // All "0s" illegal if derating is enabled
        CONSTRAIN_MIN(ptr->active_derate_byte_rank0, 1);
    }
#endif /* DDRCTL_LPDDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DERATECTL1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR_OR_MEMC_LPDDR4 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL1(void)
{
};
#endif /* DDRCTL_DDR_OR_MEMC_LPDDR4 */

/**
 * @brief function to setup the register field values for deratectl2
 */
#if defined(MEMC_NUM_RANKS_GT_1) && defined(DDRCTL_DDR_OR_MEMC_LPDDR4)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL2(void)
{
    SNPS_TRACE("Entering");
    DERATECTL2_t *const ptr = &REGB_DDRC_CH0.deratectl2;
    uint32_t tmp = ptr->value;
    mctl_t *memCtrlr = &hdlr->memCtrlr_m;
    uint32_t rank1_dev_idx = (STATIC.rank_dev_cfg_sel[0] & 0x2) >> 1;

    if (IS_DDR5) {//DDR5
        STATIC_CFG(ptr,active_derate_byte_rank1);
    } else {
        if (IS_X16(rank1_dev_idx)) {
            // LPDDR
            if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL) {
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
#ifdef DDRCTL_LPDDR_MIXED_PKG
                    if (STATIC.lpddr_mixed_pkg_en) {
                        ptr->active_derate_byte_rank1 = 0x03; // is actually x8
                        break;
                    } else {
                        ptr->active_derate_byte_rank1 = 0x01;
                        break;
                    }
#else
                    ptr->active_derate_byte_rank1 = 0x01;
                    break;
#endif /* DDRCTL_LPDDR_MIXED_PKG */
                case 32:
                    ptr->active_derate_byte_rank1 = 0x05;
                    break;
                case 64:
                    ptr->active_derate_byte_rank1 = 0x55;
                    break;
                }
            } else {//HBW
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank1 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank1 = 0x01;
                    break;
                case 64:
                    ptr->active_derate_byte_rank1 = 0x05;
                    break;
                }
            }
        } else if (IS_X8(rank1_dev_idx)) {
            // byte mode
            if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL) {
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank1 = 0x03;
                    break;
                case 32:
                    ptr->active_derate_byte_rank1 = 0x0f;
                    break;
                case 64:
                    ptr->active_derate_byte_rank1 = 0xff;
                    break;
                }
            } else { // HBW
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank1 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank1 = 0x03;
                    break;
                case 64:
                    ptr->active_derate_byte_rank1 = 0x0f;
                    break;
                }
            }
        } else {
            //X4
            ptr->active_derate_byte_rank1 = 0x00;
        }
    }

#ifdef DDRCTL_LPDDR
    if (DYN.derate_enable) {
        // All "0s" illegal if derating is enabled
        CONSTRAIN_MIN(ptr->active_derate_byte_rank1, 1);
    }
#endif /* DDRCTL_LPDDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL2, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DERATECTL2, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_NUM_RANKS_GT_1 && DDRCTL_DDR_OR_MEMC_LPDDR4 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL2(void)
{
};
#endif /* MEMC_NUM_RANKS_GT_1 && DDRCTL_DDR_OR_MEMC_LPDDR4 */

/**
 * @brief function to setup the register field values for deratectl3
 */
#if defined(MEMC_NUM_RANKS_GT_2) && defined(DDRCTL_DDR_OR_MEMC_LPDDR4)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL3(void)
{
    SNPS_TRACE("Entering");
    DERATECTL3_t *const ptr = &REGB_DDRC_CH0.deratectl3;
    uint32_t tmp = ptr->value;
    mctl_t *memCtrlr = &hdlr->memCtrlr_m;
    uint32_t rank2_dev_idx = (STATIC.rank_dev_cfg_sel[0] & 0x4) >> 2;
    if (IS_DDR5) {
        STATIC_CFG(ptr,active_derate_byte_rank2);
    } else { // LPDDR
        if (IS_X16(rank2_dev_idx)) {
            if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL) {
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank2 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank2 = 0x05;
                    break;
                case 64:
                    ptr->active_derate_byte_rank2 = 0x55;
                    break;
                }
            } else {//HBW
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank2 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank2 = 0x01;
                    break;
                case 64:
                    ptr->active_derate_byte_rank2 = 0x05;
                    break;
                }
            }
        } else if (IS_X8(rank2_dev_idx)) {
            // byte mode
            if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL) {
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank2 = 0x03;
                    break;
                case 32:
                    ptr->active_derate_byte_rank2 = 0x0f;
                    break;
                case 64:
                    ptr->active_derate_byte_rank2 = 0xff;
                    break;
                }
            } else { // HBW
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank2 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank2 = 0x03;
                    break;
                case 64:
                    ptr->active_derate_byte_rank2 = 0x0f;
                    break;
                }
            }
        } else {
        //X4
            ptr->active_derate_byte_rank2 = 0;
        }
    }

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL3, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DERATECTL3, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_NUM_RANKS_GT_2 && DDRCTL_DDR_OR_MEMC_LPDDR4 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL3(void)
{
};
#endif /* MEMC_NUM_RANKS_GT_2 && DDRCTL_DDR_OR_MEMC_LPDDR4 */

/**
 * @brief function to setup the register field values for deratectl4
 */
#if defined(MEMC_NUM_RANKS_GT_2) && defined(DDRCTL_DDR_OR_MEMC_LPDDR4)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL4(void)
{
    SNPS_TRACE("Entering");
    DERATECTL4_t *const ptr = &REGB_DDRC_CH0.deratectl4;
    uint32_t tmp = ptr->value;
    mctl_t *memCtrlr = &hdlr->memCtrlr_m;
    uint32_t rank3_dev_idx = (STATIC.rank_dev_cfg_sel[0] & 0x8) >> 3;
    if (IS_DDR5) {
        STATIC_CFG(ptr,active_derate_byte_rank3);
    } else {// LPDDR
        if (IS_X16(rank3_dev_idx)) {
            if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL) {
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank3 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank3 = 0x05;
                    break;
                case 64:
                    ptr->active_derate_byte_rank3 = 0x55;
                    break;
                }
            } else {//HBW
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank3 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank3 = 0x01;
                    break;
                case 64:
                    ptr->active_derate_byte_rank3 = 0x05;
                    break;
                }
            }
        } else if (IS_X8(rank3_dev_idx)) {
            // byte mode
            if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL) {
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank3 = 0x03;
                    break;
                case 32:
                    ptr->active_derate_byte_rank3 = 0x0f;
                    break;
                case 64:
                    ptr->active_derate_byte_rank3 = 0xff;
                    break;
                }
            } else { // HBW
                switch (MEMC_DRAM_TOTAL_DATA_WIDTH) {
                case 16:
                    ptr->active_derate_byte_rank3 = 0x01;
                    break;
                case 32:
                    ptr->active_derate_byte_rank3 = 0x03;
                    break;
                case 64:
                    ptr->active_derate_byte_rank3 = 0x0f;
                    break;
                }
            }
        } else {
            //X4
            ptr->active_derate_byte_rank3 = 0;
        }
    }

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL4, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DERATECTL4, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_NUM_RANKS_GT_2 && DDRCTL_DDR_OR_MEMC_LPDDR4 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL4(void)
{
};
#endif /* MEMC_NUM_RANKS_GT_2 && DDRCTL_DDR_OR_MEMC_LPDDR4 */

/**
 * @brief function to setup the register field values for mrctrl0
 */
#ifdef UMCTL2_CID_EN
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_MRCTRL0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    MRCTRL0_t *const ptr[2] = {
        &REGB_DDRC_CH0.mrctrl0,
        &REGB_DDRC_CH1.mrctrl0
    };
    uint32_t tmp = ptr[ch]->value;
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        DYN_CFG_ARRAY(ptr, mr_cid, ch);
        CONSTRAIN_MAX(ptr[ch]->mr_cid, ((CID_WIDTH(0) >> 1) & 0x1));
    }
#endif
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL0, ptr[ch]->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + MRCTRL0, ptr[ch]->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_CID_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_MRCTRL0(uint32_t ch)
{
};
#endif /* UMCTL2_CID_EN */

/**
 * @brief function to setup the register field values for ecccfg0
 */
#ifdef MEMC_ECC_SUPPORT_GT_0
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCFG0(void)
{
    SNPS_TRACE("Entering");
    ECCCFG0_t *const ptr = &REGB_DDRC_CH0.ecccfg0;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, ecc_mode);
    CONSTRAIN_MAX(ptr->ecc_mode, 5);

    STATIC_CFG(ptr, ecc_type);

#ifndef UMCTL2_INCL_ARB
    STATIC_CFG(ptr, test_mode);
#endif /* !UMCTL2_INCL_ARB */

#ifdef MEMC_ECCAP
    STATIC_CFG(ptr, ecc_ap_en);

    STATIC_CFG(ptr, ecc_ap_err_threshold);
    CONSTRAIN_MAX(ptr->ecc_ap_err_threshold, MEMC_MAX_INLINE_ECC_PER_BURST - 1);
#endif /* MEMC_ECCAP */

#ifdef MEMC_INLINE_ECC
    QDYN_CFG(ptr, ecc_region_map);

    QDYN_CFG(ptr, blk_channel_idle_time_x32);

    STATIC_CFG(ptr, ecc_region_map_granu);

    STATIC_CFG(ptr, ecc_region_map_other);

    STATIC_CFG(ptr, ecc_region_remap_en);
#endif /* MEMC_INLINE_ECC */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ECCCFG0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ECCCFG0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ECC_SUPPORT_GT_0 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCFG0(void)
{
};
#endif /* MEMC_ECC_SUPPORT_GT_0 */

/**
 * @brief function to setup the register field values for ecccfg1
 */
#ifdef MEMC_ECC_SUPPORT_GT_0
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCFG1(void)
{
    SNPS_TRACE("Entering");
    ECCCFG1_t *const ptr = &REGB_DDRC_CH0.ecccfg1;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, data_poison_en);

    QDYN_CFG(ptr, data_poison_bit);

#ifdef MEMC_ECC_SUPPORT_2_OR_3
	QDYN_CFG(ptr, poison_chip_en);
#endif /* MEMC_ECC_SUPPORT_2 */

#ifdef DDRCTL_KBD_SBECC_EN_1
	QDYN_CFG(ptr, poison_advecc_kbd);
#endif

#ifdef MEMC_INLINE_ECC

#ifdef DDRCTL_ECCAP_ENH
    STATIC_CFG(ptr, ecc_ap_mode);
#endif /* DDRCTL_ECCAP_ENH */

    QDYN_CFG(ptr, ecc_region_parity_lock);

    QDYN_CFG(ptr, ecc_region_waste_lock);

#ifdef DDRCTL_LPDDR
    STATIC_CFG(ptr, med_ecc_en);
#endif

    STATIC_CFG(ptr, blk_channel_active_term);
	QDYN_CFG(ptr, prop_rd_ecc_err);

    QDYN_CFG(ptr, active_blk_channel);
#endif /* MEMC_INLINE_ECC */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ECCCFG1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ECCCFG1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ECC_SUPPORT_GT_0 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCFG1(void)
{
};
#endif /* MEMC_ECC_SUPPORT_GT_0 */

/**
 * @brief function to setup the register field values for ecccfg2
 */
#ifdef MEMC_SECDED_SIDEBAND_ECC
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCFG2(void)
{
    SNPS_TRACE("Entering");
    ECCCFG2_t *const ptr = &REGB_DDRC_CH0.ecccfg2;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, flip_bit_pos1);

    QDYN_CFG(ptr, flip_bit_pos0);

    STATIC_CFG(ptr, bypass_internal_ecc);

#ifdef MEMC_USE_RMW
    DYN_CFG(ptr, dis_rmw_ue_propagation);
#endif /* MEMC_USE_RMW */    
#ifdef DDRCTL_EAPAR_EN_1
    STATIC_CFG(ptr, eapar_en);
#endif /* DDRCTL_EAPAR_EN_1 */

#ifdef DDRCTL_KBD_SBECC_EN_1
#ifdef DDRCTL_BF_ECC_EN_1
	STATIC_CFG(ptr, kbd_en);
#endif
#endif

	if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ECCCFG2, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ECCCFG2, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
	}

    SNPS_TRACE("Leaving");
}
#else /* MEMC_SECDED_SIDEBAND_ECC */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCFG2(void)
{
};
#endif /* MEMC_SECDED_SIDEBAND_ECC */

/**
 * @brief function to setup the register field values for eccctl
 */
#ifdef MEMC_ECC_SUPPORT_GT_0
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCTL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    ECCCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.eccctl,
        &REGB_DDRC_CH1.eccctl
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, ecc_corrected_err_intr_en, ch);

    DYN_CFG_ARRAY(ptr, ecc_uncorrected_err_intr_en, ch);

#ifdef MEMC_ECCAP
    DYN_CFG_ARRAY(ptr, ecc_ap_err_intr_en, ch);
#endif /* MEMC_ECCAP */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ECCCTL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ECC_SUPPORT_GT_0 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCTL(uint32_t ch)
{
};
#endif /* MEMC_ECC_SUPPORT_GT_0 */

/**
 * @brief function to setup the register field values for eccpoisonaddr0
 */
#ifdef MEMC_ECC_SUPPORT_GT_0
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONADDR0(void)
{
    SNPS_TRACE("Entering");
    ECCPOISONADDR0_t *const ptr = &REGB_DDRC_CH0.eccpoisonaddr0;
    uint32_t tmp = ptr->value;
    mctl_t *memCtrlr = &hdlr->memCtrlr_m;
    uint32_t l_ecc_poison_col;

    QDYN_CFG(ptr, ecc_poison_col);

    if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_FULL)
        l_ecc_poison_col = (ptr->ecc_poison_col & 0x07); //To compare only ecc_poison_col[2:0]
    else if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_HALF)
        l_ecc_poison_col = (ptr->ecc_poison_col & 0x0f); //To compare only ecc_poison_col[3:0]
    else if (memCtrlr->sdram_bus_width == DWC_BUSWIDTH_QUARTER)
        l_ecc_poison_col = (ptr->ecc_poison_col & 0x1f); //To compare only ecc_poison_col[4:0]
    CONSTRAIN_EQ(l_ecc_poison_col, 0);

#ifdef UMCTL2_CID_EN
    QDYN_CFG(ptr, ecc_poison_cid);
    if (CID_WIDTH(0) == 0)
        CONSTRAIN_EQ(ptr->ecc_poison_cid, 0);
#endif /* UMCTL2_CID_EN */

#ifdef MEMC_NUM_RANKS_GT_1
    QDYN_CFG(ptr, ecc_poison_rank);
#endif /* MEMC_NUM_RANKS_GT_1 */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ECCPOISONADDR0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ECCPOISONADDR0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ECC_SUPPORT_GT_0 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONADDR0(void)
{
};
#endif /* MEMC_ECC_SUPPORT_GT_0 */

/**
 * @brief function to setup the register field values for eccpoisonaddr1
 */
#ifdef MEMC_ECC_SUPPORT_GT_0
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONADDR1(void)
{
    SNPS_TRACE("Entering");
    ECCPOISONADDR1_t *const ptr = &REGB_DDRC_CH0.eccpoisonaddr1;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, ecc_poison_row);

    QDYN_CFG(ptr, ecc_poison_bank);

#ifdef DDRCTL_DDR
    QDYN_CFG(ptr, ecc_poison_bg);
#endif /* DDRCTL_DDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ECCPOISONADDR1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ECCPOISONADDR1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ECC_SUPPORT_GT_0 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONADDR1(void)
{
};
#endif /* MEMC_ECC_SUPPORT_GT_0 */

/**
 * @brief function to setup the register field values for eccpoisonpat0
 */
#ifdef MEMC_ECC_SUPPORT_GT_0
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONPAT0(void)
{
    SNPS_TRACE("Entering");
    ECCPOISONPAT0_t *const ptr = &REGB_DDRC_CH0.eccpoisonpat0;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, ecc_poison_data_31_0);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ECCPOISONPAT0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ECCPOISONPAT0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ECC_SUPPORT_GT_0 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONPAT0(void)
{
};
#endif /* MEMC_ECC_SUPPORT_GT_0 */

/**
 * @brief function to setup the register field values for eccpoisonpat1
 */
#if defined(MEMC_ECC_SUPPORT_GT_0) && defined(MEMC_DRAM_DATA_WIDTH_64)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONPAT1(void)
{
    SNPS_TRACE("Entering");
    ECCPOISONPAT1_t *const ptr = &REGB_DDRC_CH0.eccpoisonpat1;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, ecc_poison_data_63_32);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ECCPOISONPAT1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ECCPOISONPAT1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH

    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ECC_SUPPORT_GT_0 && MEMC_DRAM_DATA_WIDTH_64 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONPAT1(void)
{
};
#endif /* MEMC_ECC_SUPPORT_GT_0 && MEMC_DRAM_DATA_WIDTH_64 */

/**
 * @brief function to setup the register field values for eccpoisonpat2
 */
#ifdef MEMC_ECC_SUPPORT_GT_0
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONPAT2(void)
{
    SNPS_TRACE("Entering");
    ECCPOISONPAT2_t *const ptr = &REGB_DDRC_CH0.eccpoisonpat2;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, ecc_poison_data_71_64);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ECCPOISONPAT2, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ECCPOISONPAT2, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ECC_SUPPORT_GT_0 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONPAT2(void)
{
};
#endif /* MEMC_ECC_SUPPORT_GT_0 */

#ifdef DDRCTL_EAPAR_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_EAPARCTL0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    EAPARCTL0_t *const ptr[2] = {
        &REGB_DDRC_CH0.eaparctl0,
        &REGB_DDRC_CH1.eaparctl0
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, eapar_err_intr_en, ch);

    DYN_CFG_ARRAY(ptr, eapar_err_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, eapar_err_intr_force, ch);

    DYN_CFG_ARRAY(ptr, eapar_err_cnt_clr, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + EAPARCTL0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_EAPAR_EN_1 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_EAPARCTL0(uint32_t ch)
{
};
#endif /* DDRCTL_EAPAR_EN_1 */

/**
 * @brief function to setup the register field values for dbictl
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DBICTL(uint32_t ch)
{
    DBICTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.dbictl,
        &REGB_DDRC_CH1.dbictl
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_DDR4_OR_LPDDR
    if (IS_LPDDR4 || IS_LPDDR5 || IS_DDR4) {
        QDYN_CFG_ARRAY(ptr, rd_dbi_en, ch);
        QDYN_CFG_ARRAY(ptr, wr_dbi_en, ch);
    }
#endif /* DDRCTL_LPDDR */

    QDYN_CFG_ARRAY(ptr, dm_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DBICTL, ptr[ch]->value);
    }
}


/**
 * @brief function to setup the register field values for dimmctl
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DIMMCTL(void)
{
    SNPS_TRACE("Entering");
    DIMMCTL_t *const ptr = &REGB_DDRC_CH0.dimmctl;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, rcd_b_output_disabled);

#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
#ifdef CINIT_DDR5
    if (IS_DDR5 && (IS_RDIMM || IS_LRDIMM))
        DYN_CFG(ptr, dimm_selfref_clock_stop_mode);
#endif // CINIT_DDR5
#endif /* DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH*/

    STATIC_CFG(ptr, rcd_a_output_disabled);

    QDYN_CFG(ptr, rcd_weak_drive);
#ifdef CINIT_DDR5
    if (IS_DDR5)
        STATIC_CFG(ptr, dimm_type);
#endif  // CINIT_DDR5

#ifdef UMCTL2_HWFFC_EN
    // HWFFC not yet supported
    uint8_t rcd_num;

    if (IS_RDIMM || IS_LRDIMM)
        STATIC.rcd_num = 0;
    else
        STATIC.rcd_num = 0;
    STATIC_CFG(ptr, rcd_num);
#endif /* UMCTL2_HWFFC_EN */

    if (IS_DDR4 && IS_LRDIMM)
        STATIC.lrdimm_bcom_cmd_prot = 1; // not supported for DDR5
    else
        STATIC.lrdimm_bcom_cmd_prot = 0;
    STATIC_CFG(ptr, lrdimm_bcom_cmd_prot);

    if (SPD.sdram_width_bits[0] == 16)
        STATIC.dimm_dis_bg_mirroring = 1;
    else
        STATIC.dimm_dis_bg_mirroring = 0;
    STATIC_CFG(ptr, dimm_dis_bg_mirroring);

    if (SPD.sdram_width_bits[0] == 16) {
        // PHY parity calculation always includes BG1.
        if (hdlr->phy_training)
            STATIC.mrs_bg1_en = 1;
        else
            STATIC.mrs_bg1_en = 0; // Not to include BG1 (BG0 of odd ranks) for parity calculation
    } else {
        STATIC.mrs_bg1_en = 1;
    }
    STATIC_CFG(ptr, mrs_bg1_en);

    if (IS_X4(0))
        STATIC.mrs_a17_en = 1;
    else
        STATIC.mrs_a17_en = 0;

    STATIC_CFG(ptr, mrs_a17_en);

    STATIC_CFG(ptr, dimm_output_inv_en);
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        if (IS_RDIMM || IS_LRDIMM)
            STATIC.dimm_stagger_cs_en = 1;
    }
#endif  // CINIT_DDR4

    STATIC_CFG(ptr, dimm_addr_mirr_en);

    STATIC_CFG(ptr, dimm_stagger_cs_en);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DIMMCTL, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DIMMCTL, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DIMMCTL(void)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for opctrl0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OPCTRL0(void)
{
    SNPS_TRACE("Entering");
    OPCTRL0_t *const ptr = &REGB_DDRC_CH0.opctrl0;
    uint32_t tmp = ptr->value;

#ifdef MEMC_BYPASS
    STATIC_CFG(ptr, dis_act_bypass);

    STATIC_CFG(ptr, dis_rd_bypass);
#endif /* MEMC_BYPASS */

    STATIC_CFG(ptr, dis_wc);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + OPCTRL0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + OPCTRL0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for opctrl1
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OPCTRL1(uint32_t ch)
{
    SNPS_TRACE("Entering");
    OPCTRL1_t *const ptr[2] = {
        &REGB_DDRC_CH0.opctrl1,
        &REGB_DDRC_CH1.opctrl1
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, dis_hif, ch);

    DYN_CFG_ARRAY(ptr, dis_dq, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRL1, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for pwrctl
 */
void dwc_ddrctl_cinit_prgm_REGB_DDRC_PWRCTL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PWRCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.pwrctl,
        &REGB_DDRC_CH1.pwrctl
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_LPDDR
    DYN_CFG_ARRAY(ptr, lpddr4_sr_allowed, ch);
#endif /* DDRCTL_LPDDR */

    DYN_CFG_ARRAY(ptr, dis_cam_drain_selfref, ch);

#ifdef DDRCTL_LPDDR
    DYN_CFG_ARRAY(ptr, stay_in_selfref, ch);
#endif /* DDRCTL_LPDDR */

    DYN_CFG_ARRAY(ptr, selfref_sw, ch);

#ifdef DDRCTL_DDR
    DYN_CFG_ARRAY(ptr, mpsm_en, ch);
#endif /* DDRCTL_DDR */

    DYN_CFG_ARRAY(ptr, en_dfi_dram_clk_disable, ch);

    DYN_CFG_ARRAY(ptr, powerdown_en, ch);

    DYN_CFG_ARRAY(ptr, selfref_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PWRCTL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for hwffcctl
 */
#ifdef UMCTL2_HWFFC_EN
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_HWFFCCTL(void)
{
    SNPS_TRACE("Entering");
    HWFFCCTL_t *const ptr = &REGB_DDRC_CH0.hwffcctl;
    uint32_t tmp = ptr->value;

#ifdef DDRCTL_DDR
    if (IS_DDR4) {
        if (IS_RDIMM) {
            if (hdlr->mr7_by_phy) {
                // RDIMM: RCD01 or RCD02 Sequence A
                ptr->init_vrcg = 1;

                ptr->target_vrcg = 1;

                ptr->ctrl_word_num = 0;

                ptr->cke_power_down_mode = 0;

                ptr->power_saving_ctrl_word = 0;

                //ptr->init_vrcg = 1; // 1: CKE Power down mode in F0RC09 needs to be disabled BEFORE FFC
                //ptr->target_vrcg = 1; // 1: CKE Power down mode in F0RC09 needs to be ensabled AFTER FFC
                //ptr->ctrl_word_num = 0; // uMCTL2 does not send any MRS commands for RCD (MR7: Control Word)
                //ptr->cke_power_down_mode = 1; //
                //ptr->power_saving_ctrl_word = 0;    // [3] TODO: To be removed (actually RTL does not use this bit)
                // [2] 0: CKE powerdown with IBT ON                , 1: IBT OFF
                // [1] 0: DCS1 Input Buffer & QxCS1 Outputs Enabled, 1: Disabled
                // [0] 0: DCS1 Input Bus Termination        Enabled, 1: Disabled
            } else {
                // RDIMM: RCD02 Sequence B
                ptr->init_vrcg = 0;

                //ptr->init_vrcg = 0;
                DYN_CFG(ptr, ctrl_word_num);
                CONSTRAIN_INSIDE(ptr->ctrl_word_num, 2, 8);    // F0RC5x, F0RC3x and another commands are for coverage only.

                ptr->cke_power_down_mode = 0;

                ptr->power_saving_ctrl_word = 0;

                //ptr->cke_power_down_mode = 0; // RCD02 Sequence B
                //ptr->power_saving_ctrl_word = 0;
            }
        } else {
            // NODIMM, UDIMM
            ptr->init_vrcg = 0;

            //ptr->init_vrcg = 0;
            ptr->ctrl_word_num = 0;
            CONSTRAIN_MAX(ptr->ctrl_word_num, 1);    // for coverage only.

            ptr->cke_power_down_mode = 0;

            ptr->power_saving_ctrl_word = 0;

            //ptr->cke_power_down_mode = 0;
            //ptr->power_saving_ctrl_word = 0;
        }
    } else {
        ptr->init_vrcg = 0;
    }
#endif /* DDRCTL_DDR */


#ifdef DDRCTL_LPDDR
	    STATIC_CFG(ptr, hwffc_mode);
	    STATIC_CFG(ptr, skip_zq_stop_start);
	    STATIC_CFG(ptr, zq_interval);
	    STATIC_CFG(ptr, init_vrcg);
	    STATIC_CFG(ptr, target_vrcg);
	    STATIC_CFG(ptr, skip_mrw_odtvref);
#endif /* DDRCTL_LPDDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
	    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + HWFFCCTL, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_HWFFC_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_HWFFCCTL(void)
{
};
#endif /* UMCTL2_HWFFC_EN */

/**
 * @brief function to setup the register field values for cgctl
 */
#ifdef DDRCTL_CLK_GATE_TE_OR_ARB
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CGCTL(void)
{
    SNPS_TRACE("Entering");
    CGCTL_t *const ptr = &REGB_DDRC_CH0.cgctl;
    uint32_t tmp = ptr->value;

#ifdef DDRCTL_CLK_GATE_TE
    DYN_CFG(ptr, force_clk_te_en);
#endif /* DDRCTL_CLK_GATE_TE */

#ifdef DDRCTL_CLK_GATE_ARB
    DYN_CFG(ptr, force_clk_arb_en);
#endif /* DDRCTL_CLK_GATE_ARB */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + CGCTL, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + CGCTL, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_CLK_GATE_TE_OR_ARB  */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CGCTL(void)
{
};
#endif /* DDRCTL_CLK_GATE_TE_OR_ARB */

/**
 * @brief function to setup the register field values for inittmg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_INITTMG0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    INITTMG0_t *const ptr[2] = {
        &REGB_DDRC_CH0.inittmg0,
        &REGB_DDRC_CH1.inittmg0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_ARRAY(ptr, skip_dram_init, ch);
    CINIT_ASSERT(ptr[ch]->skip_dram_init != 2);    // 2'b10 is reserved value

    STATIC_CFG_ARRAY(ptr, pre_cke_x1024, ch);

    if (hdlr->use_snps_vip_timing) {
        if (IS_LPDDR4 || IS_LPDDR5)
            CONSTRAIN_MIN(ptr[ch]->pre_cke_x1024, 2);
#ifdef CINIT_DDR4
        if (IS_DDR4) {
            if (!hdlr->use_jedec_init)
                CONSTRAIN_MIN(ptr[ch]->pre_cke_x1024, 2);
        }
#endif
    }
    if (hdlr->use_jedec_init) {
        // Ensure Real Initialization Timing
#ifdef CINIT_DDR4
        if (IS_DDR4) {
            // after reset is de-ASSERTed, wait for 500us
            STATIC.pre_cke_x1024[ch] = 500000000 / (SPD.tck_ps[0] * MEMC_FREQ_RATIO * 1024) + 1;
        }
#elif defined (CINIT_LPDDR4) || defined (CINIT_LPDDR5)
        if (IS_LPDDR4 || IS_LPDDR5) {
            // after reset is de-ASSERTed, wait for 2 ms (tINITTMG2)
            // use tCKb instead of tCK when the slow boot clock is enabled (Bugzilla 4012)
            STATIC.pre_cke_x1024[ch] = 2000000000 / (SPD.tck_ps[0] * MEMC_FREQ_RATIO * 1024) + 1;
            // tINITTMG0 ? or tINITTMG0 + tINITTMG1 ?
        }
#endif
        STATIC_CFG_ARRAY(ptr, pre_cke_x1024, ch);
    } else {
        CONSTRAIN_INSIDE(ptr[ch]->pre_cke_x1024, 2, 4095);
    }
// post_cke_x1024
    if (hdlr->use_jedec_init) {
#ifdef DDRCTL_DDR
        // Ensure Real Initialization Timing
#ifdef CINIT_DDR4
        if (IS_DDR4) {
            // after CKE is high, wait tXPR ( tXPR = max (5tCK, tXS)), before issuing the first MRS
            // tXS = tRFCmin + 10ns
            STATIC.post_cke_x1024[ch] = (hdlr->timingParams_m[0][0].ddr4_trfc_min_ps + 10000) / (1024 * SPD.tck_ps[0] * MEMC_FREQ_RATIO) + 1;
        }
#endif // CINIT_DDR4
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
#if defined(CINIT_LPDDR4) || defined(CINIT_LPDDR5)
        if (IS_LPDDR4 || IS_LPDDR5) {
            // LPDDR4 : after CKE is high, wait tINITTMG5 (2 us), before issuing the MRR or MRW
            // use tCKb instead of tCK when the slow boot clock is enabled (Bugzilla 4012)
            STATIC.post_cke_x1024[ch] = 2000000 / (SPD.tck_ps[0] * MEMC_FREQ_RATIO * 1024) + 1;
        }
#endif
#endif /* DDRCTL_LPDDR */
        STATIC_CFG_ARRAY(ptr, pre_cke_x1024, ch);
    }
    STATIC_CFG_ARRAY(ptr, post_cke_x1024, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + INITTMG0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for inittmg2
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_INITTMG2(uint32_t ch)
{
    SNPS_TRACE("Entering");
    INITTMG2_t *const ptr[2] = {
        &REGB_DDRC_CH0.inittmg2,
        &REGB_DDRC_CH1.inittmg2
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef CINIT_DDR4
    ddrTimingParameters_t *timing = &hdlr->timingParams_m[0][0];
    if (IS_DDR4)
        STATIC.dev_zqinit_x32[ch] = DIV_32(timing->ddr4_tzqinit_tck) + 1;
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5)
        STATIC.dev_zqinit_x32[ch] = 0;
#endif /* CINIT_DDR5 */

    STATIC_CFG_ARRAY(ptr, dev_zqinit_x32, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + INITTMG2, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_INITTMG2(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for mstr4
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR4(uint32_t ch)
{
    SNPS_TRACE("Entering");
    MSTR4_t *const ptr[2] = {
        &REGB_DDRC_CH0.mstr4,
        &REGB_DDRC_CH1.mstr4
    };
    uint32_t tmp = ptr[ch]->value;
    mctl_t *memCtrlr = &hdlr->memCtrlr_m;

    // mode register are per frequency but mstr4 is per channel
    QDYN_CFG_ARRAY(ptr, wck_on, ch);
    // mode register are per frequency but mstr4 is per channel
    #ifndef LPDDR_2MC1PHY 
    CONSTRAIN_EQ(ptr[ch]->wck_on, memCtrlr->lpddr5_mr[0].mr18.wck_on);
    #endif /* LPDDR_2MC1PHY */

	QDYN_CFG_ARRAY(ptr, wck_suspend_en, ch);
	QDYN_CFG_ARRAY(ptr, ws_off_en, ch);

	if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
		dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MSTR4, ptr[ch]->value);
        }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR4(uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for mrctrl1
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_MRCTRL1(uint32_t ch)
{
    SNPS_TRACE("Entering");
    MRCTRL1_t *const ptr[2] = {
        &REGB_DDRC_CH0.mrctrl1,
        &REGB_DDRC_CH1.mrctrl1
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, mr_data, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL1, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for mrctrl2
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_MRCTRL2(uint32_t ch)
{
    SNPS_TRACE("Entering");
    MRCTRL2_t *const ptr[2] = {
        &REGB_DDRC_CH0.mrctrl2,
        &REGB_DDRC_CH1.mrctrl2
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, mr_device_sel, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + MRCTRL2, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_MRCTRL2(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for adveccindex
 */
#ifdef MEMC_ECC_SUPPORT_GT_0
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ADVECCINDEX(void)
{
    SNPS_TRACE("Entering");
    ADVECCINDEX_t *const ptr = &REGB_DDRC_CH0.adveccindex;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, ecc_poison_beats_sel);

    QDYN_CFG(ptr, ecc_err_symbol_sel);

    QDYN_CFG(ptr, ecc_syndrome_sel);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + ADVECCINDEX, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + ADVECCINDEX, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ECC_SUPPORT_GT_0 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ADVECCINDEX(void)
{
};
#endif /* MEMC_ECC_SUPPORT_GT_0 */

/**
 * @brief function to setup the register field values for ocparcfg0
 */
#ifdef UMCTL2_OCPAR_OR_OCECC_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCPARCFG0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    OCPARCFG0_t *const ptr[2] = {
        &REGB_DDRC_CH0.ocparcfg0,
        &REGB_DDRC_CH1.ocparcfg0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_ARRAY(ptr, oc_parity_en, ch);

    QDYN_CFG_ARRAY(ptr, oc_parity_type, ch);

#ifdef UMCTL2_OCPAR_EN_1
    DYN_CFG_ARRAY(ptr, par_wdata_err_intr_en, ch);

    QDYN_CFG_ARRAY(ptr, par_wdata_slverr_en, ch);

    DYN_CFG_ARRAY(ptr, par_wdata_err_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, par_wdata_err_intr_force, ch);

    QDYN_CFG_ARRAY(ptr, par_rdata_slverr_en, ch);

    DYN_CFG_ARRAY(ptr, par_rdata_err_intr_en, ch);

    DYN_CFG_ARRAY(ptr, par_rdata_err_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, par_rdata_err_intr_force, ch);

    QDYN_CFG_ARRAY(ptr, par_wdata_axi_check_bypass_en, ch);
#endif /* UMCTL2_OCPAR_EN_1 */

    QDYN_CFG_ARRAY(ptr, par_addr_slverr_en, ch);

    DYN_CFG_ARRAY(ptr, par_waddr_err_intr_en, ch);

    DYN_CFG_ARRAY(ptr, par_waddr_err_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, par_raddr_err_intr_en, ch);

    DYN_CFG_ARRAY(ptr, par_raddr_err_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, par_waddr_err_intr_force, ch);

    DYN_CFG_ARRAY(ptr, par_raddr_err_intr_force, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OCPARCFG0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_OCPAR_OR_OCECC_EN_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCPARCFG0(uint32_t ch)
{
};
#endif /* UMCTL2_OCPAR_OR_OCECC_EN_1 */

/**
 * @brief function to setup the register field values for ocsapcfg0
 */
#ifdef DDRCTL_OCSAP_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCSAPCFG0(void)
{
    SNPS_TRACE("Entering");
    OCSAPCFG0_t *const ptr = &REGB_DDRC_CH0.ocsapcfg0;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, ocsap_par_en);

    QDYN_CFG(ptr, ocsap_poison_en);

    QDYN_CFG(ptr, wdataram_addr_poison_loc);

    QDYN_CFG(ptr, rdataram_addr_poison_loc);

    QDYN_CFG(ptr, wdataram_addr_poison_ctl);

    QDYN_CFG(ptr, rdataram_addr_poison_ctl);

    QDYN_CFG(ptr, rdataram_addr_poison_port);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + OCSAPCFG0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + OCSAPCFG0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_OCSAP_EN_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCSAPCFG0(void)
{
};
#endif /* DDRCTL_OCSAP_EN_1 */

/**
 * @brief function to setup the register field values for OCSAPCFG1
 */
#ifdef UMCTL2_OCPAR_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCPARCFG1(void)
{
    SNPS_TRACE("Entering");
    OCPARCFG1_t *const ptr = &REGB_DDRC_CH0.ocparcfg1;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, par_poison_en);

    QDYN_CFG(ptr, par_poison_loc_rd_dfi);

#ifdef MEMC_INLINE_ECC
    QDYN_CFG(ptr, par_poison_loc_rd_iecc_type);
#endif /* MEMC_INLINE_ECC */

    QDYN_CFG(ptr, par_poison_loc_rd_port);

    QDYN_CFG(ptr, par_poison_loc_wr_port);

#ifndef MEMC_INLINE_ECC
    QDYN_CFG(ptr, par_poison_byte_num);
#endif /* !MEMC_INLINE_ECC */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + OCPARCFG1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + OCPARCFG1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_OCPAR_EN_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCPARCFG1(void)
{
};
#endif /* UMCTL2_OCPAR_EN_1 */

/**
 * @brief function to setup the register field values for deratectl5
 */
#ifdef DDRCTL_DDR_OR_MEMC_LPDDR4
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL5(uint32_t ch)
{
    SNPS_TRACE("Entering");
    DERATECTL5_t *const ptr[2] = {
        &REGB_DDRC_CH0.deratectl5,
        &REGB_DDRC_CH1.deratectl5
    };
    uint32_t tmp = ptr[ch]->value;

    STATIC_CFG_ARRAY(ptr, derate_temp_limit_intr_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DERATECTL5, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR_OR_MEMC_LPDDR4 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL5(uint32_t ch)
{
};
#endif /* DDRCTL_DDR_OR_MEMC_LPDDR4 */

/**
 * @brief function to setup the register field values for deratectl6
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL6(void)
{
    SNPS_TRACE("Entering");
    DERATECTL6_t *const ptr = &REGB_DDRC_CH0.deratectl6;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, derate_mr4_tuf_dis);

#ifdef DDRCTL_DDR
    QDYN_CFG(ptr, derate_low_temp_limit);

    QDYN_CFG(ptr, derate_high_temp_limit);

    QDYN_CFG(ptr, derate_temp_limit_intr_normal_en);
    QDYN_CFG(ptr, derate_temp_limit_intr_high_en);
    QDYN_CFG(ptr, derate_temp_limit_intr_low_en);
    QDYN_CFG(ptr, dis_mrr4_tcr_srx);
#endif /* DDRCTL_DDR */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DERATECTL6, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DERATECTL6, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for DERATECTL5
 */
#ifdef DDRCTL_DDR_OR_MEMC_LPDDR4
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATEDBGCTL(uint32_t ch)
{
	SNPS_TRACE("Entering");
	DERATEDBGCTL_t *const ptr[2] = {
		&REGB_DDRC_CH0.deratedbgctl,
		&REGB_DDRC_CH1.deratedbgctl
	};
	uint32_t tmp = ptr[ch]->value;
    if (IS_DDR5) {
	  STATIC_CFG_ARRAY(ptr, dbg_mr4_rank_sel, ch);
	  STATIC_CFG_ARRAY(ptr, dbg_mr4_grp_sel, ch);
    }
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value))
		dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DERATEDBGCTL, ptr[ch]->value);

	SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR_OR_MEMC_LPDDR4 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATEDBGCTL(uint32_t ch)
{
};
#endif /* DDRCTL_DDR_OR_MEMC_LPDDR4 */


/**
 * @brief function to setup the register field values for ZQCTL1
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ZQCTL1(uint32_t ch)
{
    SNPS_TRACE("Entering");
    ZQCTL1_t *const ptr[2] = {
        &REGB_DDRC_CH0.zqctl1,
        &REGB_DDRC_CH1.zqctl1
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, zq_reset, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ZQCTL1, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_LPDDR */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ZQCTL1(uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for dqsoscruntime
 */
#ifdef LPDDR45_DQSOSC_EN
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQSOSCRUNTIME(void)
{
    SNPS_TRACE("Entering");
    DQSOSCRUNTIME_t *const ptr = &REGB_DDRC_CH0.dqsoscruntime;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, dqsosc_runtime);
    CONSTRAIN_INSIDE(ptr->dqsosc_runtime, 1, 255); //Ranges from 16 to 8K DRAM clock cycles
#ifdef DDRCTL_LPDDR
    QDYN_CFG(ptr, wck2dqo_runtime);
    CONSTRAIN_INSIDE(ptr->wck2dqo_runtime, 1, 255); //Ranges from 16 to 8K DRAM clock cycles
#endif
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCRUNTIME, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* LPDDR45_DQSOSC_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQSOSCRUNTIME(void)
{
};
#endif /* LPDDR45_DQSOSC_EN */

/**
 * @brief function to setup the register field values for sched1
 */
#ifdef MEMC_ENH_CAM_PTR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED1(void)
{
    SNPS_TRACE("Entering");
    SCHED1_t *const ptr = &REGB_DDRC_CH0.sched1;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, opt_hit_gt_hpr);

    QDYN_CFG(ptr, page_hit_limit_rd);
    CONSTRAIN_MAX(ptr->page_hit_limit_rd, 4);

    QDYN_CFG(ptr, page_hit_limit_wr);
    CONSTRAIN_MAX(ptr->page_hit_limit_wr, 4);

#ifdef UMCTL2_VPR_EN
    QDYN_CFG(ptr, visible_window_limit_rd);
#ifdef MEMC_NO_OF_RD_ENTRY_GT64
    CONSTRAIN_MAX(ptr->visible_window_limit_rd, 5);
#else
    CONSTRAIN_MAX(ptr->visible_window_limit_rd, 4);
#endif /*MEMC_NO_OF_WR_ENTRY_GT64  */

    QDYN_CFG(ptr, visible_window_limit_wr);
#ifdef MEMC_NO_OF_WR_ENTRY_GT64
    CONSTRAIN_MAX(ptr->visible_window_limit_wr, 5);
#else
    CONSTRAIN_MAX(ptr->visible_window_limit_wr, 4);
#endif /*MEMC_NO_OF_WR_ENTRY_GT64  */
#endif /* UMCTL2_VPR_EN */

#ifdef MEMC_ENH_RDWR_SWITCH
    QDYN_CFG(ptr, delay_switch_write);
#endif /* MEMC_ENH_RDWR_SWITCH */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + SCHED1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + SCHED1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH

    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ENH_CAM_PTR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED1(void)
{
};
#endif /* MEMC_ENH_CAM_PTR */

/**
 * @brief function to setup the register field values for sched2
 */
#ifdef UMCTL2_DYN_BSM
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED2(void)
{
    SNPS_TRACE("Entering");
    SCHED2_t *const ptr = &REGB_DDRC_CH0.sched2;
    uint32_t tmp = ptr->value;
    uint32_t min_val;
    uint32_t l_max_cid, l_max_bgw, l_max_baw, l_bsm_num;

    // all active ranks use the device configuration 0
    if ((STATIC.active_ranks & STATIC.rank_dev_cfg_sel[0]) == 0) {
        l_max_cid = CID_WIDTH(0);
        l_max_bgw = DRAM_BGW(0);
        l_max_baw = DRAM_BAW(0);
    // all active ranks use the device configuration 1
    } else if (STATIC.active_ranks == STATIC.rank_dev_cfg_sel[0]) {
        l_max_cid = CID_WIDTH(DWC_DDRCTL_DEV_CFG_NUM - 1);
        l_max_bgw = DRAM_BGW(DWC_DDRCTL_DEV_CFG_NUM - 1);
        l_max_baw = DRAM_BAW(DWC_DDRCTL_DEV_CFG_NUM - 1);
    // bug 12819, use the bigger number of both two dev configuration are used
    } else {
        l_max_cid = max(CID_WIDTH(0), CID_WIDTH(DWC_DDRCTL_DEV_CFG_NUM - 1));
        l_max_bgw = max(DRAM_BGW(0), DRAM_BGW(DWC_DDRCTL_DEV_CFG_NUM - 1));
        l_max_baw = max(DRAM_BAW(0), DRAM_BAW(DWC_DDRCTL_DEV_CFG_NUM - 1));
    }

    //bug13206 - BG=4 / BA=2 is using the same mapping as BG=4 / BA=4
    if (l_max_bgw == 2 && l_max_baw == 1)
        l_max_baw = 2;

    l_bsm_num = (1 << l_max_cid) * (1 << l_max_bgw) * (1 << l_max_baw);
    // bug 12819, highest index of active rank specified by mstr0.active_ranks + 1
    if (STATIC.active_ranks == 0x5)
        l_bsm_num *= 3;
    else
        l_bsm_num *= SPD.num_ranks;

    // As of now dyn_bsm mode register is supported only in DDR54 configs where UMCTL2_DYN_BSM is set to 1
    // dyn bsm mode register can be enabled , if the NUM_BSM <= MEMC_NUM_BANKS. However
    // the BSM starvation does not happen when NUM_BSM == MEMC_NUM_BANKS
    // Here we are checking the Total Number of Banks should be greater than
    // UMCTL2_NUM_BSM supported. Only then dynamic BSM mode feature works.
    // The Number 32 indicates the Max number of Banks per logical rank in
    // DDR5 . In DDR4 the Max number of logical rank is 16.
    if (l_bsm_num > UMCTL2_NUM_BSM)
        STATIC.dyn_bsm_mode = 1;
    else
        STATIC.dyn_bsm_mode = 0;

    SNPS_LOG("dyn_bsm_mode = %u, l_bsm_num = %u, UMCTL2_NUM_BSM = %u, reg_active_ranks = %u, reg_rank_dev_cfg_sel = %u", STATIC.dyn_bsm_mode, l_bsm_num, UMCTL2_NUM_BSM, STATIC.active_ranks, STATIC.rank_dev_cfg_sel[0]);

    STATIC_CFG(ptr, dealloc_num_bsm_m1);

    STATIC_CFG(ptr, dealloc_bsm_thr);

    min_val = DIV_2(UMCTL2_NUM_BSM) + 1; //Minimum supported value is UMCTL2_NUM_BSM / 2 + 1
    CONSTRAIN_MIN(ptr->dealloc_bsm_thr, min_val);

    STATIC_CFG(ptr, dyn_bsm_mode);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + SCHED2, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + SCHED2, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_DYN_BSM */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED2(void)
{
};
#endif /* UMCTL2_DYN_BSM */

/**
 * @brief function to setup the register field values for sched3
 */
#ifdef MEMC_ENH_RDWR_SWITCH
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED3(void)
{
    SNPS_TRACE("Entering");
    SCHED3_t *const ptr = &REGB_DDRC_CH0.sched3;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, rd_pghit_num_thresh);
#ifndef MEMC_NO_OF_WR_ENTRY_GT256
    QDYN_CFG(ptr, wr_pghit_num_thresh);

    QDYN_CFG(ptr, wrcam_highthresh);

    QDYN_CFG(ptr, wrcam_lowthresh);

    CONSTRAIN_MIN(ptr->wrcam_lowthresh, ptr->wrcam_highthresh);
#endif

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + SCHED3, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + SCHED3, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ENH_RDWR_SWITCH */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED3(void)
{
};
#endif /* MEMC_ENH_RDWR_SWITCH */

/**
 * @brief function to setup the register field values for sched4
 */
#ifdef MEMC_ENH_RDWR_SWITCH
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED4(void)
{
    SNPS_TRACE("Entering");
    SCHED4_t *const ptr = &REGB_DDRC_CH0.sched4;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, wr_page_exp_cycles);

    QDYN_CFG(ptr, rd_page_exp_cycles);

    STATIC_CFG(ptr, wr_act_idle_gap);

    STATIC_CFG(ptr, rd_act_idle_gap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + SCHED4, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + SCHED4, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH

    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ENH_RDWR_SWITCH */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED4(void)
{
};
#endif /* MEMC_ENH_RDWR_SWITCH */

/**
 * @brief function to setup the register field values for sched5
 */
#if defined(MEMC_ENH_RDWR_SWITCH) && defined(MEMC_INLINE_ECC)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED5(void)
{
    SNPS_TRACE("Entering");
    SCHED5_t *const ptr = &REGB_DDRC_CH0.sched5;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, wrecc_cam_highthresh);
    CONSTRAIN_MAX(ptr->wrecc_cam_highthresh, ((1 << (MEMC_WRCMD_ENTRY_BITS - 1)) - 1));

    QDYN_CFG(ptr, wrecc_cam_lowthresh);
    CONSTRAIN_MIN(ptr->wrecc_cam_lowthresh, ptr->wrecc_cam_highthresh);

    QDYN_CFG(ptr, dis_opt_valid_wrecc_cam_fill_level);

    QDYN_CFG(ptr, dis_opt_loaded_wrecc_cam_fill_level);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + SCHED5, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + SCHED5, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_ENH_RDWR_SWITCH && MEMC_INLINE_ECC */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED5(void)
{
};
#endif /* MEMC_ENH_RDWR_SWITCH && MEMC_INLINE_ECC */

/**
 * @brief function to setup the register field values for sched6
 */
#if defined(MEMC_NO_OF_RD_ENTRY_GT128)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED6(void)
{
    SNPS_TRACE("Entering");
    SCHED6_t *const ptr = &REGB_DDRC_CH0.sched6;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, lpr_num_entries_extend);

    SNPS_TRACE("Leaving");
}
#else /* MEMC_NO_OF_RD_ENTRY_GT128 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED6(void)
{
};
#endif /* MEMC_NO_OF_RD_ENTRY_GT128 */

/**
 * @brief function to setup the register field values for sched7
 */
#if defined(MEMC_NO_OF_WR_ENTRY_GT256) 
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED7(void)
{
    SNPS_TRACE("Entering");
    SCHED7_t *const ptr = &REGB_DDRC_CH0.sched7;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, wr_pghit_num_thresh_extend);

    QDYN_CFG(ptr, wrcam_highthresh_extend);

    QDYN_CFG(ptr, wrcam_lowthresh_extend);

    CONSTRAIN_MIN(ptr->wrcam_lowthresh_extend, ptr->wrcam_highthresh_extend);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + SCHED7, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + SCHED7, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    SNPS_TRACE("Leaving");
}
#else /* MEMC_NO_OF_RD_ENTRY_GT128 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED7(void)
{
};
#endif /* MEMC_NO_OF_RD_ENTRY_GT128 */


/**
 * @brief function to setup the register field values for dfilpcfg0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFILPCFG0(void)
{
    SNPS_TRACE("Entering");
    DFILPCFG0_t *const ptr = &REGB_DDRC_CH0.dfilpcfg0;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dfi_lp_data_req_en);

	if (IS_DDR4 && ((PRE_CFG.dfi_tphy_wrlat[0][0]  < ((hdlr->phy_timing_params.dfi_tlp_resp + hdlr->phy_timing_params.dfi_tlp_data_wakeup)*2) + 6) ||
                   (PRE_CFG.dfi_t_rddata_en[0][0] < ((hdlr->phy_timing_params.dfi_tlp_resp + hdlr->phy_timing_params.dfi_tlp_data_wakeup)*2) + 6))) {
		STATIC.dfi_lp_en_data = 0;
   }

	STATIC_CFG(ptr, dfi_lp_en_data);

#ifdef DDRCTL_DDR
    STATIC_CFG(ptr, dfi_lp_en_mpsm);

	if (IS_DDR4){
      if (STATIC.dfi_lp_en_data == 0){
	      STATIC.dfi_lp_extra_gap = 0;
      } else {
	      STATIC.dfi_lp_extra_gap = hdlr->phy_timing_params.dfi_tlp_data_wakeup + 6/2 - 3;
      }
   } else {
	   STATIC.dfi_lp_extra_gap = 0;
   }
	STATIC_CFG(ptr, dfi_lp_extra_gap);
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
    STATIC_CFG(ptr, dfi_lp_en_dsm);

   if (STATIC.dfi_lp_en_data == 0){
	   STATIC.extra_gap_for_dfi_lp_data = 0;
   } else {
	   STATIC.extra_gap_for_dfi_lp_data = hdlr->phy_timing_params.dfi_tlp_resp + hdlr->phy_timing_params.dfi_tlp_data_wakeup - 4;
   }
    STATIC_CFG(ptr, extra_gap_for_dfi_lp_data);
#endif /* DDRCTL_LPDDR */

    STATIC_CFG(ptr, dfi_lp_en_sr);

    STATIC_CFG(ptr, dfi_lp_en_pd);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFILPCFG0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DFILPCFG0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for dfiupd1
 */
#ifdef UMCTL2_DFI_PHYUPD_WAIT_IDLE
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIUPD1(void)
{
    SNPS_TRACE("Entering");
    DFIUPD1_t *const ptr = &REGB_DDRC_CH0.dfiupd1;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dfi_phyupd_type3_wait_idle);

    STATIC_CFG(ptr, dfi_phyupd_type2_wait_idle);

    STATIC_CFG(ptr, dfi_phyupd_type1_wait_idle);

    STATIC_CFG(ptr, dfi_phyupd_type0_wait_idle);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFIUPD1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DFIUPD1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_DFI_PHYUPD_WAIT_IDLE */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIUPD1(void)
{
};
#endif /* UMCTL2_DFI_PHYUPD_WAIT_IDLE */

/**
 * @brief function to setup the register field values for DFISBPOISONCFG
 */

#ifdef DDRCTL_DFI_SB_WDT
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFISBPOISONCFG(void)
{
    SNPS_TRACE("Entering");
    DFISBPOISONCFG_t *const ptr = &REGB_DDRC_CH0.dfisbpoisoncfg;
    uint32_t tmp = ptr->value;

    ptr->dfi_tlp_data_resp_poison_margin = hdlr->phy_timing_params.dfi_tlp_resp - 1;
    ptr->dfi_tlp_ctrl_resp_poison_margin = hdlr->phy_timing_params.dfi_tlp_resp - 1;
    ptr->dfi_tinit_start_poison_margin   = QDYN.dfi_t_init_start[0][0] - 1;
    ptr->dfi_tctrlupd_min_poison_margin  = hdlr->phy_timing_params.dfi_t_ctrlup_min - 1;
    /*
    QDYN_CFG(ptr, dfi_tlp_data_resp_poison_margin);
    QDYN_CFG(ptr, dfi_tlp_ctrl_resp_poison_margin);
    QDYN_CFG(ptr, dfi_tinit_start_poison_margin);
    QDYN_CFG(ptr, dfi_tctrlupd_min_poison_margin);
    */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DFISBPOISONCFG, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DFISBPOISONCFG, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }
    SNPS_TRACE("Leaving");
};
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFISBPOISONCFG(void)
{
};
#endif /* DDRCTL_DFI_SB_WDT */


/**
 * @brief function to setup the register field values for DFISBINTRPTCFG
 */

#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFISBINTRPTCFG(uint32_t ch)
{
#ifdef DDRCTL_DFI_SB_WDT
    SNPS_TRACE("Entering");
    DFISBINTRPTCFG_t *const ptr[2] = {
        &REGB_DDRC_CH0.dfisbintrptcfg,
        &REGB_DDRC_CH1.dfisbintrptcfg
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, dfi_sideband_timer_err_intr_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFISBINTRPTCFG, ptr[ch]->value);
    }
    SNPS_TRACE("Leaving");
#endif /* DDRCTL_DFI_SB_WDT */
};
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFISBINTRPTCFG(uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */


/**
 * @brief function to setup the register field values for DFIERRINTRPTCFG
 */

#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIERRINTRPTCFG(uint32_t ch)
{
#ifdef DDRCTL_DFI_ERROR
    SNPS_TRACE("Entering");
    DFIERRINTRPTCFG_t *const ptr[22] = {
       &REGB_DDRC_CH0.dfierrintrptcfg,
       &REGB_DDRC_CH1.dfierrintrptcfg
    };
    uint32_t tmp = ptr[ch]->value;
    DYN_CFG_ARRAY(ptr, dfi_error_intr_en,ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DFIERRINTRPTCFG, ptr[ch]->value);
    }
    SNPS_TRACE("Leaving");
#endif /* DDRCTL_DFI_ERROR */
};
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIERRINTRPTCFG(uint32_t ch)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for crcparctl0
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPARCTL0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    CRCPARCTL0_t *const ptr[2] = {
        &REGB_DDRC_CH0.crcparctl0,
        &REGB_DDRC_CH1.crcparctl0
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_CAPAR_RETRY
    DYN_CFG_ARRAY(ptr, capar_fatl_err_intr_force, ch);

    DYN_CFG_ARRAY(ptr, capar_fatl_err_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, capar_fatl_err_intr_en, ch);
#endif /* DDRCTL_CAPAR_RETRY */

    DYN_CFG_ARRAY(ptr, rd_crc_err_cnt_clr, ch);

    DYN_CFG_ARRAY(ptr, rd_crc_err_max_reached_int_clr, ch);

    DYN_CFG_ARRAY(ptr, rd_crc_err_max_reached_int_en, ch);

    DYN_CFG_ARRAY(ptr, wr_crc_err_cnt_clr, ch);

    DYN_CFG_ARRAY(ptr, wr_crc_err_max_reached_intr_force, ch);

    DYN_CFG_ARRAY(ptr, wr_crc_err_max_reached_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, wr_crc_err_max_reached_intr_en, ch);

    DYN_CFG_ARRAY(ptr, wr_crc_err_intr_force, ch);

    DYN_CFG_ARRAY(ptr, wr_crc_err_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, wr_crc_err_intr_en, ch);

    DYN_CFG_ARRAY(ptr, capar_err_cnt_clr, ch);

    DYN_CFG_ARRAY(ptr, capar_err_max_reached_intr_force, ch);

    DYN_CFG_ARRAY(ptr, capar_err_max_reached_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, capar_err_max_reached_intr_en, ch);

    DYN_CFG_ARRAY(ptr, capar_err_intr_force, ch);

    DYN_CFG_ARRAY(ptr, capar_err_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, capar_err_intr_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + CRCPARCTL0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPARCTL0(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for crcparctl1
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPARCTL1(void)
{
    SNPS_TRACE("Entering");
    CRCPARCTL1_t *const ptr = &REGB_DDRC_CH0.crcparctl1;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, capar_err_max_reached_th);

    STATIC_CFG(ptr, dfi_alert_async_mode);

    STATIC_CFG(ptr, caparity_disable_before_sr);

    STATIC_CFG(ptr, crc_inc_dm);

    QDYN_CFG(ptr, wr_crc_enable);

    QDYN_CFG(ptr, rd_crc_enable);

    QDYN_CFG(ptr, dis_rd_crc_ecc_upr_nibble);

    STATIC_CFG(ptr, bypass_internal_crc);

    STATIC_CFG(ptr, parity_enable);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + CRCPARCTL1, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + CRCPARCTL1, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH

    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPARCTL1(void)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for crcparctl2
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPARCTL2(void)
{
    SNPS_TRACE("Entering");
    CRCPARCTL2_t *const ptr = &REGB_DDRC_CH0.crcparctl2;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, rd_crc_err_max_reached_th);
    CONSTRAIN_NE(ptr->rd_crc_err_max_reached_th, 0);    //0 is an illegal setting for this register

    QDYN_CFG(ptr, wr_crc_err_max_reached_th);
    CONSTRAIN_NE(ptr->wr_crc_err_max_reached_th, 0);    //0 is an illegal setting for this register

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + CRCPARCTL2, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + CRCPARCTL2, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH

    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPARCTL2(void)
{
};
#endif /* DDRCTL_DDR */

#if defined(DDRCTL_DDR) && defined(DDRCTL_ANY_RETRY)
void dwc_ddrctl_cinit_prgm_REGB_DDRC_RETRYCTL0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    RETRYCTL0_t *const ptr[2] = {
        &REGB_DDRC_CH0.retryctl0,
        &REGB_DDRC_CH1.retryctl0
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_WR_CRC_RETRY
    DYN_CFG_ARRAY(ptr, wr_crc_retry_limit_intr_force, ch);

    DYN_CFG_ARRAY(ptr, wr_crc_retry_limit_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, wr_crc_retry_limit_intr_en, ch);

    STATIC_CFG_ARRAY(ptr, wr_crc_retry_limiter, ch);

    STATIC_CFG_ARRAY(ptr, wr_crc_retry_enable, ch);
#endif /* DDRCTL_WR_CRC_RETRY */

#ifdef DDRCTL_RD_CRC_RETRY
    DYN_CFG_ARRAY(ptr, rd_retry_limit_intr_force, ch);

    DYN_CFG_ARRAY(ptr, rd_retry_limit_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, rd_retry_limit_intr_en, ch);

    STATIC_CFG_ARRAY(ptr, rd_crc_retry_limiter, ch);

    STATIC_CFG_ARRAY(ptr, rd_crc_retry_enable, ch);
#endif /* DDRCTL_RD_CRC_RETRY */

#ifdef DDRCTL_CAPAR_RETRY
    DYN_CFG_ARRAY(ptr, capar_retry_limit_intr_force, ch);
    DYN_CFG_ARRAY(ptr, capar_retry_limit_intr_clr, ch);
    DYN_CFG_ARRAY(ptr, capar_retry_limit_intr_en, ch);
    STATIC_CFG_ARRAY(ptr, capar_retry_limiter, ch);

    STATIC_CFG_ARRAY(ptr, capar_retry_enable, ch);
#endif /* DDRCTL_CAPAR_RETRY */

#ifdef DDRCTL_RD_UE_RETRY
    STATIC_CFG_ARRAY(ptr, rd_ue_retry_limiter, ch);

    STATIC_CFG_ARRAY(ptr, rd_ue_retry_enable, ch);
#endif /* DDRCTL_RD_UE_RETRY */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + RETRYCTL0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_ANY_RETRY */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_RETRYCTL0(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_ANY_RETRY */

/**
 * @brief function to setup the register field values for crcpoisonctl0
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPOISONCTL0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    CRCPOISONCTL0_t *const ptr[2] = {
        &REGB_DDRC_CH0.crcpoisonctl0,
        &REGB_DDRC_CH1.crcpoisonctl0
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, crc_poison_times, ch);

    DYN_CFG_ARRAY(ptr, crc_poison_nibble, ch);

    DYN_CFG_ARRAY(ptr, crc_poison_type, ch);

    DYN_CFG_ARRAY(ptr, crc_poison_inject_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + CRCPOISONCTL0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPOISONCTL0(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for caparpoisonctl
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_CA_PARITY)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CAPARPOISONCTL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    CAPARPOISONCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.caparpoisonctl,
        &REGB_DDRC_CH1.caparpoisonctl
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, capar_poison_cmdtype, ch);

    DYN_CFG_ARRAY(ptr, capar_poison_inject_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + CAPARPOISONCTL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_CA_PARITY */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CAPARPOISONCTL(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_CA_PARITY */

/**
 * @brief function to setup the register field values for lnkeccctl1
 */
#ifdef MEMC_LINK_ECC
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_LNKECCCTL1(uint32_t ch)
{
    SNPS_TRACE("Entering");
    LNKECCCTL1_t *const ptr[2] = {
        &REGB_DDRC_CH0.lnkeccctl1,
        &REGB_DDRC_CH1.lnkeccctl1
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, rd_link_ecc_uncorr_cnt_clr, ch);

    DYN_CFG_ARRAY(ptr, rd_link_ecc_uncorr_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, rd_link_ecc_uncorr_intr_en, ch);

    DYN_CFG_ARRAY(ptr, rd_link_ecc_corr_cnt_clr, ch);

    DYN_CFG_ARRAY(ptr, rd_link_ecc_corr_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, rd_link_ecc_corr_intr_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + LNKECCCTL1, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_LINK_ECC */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_LNKECCCTL1(uint32_t ch)
{
};
#endif /* MEMC_LINK_ECC */

/**
 * @brief function to setup the register field values for lnkeccpoisonctl0
 */
#ifdef MEMC_LINK_ECC
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_LNKECCPOISONCTL0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    LNKECCPOISONCTL0_t *const ptr[2] = {
        &REGB_DDRC_CH0.lnkeccpoisonctl0,
        &REGB_DDRC_CH1.lnkeccpoisonctl0
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, linkecc_poison_byte_sel, ch);

    DYN_CFG_ARRAY(ptr, linkecc_poison_dmi_sel, ch);

    DYN_CFG_ARRAY(ptr, linkecc_poison_rw, ch);

    DYN_CFG_ARRAY(ptr, linkecc_poison_type, ch);

    DYN_CFG_ARRAY(ptr, linkecc_poison_inject_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + LNKECCPOISONCTL0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* MEMC_LINK_ECC */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_LNKECCPOISONCTL0(uint32_t ch)
{
};
#endif /* MEMC_LINK_ECC */

/**
 * @brief function to setup the register field values for lnkeccindex
 */
#ifdef MEMC_LINK_ECC
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_LNKECCINDEX(uint32_t ch)
{
    SNPS_TRACE("Entering");
    LNKECCINDEX_t *const ptr[2] = {
        &REGB_DDRC_CH0.lnkeccindex,
        &REGB_DDRC_CH1.lnkeccindex
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef MEMC_NUM_RANKS_GT_1
    QDYN_CFG_ARRAY(ptr, rd_link_ecc_err_rank_sel, ch);
#endif /* MEMC_NUM_RANKS_GT_1 */

    QDYN_CFG_ARRAY(ptr, rd_link_ecc_err_byte_sel, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + LNKECCINDEX, ptr[ch]->value);
    }
    SNPS_TRACE("Leaving");
}
#else /* MEMC_LINK_ECC */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_LNKECCINDEX(uint32_t ch)
{
};
#endif /* MEMC_LINK_ECC */

/**
 * @brief function to setup the register field values for pasctl0
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL0_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl0,
        &REGB_DDRC_CH1.pasctl0
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_ARRAY(ptr, bist_st_en, ch);

    QDYN_CFG_ARRAY(ptr, dbg_st_en, ch);

    QDYN_CFG_ARRAY(ptr, init_done, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL0(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl2
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL2(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL2_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl2,
        &REGB_DDRC_CH1.pasctl2
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef CINIT_DDR5
	if (IS_DDR5) {
	// DDR5CTL with high speedbin has t_ppd > 2,  t_ppd_cnt_en shall be set to 1
#ifdef DDRCTL_DDR5CTL
		if(CFG->timingParams_m[0][0].ddr5_tppd_tck > 2) {
			ptr[ch]->t_ppd_cnt_en = 1;
		} else {
			ptr[ch]->t_ppd_cnt_en  = 0;
		}
#else 
		// FOr 2N mode in non-DDR5CTL,  reg_t_ppd_cnt_en shall be set to 0
		if(CFG->memCtrlr_m.ddr5_mr[0].mr2.ddr5_2n_mode == 1) {
			ptr[ch]->t_ppd_cnt_en = 1;
		} else {
			ptr[ch]->t_ppd_cnt_en = 0;
		}
#endif
	}
#endif

#ifdef UMCTL2_CID_EN
    DYN.lrank_rd2rd_gap[ch] = PRE_CFG.lrank_rd2rd_gap[ch];
    DYN.lrank_wr2wr_gap[ch] = PRE_CFG.lrank_wr2wr_gap[ch];
    DYN_CFG_ARRAY(ptr, lrank_wr2wr_gap, ch);
    DYN_CFG_ARRAY(ptr, lrank_rd2rd_gap, ch);
#endif

    DYN_CFG_ARRAY(ptr, refsb_hi_wait_thr, ch);

    DYN_CFG_ARRAY(ptr, dyn_pre_pri_lo_wait_thr, ch);

    DYN_CFG_ARRAY(ptr, dyn_pre_pri_hi_win_size, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL2, ptr[ch]->value);
    }
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL2(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl4
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL4(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL4_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl4,
        &REGB_DDRC_CH1.pasctl4
    };
    uint32_t tmp = ptr[ch]->value;

	STATIC.ci_mrr_des1[ch] = PRE_CFG.ci_mrr_des1[ch];
	STATIC.ci_mrr_des2[ch] = PRE_CFG.ci_mrr_des2[ch];
	STATIC_CFG_ARRAY(ptr, ci_mrr_des1, ch);
	STATIC_CFG_ARRAY(ptr, ci_mrr_des2, ch);

	STATIC_CFG_ARRAY(ptr, ci_mrw_des1, ch);
	STATIC_CFG_ARRAY(ptr, ci_mrw_des2, ch);

	STATIC_CFG_ARRAY(ptr, ci_mpc_des1, ch);
	STATIC_CFG_ARRAY(ptr, ci_mpc_des2, ch);

#ifdef DDRCTL_SW_RFM_CTRL
    STATIC_CFG_ARRAY(ptr, ci_rfm_des1, ch);

    STATIC_CFG_ARRAY(ptr, ci_rfm_des2, ch);
#endif // DDRCTL_SW_RFM_CTRL
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL4, ptr[ch]->value);
    }
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL4(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for cmdcfg
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CMDCFG(uint32_t ch)
{
    SNPS_TRACE("Entering");
    CMDCFG_t *const ptr[2] = {
        &REGB_DDRC_CH0.cmdcfg,
        &REGB_DDRC_CH1.cmdcfg
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_ARRAY(ptr, ctrlupd_retry_thr, ch);

    DYN_CFG_ARRAY(ptr, mrr_grp_sel, ch);

    STATIC_CFG_ARRAY(ptr, cmd_timer_x32, ch);

    STATIC_CFG_ARRAY(ptr, pde_odt_ctrl, ch);

    STATIC_CFG_ARRAY(ptr, pd_mrr_nt_odt_en, ch);

    DYN_CFG_ARRAY(ptr, multi_cyc_cs_en, ch);

    DYN_CFG_ARRAY(ptr, cmd_type, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + CMDCFG, ptr[ch]->value);
    }
    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CMDCFG(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for cmdctl
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CMDCTL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    CMDCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.cmdctl,
        &REGB_DDRC_CH1.cmdctl
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, cmd_start, ch);

    DYN_CFG_ARRAY(ptr, cmd_seq_last, ch);

    DYN_CFG_ARRAY(ptr, cmd_code, ch);

    DYN_CFG_ARRAY(ptr, cmd_ctrl, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + CMDCTL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CMDCTL(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for cmdextctl
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CMDEXTCTL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    CMDEXTCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.cmdextctl,
        &REGB_DDRC_CH1.cmdextctl
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, cmd_ext_ctrl, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + CMDEXTCTL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CMDEXTCTL(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for SWCTL
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SWCTL(void)
{
    SNPS_TRACE("Entering");
    SWCTL_t *const ptr = &REGB_DDRC_CH0.swctl;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, sw_done);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + SWCTL, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + SWCTL, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for swctlstatic
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_SWCTLSTATIC(void)
{
    SNPS_TRACE("Entering");
    SWCTLSTATIC_t *const ptr = &REGB_DDRC_CH0.swctlstatic;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, sw_static_unlock);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + SWCTLSTATIC, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + SWCTLSTATIC, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for chctl
 */
#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_CHCTL(void)
{
    SNPS_TRACE("Entering");
    CHCTL_t *const ptr = &REGB_DDRC_CH0.chctl;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dual_channel_en);
    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + CHCTL, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + CHCTL, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH*/
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_CHCTL(void)
{
};
#endif /* DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH*/

/**
 * @brief function to setup the register field values for odtmap
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ODTMAP(uint32_t ch)
{
#ifdef DDRCTL_DDR
    SNPS_TRACE("Entering");
    ODTMAP_t *const ptr[2] = {
        &REGB_DDRC_CH0.odtmap,
        &REGB_DDRC_CH1.odtmap
    };
    uint32_t tmp = ptr[ch]->value;
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        STATIC_CFG_ARRAY(ptr, rank0_wr_odt, ch);

        STATIC_CFG_ARRAY(ptr, rank0_rd_odt, ch);

#ifdef MEMC_NUM_RANKS_GT_1
        STATIC_CFG_ARRAY(ptr, rank1_wr_odt, ch);

        STATIC_CFG_ARRAY(ptr, rank1_rd_odt, ch);
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef MEMC_NUM_RANKS_GT_2
        STATIC_CFG_ARRAY(ptr, rank2_wr_odt, ch);

        STATIC_CFG_ARRAY(ptr, rank2_rd_odt, ch);

        STATIC_CFG_ARRAY(ptr, rank3_wr_odt, ch);

        STATIC_CFG_ARRAY(ptr, rank3_rd_odt, ch);
#endif /* MEMC_NUM_RANKS_GT_2 */
    }
#endif

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ODTMAP, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
#endif /* DDRCTL_DDR */
}


/**
 * @brief function to setup the register field values for dqsosccfg0
 */
#ifdef LPDDR54_DQOSC_EN_OR_MEMC_DDR5
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQSOSCCFG0(void)
{
    SNPS_TRACE("Entering");
    DQSOSCCFG0_t *const ptr = &REGB_DDRC_CH0.dqsosccfg0;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, dis_dqsosc_srx);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCCFG0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DQSOSCCFG0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* LPDDR54_DQOSC_EN_OR_MEMC_DDR5 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQSOSCCFG0(void)
{
};
#endif /* LPDDR54_DQOSC_EN_OR_MEMC_DDR5 */

/**
 * @brief function to setup the register field values for dqsosctmg0
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQSOSCTMG0(void)
{
    SNPS_TRACE("Entering");
    DQSOSCTMG0_t *const ptr = &REGB_DDRC_CH0.dqsosctmg0;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, t_oscs);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQSOSCTMG0, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + DQSOSCTMG0, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH

    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQSOSCTMG0(void)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl5
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL5(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL5_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl5,
        &REGB_DDRC_CH1.pasctl5
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, base_timer_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL5, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL5(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl6
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL6(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL6_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl6,
        &REGB_DDRC_CH1.pasctl6
    };
    uint32_t tmp = ptr[ch]->value;
    uint32_t ratio;

    // based on TCK and interval requirement calculate base_timer value
    // the timer is based on dfi clk cycles
    ratio = ddrctl_sw_get_ratio_factor(CFG, 0);
    QDYN.base_timer[ch] = CEIL((hdlr->ddr5_pasdu_en.base_timer_interval_us[ch] * 1000000), ratio * SPD.tck_ps[0]);

    QDYN_CFG_ARRAY(ptr, base_timer, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL6, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL6(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl7
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL7(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL7_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl7,
        &REGB_DDRC_CH1.pasctl7
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, glb_blk0_en, ch);

    DYN_CFG_ARRAY(ptr, glb_blk1_en, ch);

    DYN_CFG_ARRAY(ptr, glb_blk2_en, ch);

    DYN_CFG_ARRAY(ptr, glb_blk3_en, ch);

    DYN_CFG_ARRAY(ptr, glb_blk4_en, ch);

    DYN_CFG_ARRAY(ptr, glb_blk5_en, ch);

    DYN_CFG_ARRAY(ptr, glb_blk6_en, ch);

    DYN_CFG_ARRAY(ptr, glb_blk7_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL7, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL7(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl8
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL8(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL8_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl8,
        &REGB_DDRC_CH1.pasctl8
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, rank_blk0_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk1_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk2_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk3_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk4_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk5_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk6_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk7_en, ch);

#ifdef MEMC_NUM_RANKS_GT_1
    DYN_CFG_ARRAY(ptr, rank_blk8_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk9_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk10_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk11_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk12_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk13_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk14_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk15_en, ch);
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef MEMC_NUM_RANKS_GT_2
    DYN_CFG_ARRAY(ptr, rank_blk16_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk17_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk18_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk19_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk20_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk21_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk22_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk23_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk24_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk25_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk26_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk27_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk28_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk29_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk30_en, ch);

    DYN_CFG_ARRAY(ptr, rank_blk31_en, ch);
#endif /* MEMC_NUM_RANKS_GT_2 */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL8, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL8(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl9
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL9(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL9_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl9,
        &REGB_DDRC_CH1.pasctl9
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, glb_blk0_trig, ch);

    DYN_CFG_ARRAY(ptr, glb_blk1_trig, ch);

    DYN_CFG_ARRAY(ptr, glb_blk2_trig, ch);

    DYN_CFG_ARRAY(ptr, glb_blk3_trig, ch);

    DYN_CFG_ARRAY(ptr, glb_blk4_trig, ch);

    DYN_CFG_ARRAY(ptr, glb_blk5_trig, ch);

    DYN_CFG_ARRAY(ptr, glb_blk6_trig, ch);

    DYN_CFG_ARRAY(ptr, glb_blk7_trig, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL9, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL9(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl10
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL10(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL10_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl10,
        &REGB_DDRC_CH1.pasctl10
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, rank_blk0_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk1_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk2_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk3_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk4_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk5_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk6_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk7_trig, ch);

#ifdef MEMC_NUM_RANKS_GT_1
    DYN_CFG_ARRAY(ptr, rank_blk8_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk9_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk10_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk11_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk12_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk13_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk14_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk15_trig, ch);
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef MEMC_NUM_RANKS_GT_2
    DYN_CFG_ARRAY(ptr, rank_blk16_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk17_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk18_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk19_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk20_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk21_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk22_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk23_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk24_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk25_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk26_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk27_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk28_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk29_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk30_trig, ch);

    DYN_CFG_ARRAY(ptr, rank_blk31_trig, ch);
#endif /* MEMC_NUM_RANKS_GT_2 */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL10, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL10(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl11
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL11(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL11_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl11,
        &REGB_DDRC_CH1.pasctl11
    };
    uint32_t tmp = ptr[ch]->value;

    ptr[ch]->powerdown_entry_ba_0 = 0x0;
    ptr[ch]->powerdown_entry_size_0 = 0x5;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL11, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL11(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl12
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL12(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL12_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl12,
        &REGB_DDRC_CH1.pasctl12
    };
    uint32_t tmp = ptr[ch]->value;

	ptr[ch]->powerdown_exit_ba_0 = 0x8;
	ptr[ch]->powerdown_exit_size_0 = 0x7;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL12, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL12(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl13
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_1) && defined(DDRCTL_PERRANK_LP)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL13(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL13_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl13,
        &REGB_DDRC_CH1.pasctl13
    };
    uint32_t tmp = ptr[ch]->value;

    ptr[ch]->powerdown_entry_ba_1 = 0x10;
    ptr[ch]->powerdown_entry_size_1 = 0x5;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL13, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_1 && DDRCTL_PERRANK_LP */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL13(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_1 && DDRCTL_PERRANK_LP */

/**
 * @brief function to setup the register field values for pasctl14
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_1) && defined(DDRCTL_PERRANK_LP)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL14(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL14_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl14,
        &REGB_DDRC_CH1.pasctl14
    };
    uint32_t tmp = ptr[ch]->value;

	ptr[ch]->powerdown_exit_ba_1 = 0x18;
	ptr[ch]->powerdown_exit_size_1 = 0x7;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL14, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_1 && DDRCTL_PERRANK_LP */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL14(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_1 && DDRCTL_PERRANK_LP */

/**
 * @brief function to setup the register field values for pasctl15
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_2) && defined(DDRCTL_PERRANK_LP)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL15(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL15_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl15,
        &REGB_DDRC_CH1.pasctl15
    };
    uint32_t tmp = ptr[ch]->value;

    ptr[ch]->powerdown_entry_ba_2 = 0x20;
    ptr[ch]->powerdown_entry_size_2 = 0x5;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL15, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 && DDRCTL_PERRANK_LP */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL15(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 && DDRCTL_PERRANK_LP */

/**
 * @brief function to setup the register field values for pasctl16
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_2) && defined(DDRCTL_PERRANK_LP)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL16(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL16_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl16,
        &REGB_DDRC_CH1.pasctl16
    };
    uint32_t tmp = ptr[ch]->value;

	ptr[ch]->powerdown_exit_ba_2 = 0x28;
	ptr[ch]->powerdown_exit_size_2 = 0x7;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL16, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 && DDRCTL_PERRANK_LP */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL16(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 && DDRCTL_PERRANK_LP */

/**
 * @brief function to setup the register field values for pasctl17
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_2) && defined(DDRCTL_PERRANK_LP)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL17(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL17_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl17,
        &REGB_DDRC_CH1.pasctl17
    };
    uint32_t tmp = ptr[ch]->value;

    ptr[ch]->powerdown_entry_ba_3 = 0x30;
    ptr[ch]->powerdown_entry_size_3 = 0x5;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL17, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 && DDRCTL_PERRANK_LP */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL17(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 && DDRCTL_PERRANK_LP */

/**
 * @brief function to setup the register field values for pasctl18
 */
#if defined(DDRCTL_DDR) && defined(MEMC_NUM_RANKS_GT_2) && defined(DDRCTL_PERRANK_LP)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL18(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL18_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl18,
        &REGB_DDRC_CH1.pasctl18
    };
    uint32_t tmp = ptr[ch]->value;

	ptr[ch]->powerdown_exit_ba_3 = 0x38;
	ptr[ch]->powerdown_exit_size_3 = 0x7;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL18, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 && DDRCTL_PERRANK_LP */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL18(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && MEMC_NUM_RANKS_GT_2 && DDRCTL_PERRANK_LP */

/**
 * @brief function to setup the register field values for pasctl20
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL20(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL20_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl20,
        &REGB_DDRC_CH1.pasctl20
    };
    uint32_t tmp = ptr[ch]->value;

    ptr[ch]->selfref_entry1_size_0 = 0x0d;
    ptr[ch]->selfref_entry1_ba_0 = 0x40;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL20, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL20(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl21
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL21(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL21_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl21,
        &REGB_DDRC_CH1.pasctl21
    };
    uint32_t tmp = ptr[ch]->value;

	if (IS_RDIMM || IS_LRDIMM) {
		if (ch == 0)
			ptr[ch]->selfref_entry2_size_0 = DDRCTL_PASCTL21_SELFREF_ENTRY2_SIZE_0_DIMM_CH0_DEFAULT;
		else
			ptr[ch]->selfref_entry2_size_0 = DDRCTL_PASCTL21_SELFREF_ENTRY2_SIZE_0_DIMM_CH1_DEFAULT;
	} else {
		ptr[ch]->selfref_entry2_size_0 = DDRCTL_PASCTL21_SELFREF_ENTRY2_SIZE_0_NODIMM_DEFAULT;
	}
	ptr[ch]->selfref_entry2_ba_0 = DDRCTL_PASCTL21_SELFREF_ENTRY2_BA_0_DEFAULT;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL21, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL21(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl22
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL22(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL22_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl22,
        &REGB_DDRC_CH1.pasctl22
    };
    uint32_t tmp = ptr[ch]->value;

	if (IS_RDIMM || IS_LRDIMM) {
		if (ch == 0) {
			ptr[ch]->selfref_exit1_size_0 = DDRCTL_PASCTL22_SELFREF_EXIT1_SIZE_0_DIMM_CH0_DEFAULT;
			ptr[ch]->selfref_exit1_ba_0 = DDRCTL_PASCTL22_SELFREF_EXIT1_BA_0_DIMM_CH0_DEFAULT;
		} else {
			ptr[ch]->selfref_exit1_size_0 = DDRCTL_PASCTL22_SELFREF_EXIT1_SIZE_0_DIMM_CH1_DEFAULT;
			ptr[ch]->selfref_exit1_ba_0 = DDRCTL_PASCTL22_SELFREF_EXIT1_BA_0_DIMM_CH1_DEFAULT;
		}
	} else {
		ptr[ch]->selfref_exit1_size_0 = DDRCTL_PASCTL22_SELFREF_EXIT1_SIZE_0_NODIMM_DEFAULT;
		ptr[ch]->selfref_exit1_ba_0 = DDRCTL_PASCTL22_SELFREF_EXIT1_BA_0_NODIMM_DEFAULT;
	}

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL22, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL22(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl23
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL23(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL23_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl23,
        &REGB_DDRC_CH1.pasctl23
    };
    uint32_t tmp = ptr[ch]->value;

	if (IS_RDIMM || IS_LRDIMM) {
		if (ch == 0)
			ptr[ch]->selfref_exit2_ba_0 = DDRCTL_PASCTL23_SELFREF_EXIT2_BA_0_DIMM_CH0_DEFAULT;
		else
			ptr[ch]->selfref_exit2_ba_0 = DDRCTL_PASCTL23_SELFREF_EXIT2_BA_0_DIMM_CH1_DEFAULT;
	} else {
		ptr[ch]->selfref_exit2_ba_0 = DDRCTL_PASCTL23_SELFREF_EXIT2_BA_0_NODIMM_DEFAULT;
	}
	ptr[ch]->selfref_exit2_size_0 = 0x00;

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL23, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL23(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for pasctl24
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_HW_RFM_CTRL)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL24(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL24_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl24,
        &REGB_DDRC_CH1.pasctl24
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_ARRAY(ptr, rfm_raa_en, ch);

    QDYN_CFG_ARRAY(ptr, rfm_raa_reset, ch);

    QDYN_CFG_ARRAY(ptr, rfm_alert_thr, ch);

    STATIC_CFG_ARRAY(ptr, rfm_raa_use_ecs_refab, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL24, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_HW_RFM_CTRL */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL24(uint32_t ch)
{
};
#endif /* DDRCTL_HW_RFM_CTRL */

/**
 * @brief function to setup the register field values for pasctl36
 */
#if defined(DDRCTL_DDR) && defined(DDRCTL_PERRANK_LP)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL36(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL36_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl36,
        &REGB_DDRC_CH1.pasctl36
    };
    uint32_t tmp = ptr[ch]->value;

    STATIC_CFG_ARRAY(ptr, powerdown_idle_ctrl_0, ch);

    STATIC_CFG_ARRAY(ptr, powerdown_idle_ctrl_1, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL36, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_PERRANK_LP */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL36(uint32_t ch)
{
};
#endif /* DDRCTL_DDR && DDRCTL_PERRANK_LP */

/**
 * @brief function to setup the register field values for pasctl38
 */
#ifdef DDRCTL_DDR_BWL_EN
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL38(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASCTL38_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasctl38,
        &REGB_DDRC_CH1.pasctl38
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, bwl_en, ch);

    DYN_CFG_ARRAY(ptr, bwl_ctrl, ch);

    DYN_CFG_ARRAY(ptr, bwl_en_len, ch);

    DYN_CFG_ARRAY(ptr, bwl_win_len, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASCTL38, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR_BWL_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL38(uint32_t ch)
{
};
#endif /* DDRCTL_DDR_BWL_EN */

/**
 * @brief function to setup the register field values for pasintctl
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASINTCTL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    PASINTCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.pasintctl,
        &REGB_DDRC_CH1.pasintctl
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef DDRCTL_HW_RFM_CTRL
    DYN_CFG_ARRAY(ptr, rfm_alert_intr_en, ch);
#endif /* DDRCTL_HW_RFM_CTRL */

    DYN_CFG_ARRAY(ptr, ctrlupd_err_intr_en, ch);

    DYN_CFG_ARRAY(ptr, lccmd_err_intr_en, ch);

    DYN_CFG_ARRAY(ptr, ducmd_err_intr_en, ch);

    DYN_CFG_ARRAY(ptr, swcmd_err_intr_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + PASINTCTL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASINTCTL(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for ecsctl
 */
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECSCTL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    ECSCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.ecsctl,
        &REGB_DDRC_CH1.ecsctl
    };
    uint32_t tmp = ptr[ch]->value;

    QDYN_CFG_ARRAY(ptr, auto_ecs_refab_en, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ECSCTL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECSCTL(uint32_t ch)
{
};
#endif /* DDRCTL_DDR */

/**
 * @brief function to setup the register field values for DU_CMDBUF_CTRL
 */
// Commented out, currently not used
#if 0
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DU_CMDBUF_CTRL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    DU_CMDBUF_CTRL_t *const ptr[2] = {
        &REGB_DDRC_CH0.DU_CMDBUF_CTRL,
        &REGB_DDRC_CH1.DU_CMDBUF_CTRL
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, du_cmdbuf_rw_start, ch);

    DYN_CFG_ARRAY(ptr, du_cmdbuf_rw_type, ch);

    DYN_CFG_ARRAY(ptr, du_cmdbuf_op_mode, ch);

    DYN_CFG_ARRAY(ptr, du_cmdbuf_select, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DU_CMDBUF_CTRL, ptr[ch]->value);
    }
    SNPS_TRACE("Leaving");
}
#endif /* DDRCTL_DDR */
#endif

#if defined(DDRCTL_DDR) && defined(DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL37(void)
{
    SNPS_TRACE("Entering");
    PASCTL37_t *const ptr = &REGB_DDRC_CH0.pasctl37;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, t_selfref_exit_stagger);

    DYN_CFG(ptr, dch_sync_mode);

    DYN_CFG(ptr, dch_ch0_mask);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + PASCTL37, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + PASCTL37, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH*/
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL37(void)
{
};
#endif /* DDRCTL_DDR && DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH*/

/**
 * @brief function to setup the register field values for LP_CMDBUF_CTRL
 */
// Commented out, currently not used
#if 0
#ifdef DDRCTL_DDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_LP_CMDBUF_CTRL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    LP_CMDBUF_CTRL_t *const ptr[2] = {
        &REGB_DDRC_CH0.LP_CMDBUF_CTRL,
        &REGB_DDRC_CH1.LP_CMDBUF_CTRL
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, lp_cmdbuf_rw_start, ch);

    DYN_CFG_ARRAY(ptr, lp_cmdbuf_rw_type, ch);

    DYN_CFG_ARRAY(ptr, lp_cmdbuf_op_mode, ch);

    DYN_CFG_ARRAY(ptr, lp_cmdbuf_addr, ch);

    DYN_CFG_ARRAY(ptr, lp_cmdbuf_wdata, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + LP_CMDBUF_CTRL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#endif /* DDRCTL_DDR */
#endif

/**
 * @brief function to setup the register field values for datactl0
 */
#ifdef DDRCTL_LPDDR
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DATACTL0(void)
{
    SNPS_TRACE("Entering");
    DATACTL0_t *const ptr = &REGB_DDRC_CH0.datactl0;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, wr_data_x_en);

    QDYN_CFG(ptr, wr_data_copy_en);

    QDYN_CFG(ptr, rd_data_copy_en);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DATACTL0, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DATACTL0(void)
{
};
#endif /* DDRCTL_LPDDR */

/**
 * @brief function to setup the register field values for ocecccfg0
 */
#ifdef UMCTL2_OCECC_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCECCCFG0(void)
{
    SNPS_TRACE("Entering");
    OCECCCFG0_t *const ptr = &REGB_DDRC_CH0.ocecccfg0;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, ocecc_en);

    DYN_CFG(ptr, ocecc_uncorrected_err_intr_en);

    QDYN_CFG(ptr, ocecc_wdata_slverr_en);

    DYN_CFG(ptr, ocecc_uncorrected_err_intr_clr);

    DYN_CFG(ptr, ocecc_uncorrected_err_intr_force);

    QDYN_CFG(ptr, ocecc_rdata_slverr_en);

#ifdef UMCTL2_OCECC_FEC_EN
    QDYN_CFG(ptr, ocecc_fec_en);

    DYN_CFG(ptr, ocecc_corrected_err_intr_en);

    DYN_CFG(ptr, ocecc_corrected_err_intr_clr);

    DYN_CFG(ptr, ocecc_corrected_err_intr_force);
#endif /* UMCTL2_OCECC_FEC_EN */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + OCECCCFG0, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_OCECC_EN_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCECCCFG0(void)
{
};
#endif /* UMCTL2_OCECC_EN_1 */

/**
 * @brief function to setup the register field values for ocecccfg1
 */
#ifdef UMCTL2_OCECC_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCECCCFG1(void)
{
    SNPS_TRACE("Entering");
    OCECCCFG1_t *const ptr = &REGB_DDRC_CH0.ocecccfg1;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, ocecc_poison_en);

    QDYN_CFG(ptr, ocecc_poison_egen_mr_rd_0);

    QDYN_CFG(ptr, ocecc_poison_egen_mr_rd_0_byte_num);

    QDYN_CFG(ptr, ocecc_poison_egen_xpi_rd_out);

    QDYN_CFG(ptr, ocecc_poison_port_num);

    QDYN_CFG(ptr, ocecc_poison_egen_mr_rd_1);

    QDYN_CFG(ptr, ocecc_poison_egen_mr_rd_1_byte_num);

    QDYN_CFG(ptr, ocecc_poison_egen_xpi_rd_0);

    QDYN_CFG(ptr, ocecc_poison_ecc_corr_uncorr);

    QDYN_CFG(ptr, ocecc_poison_pgen_rd);

#ifdef UMCTL2_OCECC_FEC_EN
    QDYN_CFG(ptr, ocecc_poison_pgen_mr_wdata);
#endif /* UMCTL2_OCECC_FEC_EN */

    QDYN_CFG(ptr, ocecc_poison_pgen_mr_ecc);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + OCECCCFG1, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_OCECC_EN_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCECCCFG1(void)
{
};
#endif /* UMCTL2_OCECC_EN_1 */

/**
 * @brief function to setup the register field values for occapcfg
 */
#ifdef UMCTL2_OCCAP_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCCAPCFG(void)
{
    SNPS_TRACE("Entering");
    OCCAPCFG_t *const ptr = &REGB_DDRC_CH0.occapcfg;
    uint32_t tmp = ptr->value;

    QDYN_CFG(ptr, occap_en);

#ifdef UMCTL2_INCL_ARB
    DYN_CFG(ptr, occap_arb_intr_en);

    DYN_CFG(ptr, occap_arb_intr_clr);

    DYN_CFG(ptr, occap_arb_intr_force);

    DYN_CFG(ptr, occap_arb_cmp_poison_seq);

    DYN_CFG(ptr, occap_arb_cmp_poison_parallel);

    DYN_CFG(ptr, occap_arb_cmp_poison_err_inj);

    DYN_CFG(ptr, occap_arb_raq_poison_en);
#endif /* UMCTL2_INCL_ARB */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + OCCAPCFG, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_OCCAP_EN_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCCAPCFG(void)
{
};
#endif /* UMCTL2_OCCAP_EN_1 */

/**
 * @brief function to setup the register field values for occapcfg1
 */
#ifdef UMCTL2_OCCAP_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCCAPCFG1(uint32_t ch)
{
    SNPS_TRACE("Entering");
    OCCAPCFG1_t *const ptr[2] = {
        &REGB_DDRC_CH0.occapcfg1,
        &REGB_DDRC_CH1.occapcfg1
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, occap_ddrc_data_intr_en, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_data_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_data_intr_force, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_data_poison_seq, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_data_poison_parallel, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_data_poison_err_inj, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_ctrl_intr_en, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_ctrl_intr_clr, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_ctrl_intr_force, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_ctrl_poison_seq, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_ctrl_poison_parallel, ch);

    DYN_CFG_ARRAY(ptr, occap_ddrc_ctrl_poison_err_inj, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OCCAPCFG1, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_OCCAP_EN_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_OCCAPCFG1(uint32_t ch)
{
};
#endif /* UMCTL2_OCCAP_EN_1 */

/**
 * @brief function to setup the register field values for opctrlcmd
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OPCTRLCMD(uint32_t ch)
{
    SNPS_TRACE("Entering");
    OPCTRLCMD_t *const ptr[2] = {
        &REGB_DDRC_CH0.opctrlcmd,
        &REGB_DDRC_CH1.opctrlcmd
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef UMCTL2_REF_ZQ_IO
    STATIC_CFG_ARRAY(ptr, hw_ref_zq_en, ch);
#endif /* UMCTL2_REF_ZQ_IO */

    DYN_CFG_ARRAY(ptr, ctrlupd, ch);

    DYN_CFG_ARRAY(ptr, zq_calib_short, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPCTRLCMD, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for oprefctrl0
 */
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OPREFCTRL0(uint32_t ch)
{
    SNPS_TRACE("Entering");
    OPREFCTRL0_t *const ptr[2] = {
        &REGB_DDRC_CH0.oprefctrl0,
        &REGB_DDRC_CH1.oprefctrl0
    };
    uint32_t tmp = ptr[ch]->value;

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_0
    DYN_CFG_ARRAY(ptr, rank0_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_0 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_1
    DYN_CFG_ARRAY(ptr, rank1_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_1 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_2
    DYN_CFG_ARRAY(ptr, rank2_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_2 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_3
    DYN_CFG_ARRAY(ptr, rank3_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_3 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_4
    DYN_CFG_ARRAY(ptr, rank4_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_4 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_5
    DYN_CFG_ARRAY(ptr, rank5_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_5 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_6
    DYN_CFG_ARRAY(ptr, rank6_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_6 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_7
    DYN_CFG_ARRAY(ptr, rank7_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_7 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_8
    DYN_CFG_ARRAY(ptr, rank8_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_8 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_9
    DYN_CFG_ARRAY(ptr, rank9_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_9 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_10
    DYN_CFG_ARRAY(ptr, rank10_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_10 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_11
    DYN_CFG_ARRAY(ptr, rank11_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_11 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_12
    DYN_CFG_ARRAY(ptr, rank12_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_12 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_13
    DYN_CFG_ARRAY(ptr, rank13_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_13 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_14
    DYN_CFG_ARRAY(ptr, rank14_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_14 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_15
    DYN_CFG_ARRAY(ptr, rank15_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_15 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_16
    DYN_CFG_ARRAY(ptr, rank16_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_16 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_17
    DYN_CFG_ARRAY(ptr, rank17_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_17 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_18
    DYN_CFG_ARRAY(ptr, rank18_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_18 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_19
    DYN_CFG_ARRAY(ptr, rank19_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_19 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_20
    DYN_CFG_ARRAY(ptr, rank20_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_20 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_21
    DYN_CFG_ARRAY(ptr, rank21_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_21 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_22
    DYN_CFG_ARRAY(ptr, rank22_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_22 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_23
    DYN_CFG_ARRAY(ptr, rank23_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_23 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_24
    DYN_CFG_ARRAY(ptr, rank24_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_24 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_25
    DYN_CFG_ARRAY(ptr, rank25_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_25 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_26
    DYN_CFG_ARRAY(ptr, rank26_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_26 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_27
    DYN_CFG_ARRAY(ptr, rank27_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_27 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_28
    DYN_CFG_ARRAY(ptr, rank28_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_28 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_29
    DYN_CFG_ARRAY(ptr, rank29_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_29 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_30
    DYN_CFG_ARRAY(ptr, rank30_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_30 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_31
    DYN_CFG_ARRAY(ptr, rank31_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_31 */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPREFCTRL0, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}

/**
 * @brief function to setup the register field values for oprefctrl1
 */
#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_32
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_OPREFCTRL1(uint32_t ch)
{
    SNPS_TRACE("Entering");
    OPREFCTRL1_t *const ptr[2] = {
        &REGB_DDRC_CH0.oprefctrl1,
        &REGB_DDRC_CH1.oprefctrl1
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, rank32_refresh, ch);

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_33
    DYN_CFG_ARRAY(ptr, rank33_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_33 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_34
    DYN_CFG_ARRAY(ptr, rank34_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_34 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_35
    DYN_CFG_ARRAY(ptr, rank35_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_35 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_36
    DYN_CFG_ARRAY(ptr, rank36_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_36 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_37
    DYN_CFG_ARRAY(ptr, rank37_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_37 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_38
    DYN_CFG_ARRAY(ptr, rank38_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_38 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_39
    DYN_CFG_ARRAY(ptr, rank39_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_39 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_40
    DYN_CFG_ARRAY(ptr, rank40_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_40 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_41
    DYN_CFG_ARRAY(ptr, rank41_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_41 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_42
    DYN_CFG_ARRAY(ptr, rank42_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_42 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_43
    DYN_CFG_ARRAY(ptr, rank43_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_43 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_44
    DYN_CFG_ARRAY(ptr, rank44_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_44 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_45
    DYN_CFG_ARRAY(ptr, rank45_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_45 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_46
    DYN_CFG_ARRAY(ptr, rank46_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_46 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_47
    DYN_CFG_ARRAY(ptr, rank47_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_47 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_48
    DYN_CFG_ARRAY(ptr, rank48_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_48 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_49
    DYN_CFG_ARRAY(ptr, rank49_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_49*/

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_50
    DYN_CFG_ARRAY(ptr, rank50_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_50 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_51
    DYN_CFG_ARRAY(ptr, rank51_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_51 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_52
    DYN_CFG_ARRAY(ptr, rank52_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_52 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_53
    DYN_CFG_ARRAY(ptr, rank53_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_53 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_54
    DYN_CFG_ARRAY(ptr, rank54_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_54 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_55
    DYN_CFG_ARRAY(ptr, rank55_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_55 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_56
    DYN_CFG_ARRAY(ptr, rank56_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_56 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_57
    DYN_CFG_ARRAY(ptr, rank57_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_57 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_58
    DYN_CFG_ARRAY(ptr, rank58_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_58 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_59
    DYN_CFG_ARRAY(ptr, rank59_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_59 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_60
    DYN_CFG_ARRAY(ptr, rank60_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_60 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_61
    DYN_CFG_ARRAY(ptr, rank61_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_61 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_62
    DYN_CFG_ARRAY(ptr, rank62_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_62 */

#ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_63
    DYN_CFG_ARRAY(ptr, rank63_refresh, ch);
#endif /* UMCTL2_NUM_LRANKS_TOTAL_GT_63 */

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + OPREFCTRL1, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_OPREFCTRL1(uint32_t ch)
{
};
#endif

/**
 * @brief function to setup the register field values for ppt2ctrl0
 */
#if defined(DDRCTL_PPT2)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_PPT2CTRL0(void)
{
    SNPS_TRACE("Entering");

    PPT2CTRL0_t *const ptr = &REGB_DDRC_CH0.ppt2ctrl0;

    DYN_CFG(ptr, ppt2_wait_ref);

    DYN_CFG(ptr, ppt2_burst);

    DYN_CFG(ptr, ppt2_ctrlupd_num_dfi0);

    DYN_CFG(ptr, ppt2_ctrlupd_num_dfi1);

    DYN_CFG(ptr, ppt2_burst_num);

    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + PPT2CTRL0, ptr->value);

    SNPS_TRACE("Leaving");
}
#else
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_PPT2CTRL0(void)
{
};
#endif

/**
 * @brief function to setup the register field values for dqmap0
 */
#if defined(DDRCTL_DDR) && defined(UMCTL2_DQ_MAPPING)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP0(void)
{
    SNPS_TRACE("Entering");
    DQMAP0_t *const ptr = &REGB_DDRC_CH0.dqmap0;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dq_nibble_map_12_15);

    STATIC_CFG(ptr, dq_nibble_map_8_11);

    STATIC_CFG(ptr, dq_nibble_map_4_7);

    STATIC_CFG(ptr, dq_nibble_map_0_3);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQMAP0, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && UMCTL2_DQ_MAPPING */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP0(void)
{
};
#endif /* DDRCTL_DDR && UMCTL2_DQ_MAPPING */

/**
 * @brief function to setup the register field values for dqmap1
 */
#if defined(DDRCTL_DDR) && defined(UMCTL2_DQ_MAPPING) && defined(MEMC_DRAM_DATA_WIDTH_GT_23)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP1(void)
{
    SNPS_TRACE("Entering");
    DQMAP1_t *const ptr = &REGB_DDRC_CH0.dqmap1;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dq_nibble_map_28_31);

    STATIC_CFG(ptr, dq_nibble_map_24_27);

    STATIC_CFG(ptr, dq_nibble_map_20_23);

    STATIC_CFG(ptr, dq_nibble_map_16_19);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQMAP1, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && UMCTL2_DQ_MAPPING && MEMC_DRAM_DATA_WIDTH_23 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP1(void)
{
};
#endif /* DDRCTL_DDR && UMCTL2_DQ_MAPPING && MEMC_DRAM_DATA_WIDTH_23 */

/**
 * @brief function to setup the register field values for dqmap2
 */
#if defined(DDRCTL_DDR) && defined(UMCTL2_DQ_MAPPING) && defined(MEMC_DRAM_DATA_WIDTH_GT_39)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP2(void)
{
    SNPS_TRACE("Entering");
    DQMAP2_t *const ptr = &REGB_DDRC_CH0.dqmap2;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dq_nibble_map_44_47);

    STATIC_CFG(ptr, dq_nibble_map_40_43);

    STATIC_CFG(ptr, dq_nibble_map_36_39);

    STATIC_CFG(ptr, dq_nibble_map_32_35);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQMAP2, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && UMCTL2_DQ_MAPPING && MEMC_DRAM_DATA_WIDTH_39 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP2(void)
{
};
#endif /* DDRCTL_DDR && UMCTL2_DQ_MAPPING && MEMC_DRAM_DATA_WIDTH_39 */

/**
 * @brief function to setup the register field values for dqmap3
 */
#if defined(DDRCTL_DDR) && defined(UMCTL2_DQ_MAPPING) && defined(MEMC_DRAM_DATA_WIDTH_GT_55)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP3(void)
{
    SNPS_TRACE("Entering");
    DQMAP3_t *const ptr = &REGB_DDRC_CH0.dqmap3;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dq_nibble_map_60_63);

    STATIC_CFG(ptr, dq_nibble_map_56_59);

    STATIC_CFG(ptr, dq_nibble_map_52_55);

    STATIC_CFG(ptr, dq_nibble_map_48_51);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQMAP3, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && UMCTL2_DQ_MAPPING && MEMC_DRAM_DATA_WIDTH_55 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP3(void)
{
};
#endif /* DDRCTL_DDR && UMCTL2_DQ_MAPPING && MEMC_DRAM_DATA_WIDTH_55 */

/**
 * @brief function to setup the register field values for dqmap4
 */
#if defined(DDRCTL_DDR) && defined(UMCTL2_DQ_MAPPING) && defined(MEMC_DRAM_DATA_WIDTH_72_OR_MEMC_SIDEBAND_ECC)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP4(void)
{
    SNPS_TRACE("Entering");
    DQMAP4_t *const ptr = &REGB_DDRC_CH0.dqmap4;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dq_nibble_map_cb_4_7);

    STATIC_CFG(ptr, dq_nibble_map_cb_0_3);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQMAP4, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && UMCTL2_DQ_MAPPING && MEMC_DRAM_DATA_WIDTH_72_OR_MEMC_SIDEBAND_ECC */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP4(void)
{
};
#endif /* DDRCTL_DDR && UMCTL2_DQ_MAPPING && MEMC_DRAM_DATA_WIDTH_72_OR_MEMC_SIDEBAND_ECC */

/**
 * @brief function to setup the register field values for dqmap5
 */
#if defined(DDRCTL_DDR) && defined(UMCTL2_DQ_MAPPING)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP5(void)
{
    SNPS_TRACE("Entering");
    DQMAP5_t *const ptr = &REGB_DDRC_CH0.dqmap5;
    uint32_t tmp = ptr->value;

    STATIC_CFG(ptr, dis_dq_rank_swap);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + DQMAP5, ptr->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_DDR && UMCTL2_DQ_MAPPING */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP5(void)
{
};
#endif /* DDRCTL_DDR && UMCTL2_DQ_MAPPING */

/**
 * @brief function to setup the register field values for regparcfg
 */
#ifdef UMCTL2_REGPAR_EN_1
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_REGPARCFG(void)
{
    SNPS_TRACE("Entering");
    REGPARCFG_t *const ptr = &REGB_DDRC_CH0.regparcfg;
    uint32_t tmp = ptr->value;

    DYN_CFG(ptr, reg_par_poison_en);

    DYN_CFG(ptr, reg_par_err_intr_force);

    DYN_CFG(ptr, reg_par_err_intr_clr);

    DYN_CFG(ptr, reg_par_err_intr_en);

    DYN_CFG(ptr, reg_par_en);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + REGPARCFG, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + REGPARCFG, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_REGPAR_EN_1 */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_REGPARCFG(void)
{
};
#endif /* UMCTL2_REGPAR_EN_1 */

/**
 * @brief function to setup the register field values for poisoncfg
 */
#if defined(UMCTL2_INCL_ARB) && defined(UMCTL2_A_AXI)
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_POISONCFG(void)
{
    SNPS_TRACE("Entering");
    POISONCFG_t *const ptr = &REGB_DDRC_CH0.poisoncfg;
    uint32_t tmp = ptr->value;

    DYN_CFG(ptr, wr_poison_slverr_en);

    DYN_CFG(ptr, wr_poison_intr_en);

    DYN_CFG(ptr, wr_poison_intr_clr);

    DYN_CFG(ptr, rd_poison_slverr_en);

    DYN_CFG(ptr, rd_poison_intr_en);

    DYN_CFG(ptr, rd_poison_intr_clr);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + POISONCFG, ptr->value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(1) + POISONCFG, ptr->value);
#endif // DDRCTL_SINGLE_INST_DUALCH
    }

    SNPS_TRACE("Leaving");
}
#else /* UMCTL2_INCL_ARB && UMCTL2_A_AXI */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_POISONCFG(void)
{
};
#endif /* UMCTL2_INCL_ARB && UMCTL2_A_AXI */

#ifdef DDRCTL_ENH_ECC_REPORT_EN
static void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCERRCNTCTL(uint32_t ch)
{
    SNPS_TRACE("Entering");
    ECCERRCNTCTL_t *const ptr[2] = {
        &REGB_DDRC_CH0.eccerrcntctl,
        &REGB_DDRC_CH1.eccerrcntctl
    };
    uint32_t tmp = ptr[ch]->value;

    DYN_CFG_ARRAY(ptr, ecc_corr_err_per_rank_intr_en, ch);

    DYN_CFG_ARRAY(ptr, ecc_corr_err_log_mode, ch);

    DYN_CFG_ARRAY(ptr, ecc_uncorr_err_log_mode, ch);

    DYN_CFG_ARRAY(ptr, ecc_corr_err_cnt_clr_rank3, ch);

    DYN_CFG_ARRAY(ptr, ecc_corr_err_cnt_clr_rank2, ch);

    DYN_CFG_ARRAY(ptr, ecc_corr_err_cnt_clr_rank1, ch);

    DYN_CFG_ARRAY(ptr, ecc_corr_err_cnt_clr_rank0, ch);

    DYN_CFG_ARRAY(ptr, ecc_corr_threshold, ch);

    if ((CINIT_REG_FORCE_WRITE == 1) || (tmp != ptr[ch]->value)) {
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + ECCERRCNTCTL, ptr[ch]->value);
    }

    SNPS_TRACE("Leaving");
}
#else /* DDRCTL_ENH_ECC_REPORT_EN */
static inline void dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCERRCNTCTL(uint32_t ch)
{
};
#endif /* DDRCTL_ENH_ECC_REPORT_EN */

/**
 * @brief function to setup the register field values for DDRCTL_IMECFG0
 * @note requires secure APB write (pprot[1]==SECURE)
 */

static void dwc_ddrctl_cinit_prgm_REGB_DDRC_DDRCTL_IMECFG0(uint32_t ch)
{
#ifdef DDRCTL_SECURE
    DDRCTL_IMECFG0_t *const ptr[2] = {
        &REGB_DDRC_CH0.ddrctl_imecfg0,
        &REGB_DDRC_CH1.ddrctl_imecfg0
    };
    uint32_t tmp = ptr[ch]->value;

    ptr[ch]->ime_en = CFG->ime_cfg[ch].enable;

    if (tmp != ptr[ch]->value) {
        dwc_ddrctl_cinit_io_secure_write32(REGB_DDRC_CH_OFFSET(ch) + DDRCTL_IMECFG0, ptr[ch]->value);
    }

#endif /* DDRCTL_SECURE */
}


/**
 * @brief iterate through all DDRC registers setting up a 32-bit value to
 * be programmed into each writable register.
 */
void dwc_ddrctl_cinit_prgm_REGB_DDRC(void)
{
	SNPS_TRACE("Entering");
	dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR2();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIMISC();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIPHYMSTR();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_RFSHCTL0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_RFSHMOD0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_RFSHMOD1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ZQCTL0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_RFMMOD0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_RFMMOD1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ZQCTL2();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL2();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL3();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL4();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL6();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_RANKCTL();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCFG0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCFG1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCFG2();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONADDR0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONADDR1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONPAT0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONPAT1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCPOISONPAT2();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DIMMCTL();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_OPCTRL0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_HWFFCCTL();
        dwc_ddrctl_cinit_prgm_REGB_DDRC_CGCTL();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_ADVECCINDEX();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_OCPARCFG1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_OCSAPCFG0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DQSOSCRUNTIME();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED2();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED3();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED4();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED5();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED6();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SCHED7();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DFILPCFG0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIUPD0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIUPD1();
        dwc_ddrctl_cinit_prgm_REGB_DDRC_DFISBPOISONCFG();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPARCTL1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPARCTL2();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DATACTL0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SWCTL();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_CHCTL();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_OCECCCFG0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_OCECCCFG1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_OCCAPCFG();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_PPT2CTRL0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP1();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP2();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP3();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP4();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DQMAP5();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_REGPARCFG();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_POISONCFG();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_SWCTLSTATIC();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DQSOSCCFG0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_DQSOSCTMG0();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL37();
	dwc_ddrctl_cinit_prgm_REGB_DDRC_CLKGATECTL();

	for (uint32_t ch = 0; ch < hdlr->num_dch; ch++) {
		dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR3(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL1(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL3(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_MRCTRL0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_HWLPCTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_HWLPCTL2(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATECTL5(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_DERATEDBGCTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_DBICTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_OPCTRL1(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PWRCTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCCTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_EAPARCTL0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_INITTMG0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_INITTMG2(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_MSTR4(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_MRCTRL1(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_MRCTRL2(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_OCPARCFG0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_ZQCTL1(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_RETRYCTL0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPARCTL0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_CRCPOISONCTL0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_CAPARPOISONCTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_LNKECCCTL1(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_LNKECCPOISONCTL0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_LNKECCINDEX(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_DFISBINTRPTCFG(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_DFIERRINTRPTCFG(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL2(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL4(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_CMDCFG(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_CMDCTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_CMDEXTCTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_ODTMAP(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_OCCAPCFG1(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_OPCTRLCMD(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_OPREFCTRL0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_OPREFCTRL1(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL5(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL6(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL7(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL8(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL9(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL10(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL11(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL12(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL13(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL14(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL15(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL16(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL17(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL18(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL20(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL21(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL22(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL23(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL24(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL36(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASCTL38(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_PASINTCTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_ECSCTL(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_DDRCTL_IMECFG0(ch);
		dwc_ddrctl_cinit_prgm_REGB_DDRC_ECCERRCNTCTL(ch);
    }
    SNPS_TRACE("Leaving");
}

