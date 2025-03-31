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
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_prgm_port_util.h"


void ddrctl_cinit_arb_port_write(uint32_t address, uint32_t value)
{
    dwc_ddrctl_cinit_io_write32(address, value);
#if defined(DDRCTL_SINGLE_INST_DUALCH) || defined(LPDDR_2MC1PHY)
    dwc_ddrctl_cinit_io_write32(DDRCTL_CTRL_INST1_BASE_ADDR + \
                                address, value);
#endif // DDRCTL_SINGLE_INST_DUALCH
}


/**
 * @brief function to setup the register field values for PCCFG
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCCFG(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_INCL_ARB
#ifdef UMCTL2_A_AXI_0
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + PCCFG);

    SNPS_WRITE_FIELD(reg_val, PCCFG_GO2CRITICAL_EN,  STATIC_FIELD(cinit_cfg, go2critical_en));
    SNPS_WRITE_FIELD(reg_val, PCCFG_PAGEMATCH_LIMIT, STATIC_FIELD(cinit_cfg, pagematch_limit));

#ifdef DDRCTL_HET_INTERLEAVE_EN_1
    SNPS_WRITE_FIELD(reg_val, PCCFG_DCH_DENSITY_RATIO, STATIC_FIELD(cinit_cfg, dch_density_ratio));

    if ((DDRCTL_IS_LPDDR(cinit_cfg) == true) || (IS_X16(0) == false)) {
        CONSTRAIN_EQ(STATIC_FIELD(cinit_cfg, dch_density_ratio), 0);
    } else {
        if (IS_DENS_2GBIT(0)) {
            CONSTRAIN_EQ(STATIC_FIELD(cinit_cfg, dch_density_ratio), 0);
        } else if (IS_DENS_4GBIT(0)) {
            CONSTRAIN_MAX(STATIC_FIELD(cinit_cfg, dch_density_ratio), 1);
        } else {
            CONSTRAIN_MAX(STATIC_FIELD(cinit_cfg, dch_density_ratio), 2);
        }
    }
#endif /* DDRCTL_HET_INTERLEAVE_EN_1 */
    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + PCCFG, reg_val);
#endif /* UMCTL2_A_AXI_0 */
#endif /* UMCTL2_INCL_ARB */
}


/**
 * @brief function to setup the register field values for PCFGR
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGR(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_INCL_ARB
    uint32_t reg_val;
    uint32_t port_bitmap;
    uint32_t ch_bitmap;
    uint32_t thrs_bitmap;
    uint32_t ordered_bitmap;
    uint8_t  port;

    port_bitmap     = dwc_ddrctl_get_port_bitmap();
    ch_bitmap       = dwc_ddrctl_get_port_channel_bitmap();
    thrs_bitmap     = dwc_ddrctl_get_threshold_bitmap();
    ordered_bitmap  = dwc_ddrctl_get_ordered_bitmap();

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        if (SNPS_GET_BIT(port_bitmap, port) != SNPS_CINIT_SET) {
            continue;
        }

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCFGR);

        if (SNPS_GET_BIT(thrs_bitmap, port) == SNPS_CINIT_SET) {
            SNPS_WRITE_FIELD(reg_val, PCFGR_RRB_LOCK_THRESHOLD, STATIC_FIELD(cinit_cfg, rrb_lock_threshold[port]));
        }
        if (SNPS_GET_BIT(ordered_bitmap, port) == SNPS_CINIT_SET) {
            SNPS_WRITE_FIELD(reg_val, PCFGR_RDWR_ORDERED_EN, QDYN_FIELD(cinit_cfg, rdwr_ordered_en[port]));
        }
        if (SNPS_GET_BIT(ch_bitmap, port) == SNPS_CINIT_SET) {
            SNPS_WRITE_FIELD(reg_val, PCFGR_READ_REORDER_BYPASS_EN, QDYN_FIELD(cinit_cfg, read_reorder_bypass_en[port]));
        }
        SNPS_WRITE_FIELD(reg_val, PCFGR_RD_PORT_PAGEMATCH_EN, STATIC_FIELD(cinit_cfg, rd_port_pagematch_en[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGR_RD_PORT_URGENT_EN,    STATIC_FIELD(cinit_cfg, rd_port_urgent_en[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGR_RD_PORT_AGING_EN,     STATIC_FIELD(cinit_cfg, rd_port_aging_en[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGR_RD_PORT_PRIORITY,     STATIC_FIELD(cinit_cfg, rd_port_priority[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCFGR, reg_val);
    }
#endif /* UMCTL2_INCL_ARB */
}

/**
 * @brief function to setup the register field values for pcfgw
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGW(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_INCL_ARB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCFGW);

#ifdef DDRCTL_XPI_PROG_SNF
        SNPS_WRITE_FIELD(reg_val, PCFGW_SNF_MODE,             STATIC_FIELD(cinit_cfg, snf_mode[port]));
#endif
        SNPS_WRITE_FIELD(reg_val, PCFGW_WR_PORT_PAGEMATCH_EN, STATIC_FIELD(cinit_cfg, wr_port_pagematch_en[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGW_WR_PORT_URGENT_EN,    STATIC_FIELD(cinit_cfg, wr_port_urgent_en[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGW_WR_PORT_AGING_EN,     STATIC_FIELD(cinit_cfg, wr_port_aging_en[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGW_WR_PORT_PRIORITY,     STATIC_FIELD(cinit_cfg, wr_port_priority[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCFGW, reg_val);
    }
#endif /* UMCTL2_INCL_ARB */
}


/**
 * @brief function to setup the register field values for pcfgidmaskch
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGIDMASKCH(SubsysHdlr_t *cinit_cfg, uint32_t port)
{
#ifdef UMCTL2_INCL_ARB
#if defined(UMCTL2_PORT_CH0_0)
    uint32_t reg_val;
    uint32_t ch_bitmap;
    uint8_t  v_channel; // virtual channels

    ch_bitmap = dwc_ddrctl_get_arb_ports_ch_bitmap();

    for (v_channel=0; v_channel < SNPS_MAX_CHANNELS; v_channel++) {
        if (SNPS_GET_BIT(ch_bitmap, v_channel) != SNPS_CINIT_SET) {
            continue;
        }

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCFGIDMASKCH0 + \
                                            (v_channel * SNPS_8_BYTES));

        SNPS_WRITE_FIELD(reg_val, PCFGIDMASKCH0_ID_MASK, QDYN_FIELD(cinit_cfg, id_mask[port][v_channel]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCFGIDMASKCH0  + (v_channel * SNPS_8_BYTES), reg_val);
    }
#endif /* UMCTL2_PORT_CH0_0 */
#endif /* UMCTL2_INCL_ARB */
}

/**
 * @brief function to setup the register field values for pcfgidvaluech
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGIDVALUECH(SubsysHdlr_t *cinit_cfg, uint32_t port)
{
#ifdef UMCTL2_INCL_ARB
#if defined(UMCTL2_PORT_CH0_0)
    uint32_t reg_val;
    uint32_t ch_bitmap;
    uint8_t  v_channel; // virtual channels

    ch_bitmap = dwc_ddrctl_get_arb_ports_ch_bitmap();

    for (v_channel=0; v_channel < SNPS_MAX_CHANNELS; v_channel++) {
        if (SNPS_GET_BIT(ch_bitmap, v_channel) != SNPS_CINIT_SET) {
            continue;
        }

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCFGIDVALUECH0 + \
                                            (v_channel * SNPS_8_BYTES));

        SNPS_WRITE_FIELD(reg_val, PCFGIDVALUECH0_ID_VALUE, QDYN_FIELD(cinit_cfg, id_value[port][v_channel]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCFGIDVALUECH0 + (v_channel * SNPS_8_BYTES), reg_val);
    }
#endif
#endif /* UMCTL2_INCL_ARB */
}


/**
 * @brief function to setup the register field values for pctrl
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCTRL(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_INCL_ARB_OR_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCTRL);

        SNPS_WRITE_FIELD(reg_val, PCTRL_PORT_EN, DYN_FIELD(cinit_cfg, port_en[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCTRL, reg_val);
    }
#endif /* UMCTL2_INCL_ARB_OR_CHB */
}


/**
 * @brief function to setup the register field values for pcfgqos0
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGQOS0(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_INCL_ARB_OR_CHB
    uint32_t reg_val;
    uint32_t axi_bitmap;
    uint32_t use2raq_bitmap;
    uint8_t  port;
    uint8_t  level1_max;

    axi_bitmap     = dwc_ddrctl_get_arb_ports_axi_bitmap();
    use2raq_bitmap = dwc_ddrctl_get_arb_ports_axi_raq_bitmap();

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        if (SNPS_GET_BIT(axi_bitmap, port) != SNPS_CINIT_SET) {
            continue;
        }
        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCFGQOS0);

        if (SNPS_GET_BIT(use2raq_bitmap, port) == SNPS_CINIT_SET) {
            CONSTRAIN_MAX(QDYN_FIELD(cinit_cfg, rqos_map_region2[port]), 2);
            SNPS_WRITE_FIELD(reg_val, PCFGQOS0_RQOS_MAP_REGION2, QDYN_FIELD(cinit_cfg, rqos_map_region2[port]));
            CONSTRAIN_INSIDE(QDYN_FIELD(cinit_cfg, rqos_map_level2[port]), 1, 14);
            SNPS_WRITE_FIELD(reg_val, PCFGQOS0_RQOS_MAP_LEVEL2, QDYN_FIELD(cinit_cfg, rqos_map_level2[port]));
            level1_max = 13;
        } else {
            level1_max = 14;
        }

        CONSTRAIN_MAX(QDYN_FIELD(cinit_cfg, rqos_map_region1[port]), 2);
        SNPS_WRITE_FIELD(reg_val, PCFGQOS0_RQOS_MAP_REGION1, QDYN_FIELD(cinit_cfg, rqos_map_region1[port]));

        CONSTRAIN_MAX(QDYN_FIELD(cinit_cfg, rqos_map_region0[port]), 2);
        SNPS_WRITE_FIELD(reg_val, PCFGQOS0_RQOS_MAP_REGION0, QDYN_FIELD(cinit_cfg, rqos_map_region0[port]));

        CONSTRAIN_MAX(QDYN_FIELD(cinit_cfg, rqos_map_level1[port]), level1_max);
        SNPS_WRITE_FIELD(reg_val, PCFGQOS0_RQOS_MAP_LEVEL1, QDYN_FIELD(cinit_cfg, rqos_map_level1[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCFGQOS0, reg_val);
    }
#endif /* UMCTL2_INCL_ARB_OR_CHB */
}


/**
 * @brief function to setup the register field values for pcfgqos1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGQOS1(SubsysHdlr_t *cinit_cfg)
{
#if defined(UMCTL2_A_AXI_0) && defined(UMCTL2_XPI_VPR_0)
    uint32_t reg_val;
    uint32_t axi_bitmap;
    uint32_t vpr_bitmap;
    uint8_t  port;

    axi_bitmap = dwc_ddrctl_get_arb_ports_axi_bitmap();
    vpr_bitmap = dwc_ddrctl_get_xpi_vpr_bitmap();

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        if (SNPS_GET_BIT(axi_bitmap, port) != SNPS_CINIT_SET) {
            continue;
        }
        if (SNPS_GET_BIT(vpr_bitmap, port) != SNPS_CINIT_SET) {
            continue;
        }

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCFGQOS1);

        SNPS_WRITE_FIELD(reg_val, PCFGQOS1_RQOS_MAP_TIMEOUTB, QDYN_FIELD(cinit_cfg, rqos_map_timeoutb[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGQOS1_RQOS_MAP_TIMEOUTR, QDYN_FIELD(cinit_cfg, rqos_map_timeoutr[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCFGQOS1, reg_val);
    }
#endif /* UMCTL2_A_AXI_0 && UMCTL2_XPI_VPR_0 */
}


/**
 * @brief function to setup the register field values for pcfgwqos0
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGWQOS0(SubsysHdlr_t *cinit_cfg)
{
    uint32_t axi_bitmap;
    uint32_t vpw_bitmap;
    uint32_t reg_val;
    uint8_t  port;

    axi_bitmap = dwc_ddrctl_get_arb_ports_axi_bitmap();
    vpw_bitmap = dwc_ddrctl_get_xpi_vpw_bitmap();

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        if (SNPS_GET_BIT(axi_bitmap, port) != SNPS_CINIT_SET) {
            continue;
        }
        if (SNPS_GET_BIT(vpw_bitmap, port) != SNPS_CINIT_SET) {
            continue;
        }

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCFGWQOS0);

        SNPS_WRITE_FIELD(reg_val, PCFGWQOS0_WQOS_MAP_LEVEL1, QDYN_FIELD(cinit_cfg, wqos_map_level1[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGWQOS0_WQOS_MAP_LEVEL2, QDYN_FIELD(cinit_cfg, wqos_map_level2[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGWQOS0_WQOS_MAP_REGION0, QDYN_FIELD(cinit_cfg, wqos_map_region0[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGWQOS0_WQOS_MAP_REGION1, QDYN_FIELD(cinit_cfg, wqos_map_region1[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGWQOS0_WQOS_MAP_REGION2, QDYN_FIELD(cinit_cfg, wqos_map_region2[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCFGWQOS0, reg_val);
    }
}


/**
 * @brief function to setup the register field values for pcfgwqos1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGWQOS1(SubsysHdlr_t *cinit_cfg)
{
    uint32_t axi_bitmap;
    uint32_t vpw_bitmap;
    uint32_t reg_val;
    uint8_t  port;

    axi_bitmap = dwc_ddrctl_get_arb_ports_axi_bitmap();
    vpw_bitmap = dwc_ddrctl_get_xpi_vpw_bitmap();

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        if (SNPS_GET_BIT(axi_bitmap, port) != SNPS_CINIT_SET) {
            continue;
        }
        if (SNPS_GET_BIT(vpw_bitmap, port) != SNPS_CINIT_SET) {
            continue;
        }

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCFGWQOS1);

        SNPS_WRITE_FIELD(reg_val, PCFGWQOS1_WQOS_MAP_TIMEOUT1, QDYN_FIELD(cinit_cfg, wqos_map_timeout1[port]));
        SNPS_WRITE_FIELD(reg_val, PCFGWQOS1_WQOS_MAP_TIMEOUT2, QDYN_FIELD(cinit_cfg, wqos_map_timeout2[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCFGWQOS1, reg_val);
    }
}

#ifdef UMCTL2_A_SAR_0
#ifdef UMCTL2_INCL_ARB_OR_CHB
/**
 * @brief function to setup the register field values for sarbase
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SARBASE(SubsysHdlr_t *cinit_cfg, uint32_t addr_n)
{
    uint32_t reg_val;
    uint32_t addr_offset;

    addr_offset = SARBASE0 + (addr_n * SNPS_8_BYTES);

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + addr_offset);

    SNPS_WRITE_FIELD(reg_val, SARBASE0_BASE_ADDR, STATIC_FIELD(cinit_cfg, base_addr[addr_n]));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + addr_offset, reg_val);
}

/**
 * @brief function to setup the register field values for sarsize
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SARSIZE(SubsysHdlr_t *cinit_cfg, uint32_t addr_n)
{
    uint32_t reg_val;
    uint32_t addr_offset;

    addr_offset = SARSIZE0 + (addr_n * SNPS_8_BYTES);

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + addr_offset);

    SNPS_WRITE_FIELD(reg_val, SARSIZE0_NBLOCKS, STATIC_FIELD(cinit_cfg, nblocks[addr_n]));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + addr_offset, reg_val);
}

#endif /* UMCTL2_INCL_ARB_OR_CHB */
#endif /* UMCTL2_A_SAR_0 */

/**
 * @brief function to setup the register field values for sbrctl
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRCTL(SubsysHdlr_t *cinit_cfg)
{
#if defined(DDRCTL_ARB_OR_CHB_OR_HIF_SBR_EN) && defined(UMCTL2_SBR_EN_1)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRCTL);

    CONSTRAIN_INSIDE(DYN_FIELD(cinit_cfg, scrub_burst_length_nm), 1, 6);
    CONSTRAIN_INSIDE(DYN_FIELD(cinit_cfg, scrub_burst_length_lp), 1, 6);
    CONSTRAIN_MAX(DYN_FIELD(cinit_cfg, scrub_cmd_type), 1);

    SNPS_WRITE_FIELD(reg_val, SBRCTL_SCRUB_EN, DYN_FIELD(cinit_cfg, scrub_en));
    SNPS_WRITE_FIELD(reg_val, SBRCTL_SCRUB_DURING_LOWPOWER, DYN_FIELD(cinit_cfg, scrub_during_lowpower));
#ifdef UMCTL2_DUAL_CHANNEL
    SNPS_WRITE_FIELD(reg_val, SBRCTL_SCRUB_EN_DCH1, DYN_FIELD(cinit_cfg, scrub_en_dch1));
#endif /* UMCTL2_DUAL_CHANNEL */
    SNPS_WRITE_FIELD(reg_val, SBRCTL_SCRUB_BURST_LENGTH_NM, DYN_FIELD(cinit_cfg, scrub_burst_length_nm));
    SNPS_WRITE_FIELD(reg_val, SBRCTL_SCRUB_INTERVAL, DYN_FIELD(cinit_cfg, scrub_interval));

    SNPS_WRITE_FIELD(reg_val, SBRCTL_SCRUB_CMD_TYPE, DYN_FIELD(cinit_cfg, scrub_cmd_type));
    SNPS_WRITE_FIELD(reg_val, SBRCTL_SBR_CORRECTION_MODE, DYN_FIELD(cinit_cfg, sbr_correction_mode));
    SNPS_WRITE_FIELD(reg_val, SBRCTL_SCRUB_BURST_LENGTH_LP, DYN_FIELD(cinit_cfg, scrub_burst_length_lp));
#ifdef MEMC_SIDEBAND_ECC
#ifdef DDRCTL_KBD_SBECC_EN_1
    SNPS_WRITE_FIELD(reg_val, SBRCTL_SCRUB_UE, DYN_FIELD(cinit_cfg, scrub_ue));
#endif /* DDRCTL_KBD_SBECC_EN_1 */
#endif /* MEMC_SIDEBAND_ECC */

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRCTL, reg_val);
#endif /* UMCTL2_INCL_ARB_OR_CHB && UMCTL2_SBR_EN_1 */
}


/**
 * @brief function to setup the register field values for sbrwdata0
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRWDATA0(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_SBR_EN_1
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRWDATA0);

    SNPS_WRITE_FIELD(reg_val, SBRWDATA0_SCRUB_PATTERN0, DYN_FIELD(cinit_cfg, scrub_pattern0));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRWDATA0, reg_val);
#endif /* UMCTL2_SBR_EN_1 */
}


/**
 * @brief function to setup the register field values for sbrwdata1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRWDATA1(SubsysHdlr_t *cinit_cfg)
{
#if defined(UMCTL2_SBR_EN_1) && defined(MEMC_DRAM_DATA_WIDTH_64)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRWDATA1);
    
    SNPS_WRITE_FIELD(reg_val, SBRWDATA1_SCRUB_PATTERN1, DYN_FIELD(cinit_cfg, scrub_pattern1));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRWDATA1, reg_val);
#endif /* UMCTL2_SBR_EN_1 && MEMC_DRAM_DATA_WIDTH_64 */
}


/**
 * @brief function to setup the register field values for sbrstart0
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRSTART0(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_SBR_EN_1
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRSTART0);

    SNPS_WRITE_FIELD(reg_val, SBRSTART0_SBR_ADDRESS_START_MASK_0, DYN_FIELD(cinit_cfg, sbr_address_start_mask_0));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRSTART0, reg_val);
#endif /* UMCTL2_SBR_EN_1 */
}


/**
 * @brief function to setup the register field values for sbrstart1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRSTART1(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_SBR_EN_1
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRSTART1);

    SNPS_WRITE_FIELD(reg_val, SBRSTART1_SBR_ADDRESS_START_MASK_1, DYN_FIELD(cinit_cfg, sbr_address_start_mask_1));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRSTART1, reg_val);
#endif /* UMCTL2_SBR_EN_1 */
}


/**
 * @brief function to setup the register field values for sbrrange0
 */

static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRRANGE0(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_SBR_EN_1
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRRANGE0);

    SNPS_WRITE_FIELD(reg_val, SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0, DYN_FIELD(cinit_cfg, sbr_address_range_mask_0));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRRANGE0, reg_val);
#endif /* UMCTL2_SBR_EN_1 */
}


/**
 * @brief function to setup the register field values for sbrrange1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRRANGE1(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_SBR_EN_1
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRRANGE1);

    SNPS_WRITE_FIELD(reg_val, SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1, DYN_FIELD(cinit_cfg, sbr_address_range_mask_1));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRRANGE1, reg_val);
#endif /* UMCTL2_SBR_EN_1 */
}

/**
 * @brief function to setup the register field values for sbrstart0dch1
 */

static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRSTART0DCH1(SubsysHdlr_t *cinit_cfg)
{
#if defined(UMCTL2_SBR_EN_1) && defined(UMCTL2_DUAL_DATA_CHANNEL)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRSTART0DCH1);

    SNPS_WRITE_FIELD(reg_val, SBRSTART0DCH1_SBR_ADDRESS_START_MASK_DCH1_0,
                     DYN_FIELD(cinit_cfg, sbr_address_start_mask_dch1_0));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRSTART0DCH1, reg_val);
#endif /* UMCTL2_SBR_EN_1 && UMCTL2_DUAL_DATA_CHANNEL */
}


/**
 * @brief function to setup the register field values for sbrstart1dch1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRSTART1DCH1(SubsysHdlr_t *cinit_cfg)
{
#if defined(UMCTL2_SBR_EN_1) && defined(UMCTL2_DUAL_DATA_CHANNEL)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRSTART1DCH1);

    SNPS_WRITE_FIELD(reg_val, SBRSTART1DCH1_SBR_ADDRESS_START_MASK_DCH1_1,
                     DYN_FIELD(cinit_cfg, sbr_address_start_mask_dch1_1));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRSTART1DCH1, reg_val);
#endif /* UMCTL2_SBR_EN_1 && UMCTL2_DUAL_DATA_CHANNEL */
}


/**
 * @brief function to setup the register field values for sbrrange0dch1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRRANGE0DCH1(SubsysHdlr_t *cinit_cfg)
{
#if defined(UMCTL2_SBR_EN_1) && defined(UMCTL2_DUAL_DATA_CHANNEL)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRRANGE0DCH1);

    SNPS_WRITE_FIELD(reg_val, SBRRANGE0DCH1_SBR_ADDRESS_RANGE_MASK_DCH1_0,
                     DYN_FIELD(cinit_cfg, sbr_address_range_mask_dch1_0));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRRANGE0DCH1, reg_val);
#endif /* UMCTL2_SBR_EN_1 && UMCTL2_DUAL_DATA_CHANNEL */
}


/**
 * @brief function to setup the register field values for sbrrange1dch1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRRANGE1DCH1(SubsysHdlr_t *cinit_cfg)
{
#if defined(UMCTL2_SBR_EN_1) && defined(UMCTL2_DUAL_DATA_CHANNEL)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRRANGE1DCH1);
    
    SNPS_WRITE_FIELD(reg_val, SBRRANGE1DCH1_SBR_ADDRESS_RANGE_MASK_DCH1_1,
                     DYN_FIELD(cinit_cfg, sbr_address_range_mask_dch1_1));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRRANGE1DCH1, reg_val);
#endif /* UMCTL2_SBR_EN_1 && UMCTL2_DUAL_DATA_CHANNEL */
}


/**
 * @brief function to setup the register field values for pdch
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PDCH(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_INCL_ARB
#if !defined(UMCTL2_DATA_CHANNEL_INTERLEAVE_EN_1) && defined(UMCTL2_DUAL_DATA_CHANNEL)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + PDCH);

    // Program all ports, if they don't are available the write should not have impact
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_0, STATIC_FIELD(cinit_cfg, port_data_channel_0));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_1, STATIC_FIELD(cinit_cfg, port_data_channel_1));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_2, STATIC_FIELD(cinit_cfg, port_data_channel_2));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_3, STATIC_FIELD(cinit_cfg, port_data_channel_3));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_4, STATIC_FIELD(cinit_cfg, port_data_channel_4));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_5, STATIC_FIELD(cinit_cfg, port_data_channel_5));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_6, STATIC_FIELD(cinit_cfg, port_data_channel_6));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_7, STATIC_FIELD(cinit_cfg, port_data_channel_7));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_8, STATIC_FIELD(cinit_cfg, port_data_channel_8));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_9, STATIC_FIELD(cinit_cfg, port_data_channel_9));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_10, STATIC_FIELD(cinit_cfg, port_data_channel_10));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_11, STATIC_FIELD(cinit_cfg, port_data_channel_11));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_12, STATIC_FIELD(cinit_cfg, port_data_channel_12));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_13, STATIC_FIELD(cinit_cfg, port_data_channel_13));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_14, STATIC_FIELD(cinit_cfg, port_data_channel_14));
    SNPS_WRITE_FIELD(reg_val, PDCH_PORT_DATA_CHANNEL_15, STATIC_FIELD(cinit_cfg, port_data_channel_15));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + PDCH, reg_val);
#endif /* !UMCTL2_DATA_CHANNEL_INTERLEAVE_EN_1 && UMCTL2_DUAL_DATA_CHANNEL */
#endif /* UMCTL2_INCL_ARB_OR_CHB */
}


/**
 * @brief function to setup the register field values for sbrlpctl
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRLPCTL(SubsysHdlr_t *cinit_cfg)
{
#if defined(DDRCTL_DDR) && defined(UMCTL2_SBR_EN_1)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRLPCTL);

    CONSTRAIN_MAX(DYN_FIELD(cinit_cfg, perrank_dis_scrub), 3);
    SNPS_WRITE_FIELD(reg_val, SBRLPCTL_PERRANK_DIS_SCRUB, DYN_FIELD(cinit_cfg, perrank_dis_scrub));
    SNPS_WRITE_FIELD(reg_val, SBRLPCTL_SCRUB_RESTORE, DYN_FIELD(cinit_cfg, scrub_restore));
#ifdef UMCTL2_DUAL_CHANNEL
    CONSTRAIN_MAX(DYN_FIELD(cinit_cfg, perrank_dis_scrub_dch1), 3);
    SNPS_WRITE_FIELD(reg_val, SBRLPCTL_PERRANK_DIS_SCRUB_DCH1, DYN_FIELD(cinit_cfg, perrank_dis_scrub_dch1));
    SNPS_WRITE_FIELD(reg_val, SBRLPCTL_SCRUB_RESTORE_DCH1, DYN_FIELD(cinit_cfg, scrub_restore_dch1));
#endif

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRLPCTL, reg_val);
#endif /* DDRCTL_DDR && UMCTL2_SBR_EN_1 */
}


/**
 * @brief function to setup the register field values for sbraddrrestore0
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRADDRRESTORE0(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_SBR_EN_1
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRADDRRESTORE0);

    SNPS_WRITE_FIELD(reg_val, SBRADDRRESTORE0_SCRUB_RESTORE_ADDRESS0, DYN_FIELD(cinit_cfg, scrub_restore_address0));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRADDRRESTORE0, reg_val);
#endif /* UMCTL2_SBR_EN_1 */
}


/**
 * @brief function to setup the register field values for sbraddrrestore1
 */

static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRADDRRESTORE1(SubsysHdlr_t *cinit_cfg)
{
#ifdef UMCTL2_SBR_EN_1
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRADDRRESTORE1);

    SNPS_WRITE_FIELD(reg_val, SBRADDRRESTORE1_SCRUB_RESTORE_ADDRESS1,
                              DYN_FIELD(cinit_cfg, scrub_restore_address1));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRADDRRESTORE1, reg_val);
#endif /* UMCTL2_SBR_EN_1 */
}


/**
 * @brief function to setup the register field values for sbraddrrestore0dch1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRADDRRESTORE0DCH1(SubsysHdlr_t *cinit_cfg)
{
#if defined(UMCTL2_SBR_EN_1) && defined(UMCTL2_DUAL_DATA_CHANNEL)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRADDRRESTORE0DCH1);

    SNPS_WRITE_FIELD(reg_val, SBRADDRRESTORE0DCH1_SCRUB_RESTORE_ADDRESS0_DCH1,
                              DYN_FIELD(cinit_cfg, scrub_restore_address0_dch1));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRADDRRESTORE0DCH1, reg_val);
#endif /* UMCTL2_SBR_EN_1 && UMCTL2_DUAL_DATA_CHANNEL */
}


/**
 * @brief function to setup the register field values for sbraddrrestore1dch1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRADDRRESTORE1DCH1(SubsysHdlr_t *cinit_cfg)
{
#if defined(UMCTL2_SBR_EN_1) && defined(UMCTL2_DUAL_DATA_CHANNEL)
    uint32_t reg_val;

    reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(0) + SBRADDRRESTORE1DCH1);

    SNPS_WRITE_FIELD(reg_val, SBRADDRRESTORE1DCH1_SCRUB_RESTORE_ADDRESS1_DCH1,
                              DYN_FIELD(cinit_cfg, scrub_restore_address1_dch1));

    ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(0) + SBRADDRRESTORE1DCH1, reg_val);
#endif /* UMCTL2_SBR_EN_1 && UMCTL2_DUAL_DATA_CHANNEL */
}


/**
 * @brief function to setup the register field values for pchblctrl
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBLCTRL(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBLCTRL);

        SNPS_WRITE_FIELD(reg_val, PCHBLCTRL_TXSACTIVE_EN, DYN_FIELD(cinit_cfg, txsactive_en[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBLCTRL, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbtctrl
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBTCTRL(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBTCTRL);

        SNPS_WRITE_FIELD(reg_val, PCHBTCTRL_DIS_PREFETCH, DYN_FIELD(cinit_cfg, dis_prefetch[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBTCTRL_CRC_UE_RSP_SEL, DYN_FIELD(cinit_cfg, crc_ue_rsp_sel[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBTCTRL_DBG_FORCE_PCRD_STEAL_MODE,
                         DYN_FIELD(cinit_cfg, dbg_force_pcrd_steal_mode[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBTCTRL_DBG_WDC_EN, DYN_FIELD(cinit_cfg, dbg_wdc_en[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBTCTRL, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbprctmr
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBPRCTMR(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBPRCTMR);

        SNPS_WRITE_FIELD(reg_val, PCHBPRCTMR_PRC_EXP_CNT, STATIC_FIELD(cinit_cfg, prc_exp_cnt[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBPRCTMR_EXP_CNT_DIV, STATIC_FIELD(cinit_cfg, exp_cnt_div[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBPRCTMR, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbprotqctl
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBPROTQCTL(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBPROTQCTL);

        SNPS_WRITE_FIELD(reg_val, PCHBPROTQCTL_RPQ_LPR_MIN, STATIC_FIELD(cinit_cfg, rpq_lpr_min[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBPROTQCTL_RPQ_HPR_MIN, STATIC_FIELD(cinit_cfg, rpq_hpr_min[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBPROTQCTL, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbrqos0
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBRQOS0(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBRQOS0);

        SNPS_WRITE_FIELD(reg_val, PCHBRQOS0_CHB_RQOS_MAP_LEVEL1, QDYN_FIELD(cinit_cfg, chb_rqos_map_level1[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBRQOS0_CHB_RQOS_MAP_LEVEL2, QDYN_FIELD(cinit_cfg, chb_rqos_map_level2[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBRQOS0_CHB_RQOS_MAP_REGION0, QDYN_FIELD(cinit_cfg, chb_rqos_map_region0[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBRQOS0_CHB_RQOS_MAP_REGION1, QDYN_FIELD(cinit_cfg, chb_rqos_map_region1[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBRQOS0_CHB_RQOS_MAP_REGION2, QDYN_FIELD(cinit_cfg, chb_rqos_map_region2[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBRQOS0, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbrqos1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBRQOS1(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBRQOS1);

        SNPS_WRITE_FIELD(reg_val, PCHBRQOS1_VPR_UNCRD_TIMEOUT, QDYN_FIELD(cinit_cfg, vpr_uncrd_timeout[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBRQOS1_VPR_CRD_TIMEOUT, QDYN_FIELD(cinit_cfg, vpr_crd_timeout[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBRQOS1, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbwqos0
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBWQOS0(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBWQOS0);

        SNPS_WRITE_FIELD(reg_val, PCHBWQOS0_CHB_WQOS_MAP_LEVEL1, QDYN_FIELD(cinit_cfg, chb_wqos_map_level1[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBWQOS0_CHB_WQOS_MAP_LEVEL2, QDYN_FIELD(cinit_cfg, chb_wqos_map_level2[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBWQOS0_CHB_WQOS_MAP_REGION0, QDYN_FIELD(cinit_cfg, chb_wqos_map_region0[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBWQOS0_CHB_WQOS_MAP_REGION1, QDYN_FIELD(cinit_cfg, chb_wqos_map_region1[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBWQOS0_CHB_WQOS_MAP_REGION2, QDYN_FIELD(cinit_cfg, chb_wqos_map_region2[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBWQOS0, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbwqos1
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBWQOS1(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBWQOS1);

        SNPS_WRITE_FIELD(reg_val, PCHBWQOS1_VPW_UNCRD_TIMEOUT, QDYN_FIELD(cinit_cfg, vpw_uncrd_timeout[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBWQOS1_VPW_CRD_TIMEOUT, QDYN_FIELD(cinit_cfg, vpw_crd_timeout[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBWQOS1, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbcbusyh
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBCBUSYH(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBCBUSYH);

        SNPS_WRITE_FIELD(reg_val, PCHBCBUSYH_CAM_BUSY_THRESHOLD_HPR,
                         STATIC_FIELD(cinit_cfg, cam_busy_threshold_hpr[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBCBUSYH_CAM_FREE_THRESHOLD_HPR,
                         STATIC_FIELD(cinit_cfg, cam_free_threshold_hpr[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBCBUSYH_CAM_MIDDLE_THRESHOLD_HPR,
                         STATIC_FIELD(cinit_cfg, cam_middle_threshold_hpr[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBCBUSYH, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbcbusyl
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBCBUSYL(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBCBUSYL);

        SNPS_WRITE_FIELD(reg_val, PCHBCBUSYL_CAM_BUSY_THRESHOLD_LPR,
                         STATIC_FIELD(cinit_cfg, cam_busy_threshold_lpr[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBCBUSYL_CAM_FREE_THRESHOLD_LPR,
                         STATIC_FIELD(cinit_cfg, cam_free_threshold_lpr[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBCBUSYL_CAM_MIDDLE_THRESHOLD_LPR,
                         STATIC_FIELD(cinit_cfg, cam_middle_threshold_lpr[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBCBUSYL, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}


/**
 * @brief function to setup the register field values for pchbcbusyw
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBCBUSYW(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_INCL_CHB
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBCBUSYW);

        SNPS_WRITE_FIELD(reg_val, PCHBCBUSYW_CAM_BUSY_THRESHOLD_WR,
                         STATIC_FIELD(cinit_cfg, cam_busy_threshold_wr[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBCBUSYW_CAM_FREE_THRESHOLD_WR,
                         STATIC_FIELD(cinit_cfg, cam_free_threshold_wr[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBCBUSYW_CAM_MIDDLE_THRESHOLD_WR,
                         STATIC_FIELD(cinit_cfg, cam_middle_threshold_wr[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBCBUSYW, reg_val);
    }
#endif /* DDRCTL_INCL_CHB */
}

#ifdef DDRCTL_CHB_TZ_EN
/**
 * @brief function to setup the register field values for pchbcbusyw
 */
static void dwc_ddrctl_cinit_prgm_REGB_ARB_PCHBTZACT(SubsysHdlr_t *cinit_cfg)
{
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBTZACT);

        SNPS_WRITE_FIELD(reg_val, PCHBTZACT_TZ_INT_ENABLE, DYN_FIELD(cinit_cfg, tz_int_enable[port]));
        SNPS_WRITE_FIELD(reg_val, PCHBTZACT_TZ_RESPERR_ENABLE, DYN_FIELD(cinit_cfg, tz_resperr_enable[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBTZACT, reg_val);
    }
}

static void dwc_ddrctl_cinit_prgm_REGB_ARB_PCHBTZINTCLR(SubsysHdlr_t *cinit_cfg)
{
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBTZINTCLR);

        SNPS_WRITE_FIELD(reg_val, PCHBTZINTCLR_TZ_INT_CLEAR, DYN_FIELD(cinit_cfg, tz_int_clear[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBTZINTCLR, reg_val);
    }
}

static void dwc_ddrctl_cinit_prgm_REGB_ARB_PCHBTZCTRL(SubsysHdlr_t *cinit_cfg)
{
    uint32_t reg_val;
    uint8_t  port;

    for (port = 0; port < UMCTL2_A_NPORTS; port++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBTZCTRL);

        SNPS_WRITE_FIELD(reg_val, PCHBTZCTRL_TZ_SEC_INV_EN, STATIC_FIELD(cinit_cfg, tz_sec_inv_en[port]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBTZCTRL, reg_val);
    }
}

static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBTZRSETL(SubsysHdlr_t *cinit_cfg, uint32_t port)
{
    uint32_t reg_val;
    uint8_t  tz_region;

    for (tz_region = 0; tz_region < DDRCTL_CHB_TSZ_REG_NUM; tz_region++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBTZRSETL0 + (tz_region * SNPS_16_BYTES));

        SNPS_WRITE_FIELD(reg_val, PCHBTZRSETL0_TZ_BASE_ADDR_LOW,
                         STATIC_FIELD(cinit_cfg, tz_base_addr_low[port][tz_region]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBTZRSETL0 + (tz_region * SNPS_16_BYTES), reg_val);
    }
}

static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBTZRSETH(SubsysHdlr_t *cinit_cfg, uint32_t port)
{
    uint32_t reg_val;
    uint8_t  tz_region;

    for (tz_region = 0; tz_region < DDRCTL_CHB_TSZ_REG_NUM; tz_region++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBTZRSETH0 + (tz_region * SNPS_16_BYTES));

        SNPS_WRITE_FIELD(reg_val, PCHBTZRSETH0_TZ_BASE_ADDR_HIGH,
                         STATIC_FIELD(cinit_cfg, tz_base_addr_high[port][tz_region]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBTZRSETH0 + (tz_region * SNPS_16_BYTES), reg_val);
    }
}

static void dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBTZRATTR(SubsysHdlr_t *cinit_cfg, uint32_t port)
{
    uint32_t reg_val;
    uint8_t  tz_region;

    for (tz_region = 0; tz_region < DDRCTL_CHB_TSZ_REG_NUM; tz_region++) {

        reg_val = dwc_ddrctl_cinit_io_read32(REGB_ARB_PORT_OFFSET(port) + PCHBTZRATTR0 + (tz_region * SNPS_16_BYTES));

        if (tz_region != 0) {
            SNPS_WRITE_FIELD(reg_val, PCHBTZRATTR1_TZ_REGION_EN,
                            STATIC_FIELD(cinit_cfg, tz_region_en[port][tz_region]));
            SNPS_WRITE_FIELD(reg_val, PCHBTZRATTR1_TZ_REGION_SIZE,
                            STATIC_FIELD(cinit_cfg, tz_region_size[port][tz_region]));
            SNPS_WRITE_FIELD(reg_val, PCHBTZRATTR1_TZ_SUBREGION_DISABLE,
                            STATIC_FIELD(cinit_cfg, tz_subregion_disable[port][tz_region]));
        }

        SNPS_WRITE_FIELD(reg_val, PCHBTZRATTR0_TZ_REG_SP,
                         STATIC_FIELD(cinit_cfg, tz_reg_sp[port][tz_region]));

        ddrctl_cinit_arb_port_write(REGB_ARB_PORT_OFFSET(port) + PCHBTZRATTR0 + (tz_region * SNPS_16_BYTES), reg_val);
    }
}
#endif /* DDRCTL_CHB_TZ_EN */

/**
 * @brief iterate through all ARB registers setting up a 32-bit value to
 * be programmed into each writable register.
 */
void ddrctl_cinit_prgm_block_arb_port(SubsysHdlr_t *cinit_cfg)
{
    uint8_t port;
    uint8_t n_sar;

    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCCFG(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGR(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGW(cinit_cfg);
    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGIDMASKCH(cinit_cfg, port);
        dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGIDVALUECH(cinit_cfg, port);
    }

#ifdef DDRCTL_ARB_OR_CHB_OR_HIF_SBR_EN

#ifdef UMCTL2_INCL_ARB_OR_CHB
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCTRL(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGQOS0(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGQOS1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGWQOS0(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCFGWQOS1(cinit_cfg);
#endif /* UMCTL2_INCL_ARB_OR_CHB */
#if defined(UMCTL2_INCL_ARB_OR_CHB) && defined(UMCTL2_A_SAR_0)
    for (n_sar = 0; n_sar < UMCTL2_A_NSAR; n_sar++) {
        dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SARBASE(cinit_cfg, n_sar);
        dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SARSIZE(cinit_cfg, n_sar);
    }
#endif /* UMCTL2_INCL_ARB_OR_CHB && UMCTL2_A_SAR_0 */

    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRCTL(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRWDATA0(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRWDATA1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRSTART0(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRSTART1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRRANGE0(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRRANGE1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRSTART0DCH1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRSTART1DCH1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRRANGE0DCH1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRRANGE1DCH1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PDCH(cinit_cfg);

#ifdef DDRCTL_DDR
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRLPCTL(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRADDRRESTORE0(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRADDRRESTORE1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRADDRRESTORE0DCH1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_SBRADDRRESTORE1DCH1(cinit_cfg);
#endif /* DDRCTL_DDR */

#ifdef DDRCTL_INCL_CHB
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBLCTRL(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBTCTRL(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBPRCTMR(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBPROTQCTL(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBRQOS0(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBRQOS1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBWQOS0(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBWQOS1(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBCBUSYH(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBCBUSYL(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBCBUSYW(cinit_cfg);
#endif /* DDRCTL_INCL_CHB */

#ifdef DDRCTL_CHB_TZ_EN
    dwc_ddrctl_cinit_prgm_REGB_ARB_PCHBTZACT(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PCHBTZINTCLR(cinit_cfg);
    dwc_ddrctl_cinit_prgm_REGB_ARB_PCHBTZCTRL(cinit_cfg);
    for (port = 0; port < UMCTL2_A_NPORTS; port++) {
        dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBTZRSETL(cinit_cfg, port);
        dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBTZRSETH(cinit_cfg, port);
        dwc_ddrctl_cinit_prgm_REGB_ARB_PORT_PCHBTZRATTR(cinit_cfg, port);
    }
#endif /* DDRCTL_CHB_TZ_EN */
#endif /* DDRCTL_ARB_OR_CHB_OR_HIF_SBR_EN */
}

