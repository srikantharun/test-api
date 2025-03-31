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


#ifndef __DWC_DDRCTL_CINIT_HELPERS_H__
#define __DWC_DDRCTL_CINIT_HELPERS_H__

/**
 * Miscellaneous
 */

#define SNPS_CINIT_SET            1
#define SNPS_CINIT_CLEAR        0

#define SNPS_4_BYTES            4
#define SNPS_8_BYTES            8
#define SNPS_12_BYTES           12
#define SNPS_16_BYTES           16
#define SNPS_MAX_CHANNELS        16

#define RANGE(a, b, c)        ((a) >= (b) && (a) <= (c))

#define CFG            hdlr

/**
 * Configuration helpers
 */

/**
 * Controller registers helpers
 */

#define REGB_FREQ_CH0(f)    g_ctrl_regs.REGB[f].FREQ_CH[0]
#define REGB_FREQ_CH1(f)    g_ctrl_regs.REGB[f].FREQ_CH[1]

#define REGB_DDRC_CH0        g_ctrl_regs.REGB[0].DDRC_CH0
#define REGB_DDRC_CH1        g_ctrl_regs.REGB[0].DDRC_CH1

#define REGB_ARB_PORT(p)    g_ctrl_regs.REGB[0].ARB_PORT[p]

#define REGB_ADDR_MAP0        g_ctrl_regs.REGB[0].ADDR_MAP0
#define REGB_ADDR_MAP1        g_ctrl_regs.REGB[0].ADDR_MAP1

#define REGB_IME_CH0        g_ctrl_regs.REGB[0].IME_CH0
#define REGB_IME_CH1        g_ctrl_regs.REGB[0].IME_CH1


#define STATIC_FIELD(cinit_cfg, field)   cinit_cfg->memCtrlr_m.static_cfg.field
#define QDYN_FIELD(cinit_cfg, field)     cinit_cfg->memCtrlr_m.qdyn_cfg.field
#define DYN_FIELD(cinit_cfg, field)      cinit_cfg->memCtrlr_m.dyn_cfg.field


#define STATIC            CFG->memCtrlr_m.static_cfg

#define STATIC_CFG(PTR, FIELD) \
    (PTR->FIELD = STATIC.FIELD)

#define STATIC_CFG_ARRAY(PTR, FIELD, INDEX) \
    (PTR[INDEX]->FIELD = STATIC.FIELD[INDEX])

#define STATIC_CFG_MATRIX(PTR, FIELD, INDEX1, INDEX2) \
    (PTR[INDEX1]->FIELD = STATIC.FIELD[INDEX2][INDEX1])

#define QDYN            CFG->memCtrlr_m.qdyn_cfg

#define QDYN_CFG(PTR, FIELD) \
    (PTR->FIELD = QDYN.FIELD)

#define QDYN_CFG_ARRAY(PTR, FIELD, INDEX) \
    (PTR[INDEX]->FIELD = QDYN.FIELD[INDEX])

#define QDYN_CFG_MATRIX(PTR, FIELD, INDEX1, INDEX2) \
    (PTR[INDEX1]->FIELD = QDYN.FIELD[INDEX2][INDEX1])

#define DYN            CFG->memCtrlr_m.dyn_cfg

#define DYN_CFG(PTR, FIELD) \
    (PTR->FIELD = DYN.FIELD)

#define DYN_CFG_ARRAY(PTR, FIELD, INDEX) \
    (PTR[INDEX]->FIELD = DYN.FIELD[INDEX])

#define DYN_CFG_MATRIX(PTR, FIELD, INDEX1, INDEX2) \
    (PTR[INDEX1]->FIELD = DYN.FIELD[INDEX2][INDEX1])

#define PRE_CFG            CFG->memCtrlr_m.pre_cfg

#define DDR5_MR CFG->memCtrlr_m.ddr5_mr
#define DDR4_MR CFG->memCtrlr_m.ddr4_mr
#define DDR5_CW CFG->ddr5_cw
#define DDR4_CW CFG->ddr4_cw
#define LPDDR4_MR CFG->memCtrlr_m.lpddr4_mr
#define LPDDR5_MR CFG->memCtrlr_m.lpddr5_mr

/**
 * SPD helpers
 */

#define SPD            CFG->spdData_m

#define DU_THRES        CFG->ddr5_pasdu_thres


#define DDRCTL_GET_PROTOCOL(cfg)    ((cfg)->spdData_m.sdram_protocol)

#define IS_DDR4            (SPD.sdram_protocol == DWC_DDR4)
#define IS_DDR5            (SPD.sdram_protocol == DWC_DDR5)
#define IS_LPDDR4        (SPD.sdram_protocol == DWC_LPDDR4)
#define IS_LPDDR5        (SPD.sdram_protocol == DWC_LPDDR5)

#define DDRCTL_GET_DIMM_TYPE(cfg, dev)    ((cfg)->spdData_m.module_type)

#define IS_NODIMM        (SPD.module_type == DWC_NODIMM)
#define IS_UDIMM        (SPD.module_type == DWC_UDIMM)
#define IS_RDIMM        (SPD.module_type == DWC_RDIMM)
#define IS_LRDIMM        (SPD.module_type == DWC_LRDIMM)

#define IS_HIF_CONFIG        (DDRCTL_SYS_INTF == 0)
#define IS_ARB_CONFIG        (DDRCTL_SYS_INTF == 1)
#define IS_CHI_CONFIG        (DDRCTL_SYS_INTF == 2)

#define DRAM_RAW(n)        (SPD.dram_raw[n])
#define DRAM_CAW(n)        (SPD.dram_caw[n])
#define DRAM_BAW(n)        (SPD.dram_baw[n])
#define DRAM_BGW(n)        (SPD.dram_bgw[n])
#define CID_WIDTH(n)        (SPD.cid_width[n])

#define MEM_RAW(n)        ((DRAM_RAW(n) >= MRAM_RAW) ? DRAM_RAW(n) : MRAM_RAW)
#define MEM_CAW(n)        ((DRAM_CAW(n) >= MRAM_CAW) ? DRAM_CAW(n) : MRAM_CAW)
#define MEM_BAW(n)        ((DRAM_BAW(n) >= MRAM_BAW) ? DRAM_BAW(n) : MRAM_BAW)
#define MEM_BGW(n)        ((DRAM_BGW(n) >= MRAM_BGW) ? DRAM_BGW(n) : MRAM_BGW)

#define IS_X4(n)        (SPD.sdram_width_bits[n] == 4)
#define IS_X8(n)        (SPD.sdram_width_bits[n] == 8)
#define IS_X16(n)        (SPD.sdram_width_bits[n] == 16)

#define DDRCTL_GET_MEM_DENSITY(cfg, dev)    ((cfg)->spdData_m.sdram_capacity_mbits[dev])

#define IS_DENS_512MBIT(n)	(SPD.sdram_capacity_mbits[n] == 512)
#define IS_DENS_1GBIT(n)	(SPD.sdram_capacity_mbits[n] == 1024)
#define IS_DENS_2GBIT(n)	(SPD.sdram_capacity_mbits[n] == 2048)
#define IS_DENS_3GBIT(n)	(SPD.sdram_capacity_mbits[n] == 3072)
#define IS_DENS_4GBIT(n)	(SPD.sdram_capacity_mbits[n] == 4096)
#define IS_DENS_6GBIT(n)	(SPD.sdram_capacity_mbits[n] == 6144)
#define IS_DENS_8GBIT(n)	(SPD.sdram_capacity_mbits[n] == 8192)
#define IS_DENS_16GBIT(n)	(SPD.sdram_capacity_mbits[n] == 16384)
#define IS_DENS_24GBIT(n)	(SPD.sdram_capacity_mbits[n] == 24576)
#define IS_DENS_32GBIT(n)	(SPD.sdram_capacity_mbits[n] == 32768)
#define IS_DENS_64GBIT(n)	(SPD.sdram_capacity_mbits[n] == 65536)

/**
 * PHY Helpers
 */

#define PHY_TIMING        CFG->phy_timing_params

#endif /* __DWC_DDRCTL_CINIT_HELPERS_H__ */
