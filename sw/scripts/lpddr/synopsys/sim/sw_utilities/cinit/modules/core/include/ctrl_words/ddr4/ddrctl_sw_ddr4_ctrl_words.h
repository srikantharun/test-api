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


#ifndef __CORE_INCLUDE_DDR4_DDRCTL_SW_DDR4_CTRL_WORDS_H__
#define __CORE_INCLUDE_DDR4_DDRCTL_SW_DDR4_CTRL_WORDS_H__

#include "dwc_ddrctl_cinit.h"
#include "jedec/ddr5/cinit_ddr5_types.h"
#include "jedec/ddr5/cinit_ddr5_timing_utils.h"

typedef enum ddrctl_ddr4_rcd_cw_e {
    DDRCTL_DDR4_F0RC00 = 0x00,
    DDRCTL_DDR4_F0RC01 = 0x01,
    DDRCTL_DDR4_F0RC02 = 0x02,
    DDRCTL_DDR4_F0RC03 = 0x03,
    DDRCTL_DDR4_F0RC04 = 0x04,
    DDRCTL_DDR4_F0RC05 = 0x05,
    DDRCTL_DDR4_F0RC06 = 0x06,
    DDRCTL_DDR4_F0RC07 = 0x07,
    DDRCTL_DDR4_F0RC08 = 0x08,
    DDRCTL_DDR4_F0RC09 = 0x09,
    DDRCTL_DDR4_F0RC0A = 0x0A,
    DDRCTL_DDR4_F0RC0B = 0x0B,
    DDRCTL_DDR4_F0RC0C = 0x0C,
    DDRCTL_DDR4_F0RC0D = 0x0D,
    DDRCTL_DDR4_F0RC0E = 0x0E,
    DDRCTL_DDR4_F0RC0F = 0x0F,
    DDRCTL_DDR4_F0RC1X = 0x10,
    DDRCTL_DDR4_F0RC2X = 0x20,
    DDRCTL_DDR4_F0RC3X = 0x30,
    DDRCTL_DDR4_F0RC4X = 0x40,
    DDRCTL_DDR4_F0RC5X = 0x50,
    DDRCTL_DDR4_F0RC6X = 0x60,
    DDRCTL_DDR4_F0RC7X = 0x70,
    DDRCTL_DDR4_F0RC8X = 0x80,
    DDRCTL_DDR4_F0RC9X = 0x90,
    DDRCTL_DDR4_F0RCAX = 0xA0,
    DDRCTL_DDR4_F0RCBX = 0xB0,
    DDRCTL_DDR4_F0RCCX = 0xC0,
    DDRCTL_DDR4_F0RCDX = 0xD0,
    DDRCTL_DDR4_F0RCEX = 0xE0,
    DDRCTL_DDR4_F0RCFX = 0xF0
} ddrctl_ddr4_rcd_cw_t;


typedef enum ddrctl_ddr4_bcw_4b_e {
    DDRCTL_DDR4_BC00 = 0x00,
    DDRCTL_DDR4_BC01 = 0x01,
    DDRCTL_DDR4_BC02 = 0x02,
    DDRCTL_DDR4_BC03 = 0x03,
    DDRCTL_DDR4_BC04 = 0x04,
    DDRCTL_DDR4_BC05 = 0x05,
    DDRCTL_DDR4_BC06 = 0x06,
    DDRCTL_DDR4_BC07 = 0x07,
    DDRCTL_DDR4_BC08 = 0x08,
    DDRCTL_DDR4_BC09 = 0x09,
    DDRCTL_DDR4_BC0A = 0x10,
    DDRCTL_DDR4_BC0B = 0x11,
    DDRCTL_DDR4_BC0C = 0x12,
    DDRCTL_DDR4_BC0D = 0x13,
    DDRCTL_DDR4_BC0E = 0x14,
    DDRCTL_DDR4_BC0F = 0x15
} ddrctl_ddr4_bcw_4b_t;


typedef enum ddrctl_ddr4_bcw_8b_e {
    DDRCTL_DDR4_B7_0BC7x = 0x00,
    DDRCTL_DDR4_B0BC1x   = 0x01,
    DDRCTL_DDR4_B0BC6x   = 0x06,
    DDRCTL_DDR4_B0BCCx   = 0x0C,
    DDRCTL_DDR4_B0BCDx   = 0x0D,
    DDRCTL_DDR4_B0BCEx   = 0x0E,
    DDRCTL_DDR4_B0BCFx   = 0x0F
} ddrctl_ddr4_bcw_8b_t;

uint8_t ddrctl_sw_get_ddr4_rcd_cw(SubsysHdlr_t *cfg, ddrctl_ddr4_rcd_cw_t ctrl_word, uint8_t pstate);

ddrctl_error_t ddrctl_sw_get_ddr4_cw_op_speed_id(SubsysHdlr_t *cfg, uint32_t pstate, uint8_t *op_speed);

uint32_t dwc_ddrctl_cinit_get_rcx3_fg_op_speed(void);

uint8_t ddrctl_sw_get_ddr4_bcw_4b(SubsysHdlr_t *cfg, ddrctl_ddr4_bcw_4b_t bcw_num, uint8_t pstate);

uint8_t ddrctl_sw_get_ddr4_bcw_8b(SubsysHdlr_t *cfg, ddrctl_ddr4_bcw_8b_t bcw_num, uint8_t pstate);

#endif /* __CORE_INCLUDE_DDR4_DDRCTL_SW_DDR4_CTRL_WORDS_H__ */
