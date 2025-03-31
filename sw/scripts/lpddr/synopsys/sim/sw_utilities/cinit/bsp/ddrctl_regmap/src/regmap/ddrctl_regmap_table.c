// ------------------------------------------------------------------------------
//
// Copyright 2023 Synopsys, INC.
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
// ------------------------------------------------------------------------------

#include "ddrctl_regmap_table.h"

#include "regb_freq/ddrctl_ctrl0_regb_freq0_ch0.h"
#include "regb_ddrc/ddrctl_ctrl0_regb_ddrc_ch0.h"
#include "regb_arb_port/ddrctl_ctrl0_regb_arb_port0.h"
#include "regb_addr_map/ddrctl_ctrl0_regb_addr_map0.h"
#include "regb_freq/ddrctl_ctrl0_regb_freq1_ch0.h"
#include "regb_freq/ddrctl_ctrl0_regb_freq2_ch0.h"
#include "regb_freq/ddrctl_ctrl0_regb_freq3_ch0.h"
#include "regb_freq/ddrctl_ctrl0_regb_freq0_ch0.h"
#include "regb_ddrc/ddrctl_ctrl0_regb_ddrc_ch0.h"
#include "regb_arb_port/ddrctl_ctrl0_regb_arb_port0.h"
#include "regb_addr_map/ddrctl_ctrl0_regb_addr_map0.h"
#include "regb_freq/ddrctl_ctrl0_regb_freq1_ch0.h"
#include "regb_freq/ddrctl_ctrl0_regb_freq2_ch0.h"
#include "regb_freq/ddrctl_ctrl0_regb_freq3_ch0.h"


const ddrctl_block_t g_ddrctl0_regmap[] = {
    {0x00000000, "regb_freq0_ch0" , ctrl0_regb_freq0_ch0},
    {0x00010000, "regb_ddrc_ch0"  , ctrl0_regb_ddrc_ch0},
    {0x00020000, "regb_arb_port0" , ctrl0_regb_arb_port0},
    {0x00030000, "regb_addr_map0" , ctrl0_regb_addr_map0},
    {0x00100000, "regb_freq1_ch0" , ctrl0_regb_freq1_ch0},
    {0x00200000, "regb_freq2_ch0" , ctrl0_regb_freq2_ch0},
    {0x00300000, "regb_freq3_ch0" , ctrl0_regb_freq3_ch0},
    {0x00000000, NULL             , NULL           },
};
const ddrctl_block_t g_ddrctl1_regmap[] =   {{0x00000000, NULL             , NULL           }};
