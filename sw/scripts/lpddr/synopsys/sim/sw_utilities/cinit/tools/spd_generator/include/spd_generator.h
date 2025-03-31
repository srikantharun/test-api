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


#ifndef TOOLS_SPDGENERATOR_INCLUDE_SPD_GENERATOR_H_
#define TOOLS_SPDGENERATOR_INCLUDE_SPD_GENERATOR_H_

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>
#include <string.h>
#include <math.h>

#define MTB 125
#define FTB 1

#define DDR4_PROTOCOL    4
#define DDR5_PROTOCOL    5

typedef struct {
    uint8_t     verbose;
    uint32_t    flags;
    uint8_t     protocol;
    char       *spd_ini_path;
    char       *spd_bin_path;
} app_options_t;

#endif /* TOOLS_SPDGENERATOR_INCLUDE_SPD_GENERATOR_H_ */
