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


#include "spd_utils.h"

void reverse_calculation(uint32_t value, uint8_t* tMTB,  int8_t* tFTB)
{
    double tmp, rem, fcor;

    tmp = (double)value / (double)MTB;
    rem = fmod(tmp, 1);
    fcor = rem - 1;
    if (rem == 0) {
        *tMTB = tmp;
        *tFTB = 0;
    } else {
        *tMTB = ceil(tmp);
        *tFTB = (fcor * MTB) / FTB;
    }
}

uint16_t crc16_calc(uint8_t *ptr, uint16_t count)
{
    uint16_t crc, i;

    crc = 0;
    while (count-- > 0) {
                crc = crc ^ (uint16_t)*ptr++ << 8;
        for (i = 0; i < 8; ++i) {
            if (crc & 0x8000)
                crc = crc << 1 ^ 0x1021;
            else
                crc = crc << 1;
        }
    }

    return (crc & 0xFFFF);
}
