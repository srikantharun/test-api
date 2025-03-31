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

#include "ddrctl_ctrl0_regb_addr_map0.h"

#include "ddrctl_regb_addr_map.h"

ddrctl_reg_t ctrl0_regb_addr_map0[] = {
    {0x00030004, "addrmap1" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap1 },
    {0x0003000c, "addrmap3" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap3 },
    {0x00030010, "addrmap4" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap4 },
    {0x00030014, "addrmap5" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap5 },
    {0x00030018, "addrmap6" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap6 },
    {0x0003001c, "addrmap7" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap7 },
    {0x00030020, "addrmap8" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap8 },
    {0x00030024, "addrmap9" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap9 },
    {0x00030028, "addrmap10", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap10},
    {0x0003002c, "addrmap11", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap11},
    {0x00030030, "addrmap12", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_addrmap12},
    {0x00000000, NULL       , 0x00000000, 0x00000000, SEC_NON_SECURE, NULL         },
};
