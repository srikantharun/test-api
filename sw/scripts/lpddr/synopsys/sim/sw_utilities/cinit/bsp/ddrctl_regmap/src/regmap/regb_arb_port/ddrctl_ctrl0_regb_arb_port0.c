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

#include "ddrctl_ctrl0_regb_arb_port0.h"

#include "ddrctl_regb_arb_port.h"

ddrctl_reg_t ctrl0_regb_arb_port0[] = {
    {0x00020000, "pccfg"    , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_pccfg    },
    {0x00020004, "pcfgr"    , 0x0000501f, 0x0000501f, SEC_NON_SECURE, reg_pcfgr    },
    {0x00020008, "pcfgw"    , 0x0000d01f, 0x0000d01f, SEC_NON_SECURE, reg_pcfgw    },
    {0x00020090, "pctrl"    , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_pctrl    },
    {0x00020094, "pcfgqos0" , 0x02000e00, 0x02000e00, SEC_NON_SECURE, reg_pcfgqos0 },
    {0x00020098, "pcfgqos1" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_pcfgqos1 },
    {0x0002009c, "pcfgwqos0", 0x00000e00, 0x00000e00, SEC_NON_SECURE, reg_pcfgwqos0},
    {0x000200a0, "pcfgwqos1", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_pcfgwqos1},
    {0x000200e0, "sbrctl"   , 0x9000ff10, 0x9000ff10, SEC_NON_SECURE, reg_sbrctl   },
    {0x000200e4, "sbrstat"  , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_sbrstat  },
    {0x000200e8, "sbrwdata0", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_sbrwdata0},
    {0x000200f0, "sbrstart0", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_sbrstart0},
    {0x000200f4, "sbrstart1", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_sbrstart1},
    {0x000200f8, "sbrrange0", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_sbrrange0},
    {0x000200fc, "sbrrange1", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_sbrrange1},
    {0x00020114, "pstat"    , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_pstat    },
    {0x00000000, NULL       , 0x00000000, 0x00000000, SEC_NON_SECURE, NULL         },
};
