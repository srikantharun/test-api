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

#include "ddrctl_ctrl0_regb_freq2_ch0.h"

#include "ddrctl_regb_freq.h"

ddrctl_reg_t ctrl0_regb_freq2_ch0[] = {
    {0x00200000, "dramset1tmg0" , 0x0f101b0f, 0x0f101b0f, SEC_NON_SECURE, reg_dramset1tmg0 },
    {0x00200004, "dramset1tmg1" , 0x05080414, 0x05080414, SEC_NON_SECURE, reg_dramset1tmg1 },
    {0x00200008, "dramset1tmg2" , 0x0305060d, 0x0305060d, SEC_NON_SECURE, reg_dramset1tmg2 },
    {0x0020000c, "dramset1tmg3" , 0x00040404, 0x00040404, SEC_NON_SECURE, reg_dramset1tmg3 },
    {0x00200010, "dramset1tmg4" , 0x05040405, 0x05040405, SEC_NON_SECURE, reg_dramset1tmg4 },
    {0x00200014, "dramset1tmg5" , 0x05050403, 0x05050403, SEC_NON_SECURE, reg_dramset1tmg5 },
    {0x00200018, "dramset1tmg6" , 0x00000005, 0x00000005, SEC_NON_SECURE, reg_dramset1tmg6 },
    {0x0020001c, "dramset1tmg7" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dramset1tmg7 },
    {0x00200024, "dramset1tmg9" , 0x0004040d, 0x0004040d, SEC_NON_SECURE, reg_dramset1tmg9 },
    {0x00200030, "dramset1tmg12", 0x1a020010, 0x1a020010, SEC_NON_SECURE, reg_dramset1tmg12},
    {0x00200034, "dramset1tmg13", 0x1c200104, 0x1c200104, SEC_NON_SECURE, reg_dramset1tmg13},
    {0x00200038, "dramset1tmg14", 0x000800a0, 0x000800a0, SEC_NON_SECURE, reg_dramset1tmg14},
    {0x00200044, "dramset1tmg17", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dramset1tmg17},
    {0x0020005c, "dramset1tmg23", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dramset1tmg23},
    {0x00200060, "dramset1tmg24", 0x000f0f0f, 0x000f0f0f, SEC_NON_SECURE, reg_dramset1tmg24},
    {0x00200064, "dramset1tmg25", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dramset1tmg25},
    {0x00200078, "dramset1tmg30", 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dramset1tmg30},
    {0x00200080, "dramset1tmg32", 0x00030408, 0x00030408, SEC_NON_SECURE, reg_dramset1tmg32},
    {0x00200500, "initmr0"      , 0x00000510, 0x00000510, SEC_NON_SECURE, reg_initmr0      },
    {0x00200504, "initmr1"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_initmr1      },
    {0x00200508, "initmr2"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_initmr2      },
    {0x0020050c, "initmr3"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_initmr3      },
    {0x00200580, "dfitmg0"      , 0x07020002, 0x07020002, SEC_NON_SECURE, reg_dfitmg0      },
    {0x00200584, "dfitmg1"      , 0x00000404, 0x00000404, SEC_NON_SECURE, reg_dfitmg1      },
    {0x00200588, "dfitmg2"      , 0x00000202, 0x00000202, SEC_NON_SECURE, reg_dfitmg2      },
    {0x00200590, "dfitmg4"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dfitmg4      },
    {0x00200594, "dfitmg5"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dfitmg5      },
    {0x00200598, "dfitmg6"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dfitmg6      },
    {0x002005ac, "dfiupdtmg1"   , 0x00010001, 0x00010001, SEC_NON_SECURE, reg_dfiupdtmg1   },
    {0x002005b4, "dfiupdtmg2"   , 0xc000012c, 0xc000012c, SEC_NON_SECURE, reg_dfiupdtmg2   },
    {0x002005b8, "dfiupdtmg3"   , 0x00000001, 0x00000001, SEC_NON_SECURE, reg_dfiupdtmg3   },
    {0x00200600, "rfshset1tmg0" , 0x02100062, 0x02100062, SEC_NON_SECURE, reg_rfshset1tmg0 },
    {0x00200604, "rfshset1tmg1" , 0x0000008c, 0x0000008c, SEC_NON_SECURE, reg_rfshset1tmg1 },
    {0x00200608, "rfshset1tmg2" , 0x8c8c008c, 0x8c8c008c, SEC_NON_SECURE, reg_rfshset1tmg2 },
    {0x0020060c, "rfshset1tmg3" , 0x10000000, 0x10000000, SEC_NON_SECURE, reg_rfshset1tmg3 },
    {0x00200610, "rfshset1tmg4" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_rfshset1tmg4 },
    {0x00200650, "rfmset1tmg0"  , 0x0000008c, 0x0000008c, SEC_NON_SECURE, reg_rfmset1tmg0  },
    {0x00200800, "zqset1tmg0"   , 0x00400200, 0x00400200, SEC_NON_SECURE, reg_zqset1tmg0   },
    {0x00200804, "zqset1tmg1"   , 0x02000100, 0x02000100, SEC_NON_SECURE, reg_zqset1tmg1   },
    {0x00200808, "zqset1tmg2"   , 0x00000018, 0x00000018, SEC_NON_SECURE, reg_zqset1tmg2   },
    {0x00200a80, "dqsoscctl0"   , 0x00000070, 0x00000070, SEC_NON_SECURE, reg_dqsoscctl0   },
    {0x00200b00, "derateint"    , 0x00800000, 0x00800000, SEC_NON_SECURE, reg_derateint    },
    {0x00200b04, "derateval0"   , 0x050f0504, 0x050f0504, SEC_NON_SECURE, reg_derateval0   },
    {0x00200b08, "derateval1"   , 0x00000514, 0x00000514, SEC_NON_SECURE, reg_derateval1   },
    {0x00200b80, "hwlptmg0"     , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_hwlptmg0     },
    {0x00200b84, "dvfsctl0"     , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dvfsctl0     },
    {0x00200c00, "schedtmg0"    , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_schedtmg0    },
    {0x00200c80, "perfhpr1"     , 0x0f000001, 0x0f000001, SEC_NON_SECURE, reg_perfhpr1     },
    {0x00200c84, "perflpr1"     , 0x0f00007f, 0x0f00007f, SEC_NON_SECURE, reg_perflpr1     },
    {0x00200c88, "perfwr1"      , 0x0f00007f, 0x0f00007f, SEC_NON_SECURE, reg_perfwr1      },
    {0x00200d00, "tmgcfg"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_tmgcfg       },
    {0x00200d04, "ranktmg0"     , 0x00000606, 0x00000606, SEC_NON_SECURE, reg_ranktmg0     },
    {0x00200d08, "ranktmg1"     , 0x00000f0f, 0x00000f0f, SEC_NON_SECURE, reg_ranktmg1     },
    {0x00200d0c, "pwrtmg"       , 0x00400010, 0x00400010, SEC_NON_SECURE, reg_pwrtmg       },
    {0x00200d30, "ddr4pprtmg0"  , 0x002faf09, 0x002faf09, SEC_NON_SECURE, reg_ddr4pprtmg0  },
    {0x00200d34, "ddr4pprtmg1"  , 0x180009c5, 0x180009c5, SEC_NON_SECURE, reg_ddr4pprtmg1  },
    {0x00200d80, "lnkeccctl0"   , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkeccctl0   },
    {0x00000000, NULL           , 0x00000000, 0x00000000, SEC_NON_SECURE, NULL             },
};
