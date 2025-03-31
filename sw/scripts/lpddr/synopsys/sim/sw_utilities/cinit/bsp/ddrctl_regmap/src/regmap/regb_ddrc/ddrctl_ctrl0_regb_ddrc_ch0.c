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

#include "ddrctl_ctrl0_regb_ddrc_ch0.h"

#include "ddrctl_regb_ddrc.h"

ddrctl_reg_t ctrl0_regb_ddrc_ch0[] = {
    {0x00010000, "mstr0"            , 0x03040090, 0x03040090, SEC_NON_SECURE, reg_mstr0            },
    {0x00010008, "mstr2"            , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_mstr2            },
    {0x00010010, "mstr4"            , 0x00000100, 0x00000100, SEC_NON_SECURE, reg_mstr4            },
    {0x00010014, "stat"             , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_stat             },
    {0x00010080, "mrctrl0"          , 0x00000030, 0x00000030, SEC_NON_SECURE, reg_mrctrl0          },
    {0x00010084, "mrctrl1"          , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_mrctrl1          },
    {0x00010090, "mrstat"           , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_mrstat           },
    {0x00010094, "mrrdata0"         , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_mrrdata0         },
    {0x00010098, "mrrdata1"         , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_mrrdata1         },
    {0x00010100, "deratectl0"       , 0x00000020, 0x00000020, SEC_NON_SECURE, reg_deratectl0       },
    {0x00010104, "deratectl1"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_deratectl1       },
    {0x00010108, "deratectl2"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_deratectl2       },
    {0x00010114, "deratectl5"       , 0x00000001, 0x00000001, SEC_NON_SECURE, reg_deratectl5       },
    {0x00010118, "deratectl6"       , 0x00500000, 0x00500000, SEC_NON_SECURE, reg_deratectl6       },
    {0x00010120, "deratestat0"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_deratestat0      },
    {0x00010128, "deratedbgctl"     , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_deratedbgctl     },
    {0x0001012c, "deratedbgstat"    , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_deratedbgstat    },
    {0x00010180, "pwrctl"           , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_pwrctl           },
    {0x00010184, "hwlpctl"          , 0x00000203, 0x00000203, SEC_NON_SECURE, reg_hwlpctl          },
    {0x0001018c, "clkgatectl"       , 0x0000003f, 0x0000003f, SEC_NON_SECURE, reg_clkgatectl       },
    {0x00010200, "rfshmod0"         , 0x000f0000, 0x000f0000, SEC_NON_SECURE, reg_rfshmod0         },
    {0x00010208, "rfshctl0"         , 0x00006600, 0x00006600, SEC_NON_SECURE, reg_rfshctl0         },
    {0x00010220, "rfmmod0"          , 0x0a000100, 0x0a000100, SEC_NON_SECURE, reg_rfmmod0          },
    {0x00010224, "rfmmod1"          , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_rfmmod1          },
    {0x00010228, "rfmctl"           , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_rfmctl           },
    {0x0001022c, "rfmstat"          , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_rfmstat          },
    {0x00010280, "zqctl0"           , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_zqctl0           },
    {0x00010284, "zqctl1"           , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_zqctl1           },
    {0x00010288, "zqctl2"           , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_zqctl2           },
    {0x0001028c, "zqstat"           , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_zqstat           },
    {0x00010300, "dqsoscruntime"    , 0x00400040, 0x00400040, SEC_NON_SECURE, reg_dqsoscruntime    },
    {0x00010304, "dqsoscstat0"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dqsoscstat0      },
    {0x00010308, "dqsosccfg0"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dqsosccfg0       },
    {0x00010380, "sched0"           , 0x9001201c, 0x9001201c, SEC_NON_SECURE, reg_sched0           },
    {0x00010384, "sched1"           , 0x00002000, 0x00002000, SEC_NON_SECURE, reg_sched1           },
    {0x0001038c, "sched3"           , 0x04040208, 0x04040208, SEC_NON_SECURE, reg_sched3           },
    {0x00010390, "sched4"           , 0x08400810, 0x08400810, SEC_NON_SECURE, reg_sched4           },
    {0x00010394, "sched5"           , 0x10000204, 0x10000204, SEC_NON_SECURE, reg_sched5           },
    {0x00010400, "hwffcctl"         , 0x04000010, 0x04000010, SEC_NON_SECURE, reg_hwffcctl         },
    {0x00010404, "hwffcstat"        , 0x00000300, 0x00000300, SEC_NON_SECURE, reg_hwffcstat        },
    {0x00010500, "dfilpcfg0"        , 0x00100000, 0x00100000, SEC_NON_SECURE, reg_dfilpcfg0        },
    {0x00010508, "dfiupd0"          , 0x00008000, 0x00008000, SEC_NON_SECURE, reg_dfiupd0          },
    {0x00010510, "dfimisc"          , 0x00000041, 0x00000041, SEC_NON_SECURE, reg_dfimisc          },
    {0x00010514, "dfistat"          , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_dfistat          },
    {0x00010518, "dfiphymstr"       , 0x80000001, 0x80000001, SEC_NON_SECURE, reg_dfiphymstr       },
    {0x00010580, "poisoncfg"        , 0x00110011, 0x00110011, SEC_NON_SECURE, reg_poisoncfg        },
    {0x00010584, "poisonstat"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_poisonstat       },
    {0x00010600, "ecccfg0"          , 0x033f7f40, 0x033f7f40, SEC_NON_SECURE, reg_ecccfg0          },
    {0x00010604, "ecccfg1"          , 0x00001fb0, 0x00001fb0, SEC_NON_SECURE, reg_ecccfg1          },
    {0x00010608, "eccstat"          , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccstat          },
    {0x0001060c, "eccctl"           , 0x00000700, 0x00000700, SEC_NON_SECURE, reg_eccctl           },
    {0x00010610, "eccerrcnt"        , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccerrcnt        },
    {0x00010614, "ecccaddr0"        , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_ecccaddr0        },
    {0x00010618, "ecccaddr1"        , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_ecccaddr1        },
    {0x0001061c, "ecccsyn0"         , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_ecccsyn0         },
    {0x00010620, "ecccsyn1"         , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_ecccsyn1         },
    {0x00010624, "ecccsyn2"         , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_ecccsyn2         },
    {0x00010628, "eccbitmask0"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccbitmask0      },
    {0x0001062c, "eccbitmask1"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccbitmask1      },
    {0x00010630, "eccbitmask2"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccbitmask2      },
    {0x00010634, "eccuaddr0"        , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccuaddr0        },
    {0x00010638, "eccuaddr1"        , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccuaddr1        },
    {0x0001063c, "eccusyn0"         , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccusyn0         },
    {0x00010640, "eccusyn1"         , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccusyn1         },
    {0x00010644, "eccusyn2"         , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccusyn2         },
    {0x00010648, "eccpoisonaddr0"   , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccpoisonaddr0   },
    {0x0001064c, "eccpoisonaddr1"   , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccpoisonaddr1   },
    {0x00010658, "eccpoisonpat0"    , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccpoisonpat0    },
    {0x00010660, "eccpoisonpat2"    , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccpoisonpat2    },
    {0x00010664, "eccapstat"        , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_eccapstat        },
    {0x00010984, "lnkeccctl1"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkeccctl1       },
    {0x00010988, "lnkeccpoisonctl0" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkeccpoisonctl0 },
    {0x0001098c, "lnkeccpoisonstat" , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkeccpoisonstat },
    {0x00010990, "lnkeccindex"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkeccindex      },
    {0x00010994, "lnkeccerrcnt0"    , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkeccerrcnt0    },
    {0x00010998, "lnkeccerrstat"    , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkeccerrstat    },
    {0x000109e0, "lnkecccaddr0"     , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkecccaddr0     },
    {0x000109e4, "lnkecccaddr1"     , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkecccaddr1     },
    {0x000109e8, "lnkeccuaddr0"     , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkeccuaddr0     },
    {0x000109ec, "lnkeccuaddr1"     , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_lnkeccuaddr1     },
    {0x00010b80, "opctrl0"          , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_opctrl0          },
    {0x00010b84, "opctrl1"          , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_opctrl1          },
    {0x00010b88, "opctrlcam"        , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_opctrlcam        },
    {0x00010b8c, "opctrlcmd"        , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_opctrlcmd        },
    {0x00010b90, "opctrlstat"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_opctrlstat       },
    {0x00010b94, "opctrlcam1"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_opctrlcam1       },
    {0x00010b98, "oprefctrl0"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_oprefctrl0       },
    {0x00010ba0, "oprefstat0"       , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_oprefstat0       },
    {0x00010c80, "swctl"            , 0x00000001, 0x00000001, SEC_NON_SECURE, reg_swctl            },
    {0x00010c84, "swstat"           , 0x00000001, 0x00000001, SEC_NON_SECURE, reg_swstat           },
    {0x00010c90, "rankctl"          , 0x000f000f, 0x000f000f, SEC_NON_SECURE, reg_rankctl          },
    {0x00010c94, "dbictl"           , 0x00000001, 0x00000001, SEC_NON_SECURE, reg_dbictl           },
    {0x00010c9c, "odtmap"           , 0x00002211, 0x00002211, SEC_NON_SECURE, reg_odtmap           },
    {0x00010ca0, "datactl0"         , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_datactl0         },
    {0x00010ca4, "swctlstatic"      , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_swctlstatic      },
    {0x00010cb0, "cgctl"            , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_cgctl            },
    {0x00010d00, "inittmg0"         , 0x0002004e, 0x0002004e, SEC_NON_SECURE, reg_inittmg0         },
    {0x00010f00, "ppt2ctrl0"        , 0x80008200, 0x80008200, SEC_NON_SECURE, reg_ppt2ctrl0        },
    {0x00010f10, "ppt2stat0"        , 0x00000000, 0x00000000, SEC_NON_SECURE, reg_ppt2stat0        },
    {0x00010ff8, "ddrctl_ver_number", 0x3136302a, 0x3136302a, SEC_NON_SECURE, reg_ddrctl_ver_number},
    {0x00010ffc, "ddrctl_ver_type"  , 0x6c633030, 0x6c633030, SEC_NON_SECURE, reg_ddrctl_ver_type  },
    {0x00000000, NULL               , 0x00000000, 0x00000000, SEC_NON_SECURE, NULL                 },
};
