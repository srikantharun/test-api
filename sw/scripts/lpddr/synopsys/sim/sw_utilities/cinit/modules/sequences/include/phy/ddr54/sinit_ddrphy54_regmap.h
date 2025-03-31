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


#ifndef __SEQUENCES_INCLUDE_PHY_SINIT_DDRPHY54_REGMAP_H__
#define __SEQUENCES_INCLUDE_PHY_SINIT_DDRPHY54_REGMAP_H__

#define DDR54_PHY_BLOCK_ANIB            0x00000
#define DDR54_PHY_BLOCK_DBYTE           0x10000
#define DDR54_PHY_BLOCK_MASTER          0x20000
#define DDR54_PHY_BLOCK_ACSM            0x40000
#define DDR54_PHY_BLOCK_UCTL_MEMORY     0x50000
#define DDR54_PHY_BLOCK_PPGC            0x70000
#define DDR54_PHY_BLOCK_INITENG         0x90000
#define DDR54_PHY_BLOCK_PUB             0xC0000
#define DDR54_PHY_BLOCK_APBONLY         0xD0000


#define PHY_DQ_NIBBLE_OFFSET(dq_nibble)                         ((dq_nibble) * 0x100)
#define PHY_INSTAMCE_OFFSET(instance)                           ((instance) * 0x1000)
#define PHY_PSTATE_OFFSET(pstate)                               ((pstate) * 0x100000)


#define ATUDLY_PX(pstate, anibs_inst)                           ((DDR54_PHY_BLOCK_ANIB) + \
                                                                (PHY_PSTATE_OFFSET(pstate)) + \
                                                                (PHY_INSTAMCE_OFFSET(anibs_inst)) + 0x007F)
#define ATXDLY_PX(pstate, anibs_inst)                           ((DDR54_PHY_BLOCK_ANIB) + \
                                                                (PHY_PSTATE_OFFSET(pstate)) + \
                                                                (PHY_INSTAMCE_OFFSET(anibs_inst)) + 0x0080)
#define AT_DLY_FINE_MASK                                         0x0000003F
#define AT_DLY_FINE_BIT_OFFSET                                            0
#define AT_DLY_COARSE_MASK                                       0x000000C0
#define AT_DLY_COARSE_BIT_OFFSET                                          6


#define TXDQSDLYTG0_UY_PX(pstate, dbyte_inst, dq_nibble)        ((DDR54_PHY_BLOCK_DBYTE) + \
                                                                (PHY_PSTATE_OFFSET(pstate)) + \
                                                                (PHY_INSTAMCE_OFFSET(dbyte_inst)) + \
                                                                (PHY_DQ_NIBBLE_OFFSET(dq_nibble)) + 0x00D0)
                                                                
#define TXDQSDLYTG0                           ((DDR54_PHY_BLOCK_DBYTE)  + 0x00D0)
#define TXDQSDLYTG0_FINE_32_MASK                                       0x0000001F
#define TXDQSDLYTG0_FINE_64_MASK                                       0x0000003F
#define TXDQSDLYTG0_FINE_BIT_OFFSET                                             0
#define TXDQSDLYTG0_COARSE_MASK                                        0x000007C0
#define TXDQSDLYTG0_COARSE_BIT_OFFSET                                           6


#define TIMINGMODECNTRL                       ((DDR54_PHY_BLOCK_MASTER) + 0x0040)
#define TIMINGMODECNTRL_DLY64PREC_MASK                                 0x00000001
#define TIMINGMODECNTRL_DLY64PREC_BIT_OFFSET                                    0


#define MICROCONTMUXSEL                                          ((DDR54_PHY_BLOCK_APBONLY) + 0x0000)
#define MICROCONTMUXSEL_MASK                                                               0x00000001
#define MICROCONTMUXSEL_BIT_OFFSET                                                                  0
#define MICROCONTMUXSEL_CSR_CONTROL_ENABLE                                                          1
#define MICROCONTMUXSEL_CSR_CONTROL_DISABLE                                                         0


#define UCTSHADOWREGS                                            ((DDR54_PHY_BLOCK_APBONLY) + 0x0004)
#define UCTSHADOWREGS_UCTWRITEPROTSHADOW_MASK                                              0x00000001
#define UCTSHADOWREGS_UCTWRITEPROTSHADOW_BIT_OFFSET                                                 0
#define UCTSHADOWREGS_UCTDATWRITEPROTSHADOW_MASK                                           0x00000002
#define UCTSHADOWREGS_UCTDATWRITEPROTSHADOW_BIT_OFFSET                                              1

#define DCTWRITEPROT                                             ((DDR54_PHY_BLOCK_APBONLY) + 0x0031)
#define DCTWRITEPROT_MASK                                                                  0x00000001
#define DCTWRITEPROT_BIT_OFFSET                                                                     0

#define UCTWRITEONLYSHADOW                                       ((DDR54_PHY_BLOCK_APBONLY) + 0x0032)
#define UCTWRITEONLYSHADOW_MASK                                                            0x0000FFFF
#define UCTWRITEONLYSHADOW_BIT_OFFSET                                                               0

#define UCTDATWRITEONLYSHADOW                                    ((DDR54_PHY_BLOCK_APBONLY) + 0x0034)
#define UCTDATWRITEONLYSHADOW_MASK                                                        0x0000FFFF
#define UCTDATWRITEONLYSHADOW_BIT_OFFSET                                                           0


#endif /* __SEQUENCES_INCLUDE_PHY_SINIT_DDRPHY54_REGMAP_H__ */
