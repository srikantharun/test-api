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


#ifndef __DWC_DDRCTL_REG_MAP_MACROS_H__
#define __DWC_DDRCTL_REG_MAP_MACROS_H__

#include "dwc_ddrctl_reg_map.h"

#ifdef CINIT_ENABLE_REG_FORCE_WRITE
    #define CINIT_REG_FORCE_WRITE 1
#else
    #define CINIT_REG_FORCE_WRITE 0
#endif


#define DDRCTL_CTRL_INST0_BASE_ADDR     (hdlr->ddrctl_base_addr[0])
#define DDRCTL_CTRL_INST1_BASE_ADDR     (hdlr->ddrctl_base_addr[1])


#ifdef DDRCTL_SINGLE_INST_DUALCH
#define REG_GROUP_DDRC_CH_SIZE          (DDRCTL_CTRL_INST1_BASE_ADDR - DDRCTL_CTRL_INST0_BASE_ADDR)
#define REG_GROUP_IME_CH_SIZE           (DDRCTL_CTRL_INST1_BASE_ADDR - DDRCTL_CTRL_INST0_BASE_ADDR)
#elif defined(LPDDR_2MC1PHY)
#define REG_GROUP_DDRC_CH_SIZE          (0x01810000)
#define REG_GROUP_IME_CH_SIZE           (0x01810000)
#else
#define REG_GROUP_DDRC_CH_SIZE          (0x00001000)
#define REG_GROUP_IME_CH_SIZE           (0x00001000)
#endif /* DDRCTL_SINGLE_INST_DUALCH */

#define REG_GROUP_ARB_PORT_SIZE         (0x00001000)
#define REG_GROUP_FREQ_SIZE             (0x00100000)
#define REG_GROUP_ADDR_MAP_SIZE         (0x00001000)


#define REGB_DDRC_CH_OFFSET(channel)            ((DDRCTL_CTRL_INST0_BASE_ADDR) + (REG_GROUP_DDRC_CH0)  + \
                                                 ((channel) * (REG_GROUP_DDRC_CH_SIZE)))
#define REGB_ARB_PORT_OFFSET(port)              ((DDRCTL_CTRL_INST0_BASE_ADDR) + (REG_GROUP_ARB_PORT0) + \
                                                 ((REG_GROUP_ARB_PORT_SIZE) * (port)))
#define REGB_FREQ_CH(freq, channel)             ((DDRCTL_CTRL_INST0_BASE_ADDR) + (REG_GROUP_FREQ0_CH0) + \
                                                 ((channel) * (REG_GROUP_DDRC_CH_SIZE)) + \
                                                 ((freq)    * (REG_GROUP_FREQ_SIZE)))
#define REGB_ADDR_MAP_OFFSET(map)               ((DDRCTL_CTRL_INST0_BASE_ADDR) + (REG_GROUP_ADDR_MAP0) + \
                                                 ((map)     * (REG_GROUP_ADDR_MAP_SIZE)))
#define REGB_IME_CH_OFFSET(channel)             ((DDRCTL_CTRL_INST0_BASE_ADDR) + (REG_GROUP_IME_CH0)   + \
                                                 ((channel) * (REG_GROUP_IME_CH_SIZE)))

#endif /* __DWC_DDRCTL_REG_MAP_MACROS_H__ */
