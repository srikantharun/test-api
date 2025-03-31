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


#ifndef __DWC_DDRCTL_CINIT_MACROS_H__
#define __DWC_DDRCTL_CINIT_MACROS_H__


#include "dwc_cinit_bsp.h"

#define SWAP_UINT32(value) (((value) >> 24u) | (((value) & 0x00FF0000u) >> 8u) | \
                            (((value) & 0x0000FF00u) << 8u) | (((value) & 0x000000FFu) << 24u))

#define CEIL(a, b)    (((a) / (b)) + (((a) % (b)) > 0 ? 1 : 0))


#define DIVIDE_ROUNDDOWN(a, b) ((a) / (b))


#ifdef DDRCTL_SINGLE_INST_DUALCH
#define IS_DUAL_CHAN (1)
#else /* DDRCTL_SINGLE_INST_DUALCH*/
#ifdef DDRCTL_DDR_SINGLE_CHANNEL
#define IS_DUAL_CHAN (0)
#else /* DDRCTL_DDR_SINGLE_CHANNEL*/
#ifdef UMCTL2_DUAL_CHANNEL
#ifdef IS_DDR5
#define IS_DUAL_CHAN ((REGB_DDRC_CH0.chctl.dual_channel_en == 1))
#else /* IS_DDR5 */
#define IS_DUAL_CHAN (1)
#endif /* IS_DDR5 */
#else /* UMCTL2_DUAL_CHANNEL */
#define IS_DUAL_CHAN (0)
#endif /* UMCTL2_DUAL_CHANNEL */
#endif /* DDRCTL_DDR_SINGLE_CHANNEL*/
#endif /* DDRCTL_SINGLE_INST_DUALCH*/

#define DWC_DDRCTL_MAX_LUT_ENTRIES (1<<DDRCTL_LUT_ADDRMAP_CS_WIN_BITS)

//@todo re-define the macro when ddr4 MRAM heterogenour rank is supported
#if defined(DDRCTL_LUT_ADDRMAP) && defined(CINIT_DDR5)
#define DWC_DDRCTL_DEV_CFG_NUM  (DDRCTL_NUM_ADDR_MAP)
#else
#define DWC_DDRCTL_DEV_CFG_NUM (1)
#endif


#define DIV_2(val)  ((val) >> 1)
#define DIV_4(val)  ((val) >> 2)
#define DIV_8(val)  ((val) >> 3)
#define DIV_16(val) ((val) >> 4)
#define DIV_32(val) ((val) >> 5)
#define DIV_1024(val) ((val) >> 10)

#define GET_ARR_NELEMS(arr_symbol) (sizeof(arr_symbol) / sizeof(arr_symbol[0]))

#endif /* __DWC_DDRCTL_CINIT_MACROS_H__ */
