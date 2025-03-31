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


/**
 * @detail The purpose of the functions in this file is to simplify the register block arb port.
 */

#include "dwc_ddrctl_cinit_prgm_port_util.h"
#include "dwc_ddrctl_cinit_util.h"


uint32_t dwc_ddrctl_get_port_bitmap()
{
    uint32_t bitmap = 0;

#if defined(UMCTL2_PORT_0)
    SNPS_SET_BIT(bitmap, 0, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_1)
    SNPS_SET_BIT(bitmap, 1, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_2)
    SNPS_SET_BIT(bitmap, 2, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_3)
    SNPS_SET_BIT(bitmap, 3, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_4)
    SNPS_SET_BIT(bitmap, 4, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_5)
    SNPS_SET_BIT(bitmap, 5, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_6)
    SNPS_SET_BIT(bitmap, 6, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_7)
    SNPS_SET_BIT(bitmap, 7, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_8)
    SNPS_SET_BIT(bitmap, 8, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_9)
    SNPS_SET_BIT(bitmap, 9, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_10)
    SNPS_SET_BIT(bitmap, 10, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_11)
    SNPS_SET_BIT(bitmap, 11, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_12)
    SNPS_SET_BIT(bitmap, 12, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_13)
    SNPS_SET_BIT(bitmap, 13, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_14)
    SNPS_SET_BIT(bitmap, 14, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_15)
    SNPS_SET_BIT(bitmap, 15, SNPS_CINIT_SET);
#endif

return bitmap;
}

uint32_t dwc_ddrctl_get_port_channel_bitmap()
{
    uint32_t bitmap = 0;

#if defined(UMCTL2_PORT_CH0_0)
    SNPS_SET_BIT(bitmap, 0, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_1)
    SNPS_SET_BIT(bitmap, 1, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_2)
    SNPS_SET_BIT(bitmap, 2, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_3)
    SNPS_SET_BIT(bitmap, 3, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_4)
    SNPS_SET_BIT(bitmap, 4, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_5)
    SNPS_SET_BIT(bitmap, 5, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_6)
    SNPS_SET_BIT(bitmap, 6, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_7)
    SNPS_SET_BIT(bitmap, 7, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_8)
    SNPS_SET_BIT(bitmap, 8, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_9)
    SNPS_SET_BIT(bitmap, 9, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_10)
    SNPS_SET_BIT(bitmap, 10, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_11)
    SNPS_SET_BIT(bitmap, 11, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_12)
    SNPS_SET_BIT(bitmap, 12, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_13)
    SNPS_SET_BIT(bitmap, 13, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_14)
    SNPS_SET_BIT(bitmap, 14, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_PORT_CH0_15)
    SNPS_SET_BIT(bitmap, 15, SNPS_CINIT_SET);
#endif

return bitmap;
}


uint32_t dwc_ddrctl_get_threshold_bitmap()
{
    uint32_t bitmap = 0;

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_0)
    SNPS_SET_BIT(bitmap, 0, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_1)
    SNPS_SET_BIT(bitmap, 1, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_2)
    SNPS_SET_BIT(bitmap, 2, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_3)
    SNPS_SET_BIT(bitmap, 3, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_4)
    SNPS_SET_BIT(bitmap, 4, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_5)
    SNPS_SET_BIT(bitmap, 5, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_6)
    SNPS_SET_BIT(bitmap, 6, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_7)
    SNPS_SET_BIT(bitmap, 7, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_8)
    SNPS_SET_BIT(bitmap, 8, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_9)
    SNPS_SET_BIT(bitmap, 9, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_10)
    SNPS_SET_BIT(bitmap, 10, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_11)
    SNPS_SET_BIT(bitmap, 11, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_12)
    SNPS_SET_BIT(bitmap, 12, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_13)
    SNPS_SET_BIT(bitmap, 13, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_14)
    SNPS_SET_BIT(bitmap, 14, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RRB_THRESHOLD_EN_15)
    SNPS_SET_BIT(bitmap, 15, SNPS_CINIT_SET);
#endif

return bitmap;
}

uint32_t dwc_ddrctl_get_ordered_bitmap()
{
    uint32_t bitmap = 0;

#if defined(UMCTL2_A_RDWR_ORDERED_0)
    SNPS_SET_BIT(bitmap, 0, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_1)
    SNPS_SET_BIT(bitmap, 1, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_2)
    SNPS_SET_BIT(bitmap, 2, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_3)
    SNPS_SET_BIT(bitmap, 3, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_4)
    SNPS_SET_BIT(bitmap, 4, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_5)
    SNPS_SET_BIT(bitmap, 5, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_6)
    SNPS_SET_BIT(bitmap, 6, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_7)
    SNPS_SET_BIT(bitmap, 7, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_8)
    SNPS_SET_BIT(bitmap, 8, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_9)
    SNPS_SET_BIT(bitmap, 9, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_10)
    SNPS_SET_BIT(bitmap, 10, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_11)
    SNPS_SET_BIT(bitmap, 11, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_12)
    SNPS_SET_BIT(bitmap, 12, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_13)
    SNPS_SET_BIT(bitmap, 13, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_14)
    SNPS_SET_BIT(bitmap, 14, SNPS_CINIT_SET);
#endif

#if defined(UMCTL2_A_RDWR_ORDERED_15)
    SNPS_SET_BIT(bitmap, 15, SNPS_CINIT_SET);
#endif

return bitmap;
}


uint32_t dwc_ddrctl_get_arb_ports_ch_bitmap()
{
    uint32_t bitmap = 0;

#if defined(UMCTL2_PORT_CH0_0)  || defined(UMCTL2_PORT_CH0_1)  || defined(UMCTL2_PORT_CH0_2)  || \
    defined(UMCTL2_PORT_CH0_3)  || defined(UMCTL2_PORT_CH0_4)  || defined(UMCTL2_PORT_CH0_5)  || \
    defined(UMCTL2_PORT_CH0_6)  || defined(UMCTL2_PORT_CH0_7)  || defined(UMCTL2_PORT_CH0_8)  || \
    defined(UMCTL2_PORT_CH0_9)  || defined(UMCTL2_PORT_CH0_10) || defined(UMCTL2_PORT_CH0_11) || \
    defined(UMCTL2_PORT_CH0_12) || defined(UMCTL2_PORT_CH0_13) || defined(UMCTL2_PORT_CH0_14) || \
    defined(UMCTL2_PORT_CH0_15)
    SNPS_SET_BIT(bitmap, 0, 1);
#endif

#if defined(UMCTL2_PORT_CH1_0)  || defined(UMCTL2_PORT_CH1_1)  || defined(UMCTL2_PORT_CH1_2)  || \
    defined(UMCTL2_PORT_CH1_3)  || defined(UMCTL2_PORT_CH1_4)  || defined(UMCTL2_PORT_CH1_5)  || \
    defined(UMCTL2_PORT_CH1_6)  || defined(UMCTL2_PORT_CH1_7)  || defined(UMCTL2_PORT_CH1_8)  || \
    defined(UMCTL2_PORT_CH1_9)  || defined(UMCTL2_PORT_CH1_10) || defined(UMCTL2_PORT_CH1_11) || \
    defined(UMCTL2_PORT_CH1_12) || defined(UMCTL2_PORT_CH1_13) || defined(UMCTL2_PORT_CH1_14) || \
    defined(UMCTL2_PORT_CH1_15)
    SNPS_SET_BIT(bitmap, 1, 1);
#endif /* UMCTL2_PORT_CH1_0 */

#if defined(UMCTL2_PORT_CH2_0)  || defined(UMCTL2_PORT_CH2_1)  || defined(UMCTL2_PORT_CH2_2)  || \
    defined(UMCTL2_PORT_CH2_3)  || defined(UMCTL2_PORT_CH2_4)  || defined(UMCTL2_PORT_CH2_5)  || \
    defined(UMCTL2_PORT_CH2_6)  || defined(UMCTL2_PORT_CH2_7)  || defined(UMCTL2_PORT_CH2_8)  || \
    defined(UMCTL2_PORT_CH2_9)  || defined(UMCTL2_PORT_CH2_10) || defined(UMCTL2_PORT_CH2_11) || \
    defined(UMCTL2_PORT_CH2_12) || defined(UMCTL2_PORT_CH2_13) || defined(UMCTL2_PORT_CH2_14) || \
    defined(UMCTL2_PORT_CH2_15)
    SNPS_SET_BIT(bitmap, 2, 1);
#endif

#if defined(UMCTL2_PORT_CH3_0)  || defined(UMCTL2_PORT_CH3_1)  || defined(UMCTL2_PORT_CH3_2)  || \
    defined(UMCTL2_PORT_CH3_3)  || defined(UMCTL2_PORT_CH3_4)  || defined(UMCTL2_PORT_CH3_5)  || \
    defined(UMCTL2_PORT_CH3_6)  || defined(UMCTL2_PORT_CH3_7)  || defined(UMCTL2_PORT_CH3_8)  || \
    defined(UMCTL2_PORT_CH3_9)  || defined(UMCTL2_PORT_CH3_10) || defined(UMCTL2_PORT_CH3_11) || \
    defined(UMCTL2_PORT_CH3_12) || defined(UMCTL2_PORT_CH3_13) || defined(UMCTL2_PORT_CH3_14) || \
    defined(UMCTL2_PORT_CH3_15)
    SNPS_SET_BIT(bitmap, 3, 1);
#endif

#if defined(UMCTL2_PORT_CH4_0)  || defined(UMCTL2_PORT_CH4_1)  || defined(UMCTL2_PORT_CH4_2)  || \
    defined(UMCTL2_PORT_CH4_3)  || defined(UMCTL2_PORT_CH4_4)  || defined(UMCTL2_PORT_CH4_5)  || \
    defined(UMCTL2_PORT_CH4_6)  || defined(UMCTL2_PORT_CH4_7)  || defined(UMCTL2_PORT_CH4_8)  || \
    defined(UMCTL2_PORT_CH4_9)  || defined(UMCTL2_PORT_CH4_10) || defined(UMCTL2_PORT_CH4_11) || \
    defined(UMCTL2_PORT_CH4_12) || defined(UMCTL2_PORT_CH4_13) || defined(UMCTL2_PORT_CH4_14) || \
    defined(UMCTL2_PORT_CH4_15)
    SNPS_SET_BIT(bitmap, 4, 1);
#endif

#if defined(UMCTL2_PORT_CH5_0)  || defined(UMCTL2_PORT_CH5_1)  || defined(UMCTL2_PORT_CH5_2)  || \
    defined(UMCTL2_PORT_CH5_3)  || defined(UMCTL2_PORT_CH5_4)  || defined(UMCTL2_PORT_CH5_5)  || \
    defined(UMCTL2_PORT_CH5_6)  || defined(UMCTL2_PORT_CH5_7)  || defined(UMCTL2_PORT_CH5_8)  || \
    defined(UMCTL2_PORT_CH5_9)  || defined(UMCTL2_PORT_CH5_10) || defined(UMCTL2_PORT_CH5_11) || \
    defined(UMCTL2_PORT_CH5_12) || defined(UMCTL2_PORT_CH5_13) || defined(UMCTL2_PORT_CH5_14) || \
    defined(UMCTL2_PORT_CH5_15)
    SNPS_SET_BIT(bitmap, 5, 1);
#endif

#if defined(UMCTL2_PORT_CH6_0)  || defined(UMCTL2_PORT_CH6_1)  || defined(UMCTL2_PORT_CH6_2)  || \
    defined(UMCTL2_PORT_CH6_3)  || defined(UMCTL2_PORT_CH6_4)  || defined(UMCTL2_PORT_CH6_5)  || \
    defined(UMCTL2_PORT_CH6_6)  || defined(UMCTL2_PORT_CH6_7)  || defined(UMCTL2_PORT_CH6_8)  || \
    defined(UMCTL2_PORT_CH6_9)  || defined(UMCTL2_PORT_CH6_10) || defined(UMCTL2_PORT_CH6_11) || \
    defined(UMCTL2_PORT_CH6_12) || defined(UMCTL2_PORT_CH6_13) || defined(UMCTL2_PORT_CH6_14) || \
    defined(UMCTL2_PORT_CH6_15)
    SNPS_SET_BIT(bitmap, 6, 1);
#endif

#if defined(UMCTL2_PORT_CH7_0)  || defined(UMCTL2_PORT_CH7_1)  || defined(UMCTL2_PORT_CH7_2)  || \
    defined(UMCTL2_PORT_CH7_3)  || defined(UMCTL2_PORT_CH7_4)  || defined(UMCTL2_PORT_CH7_5)  || \
    defined(UMCTL2_PORT_CH7_6)  || defined(UMCTL2_PORT_CH7_7)  || defined(UMCTL2_PORT_CH7_8)  || \
    defined(UMCTL2_PORT_CH7_9)  || defined(UMCTL2_PORT_CH7_10) || defined(UMCTL2_PORT_CH7_11) || \
    defined(UMCTL2_PORT_CH7_12) || defined(UMCTL2_PORT_CH7_13) || defined(UMCTL2_PORT_CH7_14) || \
    defined(UMCTL2_PORT_CH7_15)
    SNPS_SET_BIT(bitmap, 7, 1);
#endif

#if defined(UMCTL2_PORT_CH8_0)  || defined(UMCTL2_PORT_CH8_1)  || defined(UMCTL2_PORT_CH8_2)  || \
    defined(UMCTL2_PORT_CH8_3)  || defined(UMCTL2_PORT_CH8_4)  || defined(UMCTL2_PORT_CH8_5)  || \
    defined(UMCTL2_PORT_CH8_6)  || defined(UMCTL2_PORT_CH8_7)  || defined(UMCTL2_PORT_CH8_8)  || \
    defined(UMCTL2_PORT_CH8_9)  || defined(UMCTL2_PORT_CH8_10) || defined(UMCTL2_PORT_CH8_11) || \
    defined(UMCTL2_PORT_CH8_12) || defined(UMCTL2_PORT_CH8_13) || defined(UMCTL2_PORT_CH8_14) || \
    defined(UMCTL2_PORT_CH8_15)
    SNPS_SET_BIT(bitmap, 8, 1);
#endif

#if defined(UMCTL2_PORT_CH9_0)  || defined(UMCTL2_PORT_CH9_1)  || defined(UMCTL2_PORT_CH9_2)  || \
    defined(UMCTL2_PORT_CH9_3)  || defined(UMCTL2_PORT_CH9_4)  || defined(UMCTL2_PORT_CH9_5)  || \
    defined(UMCTL2_PORT_CH9_6)  || defined(UMCTL2_PORT_CH9_7)  || defined(UMCTL2_PORT_CH9_8)  || \
    defined(UMCTL2_PORT_CH9_9)  || defined(UMCTL2_PORT_CH9_10) || defined(UMCTL2_PORT_CH9_11) || \
    defined(UMCTL2_PORT_CH9_12) || defined(UMCTL2_PORT_CH9_13) || defined(UMCTL2_PORT_CH9_14) || \
    defined(UMCTL2_PORT_CH9_15)
    SNPS_SET_BIT(bitmap, 9, 1);
#endif

#if defined(UMCTL2_PORT_CH10_0)  || defined(UMCTL2_PORT_CH10_1)  || defined(UMCTL2_PORT_CH10_2)  || \
    defined(UMCTL2_PORT_CH10_3)  || defined(UMCTL2_PORT_CH10_4)  || defined(UMCTL2_PORT_CH10_5)  || \
    defined(UMCTL2_PORT_CH10_6)  || defined(UMCTL2_PORT_CH10_7)  || defined(UMCTL2_PORT_CH10_8)  || \
    defined(UMCTL2_PORT_CH10_9)  || defined(UMCTL2_PORT_CH10_10) || defined(UMCTL2_PORT_CH10_11) || \
    defined(UMCTL2_PORT_CH10_12) || defined(UMCTL2_PORT_CH10_13) || defined(UMCTL2_PORT_CH10_14) || \
    defined(UMCTL2_PORT_CH10_15)
    SNPS_SET_BIT(bitmap, 10, 1);
#endif

#if defined(UMCTL2_PORT_CH11_0)  || defined(UMCTL2_PORT_CH11_1)  || defined(UMCTL2_PORT_CH11_2)  || \
    defined(UMCTL2_PORT_CH11_3)  || defined(UMCTL2_PORT_CH11_4)  || defined(UMCTL2_PORT_CH11_5)  || \
    defined(UMCTL2_PORT_CH11_6)  || defined(UMCTL2_PORT_CH11_7)  || defined(UMCTL2_PORT_CH11_8)  || \
    defined(UMCTL2_PORT_CH11_9)  || defined(UMCTL2_PORT_CH11_10) || defined(UMCTL2_PORT_CH11_11) || \
    defined(UMCTL2_PORT_CH11_12) || defined(UMCTL2_PORT_CH11_13) || defined(UMCTL2_PORT_CH11_14) || \
    defined(UMCTL2_PORT_CH11_15)
    SNPS_SET_BIT(bitmap, 11, 1);
#endif

#if defined(UMCTL2_PORT_CH12_0)  || defined(UMCTL2_PORT_CH12_1)  || defined(UMCTL2_PORT_CH12_2)  || \
    defined(UMCTL2_PORT_CH12_3)  || defined(UMCTL2_PORT_CH12_4)  || defined(UMCTL2_PORT_CH12_5)  || \
    defined(UMCTL2_PORT_CH12_6)  || defined(UMCTL2_PORT_CH12_7)  || defined(UMCTL2_PORT_CH12_8)  || \
    defined(UMCTL2_PORT_CH12_9)  || defined(UMCTL2_PORT_CH12_10) || defined(UMCTL2_PORT_CH12_11) || \
    defined(UMCTL2_PORT_CH12_12) || defined(UMCTL2_PORT_CH12_13) || defined(UMCTL2_PORT_CH12_14) || \
    defined(UMCTL2_PORT_CH12_15)
    SNPS_SET_BIT(bitmap, 12, 1);
#endif

#if defined(UMCTL2_PORT_CH13_0)  || defined(UMCTL2_PORT_CH13_1)  || defined(UMCTL2_PORT_CH13_2)  || \
    defined(UMCTL2_PORT_CH13_3)  || defined(UMCTL2_PORT_CH13_4)  || defined(UMCTL2_PORT_CH13_5)  || \
    defined(UMCTL2_PORT_CH13_6)  || defined(UMCTL2_PORT_CH13_7)  || defined(UMCTL2_PORT_CH13_8)  || \
    defined(UMCTL2_PORT_CH13_9)  || defined(UMCTL2_PORT_CH13_10) || defined(UMCTL2_PORT_CH13_11) || \
    defined(UMCTL2_PORT_CH13_12) || defined(UMCTL2_PORT_CH13_13) || defined(UMCTL2_PORT_CH13_14) || \
    defined(UMCTL2_PORT_CH13_15)
    SNPS_SET_BIT(bitmap, 13, 1);
#endif

#if defined(UMCTL2_PORT_CH14_0)  || defined(UMCTL2_PORT_CH14_1)  || defined(UMCTL2_PORT_CH14_2)  || \
    defined(UMCTL2_PORT_CH14_3)  || defined(UMCTL2_PORT_CH14_4)  || defined(UMCTL2_PORT_CH14_5)  || \
    defined(UMCTL2_PORT_CH14_6)  || defined(UMCTL2_PORT_CH14_7)  || defined(UMCTL2_PORT_CH14_8)  || \
    defined(UMCTL2_PORT_CH14_9)  || defined(UMCTL2_PORT_CH14_10) || defined(UMCTL2_PORT_CH14_11) || \
    defined(UMCTL2_PORT_CH14_12) || defined(UMCTL2_PORT_CH14_13) || defined(UMCTL2_PORT_CH14_14) || \
    defined(UMCTL2_PORT_CH14_15)
    SNPS_SET_BIT(bitmap, 14, 1);
#endif

#if defined(UMCTL2_PORT_CH15_0)  || defined(UMCTL2_PORT_CH15_1)  || defined(UMCTL2_PORT_CH15_2)  || \
    defined(UMCTL2_PORT_CH15_3)  || defined(UMCTL2_PORT_CH15_4)  || defined(UMCTL2_PORT_CH15_5)  || \
    defined(UMCTL2_PORT_CH15_6)  || defined(UMCTL2_PORT_CH15_7)  || defined(UMCTL2_PORT_CH15_8)  || \
    defined(UMCTL2_PORT_CH15_9)  || defined(UMCTL2_PORT_CH15_10) || defined(UMCTL2_PORT_CH15_11) || \
    defined(UMCTL2_PORT_CH15_12) || defined(UMCTL2_PORT_CH15_13) || defined(UMCTL2_PORT_CH15_14) || \
    defined(UMCTL2_PORT_CH15_15)
    SNPS_SET_BIT(bitmap, 15, 1);
#endif
    return bitmap;
}


uint32_t dwc_ddrctl_get_arb_ports_axi_bitmap()
{
    uint32_t bitmap = 0;

#ifdef UMCTL2_A_AXI_0
    SNPS_SET_BIT(bitmap, 0, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_1
    SNPS_SET_BIT(bitmap, 1, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_2
    SNPS_SET_BIT(bitmap, 2, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_3
    SNPS_SET_BIT(bitmap, 3, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_4
    SNPS_SET_BIT(bitmap, 4, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_5
    SNPS_SET_BIT(bitmap, 5, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_6
    SNPS_SET_BIT(bitmap, 6, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_7
    SNPS_SET_BIT(bitmap, 7, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_8
    SNPS_SET_BIT(bitmap, 8, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_9
    SNPS_SET_BIT(bitmap, 9, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_10
    SNPS_SET_BIT(bitmap, 10, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_11
    SNPS_SET_BIT(bitmap, 11, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_12
    SNPS_SET_BIT(bitmap, 12, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_13
    SNPS_SET_BIT(bitmap, 13, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_14
    SNPS_SET_BIT(bitmap, 14, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_AXI_15
    SNPS_SET_BIT(bitmap, 15, SNPS_CINIT_SET);
#endif

return bitmap;
}

uint32_t dwc_ddrctl_get_arb_ports_axi_raq_bitmap()
{
    uint32_t bitmap = 0;

#ifdef UMCTL2_A_USE2RAQ_0
    SNPS_SET_BIT(bitmap, 0, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_1
    SNPS_SET_BIT(bitmap, 1, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_2
    SNPS_SET_BIT(bitmap, 2, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_3
    SNPS_SET_BIT(bitmap, 3, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_4
    SNPS_SET_BIT(bitmap, 4, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_5
    SNPS_SET_BIT(bitmap, 5, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_6
    SNPS_SET_BIT(bitmap, 6, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_7
    SNPS_SET_BIT(bitmap, 7, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_8
    SNPS_SET_BIT(bitmap, 8, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_9
    SNPS_SET_BIT(bitmap, 9, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_10
    SNPS_SET_BIT(bitmap, 10, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_11
    SNPS_SET_BIT(bitmap, 11, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_12
    SNPS_SET_BIT(bitmap, 12, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_13
    SNPS_SET_BIT(bitmap, 13, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_14
    SNPS_SET_BIT(bitmap, 14, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_A_USE2RAQ_15
    SNPS_SET_BIT(bitmap, 15, SNPS_CINIT_SET);
#endif

return bitmap;
}

uint32_t dwc_ddrctl_get_xpi_vpr_bitmap()
{
    uint32_t bitmap = 0;

#ifdef UMCTL2_XPI_VPR_0
    SNPS_SET_BIT(bitmap, 0, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_1
    SNPS_SET_BIT(bitmap, 1, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_2
    SNPS_SET_BIT(bitmap, 2, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_3
    SNPS_SET_BIT(bitmap, 3, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_4
    SNPS_SET_BIT(bitmap, 4, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_5
    SNPS_SET_BIT(bitmap, 5, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_6
    SNPS_SET_BIT(bitmap, 6, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_7
    SNPS_SET_BIT(bitmap, 7, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_8
    SNPS_SET_BIT(bitmap, 8, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_9
    SNPS_SET_BIT(bitmap, 9, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_10
    SNPS_SET_BIT(bitmap, 10, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_11
    SNPS_SET_BIT(bitmap, 11, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_12
    SNPS_SET_BIT(bitmap, 12, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_13
    SNPS_SET_BIT(bitmap, 13, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_14
    SNPS_SET_BIT(bitmap, 14, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPR_15
    SNPS_SET_BIT(bitmap, 15, SNPS_CINIT_SET);
#endif

return bitmap;
}

uint32_t dwc_ddrctl_get_xpi_vpw_bitmap()
{
    uint32_t bitmap = 0;

#ifdef UMCTL2_XPI_VPW_0
    SNPS_SET_BIT(bitmap, 0, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_1
    SNPS_SET_BIT(bitmap, 1, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_2
    SNPS_SET_BIT(bitmap, 2, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_3
    SNPS_SET_BIT(bitmap, 3, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_4
    SNPS_SET_BIT(bitmap, 4, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_5
    SNPS_SET_BIT(bitmap, 5, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_6
    SNPS_SET_BIT(bitmap, 6, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_7
    SNPS_SET_BIT(bitmap, 7, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_8
    SNPS_SET_BIT(bitmap, 8, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_9
    SNPS_SET_BIT(bitmap, 9, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_10
    SNPS_SET_BIT(bitmap, 10, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_11
    SNPS_SET_BIT(bitmap, 11, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_12
    SNPS_SET_BIT(bitmap, 12, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_13
    SNPS_SET_BIT(bitmap, 13, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_14
    SNPS_SET_BIT(bitmap, 14, SNPS_CINIT_SET);
#endif

#ifdef UMCTL2_XPI_VPW_15
    SNPS_SET_BIT(bitmap, 15, SNPS_CINIT_SET);
#endif

return bitmap;
}
