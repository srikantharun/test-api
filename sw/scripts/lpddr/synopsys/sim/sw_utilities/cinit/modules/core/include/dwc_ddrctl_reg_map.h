// coreBuilder: This is an automated C header file. DO NOT EDIT.

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


#ifndef __MODULES_CORE_INCLUDE_DWC_DDRCTL_REG_MAP_H__
#define __MODULES_CORE_INCLUDE_DWC_DDRCTL_REG_MAP_H__

#define REG_GROUP_DDRC_CH0                                             0x00010000

#define MSTR0                                                          0x00000000
#define MSTR0_DDR4_MASK                                                0x00000001
#define MSTR0_DDR4_BIT_OFFSET                                                   0
#define MSTR0_LPDDR4_MASK                                              0x00000002
#define MSTR0_LPDDR4_BIT_OFFSET                                                 1
#define MSTR0_DDR5_MASK                                                0x00000004
#define MSTR0_DDR5_BIT_OFFSET                                                   2
#define MSTR0_LPDDR5_MASK                                              0x00000008
#define MSTR0_LPDDR5_BIT_OFFSET                                                 3
#define MSTR0_BANK_CONFIG_MASK                                         0x00000030
#define MSTR0_BANK_CONFIG_BIT_OFFSET                                            4
#define MSTR0_BG_CONFIG_MASK                                           0x000000C0
#define MSTR0_BG_CONFIG_BIT_OFFSET                                              6
#define MSTR0_BURST_MODE_MASK                                          0x00000100
#define MSTR0_BURST_MODE_BIT_OFFSET                                             8
#define MSTR0_BURSTCHOP_MASK                                           0x00000200
#define MSTR0_BURSTCHOP_BIT_OFFSET                                              9
#define MSTR0_EN_2T_TIMING_MODE_MASK                                   0x00000400
#define MSTR0_EN_2T_TIMING_MODE_BIT_OFFSET                                     10
#define MSTR0_LPDDR5X_MASK                                             0x00000800
#define MSTR0_LPDDR5X_BIT_OFFSET                                               11
#define MSTR0_DATA_BUS_WIDTH_MASK                                      0x00003000
#define MSTR0_DATA_BUS_WIDTH_BIT_OFFSET                                        12
#define MSTR0_DLL_OFF_MODE_MASK                                        0x00008000
#define MSTR0_DLL_OFF_MODE_BIT_OFFSET                                          15
#define MSTR0_BURST_RDWR_MASK                                          0x001F0000
#define MSTR0_BURST_RDWR_BIT_OFFSET                                            16
#define MSTR0_ACTIVE_LOGICAL_RANKS_MASK                                0x00E00000
#define MSTR0_ACTIVE_LOGICAL_RANKS_BIT_OFFSET                                  21
#define MSTR0_ACTIVE_RANKS_MASK                                        0x3F000000
#define MSTR0_ACTIVE_RANKS_BIT_OFFSET                                          24
#define MSTR0_DEVICE_CONFIG_MASK                                       0xC0000000
#define MSTR0_DEVICE_CONFIG_BIT_OFFSET                                         30

#define MSTR1                                                          0x00000004
#define MSTR1_RANK_TMGREG_SEL_MASK                                     0x0000000F
#define MSTR1_RANK_TMGREG_SEL_BIT_OFFSET                                        0
#define MSTR1_BANK_CONFIG_2_MASK                                       0x00000030
#define MSTR1_BANK_CONFIG_2_BIT_OFFSET                                          4
#define MSTR1_BG_CONFIG_2_MASK                                         0x000000C0
#define MSTR1_BG_CONFIG_2_BIT_OFFSET                                            6
#define MSTR1_RFC_TMGREG_SEL_MASK                                      0x0000FF00
#define MSTR1_RFC_TMGREG_SEL_BIT_OFFSET                                         8
#define MSTR1_ALT_ADDRMAP_EN_MASK                                      0x00010000
#define MSTR1_ALT_ADDRMAP_EN_BIT_OFFSET                                        16
#define MSTR1_ACTIVE_LOGICAL_RANKS_2_MASK                              0x00E00000
#define MSTR1_ACTIVE_LOGICAL_RANKS_2_BIT_OFFSET                                21
#define MSTR1_DEVICE_CONFIG_2_MASK                                     0xC0000000
#define MSTR1_DEVICE_CONFIG_2_BIT_OFFSET                                       30

#define MSTR2                                                          0x00000008
#define MSTR2_TARGET_FREQUENCY_MASK                                    0xFFFFFFFF
#define MSTR2_TARGET_FREQUENCY_BIT_OFFSET                                       0

#define MSTR3                                                          0x0000000C
#define MSTR3_GEARDOWN_MODE_MASK                                       0x00000001
#define MSTR3_GEARDOWN_MODE_BIT_OFFSET                                          0
#define MSTR3_RANK_TMGSET_SEL_MASK                                     0x000000F0
#define MSTR3_RANK_TMGSET_SEL_BIT_OFFSET                                        4
#define MSTR3_RANK_DEV_CFG_SEL_MASK                                    0xFFFFFF00
#define MSTR3_RANK_DEV_CFG_SEL_BIT_OFFSET                                       8

#define MSTR4                                                          0x00000010
#define MSTR4_WCK_ON_MASK                                              0x00000001
#define MSTR4_WCK_ON_BIT_OFFSET                                                 0
#define MSTR4_WCK_SUSPEND_EN_MASK                                      0x00000010
#define MSTR4_WCK_SUSPEND_EN_BIT_OFFSET                                         4
#define MSTR4_WS_OFF_EN_MASK                                           0x00000100
#define MSTR4_WS_OFF_EN_BIT_OFFSET                                              8

#define STAT                                                           0x00000014
#define STAT_OPERATING_MODE_MASK                                       0x00000007
#define STAT_OPERATING_MODE_BIT_OFFSET                                          0
#define STAT_SELFREF_TYPE_MASK                                         0x00000FF0
#define STAT_SELFREF_TYPE_BIT_OFFSET                                            4
#define STAT_SELFREF_STATE_MASK                                        0x00007000
#define STAT_SELFREF_STATE_BIT_OFFSET                                          12
#define STAT_SELFREF_CAM_NOT_EMPTY_MASK                                0x00010000
#define STAT_SELFREF_CAM_NOT_EMPTY_BIT_OFFSET                                  16
#define STAT_POWERDOWN_STATE_MASK                                      0x00F00000
#define STAT_POWERDOWN_STATE_BIT_OFFSET                                        20
#define STAT_MPSM_STATE_MASK                                           0x3F000000
#define STAT_MPSM_STATE_BIT_OFFSET                                             24
#define STAT_DFI_LP_STATE_MASK                                         0x40000000
#define STAT_DFI_LP_STATE_BIT_OFFSET                                           30

#define STAT2                                                          0x00000018
#define STAT2_GLB_BLK_EVENTS_ONGOING_MASK                              0x000000FF
#define STAT2_GLB_BLK_EVENTS_ONGOING_BIT_OFFSET                                 0
#define STAT2_SELFREF_ONGOING_MASK                                     0x0F000000
#define STAT2_SELFREF_ONGOING_BIT_OFFSET                                       24
#define STAT2_POWERDOWN_ONGOING_MASK                                   0xF0000000
#define STAT2_POWERDOWN_ONGOING_BIT_OFFSET                                     28

#define STAT3                                                          0x0000001C
#define STAT3_RANK_BLK_EVENTS_ONGOING_MASK                             0xFFFFFFFF
#define STAT3_RANK_BLK_EVENTS_ONGOING_BIT_OFFSET                                0

#define MRCTRL0                                                        0x00000080
#define MRCTRL0_MR_TYPE_MASK                                           0x00000001
#define MRCTRL0_MR_TYPE_BIT_OFFSET                                              0
#define MRCTRL0_MPR_EN_MASK                                            0x00000002
#define MRCTRL0_MPR_EN_BIT_OFFSET                                               1
#define MRCTRL0_PDA_EN_MASK                                            0x00000004
#define MRCTRL0_PDA_EN_BIT_OFFSET                                               2
#define MRCTRL0_SW_INIT_INT_MASK                                       0x00000008
#define MRCTRL0_SW_INIT_INT_BIT_OFFSET                                          3
#define MRCTRL0_MR_RANK_MASK                                           0x00000FF0
#define MRCTRL0_MR_RANK_BIT_OFFSET                                              4
#define MRCTRL0_MR_ADDR_MASK                                           0x0000F000
#define MRCTRL0_MR_ADDR_BIT_OFFSET                                             12
#define MRCTRL0_MR_CID_MASK                                            0x00FF0000
#define MRCTRL0_MR_CID_BIT_OFFSET                                              16
#define MRCTRL0_MRR_DONE_CLR_MASK                                      0x01000000
#define MRCTRL0_MRR_DONE_CLR_BIT_OFFSET                                        24
#define MRCTRL0_DIS_MRRW_TRFC_MASK                                     0x08000000
#define MRCTRL0_DIS_MRRW_TRFC_BIT_OFFSET                                       27
#define MRCTRL0_PPR_EN_MASK                                            0x10000000
#define MRCTRL0_PPR_EN_BIT_OFFSET                                              28
#define MRCTRL0_PPR_PGMPST_EN_MASK                                     0x20000000
#define MRCTRL0_PPR_PGMPST_EN_BIT_OFFSET                                       29
#define MRCTRL0_PBA_MODE_MASK                                          0x40000000
#define MRCTRL0_PBA_MODE_BIT_OFFSET                                            30
#define MRCTRL0_MR_WR_MASK                                             0x80000000
#define MRCTRL0_MR_WR_BIT_OFFSET                                               31

#define MRCTRL1                                                        0x00000084
#define MRCTRL1_MR_DATA_MASK                                           0xFFFFFFFF
#define MRCTRL1_MR_DATA_BIT_OFFSET                                              0

#define MRCTRL2                                                        0x00000088
#define MRCTRL2_MR_DEVICE_SEL_MASK                                     0xFFFFFFFF
#define MRCTRL2_MR_DEVICE_SEL_BIT_OFFSET                                        0

#define MRSTAT                                                         0x00000090
#define MRSTAT_MR_WR_BUSY_MASK                                         0x00000001
#define MRSTAT_MR_WR_BUSY_BIT_OFFSET                                            0
#define MRSTAT_PDA_DONE_MASK                                           0x00000100
#define MRSTAT_PDA_DONE_BIT_OFFSET                                              8
#define MRSTAT_MRR_DONE_MASK                                           0x00010000
#define MRSTAT_MRR_DONE_BIT_OFFSET                                             16
#define MRSTAT_PPR_DONE_MASK                                           0x00020000
#define MRSTAT_PPR_DONE_BIT_OFFSET                                             17

#define MRRDATA0                                                       0x00000094
#define MRRDATA0_MRR_DATA_LWR_MASK                                     0xFFFFFFFF
#define MRRDATA0_MRR_DATA_LWR_BIT_OFFSET                                        0

#define MRRDATA1                                                       0x00000098
#define MRRDATA1_MRR_DATA_UPR_MASK                                     0xFFFFFFFF
#define MRRDATA1_MRR_DATA_UPR_BIT_OFFSET                                        0

#define DERATECTL0                                                     0x00000100
#define DERATECTL0_DERATE_ENABLE_MASK                                  0x00000001
#define DERATECTL0_DERATE_ENABLE_BIT_OFFSET                                     0
#define DERATECTL0_LPDDR4_REFRESH_MODE_MASK                            0x00000002
#define DERATECTL0_LPDDR4_REFRESH_MODE_BIT_OFFSET                               1
#define DERATECTL0_DERATE_MR4_PAUSE_FC_MASK                            0x00000004
#define DERATECTL0_DERATE_MR4_PAUSE_FC_BIT_OFFSET                               2
#define DERATECTL0_DIS_TREFI_X6X8_MASK                                 0x00000008
#define DERATECTL0_DIS_TREFI_X6X8_BIT_OFFSET                                    3
#define DERATECTL0_DIS_TREFI_X0125_MASK                                0x00000010
#define DERATECTL0_DIS_TREFI_X0125_BIT_OFFSET                                   4
#define DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP_MASK                        0x00000020
#define DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP_BIT_OFFSET                           5

#define DERATECTL1                                                     0x00000104
#define DERATECTL1_ACTIVE_DERATE_BYTE_RANK0_MASK                       0xFFFFFFFF
#define DERATECTL1_ACTIVE_DERATE_BYTE_RANK0_BIT_OFFSET                          0

#define DERATECTL2                                                     0x00000108
#define DERATECTL2_ACTIVE_DERATE_BYTE_RANK1_MASK                       0xFFFFFFFF
#define DERATECTL2_ACTIVE_DERATE_BYTE_RANK1_BIT_OFFSET                          0

#define DERATECTL3                                                     0x0000010C
#define DERATECTL3_ACTIVE_DERATE_BYTE_RANK2_MASK                       0xFFFFFFFF
#define DERATECTL3_ACTIVE_DERATE_BYTE_RANK2_BIT_OFFSET                          0

#define DERATECTL4                                                     0x00000110
#define DERATECTL4_ACTIVE_DERATE_BYTE_RANK3_MASK                       0xFFFFFFFF
#define DERATECTL4_ACTIVE_DERATE_BYTE_RANK3_BIT_OFFSET                          0

#define DERATECTL5                                                     0x00000114
#define DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN_MASK                      0x00000001
#define DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN_BIT_OFFSET                         0
#define DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR_MASK                     0x00000002
#define DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR_BIT_OFFSET                        1
#define DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE_MASK                   0x00000004
#define DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE_BIT_OFFSET                      2

#define DERATECTL6                                                     0x00000118
#define DERATECTL6_DERATE_MR4_TUF_DIS_MASK                             0x00000001
#define DERATECTL6_DERATE_MR4_TUF_DIS_BIT_OFFSET                                0
#define DERATECTL6_DIS_MRR4_TCR_SRX_MASK                               0x00000002
#define DERATECTL6_DIS_MRR4_TCR_SRX_BIT_OFFSET                                  1
#define DERATECTL6_DERATE_TEMP_LIMIT_INTR_NORMAL_EN_MASK               0x00000004
#define DERATECTL6_DERATE_TEMP_LIMIT_INTR_NORMAL_EN_BIT_OFFSET                  2
#define DERATECTL6_DERATE_TEMP_LIMIT_INTR_HIGH_EN_MASK                 0x00000008
#define DERATECTL6_DERATE_TEMP_LIMIT_INTR_HIGH_EN_BIT_OFFSET                    3
#define DERATECTL6_DERATE_TEMP_LIMIT_INTR_LOW_EN_MASK                  0x00000010
#define DERATECTL6_DERATE_TEMP_LIMIT_INTR_LOW_EN_BIT_OFFSET                     4
#define DERATECTL6_DERATE_LOW_TEMP_LIMIT_MASK                          0x00070000
#define DERATECTL6_DERATE_LOW_TEMP_LIMIT_BIT_OFFSET                            16
#define DERATECTL6_DERATE_HIGH_TEMP_LIMIT_MASK                         0x00700000
#define DERATECTL6_DERATE_HIGH_TEMP_LIMIT_BIT_OFFSET                           20

#define DERATECTL7                                                     0x0000011C
#define DERATECTL7_DERATE_TEMP_LIMIT_INTR_CLR_RANK0_MASK               0x00000001
#define DERATECTL7_DERATE_TEMP_LIMIT_INTR_CLR_RANK0_BIT_OFFSET                  0
#define DERATECTL7_DERATE_TEMP_LIMIT_INTR_CLR_RANK1_MASK               0x00000002
#define DERATECTL7_DERATE_TEMP_LIMIT_INTR_CLR_RANK1_BIT_OFFSET                  1
#define DERATECTL7_DERATE_TEMP_LIMIT_INTR_CLR_RANK2_MASK               0x00000004
#define DERATECTL7_DERATE_TEMP_LIMIT_INTR_CLR_RANK2_BIT_OFFSET                  2
#define DERATECTL7_DERATE_TEMP_LIMIT_INTR_CLR_RANK3_MASK               0x00000008
#define DERATECTL7_DERATE_TEMP_LIMIT_INTR_CLR_RANK3_BIT_OFFSET                  3

#define DERATESTAT0                                                    0x00000120
#define DERATESTAT0_DERATE_TEMP_LIMIT_INTR_MASK                        0x00000001
#define DERATESTAT0_DERATE_TEMP_LIMIT_INTR_BIT_OFFSET                           0

#define DERATESTAT1                                                    0x00000124
#define DERATESTAT1_REFRESH_RATE_RANK0_MASK                            0x00000007
#define DERATESTAT1_REFRESH_RATE_RANK0_BIT_OFFSET                               0
#define DERATESTAT1_REFRESH_RATE_RANK1_MASK                            0x00000070
#define DERATESTAT1_REFRESH_RATE_RANK1_BIT_OFFSET                               4
#define DERATESTAT1_REFRESH_RATE_RANK2_MASK                            0x00000700
#define DERATESTAT1_REFRESH_RATE_RANK2_BIT_OFFSET                               8
#define DERATESTAT1_REFRESH_RATE_RANK3_MASK                            0x00007000
#define DERATESTAT1_REFRESH_RATE_RANK3_BIT_OFFSET                              12
#define DERATESTAT1_DERATE_TEMP_LIMIT_INTR_STS_RANK0_MASK              0x000F0000
#define DERATESTAT1_DERATE_TEMP_LIMIT_INTR_STS_RANK0_BIT_OFFSET                16
#define DERATESTAT1_DERATE_TEMP_LIMIT_INTR_STS_RANK1_MASK              0x00F00000
#define DERATESTAT1_DERATE_TEMP_LIMIT_INTR_STS_RANK1_BIT_OFFSET                20
#define DERATESTAT1_DERATE_TEMP_LIMIT_INTR_STS_RANK2_MASK              0x0F000000
#define DERATESTAT1_DERATE_TEMP_LIMIT_INTR_STS_RANK2_BIT_OFFSET                24
#define DERATESTAT1_DERATE_TEMP_LIMIT_INTR_STS_RANK3_MASK              0xF0000000
#define DERATESTAT1_DERATE_TEMP_LIMIT_INTR_STS_RANK3_BIT_OFFSET                28

#define DERATEDBGCTL                                                   0x00000128
#define DERATEDBGCTL_DBG_MR4_GRP_SEL_MASK                              0x00000007
#define DERATEDBGCTL_DBG_MR4_GRP_SEL_BIT_OFFSET                                 0
#define DERATEDBGCTL_DBG_MR4_RANK_SEL_MASK                             0x00000030
#define DERATEDBGCTL_DBG_MR4_RANK_SEL_BIT_OFFSET                                4

#define DERATEDBGSTAT                                                  0x0000012C
#define DERATEDBGSTAT_DBG_MR4_BYTE0_MASK                               0x000000FF
#define DERATEDBGSTAT_DBG_MR4_BYTE0_BIT_OFFSET                                  0
#define DERATEDBGSTAT_DBG_MR4_BYTE1_MASK                               0x0000FF00
#define DERATEDBGSTAT_DBG_MR4_BYTE1_BIT_OFFSET                                  8
#define DERATEDBGSTAT_DBG_MR4_BYTE2_MASK                               0x00FF0000
#define DERATEDBGSTAT_DBG_MR4_BYTE2_BIT_OFFSET                                 16
#define DERATEDBGSTAT_DBG_MR4_BYTE3_MASK                               0xFF000000
#define DERATEDBGSTAT_DBG_MR4_BYTE3_BIT_OFFSET                                 24

#define PWRCTL                                                         0x00000180
#define PWRCTL_SELFREF_EN_MASK                                         0x0000000F
#define PWRCTL_SELFREF_EN_BIT_OFFSET                                            0
#define PWRCTL_POWERDOWN_EN_MASK                                       0x000000F0
#define PWRCTL_POWERDOWN_EN_BIT_OFFSET                                          4
#define PWRCTL_ACTV_PD_EN_MASK                                         0x00000100
#define PWRCTL_ACTV_PD_EN_BIT_OFFSET                                            8
#define PWRCTL_EN_DFI_DRAM_CLK_DISABLE_MASK                            0x00000200
#define PWRCTL_EN_DFI_DRAM_CLK_DISABLE_BIT_OFFSET                               9
#define PWRCTL_MPSM_EN_MASK                                            0x00000400
#define PWRCTL_MPSM_EN_BIT_OFFSET                                              10
#define PWRCTL_SELFREF_SW_MASK                                         0x00000800
#define PWRCTL_SELFREF_SW_BIT_OFFSET                                           11
#define PWRCTL_STAY_IN_SELFREF_MASK                                    0x00008000
#define PWRCTL_STAY_IN_SELFREF_BIT_OFFSET                                      15
#define PWRCTL_DIS_CAM_DRAIN_SELFREF_MASK                              0x00010000
#define PWRCTL_DIS_CAM_DRAIN_SELFREF_BIT_OFFSET                                16
#define PWRCTL_LPDDR4_SR_ALLOWED_MASK                                  0x00020000
#define PWRCTL_LPDDR4_SR_ALLOWED_BIT_OFFSET                                    17
#define PWRCTL_DSM_EN_MASK                                             0x00040000
#define PWRCTL_DSM_EN_BIT_OFFSET                                               18
#define PWRCTL_MPSM_PD_EN_MASK                                         0x00F00000
#define PWRCTL_MPSM_PD_EN_BIT_OFFSET                                           20
#define PWRCTL_MPSM_DEEP_PD_EN_MASK                                    0xFF000000
#define PWRCTL_MPSM_DEEP_PD_EN_BIT_OFFSET                                      24

#define HWLPCTL                                                        0x00000184
#define HWLPCTL_HW_LP_EN_MASK                                          0x00000001
#define HWLPCTL_HW_LP_EN_BIT_OFFSET                                             0
#define HWLPCTL_HW_LP_EXIT_IDLE_EN_MASK                                0x00000002
#define HWLPCTL_HW_LP_EXIT_IDLE_EN_BIT_OFFSET                                   1
#define HWLPCTL_HW_LP_CTRL_MASK                                        0x00000004
#define HWLPCTL_HW_LP_CTRL_BIT_OFFSET                                           2
#define HWLPCTL_HW_LP_ACCEPT_WAIT_WINDOW_MASK                          0x00000F00
#define HWLPCTL_HW_LP_ACCEPT_WAIT_WINDOW_BIT_OFFSET                             8

#define HWLPCTL2                                                       0x00000188
#define HWLPCTL2_CACTIVE_IN_MASK_MASK                                  0xFFFFFFFF
#define HWLPCTL2_CACTIVE_IN_MASK_BIT_OFFSET                                     0

#define CLKGATECTL                                                     0x0000018C
#define CLKGATECTL_BSM_CLK_ON_MASK                                     0x0000003F
#define CLKGATECTL_BSM_CLK_ON_BIT_OFFSET                                        0

#define RFSHMOD0                                                       0x00000200
#define RFSHMOD0_REFRESH_BURST_MASK                                    0x0000003F
#define RFSHMOD0_REFRESH_BURST_BIT_OFFSET                                       0
#define RFSHMOD0_AUTO_REFAB_EN_MASK                                    0x000000C0
#define RFSHMOD0_AUTO_REFAB_EN_BIT_OFFSET                                       6
#define RFSHMOD0_PER_BANK_REFRESH_MASK                                 0x00000100
#define RFSHMOD0_PER_BANK_REFRESH_BIT_OFFSET                                    8
#define RFSHMOD0_PER_BANK_REFRESH_OPT_EN_MASK                          0x00000200
#define RFSHMOD0_PER_BANK_REFRESH_OPT_EN_BIT_OFFSET                             9
#define RFSHMOD0_REFRESH_BURST_2X_MASK                                 0x0000FC00
#define RFSHMOD0_REFRESH_BURST_2X_BIT_OFFSET                                   10
#define RFSHMOD0_MIXED_REFSB_HI_THR_MASK                               0x000F0000
#define RFSHMOD0_MIXED_REFSB_HI_THR_BIT_OFFSET                                 16
#define RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN_MASK                         0x01000000
#define RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN_BIT_OFFSET                           24

#define RFSHMOD1                                                       0x00000204
#define RFSHMOD1_SAME_BANK_REFRESH_MASK                                0x00000003
#define RFSHMOD1_SAME_BANK_REFRESH_BIT_OFFSET                                   0
#define RFSHMOD1_TCR_REFAB_THR_MASK                                    0x00000070
#define RFSHMOD1_TCR_REFAB_THR_BIT_OFFSET                                       4
#define RFSHMOD1_FGR_MODE_MASK                                         0x00000700
#define RFSHMOD1_FGR_MODE_BIT_OFFSET                                            8

#define RFSHCTL0                                                       0x00000208
#define RFSHCTL0_DIS_AUTO_REFRESH_MASK                                 0x00000001
#define RFSHCTL0_DIS_AUTO_REFRESH_BIT_OFFSET                                    0
#define RFSHCTL0_REFRESH_UPDATE_LEVEL_MASK                             0x00000010
#define RFSHCTL0_REFRESH_UPDATE_LEVEL_BIT_OFFSET                                4
#define RFSHCTL0_REF_3DS_BURST_LIMIT_EN_MASK                           0x00000100
#define RFSHCTL0_REF_3DS_BURST_LIMIT_EN_BIT_OFFSET                              8
#define RFSHCTL0_REF_3DS_BURST_LIMIT_THR_MASK                          0x00007E00
#define RFSHCTL0_REF_3DS_BURST_LIMIT_THR_BIT_OFFSET                             9
#define RFSHCTL0_RANK_DIS_REFRESH_MASK                                 0xFFFF0000
#define RFSHCTL0_RANK_DIS_REFRESH_BIT_OFFSET                                   16

#define RFMMOD0                                                        0x00000220
#define RFMMOD0_RFM_EN_MASK                                            0x00000001
#define RFMMOD0_RFM_EN_BIT_OFFSET                                               0
#define RFMMOD0_RFMSBC_MASK                                            0x00000010
#define RFMMOD0_RFMSBC_BIT_OFFSET                                               4
#define RFMMOD0_RAAIMT_MASK                                            0x00001F00
#define RFMMOD0_RAAIMT_BIT_OFFSET                                               8
#define RFMMOD0_RAAMULT_MASK                                           0x00030000
#define RFMMOD0_RAAMULT_BIT_OFFSET                                             16
#define RFMMOD0_RAADEC_MASK                                            0x000C0000
#define RFMMOD0_RAADEC_BIT_OFFSET                                              18
#define RFMMOD0_RFMTH_RM_THR_MASK                                      0x1F000000
#define RFMMOD0_RFMTH_RM_THR_BIT_OFFSET                                        24

#define RFMMOD1                                                        0x00000224
#define RFMMOD1_INIT_RAA_CNT_MASK                                      0x000007FF
#define RFMMOD1_INIT_RAA_CNT_BIT_OFFSET                                         0

#define RFMCTL                                                         0x00000228
#define RFMCTL_DBG_RAA_RANK_MASK                                       0x0000000F
#define RFMCTL_DBG_RAA_RANK_BIT_OFFSET                                          0
#define RFMCTL_DBG_RAA_BG_BANK_MASK                                    0xFFFFFFF0
#define RFMCTL_DBG_RAA_BG_BANK_BIT_OFFSET                                       4

#define RFMSTAT                                                        0x0000022C
#define RFMSTAT_RANK_RAA_CNT_GT0_MASK                                  0x0000FFFF
#define RFMSTAT_RANK_RAA_CNT_GT0_BIT_OFFSET                                     0
#define RFMSTAT_DBG_RAA_CNT_MASK                                       0x07FF0000
#define RFMSTAT_DBG_RAA_CNT_BIT_OFFSET                                         16

#define ZQCTL0                                                         0x00000280
#define ZQCTL0_DIS_MPSMX_ZQCL_MASK                                     0x10000000
#define ZQCTL0_DIS_MPSMX_ZQCL_BIT_OFFSET                                       28
#define ZQCTL0_ZQ_RESISTOR_SHARED_MASK                                 0x20000000
#define ZQCTL0_ZQ_RESISTOR_SHARED_BIT_OFFSET                                   29
#define ZQCTL0_DIS_AUTO_ZQ_MASK                                        0x80000000
#define ZQCTL0_DIS_AUTO_ZQ_BIT_OFFSET                                          31

#define ZQCTL1                                                         0x00000284
#define ZQCTL1_ZQ_RESET_MASK                                           0x00000001
#define ZQCTL1_ZQ_RESET_BIT_OFFSET                                              0

#define ZQCTL2                                                         0x00000288
#define ZQCTL2_DIS_SRX_ZQCL_MASK                                       0x00000001
#define ZQCTL2_DIS_SRX_ZQCL_BIT_OFFSET                                          0
#define ZQCTL2_DIS_SRX_ZQCL_HWFFC_MASK                                 0x00000002
#define ZQCTL2_DIS_SRX_ZQCL_HWFFC_BIT_OFFSET                                    1

#define ZQSTAT                                                         0x0000028C
#define ZQSTAT_ZQ_RESET_BUSY_MASK                                      0x00000001
#define ZQSTAT_ZQ_RESET_BUSY_BIT_OFFSET                                         0

#define DQSOSCRUNTIME                                                  0x00000300
#define DQSOSCRUNTIME_DQSOSC_RUNTIME_MASK                              0x000000FF
#define DQSOSCRUNTIME_DQSOSC_RUNTIME_BIT_OFFSET                                 0
#define DQSOSCRUNTIME_WCK2DQO_RUNTIME_MASK                             0x00FF0000
#define DQSOSCRUNTIME_WCK2DQO_RUNTIME_BIT_OFFSET                               16

#define DQSOSCSTAT0                                                    0x00000304
#define DQSOSCSTAT0_DQSOSC_STATE_MASK                                  0x00000007
#define DQSOSCSTAT0_DQSOSC_STATE_BIT_OFFSET                                     0
#define DQSOSCSTAT0_DQSOSC_PER_RANK_STAT_MASK                          0xFFFFFFF0
#define DQSOSCSTAT0_DQSOSC_PER_RANK_STAT_BIT_OFFSET                             4

#define DQSOSCCFG0                                                     0x00000308
#define DQSOSCCFG0_DIS_DQSOSC_SRX_MASK                                 0x00000001
#define DQSOSCCFG0_DIS_DQSOSC_SRX_BIT_OFFSET                                    0

#define DQSOSCTMG0                                                     0x0000030C
#define DQSOSCTMG0_T_OSCS_MASK                                         0x00003FFF
#define DQSOSCTMG0_T_OSCS_BIT_OFFSET                                            0
#define DQSOSCTMG0_T_TRKCALCCUR_MASK                                   0x01FF0000
#define DQSOSCTMG0_T_TRKCALCCUR_BIT_OFFSET                                     16

#define SCHED0                                                         0x00000380
#define SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH_MASK                      0x00000001
#define SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH_BIT_OFFSET                         0
#define SCHED0_PREFER_WRITE_MASK                                       0x00000002
#define SCHED0_PREFER_WRITE_BIT_OFFSET                                          1
#define SCHED0_PAGECLOSE_MASK                                          0x00000004
#define SCHED0_PAGECLOSE_BIT_OFFSET                                             2
#define SCHED0_RDWR_SWITCH_POLICY_SEL_MASK                             0x00000008
#define SCHED0_RDWR_SWITCH_POLICY_SEL_BIT_OFFSET                                3
#define SCHED0_OPT_WRCAM_FILL_LEVEL_MASK                               0x00000010
#define SCHED0_OPT_WRCAM_FILL_LEVEL_BIT_OFFSET                                  4
#define SCHED0_DIS_OPT_NTT_BY_ACT_MASK                                 0x00000020
#define SCHED0_DIS_OPT_NTT_BY_ACT_BIT_OFFSET                                    5
#define SCHED0_DIS_OPT_NTT_BY_PRE_MASK                                 0x00000040
#define SCHED0_DIS_OPT_NTT_BY_PRE_BIT_OFFSET                                    6
#define SCHED0_AUTOPRE_RMW_MASK                                        0x00000080
#define SCHED0_AUTOPRE_RMW_BIT_OFFSET                                           7
#define SCHED0_LPR_NUM_ENTRIES_MASK                                    0x00007F00
#define SCHED0_LPR_NUM_ENTRIES_BIT_OFFSET                                       8
#define SCHED0_LPDDR4_OPT_ACT_TIMING_MASK                              0x00008000
#define SCHED0_LPDDR4_OPT_ACT_TIMING_BIT_OFFSET                                15
#define SCHED0_LPDDR5_OPT_ACT_TIMING_MASK                              0x00010000
#define SCHED0_LPDDR5_OPT_ACT_TIMING_BIT_OFFSET                                16
#define SCHED0_W_STARVE_FREE_RUNNING_MASK                              0x01000000
#define SCHED0_W_STARVE_FREE_RUNNING_BIT_OFFSET                                24
#define SCHED0_DIS_PREFER_COL_BY_ACT_MASK                              0x02000000
#define SCHED0_DIS_PREFER_COL_BY_ACT_BIT_OFFSET                                25
#define SCHED0_DIS_PREFER_COL_BY_PRE_MASK                              0x04000000
#define SCHED0_DIS_PREFER_COL_BY_PRE_BIT_OFFSET                                26
#define SCHED0_OPT_ACT_LAT_MASK                                        0x08000000
#define SCHED0_OPT_ACT_LAT_BIT_OFFSET                                          27
#define SCHED0_EN_COUNT_EVERY_WR_MASK                                  0x10000000
#define SCHED0_EN_COUNT_EVERY_WR_BIT_OFFSET                                    28
#define SCHED0_PREFER_READ_MASK                                        0x20000000
#define SCHED0_PREFER_READ_BIT_OFFSET                                          29
#define SCHED0_DIS_SPECULATIVE_ACT_MASK                                0x40000000
#define SCHED0_DIS_SPECULATIVE_ACT_BIT_OFFSET                                  30
#define SCHED0_OPT_VPRW_SCH_MASK                                       0x80000000
#define SCHED0_OPT_VPRW_SCH_BIT_OFFSET                                         31

#define SCHED1                                                         0x00000384
#define SCHED1_DELAY_SWITCH_WRITE_MASK                                 0x0000F000
#define SCHED1_DELAY_SWITCH_WRITE_BIT_OFFSET                                   12
#define SCHED1_VISIBLE_WINDOW_LIMIT_WR_MASK                            0x00070000
#define SCHED1_VISIBLE_WINDOW_LIMIT_WR_BIT_OFFSET                              16
#define SCHED1_VISIBLE_WINDOW_LIMIT_RD_MASK                            0x00700000
#define SCHED1_VISIBLE_WINDOW_LIMIT_RD_BIT_OFFSET                              20
#define SCHED1_PAGE_HIT_LIMIT_WR_MASK                                  0x07000000
#define SCHED1_PAGE_HIT_LIMIT_WR_BIT_OFFSET                                    24
#define SCHED1_PAGE_HIT_LIMIT_RD_MASK                                  0x70000000
#define SCHED1_PAGE_HIT_LIMIT_RD_BIT_OFFSET                                    28
#define SCHED1_OPT_HIT_GT_HPR_MASK                                     0x80000000
#define SCHED1_OPT_HIT_GT_HPR_BIT_OFFSET                                       31

#define SCHED2                                                         0x00000388
#define SCHED2_DYN_BSM_MODE_MASK                                       0x00000001
#define SCHED2_DYN_BSM_MODE_BIT_OFFSET                                          0
#define SCHED2_MAX_NUM_ALLOC_BSM_CLR_MASK                              0x00000002
#define SCHED2_MAX_NUM_ALLOC_BSM_CLR_BIT_OFFSET                                 1
#define SCHED2_MAX_NUM_UNALLOC_ENTRIES_CLR_MASK                        0x00000004
#define SCHED2_MAX_NUM_UNALLOC_ENTRIES_CLR_BIT_OFFSET                           2
#define SCHED2_BANK_HIT_LIMIT_MASK                                     0x000000F0
#define SCHED2_BANK_HIT_LIMIT_BIT_OFFSET                                        4
#define SCHED2_DEALLOC_BSM_THR_MASK                                    0x0000FF00
#define SCHED2_DEALLOC_BSM_THR_BIT_OFFSET                                       8
#define SCHED2_DEALLOC_NUM_BSM_M1_MASK                                 0xFFFF0000
#define SCHED2_DEALLOC_NUM_BSM_M1_BIT_OFFSET                                   16

#define SCHED3                                                         0x0000038C
#define SCHED3_WRCAM_LOWTHRESH_MASK                                    0x000000FF
#define SCHED3_WRCAM_LOWTHRESH_BIT_OFFSET                                       0
#define SCHED3_WRCAM_HIGHTHRESH_MASK                                   0x0000FF00
#define SCHED3_WRCAM_HIGHTHRESH_BIT_OFFSET                                      8
#define SCHED3_WR_PGHIT_NUM_THRESH_MASK                                0x00FF0000
#define SCHED3_WR_PGHIT_NUM_THRESH_BIT_OFFSET                                  16
#define SCHED3_RD_PGHIT_NUM_THRESH_MASK                                0xFF000000
#define SCHED3_RD_PGHIT_NUM_THRESH_BIT_OFFSET                                  24

#define SCHED4                                                         0x00000390
#define SCHED4_RD_ACT_IDLE_GAP_MASK                                    0x000000FF
#define SCHED4_RD_ACT_IDLE_GAP_BIT_OFFSET                                       0
#define SCHED4_WR_ACT_IDLE_GAP_MASK                                    0x0000FF00
#define SCHED4_WR_ACT_IDLE_GAP_BIT_OFFSET                                       8
#define SCHED4_RD_PAGE_EXP_CYCLES_MASK                                 0x00FF0000
#define SCHED4_RD_PAGE_EXP_CYCLES_BIT_OFFSET                                   16
#define SCHED4_WR_PAGE_EXP_CYCLES_MASK                                 0xFF000000
#define SCHED4_WR_PAGE_EXP_CYCLES_BIT_OFFSET                                   24

#define SCHED5                                                         0x00000394
#define SCHED5_WRECC_CAM_LOWTHRESH_MASK                                0x000000FF
#define SCHED5_WRECC_CAM_LOWTHRESH_BIT_OFFSET                                   0
#define SCHED5_WRECC_CAM_HIGHTHRESH_MASK                               0x0FFFFF00
#define SCHED5_WRECC_CAM_HIGHTHRESH_BIT_OFFSET                                  8
#define SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL_MASK                0x10000000
#define SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL_BIT_OFFSET                  28
#define SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL_MASK                 0x20000000
#define SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL_BIT_OFFSET                   29

#define HWFFCCTL                                                       0x00000400
#define HWFFCCTL_HWFFC_EN_MASK                                         0x00000003
#define HWFFCCTL_HWFFC_EN_BIT_OFFSET                                            0
#define HWFFCCTL_HWFFC_ODT_EN_MASK                                     0x00000004
#define HWFFCCTL_HWFFC_ODT_EN_BIT_OFFSET                                        2
#define HWFFCCTL_HWFFC_VREF_EN_MASK                                    0x00000008
#define HWFFCCTL_HWFFC_VREF_EN_BIT_OFFSET                                       3
#define HWFFCCTL_INIT_FSP_MASK                                         0x00000010
#define HWFFCCTL_INIT_FSP_BIT_OFFSET                                            4
#define HWFFCCTL_INIT_VRCG_MASK                                        0x00000020
#define HWFFCCTL_INIT_VRCG_BIT_OFFSET                                           5
#define HWFFCCTL_TARGET_VRCG_MASK                                      0x00000040
#define HWFFCCTL_TARGET_VRCG_BIT_OFFSET                                         6
#define HWFFCCTL_CKE_POWER_DOWN_MODE_MASK                              0x00000080
#define HWFFCCTL_CKE_POWER_DOWN_MODE_BIT_OFFSET                                 7
#define HWFFCCTL_POWER_SAVING_CTRL_WORD_MASK                           0x00000F00
#define HWFFCCTL_POWER_SAVING_CTRL_WORD_BIT_OFFSET                              8
#define HWFFCCTL_CTRL_WORD_NUM_MASK                                    0x0000F000
#define HWFFCCTL_CTRL_WORD_NUM_BIT_OFFSET                                      12
#define HWFFCCTL_SKIP_MRW_ODTVREF_MASK                                 0x01000000
#define HWFFCCTL_SKIP_MRW_ODTVREF_BIT_OFFSET                                   24
#define HWFFCCTL_SKIP_ZQ_STOP_START_MASK                               0x02000000
#define HWFFCCTL_SKIP_ZQ_STOP_START_BIT_OFFSET                                 25
#define HWFFCCTL_ZQ_INTERVAL_MASK                                      0x0C000000
#define HWFFCCTL_ZQ_INTERVAL_BIT_OFFSET                                        26
#define HWFFCCTL_HWFFC_MODE_MASK                                       0x80000000
#define HWFFCCTL_HWFFC_MODE_BIT_OFFSET                                         31

#define HWFFCSTAT                                                      0x00000404
#define HWFFCSTAT_HWFFC_IN_PROGRESS_MASK                               0x00000001
#define HWFFCSTAT_HWFFC_IN_PROGRESS_BIT_OFFSET                                  0
#define HWFFCSTAT_HWFFC_OPERATING_MODE_MASK                            0x00000002
#define HWFFCSTAT_HWFFC_OPERATING_MODE_BIT_OFFSET                               1
#define HWFFCSTAT_CURRENT_FREQUENCY_MASK                               0x000000F0
#define HWFFCSTAT_CURRENT_FREQUENCY_BIT_OFFSET                                  4
#define HWFFCSTAT_CURRENT_FSP_MASK                                     0x00000100
#define HWFFCSTAT_CURRENT_FSP_BIT_OFFSET                                        8
#define HWFFCSTAT_CURRENT_VRCG_MASK                                    0x00000200
#define HWFFCSTAT_CURRENT_VRCG_BIT_OFFSET                                       9

#define HWFFC_MRWBUF_CTRL0                                             0x00000410
#define HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_ADDR_MASK                      0x00FF0000
#define HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_ADDR_BIT_OFFSET                        16
#define HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_SELECT_MASK                    0x3F000000
#define HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_SELECT_BIT_OFFSET                      24
#define HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_RW_TYPE_MASK                   0x40000000
#define HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_RW_TYPE_BIT_OFFSET                     30
#define HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_RW_START_MASK                  0x80000000
#define HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_RW_START_BIT_OFFSET                    31

#define HWFFC_MRWBUF_CTRL1                                             0x00000414
#define HWFFC_MRWBUF_CTRL1_HWFFC_MRWBUF_WDATA_MASK                     0xFFFFFFFF
#define HWFFC_MRWBUF_CTRL1_HWFFC_MRWBUF_WDATA_BIT_OFFSET                        0

#define HWFFC_MRWBUF_STAT                                              0x00000418
#define HWFFC_MRWBUF_STAT_HWFFC_MRWBUF_RDATA_MASK                      0xFFFFFFFF
#define HWFFC_MRWBUF_STAT_HWFFC_MRWBUF_RDATA_BIT_OFFSET                         0

#define DQMAP0                                                         0x00000480
#define DQMAP0_DQ_NIBBLE_MAP_0_3_MASK                                  0x000000FF
#define DQMAP0_DQ_NIBBLE_MAP_0_3_BIT_OFFSET                                     0
#define DQMAP0_DQ_NIBBLE_MAP_4_7_MASK                                  0x0000FF00
#define DQMAP0_DQ_NIBBLE_MAP_4_7_BIT_OFFSET                                     8
#define DQMAP0_DQ_NIBBLE_MAP_8_11_MASK                                 0x00FF0000
#define DQMAP0_DQ_NIBBLE_MAP_8_11_BIT_OFFSET                                   16
#define DQMAP0_DQ_NIBBLE_MAP_12_15_MASK                                0xFF000000
#define DQMAP0_DQ_NIBBLE_MAP_12_15_BIT_OFFSET                                  24

#define DQMAP1                                                         0x00000484
#define DQMAP1_DQ_NIBBLE_MAP_16_19_MASK                                0x000000FF
#define DQMAP1_DQ_NIBBLE_MAP_16_19_BIT_OFFSET                                   0
#define DQMAP1_DQ_NIBBLE_MAP_20_23_MASK                                0x0000FF00
#define DQMAP1_DQ_NIBBLE_MAP_20_23_BIT_OFFSET                                   8
#define DQMAP1_DQ_NIBBLE_MAP_24_27_MASK                                0x00FF0000
#define DQMAP1_DQ_NIBBLE_MAP_24_27_BIT_OFFSET                                  16
#define DQMAP1_DQ_NIBBLE_MAP_28_31_MASK                                0xFF000000
#define DQMAP1_DQ_NIBBLE_MAP_28_31_BIT_OFFSET                                  24

#define DQMAP2                                                         0x00000488
#define DQMAP2_DQ_NIBBLE_MAP_32_35_MASK                                0x000000FF
#define DQMAP2_DQ_NIBBLE_MAP_32_35_BIT_OFFSET                                   0
#define DQMAP2_DQ_NIBBLE_MAP_36_39_MASK                                0x0000FF00
#define DQMAP2_DQ_NIBBLE_MAP_36_39_BIT_OFFSET                                   8
#define DQMAP2_DQ_NIBBLE_MAP_40_43_MASK                                0x00FF0000
#define DQMAP2_DQ_NIBBLE_MAP_40_43_BIT_OFFSET                                  16
#define DQMAP2_DQ_NIBBLE_MAP_44_47_MASK                                0xFF000000
#define DQMAP2_DQ_NIBBLE_MAP_44_47_BIT_OFFSET                                  24

#define DQMAP3                                                         0x0000048C
#define DQMAP3_DQ_NIBBLE_MAP_48_51_MASK                                0x000000FF
#define DQMAP3_DQ_NIBBLE_MAP_48_51_BIT_OFFSET                                   0
#define DQMAP3_DQ_NIBBLE_MAP_52_55_MASK                                0x0000FF00
#define DQMAP3_DQ_NIBBLE_MAP_52_55_BIT_OFFSET                                   8
#define DQMAP3_DQ_NIBBLE_MAP_56_59_MASK                                0x00FF0000
#define DQMAP3_DQ_NIBBLE_MAP_56_59_BIT_OFFSET                                  16
#define DQMAP3_DQ_NIBBLE_MAP_60_63_MASK                                0xFF000000
#define DQMAP3_DQ_NIBBLE_MAP_60_63_BIT_OFFSET                                  24

#define DQMAP4                                                         0x00000490
#define DQMAP4_DQ_NIBBLE_MAP_CB_0_3_MASK                               0x000000FF
#define DQMAP4_DQ_NIBBLE_MAP_CB_0_3_BIT_OFFSET                                  0
#define DQMAP4_DQ_NIBBLE_MAP_CB_4_7_MASK                               0x0000FF00
#define DQMAP4_DQ_NIBBLE_MAP_CB_4_7_BIT_OFFSET                                  8
#define DQMAP4_DQ_NIBBLE_MAP_CB_8_11_MASK                              0x00FF0000
#define DQMAP4_DQ_NIBBLE_MAP_CB_8_11_BIT_OFFSET                                16
#define DQMAP4_DQ_NIBBLE_MAP_CB_12_15_MASK                             0xFF000000
#define DQMAP4_DQ_NIBBLE_MAP_CB_12_15_BIT_OFFSET                               24

#define DQMAP5                                                         0x00000494
#define DQMAP5_DIS_DQ_RANK_SWAP_MASK                                   0x00000001
#define DQMAP5_DIS_DQ_RANK_SWAP_BIT_OFFSET                                      0

#define DFILPCFG0                                                      0x00000500
#define DFILPCFG0_DFI_LP_EN_PD_MASK                                    0x00000001
#define DFILPCFG0_DFI_LP_EN_PD_BIT_OFFSET                                       0
#define DFILPCFG0_DFI_LP_EN_SR_MASK                                    0x00000010
#define DFILPCFG0_DFI_LP_EN_SR_BIT_OFFSET                                       4
#define DFILPCFG0_DFI_LP_EN_DSM_MASK                                   0x00000100
#define DFILPCFG0_DFI_LP_EN_DSM_BIT_OFFSET                                      8
#define DFILPCFG0_DFI_LP_EN_MPSM_MASK                                  0x00001000
#define DFILPCFG0_DFI_LP_EN_MPSM_BIT_OFFSET                                    12
#define DFILPCFG0_DFI_LP_EN_DATA_MASK                                  0x00010000
#define DFILPCFG0_DFI_LP_EN_DATA_BIT_OFFSET                                    16
#define DFILPCFG0_DFI_LP_DATA_REQ_EN_MASK                              0x00100000
#define DFILPCFG0_DFI_LP_DATA_REQ_EN_BIT_OFFSET                                20
#define DFILPCFG0_DFI_LP_EXTRA_GAP_MASK                                0x0F000000
#define DFILPCFG0_DFI_LP_EXTRA_GAP_BIT_OFFSET                                  24
#define DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA_MASK                       0x30000000
#define DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA_BIT_OFFSET                         28

#define DFIUPD0                                                        0x00000508
#define DFIUPD0_DFI_PHYUPD_EN_MASK                                     0x00008000
#define DFIUPD0_DFI_PHYUPD_EN_BIT_OFFSET                                       15
#define DFIUPD0_CTRLUPD_PRE_SRX_MASK                                   0x20000000
#define DFIUPD0_CTRLUPD_PRE_SRX_BIT_OFFSET                                     29
#define DFIUPD0_DIS_AUTO_CTRLUPD_SRX_MASK                              0x40000000
#define DFIUPD0_DIS_AUTO_CTRLUPD_SRX_BIT_OFFSET                                30
#define DFIUPD0_DIS_AUTO_CTRLUPD_MASK                                  0x80000000
#define DFIUPD0_DIS_AUTO_CTRLUPD_BIT_OFFSET                                    31

#define DFIUPD1                                                        0x0000050C
#define DFIUPD1_DFI_PHYUPD_TYPE0_WAIT_IDLE_MASK                        0x00000001
#define DFIUPD1_DFI_PHYUPD_TYPE0_WAIT_IDLE_BIT_OFFSET                           0
#define DFIUPD1_DFI_PHYUPD_TYPE1_WAIT_IDLE_MASK                        0x00000100
#define DFIUPD1_DFI_PHYUPD_TYPE1_WAIT_IDLE_BIT_OFFSET                           8
#define DFIUPD1_DFI_PHYUPD_TYPE2_WAIT_IDLE_MASK                        0x00010000
#define DFIUPD1_DFI_PHYUPD_TYPE2_WAIT_IDLE_BIT_OFFSET                          16
#define DFIUPD1_DFI_PHYUPD_TYPE3_WAIT_IDLE_MASK                        0x01000000
#define DFIUPD1_DFI_PHYUPD_TYPE3_WAIT_IDLE_BIT_OFFSET                          24

#define DFIMISC                                                        0x00000510
#define DFIMISC_DFI_INIT_COMPLETE_EN_MASK                              0x00000001
#define DFIMISC_DFI_INIT_COMPLETE_EN_BIT_OFFSET                                 0
#define DFIMISC_PHY_DBI_MODE_MASK                                      0x00000002
#define DFIMISC_PHY_DBI_MODE_BIT_OFFSET                                         1
#define DFIMISC_DFI_DATA_CS_POLARITY_MASK                              0x00000004
#define DFIMISC_DFI_DATA_CS_POLARITY_BIT_OFFSET                                 2
#define DFIMISC_SHARE_DFI_DRAM_CLK_DISABLE_MASK                        0x00000008
#define DFIMISC_SHARE_DFI_DRAM_CLK_DISABLE_BIT_OFFSET                           3
#define DFIMISC_DFI_RESET_N_MASK                                       0x00000010
#define DFIMISC_DFI_RESET_N_BIT_OFFSET                                          4
#define DFIMISC_DFI_INIT_START_MASK                                    0x00000020
#define DFIMISC_DFI_INIT_START_BIT_OFFSET                                       5
#define DFIMISC_DIS_DYN_ADR_TRI_MASK                                   0x00000040
#define DFIMISC_DIS_DYN_ADR_TRI_BIT_OFFSET                                      6
#define DFIMISC_LP_OPTIMIZED_WRITE_MASK                                0x00000080
#define DFIMISC_LP_OPTIMIZED_WRITE_BIT_OFFSET                                   7
#define DFIMISC_DFI_FREQUENCY_MASK                                     0x00001F00
#define DFIMISC_DFI_FREQUENCY_BIT_OFFSET                                        8
#define DFIMISC_DFI_FREQ_FSP_MASK                                      0x0000C000
#define DFIMISC_DFI_FREQ_FSP_BIT_OFFSET                                        14
#define DFIMISC_DFI_CHANNEL_MODE_MASK                                  0x00030000
#define DFIMISC_DFI_CHANNEL_MODE_BIT_OFFSET                                    16

#define DFISTAT                                                        0x00000514
#define DFISTAT_DFI_INIT_COMPLETE_MASK                                 0x00000001
#define DFISTAT_DFI_INIT_COMPLETE_BIT_OFFSET                                    0
#define DFISTAT_DFI_LP_CTRL_ACK_STAT_MASK                              0x00000002
#define DFISTAT_DFI_LP_CTRL_ACK_STAT_BIT_OFFSET                                 1
#define DFISTAT_DFI_LP_DATA_ACK_STAT_MASK                              0x00000004
#define DFISTAT_DFI_LP_DATA_ACK_STAT_BIT_OFFSET                                 2

#define DFIPHYMSTR                                                     0x00000518
#define DFIPHYMSTR_DFI_PHYMSTR_EN_MASK                                 0x00000001
#define DFIPHYMSTR_DFI_PHYMSTR_EN_BIT_OFFSET                                    0
#define DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32_MASK                        0xFF000000
#define DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32_BIT_OFFSET                          24

#define DFI0MSGCTL0                                                    0x00000520
#define DFI0MSGCTL0_DFI0_CTRLMSG_DATA_MASK                             0x0000FFFF
#define DFI0MSGCTL0_DFI0_CTRLMSG_DATA_BIT_OFFSET                                0
#define DFI0MSGCTL0_DFI0_CTRLMSG_CMD_MASK                              0x00FF0000
#define DFI0MSGCTL0_DFI0_CTRLMSG_CMD_BIT_OFFSET                                16
#define DFI0MSGCTL0_DFI0_CTRLMSG_TOUT_CLR_MASK                         0x01000000
#define DFI0MSGCTL0_DFI0_CTRLMSG_TOUT_CLR_BIT_OFFSET                           24
#define DFI0MSGCTL0_DFI0_CTRLMSG_REQ_MASK                              0x80000000
#define DFI0MSGCTL0_DFI0_CTRLMSG_REQ_BIT_OFFSET                                31

#define DFI0MSGSTAT0                                                   0x00000524
#define DFI0MSGSTAT0_DFI0_CTRLMSG_REQ_BUSY_MASK                        0x00000001
#define DFI0MSGSTAT0_DFI0_CTRLMSG_REQ_BUSY_BIT_OFFSET                           0
#define DFI0MSGSTAT0_DFI0_CTRLMSG_RESP_TOUT_MASK                       0x00010000
#define DFI0MSGSTAT0_DFI0_CTRLMSG_RESP_TOUT_BIT_OFFSET                         16

#define DFISBINTRPTCFG                                                 0x00000528
#define DFISBINTRPTCFG_DFI_SIDEBAND_TIMER_ERR_INTR_EN_MASK             0x00000001
#define DFISBINTRPTCFG_DFI_SIDEBAND_TIMER_ERR_INTR_EN_BIT_OFFSET                0
#define DFISBINTRPTCFG_DFI_SIDEBAND_TIMER_ERR_INTR_CLR_MASK            0x00000002
#define DFISBINTRPTCFG_DFI_SIDEBAND_TIMER_ERR_INTR_CLR_BIT_OFFSET               1
#define DFISBINTRPTCFG_DFI_SIDEBAND_TIMER_ERR_INTR_FORCE_MASK          0x00000004
#define DFISBINTRPTCFG_DFI_SIDEBAND_TIMER_ERR_INTR_FORCE_BIT_OFFSET             2

#define DFISBPOISONCFG                                                 0x00000530
#define DFISBPOISONCFG_DFI_TCTRLUPD_MIN_POISON_ERR_INJ_MASK            0x00000001
#define DFISBPOISONCFG_DFI_TCTRLUPD_MIN_POISON_ERR_INJ_BIT_OFFSET               0
#define DFISBPOISONCFG_DFI_TCTRLUPD_MAX_POISON_ERR_INJ_MASK            0x00000002
#define DFISBPOISONCFG_DFI_TCTRLUPD_MAX_POISON_ERR_INJ_BIT_OFFSET               1
#define DFISBPOISONCFG_DFI_TINIT_START_POISON_ERR_INJ_MASK             0x00000010
#define DFISBPOISONCFG_DFI_TINIT_START_POISON_ERR_INJ_BIT_OFFSET                4
#define DFISBPOISONCFG_DFI_TINIT_COMPLETE_POISON_ERR_INJ_MASK          0x00000020
#define DFISBPOISONCFG_DFI_TINIT_COMPLETE_POISON_ERR_INJ_BIT_OFFSET             5
#define DFISBPOISONCFG_DFI_TLP_CTRL_RESP_POISON_ERR_INJ_MASK           0x00000100
#define DFISBPOISONCFG_DFI_TLP_CTRL_RESP_POISON_ERR_INJ_BIT_OFFSET              8
#define DFISBPOISONCFG_DFI_TLP_DATA_RESP_POISON_ERR_INJ_MASK           0x00000200
#define DFISBPOISONCFG_DFI_TLP_DATA_RESP_POISON_ERR_INJ_BIT_OFFSET              9
#define DFISBPOISONCFG_DFI_TLP_CTRL_WAKEUP_POISON_ERR_INJ_MASK         0x00000400
#define DFISBPOISONCFG_DFI_TLP_CTRL_WAKEUP_POISON_ERR_INJ_BIT_OFFSET           10
#define DFISBPOISONCFG_DFI_TLP_DATA_WAKEUP_POISON_ERR_INJ_MASK         0x00000800
#define DFISBPOISONCFG_DFI_TLP_DATA_WAKEUP_POISON_ERR_INJ_BIT_OFFSET           11
#define DFISBPOISONCFG_DFI_TCTRLUPD_MIN_POISON_MARGIN_MASK             0x000F0000
#define DFISBPOISONCFG_DFI_TCTRLUPD_MIN_POISON_MARGIN_BIT_OFFSET               16
#define DFISBPOISONCFG_DFI_TINIT_START_POISON_MARGIN_MASK              0x00F00000
#define DFISBPOISONCFG_DFI_TINIT_START_POISON_MARGIN_BIT_OFFSET                20
#define DFISBPOISONCFG_DFI_TLP_CTRL_RESP_POISON_MARGIN_MASK            0x0F000000
#define DFISBPOISONCFG_DFI_TLP_CTRL_RESP_POISON_MARGIN_BIT_OFFSET              24
#define DFISBPOISONCFG_DFI_TLP_DATA_RESP_POISON_MARGIN_MASK            0xF0000000
#define DFISBPOISONCFG_DFI_TLP_DATA_RESP_POISON_MARGIN_BIT_OFFSET              28

#define DFISBTIMERSTAT                                                 0x00000538
#define DFISBTIMERSTAT_DFI_TCTRLUPD_MIN_ERROR_MASK                     0x00000002
#define DFISBTIMERSTAT_DFI_TCTRLUPD_MIN_ERROR_BIT_OFFSET                        1
#define DFISBTIMERSTAT_DFI_TCTRLUPD_MAX_ERROR_MASK                     0x00000004
#define DFISBTIMERSTAT_DFI_TCTRLUPD_MAX_ERROR_BIT_OFFSET                        2
#define DFISBTIMERSTAT_DFI_TINIT_START_ERROR_MASK                      0x00000010
#define DFISBTIMERSTAT_DFI_TINIT_START_ERROR_BIT_OFFSET                         4
#define DFISBTIMERSTAT_DFI_TINIT_COMPLETE_ERROR_MASK                   0x00000020
#define DFISBTIMERSTAT_DFI_TINIT_COMPLETE_ERROR_BIT_OFFSET                      5
#define DFISBTIMERSTAT_DFI_TLP_CTRL_RESP_ERROR_MASK                    0x00000100
#define DFISBTIMERSTAT_DFI_TLP_CTRL_RESP_ERROR_BIT_OFFSET                       8
#define DFISBTIMERSTAT_DFI_TLP_DATA_RESP_ERROR_MASK                    0x00000200
#define DFISBTIMERSTAT_DFI_TLP_DATA_RESP_ERROR_BIT_OFFSET                       9
#define DFISBTIMERSTAT_DFI_TLP_CTRL_WAKEUP_ERROR_MASK                  0x00000400
#define DFISBTIMERSTAT_DFI_TLP_CTRL_WAKEUP_ERROR_BIT_OFFSET                    10
#define DFISBTIMERSTAT_DFI_TLP_DATA_WAKEUP_ERROR_MASK                  0x00000800
#define DFISBTIMERSTAT_DFI_TLP_DATA_WAKEUP_ERROR_BIT_OFFSET                    11

#define DFISBTIMERSTAT1                                                0x00000540
#define DFISBTIMERSTAT1_DFI_SIDEBAND_TIMER_ERR_INTR_MASK               0x00000001
#define DFISBTIMERSTAT1_DFI_SIDEBAND_TIMER_ERR_INTR_BIT_OFFSET                  0

#define DFIERRINTRPTCFG                                                0x00000548
#define DFIERRINTRPTCFG_DFI_ERROR_INTR_EN_MASK                         0x00000001
#define DFIERRINTRPTCFG_DFI_ERROR_INTR_EN_BIT_OFFSET                            0
#define DFIERRINTRPTCFG_DFI_ERROR_INTR_CLR_MASK                        0x00000002
#define DFIERRINTRPTCFG_DFI_ERROR_INTR_CLR_BIT_OFFSET                           1
#define DFIERRINTRPTCFG_DFI_ERROR_INTR_FORCE_MASK                      0x00000004
#define DFIERRINTRPTCFG_DFI_ERROR_INTR_FORCE_BIT_OFFSET                         2

#define DFIERRORSTAT                                                   0x00000550
#define DFIERRORSTAT_DFI_ERROR_INTR_MASK                               0x00000001
#define DFIERRORSTAT_DFI_ERROR_INTR_BIT_OFFSET                                  0

#define DFIERRORSTAT1                                                  0x00000558
#define DFIERRORSTAT1_DFI_ERROR_INFO_MASK                              0x0000000F
#define DFIERRORSTAT1_DFI_ERROR_INFO_BIT_OFFSET                                 0

#define POISONCFG                                                      0x00000580
#define POISONCFG_WR_POISON_SLVERR_EN_MASK                             0x00000001
#define POISONCFG_WR_POISON_SLVERR_EN_BIT_OFFSET                                0
#define POISONCFG_WR_POISON_INTR_EN_MASK                               0x00000010
#define POISONCFG_WR_POISON_INTR_EN_BIT_OFFSET                                  4
#define POISONCFG_WR_POISON_INTR_CLR_MASK                              0x00000100
#define POISONCFG_WR_POISON_INTR_CLR_BIT_OFFSET                                 8
#define POISONCFG_RD_POISON_SLVERR_EN_MASK                             0x00010000
#define POISONCFG_RD_POISON_SLVERR_EN_BIT_OFFSET                               16
#define POISONCFG_RD_POISON_INTR_EN_MASK                               0x00100000
#define POISONCFG_RD_POISON_INTR_EN_BIT_OFFSET                                 20
#define POISONCFG_RD_POISON_INTR_CLR_MASK                              0x01000000
#define POISONCFG_RD_POISON_INTR_CLR_BIT_OFFSET                                24

#define POISONSTAT                                                     0x00000584
#define POISONSTAT_WR_POISON_INTR_0_MASK                               0x00000001
#define POISONSTAT_WR_POISON_INTR_0_BIT_OFFSET                                  0
#define POISONSTAT_WR_POISON_INTR_1_MASK                               0x00000002
#define POISONSTAT_WR_POISON_INTR_1_BIT_OFFSET                                  1
#define POISONSTAT_WR_POISON_INTR_2_MASK                               0x00000004
#define POISONSTAT_WR_POISON_INTR_2_BIT_OFFSET                                  2
#define POISONSTAT_WR_POISON_INTR_3_MASK                               0x00000008
#define POISONSTAT_WR_POISON_INTR_3_BIT_OFFSET                                  3
#define POISONSTAT_WR_POISON_INTR_4_MASK                               0x00000010
#define POISONSTAT_WR_POISON_INTR_4_BIT_OFFSET                                  4
#define POISONSTAT_WR_POISON_INTR_5_MASK                               0x00000020
#define POISONSTAT_WR_POISON_INTR_5_BIT_OFFSET                                  5
#define POISONSTAT_WR_POISON_INTR_6_MASK                               0x00000040
#define POISONSTAT_WR_POISON_INTR_6_BIT_OFFSET                                  6
#define POISONSTAT_WR_POISON_INTR_7_MASK                               0x00000080
#define POISONSTAT_WR_POISON_INTR_7_BIT_OFFSET                                  7
#define POISONSTAT_WR_POISON_INTR_8_MASK                               0x00000100
#define POISONSTAT_WR_POISON_INTR_8_BIT_OFFSET                                  8
#define POISONSTAT_WR_POISON_INTR_9_MASK                               0x00000200
#define POISONSTAT_WR_POISON_INTR_9_BIT_OFFSET                                  9
#define POISONSTAT_WR_POISON_INTR_10_MASK                              0x00000400
#define POISONSTAT_WR_POISON_INTR_10_BIT_OFFSET                                10
#define POISONSTAT_WR_POISON_INTR_11_MASK                              0x00000800
#define POISONSTAT_WR_POISON_INTR_11_BIT_OFFSET                                11
#define POISONSTAT_WR_POISON_INTR_12_MASK                              0x00001000
#define POISONSTAT_WR_POISON_INTR_12_BIT_OFFSET                                12
#define POISONSTAT_WR_POISON_INTR_13_MASK                              0x00002000
#define POISONSTAT_WR_POISON_INTR_13_BIT_OFFSET                                13
#define POISONSTAT_WR_POISON_INTR_14_MASK                              0x00004000
#define POISONSTAT_WR_POISON_INTR_14_BIT_OFFSET                                14
#define POISONSTAT_WR_POISON_INTR_15_MASK                              0x00008000
#define POISONSTAT_WR_POISON_INTR_15_BIT_OFFSET                                15
#define POISONSTAT_RD_POISON_INTR_0_MASK                               0x00010000
#define POISONSTAT_RD_POISON_INTR_0_BIT_OFFSET                                 16
#define POISONSTAT_RD_POISON_INTR_1_MASK                               0x00020000
#define POISONSTAT_RD_POISON_INTR_1_BIT_OFFSET                                 17
#define POISONSTAT_RD_POISON_INTR_2_MASK                               0x00040000
#define POISONSTAT_RD_POISON_INTR_2_BIT_OFFSET                                 18
#define POISONSTAT_RD_POISON_INTR_3_MASK                               0x00080000
#define POISONSTAT_RD_POISON_INTR_3_BIT_OFFSET                                 19
#define POISONSTAT_RD_POISON_INTR_4_MASK                               0x00100000
#define POISONSTAT_RD_POISON_INTR_4_BIT_OFFSET                                 20
#define POISONSTAT_RD_POISON_INTR_5_MASK                               0x00200000
#define POISONSTAT_RD_POISON_INTR_5_BIT_OFFSET                                 21
#define POISONSTAT_RD_POISON_INTR_6_MASK                               0x00400000
#define POISONSTAT_RD_POISON_INTR_6_BIT_OFFSET                                 22
#define POISONSTAT_RD_POISON_INTR_7_MASK                               0x00800000
#define POISONSTAT_RD_POISON_INTR_7_BIT_OFFSET                                 23
#define POISONSTAT_RD_POISON_INTR_8_MASK                               0x01000000
#define POISONSTAT_RD_POISON_INTR_8_BIT_OFFSET                                 24
#define POISONSTAT_RD_POISON_INTR_9_MASK                               0x02000000
#define POISONSTAT_RD_POISON_INTR_9_BIT_OFFSET                                 25
#define POISONSTAT_RD_POISON_INTR_10_MASK                              0x04000000
#define POISONSTAT_RD_POISON_INTR_10_BIT_OFFSET                                26
#define POISONSTAT_RD_POISON_INTR_11_MASK                              0x08000000
#define POISONSTAT_RD_POISON_INTR_11_BIT_OFFSET                                27
#define POISONSTAT_RD_POISON_INTR_12_MASK                              0x10000000
#define POISONSTAT_RD_POISON_INTR_12_BIT_OFFSET                                28
#define POISONSTAT_RD_POISON_INTR_13_MASK                              0x20000000
#define POISONSTAT_RD_POISON_INTR_13_BIT_OFFSET                                29
#define POISONSTAT_RD_POISON_INTR_14_MASK                              0x40000000
#define POISONSTAT_RD_POISON_INTR_14_BIT_OFFSET                                30
#define POISONSTAT_RD_POISON_INTR_15_MASK                              0x80000000
#define POISONSTAT_RD_POISON_INTR_15_BIT_OFFSET                                31

#define ECCCFG0                                                        0x00000600
#define ECCCFG0_ECC_MODE_MASK                                          0x00000007
#define ECCCFG0_ECC_MODE_BIT_OFFSET                                             0
#define ECCCFG0_TEST_MODE_MASK                                         0x00000008
#define ECCCFG0_TEST_MODE_BIT_OFFSET                                            3
#define ECCCFG0_ECC_TYPE_MASK                                          0x00000030
#define ECCCFG0_ECC_TYPE_BIT_OFFSET                                             4
#define ECCCFG0_ECC_AP_EN_MASK                                         0x00000040
#define ECCCFG0_ECC_AP_EN_BIT_OFFSET                                            6
#define ECCCFG0_ECC_REGION_REMAP_EN_MASK                               0x00000080
#define ECCCFG0_ECC_REGION_REMAP_EN_BIT_OFFSET                                  7
#define ECCCFG0_ECC_REGION_MAP_MASK                                    0x00007F00
#define ECCCFG0_ECC_REGION_MAP_BIT_OFFSET                                       8
#define ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32_MASK                         0x003F0000
#define ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32_BIT_OFFSET                           16
#define ECCCFG0_ECC_AP_ERR_THRESHOLD_MASK                              0x1F000000
#define ECCCFG0_ECC_AP_ERR_THRESHOLD_BIT_OFFSET                                24
#define ECCCFG0_ECC_REGION_MAP_OTHER_MASK                              0x20000000
#define ECCCFG0_ECC_REGION_MAP_OTHER_BIT_OFFSET                                29
#define ECCCFG0_ECC_REGION_MAP_GRANU_MASK                              0xC0000000
#define ECCCFG0_ECC_REGION_MAP_GRANU_BIT_OFFSET                                30

#define ECCCFG1                                                        0x00000604
#define ECCCFG1_DATA_POISON_EN_MASK                                    0x00000001
#define ECCCFG1_DATA_POISON_EN_BIT_OFFSET                                       0
#define ECCCFG1_DATA_POISON_BIT_MASK                                   0x00000002
#define ECCCFG1_DATA_POISON_BIT_BIT_OFFSET                                      1
#define ECCCFG1_POISON_CHIP_EN_MASK                                    0x00000004
#define ECCCFG1_POISON_CHIP_EN_BIT_OFFSET                                       2
#define ECCCFG1_ECC_AP_MODE_MASK                                       0x00000008
#define ECCCFG1_ECC_AP_MODE_BIT_OFFSET                                          3
#define ECCCFG1_ECC_REGION_PARITY_LOCK_MASK                            0x00000010
#define ECCCFG1_ECC_REGION_PARITY_LOCK_BIT_OFFSET                               4
#define ECCCFG1_ECC_REGION_WASTE_LOCK_MASK                             0x00000020
#define ECCCFG1_ECC_REGION_WASTE_LOCK_BIT_OFFSET                                5
#define ECCCFG1_MED_ECC_EN_MASK                                        0x00000040
#define ECCCFG1_MED_ECC_EN_BIT_OFFSET                                           6
#define ECCCFG1_BLK_CHANNEL_ACTIVE_TERM_MASK                           0x00000080
#define ECCCFG1_BLK_CHANNEL_ACTIVE_TERM_BIT_OFFSET                              7
#define ECCCFG1_ACTIVE_BLK_CHANNEL_MASK                                0x00001F00
#define ECCCFG1_ACTIVE_BLK_CHANNEL_BIT_OFFSET                                   8
#define ECCCFG1_POISON_ADVECC_KBD_MASK                                 0x00008000
#define ECCCFG1_POISON_ADVECC_KBD_BIT_OFFSET                                   15
#define ECCCFG1_POISON_NUM_DFI_BEAT_MASK                               0x000F0000
#define ECCCFG1_POISON_NUM_DFI_BEAT_BIT_OFFSET                                 16
#define ECCCFG1_PROP_RD_ECC_ERR_MASK                                   0x00300000
#define ECCCFG1_PROP_RD_ECC_ERR_BIT_OFFSET                                     20

#define ECCSTAT                                                        0x00000608
#define ECCSTAT_ECC_CORRECTED_BIT_NUM_MASK                             0x0000007F
#define ECCSTAT_ECC_CORRECTED_BIT_NUM_BIT_OFFSET                                0
#define ECCSTAT_ECC_CORRECTED_ERR_MASK                                 0x0000FF00
#define ECCSTAT_ECC_CORRECTED_ERR_BIT_OFFSET                                    8
#define ECCSTAT_ECC_UNCORRECTED_ERR_MASK                               0x00FF0000
#define ECCSTAT_ECC_UNCORRECTED_ERR_BIT_OFFSET                                 16
#define ECCSTAT_SBR_READ_ECC_CE_MASK                                   0x01000000
#define ECCSTAT_SBR_READ_ECC_CE_BIT_OFFSET                                     24
#define ECCSTAT_SBR_READ_ECC_UE_MASK                                   0x02000000
#define ECCSTAT_SBR_READ_ECC_UE_BIT_OFFSET                                     25

#define ECCCTL                                                         0x0000060C
#define ECCCTL_ECC_CORRECTED_ERR_CLR_MASK                              0x00000001
#define ECCCTL_ECC_CORRECTED_ERR_CLR_BIT_OFFSET                                 0
#define ECCCTL_ECC_UNCORRECTED_ERR_CLR_MASK                            0x00000002
#define ECCCTL_ECC_UNCORRECTED_ERR_CLR_BIT_OFFSET                               1
#define ECCCTL_ECC_CORR_ERR_CNT_CLR_MASK                               0x00000004
#define ECCCTL_ECC_CORR_ERR_CNT_CLR_BIT_OFFSET                                  2
#define ECCCTL_ECC_UNCORR_ERR_CNT_CLR_MASK                             0x00000008
#define ECCCTL_ECC_UNCORR_ERR_CNT_CLR_BIT_OFFSET                                3
#define ECCCTL_ECC_AP_ERR_INTR_CLR_MASK                                0x00000010
#define ECCCTL_ECC_AP_ERR_INTR_CLR_BIT_OFFSET                                   4
#define ECCCTL_ECC_CORRECTED_ERR_INTR_EN_MASK                          0x00000100
#define ECCCTL_ECC_CORRECTED_ERR_INTR_EN_BIT_OFFSET                             8
#define ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN_MASK                        0x00000200
#define ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN_BIT_OFFSET                           9
#define ECCCTL_ECC_AP_ERR_INTR_EN_MASK                                 0x00000400
#define ECCCTL_ECC_AP_ERR_INTR_EN_BIT_OFFSET                                   10
#define ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE_MASK                       0x00010000
#define ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE_BIT_OFFSET                         16
#define ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE_MASK                     0x00020000
#define ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE_BIT_OFFSET                       17
#define ECCCTL_ECC_AP_ERR_INTR_FORCE_MASK                              0x00040000
#define ECCCTL_ECC_AP_ERR_INTR_FORCE_BIT_OFFSET                                18

#define ECCERRCNT                                                      0x00000610
#define ECCERRCNT_ECC_CORR_ERR_CNT_MASK                                0x0000FFFF
#define ECCERRCNT_ECC_CORR_ERR_CNT_BIT_OFFSET                                   0
#define ECCERRCNT_ECC_UNCORR_ERR_CNT_MASK                              0xFFFF0000
#define ECCERRCNT_ECC_UNCORR_ERR_CNT_BIT_OFFSET                                16

#define ECCCADDR0                                                      0x00000614
#define ECCCADDR0_ECC_CORR_ROW_MASK                                    0x00FFFFFF
#define ECCCADDR0_ECC_CORR_ROW_BIT_OFFSET                                       0
#define ECCCADDR0_ECC_CORR_RANK_MASK                                   0xFF000000
#define ECCCADDR0_ECC_CORR_RANK_BIT_OFFSET                                     24

#define ECCCADDR1                                                      0x00000618
#define ECCCADDR1_ECC_CORR_COL_MASK                                    0x000007FF
#define ECCCADDR1_ECC_CORR_COL_BIT_OFFSET                                       0
#define ECCCADDR1_ECC_CORR_BANK_MASK                                   0x00FF0000
#define ECCCADDR1_ECC_CORR_BANK_BIT_OFFSET                                     16
#define ECCCADDR1_ECC_CORR_BG_MASK                                     0x0F000000
#define ECCCADDR1_ECC_CORR_BG_BIT_OFFSET                                       24
#define ECCCADDR1_ECC_CORR_CID_MASK                                    0xF0000000
#define ECCCADDR1_ECC_CORR_CID_BIT_OFFSET                                      28

#define ECCCSYN0                                                       0x0000061C
#define ECCCSYN0_ECC_CORR_SYNDROMES_31_0_MASK                          0xFFFFFFFF
#define ECCCSYN0_ECC_CORR_SYNDROMES_31_0_BIT_OFFSET                             0

#define ECCCSYN1                                                       0x00000620
#define ECCCSYN1_ECC_CORR_SYNDROMES_63_32_MASK                         0xFFFFFFFF
#define ECCCSYN1_ECC_CORR_SYNDROMES_63_32_BIT_OFFSET                            0

#define ECCCSYN2                                                       0x00000624
#define ECCCSYN2_ECC_CORR_SYNDROMES_71_64_MASK                         0x000000FF
#define ECCCSYN2_ECC_CORR_SYNDROMES_71_64_BIT_OFFSET                            0
#define ECCCSYN2_CB_CORR_SYNDROME_MASK                                 0x00FF0000
#define ECCCSYN2_CB_CORR_SYNDROME_BIT_OFFSET                                   16

#define ECCBITMASK0                                                    0x00000628
#define ECCBITMASK0_ECC_CORR_BIT_MASK_31_0_MASK                        0xFFFFFFFF
#define ECCBITMASK0_ECC_CORR_BIT_MASK_31_0_BIT_OFFSET                           0

#define ECCBITMASK1                                                    0x0000062C
#define ECCBITMASK1_ECC_CORR_BIT_MASK_63_32_MASK                       0xFFFFFFFF
#define ECCBITMASK1_ECC_CORR_BIT_MASK_63_32_BIT_OFFSET                          0

#define ECCBITMASK2                                                    0x00000630
#define ECCBITMASK2_ECC_CORR_BIT_MASK_71_64_MASK                       0x000000FF
#define ECCBITMASK2_ECC_CORR_BIT_MASK_71_64_BIT_OFFSET                          0

#define ECCUADDR0                                                      0x00000634
#define ECCUADDR0_ECC_UNCORR_ROW_MASK                                  0x00FFFFFF
#define ECCUADDR0_ECC_UNCORR_ROW_BIT_OFFSET                                     0
#define ECCUADDR0_ECC_UNCORR_RANK_MASK                                 0xFF000000
#define ECCUADDR0_ECC_UNCORR_RANK_BIT_OFFSET                                   24

#define ECCUADDR1                                                      0x00000638
#define ECCUADDR1_ECC_UNCORR_COL_MASK                                  0x000007FF
#define ECCUADDR1_ECC_UNCORR_COL_BIT_OFFSET                                     0
#define ECCUADDR1_ECC_UNCORR_BANK_MASK                                 0x00FF0000
#define ECCUADDR1_ECC_UNCORR_BANK_BIT_OFFSET                                   16
#define ECCUADDR1_ECC_UNCORR_BG_MASK                                   0x0F000000
#define ECCUADDR1_ECC_UNCORR_BG_BIT_OFFSET                                     24
#define ECCUADDR1_ECC_UNCORR_CID_MASK                                  0xF0000000
#define ECCUADDR1_ECC_UNCORR_CID_BIT_OFFSET                                    28

#define ECCUSYN0                                                       0x0000063C
#define ECCUSYN0_ECC_UNCORR_SYNDROMES_31_0_MASK                        0xFFFFFFFF
#define ECCUSYN0_ECC_UNCORR_SYNDROMES_31_0_BIT_OFFSET                           0

#define ECCUSYN1                                                       0x00000640
#define ECCUSYN1_ECC_UNCORR_SYNDROMES_63_32_MASK                       0xFFFFFFFF
#define ECCUSYN1_ECC_UNCORR_SYNDROMES_63_32_BIT_OFFSET                          0

#define ECCUSYN2                                                       0x00000644
#define ECCUSYN2_ECC_UNCORR_SYNDROMES_71_64_MASK                       0x000000FF
#define ECCUSYN2_ECC_UNCORR_SYNDROMES_71_64_BIT_OFFSET                          0
#define ECCUSYN2_CB_UNCORR_SYNDROME_MASK                               0x00FF0000
#define ECCUSYN2_CB_UNCORR_SYNDROME_BIT_OFFSET                                 16

#define ECCPOISONADDR0                                                 0x00000648
#define ECCPOISONADDR0_ECC_POISON_COL_MASK                             0x00000FFF
#define ECCPOISONADDR0_ECC_POISON_COL_BIT_OFFSET                                0
#define ECCPOISONADDR0_ECC_POISON_CID_MASK                             0x00FF0000
#define ECCPOISONADDR0_ECC_POISON_CID_BIT_OFFSET                               16
#define ECCPOISONADDR0_ECC_POISON_RANK_MASK                            0xFF000000
#define ECCPOISONADDR0_ECC_POISON_RANK_BIT_OFFSET                              24

#define ECCPOISONADDR1                                                 0x0000064C
#define ECCPOISONADDR1_ECC_POISON_ROW_MASK                             0x00FFFFFF
#define ECCPOISONADDR1_ECC_POISON_ROW_BIT_OFFSET                                0
#define ECCPOISONADDR1_ECC_POISON_BANK_MASK                            0x0F000000
#define ECCPOISONADDR1_ECC_POISON_BANK_BIT_OFFSET                              24
#define ECCPOISONADDR1_ECC_POISON_BG_MASK                              0xF0000000
#define ECCPOISONADDR1_ECC_POISON_BG_BIT_OFFSET                                28

#define ADVECCINDEX                                                    0x00000650
#define ADVECCINDEX_ECC_SYNDROME_SEL_MASK                              0x00000007
#define ADVECCINDEX_ECC_SYNDROME_SEL_BIT_OFFSET                                 0
#define ADVECCINDEX_ECC_ERR_SYMBOL_SEL_MASK                            0x00000018
#define ADVECCINDEX_ECC_ERR_SYMBOL_SEL_BIT_OFFSET                               3
#define ADVECCINDEX_ECC_POISON_BEATS_SEL_MASK                          0x000001E0
#define ADVECCINDEX_ECC_POISON_BEATS_SEL_BIT_OFFSET                             5

#define ADVECCSTAT                                                     0x00000654
#define ADVECCSTAT_ADVECC_CORRECTED_ERR_MASK                           0x00000001
#define ADVECCSTAT_ADVECC_CORRECTED_ERR_BIT_OFFSET                              0
#define ADVECCSTAT_ADVECC_UNCORRECTED_ERR_MASK                         0x00000002
#define ADVECCSTAT_ADVECC_UNCORRECTED_ERR_BIT_OFFSET                            1
#define ADVECCSTAT_ADVECC_NUM_ERR_SYMBOL_MASK                          0x0000001C
#define ADVECCSTAT_ADVECC_NUM_ERR_SYMBOL_BIT_OFFSET                             2
#define ADVECCSTAT_ADVECC_ERR_SYMBOL_POS_MASK                          0x0000FFE0
#define ADVECCSTAT_ADVECC_ERR_SYMBOL_POS_BIT_OFFSET                             5
#define ADVECCSTAT_ADVECC_ERR_SYMBOL_BITS_MASK                         0x00FF0000
#define ADVECCSTAT_ADVECC_ERR_SYMBOL_BITS_BIT_OFFSET                           16
#define ADVECCSTAT_ADVECC_CE_KBD_STAT_MASK                             0x0F000000
#define ADVECCSTAT_ADVECC_CE_KBD_STAT_BIT_OFFSET                               24
#define ADVECCSTAT_ADVECC_UE_KBD_STAT_MASK                             0x30000000
#define ADVECCSTAT_ADVECC_UE_KBD_STAT_BIT_OFFSET                               28
#define ADVECCSTAT_SBR_READ_ADVECC_CE_MASK                             0x40000000
#define ADVECCSTAT_SBR_READ_ADVECC_CE_BIT_OFFSET                               30
#define ADVECCSTAT_SBR_READ_ADVECC_UE_MASK                             0x80000000
#define ADVECCSTAT_SBR_READ_ADVECC_UE_BIT_OFFSET                               31

#define ECCPOISONPAT0                                                  0x00000658
#define ECCPOISONPAT0_ECC_POISON_DATA_31_0_MASK                        0xFFFFFFFF
#define ECCPOISONPAT0_ECC_POISON_DATA_31_0_BIT_OFFSET                           0

#define ECCPOISONPAT1                                                  0x0000065C
#define ECCPOISONPAT1_ECC_POISON_DATA_63_32_MASK                       0xFFFFFFFF
#define ECCPOISONPAT1_ECC_POISON_DATA_63_32_BIT_OFFSET                          0

#define ECCPOISONPAT2                                                  0x00000660
#define ECCPOISONPAT2_ECC_POISON_DATA_71_64_MASK                       0x000000FF
#define ECCPOISONPAT2_ECC_POISON_DATA_71_64_BIT_OFFSET                          0

#define ECCAPSTAT                                                      0x00000664
#define ECCAPSTAT_ECC_AP_ERR_MASK                                      0x00000001
#define ECCAPSTAT_ECC_AP_ERR_BIT_OFFSET                                         0

#define ECCCFG2                                                        0x00000668
#define ECCCFG2_BYPASS_INTERNAL_ECC_MASK                               0x00000001
#define ECCCFG2_BYPASS_INTERNAL_ECC_BIT_OFFSET                                  0
#define ECCCFG2_KBD_EN_MASK                                            0x00000002
#define ECCCFG2_KBD_EN_BIT_OFFSET                                               1
#define ECCCFG2_DIS_RMW_UE_PROPAGATION_MASK                            0x00000010
#define ECCCFG2_DIS_RMW_UE_PROPAGATION_BIT_OFFSET                               4
#define ECCCFG2_EAPAR_EN_MASK                                          0x00000100
#define ECCCFG2_EAPAR_EN_BIT_OFFSET                                             8
#define ECCCFG2_FLIP_BIT_POS0_MASK                                     0x007F0000
#define ECCCFG2_FLIP_BIT_POS0_BIT_OFFSET                                       16
#define ECCCFG2_FLIP_BIT_POS1_MASK                                     0x7F000000
#define ECCCFG2_FLIP_BIT_POS1_BIT_OFFSET                                       24

#define ECCCDATA0                                                      0x0000066C
#define ECCCDATA0_ECC_CORR_DATA_31_0_MASK                              0xFFFFFFFF
#define ECCCDATA0_ECC_CORR_DATA_31_0_BIT_OFFSET                                 0

#define ECCCDATA1                                                      0x00000670
#define ECCCDATA1_ECC_CORR_DATA_63_32_MASK                             0xFFFFFFFF
#define ECCCDATA1_ECC_CORR_DATA_63_32_BIT_OFFSET                                0

#define ECCUDATA0                                                      0x00000674
#define ECCUDATA0_ECC_UNCORR_DATA_31_0_MASK                            0xFFFFFFFF
#define ECCUDATA0_ECC_UNCORR_DATA_31_0_BIT_OFFSET                               0

#define ECCUDATA1                                                      0x00000678
#define ECCUDATA1_ECC_UNCORR_DATA_63_32_MASK                           0xFFFFFFFF
#define ECCUDATA1_ECC_UNCORR_DATA_63_32_BIT_OFFSET                              0

#define ECCSYMBOL                                                      0x0000067C
#define ECCSYMBOL_ECC_CORR_SYM_71_64_MASK                              0x000000FF
#define ECCSYMBOL_ECC_CORR_SYM_71_64_BIT_OFFSET                                 0
#define ECCSYMBOL_ECC_UNCORR_SYM_71_64_MASK                            0x00FF0000
#define ECCSYMBOL_ECC_UNCORR_SYM_71_64_BIT_OFFSET                              16

#define OCPARCFG0                                                      0x00000680
#define OCPARCFG0_OC_PARITY_EN_MASK                                    0x00000001
#define OCPARCFG0_OC_PARITY_EN_BIT_OFFSET                                       0
#define OCPARCFG0_OC_PARITY_TYPE_MASK                                  0x00000002
#define OCPARCFG0_OC_PARITY_TYPE_BIT_OFFSET                                     1
#define OCPARCFG0_PAR_WDATA_ERR_INTR_EN_MASK                           0x00000010
#define OCPARCFG0_PAR_WDATA_ERR_INTR_EN_BIT_OFFSET                              4
#define OCPARCFG0_PAR_WDATA_SLVERR_EN_MASK                             0x00000020
#define OCPARCFG0_PAR_WDATA_SLVERR_EN_BIT_OFFSET                                5
#define OCPARCFG0_PAR_WDATA_ERR_INTR_CLR_MASK                          0x00000040
#define OCPARCFG0_PAR_WDATA_ERR_INTR_CLR_BIT_OFFSET                             6
#define OCPARCFG0_PAR_WDATA_ERR_INTR_FORCE_MASK                        0x00000080
#define OCPARCFG0_PAR_WDATA_ERR_INTR_FORCE_BIT_OFFSET                           7
#define OCPARCFG0_PAR_WDATA_AXI_CHECK_BYPASS_EN_MASK                   0x00000100
#define OCPARCFG0_PAR_WDATA_AXI_CHECK_BYPASS_EN_BIT_OFFSET                      8
#define OCPARCFG0_PAR_RDATA_SLVERR_EN_MASK                             0x00001000
#define OCPARCFG0_PAR_RDATA_SLVERR_EN_BIT_OFFSET                               12
#define OCPARCFG0_PAR_RDATA_ERR_INTR_EN_MASK                           0x00002000
#define OCPARCFG0_PAR_RDATA_ERR_INTR_EN_BIT_OFFSET                             13
#define OCPARCFG0_PAR_RDATA_ERR_INTR_CLR_MASK                          0x00004000
#define OCPARCFG0_PAR_RDATA_ERR_INTR_CLR_BIT_OFFSET                            14
#define OCPARCFG0_PAR_RDATA_ERR_INTR_FORCE_MASK                        0x00008000
#define OCPARCFG0_PAR_RDATA_ERR_INTR_FORCE_BIT_OFFSET                          15
#define OCPARCFG0_PAR_ADDR_SLVERR_EN_MASK                              0x00100000
#define OCPARCFG0_PAR_ADDR_SLVERR_EN_BIT_OFFSET                                20
#define OCPARCFG0_PAR_WADDR_ERR_INTR_EN_MASK                           0x00200000
#define OCPARCFG0_PAR_WADDR_ERR_INTR_EN_BIT_OFFSET                             21
#define OCPARCFG0_PAR_WADDR_ERR_INTR_CLR_MASK                          0x00400000
#define OCPARCFG0_PAR_WADDR_ERR_INTR_CLR_BIT_OFFSET                            22
#define OCPARCFG0_PAR_RADDR_ERR_INTR_EN_MASK                           0x00800000
#define OCPARCFG0_PAR_RADDR_ERR_INTR_EN_BIT_OFFSET                             23
#define OCPARCFG0_PAR_RADDR_ERR_INTR_CLR_MASK                          0x01000000
#define OCPARCFG0_PAR_RADDR_ERR_INTR_CLR_BIT_OFFSET                            24
#define OCPARCFG0_PAR_WADDR_ERR_INTR_FORCE_MASK                        0x02000000
#define OCPARCFG0_PAR_WADDR_ERR_INTR_FORCE_BIT_OFFSET                          25
#define OCPARCFG0_PAR_RADDR_ERR_INTR_FORCE_MASK                        0x04000000
#define OCPARCFG0_PAR_RADDR_ERR_INTR_FORCE_BIT_OFFSET                          26

#define OCPARCFG1                                                      0x00000684
#define OCPARCFG1_PAR_POISON_EN_MASK                                   0x00000001
#define OCPARCFG1_PAR_POISON_EN_BIT_OFFSET                                      0
#define OCPARCFG1_PAR_POISON_LOC_RD_DFI_MASK                           0x00000004
#define OCPARCFG1_PAR_POISON_LOC_RD_DFI_BIT_OFFSET                              2
#define OCPARCFG1_PAR_POISON_LOC_RD_IECC_TYPE_MASK                     0x00000008
#define OCPARCFG1_PAR_POISON_LOC_RD_IECC_TYPE_BIT_OFFSET                        3
#define OCPARCFG1_PAR_POISON_LOC_RD_PORT_MASK                          0x000000F0
#define OCPARCFG1_PAR_POISON_LOC_RD_PORT_BIT_OFFSET                             4
#define OCPARCFG1_PAR_POISON_LOC_WR_PORT_MASK                          0x00000F00
#define OCPARCFG1_PAR_POISON_LOC_WR_PORT_BIT_OFFSET                             8
#define OCPARCFG1_PAR_POISON_BYTE_NUM_MASK                             0xFFFF0000
#define OCPARCFG1_PAR_POISON_BYTE_NUM_BIT_OFFSET                               16

#define OCPARSTAT0                                                     0x00000688
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_0_MASK                           0x00000001
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_0_BIT_OFFSET                              0
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_1_MASK                           0x00000002
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_1_BIT_OFFSET                              1
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_2_MASK                           0x00000004
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_2_BIT_OFFSET                              2
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_3_MASK                           0x00000008
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_3_BIT_OFFSET                              3
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_4_MASK                           0x00000010
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_4_BIT_OFFSET                              4
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_5_MASK                           0x00000020
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_5_BIT_OFFSET                              5
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_6_MASK                           0x00000040
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_6_BIT_OFFSET                              6
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_7_MASK                           0x00000080
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_7_BIT_OFFSET                              7
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_8_MASK                           0x00000100
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_8_BIT_OFFSET                              8
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_9_MASK                           0x00000200
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_9_BIT_OFFSET                              9
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_10_MASK                          0x00000400
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_10_BIT_OFFSET                            10
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_11_MASK                          0x00000800
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_11_BIT_OFFSET                            11
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_12_MASK                          0x00001000
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_12_BIT_OFFSET                            12
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_13_MASK                          0x00002000
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_13_BIT_OFFSET                            13
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_14_MASK                          0x00004000
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_14_BIT_OFFSET                            14
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_15_MASK                          0x00008000
#define OCPARSTAT0_PAR_WADDR_ERR_INTR_15_BIT_OFFSET                            15
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_0_MASK                           0x00010000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_0_BIT_OFFSET                             16
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_1_MASK                           0x00020000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_1_BIT_OFFSET                             17
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_2_MASK                           0x00040000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_2_BIT_OFFSET                             18
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_3_MASK                           0x00080000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_3_BIT_OFFSET                             19
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_4_MASK                           0x00100000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_4_BIT_OFFSET                             20
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_5_MASK                           0x00200000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_5_BIT_OFFSET                             21
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_6_MASK                           0x00400000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_6_BIT_OFFSET                             22
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_7_MASK                           0x00800000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_7_BIT_OFFSET                             23
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_8_MASK                           0x01000000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_8_BIT_OFFSET                             24
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_9_MASK                           0x02000000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_9_BIT_OFFSET                             25
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_10_MASK                          0x04000000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_10_BIT_OFFSET                            26
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_11_MASK                          0x08000000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_11_BIT_OFFSET                            27
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_12_MASK                          0x10000000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_12_BIT_OFFSET                            28
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_13_MASK                          0x20000000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_13_BIT_OFFSET                            29
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_14_MASK                          0x40000000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_14_BIT_OFFSET                            30
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_15_MASK                          0x80000000
#define OCPARSTAT0_PAR_RADDR_ERR_INTR_15_BIT_OFFSET                            31

#define OCPARSTAT1                                                     0x0000068C
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_0_MASK                        0x00000001
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_0_BIT_OFFSET                           0
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_1_MASK                        0x00000002
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_1_BIT_OFFSET                           1
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_2_MASK                        0x00000004
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_2_BIT_OFFSET                           2
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_3_MASK                        0x00000008
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_3_BIT_OFFSET                           3
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_4_MASK                        0x00000010
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_4_BIT_OFFSET                           4
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_5_MASK                        0x00000020
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_5_BIT_OFFSET                           5
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_6_MASK                        0x00000040
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_6_BIT_OFFSET                           6
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_7_MASK                        0x00000080
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_7_BIT_OFFSET                           7
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_8_MASK                        0x00000100
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_8_BIT_OFFSET                           8
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_9_MASK                        0x00000200
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_9_BIT_OFFSET                           9
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_10_MASK                       0x00000400
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_10_BIT_OFFSET                         10
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_11_MASK                       0x00000800
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_11_BIT_OFFSET                         11
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_12_MASK                       0x00001000
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_12_BIT_OFFSET                         12
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_13_MASK                       0x00002000
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_13_BIT_OFFSET                         13
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_14_MASK                       0x00004000
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_14_BIT_OFFSET                         14
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_15_MASK                       0x00008000
#define OCPARSTAT1_PAR_WDATA_IN_ERR_INTR_15_BIT_OFFSET                         15
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_0_MASK                           0x00010000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_0_BIT_OFFSET                             16
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_1_MASK                           0x00020000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_1_BIT_OFFSET                             17
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_2_MASK                           0x00040000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_2_BIT_OFFSET                             18
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_3_MASK                           0x00080000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_3_BIT_OFFSET                             19
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_4_MASK                           0x00100000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_4_BIT_OFFSET                             20
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_5_MASK                           0x00200000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_5_BIT_OFFSET                             21
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_6_MASK                           0x00400000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_6_BIT_OFFSET                             22
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_7_MASK                           0x00800000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_7_BIT_OFFSET                             23
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_8_MASK                           0x01000000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_8_BIT_OFFSET                             24
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_9_MASK                           0x02000000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_9_BIT_OFFSET                             25
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_10_MASK                          0x04000000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_10_BIT_OFFSET                            26
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_11_MASK                          0x08000000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_11_BIT_OFFSET                            27
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_12_MASK                          0x10000000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_12_BIT_OFFSET                            28
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_13_MASK                          0x20000000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_13_BIT_OFFSET                            29
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_14_MASK                          0x40000000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_14_BIT_OFFSET                            30
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_15_MASK                          0x80000000
#define OCPARSTAT1_PAR_RDATA_ERR_INTR_15_BIT_OFFSET                            31

#define OCPARSTAT2                                                     0x00000690
#define OCPARSTAT2_PAR_WDATA_OUT_ERR_INTR_MASK                         0x0000000F
#define OCPARSTAT2_PAR_WDATA_OUT_ERR_INTR_BIT_OFFSET                            0
#define OCPARSTAT2_PAR_RDATA_IN_ERR_ECC_INTR_MASK                      0x00000010
#define OCPARSTAT2_PAR_RDATA_IN_ERR_ECC_INTR_BIT_OFFSET                         4
#define OCPARSTAT2_PAR_RDATA_LOG_PORT_NUM_MASK                         0x00000F00
#define OCPARSTAT2_PAR_RDATA_LOG_PORT_NUM_BIT_OFFSET                            8

#define OCPARSTAT3                                                     0x00000694
#define OCPARSTAT3_PAR_RDATA_LOG_BYTE_NUM_MASK                         0xFFFFFFFF
#define OCPARSTAT3_PAR_RDATA_LOG_BYTE_NUM_BIT_OFFSET                            0

#define OCPARSTAT4                                                     0x00000698
#define OCPARSTAT4_PAR_WADDR_LOG_LOW_MASK                              0xFFFFFFFF
#define OCPARSTAT4_PAR_WADDR_LOG_LOW_BIT_OFFSET                                 0

#define OCPARSTAT5                                                     0x0000069C
#define OCPARSTAT5_PAR_WADDR_LOG_HIGH_MASK                             0x0FFFFFFF
#define OCPARSTAT5_PAR_WADDR_LOG_HIGH_BIT_OFFSET                                0
#define OCPARSTAT5_PAR_WADDR_LOG_PORT_NUM_MASK                         0xF0000000
#define OCPARSTAT5_PAR_WADDR_LOG_PORT_NUM_BIT_OFFSET                           28

#define OCPARSTAT6                                                     0x000006A0
#define OCPARSTAT6_PAR_RADDR_LOG_LOW_MASK                              0xFFFFFFFF
#define OCPARSTAT6_PAR_RADDR_LOG_LOW_BIT_OFFSET                                 0

#define OCPARSTAT7                                                     0x000006A4
#define OCPARSTAT7_PAR_RADDR_LOG_HIGH_MASK                             0x0FFFFFFF
#define OCPARSTAT7_PAR_RADDR_LOG_HIGH_BIT_OFFSET                                0
#define OCPARSTAT7_PAR_RADDR_LOG_PORT_NUM_MASK                         0xF0000000
#define OCPARSTAT7_PAR_RADDR_LOG_PORT_NUM_BIT_OFFSET                           28

#define OCPARSTAT8                                                     0x000006A8
#define OCPARSTAT8_PAR_RDATA_LOG_HIGH_BYTE_NUM_MASK                    0xFFFFFFFF
#define OCPARSTAT8_PAR_RDATA_LOG_HIGH_BYTE_NUM_BIT_OFFSET                       0

#define OCSAPCFG0                                                      0x000006B0
#define OCSAPCFG0_OCSAP_PAR_EN_MASK                                    0x00000001
#define OCSAPCFG0_OCSAP_PAR_EN_BIT_OFFSET                                       0
#define OCSAPCFG0_OCSAP_POISON_EN_MASK                                 0x00000100
#define OCSAPCFG0_OCSAP_POISON_EN_BIT_OFFSET                                    8
#define OCSAPCFG0_WDATARAM_ADDR_POISON_LOC_MASK                        0x00001000
#define OCSAPCFG0_WDATARAM_ADDR_POISON_LOC_BIT_OFFSET                          12
#define OCSAPCFG0_RDATARAM_ADDR_POISON_LOC_MASK                        0x00002000
#define OCSAPCFG0_RDATARAM_ADDR_POISON_LOC_BIT_OFFSET                          13
#define OCSAPCFG0_WDATARAM_ADDR_POISON_CTL_MASK                        0x00070000
#define OCSAPCFG0_WDATARAM_ADDR_POISON_CTL_BIT_OFFSET                          16
#define OCSAPCFG0_RDATARAM_ADDR_POISON_CTL_MASK                        0x07000000
#define OCSAPCFG0_RDATARAM_ADDR_POISON_CTL_BIT_OFFSET                          24
#define OCSAPCFG0_RDATARAM_ADDR_POISON_PORT_MASK                       0xF0000000
#define OCSAPCFG0_RDATARAM_ADDR_POISON_PORT_BIT_OFFSET                         28

#define OCECCCFG0                                                      0x00000700
#define OCECCCFG0_OCECC_EN_MASK                                        0x00000001
#define OCECCCFG0_OCECC_EN_BIT_OFFSET                                           0
#define OCECCCFG0_OCECC_FEC_EN_MASK                                    0x00000002
#define OCECCCFG0_OCECC_FEC_EN_BIT_OFFSET                                       1
#define OCECCCFG0_OCECC_UNCORRECTED_ERR_INTR_EN_MASK                   0x00000010
#define OCECCCFG0_OCECC_UNCORRECTED_ERR_INTR_EN_BIT_OFFSET                      4
#define OCECCCFG0_OCECC_WDATA_SLVERR_EN_MASK                           0x00000020
#define OCECCCFG0_OCECC_WDATA_SLVERR_EN_BIT_OFFSET                              5
#define OCECCCFG0_OCECC_UNCORRECTED_ERR_INTR_CLR_MASK                  0x00000040
#define OCECCCFG0_OCECC_UNCORRECTED_ERR_INTR_CLR_BIT_OFFSET                     6
#define OCECCCFG0_OCECC_UNCORRECTED_ERR_INTR_FORCE_MASK                0x00000080
#define OCECCCFG0_OCECC_UNCORRECTED_ERR_INTR_FORCE_BIT_OFFSET                   7
#define OCECCCFG0_OCECC_CORRECTED_ERR_INTR_EN_MASK                     0x00001000
#define OCECCCFG0_OCECC_CORRECTED_ERR_INTR_EN_BIT_OFFSET                       12
#define OCECCCFG0_OCECC_RDATA_SLVERR_EN_MASK                           0x00002000
#define OCECCCFG0_OCECC_RDATA_SLVERR_EN_BIT_OFFSET                             13
#define OCECCCFG0_OCECC_CORRECTED_ERR_INTR_CLR_MASK                    0x00004000
#define OCECCCFG0_OCECC_CORRECTED_ERR_INTR_CLR_BIT_OFFSET                      14
#define OCECCCFG0_OCECC_CORRECTED_ERR_INTR_FORCE_MASK                  0x00008000
#define OCECCCFG0_OCECC_CORRECTED_ERR_INTR_FORCE_BIT_OFFSET                    15

#define OCECCCFG1                                                      0x00000704
#define OCECCCFG1_OCECC_POISON_EN_MASK                                 0x00000001
#define OCECCCFG1_OCECC_POISON_EN_BIT_OFFSET                                    0
#define OCECCCFG1_OCECC_POISON_EGEN_MR_RD_0_MASK                       0x00000002
#define OCECCCFG1_OCECC_POISON_EGEN_MR_RD_0_BIT_OFFSET                          1
#define OCECCCFG1_OCECC_POISON_EGEN_MR_RD_0_BYTE_NUM_MASK              0x0000007C
#define OCECCCFG1_OCECC_POISON_EGEN_MR_RD_0_BYTE_NUM_BIT_OFFSET                 2
#define OCECCCFG1_OCECC_POISON_EGEN_XPI_RD_OUT_MASK                    0x00000080
#define OCECCCFG1_OCECC_POISON_EGEN_XPI_RD_OUT_BIT_OFFSET                       7
#define OCECCCFG1_OCECC_POISON_PORT_NUM_MASK                           0x00000F00
#define OCECCCFG1_OCECC_POISON_PORT_NUM_BIT_OFFSET                              8
#define OCECCCFG1_OCECC_POISON_EGEN_MR_RD_1_MASK                       0x00001000
#define OCECCCFG1_OCECC_POISON_EGEN_MR_RD_1_BIT_OFFSET                         12
#define OCECCCFG1_OCECC_POISON_EGEN_MR_RD_1_BYTE_NUM_MASK              0x0003E000
#define OCECCCFG1_OCECC_POISON_EGEN_MR_RD_1_BYTE_NUM_BIT_OFFSET                13
#define OCECCCFG1_OCECC_POISON_EGEN_XPI_RD_0_MASK                      0x00040000
#define OCECCCFG1_OCECC_POISON_EGEN_XPI_RD_0_BIT_OFFSET                        18
#define OCECCCFG1_OCECC_POISON_ECC_CORR_UNCORR_MASK                    0x00180000
#define OCECCCFG1_OCECC_POISON_ECC_CORR_UNCORR_BIT_OFFSET                      19
#define OCECCCFG1_OCECC_POISON_PGEN_RD_MASK                            0x00200000
#define OCECCCFG1_OCECC_POISON_PGEN_RD_BIT_OFFSET                              21
#define OCECCCFG1_OCECC_POISON_PGEN_MR_WDATA_MASK                      0x00400000
#define OCECCCFG1_OCECC_POISON_PGEN_MR_WDATA_BIT_OFFSET                        22
#define OCECCCFG1_OCECC_POISON_PGEN_MR_ECC_MASK                        0x00800000
#define OCECCCFG1_OCECC_POISON_PGEN_MR_ECC_BIT_OFFSET                          23

#define OCECCSTAT0                                                     0x00000708
#define OCECCSTAT0_OCECC_UNCORRECTED_ERR_MASK                          0x00000001
#define OCECCSTAT0_OCECC_UNCORRECTED_ERR_BIT_OFFSET                             0
#define OCECCSTAT0_OCECC_CORRECTED_ERR_MASK                            0x00000002
#define OCECCSTAT0_OCECC_CORRECTED_ERR_BIT_OFFSET                               1
#define OCECCSTAT0_OCECC_ERR_DDRC_MR_RD_MASK                           0x00020000
#define OCECCSTAT0_OCECC_ERR_DDRC_MR_RD_BIT_OFFSET                             17
#define OCECCSTAT0_PAR_ERR_MR_WDATA_MASK                               0x00040000
#define OCECCSTAT0_PAR_ERR_MR_WDATA_BIT_OFFSET                                 18
#define OCECCSTAT0_PAR_ERR_MR_ECC_MASK                                 0x00080000
#define OCECCSTAT0_PAR_ERR_MR_ECC_BIT_OFFSET                                   19
#define OCECCSTAT0_PAR_ERR_RD_MASK                                     0x00100000
#define OCECCSTAT0_PAR_ERR_RD_BIT_OFFSET                                       20

#define OCECCSTAT1                                                     0x0000070C
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_0_MASK                          0x00000001
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_0_BIT_OFFSET                             0
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_1_MASK                          0x00000002
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_1_BIT_OFFSET                             1
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_2_MASK                          0x00000004
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_2_BIT_OFFSET                             2
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_3_MASK                          0x00000008
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_3_BIT_OFFSET                             3
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_4_MASK                          0x00000010
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_4_BIT_OFFSET                             4
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_5_MASK                          0x00000020
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_5_BIT_OFFSET                             5
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_6_MASK                          0x00000040
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_6_BIT_OFFSET                             6
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_7_MASK                          0x00000080
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_7_BIT_OFFSET                             7
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_8_MASK                          0x00000100
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_8_BIT_OFFSET                             8
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_9_MASK                          0x00000200
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_9_BIT_OFFSET                             9
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_10_MASK                         0x00000400
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_10_BIT_OFFSET                           10
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_11_MASK                         0x00000800
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_11_BIT_OFFSET                           11
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_12_MASK                         0x00001000
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_12_BIT_OFFSET                           12
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_13_MASK                         0x00002000
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_13_BIT_OFFSET                           13
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_14_MASK                         0x00004000
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_14_BIT_OFFSET                           14
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_15_MASK                         0x00008000
#define OCECCSTAT1_OCECC_ERR_XPI_WR_IN_15_BIT_OFFSET                           15
#define OCECCSTAT1_OCECC_ERR_XPI_RD_0_MASK                             0x00010000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_0_BIT_OFFSET                               16
#define OCECCSTAT1_OCECC_ERR_XPI_RD_1_MASK                             0x00020000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_1_BIT_OFFSET                               17
#define OCECCSTAT1_OCECC_ERR_XPI_RD_2_MASK                             0x00040000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_2_BIT_OFFSET                               18
#define OCECCSTAT1_OCECC_ERR_XPI_RD_3_MASK                             0x00080000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_3_BIT_OFFSET                               19
#define OCECCSTAT1_OCECC_ERR_XPI_RD_4_MASK                             0x00100000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_4_BIT_OFFSET                               20
#define OCECCSTAT1_OCECC_ERR_XPI_RD_5_MASK                             0x00200000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_5_BIT_OFFSET                               21
#define OCECCSTAT1_OCECC_ERR_XPI_RD_6_MASK                             0x00400000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_6_BIT_OFFSET                               22
#define OCECCSTAT1_OCECC_ERR_XPI_RD_7_MASK                             0x00800000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_7_BIT_OFFSET                               23
#define OCECCSTAT1_OCECC_ERR_XPI_RD_8_MASK                             0x01000000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_8_BIT_OFFSET                               24
#define OCECCSTAT1_OCECC_ERR_XPI_RD_9_MASK                             0x02000000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_9_BIT_OFFSET                               25
#define OCECCSTAT1_OCECC_ERR_XPI_RD_10_MASK                            0x04000000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_10_BIT_OFFSET                              26
#define OCECCSTAT1_OCECC_ERR_XPI_RD_11_MASK                            0x08000000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_11_BIT_OFFSET                              27
#define OCECCSTAT1_OCECC_ERR_XPI_RD_12_MASK                            0x10000000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_12_BIT_OFFSET                              28
#define OCECCSTAT1_OCECC_ERR_XPI_RD_13_MASK                            0x20000000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_13_BIT_OFFSET                              29
#define OCECCSTAT1_OCECC_ERR_XPI_RD_14_MASK                            0x40000000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_14_BIT_OFFSET                              30
#define OCECCSTAT1_OCECC_ERR_XPI_RD_15_MASK                            0x80000000
#define OCECCSTAT1_OCECC_ERR_XPI_RD_15_BIT_OFFSET                              31

#define OCECCSTAT2                                                     0x00000710
#define OCECCSTAT2_OCECC_ERR_DDRC_MR_RD_BYTE_NUM_MASK                  0xFFFFFFFF
#define OCECCSTAT2_OCECC_ERR_DDRC_MR_RD_BYTE_NUM_BIT_OFFSET                     0

#define OCCAPCFG                                                       0x00000780
#define OCCAPCFG_OCCAP_EN_MASK                                         0x00000001
#define OCCAPCFG_OCCAP_EN_BIT_OFFSET                                            0
#define OCCAPCFG_OCCAP_ARB_INTR_EN_MASK                                0x00010000
#define OCCAPCFG_OCCAP_ARB_INTR_EN_BIT_OFFSET                                  16
#define OCCAPCFG_OCCAP_ARB_INTR_CLR_MASK                               0x00020000
#define OCCAPCFG_OCCAP_ARB_INTR_CLR_BIT_OFFSET                                 17
#define OCCAPCFG_OCCAP_ARB_INTR_FORCE_MASK                             0x00040000
#define OCCAPCFG_OCCAP_ARB_INTR_FORCE_BIT_OFFSET                               18
#define OCCAPCFG_OCCAP_ARB_CMP_POISON_SEQ_MASK                         0x01000000
#define OCCAPCFG_OCCAP_ARB_CMP_POISON_SEQ_BIT_OFFSET                           24
#define OCCAPCFG_OCCAP_ARB_CMP_POISON_PARALLEL_MASK                    0x02000000
#define OCCAPCFG_OCCAP_ARB_CMP_POISON_PARALLEL_BIT_OFFSET                      25
#define OCCAPCFG_OCCAP_ARB_CMP_POISON_ERR_INJ_MASK                     0x04000000
#define OCCAPCFG_OCCAP_ARB_CMP_POISON_ERR_INJ_BIT_OFFSET                       26
#define OCCAPCFG_OCCAP_ARB_RAQ_POISON_EN_MASK                          0x08000000
#define OCCAPCFG_OCCAP_ARB_RAQ_POISON_EN_BIT_OFFSET                            27

#define OCCAPSTAT                                                      0x00000784
#define OCCAPSTAT_OCCAP_ARB_ERR_INTR_MASK                              0x00010000
#define OCCAPSTAT_OCCAP_ARB_ERR_INTR_BIT_OFFSET                                16
#define OCCAPSTAT_OCCAP_ARB_CMP_POISON_COMPLETE_MASK                   0x00020000
#define OCCAPSTAT_OCCAP_ARB_CMP_POISON_COMPLETE_BIT_OFFSET                     17
#define OCCAPSTAT_OCCAP_ARB_CMP_POISON_SEQ_ERR_MASK                    0x01000000
#define OCCAPSTAT_OCCAP_ARB_CMP_POISON_SEQ_ERR_BIT_OFFSET                      24
#define OCCAPSTAT_OCCAP_ARB_CMP_POISON_PARALLEL_ERR_MASK               0x02000000
#define OCCAPSTAT_OCCAP_ARB_CMP_POISON_PARALLEL_ERR_BIT_OFFSET                 25

#define OCCAPCFG1                                                      0x00000788
#define OCCAPCFG1_OCCAP_DDRC_DATA_INTR_EN_MASK                         0x00000001
#define OCCAPCFG1_OCCAP_DDRC_DATA_INTR_EN_BIT_OFFSET                            0
#define OCCAPCFG1_OCCAP_DDRC_DATA_INTR_CLR_MASK                        0x00000002
#define OCCAPCFG1_OCCAP_DDRC_DATA_INTR_CLR_BIT_OFFSET                           1
#define OCCAPCFG1_OCCAP_DDRC_DATA_INTR_FORCE_MASK                      0x00000004
#define OCCAPCFG1_OCCAP_DDRC_DATA_INTR_FORCE_BIT_OFFSET                         2
#define OCCAPCFG1_OCCAP_DDRC_DATA_POISON_SEQ_MASK                      0x00000100
#define OCCAPCFG1_OCCAP_DDRC_DATA_POISON_SEQ_BIT_OFFSET                         8
#define OCCAPCFG1_OCCAP_DDRC_DATA_POISON_PARALLEL_MASK                 0x00000200
#define OCCAPCFG1_OCCAP_DDRC_DATA_POISON_PARALLEL_BIT_OFFSET                    9
#define OCCAPCFG1_OCCAP_DDRC_DATA_POISON_ERR_INJ_MASK                  0x00000400
#define OCCAPCFG1_OCCAP_DDRC_DATA_POISON_ERR_INJ_BIT_OFFSET                    10
#define OCCAPCFG1_OCCAP_DDRC_CTRL_INTR_EN_MASK                         0x00010000
#define OCCAPCFG1_OCCAP_DDRC_CTRL_INTR_EN_BIT_OFFSET                           16
#define OCCAPCFG1_OCCAP_DDRC_CTRL_INTR_CLR_MASK                        0x00020000
#define OCCAPCFG1_OCCAP_DDRC_CTRL_INTR_CLR_BIT_OFFSET                          17
#define OCCAPCFG1_OCCAP_DDRC_CTRL_INTR_FORCE_MASK                      0x00040000
#define OCCAPCFG1_OCCAP_DDRC_CTRL_INTR_FORCE_BIT_OFFSET                        18
#define OCCAPCFG1_OCCAP_DDRC_CTRL_POISON_SEQ_MASK                      0x01000000
#define OCCAPCFG1_OCCAP_DDRC_CTRL_POISON_SEQ_BIT_OFFSET                        24
#define OCCAPCFG1_OCCAP_DDRC_CTRL_POISON_PARALLEL_MASK                 0x02000000
#define OCCAPCFG1_OCCAP_DDRC_CTRL_POISON_PARALLEL_BIT_OFFSET                   25
#define OCCAPCFG1_OCCAP_DDRC_CTRL_POISON_ERR_INJ_MASK                  0x04000000
#define OCCAPCFG1_OCCAP_DDRC_CTRL_POISON_ERR_INJ_BIT_OFFSET                    26

#define OCCAPSTAT1                                                     0x0000078C
#define OCCAPSTAT1_OCCAP_DDRC_DATA_ERR_INTR_MASK                       0x00000001
#define OCCAPSTAT1_OCCAP_DDRC_DATA_ERR_INTR_BIT_OFFSET                          0
#define OCCAPSTAT1_OCCAP_DDRC_DATA_POISON_COMPLETE_MASK                0x00000002
#define OCCAPSTAT1_OCCAP_DDRC_DATA_POISON_COMPLETE_BIT_OFFSET                   1
#define OCCAPSTAT1_OCCAP_DDRC_DATA_POISON_SEQ_ERR_MASK                 0x00000100
#define OCCAPSTAT1_OCCAP_DDRC_DATA_POISON_SEQ_ERR_BIT_OFFSET                    8
#define OCCAPSTAT1_OCCAP_DDRC_DATA_POISON_PARALLEL_ERR_MASK            0x00000200
#define OCCAPSTAT1_OCCAP_DDRC_DATA_POISON_PARALLEL_ERR_BIT_OFFSET               9
#define OCCAPSTAT1_OCCAP_DDRC_CTRL_ERR_INTR_MASK                       0x00010000
#define OCCAPSTAT1_OCCAP_DDRC_CTRL_ERR_INTR_BIT_OFFSET                         16
#define OCCAPSTAT1_OCCAP_DDRC_CTRL_POISON_COMPLETE_MASK                0x00020000
#define OCCAPSTAT1_OCCAP_DDRC_CTRL_POISON_COMPLETE_BIT_OFFSET                  17
#define OCCAPSTAT1_OCCAP_DDRC_CTRL_POISON_SEQ_ERR_MASK                 0x01000000
#define OCCAPSTAT1_OCCAP_DDRC_CTRL_POISON_SEQ_ERR_BIT_OFFSET                   24
#define OCCAPSTAT1_OCCAP_DDRC_CTRL_POISON_PARALLEL_ERR_MASK            0x02000000
#define OCCAPSTAT1_OCCAP_DDRC_CTRL_POISON_PARALLEL_ERR_BIT_OFFSET              25

#define OCCAPCFG2                                                      0x00000790
#define OCCAPCFG2_OCCAP_DFIIC_INTR_EN_MASK                             0x00000001
#define OCCAPCFG2_OCCAP_DFIIC_INTR_EN_BIT_OFFSET                                0
#define OCCAPCFG2_OCCAP_DFIIC_INTR_CLR_MASK                            0x00000002
#define OCCAPCFG2_OCCAP_DFIIC_INTR_CLR_BIT_OFFSET                               1
#define OCCAPCFG2_OCCAP_DFIIC_INTR_FORCE_MASK                          0x00000004
#define OCCAPCFG2_OCCAP_DFIIC_INTR_FORCE_BIT_OFFSET                             2

#define OCCAPSTAT2                                                     0x00000794
#define OCCAPSTAT2_OCCAP_DFIIC_ERR_INTR_MASK                           0x00000001
#define OCCAPSTAT2_OCCAP_DFIIC_ERR_INTR_BIT_OFFSET                              0

#define CRCPARCTL0                                                     0x00000800
#define CRCPARCTL0_CAPAR_ERR_INTR_EN_MASK                              0x00000001
#define CRCPARCTL0_CAPAR_ERR_INTR_EN_BIT_OFFSET                                 0
#define CRCPARCTL0_CAPAR_ERR_INTR_CLR_MASK                             0x00000002
#define CRCPARCTL0_CAPAR_ERR_INTR_CLR_BIT_OFFSET                                1
#define CRCPARCTL0_CAPAR_ERR_INTR_FORCE_MASK                           0x00000004
#define CRCPARCTL0_CAPAR_ERR_INTR_FORCE_BIT_OFFSET                              2
#define CRCPARCTL0_CAPAR_ERR_MAX_REACHED_INTR_EN_MASK                  0x00000010
#define CRCPARCTL0_CAPAR_ERR_MAX_REACHED_INTR_EN_BIT_OFFSET                     4
#define CRCPARCTL0_CAPAR_ERR_MAX_REACHED_INTR_CLR_MASK                 0x00000020
#define CRCPARCTL0_CAPAR_ERR_MAX_REACHED_INTR_CLR_BIT_OFFSET                    5
#define CRCPARCTL0_CAPAR_ERR_MAX_REACHED_INTR_FORCE_MASK               0x00000040
#define CRCPARCTL0_CAPAR_ERR_MAX_REACHED_INTR_FORCE_BIT_OFFSET                  6
#define CRCPARCTL0_CAPAR_ERR_CNT_CLR_MASK                              0x00000080
#define CRCPARCTL0_CAPAR_ERR_CNT_CLR_BIT_OFFSET                                 7
#define CRCPARCTL0_WR_CRC_ERR_INTR_EN_MASK                             0x00000100
#define CRCPARCTL0_WR_CRC_ERR_INTR_EN_BIT_OFFSET                                8
#define CRCPARCTL0_WR_CRC_ERR_INTR_CLR_MASK                            0x00000200
#define CRCPARCTL0_WR_CRC_ERR_INTR_CLR_BIT_OFFSET                               9
#define CRCPARCTL0_WR_CRC_ERR_INTR_FORCE_MASK                          0x00000400
#define CRCPARCTL0_WR_CRC_ERR_INTR_FORCE_BIT_OFFSET                            10
#define CRCPARCTL0_WR_CRC_ERR_MAX_REACHED_INTR_EN_MASK                 0x00001000
#define CRCPARCTL0_WR_CRC_ERR_MAX_REACHED_INTR_EN_BIT_OFFSET                   12
#define CRCPARCTL0_WR_CRC_ERR_MAX_REACHED_INTR_CLR_MASK                0x00002000
#define CRCPARCTL0_WR_CRC_ERR_MAX_REACHED_INTR_CLR_BIT_OFFSET                  13
#define CRCPARCTL0_WR_CRC_ERR_MAX_REACHED_INTR_FORCE_MASK              0x00004000
#define CRCPARCTL0_WR_CRC_ERR_MAX_REACHED_INTR_FORCE_BIT_OFFSET                14
#define CRCPARCTL0_WR_CRC_ERR_CNT_CLR_MASK                             0x00008000
#define CRCPARCTL0_WR_CRC_ERR_CNT_CLR_BIT_OFFSET                               15
#define CRCPARCTL0_RD_CRC_ERR_MAX_REACHED_INT_EN_MASK                  0x00100000
#define CRCPARCTL0_RD_CRC_ERR_MAX_REACHED_INT_EN_BIT_OFFSET                    20
#define CRCPARCTL0_RD_CRC_ERR_MAX_REACHED_INT_CLR_MASK                 0x00200000
#define CRCPARCTL0_RD_CRC_ERR_MAX_REACHED_INT_CLR_BIT_OFFSET                   21
#define CRCPARCTL0_RD_CRC_ERR_CNT_CLR_MASK                             0x00400000
#define CRCPARCTL0_RD_CRC_ERR_CNT_CLR_BIT_OFFSET                               22
#define CRCPARCTL0_RD_CRC_ERR_MAX_REACHED_INTR_FORCE_MASK              0x00800000
#define CRCPARCTL0_RD_CRC_ERR_MAX_REACHED_INTR_FORCE_BIT_OFFSET                23
#define CRCPARCTL0_CAPAR_FATL_ERR_INTR_EN_MASK                         0x01000000
#define CRCPARCTL0_CAPAR_FATL_ERR_INTR_EN_BIT_OFFSET                           24
#define CRCPARCTL0_CAPAR_FATL_ERR_INTR_CLR_MASK                        0x02000000
#define CRCPARCTL0_CAPAR_FATL_ERR_INTR_CLR_BIT_OFFSET                          25
#define CRCPARCTL0_CAPAR_FATL_ERR_INTR_FORCE_MASK                      0x04000000
#define CRCPARCTL0_CAPAR_FATL_ERR_INTR_FORCE_BIT_OFFSET                        26

#define CRCPARCTL1                                                     0x00000804
#define CRCPARCTL1_PARITY_ENABLE_MASK                                  0x00000001
#define CRCPARCTL1_PARITY_ENABLE_BIT_OFFSET                                     0
#define CRCPARCTL1_BYPASS_INTERNAL_CRC_MASK                            0x00000002
#define CRCPARCTL1_BYPASS_INTERNAL_CRC_BIT_OFFSET                               1
#define CRCPARCTL1_RD_CRC_ENABLE_MASK                                  0x00000008
#define CRCPARCTL1_RD_CRC_ENABLE_BIT_OFFSET                                     3
#define CRCPARCTL1_WR_CRC_ENABLE_MASK                                  0x00000010
#define CRCPARCTL1_WR_CRC_ENABLE_BIT_OFFSET                                     4
#define CRCPARCTL1_DIS_RD_CRC_ECC_UPR_NIBBLE_MASK                      0x00000040
#define CRCPARCTL1_DIS_RD_CRC_ECC_UPR_NIBBLE_BIT_OFFSET                         6
#define CRCPARCTL1_CRC_INC_DM_MASK                                     0x00000080
#define CRCPARCTL1_CRC_INC_DM_BIT_OFFSET                                        7
#define CRCPARCTL1_CAPARITY_DISABLE_BEFORE_SR_MASK                     0x00001000
#define CRCPARCTL1_CAPARITY_DISABLE_BEFORE_SR_BIT_OFFSET                       12
#define CRCPARCTL1_DFI_ALERT_ASYNC_MODE_MASK                           0x00008000
#define CRCPARCTL1_DFI_ALERT_ASYNC_MODE_BIT_OFFSET                             15
#define CRCPARCTL1_CAPAR_ERR_MAX_REACHED_TH_MASK                       0x0FFF0000
#define CRCPARCTL1_CAPAR_ERR_MAX_REACHED_TH_BIT_OFFSET                         16

#define CRCPARCTL2                                                     0x00000808
#define CRCPARCTL2_WR_CRC_ERR_MAX_REACHED_TH_MASK                      0x00000FFF
#define CRCPARCTL2_WR_CRC_ERR_MAX_REACHED_TH_BIT_OFFSET                         0
#define CRCPARCTL2_RD_CRC_ERR_MAX_REACHED_TH_MASK                      0x0FFF0000
#define CRCPARCTL2_RD_CRC_ERR_MAX_REACHED_TH_BIT_OFFSET                        16

#define CRCPARSTAT                                                     0x0000080C
#define CRCPARSTAT_CAPAR_ERR_INTR_MASK                                 0x00010000
#define CRCPARSTAT_CAPAR_ERR_INTR_BIT_OFFSET                                   16
#define CRCPARSTAT_CAPAR_ERR_MAX_REACHED_INTR_MASK                     0x00020000
#define CRCPARSTAT_CAPAR_ERR_MAX_REACHED_INTR_BIT_OFFSET                       17
#define CRCPARSTAT_CAPAR_FATL_ERR_INTR_MASK                            0x00040000
#define CRCPARSTAT_CAPAR_FATL_ERR_INTR_BIT_OFFSET                              18
#define CRCPARSTAT_WR_CRC_ERR_INTR_MASK                                0x01000000
#define CRCPARSTAT_WR_CRC_ERR_INTR_BIT_OFFSET                                  24
#define CRCPARSTAT_WR_CRC_ERR_MAX_REACHED_INTR_MASK                    0x02000000
#define CRCPARSTAT_WR_CRC_ERR_MAX_REACHED_INTR_BIT_OFFSET                      25
#define CRCPARSTAT_WR_CRC_RETRY_LIMIT_INTR_MASK                        0x04000000
#define CRCPARSTAT_WR_CRC_RETRY_LIMIT_INTR_BIT_OFFSET                          26
#define CRCPARSTAT_RD_RETRY_LIMIT_INTR_MASK                            0x08000000
#define CRCPARSTAT_RD_RETRY_LIMIT_INTR_BIT_OFFSET                              27
#define CRCPARSTAT_CAPAR_RETRY_LIMIT_REACHED_INTR_MASK                 0x10000000
#define CRCPARSTAT_CAPAR_RETRY_LIMIT_REACHED_INTR_BIT_OFFSET                   28

#define CAPARPOISONCTL                                                 0x00000810
#define CAPARPOISONCTL_CAPAR_POISON_INJECT_EN_MASK                     0x00000001
#define CAPARPOISONCTL_CAPAR_POISON_INJECT_EN_BIT_OFFSET                        0
#define CAPARPOISONCTL_CAPAR_POISON_CMDTYPE_MASK                       0x00000300
#define CAPARPOISONCTL_CAPAR_POISON_CMDTYPE_BIT_OFFSET                          8
#define CAPARPOISONCTL_CAPAR_POISON_POSITION_MASK                      0x000FF000
#define CAPARPOISONCTL_CAPAR_POISON_POSITION_BIT_OFFSET                        12

#define CAPARPOISONSTAT                                                0x00000814
#define CAPARPOISONSTAT_CAPAR_POISON_COMPLETE_MASK                     0x00000001
#define CAPARPOISONSTAT_CAPAR_POISON_COMPLETE_BIT_OFFSET                        0

#define CRCPOISONCTL0                                                  0x00000820
#define CRCPOISONCTL0_CRC_POISON_INJECT_EN_MASK                        0x00000001
#define CRCPOISONCTL0_CRC_POISON_INJECT_EN_BIT_OFFSET                           0
#define CRCPOISONCTL0_CRC_POISON_TYPE_MASK                             0x00000002
#define CRCPOISONCTL0_CRC_POISON_TYPE_BIT_OFFSET                                1
#define CRCPOISONCTL0_CRC_POISON_NIBBLE_MASK                           0x00001F00
#define CRCPOISONCTL0_CRC_POISON_NIBBLE_BIT_OFFSET                              8
#define CRCPOISONCTL0_CRC_POISON_TIMES_MASK                            0x001F0000
#define CRCPOISONCTL0_CRC_POISON_TIMES_BIT_OFFSET                              16

#define CRCPOISONSTAT                                                  0x0000082C
#define CRCPOISONSTAT_CRC_POISON_COMPLETE_MASK                         0x00000001
#define CRCPOISONSTAT_CRC_POISON_COMPLETE_BIT_OFFSET                            0

#define RDCRCERRADDR0                                                  0x00000830
#define RDCRCERRADDR0_RD_CRC_ERR_ROW_MASK                              0x00FFFFFF
#define RDCRCERRADDR0_RD_CRC_ERR_ROW_BIT_OFFSET                                 0
#define RDCRCERRADDR0_RD_CRC_ERR_RANK_MASK                             0xFF000000
#define RDCRCERRADDR0_RD_CRC_ERR_RANK_BIT_OFFSET                               24

#define RDCRCERRADDR1                                                  0x00000834
#define RDCRCERRADDR1_RD_CRC_ERR_COL_MASK                              0x000007FF
#define RDCRCERRADDR1_RD_CRC_ERR_COL_BIT_OFFSET                                 0
#define RDCRCERRADDR1_RD_CRC_ERR_BANK_MASK                             0x00FF0000
#define RDCRCERRADDR1_RD_CRC_ERR_BANK_BIT_OFFSET                               16
#define RDCRCERRADDR1_RD_CRC_ERR_BG_MASK                               0x0F000000
#define RDCRCERRADDR1_RD_CRC_ERR_BG_BIT_OFFSET                                 24
#define RDCRCERRADDR1_RD_CRC_ERR_CID_MASK                              0xF0000000
#define RDCRCERRADDR1_RD_CRC_ERR_CID_BIT_OFFSET                                28

#define RDCRCERRSTAT0                                                  0x00000840
#define RDCRCERRSTAT0_RD_CRC_ERR_MAX_REACHED_INT_NIBBLE_MASK           0x000FFFFF
#define RDCRCERRSTAT0_RD_CRC_ERR_MAX_REACHED_INT_NIBBLE_BIT_OFFSET              0
#define RDCRCERRSTAT0_RD_CRC_ERR_MAX_REACHED_INT_MASK                  0x80000000
#define RDCRCERRSTAT0_RD_CRC_ERR_MAX_REACHED_INT_BIT_OFFSET                    31

#define CRCSTAT0                                                       0x00000848
#define CRCSTAT0_RD_CRC_ERR_CNT_NIBBLE_0_MASK                          0x00000FFF
#define CRCSTAT0_RD_CRC_ERR_CNT_NIBBLE_0_BIT_OFFSET                             0
#define CRCSTAT0_RD_CRC_ERR_CNT_NIBBLE_1_MASK                          0x0FFF0000
#define CRCSTAT0_RD_CRC_ERR_CNT_NIBBLE_1_BIT_OFFSET                            16

#define CRCSTAT1                                                       0x0000084C
#define CRCSTAT1_RD_CRC_ERR_CNT_NIBBLE_2_MASK                          0x00000FFF
#define CRCSTAT1_RD_CRC_ERR_CNT_NIBBLE_2_BIT_OFFSET                             0
#define CRCSTAT1_RD_CRC_ERR_CNT_NIBBLE_3_MASK                          0x0FFF0000
#define CRCSTAT1_RD_CRC_ERR_CNT_NIBBLE_3_BIT_OFFSET                            16

#define CRCSTAT2                                                       0x00000850
#define CRCSTAT2_RD_CRC_ERR_CNT_NIBBLE_4_MASK                          0x00000FFF
#define CRCSTAT2_RD_CRC_ERR_CNT_NIBBLE_4_BIT_OFFSET                             0
#define CRCSTAT2_RD_CRC_ERR_CNT_NIBBLE_5_MASK                          0x0FFF0000
#define CRCSTAT2_RD_CRC_ERR_CNT_NIBBLE_5_BIT_OFFSET                            16

#define CRCSTAT3                                                       0x00000854
#define CRCSTAT3_RD_CRC_ERR_CNT_NIBBLE_6_MASK                          0x00000FFF
#define CRCSTAT3_RD_CRC_ERR_CNT_NIBBLE_6_BIT_OFFSET                             0
#define CRCSTAT3_RD_CRC_ERR_CNT_NIBBLE_7_MASK                          0x0FFF0000
#define CRCSTAT3_RD_CRC_ERR_CNT_NIBBLE_7_BIT_OFFSET                            16

#define CRCSTAT4                                                       0x00000858
#define CRCSTAT4_RD_CRC_ERR_CNT_NIBBLE_8_MASK                          0x00000FFF
#define CRCSTAT4_RD_CRC_ERR_CNT_NIBBLE_8_BIT_OFFSET                             0
#define CRCSTAT4_RD_CRC_ERR_CNT_NIBBLE_9_MASK                          0x0FFF0000
#define CRCSTAT4_RD_CRC_ERR_CNT_NIBBLE_9_BIT_OFFSET                            16

#define CRCSTAT5                                                       0x0000085C
#define CRCSTAT5_RD_CRC_ERR_CNT_NIBBLE_10_MASK                         0x00000FFF
#define CRCSTAT5_RD_CRC_ERR_CNT_NIBBLE_10_BIT_OFFSET                            0
#define CRCSTAT5_RD_CRC_ERR_CNT_NIBBLE_11_MASK                         0x0FFF0000
#define CRCSTAT5_RD_CRC_ERR_CNT_NIBBLE_11_BIT_OFFSET                           16

#define CRCSTAT6                                                       0x00000860
#define CRCSTAT6_RD_CRC_ERR_CNT_NIBBLE_12_MASK                         0x00000FFF
#define CRCSTAT6_RD_CRC_ERR_CNT_NIBBLE_12_BIT_OFFSET                            0
#define CRCSTAT6_RD_CRC_ERR_CNT_NIBBLE_13_MASK                         0x0FFF0000
#define CRCSTAT6_RD_CRC_ERR_CNT_NIBBLE_13_BIT_OFFSET                           16

#define CRCSTAT7                                                       0x00000864
#define CRCSTAT7_RD_CRC_ERR_CNT_NIBBLE_14_MASK                         0x00000FFF
#define CRCSTAT7_RD_CRC_ERR_CNT_NIBBLE_14_BIT_OFFSET                            0
#define CRCSTAT7_RD_CRC_ERR_CNT_NIBBLE_15_MASK                         0x0FFF0000
#define CRCSTAT7_RD_CRC_ERR_CNT_NIBBLE_15_BIT_OFFSET                           16

#define CRCSTAT8                                                       0x00000868
#define CRCSTAT8_RD_CRC_ERR_CNT_NIBBLE_16_MASK                         0x00000FFF
#define CRCSTAT8_RD_CRC_ERR_CNT_NIBBLE_16_BIT_OFFSET                            0
#define CRCSTAT8_RD_CRC_ERR_CNT_NIBBLE_17_MASK                         0x0FFF0000
#define CRCSTAT8_RD_CRC_ERR_CNT_NIBBLE_17_BIT_OFFSET                           16

#define CRCSTAT9                                                       0x0000086C
#define CRCSTAT9_RD_CRC_ERR_CNT_NIBBLE_18_MASK                         0x00000FFF
#define CRCSTAT9_RD_CRC_ERR_CNT_NIBBLE_18_BIT_OFFSET                            0
#define CRCSTAT9_RD_CRC_ERR_CNT_NIBBLE_19_MASK                         0x0FFF0000
#define CRCSTAT9_RD_CRC_ERR_CNT_NIBBLE_19_BIT_OFFSET                           16

#define CRCSTAT10                                                      0x00000870
#define CRCSTAT10_WR_CRC_ERR_CNT_MASK                                  0x00000FFF
#define CRCSTAT10_WR_CRC_ERR_CNT_BIT_OFFSET                                     0
#define CRCSTAT10_CAPAR_ERR_CNT_MASK                                   0x00FFF000
#define CRCSTAT10_CAPAR_ERR_CNT_BIT_OFFSET                                     12

#define REGPARCFG                                                      0x00000880
#define REGPARCFG_REG_PAR_EN_MASK                                      0x00000001
#define REGPARCFG_REG_PAR_EN_BIT_OFFSET                                         0
#define REGPARCFG_REG_PAR_ERR_INTR_EN_MASK                             0x00000002
#define REGPARCFG_REG_PAR_ERR_INTR_EN_BIT_OFFSET                                1
#define REGPARCFG_REG_PAR_ERR_INTR_CLR_MASK                            0x00000004
#define REGPARCFG_REG_PAR_ERR_INTR_CLR_BIT_OFFSET                               2
#define REGPARCFG_REG_PAR_ERR_INTR_FORCE_MASK                          0x00000008
#define REGPARCFG_REG_PAR_ERR_INTR_FORCE_BIT_OFFSET                             3
#define REGPARCFG_REG_PAR_POISON_EN_MASK                               0x00000100
#define REGPARCFG_REG_PAR_POISON_EN_BIT_OFFSET                                  8

#define REGPARSTAT                                                     0x00000884
#define REGPARSTAT_REG_PAR_ERR_INTR_MASK                               0x00000001
#define REGPARSTAT_REG_PAR_ERR_INTR_BIT_OFFSET                                  0

#define RETRYCTL0                                                      0x00000890
#define RETRYCTL0_CAPAR_RETRY_ENABLE_MASK                              0x00000001
#define RETRYCTL0_CAPAR_RETRY_ENABLE_BIT_OFFSET                                 0
#define RETRYCTL0_RD_UE_RETRY_ENABLE_MASK                              0x00000002
#define RETRYCTL0_RD_UE_RETRY_ENABLE_BIT_OFFSET                                 1
#define RETRYCTL0_RD_CRC_RETRY_ENABLE_MASK                             0x00000004
#define RETRYCTL0_RD_CRC_RETRY_ENABLE_BIT_OFFSET                                2
#define RETRYCTL0_WR_CRC_RETRY_ENABLE_MASK                             0x00000008
#define RETRYCTL0_WR_CRC_RETRY_ENABLE_BIT_OFFSET                                3
#define RETRYCTL0_WR_CRC_RETRY_LIMITER_MASK                            0x00000700
#define RETRYCTL0_WR_CRC_RETRY_LIMITER_BIT_OFFSET                               8
#define RETRYCTL0_RD_CRC_RETRY_LIMITER_MASK                            0x00003800
#define RETRYCTL0_RD_CRC_RETRY_LIMITER_BIT_OFFSET                              11
#define RETRYCTL0_RD_UE_RETRY_LIMITER_MASK                             0x0001C000
#define RETRYCTL0_RD_UE_RETRY_LIMITER_BIT_OFFSET                               14
#define RETRYCTL0_CAPAR_RETRY_LIMITER_MASK                             0x000E0000
#define RETRYCTL0_CAPAR_RETRY_LIMITER_BIT_OFFSET                               17
#define RETRYCTL0_WR_CRC_RETRY_LIMIT_INTR_EN_MASK                      0x00100000
#define RETRYCTL0_WR_CRC_RETRY_LIMIT_INTR_EN_BIT_OFFSET                        20
#define RETRYCTL0_WR_CRC_RETRY_LIMIT_INTR_CLR_MASK                     0x00200000
#define RETRYCTL0_WR_CRC_RETRY_LIMIT_INTR_CLR_BIT_OFFSET                       21
#define RETRYCTL0_WR_CRC_RETRY_LIMIT_INTR_FORCE_MASK                   0x00400000
#define RETRYCTL0_WR_CRC_RETRY_LIMIT_INTR_FORCE_BIT_OFFSET                     22
#define RETRYCTL0_RD_RETRY_LIMIT_INTR_EN_MASK                          0x00800000
#define RETRYCTL0_RD_RETRY_LIMIT_INTR_EN_BIT_OFFSET                            23
#define RETRYCTL0_RD_RETRY_LIMIT_INTR_CLR_MASK                         0x01000000
#define RETRYCTL0_RD_RETRY_LIMIT_INTR_CLR_BIT_OFFSET                           24
#define RETRYCTL0_RD_RETRY_LIMIT_INTR_FORCE_MASK                       0x02000000
#define RETRYCTL0_RD_RETRY_LIMIT_INTR_FORCE_BIT_OFFSET                         25
#define RETRYCTL0_CAPAR_RETRY_LIMIT_INTR_EN_MASK                       0x04000000
#define RETRYCTL0_CAPAR_RETRY_LIMIT_INTR_EN_BIT_OFFSET                         26
#define RETRYCTL0_CAPAR_RETRY_LIMIT_INTR_CLR_MASK                      0x08000000
#define RETRYCTL0_CAPAR_RETRY_LIMIT_INTR_CLR_BIT_OFFSET                        27
#define RETRYCTL0_CAPAR_RETRY_LIMIT_INTR_FORCE_MASK                    0x10000000
#define RETRYCTL0_CAPAR_RETRY_LIMIT_INTR_FORCE_BIT_OFFSET                      28

#define RETRYCTL1                                                      0x00000894
#define RETRYCTL1_MAKE_MULTI_RETRY_FATL_ERR_MASK                       0x20000000
#define RETRYCTL1_MAKE_MULTI_RETRY_FATL_ERR_BIT_OFFSET                         29
#define RETRYCTL1_DIS_CAPAR_SELFREF_RETRY_MASK                         0x40000000
#define RETRYCTL1_DIS_CAPAR_SELFREF_RETRY_BIT_OFFSET                           30
#define RETRYCTL1_DIS_CAPAR_POWERDOWN_RETRY_MASK                       0x80000000
#define RETRYCTL1_DIS_CAPAR_POWERDOWN_RETRY_BIT_OFFSET                         31

#define RETRYSTAT0                                                     0x000008A0
#define RETRYSTAT0_RETRY_STAT_MASK                                     0x00000003
#define RETRYSTAT0_RETRY_STAT_BIT_OFFSET                                        0
#define RETRYSTAT0_RETRY_FIFO_FILL_LEVEL_MASK                          0x00007F80
#define RETRYSTAT0_RETRY_FIFO_FILL_LEVEL_BIT_OFFSET                             7
#define RETRYSTAT0_RD_UE_RETRY_LIMIT_REACHED_MASK                      0x00010000
#define RETRYSTAT0_RD_UE_RETRY_LIMIT_REACHED_BIT_OFFSET                        16
#define RETRYSTAT0_RD_CRC_RETRY_LIMIT_REACHED_MASK                     0x00020000
#define RETRYSTAT0_RD_CRC_RETRY_LIMIT_REACHED_BIT_OFFSET                       17
#define RETRYSTAT0_CAPAR_FATL_ERR_CODE_MASK                            0x3F000000
#define RETRYSTAT0_CAPAR_FATL_ERR_CODE_BIT_OFFSET                              24

#define LNKECCCTL1                                                     0x00000984
#define LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN_MASK                       0x00000001
#define LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN_BIT_OFFSET                          0
#define LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR_MASK                      0x00000002
#define LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR_BIT_OFFSET                         1
#define LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR_MASK                       0x00000004
#define LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR_BIT_OFFSET                          2
#define LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE_MASK                    0x00000008
#define LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE_BIT_OFFSET                       3
#define LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN_MASK                     0x00000010
#define LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN_BIT_OFFSET                        4
#define LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR_MASK                    0x00000020
#define LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR_BIT_OFFSET                       5
#define LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR_MASK                     0x00000040
#define LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR_BIT_OFFSET                        6
#define LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE_MASK                  0x00000080
#define LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE_BIT_OFFSET                     7

#define LNKECCPOISONCTL0                                               0x00000988
#define LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN_MASK                 0x00000001
#define LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN_BIT_OFFSET                    0
#define LNKECCPOISONCTL0_LINKECC_POISON_TYPE_MASK                      0x00000002
#define LNKECCPOISONCTL0_LINKECC_POISON_TYPE_BIT_OFFSET                         1
#define LNKECCPOISONCTL0_LINKECC_POISON_RW_MASK                        0x00000004
#define LNKECCPOISONCTL0_LINKECC_POISON_RW_BIT_OFFSET                           2
#define LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL_MASK                   0x00FF0000
#define LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL_BIT_OFFSET                     16
#define LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL_MASK                  0xFF000000
#define LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL_BIT_OFFSET                    24

#define LNKECCPOISONSTAT                                               0x0000098C
#define LNKECCPOISONSTAT_LINKECC_POISON_COMPLETE_MASK                  0x00000001
#define LNKECCPOISONSTAT_LINKECC_POISON_COMPLETE_BIT_OFFSET                     0

#define LNKECCINDEX                                                    0x00000990
#define LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL_MASK                      0x00000007
#define LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL_BIT_OFFSET                         0
#define LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL_MASK                      0x00000030
#define LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL_BIT_OFFSET                         4

#define LNKECCERRCNT0                                                  0x00000994
#define LNKECCERRCNT0_RD_LINK_ECC_ERR_SYNDROME_MASK                    0x000001FF
#define LNKECCERRCNT0_RD_LINK_ECC_ERR_SYNDROME_BIT_OFFSET                       0
#define LNKECCERRCNT0_RD_LINK_ECC_CORR_CNT_MASK                        0x00FF0000
#define LNKECCERRCNT0_RD_LINK_ECC_CORR_CNT_BIT_OFFSET                          16
#define LNKECCERRCNT0_RD_LINK_ECC_UNCORR_CNT_MASK                      0xFF000000
#define LNKECCERRCNT0_RD_LINK_ECC_UNCORR_CNT_BIT_OFFSET                        24

#define LNKECCERRSTAT                                                  0x00000998
#define LNKECCERRSTAT_RD_LINK_ECC_CORR_ERR_INT_MASK                    0x0000000F
#define LNKECCERRSTAT_RD_LINK_ECC_CORR_ERR_INT_BIT_OFFSET                       0
#define LNKECCERRSTAT_RD_LINK_ECC_UNCORR_ERR_INT_MASK                  0x00000F00
#define LNKECCERRSTAT_RD_LINK_ECC_UNCORR_ERR_INT_BIT_OFFSET                     8

#define EAPARCTL0                                                      0x000009A0
#define EAPARCTL0_EAPAR_ERR_INTR_EN_MASK                               0x00000001
#define EAPARCTL0_EAPAR_ERR_INTR_EN_BIT_OFFSET                                  0
#define EAPARCTL0_EAPAR_ERR_INTR_CLR_MASK                              0x00000002
#define EAPARCTL0_EAPAR_ERR_INTR_CLR_BIT_OFFSET                                 1
#define EAPARCTL0_EAPAR_ERR_INTR_FORCE_MASK                            0x00000004
#define EAPARCTL0_EAPAR_ERR_INTR_FORCE_BIT_OFFSET                               2
#define EAPARCTL0_EAPAR_ERR_CNT_CLR_MASK                               0x00000008
#define EAPARCTL0_EAPAR_ERR_CNT_CLR_BIT_OFFSET                                  3

#define EAPARSTAT0                                                     0x000009A4
#define EAPARSTAT0_EAPAR_ERROR_MASK                                    0x0000FFFF
#define EAPARSTAT0_EAPAR_ERROR_BIT_OFFSET                                       0
#define EAPARSTAT0_EAPAR_ERR_SBR_RD_MASK                               0x00010000
#define EAPARSTAT0_EAPAR_ERR_SBR_RD_BIT_OFFSET                                 16

#define EAPARERRCNT                                                    0x000009A8
#define EAPARERRCNT_EAPAR_ERR_CNT_MASK                                 0x0000FFFF
#define EAPARERRCNT_EAPAR_ERR_CNT_BIT_OFFSET                                    0

#define EAPARADDR0                                                     0x000009B0
#define EAPARADDR0_EAPAR_ERR_ROW_MASK                                  0x00FFFFFF
#define EAPARADDR0_EAPAR_ERR_ROW_BIT_OFFSET                                     0
#define EAPARADDR0_EAPAR_ERR_RANK_MASK                                 0xFF000000
#define EAPARADDR0_EAPAR_ERR_RANK_BIT_OFFSET                                   24

#define EAPARADDR1                                                     0x000009B4
#define EAPARADDR1_EAPAR_ERR_COL_MASK                                  0x000007FF
#define EAPARADDR1_EAPAR_ERR_COL_BIT_OFFSET                                     0
#define EAPARADDR1_EAPAR_ERR_BANK_MASK                                 0x00FF0000
#define EAPARADDR1_EAPAR_ERR_BANK_BIT_OFFSET                                   16
#define EAPARADDR1_EAPAR_ERR_BG_MASK                                   0x0F000000
#define EAPARADDR1_EAPAR_ERR_BG_BIT_OFFSET                                     24
#define EAPARADDR1_EAPAR_ERR_CID_MASK                                  0xF0000000
#define EAPARADDR1_EAPAR_ERR_CID_BIT_OFFSET                                    28

#define EAPARSYN0                                                      0x000009B8
#define EAPARSYN0_EAPAR_ERR_SYNDROMES_31_0_MASK                        0xFFFFFFFF
#define EAPARSYN0_EAPAR_ERR_SYNDROMES_31_0_BIT_OFFSET                           0

#define EAPARSYN1                                                      0x000009BC
#define EAPARSYN1_EAPAR_ERR_SYNDROMES_63_32_MASK                       0xFFFFFFFF
#define EAPARSYN1_EAPAR_ERR_SYNDROMES_63_32_BIT_OFFSET                          0

#define EAPARSYN2                                                      0x000009C0
#define EAPARSYN2_EAPAR_ERR_SYNDROMES_71_64_MASK                       0x000000FF
#define EAPARSYN2_EAPAR_ERR_SYNDROMES_71_64_BIT_OFFSET                          0
#define EAPARSYN2_EAPAR_ERR_CB_SYNDROME_MASK                           0x00FF0000
#define EAPARSYN2_EAPAR_ERR_CB_SYNDROME_BIT_OFFSET                             16

#define LNKECCCADDR0                                                   0x000009E0
#define LNKECCCADDR0_LINK_ECC_CORR_ROW_MASK                            0x00FFFFFF
#define LNKECCCADDR0_LINK_ECC_CORR_ROW_BIT_OFFSET                               0
#define LNKECCCADDR0_LINK_ECC_CORR_RANK_MASK                           0xFF000000
#define LNKECCCADDR0_LINK_ECC_CORR_RANK_BIT_OFFSET                             24

#define LNKECCCADDR1                                                   0x000009E4
#define LNKECCCADDR1_LINK_ECC_CORR_COL_MASK                            0x000007FF
#define LNKECCCADDR1_LINK_ECC_CORR_COL_BIT_OFFSET                               0
#define LNKECCCADDR1_LINK_ECC_CORR_BANK_MASK                           0x00FF0000
#define LNKECCCADDR1_LINK_ECC_CORR_BANK_BIT_OFFSET                             16
#define LNKECCCADDR1_LINK_ECC_CORR_BG_MASK                             0xFF000000
#define LNKECCCADDR1_LINK_ECC_CORR_BG_BIT_OFFSET                               24

#define LNKECCUADDR0                                                   0x000009E8
#define LNKECCUADDR0_LINK_ECC_UNCORR_ROW_MASK                          0x00FFFFFF
#define LNKECCUADDR0_LINK_ECC_UNCORR_ROW_BIT_OFFSET                             0
#define LNKECCUADDR0_LINK_ECC_UNCORR_RANK_MASK                         0xFF000000
#define LNKECCUADDR0_LINK_ECC_UNCORR_RANK_BIT_OFFSET                           24

#define LNKECCUADDR1                                                   0x000009EC
#define LNKECCUADDR1_LINK_ECC_UNCORR_COL_MASK                          0x000007FF
#define LNKECCUADDR1_LINK_ECC_UNCORR_COL_BIT_OFFSET                             0
#define LNKECCUADDR1_LINK_ECC_UNCORR_BANK_MASK                         0x00FF0000
#define LNKECCUADDR1_LINK_ECC_UNCORR_BANK_BIT_OFFSET                           16
#define LNKECCUADDR1_LINK_ECC_UNCORR_BG_MASK                           0xFF000000
#define LNKECCUADDR1_LINK_ECC_UNCORR_BG_BIT_OFFSET                             24

#define PASCTL0                                                        0x00000A00
#define PASCTL0_INIT_DONE_MASK                                         0x00000001
#define PASCTL0_INIT_DONE_BIT_OFFSET                                            0
#define PASCTL0_DBG_ST_EN_MASK                                         0x00000002
#define PASCTL0_DBG_ST_EN_BIT_OFFSET                                            1
#define PASCTL0_BIST_ST_EN_MASK                                        0x00000004
#define PASCTL0_BIST_ST_EN_BIT_OFFSET                                           2

#define PASCTL1                                                        0x00000A04
#define PASCTL1_PRE_SB_ENABLE_MASK                                     0x00000001
#define PASCTL1_PRE_SB_ENABLE_BIT_OFFSET                                        0
#define PASCTL1_PRE_AB_ENABLE_MASK                                     0x00000002
#define PASCTL1_PRE_AB_ENABLE_BIT_OFFSET                                        1
#define PASCTL1_PRE_SLOT_CONFIG_MASK                                   0x0000000C
#define PASCTL1_PRE_SLOT_CONFIG_BIT_OFFSET                                      2
#define PASCTL1_WR_MIN_GAP_MASK                                        0x000000F0
#define PASCTL1_WR_MIN_GAP_BIT_OFFSET                                           4
#define PASCTL1_RD_MIN_GAP_MASK                                        0x00000F00
#define PASCTL1_RD_MIN_GAP_BIT_OFFSET                                           8
#define PASCTL1_RANK_SWITCH_GAP_UNIT_SEL_MASK                          0x00001000
#define PASCTL1_RANK_SWITCH_GAP_UNIT_SEL_BIT_OFFSET                            12
#define PASCTL1_MRR_DES_TIMING_UNIT_SEL_MASK                           0x00006000
#define PASCTL1_MRR_DES_TIMING_UNIT_SEL_BIT_OFFSET                             13
#define PASCTL1_SELFREF_WO_REF_PENDING_MASK                            0x00040000
#define PASCTL1_SELFREF_WO_REF_PENDING_BIT_OFFSET                              18
#define PASCTL1_DFI_ALERT_ASSERTION_MODE_MASK                          0x00080000
#define PASCTL1_DFI_ALERT_ASSERTION_MODE_BIT_OFFSET                            19
#define PASCTL1_SPECULATIVE_REF_PRI_SEL_MASK                           0x00100000
#define PASCTL1_SPECULATIVE_REF_PRI_SEL_BIT_OFFSET                             20
#define PASCTL1_DYN_PRE_PRI_DIS_MASK                                   0x00200000
#define PASCTL1_DYN_PRE_PRI_DIS_BIT_OFFSET                                     21
#define PASCTL1_FIXED_PRE_PRI_SEL_MASK                                 0x00400000
#define PASCTL1_FIXED_PRE_PRI_SEL_BIT_OFFSET                                   22
#define PASCTL1_BLK_ACT_EN_MASK                                        0x00800000
#define PASCTL1_BLK_ACT_EN_BIT_OFFSET                                          23
#define PASCTL1_ACT2RDA_CNT_MASK_MASK                                  0x01000000
#define PASCTL1_ACT2RDA_CNT_MASK_BIT_OFFSET                                    24

#define PASCTL2                                                        0x00000A08
#define PASCTL2_DYN_PRE_PRI_HI_WIN_SIZE_MASK                           0x000000FF
#define PASCTL2_DYN_PRE_PRI_HI_WIN_SIZE_BIT_OFFSET                              0
#define PASCTL2_DYN_PRE_PRI_LO_WAIT_THR_MASK                           0x0000FF00
#define PASCTL2_DYN_PRE_PRI_LO_WAIT_THR_BIT_OFFSET                              8
#define PASCTL2_LRANK_RD2RD_GAP_MASK                                   0x00070000
#define PASCTL2_LRANK_RD2RD_GAP_BIT_OFFSET                                     16
#define PASCTL2_LRANK_WR2WR_GAP_MASK                                   0x00380000
#define PASCTL2_LRANK_WR2WR_GAP_BIT_OFFSET                                     19
#define PASCTL2_REFSB_HI_WAIT_THR_MASK                                 0x3F000000
#define PASCTL2_REFSB_HI_WAIT_THR_BIT_OFFSET                                   24
#define PASCTL2_T_PPD_CNT_EN_MASK                                      0x40000000
#define PASCTL2_T_PPD_CNT_EN_BIT_OFFSET                                        30

#define PASCTL3                                                        0x00000A0C
#define PASCTL3_DIMM_T_DCAW_MASK                                       0x000000FF
#define PASCTL3_DIMM_T_DCAW_BIT_OFFSET                                          0
#define PASCTL3_DIMM_N_DCAC_M1_MASK                                    0x00001F00
#define PASCTL3_DIMM_N_DCAC_M1_BIT_OFFSET                                       8
#define PASCTL3_DIMM_DCAW_EN_MASK                                      0x0000C000
#define PASCTL3_DIMM_DCAW_EN_BIT_OFFSET                                        14
#define PASCTL3_ENABLE_TRFC_DPR_MASK                                   0x00070000
#define PASCTL3_ENABLE_TRFC_DPR_BIT_OFFSET                                     16

#define PASCTL4                                                        0x00000A10
#define PASCTL4_CI_MRR_DES1_MASK                                       0x0000000F
#define PASCTL4_CI_MRR_DES1_BIT_OFFSET                                          0
#define PASCTL4_CI_MRR_DES2_MASK                                       0x000000F0
#define PASCTL4_CI_MRR_DES2_BIT_OFFSET                                          4
#define PASCTL4_CI_MRW_DES1_MASK                                       0x00000F00
#define PASCTL4_CI_MRW_DES1_BIT_OFFSET                                          8
#define PASCTL4_CI_MRW_DES2_MASK                                       0x0000F000
#define PASCTL4_CI_MRW_DES2_BIT_OFFSET                                         12
#define PASCTL4_CI_MPC_DES1_MASK                                       0x000F0000
#define PASCTL4_CI_MPC_DES1_BIT_OFFSET                                         16
#define PASCTL4_CI_MPC_DES2_MASK                                       0x00F00000
#define PASCTL4_CI_MPC_DES2_BIT_OFFSET                                         20
#define PASCTL4_CI_RFM_DES1_MASK                                       0x0F000000
#define PASCTL4_CI_RFM_DES1_BIT_OFFSET                                         24
#define PASCTL4_CI_RFM_DES2_MASK                                       0xF0000000
#define PASCTL4_CI_RFM_DES2_BIT_OFFSET                                         28

#define PASCTL5                                                        0x00000A14
#define PASCTL5_BASE_TIMER_EN_MASK                                     0x00000001
#define PASCTL5_BASE_TIMER_EN_BIT_OFFSET                                        0

#define PASCTL6                                                        0x00000A18
#define PASCTL6_BASE_TIMER_MASK                                        0xFFFFFFFF
#define PASCTL6_BASE_TIMER_BIT_OFFSET                                           0

#define PASCTL7                                                        0x00000A1C
#define PASCTL7_GLB_BLK0_EN_MASK                                       0x00000001
#define PASCTL7_GLB_BLK0_EN_BIT_OFFSET                                          0
#define PASCTL7_GLB_BLK1_EN_MASK                                       0x00000002
#define PASCTL7_GLB_BLK1_EN_BIT_OFFSET                                          1
#define PASCTL7_GLB_BLK2_EN_MASK                                       0x00000004
#define PASCTL7_GLB_BLK2_EN_BIT_OFFSET                                          2
#define PASCTL7_GLB_BLK3_EN_MASK                                       0x00000008
#define PASCTL7_GLB_BLK3_EN_BIT_OFFSET                                          3
#define PASCTL7_GLB_BLK4_EN_MASK                                       0x00000010
#define PASCTL7_GLB_BLK4_EN_BIT_OFFSET                                          4
#define PASCTL7_GLB_BLK5_EN_MASK                                       0x00000020
#define PASCTL7_GLB_BLK5_EN_BIT_OFFSET                                          5
#define PASCTL7_GLB_BLK6_EN_MASK                                       0x00000040
#define PASCTL7_GLB_BLK6_EN_BIT_OFFSET                                          6
#define PASCTL7_GLB_BLK7_EN_MASK                                       0x00000080
#define PASCTL7_GLB_BLK7_EN_BIT_OFFSET                                          7

#define PASCTL8                                                        0x00000A20
#define PASCTL8_RANK_BLK0_EN_MASK                                      0x00000001
#define PASCTL8_RANK_BLK0_EN_BIT_OFFSET                                         0
#define PASCTL8_RANK_BLK1_EN_MASK                                      0x00000002
#define PASCTL8_RANK_BLK1_EN_BIT_OFFSET                                         1
#define PASCTL8_RANK_BLK2_EN_MASK                                      0x00000004
#define PASCTL8_RANK_BLK2_EN_BIT_OFFSET                                         2
#define PASCTL8_RANK_BLK3_EN_MASK                                      0x00000008
#define PASCTL8_RANK_BLK3_EN_BIT_OFFSET                                         3
#define PASCTL8_RANK_BLK4_EN_MASK                                      0x00000010
#define PASCTL8_RANK_BLK4_EN_BIT_OFFSET                                         4
#define PASCTL8_RANK_BLK5_EN_MASK                                      0x00000020
#define PASCTL8_RANK_BLK5_EN_BIT_OFFSET                                         5
#define PASCTL8_RANK_BLK6_EN_MASK                                      0x00000040
#define PASCTL8_RANK_BLK6_EN_BIT_OFFSET                                         6
#define PASCTL8_RANK_BLK7_EN_MASK                                      0x00000080
#define PASCTL8_RANK_BLK7_EN_BIT_OFFSET                                         7
#define PASCTL8_RANK_BLK8_EN_MASK                                      0x00000100
#define PASCTL8_RANK_BLK8_EN_BIT_OFFSET                                         8
#define PASCTL8_RANK_BLK9_EN_MASK                                      0x00000200
#define PASCTL8_RANK_BLK9_EN_BIT_OFFSET                                         9
#define PASCTL8_RANK_BLK10_EN_MASK                                     0x00000400
#define PASCTL8_RANK_BLK10_EN_BIT_OFFSET                                       10
#define PASCTL8_RANK_BLK11_EN_MASK                                     0x00000800
#define PASCTL8_RANK_BLK11_EN_BIT_OFFSET                                       11
#define PASCTL8_RANK_BLK12_EN_MASK                                     0x00001000
#define PASCTL8_RANK_BLK12_EN_BIT_OFFSET                                       12
#define PASCTL8_RANK_BLK13_EN_MASK                                     0x00002000
#define PASCTL8_RANK_BLK13_EN_BIT_OFFSET                                       13
#define PASCTL8_RANK_BLK14_EN_MASK                                     0x00004000
#define PASCTL8_RANK_BLK14_EN_BIT_OFFSET                                       14
#define PASCTL8_RANK_BLK15_EN_MASK                                     0x00008000
#define PASCTL8_RANK_BLK15_EN_BIT_OFFSET                                       15
#define PASCTL8_RANK_BLK16_EN_MASK                                     0x00010000
#define PASCTL8_RANK_BLK16_EN_BIT_OFFSET                                       16
#define PASCTL8_RANK_BLK17_EN_MASK                                     0x00020000
#define PASCTL8_RANK_BLK17_EN_BIT_OFFSET                                       17
#define PASCTL8_RANK_BLK18_EN_MASK                                     0x00040000
#define PASCTL8_RANK_BLK18_EN_BIT_OFFSET                                       18
#define PASCTL8_RANK_BLK19_EN_MASK                                     0x00080000
#define PASCTL8_RANK_BLK19_EN_BIT_OFFSET                                       19
#define PASCTL8_RANK_BLK20_EN_MASK                                     0x00100000
#define PASCTL8_RANK_BLK20_EN_BIT_OFFSET                                       20
#define PASCTL8_RANK_BLK21_EN_MASK                                     0x00200000
#define PASCTL8_RANK_BLK21_EN_BIT_OFFSET                                       21
#define PASCTL8_RANK_BLK22_EN_MASK                                     0x00400000
#define PASCTL8_RANK_BLK22_EN_BIT_OFFSET                                       22
#define PASCTL8_RANK_BLK23_EN_MASK                                     0x00800000
#define PASCTL8_RANK_BLK23_EN_BIT_OFFSET                                       23
#define PASCTL8_RANK_BLK24_EN_MASK                                     0x01000000
#define PASCTL8_RANK_BLK24_EN_BIT_OFFSET                                       24
#define PASCTL8_RANK_BLK25_EN_MASK                                     0x02000000
#define PASCTL8_RANK_BLK25_EN_BIT_OFFSET                                       25
#define PASCTL8_RANK_BLK26_EN_MASK                                     0x04000000
#define PASCTL8_RANK_BLK26_EN_BIT_OFFSET                                       26
#define PASCTL8_RANK_BLK27_EN_MASK                                     0x08000000
#define PASCTL8_RANK_BLK27_EN_BIT_OFFSET                                       27
#define PASCTL8_RANK_BLK28_EN_MASK                                     0x10000000
#define PASCTL8_RANK_BLK28_EN_BIT_OFFSET                                       28
#define PASCTL8_RANK_BLK29_EN_MASK                                     0x20000000
#define PASCTL8_RANK_BLK29_EN_BIT_OFFSET                                       29
#define PASCTL8_RANK_BLK30_EN_MASK                                     0x40000000
#define PASCTL8_RANK_BLK30_EN_BIT_OFFSET                                       30
#define PASCTL8_RANK_BLK31_EN_MASK                                     0x80000000
#define PASCTL8_RANK_BLK31_EN_BIT_OFFSET                                       31

#define PASCTL9                                                        0x00000A24
#define PASCTL9_GLB_BLK0_TRIG_MASK                                     0x00000001
#define PASCTL9_GLB_BLK0_TRIG_BIT_OFFSET                                        0
#define PASCTL9_GLB_BLK1_TRIG_MASK                                     0x00000002
#define PASCTL9_GLB_BLK1_TRIG_BIT_OFFSET                                        1
#define PASCTL9_GLB_BLK2_TRIG_MASK                                     0x00000004
#define PASCTL9_GLB_BLK2_TRIG_BIT_OFFSET                                        2
#define PASCTL9_GLB_BLK3_TRIG_MASK                                     0x00000008
#define PASCTL9_GLB_BLK3_TRIG_BIT_OFFSET                                        3
#define PASCTL9_GLB_BLK4_TRIG_MASK                                     0x00000010
#define PASCTL9_GLB_BLK4_TRIG_BIT_OFFSET                                        4
#define PASCTL9_GLB_BLK5_TRIG_MASK                                     0x00000020
#define PASCTL9_GLB_BLK5_TRIG_BIT_OFFSET                                        5
#define PASCTL9_GLB_BLK6_TRIG_MASK                                     0x00000040
#define PASCTL9_GLB_BLK6_TRIG_BIT_OFFSET                                        6
#define PASCTL9_GLB_BLK7_TRIG_MASK                                     0x00000080
#define PASCTL9_GLB_BLK7_TRIG_BIT_OFFSET                                        7

#define PASCTL10                                                       0x00000A28
#define PASCTL10_RANK_BLK0_TRIG_MASK                                   0x00000001
#define PASCTL10_RANK_BLK0_TRIG_BIT_OFFSET                                      0
#define PASCTL10_RANK_BLK1_TRIG_MASK                                   0x00000002
#define PASCTL10_RANK_BLK1_TRIG_BIT_OFFSET                                      1
#define PASCTL10_RANK_BLK2_TRIG_MASK                                   0x00000004
#define PASCTL10_RANK_BLK2_TRIG_BIT_OFFSET                                      2
#define PASCTL10_RANK_BLK3_TRIG_MASK                                   0x00000008
#define PASCTL10_RANK_BLK3_TRIG_BIT_OFFSET                                      3
#define PASCTL10_RANK_BLK4_TRIG_MASK                                   0x00000010
#define PASCTL10_RANK_BLK4_TRIG_BIT_OFFSET                                      4
#define PASCTL10_RANK_BLK5_TRIG_MASK                                   0x00000020
#define PASCTL10_RANK_BLK5_TRIG_BIT_OFFSET                                      5
#define PASCTL10_RANK_BLK6_TRIG_MASK                                   0x00000040
#define PASCTL10_RANK_BLK6_TRIG_BIT_OFFSET                                      6
#define PASCTL10_RANK_BLK7_TRIG_MASK                                   0x00000080
#define PASCTL10_RANK_BLK7_TRIG_BIT_OFFSET                                      7
#define PASCTL10_RANK_BLK8_TRIG_MASK                                   0x00000100
#define PASCTL10_RANK_BLK8_TRIG_BIT_OFFSET                                      8
#define PASCTL10_RANK_BLK9_TRIG_MASK                                   0x00000200
#define PASCTL10_RANK_BLK9_TRIG_BIT_OFFSET                                      9
#define PASCTL10_RANK_BLK10_TRIG_MASK                                  0x00000400
#define PASCTL10_RANK_BLK10_TRIG_BIT_OFFSET                                    10
#define PASCTL10_RANK_BLK11_TRIG_MASK                                  0x00000800
#define PASCTL10_RANK_BLK11_TRIG_BIT_OFFSET                                    11
#define PASCTL10_RANK_BLK12_TRIG_MASK                                  0x00001000
#define PASCTL10_RANK_BLK12_TRIG_BIT_OFFSET                                    12
#define PASCTL10_RANK_BLK13_TRIG_MASK                                  0x00002000
#define PASCTL10_RANK_BLK13_TRIG_BIT_OFFSET                                    13
#define PASCTL10_RANK_BLK14_TRIG_MASK                                  0x00004000
#define PASCTL10_RANK_BLK14_TRIG_BIT_OFFSET                                    14
#define PASCTL10_RANK_BLK15_TRIG_MASK                                  0x00008000
#define PASCTL10_RANK_BLK15_TRIG_BIT_OFFSET                                    15
#define PASCTL10_RANK_BLK16_TRIG_MASK                                  0x00010000
#define PASCTL10_RANK_BLK16_TRIG_BIT_OFFSET                                    16
#define PASCTL10_RANK_BLK17_TRIG_MASK                                  0x00020000
#define PASCTL10_RANK_BLK17_TRIG_BIT_OFFSET                                    17
#define PASCTL10_RANK_BLK18_TRIG_MASK                                  0x00040000
#define PASCTL10_RANK_BLK18_TRIG_BIT_OFFSET                                    18
#define PASCTL10_RANK_BLK19_TRIG_MASK                                  0x00080000
#define PASCTL10_RANK_BLK19_TRIG_BIT_OFFSET                                    19
#define PASCTL10_RANK_BLK20_TRIG_MASK                                  0x00100000
#define PASCTL10_RANK_BLK20_TRIG_BIT_OFFSET                                    20
#define PASCTL10_RANK_BLK21_TRIG_MASK                                  0x00200000
#define PASCTL10_RANK_BLK21_TRIG_BIT_OFFSET                                    21
#define PASCTL10_RANK_BLK22_TRIG_MASK                                  0x00400000
#define PASCTL10_RANK_BLK22_TRIG_BIT_OFFSET                                    22
#define PASCTL10_RANK_BLK23_TRIG_MASK                                  0x00800000
#define PASCTL10_RANK_BLK23_TRIG_BIT_OFFSET                                    23
#define PASCTL10_RANK_BLK24_TRIG_MASK                                  0x01000000
#define PASCTL10_RANK_BLK24_TRIG_BIT_OFFSET                                    24
#define PASCTL10_RANK_BLK25_TRIG_MASK                                  0x02000000
#define PASCTL10_RANK_BLK25_TRIG_BIT_OFFSET                                    25
#define PASCTL10_RANK_BLK26_TRIG_MASK                                  0x04000000
#define PASCTL10_RANK_BLK26_TRIG_BIT_OFFSET                                    26
#define PASCTL10_RANK_BLK27_TRIG_MASK                                  0x08000000
#define PASCTL10_RANK_BLK27_TRIG_BIT_OFFSET                                    27
#define PASCTL10_RANK_BLK28_TRIG_MASK                                  0x10000000
#define PASCTL10_RANK_BLK28_TRIG_BIT_OFFSET                                    28
#define PASCTL10_RANK_BLK29_TRIG_MASK                                  0x20000000
#define PASCTL10_RANK_BLK29_TRIG_BIT_OFFSET                                    29
#define PASCTL10_RANK_BLK30_TRIG_MASK                                  0x40000000
#define PASCTL10_RANK_BLK30_TRIG_BIT_OFFSET                                    30
#define PASCTL10_RANK_BLK31_TRIG_MASK                                  0x80000000
#define PASCTL10_RANK_BLK31_TRIG_BIT_OFFSET                                    31

#define PASCTL11                                                       0x00000A2C
#define PASCTL11_POWERDOWN_ENTRY_BA_0_MASK                             0x000000FF
#define PASCTL11_POWERDOWN_ENTRY_BA_0_BIT_OFFSET                                0
#define PASCTL11_POWERDOWN_ENTRY_SIZE_0_MASK                           0x00FF0000
#define PASCTL11_POWERDOWN_ENTRY_SIZE_0_BIT_OFFSET                             16

#define PASCTL12                                                       0x00000A30
#define PASCTL12_POWERDOWN_EXIT_BA_0_MASK                              0x000000FF
#define PASCTL12_POWERDOWN_EXIT_BA_0_BIT_OFFSET                                 0
#define PASCTL12_POWERDOWN_EXIT_SIZE_0_MASK                            0x00FF0000
#define PASCTL12_POWERDOWN_EXIT_SIZE_0_BIT_OFFSET                              16

#define PASCTL13                                                       0x00000A34
#define PASCTL13_POWERDOWN_ENTRY_BA_1_MASK                             0x000000FF
#define PASCTL13_POWERDOWN_ENTRY_BA_1_BIT_OFFSET                                0
#define PASCTL13_POWERDOWN_ENTRY_SIZE_1_MASK                           0x00FF0000
#define PASCTL13_POWERDOWN_ENTRY_SIZE_1_BIT_OFFSET                             16

#define PASCTL14                                                       0x00000A38
#define PASCTL14_POWERDOWN_EXIT_BA_1_MASK                              0x000000FF
#define PASCTL14_POWERDOWN_EXIT_BA_1_BIT_OFFSET                                 0
#define PASCTL14_POWERDOWN_EXIT_SIZE_1_MASK                            0x00FF0000
#define PASCTL14_POWERDOWN_EXIT_SIZE_1_BIT_OFFSET                              16

#define PASCTL15                                                       0x00000A3C
#define PASCTL15_POWERDOWN_ENTRY_BA_2_MASK                             0x000000FF
#define PASCTL15_POWERDOWN_ENTRY_BA_2_BIT_OFFSET                                0
#define PASCTL15_POWERDOWN_ENTRY_SIZE_2_MASK                           0x00FF0000
#define PASCTL15_POWERDOWN_ENTRY_SIZE_2_BIT_OFFSET                             16

#define PASCTL16                                                       0x00000A40
#define PASCTL16_POWERDOWN_EXIT_BA_2_MASK                              0x000000FF
#define PASCTL16_POWERDOWN_EXIT_BA_2_BIT_OFFSET                                 0
#define PASCTL16_POWERDOWN_EXIT_SIZE_2_MASK                            0x00FF0000
#define PASCTL16_POWERDOWN_EXIT_SIZE_2_BIT_OFFSET                              16

#define PASCTL17                                                       0x00000A44
#define PASCTL17_POWERDOWN_ENTRY_BA_3_MASK                             0x000000FF
#define PASCTL17_POWERDOWN_ENTRY_BA_3_BIT_OFFSET                                0
#define PASCTL17_POWERDOWN_ENTRY_SIZE_3_MASK                           0x00FF0000
#define PASCTL17_POWERDOWN_ENTRY_SIZE_3_BIT_OFFSET                             16

#define PASCTL18                                                       0x00000A48
#define PASCTL18_POWERDOWN_EXIT_BA_3_MASK                              0x000000FF
#define PASCTL18_POWERDOWN_EXIT_BA_3_BIT_OFFSET                                 0
#define PASCTL18_POWERDOWN_EXIT_SIZE_3_MASK                            0x00FF0000
#define PASCTL18_POWERDOWN_EXIT_SIZE_3_BIT_OFFSET                              16

#define PASCTL19                                                       0x00000A4C
#define PASCTL19_PRANK0_MODE_MASK                                      0x000000FF
#define PASCTL19_PRANK0_MODE_BIT_OFFSET                                         0
#define PASCTL19_PRANK1_MODE_MASK                                      0x0000FF00
#define PASCTL19_PRANK1_MODE_BIT_OFFSET                                         8
#define PASCTL19_PRANK2_MODE_MASK                                      0x00FF0000
#define PASCTL19_PRANK2_MODE_BIT_OFFSET                                        16
#define PASCTL19_PRANK3_MODE_MASK                                      0xFF000000
#define PASCTL19_PRANK3_MODE_BIT_OFFSET                                        24

#define PASCTL20                                                       0x00000A50
#define PASCTL20_SELFREF_ENTRY1_BA_0_MASK                              0x000000FF
#define PASCTL20_SELFREF_ENTRY1_BA_0_BIT_OFFSET                                 0
#define PASCTL20_SELFREF_ENTRY1_SIZE_0_MASK                            0x00FF0000
#define PASCTL20_SELFREF_ENTRY1_SIZE_0_BIT_OFFSET                              16

#define PASCTL21                                                       0x00000A54
#define PASCTL21_SELFREF_ENTRY2_BA_0_MASK                              0x000000FF
#define PASCTL21_SELFREF_ENTRY2_BA_0_BIT_OFFSET                                 0
#define PASCTL21_SELFREF_ENTRY2_SIZE_0_MASK                            0x00FF0000
#define PASCTL21_SELFREF_ENTRY2_SIZE_0_BIT_OFFSET                              16

#define PASCTL22                                                       0x00000A58
#define PASCTL22_SELFREF_EXIT1_BA_0_MASK                               0x000000FF
#define PASCTL22_SELFREF_EXIT1_BA_0_BIT_OFFSET                                  0
#define PASCTL22_SELFREF_EXIT1_SIZE_0_MASK                             0x00FF0000
#define PASCTL22_SELFREF_EXIT1_SIZE_0_BIT_OFFSET                               16

#define PASCTL23                                                       0x00000A5C
#define PASCTL23_SELFREF_EXIT2_BA_0_MASK                               0x000000FF
#define PASCTL23_SELFREF_EXIT2_BA_0_BIT_OFFSET                                  0
#define PASCTL23_SELFREF_EXIT2_SIZE_0_MASK                             0x00FF0000
#define PASCTL23_SELFREF_EXIT2_SIZE_0_BIT_OFFSET                               16

#define PASCTL24                                                       0x00000A60
#define PASCTL24_RFM_RAA_EN_MASK                                       0x0000000F
#define PASCTL24_RFM_RAA_EN_BIT_OFFSET                                          0
#define PASCTL24_RFM_RAA_RESET_MASK                                    0x000000F0
#define PASCTL24_RFM_RAA_RESET_BIT_OFFSET                                       4
#define PASCTL24_RFM_RAA_USE_ECS_REFAB_MASK                            0x00000100
#define PASCTL24_RFM_RAA_USE_ECS_REFAB_BIT_OFFSET                               8
#define PASCTL24_RFM_ALERT_THR_MASK                                    0xFFFF0000
#define PASCTL24_RFM_ALERT_THR_BIT_OFFSET                                      16

#define PASCTL25                                                       0x00000A64
#define PASCTL25_RFM_CMD_LOG_MASK                                      0xFFFFFFFF
#define PASCTL25_RFM_CMD_LOG_BIT_OFFSET                                         0

#define PASCTL26                                                       0x00000A68
#define PASCTL26_CAPAR_RETRY_SIZE_MASK                                 0x003F0000
#define PASCTL26_CAPAR_RETRY_SIZE_BIT_OFFSET                                   16

#define PASCTL36                                                       0x00000A90
#define PASCTL36_POWERDOWN_IDLE_CTRL_0_MASK                            0x00000003
#define PASCTL36_POWERDOWN_IDLE_CTRL_0_BIT_OFFSET                               0
#define PASCTL36_POWERDOWN_IDLE_CTRL_1_MASK                            0x00000004
#define PASCTL36_POWERDOWN_IDLE_CTRL_1_BIT_OFFSET                               2

#define PASCTL37                                                       0x00000A94
#define PASCTL37_DCH_SYNC_MODE_MASK                                    0x00000001
#define PASCTL37_DCH_SYNC_MODE_BIT_OFFSET                                       0
#define PASCTL37_DCH_CH0_MASK_MASK                                     0x00000002
#define PASCTL37_DCH_CH0_MASK_BIT_OFFSET                                        1
#define PASCTL37_T_SELFREF_EXIT_STAGGER_MASK                           0x01FF0000
#define PASCTL37_T_SELFREF_EXIT_STAGGER_BIT_OFFSET                             16

#define PASCTL38                                                       0x00000A98
#define PASCTL38_BWL_WIN_LEN_MASK                                      0x000003FF
#define PASCTL38_BWL_WIN_LEN_BIT_OFFSET                                         0
#define PASCTL38_BWL_EN_LEN_MASK                                       0x000FFC00
#define PASCTL38_BWL_EN_LEN_BIT_OFFSET                                         10
#define PASCTL38_BWL_CTRL_MASK                                         0x40000000
#define PASCTL38_BWL_CTRL_BIT_OFFSET                                           30
#define PASCTL38_BWL_EN_MASK                                           0x80000000
#define PASCTL38_BWL_EN_BIT_OFFSET                                             31

#define ECSCTL                                                         0x00000AF0
#define ECSCTL_AUTO_ECS_REFAB_EN_MASK                                  0xFFFFFFFF
#define ECSCTL_AUTO_ECS_REFAB_EN_BIT_OFFSET                                     0

#define ECS_STAT_DEV_SEL                                               0x00000AF4
#define ECS_STAT_DEV_SEL_TARGET_ECS_MRR_DEVICE_IDX_MASK                0x0000001F
#define ECS_STAT_DEV_SEL_TARGET_ECS_MRR_DEVICE_IDX_BIT_OFFSET                   0

#define ECS_STAT_MR0                                                   0x00000AF8
#define ECS_STAT_MR0_ECS_MR16_MASK                                     0x000000FF
#define ECS_STAT_MR0_ECS_MR16_BIT_OFFSET                                        0
#define ECS_STAT_MR0_ECS_MR17_MASK                                     0x0000FF00
#define ECS_STAT_MR0_ECS_MR17_BIT_OFFSET                                        8
#define ECS_STAT_MR0_ECS_MR18_MASK                                     0x00FF0000
#define ECS_STAT_MR0_ECS_MR18_BIT_OFFSET                                       16
#define ECS_STAT_MR0_ECS_MR19_MASK                                     0xFF000000
#define ECS_STAT_MR0_ECS_MR19_BIT_OFFSET                                       24

#define ECS_STAT_MR1                                                   0x00000AFC
#define ECS_STAT_MR1_ECS_MR20_MASK                                     0x000000FF
#define ECS_STAT_MR1_ECS_MR20_BIT_OFFSET                                        0

#define CMDCFG                                                         0x00000B00
#define CMDCFG_CMD_TYPE_MASK                                           0x00000001
#define CMDCFG_CMD_TYPE_BIT_OFFSET                                              0
#define CMDCFG_MULTI_CYC_CS_EN_MASK                                    0x00000002
#define CMDCFG_MULTI_CYC_CS_EN_BIT_OFFSET                                       1
#define CMDCFG_PDE_ODT_CTRL_MASK                                       0x00000004
#define CMDCFG_PDE_ODT_CTRL_BIT_OFFSET                                          2
#define CMDCFG_PD_MRR_NT_ODT_EN_MASK                                   0x00000008
#define CMDCFG_PD_MRR_NT_ODT_EN_BIT_OFFSET                                      3
#define CMDCFG_CMD_TIMER_X32_MASK                                      0x0000FFF0
#define CMDCFG_CMD_TIMER_X32_BIT_OFFSET                                         4
#define CMDCFG_MRR_GRP_SEL_MASK                                        0x00070000
#define CMDCFG_MRR_GRP_SEL_BIT_OFFSET                                          16
#define CMDCFG_CTRLUPD_RETRY_THR_MASK                                  0x01E00000
#define CMDCFG_CTRLUPD_RETRY_THR_BIT_OFFSET                                    21

#define CMDCTL                                                         0x00000B04
#define CMDCTL_CMD_CTRL_MASK                                           0x00FFFFFF
#define CMDCTL_CMD_CTRL_BIT_OFFSET                                              0
#define CMDCTL_CMD_CODE_MASK                                           0x1F000000
#define CMDCTL_CMD_CODE_BIT_OFFSET                                             24
#define CMDCTL_CMD_SEQ_ONGOING_MASK                                    0x20000000
#define CMDCTL_CMD_SEQ_ONGOING_BIT_OFFSET                                      29
#define CMDCTL_CMD_SEQ_LAST_MASK                                       0x40000000
#define CMDCTL_CMD_SEQ_LAST_BIT_OFFSET                                         30
#define CMDCTL_CMD_START_MASK                                          0x80000000
#define CMDCTL_CMD_START_BIT_OFFSET                                            31

#define CMDEXTCTL                                                      0x00000B08
#define CMDEXTCTL_CMD_EXT_CTRL_MASK                                    0xFFFFFFFF
#define CMDEXTCTL_CMD_EXT_CTRL_BIT_OFFSET                                       0

#define CMDSTAT                                                        0x00000B0C
#define CMDSTAT_MRR_DATA_VLD_MASK                                      0x00000001
#define CMDSTAT_MRR_DATA_VLD_BIT_OFFSET                                         0
#define CMDSTAT_RD_DATA_VLD_MASK                                       0x00000002
#define CMDSTAT_RD_DATA_VLD_BIT_OFFSET                                          1
#define CMDSTAT_DDR5_2N_MODE_MASK                                      0x00000004
#define CMDSTAT_DDR5_2N_MODE_BIT_OFFSET                                         2
#define CMDSTAT_SWCMD_LOCK_MASK                                        0x00000100
#define CMDSTAT_SWCMD_LOCK_BIT_OFFSET                                           8
#define CMDSTAT_DUCMD_LOCK_MASK                                        0x00000200
#define CMDSTAT_DUCMD_LOCK_BIT_OFFSET                                           9
#define CMDSTAT_LCCMD_LOCK_MASK                                        0x00000400
#define CMDSTAT_LCCMD_LOCK_BIT_OFFSET                                          10
#define CMDSTAT_CMD_RSLT_MASK                                          0x3FFFF000
#define CMDSTAT_CMD_RSLT_BIT_OFFSET                                            12
#define CMDSTAT_CMD_ERR_MASK                                           0x40000000
#define CMDSTAT_CMD_ERR_BIT_OFFSET                                             30
#define CMDSTAT_CMD_DONE_MASK                                          0x80000000
#define CMDSTAT_CMD_DONE_BIT_OFFSET                                            31

#define CMDMRRDATA                                                     0x00000B14
#define CMDMRRDATA_CMD_MRR_DATA_MASK                                   0xFFFFFFFF
#define CMDMRRDATA_CMD_MRR_DATA_BIT_OFFSET                                      0

#define PASINT                                                         0x00000B18
#define PASINT_SWCMD_ERR_INTR_MASK                                     0x00000001
#define PASINT_SWCMD_ERR_INTR_BIT_OFFSET                                        0
#define PASINT_DUCMD_ERR_INTR_MASK                                     0x00000002
#define PASINT_DUCMD_ERR_INTR_BIT_OFFSET                                        1
#define PASINT_LCCMD_ERR_INTR_MASK                                     0x00000004
#define PASINT_LCCMD_ERR_INTR_BIT_OFFSET                                        2
#define PASINT_CTRLUPD_ERR_INTR_MASK                                   0x00000008
#define PASINT_CTRLUPD_ERR_INTR_BIT_OFFSET                                      3
#define PASINT_RFM_ALERT_INTR_MASK                                     0x00000010
#define PASINT_RFM_ALERT_INTR_BIT_OFFSET                                        4
#define PASINT_CAPARCMD_ERR_INTR_MASK                                  0x00000020
#define PASINT_CAPARCMD_ERR_INTR_BIT_OFFSET                                     5

#define PASINTCTL                                                      0x00000B1C
#define PASINTCTL_SWCMD_ERR_INTR_EN_MASK                               0x00000001
#define PASINTCTL_SWCMD_ERR_INTR_EN_BIT_OFFSET                                  0
#define PASINTCTL_SWCMD_ERR_INTR_CLR_MASK                              0x00000002
#define PASINTCTL_SWCMD_ERR_INTR_CLR_BIT_OFFSET                                 1
#define PASINTCTL_SWCMD_ERR_INTR_FORCE_MASK                            0x00000004
#define PASINTCTL_SWCMD_ERR_INTR_FORCE_BIT_OFFSET                               2
#define PASINTCTL_DUCMD_ERR_INTR_EN_MASK                               0x00000010
#define PASINTCTL_DUCMD_ERR_INTR_EN_BIT_OFFSET                                  4
#define PASINTCTL_DUCMD_ERR_INTR_CLR_MASK                              0x00000020
#define PASINTCTL_DUCMD_ERR_INTR_CLR_BIT_OFFSET                                 5
#define PASINTCTL_DUCMD_ERR_INTR_FORCE_MASK                            0x00000040
#define PASINTCTL_DUCMD_ERR_INTR_FORCE_BIT_OFFSET                               6
#define PASINTCTL_LCCMD_ERR_INTR_EN_MASK                               0x00000100
#define PASINTCTL_LCCMD_ERR_INTR_EN_BIT_OFFSET                                  8
#define PASINTCTL_LCCMD_ERR_INTR_CLR_MASK                              0x00000200
#define PASINTCTL_LCCMD_ERR_INTR_CLR_BIT_OFFSET                                 9
#define PASINTCTL_LCCMD_ERR_INTR_FORCE_MASK                            0x00000400
#define PASINTCTL_LCCMD_ERR_INTR_FORCE_BIT_OFFSET                              10
#define PASINTCTL_CTRLUPD_ERR_INTR_EN_MASK                             0x00001000
#define PASINTCTL_CTRLUPD_ERR_INTR_EN_BIT_OFFSET                               12
#define PASINTCTL_CTRLUPD_ERR_INTR_CLR_MASK                            0x00002000
#define PASINTCTL_CTRLUPD_ERR_INTR_CLR_BIT_OFFSET                              13
#define PASINTCTL_CTRLUPD_ERR_INTR_FORCE_MASK                          0x00004000
#define PASINTCTL_CTRLUPD_ERR_INTR_FORCE_BIT_OFFSET                            14
#define PASINTCTL_RFM_ALERT_INTR_EN_MASK                               0x00010000
#define PASINTCTL_RFM_ALERT_INTR_EN_BIT_OFFSET                                 16
#define PASINTCTL_RFM_ALERT_INTR_CLR_MASK                              0x00020000
#define PASINTCTL_RFM_ALERT_INTR_CLR_BIT_OFFSET                                17
#define PASINTCTL_RFM_ALERT_INTR_FORCE_MASK                            0x00040000
#define PASINTCTL_RFM_ALERT_INTR_FORCE_BIT_OFFSET                              18
#define PASINTCTL_CAPARCMD_ERR_INTR_EN_MASK                            0x00100000
#define PASINTCTL_CAPARCMD_ERR_INTR_EN_BIT_OFFSET                              20
#define PASINTCTL_CAPARCMD_ERR_INTR_CLR_MASK                           0x00200000
#define PASINTCTL_CAPARCMD_ERR_INTR_CLR_BIT_OFFSET                             21
#define PASINTCTL_CAPARCMD_ERR_INTR_FORCE_MASK                         0x00400000
#define PASINTCTL_CAPARCMD_ERR_INTR_FORCE_BIT_OFFSET                           22

#define PASERRSTS                                                      0x00000B20
#define PASERRSTS_SWCMD_ERR_STS_MASK                                   0x00000007
#define PASERRSTS_SWCMD_ERR_STS_BIT_OFFSET                                      0
#define PASERRSTS_DUCMD_ERR_STS_MASK                                   0x00000070
#define PASERRSTS_DUCMD_ERR_STS_BIT_OFFSET                                      4
#define PASERRSTS_LCCMD_ERR_STS_MASK                                   0x00000700
#define PASERRSTS_LCCMD_ERR_STS_BIT_OFFSET                                      8
#define PASERRSTS_CAPARCMD_ERR_STS_MASK                                0x00007000
#define PASERRSTS_CAPARCMD_ERR_STS_BIT_OFFSET                                  12

#define DU_CFGBUF_CTRL                                                 0x00000B24
#define DU_CFGBUF_CTRL_DU_CFGBUF_WDATA_MASK                            0x0000FFFF
#define DU_CFGBUF_CTRL_DU_CFGBUF_WDATA_BIT_OFFSET                               0
#define DU_CFGBUF_CTRL_DU_CFGBUF_ADDR_MASK                             0x00FF0000
#define DU_CFGBUF_CTRL_DU_CFGBUF_ADDR_BIT_OFFSET                               16
#define DU_CFGBUF_CTRL_DU_CFGBUF_SELECT_MASK                           0x01000000
#define DU_CFGBUF_CTRL_DU_CFGBUF_SELECT_BIT_OFFSET                             24
#define DU_CFGBUF_CTRL_DU_CFGBUF_OP_MODE_MASK                          0x20000000
#define DU_CFGBUF_CTRL_DU_CFGBUF_OP_MODE_BIT_OFFSET                            29
#define DU_CFGBUF_CTRL_DU_CFGBUF_RW_TYPE_MASK                          0x40000000
#define DU_CFGBUF_CTRL_DU_CFGBUF_RW_TYPE_BIT_OFFSET                            30
#define DU_CFGBUF_CTRL_DU_CFGBUF_RW_START_MASK                         0x80000000
#define DU_CFGBUF_CTRL_DU_CFGBUF_RW_START_BIT_OFFSET                           31

#define DU_CFGBUF_STAT                                                 0x00000B28
#define DU_CFGBUF_STAT_DU_CFGBUF_RDATA_MASK                            0x0000FFFF
#define DU_CFGBUF_STAT_DU_CFGBUF_RDATA_BIT_OFFSET                               0

#define DU_CMDBUF_CTRL                                                 0x00000B2C
#define DU_CMDBUF_CTRL_DU_CMDBUF_WDATA_MASK                            0x0000FFFF
#define DU_CMDBUF_CTRL_DU_CMDBUF_WDATA_BIT_OFFSET                               0
#define DU_CMDBUF_CTRL_DU_CMDBUF_ADDR_MASK                             0x00FF0000
#define DU_CMDBUF_CTRL_DU_CMDBUF_ADDR_BIT_OFFSET                               16
#define DU_CMDBUF_CTRL_DU_CMDBUF_SELECT_MASK                           0x01000000
#define DU_CMDBUF_CTRL_DU_CMDBUF_SELECT_BIT_OFFSET                             24
#define DU_CMDBUF_CTRL_DU_CMDBUF_OP_MODE_MASK                          0x20000000
#define DU_CMDBUF_CTRL_DU_CMDBUF_OP_MODE_BIT_OFFSET                            29
#define DU_CMDBUF_CTRL_DU_CMDBUF_RW_TYPE_MASK                          0x40000000
#define DU_CMDBUF_CTRL_DU_CMDBUF_RW_TYPE_BIT_OFFSET                            30
#define DU_CMDBUF_CTRL_DU_CMDBUF_RW_START_MASK                         0x80000000
#define DU_CMDBUF_CTRL_DU_CMDBUF_RW_START_BIT_OFFSET                           31

#define DU_CMDBUF_STAT                                                 0x00000B30
#define DU_CMDBUF_STAT_DU_CMDBUF_RDATA_MASK                            0x0000FFFF
#define DU_CMDBUF_STAT_DU_CMDBUF_RDATA_BIT_OFFSET                               0

#define LP_CMDBUF_CTRL                                                 0x00000B34
#define LP_CMDBUF_CTRL_LP_CMDBUF_WDATA_MASK                            0x0000FFFF
#define LP_CMDBUF_CTRL_LP_CMDBUF_WDATA_BIT_OFFSET                               0
#define LP_CMDBUF_CTRL_LP_CMDBUF_ADDR_MASK                             0x00FF0000
#define LP_CMDBUF_CTRL_LP_CMDBUF_ADDR_BIT_OFFSET                               16
#define LP_CMDBUF_CTRL_LP_CMDBUF_OP_MODE_MASK                          0x20000000
#define LP_CMDBUF_CTRL_LP_CMDBUF_OP_MODE_BIT_OFFSET                            29
#define LP_CMDBUF_CTRL_LP_CMDBUF_RW_TYPE_MASK                          0x40000000
#define LP_CMDBUF_CTRL_LP_CMDBUF_RW_TYPE_BIT_OFFSET                            30
#define LP_CMDBUF_CTRL_LP_CMDBUF_RW_START_MASK                         0x80000000
#define LP_CMDBUF_CTRL_LP_CMDBUF_RW_START_BIT_OFFSET                           31

#define LP_CMDBUF_STAT                                                 0x00000B38
#define LP_CMDBUF_STAT_LP_CMDBUF_RDATA_MASK                            0x0000FFFF
#define LP_CMDBUF_STAT_LP_CMDBUF_RDATA_BIT_OFFSET                               0

#define RW_CMD_CTRL                                                    0x00000B3C
#define RW_CMD_CTRL_WR_DATA_CB_MASK                                    0x000000FF
#define RW_CMD_CTRL_WR_DATA_CB_BIT_OFFSET                                       0
#define RW_CMD_CTRL_WR_DATA_DQ_MASK_MASK                               0x0000FF00
#define RW_CMD_CTRL_WR_DATA_DQ_MASK_BIT_OFFSET                                  8
#define RW_CMD_CTRL_WR_DATA_CB_MASK_MASK                               0x00100000
#define RW_CMD_CTRL_WR_DATA_CB_MASK_BIT_OFFSET                                 20
#define RW_CMD_CTRL_DATA_ECC_SEL_MASK                                  0x00200000
#define RW_CMD_CTRL_DATA_ECC_SEL_BIT_OFFSET                                    21
#define RW_CMD_CTRL_RW_ECC_EN_MASK                                     0x00400000
#define RW_CMD_CTRL_RW_ECC_EN_BIT_OFFSET                                       22
#define RW_CMD_CTRL_WR_DATA_SEL_MASK                                   0x00800000
#define RW_CMD_CTRL_WR_DATA_SEL_BIT_OFFSET                                     23
#define RW_CMD_CTRL_BUF_ADDR_MASK                                      0x0F000000
#define RW_CMD_CTRL_BUF_ADDR_BIT_OFFSET                                        24
#define RW_CMD_CTRL_BUF_RW_OP_TYPE_MASK                                0x40000000
#define RW_CMD_CTRL_BUF_RW_OP_TYPE_BIT_OFFSET                                  30
#define RW_CMD_CTRL_BUF_RW_START_MASK                                  0x80000000
#define RW_CMD_CTRL_BUF_RW_START_BIT_OFFSET                                    31

#define RW_WR_DATA0                                                    0x00000B40
#define RW_WR_DATA0_WR_DATA_DQ0_MASK                                   0xFFFFFFFF
#define RW_WR_DATA0_WR_DATA_DQ0_BIT_OFFSET                                      0

#define RW_WR_DATA1                                                    0x00000B44
#define RW_WR_DATA1_WR_DATA_DQ1_MASK                                   0xFFFFFFFF
#define RW_WR_DATA1_WR_DATA_DQ1_BIT_OFFSET                                      0

#define RW_RD_DATA0                                                    0x00000B48
#define RW_RD_DATA0_RD_DATA_DQ0_MASK                                   0xFFFFFFFF
#define RW_RD_DATA0_RD_DATA_DQ0_BIT_OFFSET                                      0

#define RW_RD_DATA1                                                    0x00000B4C
#define RW_RD_DATA1_RD_DATA_DQ1_MASK                                   0xFFFFFFFF
#define RW_RD_DATA1_RD_DATA_DQ1_BIT_OFFSET                                      0

#define CAPAR_CMDBUF_CTRL                                              0x00000B50
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_WDATA_MASK                      0x0000FFFF
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_WDATA_BIT_OFFSET                         0
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_ADDR_MASK                       0x003F0000
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_ADDR_BIT_OFFSET                         16
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_OP_MODE_MASK                    0x20000000
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_OP_MODE_BIT_OFFSET                      29
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_RW_TYPE_MASK                    0x40000000
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_RW_TYPE_BIT_OFFSET                      30
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_RW_START_MASK                   0x80000000
#define CAPAR_CMDBUF_CTRL_CAPAR_CMDBUF_RW_START_BIT_OFFSET                     31

#define CAPAR_CMDBUF_STAT                                              0x00000B54
#define CAPAR_CMDBUF_STAT_CAPAR_CMDBUF_RDATA_MASK                      0x0000FFFF
#define CAPAR_CMDBUF_STAT_CAPAR_CMDBUF_RDATA_BIT_OFFSET                         0

#define OPCTRL0                                                        0x00000B80
#define OPCTRL0_DIS_WC_MASK                                            0x00000001
#define OPCTRL0_DIS_WC_BIT_OFFSET                                               0
#define OPCTRL0_DIS_RD_BYPASS_MASK                                     0x00000002
#define OPCTRL0_DIS_RD_BYPASS_BIT_OFFSET                                        1
#define OPCTRL0_DIS_ACT_BYPASS_MASK                                    0x00000004
#define OPCTRL0_DIS_ACT_BYPASS_BIT_OFFSET                                       2
#define OPCTRL0_DIS_MAX_RANK_RD_OPT_MASK                               0x00000040
#define OPCTRL0_DIS_MAX_RANK_RD_OPT_BIT_OFFSET                                  6
#define OPCTRL0_DIS_MAX_RANK_WR_OPT_MASK                               0x00000080
#define OPCTRL0_DIS_MAX_RANK_WR_OPT_BIT_OFFSET                                  7

#define OPCTRL1                                                        0x00000B84
#define OPCTRL1_DIS_DQ_MASK                                            0x00000001
#define OPCTRL1_DIS_DQ_BIT_OFFSET                                               0
#define OPCTRL1_DIS_HIF_MASK                                           0x00000002
#define OPCTRL1_DIS_HIF_BIT_OFFSET                                              1

#define OPCTRLCAM                                                      0x00000B88
#define OPCTRLCAM_DBG_HPR_Q_DEPTH_MASK                                 0x000000FF
#define OPCTRLCAM_DBG_HPR_Q_DEPTH_BIT_OFFSET                                    0
#define OPCTRLCAM_DBG_LPR_Q_DEPTH_MASK                                 0x0000FF00
#define OPCTRLCAM_DBG_LPR_Q_DEPTH_BIT_OFFSET                                    8
#define OPCTRLCAM_DBG_W_Q_DEPTH_MASK                                   0x00FF0000
#define OPCTRLCAM_DBG_W_Q_DEPTH_BIT_OFFSET                                     16
#define OPCTRLCAM_DBG_STALL_MASK                                       0x01000000
#define OPCTRLCAM_DBG_STALL_BIT_OFFSET                                         24
#define OPCTRLCAM_DBG_RD_Q_EMPTY_MASK                                  0x02000000
#define OPCTRLCAM_DBG_RD_Q_EMPTY_BIT_OFFSET                                    25
#define OPCTRLCAM_DBG_WR_Q_EMPTY_MASK                                  0x04000000
#define OPCTRLCAM_DBG_WR_Q_EMPTY_BIT_OFFSET                                    26
#define OPCTRLCAM_RD_DATA_PIPELINE_EMPTY_MASK                          0x10000000
#define OPCTRLCAM_RD_DATA_PIPELINE_EMPTY_BIT_OFFSET                            28
#define OPCTRLCAM_WR_DATA_PIPELINE_EMPTY_MASK                          0x20000000
#define OPCTRLCAM_WR_DATA_PIPELINE_EMPTY_BIT_OFFSET                            29
#define OPCTRLCAM_DBG_STALL_WR_MASK                                    0x40000000
#define OPCTRLCAM_DBG_STALL_WR_BIT_OFFSET                                      30
#define OPCTRLCAM_DBG_STALL_RD_MASK                                    0x80000000
#define OPCTRLCAM_DBG_STALL_RD_BIT_OFFSET                                      31

#define OPCTRLCMD                                                      0x00000B8C
#define OPCTRLCMD_ZQ_CALIB_SHORT_MASK                                  0x00010000
#define OPCTRLCMD_ZQ_CALIB_SHORT_BIT_OFFSET                                    16
#define OPCTRLCMD_CTRLUPD_MASK                                         0x00020000
#define OPCTRLCMD_CTRLUPD_BIT_OFFSET                                           17
#define OPCTRLCMD_CTRLUPD_BURST_MASK                                   0x00040000
#define OPCTRLCMD_CTRLUPD_BURST_BIT_OFFSET                                     18
#define OPCTRLCMD_HW_REF_ZQ_EN_MASK                                    0x80000000
#define OPCTRLCMD_HW_REF_ZQ_EN_BIT_OFFSET                                      31

#define OPCTRLSTAT                                                     0x00000B90
#define OPCTRLSTAT_ZQ_CALIB_SHORT_BUSY_MASK                            0x00010000
#define OPCTRLSTAT_ZQ_CALIB_SHORT_BUSY_BIT_OFFSET                              16
#define OPCTRLSTAT_CTRLUPD_BUSY_MASK                                   0x00020000
#define OPCTRLSTAT_CTRLUPD_BUSY_BIT_OFFSET                                     17
#define OPCTRLSTAT_CTRLUPD_BURST_BUSY_MASK                             0x00040000
#define OPCTRLSTAT_CTRLUPD_BURST_BUSY_BIT_OFFSET                               18

#define OPCTRLCAM1                                                     0x00000B94
#define OPCTRLCAM1_DBG_WRECC_Q_DEPTH_MASK                              0xFFFFFFFF
#define OPCTRLCAM1_DBG_WRECC_Q_DEPTH_BIT_OFFSET                                 0

#define OPREFCTRL0                                                     0x00000B98
#define OPREFCTRL0_RANK0_REFRESH_MASK                                  0x00000001
#define OPREFCTRL0_RANK0_REFRESH_BIT_OFFSET                                     0
#define OPREFCTRL0_RANK1_REFRESH_MASK                                  0x00000002
#define OPREFCTRL0_RANK1_REFRESH_BIT_OFFSET                                     1
#define OPREFCTRL0_RANK2_REFRESH_MASK                                  0x00000004
#define OPREFCTRL0_RANK2_REFRESH_BIT_OFFSET                                     2
#define OPREFCTRL0_RANK3_REFRESH_MASK                                  0x00000008
#define OPREFCTRL0_RANK3_REFRESH_BIT_OFFSET                                     3
#define OPREFCTRL0_RANK4_REFRESH_MASK                                  0x00000010
#define OPREFCTRL0_RANK4_REFRESH_BIT_OFFSET                                     4
#define OPREFCTRL0_RANK5_REFRESH_MASK                                  0x00000020
#define OPREFCTRL0_RANK5_REFRESH_BIT_OFFSET                                     5
#define OPREFCTRL0_RANK6_REFRESH_MASK                                  0x00000040
#define OPREFCTRL0_RANK6_REFRESH_BIT_OFFSET                                     6
#define OPREFCTRL0_RANK7_REFRESH_MASK                                  0x00000080
#define OPREFCTRL0_RANK7_REFRESH_BIT_OFFSET                                     7
#define OPREFCTRL0_RANK8_REFRESH_MASK                                  0x00000100
#define OPREFCTRL0_RANK8_REFRESH_BIT_OFFSET                                     8
#define OPREFCTRL0_RANK9_REFRESH_MASK                                  0x00000200
#define OPREFCTRL0_RANK9_REFRESH_BIT_OFFSET                                     9
#define OPREFCTRL0_RANK10_REFRESH_MASK                                 0x00000400
#define OPREFCTRL0_RANK10_REFRESH_BIT_OFFSET                                   10
#define OPREFCTRL0_RANK11_REFRESH_MASK                                 0x00000800
#define OPREFCTRL0_RANK11_REFRESH_BIT_OFFSET                                   11
#define OPREFCTRL0_RANK12_REFRESH_MASK                                 0x00001000
#define OPREFCTRL0_RANK12_REFRESH_BIT_OFFSET                                   12
#define OPREFCTRL0_RANK13_REFRESH_MASK                                 0x00002000
#define OPREFCTRL0_RANK13_REFRESH_BIT_OFFSET                                   13
#define OPREFCTRL0_RANK14_REFRESH_MASK                                 0x00004000
#define OPREFCTRL0_RANK14_REFRESH_BIT_OFFSET                                   14
#define OPREFCTRL0_RANK15_REFRESH_MASK                                 0x00008000
#define OPREFCTRL0_RANK15_REFRESH_BIT_OFFSET                                   15
#define OPREFCTRL0_RANK16_REFRESH_MASK                                 0x00010000
#define OPREFCTRL0_RANK16_REFRESH_BIT_OFFSET                                   16
#define OPREFCTRL0_RANK17_REFRESH_MASK                                 0x00020000
#define OPREFCTRL0_RANK17_REFRESH_BIT_OFFSET                                   17
#define OPREFCTRL0_RANK18_REFRESH_MASK                                 0x00040000
#define OPREFCTRL0_RANK18_REFRESH_BIT_OFFSET                                   18
#define OPREFCTRL0_RANK19_REFRESH_MASK                                 0x00080000
#define OPREFCTRL0_RANK19_REFRESH_BIT_OFFSET                                   19
#define OPREFCTRL0_RANK20_REFRESH_MASK                                 0x00100000
#define OPREFCTRL0_RANK20_REFRESH_BIT_OFFSET                                   20
#define OPREFCTRL0_RANK21_REFRESH_MASK                                 0x00200000
#define OPREFCTRL0_RANK21_REFRESH_BIT_OFFSET                                   21
#define OPREFCTRL0_RANK22_REFRESH_MASK                                 0x00400000
#define OPREFCTRL0_RANK22_REFRESH_BIT_OFFSET                                   22
#define OPREFCTRL0_RANK23_REFRESH_MASK                                 0x00800000
#define OPREFCTRL0_RANK23_REFRESH_BIT_OFFSET                                   23
#define OPREFCTRL0_RANK24_REFRESH_MASK                                 0x01000000
#define OPREFCTRL0_RANK24_REFRESH_BIT_OFFSET                                   24
#define OPREFCTRL0_RANK25_REFRESH_MASK                                 0x02000000
#define OPREFCTRL0_RANK25_REFRESH_BIT_OFFSET                                   25
#define OPREFCTRL0_RANK26_REFRESH_MASK                                 0x04000000
#define OPREFCTRL0_RANK26_REFRESH_BIT_OFFSET                                   26
#define OPREFCTRL0_RANK27_REFRESH_MASK                                 0x08000000
#define OPREFCTRL0_RANK27_REFRESH_BIT_OFFSET                                   27
#define OPREFCTRL0_RANK28_REFRESH_MASK                                 0x10000000
#define OPREFCTRL0_RANK28_REFRESH_BIT_OFFSET                                   28
#define OPREFCTRL0_RANK29_REFRESH_MASK                                 0x20000000
#define OPREFCTRL0_RANK29_REFRESH_BIT_OFFSET                                   29
#define OPREFCTRL0_RANK30_REFRESH_MASK                                 0x40000000
#define OPREFCTRL0_RANK30_REFRESH_BIT_OFFSET                                   30
#define OPREFCTRL0_RANK31_REFRESH_MASK                                 0x80000000
#define OPREFCTRL0_RANK31_REFRESH_BIT_OFFSET                                   31

#define OPREFCTRL1                                                     0x00000B9C
#define OPREFCTRL1_RANK32_REFRESH_MASK                                 0x00000001
#define OPREFCTRL1_RANK32_REFRESH_BIT_OFFSET                                    0
#define OPREFCTRL1_RANK33_REFRESH_MASK                                 0x00000002
#define OPREFCTRL1_RANK33_REFRESH_BIT_OFFSET                                    1
#define OPREFCTRL1_RANK34_REFRESH_MASK                                 0x00000004
#define OPREFCTRL1_RANK34_REFRESH_BIT_OFFSET                                    2
#define OPREFCTRL1_RANK35_REFRESH_MASK                                 0x00000008
#define OPREFCTRL1_RANK35_REFRESH_BIT_OFFSET                                    3
#define OPREFCTRL1_RANK36_REFRESH_MASK                                 0x00000010
#define OPREFCTRL1_RANK36_REFRESH_BIT_OFFSET                                    4
#define OPREFCTRL1_RANK37_REFRESH_MASK                                 0x00000020
#define OPREFCTRL1_RANK37_REFRESH_BIT_OFFSET                                    5
#define OPREFCTRL1_RANK38_REFRESH_MASK                                 0x00000040
#define OPREFCTRL1_RANK38_REFRESH_BIT_OFFSET                                    6
#define OPREFCTRL1_RANK39_REFRESH_MASK                                 0x00000080
#define OPREFCTRL1_RANK39_REFRESH_BIT_OFFSET                                    7
#define OPREFCTRL1_RANK40_REFRESH_MASK                                 0x00000100
#define OPREFCTRL1_RANK40_REFRESH_BIT_OFFSET                                    8
#define OPREFCTRL1_RANK41_REFRESH_MASK                                 0x00000200
#define OPREFCTRL1_RANK41_REFRESH_BIT_OFFSET                                    9
#define OPREFCTRL1_RANK42_REFRESH_MASK                                 0x00000400
#define OPREFCTRL1_RANK42_REFRESH_BIT_OFFSET                                   10
#define OPREFCTRL1_RANK43_REFRESH_MASK                                 0x00000800
#define OPREFCTRL1_RANK43_REFRESH_BIT_OFFSET                                   11
#define OPREFCTRL1_RANK44_REFRESH_MASK                                 0x00001000
#define OPREFCTRL1_RANK44_REFRESH_BIT_OFFSET                                   12
#define OPREFCTRL1_RANK45_REFRESH_MASK                                 0x00002000
#define OPREFCTRL1_RANK45_REFRESH_BIT_OFFSET                                   13
#define OPREFCTRL1_RANK46_REFRESH_MASK                                 0x00004000
#define OPREFCTRL1_RANK46_REFRESH_BIT_OFFSET                                   14
#define OPREFCTRL1_RANK47_REFRESH_MASK                                 0x00008000
#define OPREFCTRL1_RANK47_REFRESH_BIT_OFFSET                                   15
#define OPREFCTRL1_RANK48_REFRESH_MASK                                 0x00010000
#define OPREFCTRL1_RANK48_REFRESH_BIT_OFFSET                                   16
#define OPREFCTRL1_RANK49_REFRESH_MASK                                 0x00020000
#define OPREFCTRL1_RANK49_REFRESH_BIT_OFFSET                                   17
#define OPREFCTRL1_RANK50_REFRESH_MASK                                 0x00040000
#define OPREFCTRL1_RANK50_REFRESH_BIT_OFFSET                                   18
#define OPREFCTRL1_RANK51_REFRESH_MASK                                 0x00080000
#define OPREFCTRL1_RANK51_REFRESH_BIT_OFFSET                                   19
#define OPREFCTRL1_RANK52_REFRESH_MASK                                 0x00100000
#define OPREFCTRL1_RANK52_REFRESH_BIT_OFFSET                                   20
#define OPREFCTRL1_RANK53_REFRESH_MASK                                 0x00200000
#define OPREFCTRL1_RANK53_REFRESH_BIT_OFFSET                                   21
#define OPREFCTRL1_RANK54_REFRESH_MASK                                 0x00400000
#define OPREFCTRL1_RANK54_REFRESH_BIT_OFFSET                                   22
#define OPREFCTRL1_RANK55_REFRESH_MASK                                 0x00800000
#define OPREFCTRL1_RANK55_REFRESH_BIT_OFFSET                                   23
#define OPREFCTRL1_RANK56_REFRESH_MASK                                 0x01000000
#define OPREFCTRL1_RANK56_REFRESH_BIT_OFFSET                                   24
#define OPREFCTRL1_RANK57_REFRESH_MASK                                 0x02000000
#define OPREFCTRL1_RANK57_REFRESH_BIT_OFFSET                                   25
#define OPREFCTRL1_RANK58_REFRESH_MASK                                 0x04000000
#define OPREFCTRL1_RANK58_REFRESH_BIT_OFFSET                                   26
#define OPREFCTRL1_RANK59_REFRESH_MASK                                 0x08000000
#define OPREFCTRL1_RANK59_REFRESH_BIT_OFFSET                                   27
#define OPREFCTRL1_RANK60_REFRESH_MASK                                 0x10000000
#define OPREFCTRL1_RANK60_REFRESH_BIT_OFFSET                                   28
#define OPREFCTRL1_RANK61_REFRESH_MASK                                 0x20000000
#define OPREFCTRL1_RANK61_REFRESH_BIT_OFFSET                                   29
#define OPREFCTRL1_RANK62_REFRESH_MASK                                 0x40000000
#define OPREFCTRL1_RANK62_REFRESH_BIT_OFFSET                                   30
#define OPREFCTRL1_RANK63_REFRESH_MASK                                 0x80000000
#define OPREFCTRL1_RANK63_REFRESH_BIT_OFFSET                                   31

#define OPREFSTAT0                                                     0x00000BA0
#define OPREFSTAT0_RANK0_REFRESH_BUSY_MASK                             0x00000001
#define OPREFSTAT0_RANK0_REFRESH_BUSY_BIT_OFFSET                                0
#define OPREFSTAT0_RANK1_REFRESH_BUSY_MASK                             0x00000002
#define OPREFSTAT0_RANK1_REFRESH_BUSY_BIT_OFFSET                                1
#define OPREFSTAT0_RANK2_REFRESH_BUSY_MASK                             0x00000004
#define OPREFSTAT0_RANK2_REFRESH_BUSY_BIT_OFFSET                                2
#define OPREFSTAT0_RANK3_REFRESH_BUSY_MASK                             0x00000008
#define OPREFSTAT0_RANK3_REFRESH_BUSY_BIT_OFFSET                                3
#define OPREFSTAT0_RANK4_REFRESH_BUSY_MASK                             0x00000010
#define OPREFSTAT0_RANK4_REFRESH_BUSY_BIT_OFFSET                                4
#define OPREFSTAT0_RANK5_REFRESH_BUSY_MASK                             0x00000020
#define OPREFSTAT0_RANK5_REFRESH_BUSY_BIT_OFFSET                                5
#define OPREFSTAT0_RANK6_REFRESH_BUSY_MASK                             0x00000040
#define OPREFSTAT0_RANK6_REFRESH_BUSY_BIT_OFFSET                                6
#define OPREFSTAT0_RANK7_REFRESH_BUSY_MASK                             0x00000080
#define OPREFSTAT0_RANK7_REFRESH_BUSY_BIT_OFFSET                                7
#define OPREFSTAT0_RANK8_REFRESH_BUSY_MASK                             0x00000100
#define OPREFSTAT0_RANK8_REFRESH_BUSY_BIT_OFFSET                                8
#define OPREFSTAT0_RANK9_REFRESH_BUSY_MASK                             0x00000200
#define OPREFSTAT0_RANK9_REFRESH_BUSY_BIT_OFFSET                                9
#define OPREFSTAT0_RANK10_REFRESH_BUSY_MASK                            0x00000400
#define OPREFSTAT0_RANK10_REFRESH_BUSY_BIT_OFFSET                              10
#define OPREFSTAT0_RANK11_REFRESH_BUSY_MASK                            0x00000800
#define OPREFSTAT0_RANK11_REFRESH_BUSY_BIT_OFFSET                              11
#define OPREFSTAT0_RANK12_REFRESH_BUSY_MASK                            0x00001000
#define OPREFSTAT0_RANK12_REFRESH_BUSY_BIT_OFFSET                              12
#define OPREFSTAT0_RANK13_REFRESH_BUSY_MASK                            0x00002000
#define OPREFSTAT0_RANK13_REFRESH_BUSY_BIT_OFFSET                              13
#define OPREFSTAT0_RANK14_REFRESH_BUSY_MASK                            0x00004000
#define OPREFSTAT0_RANK14_REFRESH_BUSY_BIT_OFFSET                              14
#define OPREFSTAT0_RANK15_REFRESH_BUSY_MASK                            0x00008000
#define OPREFSTAT0_RANK15_REFRESH_BUSY_BIT_OFFSET                              15
#define OPREFSTAT0_RANK16_REFRESH_BUSY_MASK                            0x00010000
#define OPREFSTAT0_RANK16_REFRESH_BUSY_BIT_OFFSET                              16
#define OPREFSTAT0_RANK17_REFRESH_BUSY_MASK                            0x00020000
#define OPREFSTAT0_RANK17_REFRESH_BUSY_BIT_OFFSET                              17
#define OPREFSTAT0_RANK18_REFRESH_BUSY_MASK                            0x00040000
#define OPREFSTAT0_RANK18_REFRESH_BUSY_BIT_OFFSET                              18
#define OPREFSTAT0_RANK19_REFRESH_BUSY_MASK                            0x00080000
#define OPREFSTAT0_RANK19_REFRESH_BUSY_BIT_OFFSET                              19
#define OPREFSTAT0_RANK20_REFRESH_BUSY_MASK                            0x00100000
#define OPREFSTAT0_RANK20_REFRESH_BUSY_BIT_OFFSET                              20
#define OPREFSTAT0_RANK21_REFRESH_BUSY_MASK                            0x00200000
#define OPREFSTAT0_RANK21_REFRESH_BUSY_BIT_OFFSET                              21
#define OPREFSTAT0_RANK22_REFRESH_BUSY_MASK                            0x00400000
#define OPREFSTAT0_RANK22_REFRESH_BUSY_BIT_OFFSET                              22
#define OPREFSTAT0_RANK23_REFRESH_BUSY_MASK                            0x00800000
#define OPREFSTAT0_RANK23_REFRESH_BUSY_BIT_OFFSET                              23
#define OPREFSTAT0_RANK24_REFRESH_BUSY_MASK                            0x01000000
#define OPREFSTAT0_RANK24_REFRESH_BUSY_BIT_OFFSET                              24
#define OPREFSTAT0_RANK25_REFRESH_BUSY_MASK                            0x02000000
#define OPREFSTAT0_RANK25_REFRESH_BUSY_BIT_OFFSET                              25
#define OPREFSTAT0_RANK26_REFRESH_BUSY_MASK                            0x04000000
#define OPREFSTAT0_RANK26_REFRESH_BUSY_BIT_OFFSET                              26
#define OPREFSTAT0_RANK27_REFRESH_BUSY_MASK                            0x08000000
#define OPREFSTAT0_RANK27_REFRESH_BUSY_BIT_OFFSET                              27
#define OPREFSTAT0_RANK28_REFRESH_BUSY_MASK                            0x10000000
#define OPREFSTAT0_RANK28_REFRESH_BUSY_BIT_OFFSET                              28
#define OPREFSTAT0_RANK29_REFRESH_BUSY_MASK                            0x20000000
#define OPREFSTAT0_RANK29_REFRESH_BUSY_BIT_OFFSET                              29
#define OPREFSTAT0_RANK30_REFRESH_BUSY_MASK                            0x40000000
#define OPREFSTAT0_RANK30_REFRESH_BUSY_BIT_OFFSET                              30
#define OPREFSTAT0_RANK31_REFRESH_BUSY_MASK                            0x80000000
#define OPREFSTAT0_RANK31_REFRESH_BUSY_BIT_OFFSET                              31

#define OPREFSTAT1                                                     0x00000BA4
#define OPREFSTAT1_RANK32_REFRESH_BUSY_MASK                            0x00000001
#define OPREFSTAT1_RANK32_REFRESH_BUSY_BIT_OFFSET                               0
#define OPREFSTAT1_RANK33_REFRESH_BUSY_MASK                            0x00000002
#define OPREFSTAT1_RANK33_REFRESH_BUSY_BIT_OFFSET                               1
#define OPREFSTAT1_RANK34_REFRESH_BUSY_MASK                            0x00000004
#define OPREFSTAT1_RANK34_REFRESH_BUSY_BIT_OFFSET                               2
#define OPREFSTAT1_RANK35_REFRESH_BUSY_MASK                            0x00000008
#define OPREFSTAT1_RANK35_REFRESH_BUSY_BIT_OFFSET                               3
#define OPREFSTAT1_RANK36_REFRESH_BUSY_MASK                            0x00000010
#define OPREFSTAT1_RANK36_REFRESH_BUSY_BIT_OFFSET                               4
#define OPREFSTAT1_RANK37_REFRESH_BUSY_MASK                            0x00000020
#define OPREFSTAT1_RANK37_REFRESH_BUSY_BIT_OFFSET                               5
#define OPREFSTAT1_RANK38_REFRESH_BUSY_MASK                            0x00000040
#define OPREFSTAT1_RANK38_REFRESH_BUSY_BIT_OFFSET                               6
#define OPREFSTAT1_RANK39_REFRESH_BUSY_MASK                            0x00000080
#define OPREFSTAT1_RANK39_REFRESH_BUSY_BIT_OFFSET                               7
#define OPREFSTAT1_RANK40_REFRESH_BUSY_MASK                            0x00000100
#define OPREFSTAT1_RANK40_REFRESH_BUSY_BIT_OFFSET                               8
#define OPREFSTAT1_RANK41_REFRESH_BUSY_MASK                            0x00000200
#define OPREFSTAT1_RANK41_REFRESH_BUSY_BIT_OFFSET                               9
#define OPREFSTAT1_RANK42_REFRESH_BUSY_MASK                            0x00000400
#define OPREFSTAT1_RANK42_REFRESH_BUSY_BIT_OFFSET                              10
#define OPREFSTAT1_RANK43_REFRESH_BUSY_MASK                            0x00000800
#define OPREFSTAT1_RANK43_REFRESH_BUSY_BIT_OFFSET                              11
#define OPREFSTAT1_RANK44_REFRESH_BUSY_MASK                            0x00001000
#define OPREFSTAT1_RANK44_REFRESH_BUSY_BIT_OFFSET                              12
#define OPREFSTAT1_RANK45_REFRESH_BUSY_MASK                            0x00002000
#define OPREFSTAT1_RANK45_REFRESH_BUSY_BIT_OFFSET                              13
#define OPREFSTAT1_RANK46_REFRESH_BUSY_MASK                            0x00004000
#define OPREFSTAT1_RANK46_REFRESH_BUSY_BIT_OFFSET                              14
#define OPREFSTAT1_RANK47_REFRESH_BUSY_MASK                            0x00008000
#define OPREFSTAT1_RANK47_REFRESH_BUSY_BIT_OFFSET                              15
#define OPREFSTAT1_RANK48_REFRESH_BUSY_MASK                            0x00010000
#define OPREFSTAT1_RANK48_REFRESH_BUSY_BIT_OFFSET                              16
#define OPREFSTAT1_RANK49_REFRESH_BUSY_MASK                            0x00020000
#define OPREFSTAT1_RANK49_REFRESH_BUSY_BIT_OFFSET                              17
#define OPREFSTAT1_RANK50_REFRESH_BUSY_MASK                            0x00040000
#define OPREFSTAT1_RANK50_REFRESH_BUSY_BIT_OFFSET                              18
#define OPREFSTAT1_RANK51_REFRESH_BUSY_MASK                            0x00080000
#define OPREFSTAT1_RANK51_REFRESH_BUSY_BIT_OFFSET                              19
#define OPREFSTAT1_RANK52_REFRESH_BUSY_MASK                            0x00100000
#define OPREFSTAT1_RANK52_REFRESH_BUSY_BIT_OFFSET                              20
#define OPREFSTAT1_RANK53_REFRESH_BUSY_MASK                            0x00200000
#define OPREFSTAT1_RANK53_REFRESH_BUSY_BIT_OFFSET                              21
#define OPREFSTAT1_RANK54_REFRESH_BUSY_MASK                            0x00400000
#define OPREFSTAT1_RANK54_REFRESH_BUSY_BIT_OFFSET                              22
#define OPREFSTAT1_RANK55_REFRESH_BUSY_MASK                            0x00800000
#define OPREFSTAT1_RANK55_REFRESH_BUSY_BIT_OFFSET                              23
#define OPREFSTAT1_RANK56_REFRESH_BUSY_MASK                            0x01000000
#define OPREFSTAT1_RANK56_REFRESH_BUSY_BIT_OFFSET                              24
#define OPREFSTAT1_RANK57_REFRESH_BUSY_MASK                            0x02000000
#define OPREFSTAT1_RANK57_REFRESH_BUSY_BIT_OFFSET                              25
#define OPREFSTAT1_RANK58_REFRESH_BUSY_MASK                            0x04000000
#define OPREFSTAT1_RANK58_REFRESH_BUSY_BIT_OFFSET                              26
#define OPREFSTAT1_RANK59_REFRESH_BUSY_MASK                            0x08000000
#define OPREFSTAT1_RANK59_REFRESH_BUSY_BIT_OFFSET                              27
#define OPREFSTAT1_RANK60_REFRESH_BUSY_MASK                            0x10000000
#define OPREFSTAT1_RANK60_REFRESH_BUSY_BIT_OFFSET                              28
#define OPREFSTAT1_RANK61_REFRESH_BUSY_MASK                            0x20000000
#define OPREFSTAT1_RANK61_REFRESH_BUSY_BIT_OFFSET                              29
#define OPREFSTAT1_RANK62_REFRESH_BUSY_MASK                            0x40000000
#define OPREFSTAT1_RANK62_REFRESH_BUSY_BIT_OFFSET                              30
#define OPREFSTAT1_RANK63_REFRESH_BUSY_MASK                            0x80000000
#define OPREFSTAT1_RANK63_REFRESH_BUSY_BIT_OFFSET                              31

#define OPDPSTAT0                                                      0x00000BA8
#define OPDPSTAT0_DFI_CMD_DELAY_MASK                                   0xFFFFFFFF
#define OPDPSTAT0_DFI_CMD_DELAY_BIT_OFFSET                                      0

#define OPCTRLWRCAM                                                    0x00000BAC
#define OPCTRLWRCAM_DBG_W_Q_DEPTH_EXTEND_MASK                          0xFFFFFFFF
#define OPCTRLWRCAM_DBG_W_Q_DEPTH_EXTEND_BIT_OFFSET                             0

#define OPCTRLRDCAM                                                    0x00000BB0
#define OPCTRLRDCAM_DBG_HPR_Q_DEPTH_EXTEND_MASK                        0x0000FFFF
#define OPCTRLRDCAM_DBG_HPR_Q_DEPTH_EXTEND_BIT_OFFSET                           0
#define OPCTRLRDCAM_DBG_LPR_Q_DEPTH_EXTEND_MASK                        0xFFFF0000
#define OPCTRLRDCAM_DBG_LPR_Q_DEPTH_EXTEND_BIT_OFFSET                          16

#define SCHED6                                                         0x00000BB4
#define SCHED6_LPR_NUM_ENTRIES_EXTEND_MASK                             0xFFFFFFFF
#define SCHED6_LPR_NUM_ENTRIES_EXTEND_BIT_OFFSET                                0

#define SCHED7                                                         0x00000BB8
#define SCHED7_WRCAM_LOWTHRESH_EXTEND_MASK                             0x000003FF
#define SCHED7_WRCAM_LOWTHRESH_EXTEND_BIT_OFFSET                                0
#define SCHED7_WRCAM_HIGHTHRESH_EXTEND_MASK                            0x000FFC00
#define SCHED7_WRCAM_HIGHTHRESH_EXTEND_BIT_OFFSET                              10
#define SCHED7_WR_PGHIT_NUM_THRESH_EXTEND_MASK                         0xFFF00000
#define SCHED7_WR_PGHIT_NUM_THRESH_EXTEND_BIT_OFFSET                           20

#define SWCTL                                                          0x00000C80
#define SWCTL_SW_DONE_MASK                                             0x00000001
#define SWCTL_SW_DONE_BIT_OFFSET                                                0

#define SWSTAT                                                         0x00000C84
#define SWSTAT_SW_DONE_ACK_MASK                                        0x00000001
#define SWSTAT_SW_DONE_ACK_BIT_OFFSET                                           0

#define DIMMCTL                                                        0x00000C88
#define DIMMCTL_DIMM_STAGGER_CS_EN_MASK                                0x00000001
#define DIMMCTL_DIMM_STAGGER_CS_EN_BIT_OFFSET                                   0
#define DIMMCTL_DIMM_ADDR_MIRR_EN_MASK                                 0x00000002
#define DIMMCTL_DIMM_ADDR_MIRR_EN_BIT_OFFSET                                    1
#define DIMMCTL_DIMM_OUTPUT_INV_EN_MASK                                0x00000004
#define DIMMCTL_DIMM_OUTPUT_INV_EN_BIT_OFFSET                                   2
#define DIMMCTL_MRS_A17_EN_MASK                                        0x00000008
#define DIMMCTL_MRS_A17_EN_BIT_OFFSET                                           3
#define DIMMCTL_MRS_BG1_EN_MASK                                        0x00000010
#define DIMMCTL_MRS_BG1_EN_BIT_OFFSET                                           4
#define DIMMCTL_DIMM_DIS_BG_MIRRORING_MASK                             0x00000020
#define DIMMCTL_DIMM_DIS_BG_MIRRORING_BIT_OFFSET                                5
#define DIMMCTL_LRDIMM_BCOM_CMD_PROT_MASK                              0x00000040
#define DIMMCTL_LRDIMM_BCOM_CMD_PROT_BIT_OFFSET                                 6
#define DIMMCTL_RCD_NUM_MASK                                           0x00000300
#define DIMMCTL_RCD_NUM_BIT_OFFSET                                              8
#define DIMMCTL_DIMM_TYPE_MASK                                         0x00000C00
#define DIMMCTL_DIMM_TYPE_BIT_OFFSET                                           10
#define DIMMCTL_RCD_WEAK_DRIVE_MASK                                    0x00001000
#define DIMMCTL_RCD_WEAK_DRIVE_BIT_OFFSET                                      12
#define DIMMCTL_RCD_A_OUTPUT_DISABLED_MASK                             0x00002000
#define DIMMCTL_RCD_A_OUTPUT_DISABLED_BIT_OFFSET                               13
#define DIMMCTL_RCD_B_OUTPUT_DISABLED_MASK                             0x00004000
#define DIMMCTL_RCD_B_OUTPUT_DISABLED_BIT_OFFSET                               14
#define DIMMCTL_DIMM_SELFREF_CLOCK_STOP_MODE_MASK                      0x00008000
#define DIMMCTL_DIMM_SELFREF_CLOCK_STOP_MODE_BIT_OFFSET                        15

#define CHCTL                                                          0x00000C8C
#define CHCTL_DUAL_CHANNEL_EN_MASK                                     0x00000001
#define CHCTL_DUAL_CHANNEL_EN_BIT_OFFSET                                        0

#define RANKCTL                                                        0x00000C90
#define RANKCTL_MAX_RANK_RD_MASK                                       0x0000000F
#define RANKCTL_MAX_RANK_RD_BIT_OFFSET                                          0
#define RANKCTL_MAX_RANK_WR_MASK                                       0x0000F000
#define RANKCTL_MAX_RANK_WR_BIT_OFFSET                                         12
#define RANKCTL_MAX_LOGICAL_RANK_RD_MASK                               0x000F0000
#define RANKCTL_MAX_LOGICAL_RANK_RD_BIT_OFFSET                                 16
#define RANKCTL_MAX_LOGICAL_RANK_WR_MASK                               0x00F00000
#define RANKCTL_MAX_LOGICAL_RANK_WR_BIT_OFFSET                                 20

#define DBICTL                                                         0x00000C94
#define DBICTL_DM_EN_MASK                                              0x00000001
#define DBICTL_DM_EN_BIT_OFFSET                                                 0
#define DBICTL_WR_DBI_EN_MASK                                          0x00000002
#define DBICTL_WR_DBI_EN_BIT_OFFSET                                             1
#define DBICTL_RD_DBI_EN_MASK                                          0x00000004
#define DBICTL_RD_DBI_EN_BIT_OFFSET                                             2

#define DYNBSMSTAT                                                     0x00000C98
#define DYNBSMSTAT_NUM_ALLOC_BSM_MASK                                  0x000000FF
#define DYNBSMSTAT_NUM_ALLOC_BSM_BIT_OFFSET                                     0
#define DYNBSMSTAT_MAX_NUM_ALLOC_BSM_MASK                              0x0000FF00
#define DYNBSMSTAT_MAX_NUM_ALLOC_BSM_BIT_OFFSET                                 8
#define DYNBSMSTAT_MAX_NUM_UNALLOC_ENTRIES_MASK                        0xFFFF0000
#define DYNBSMSTAT_MAX_NUM_UNALLOC_ENTRIES_BIT_OFFSET                          16

#define ODTMAP                                                         0x00000C9C
#define ODTMAP_RANK0_WR_ODT_MASK                                       0x0000000F
#define ODTMAP_RANK0_WR_ODT_BIT_OFFSET                                          0
#define ODTMAP_RANK0_RD_ODT_MASK                                       0x000000F0
#define ODTMAP_RANK0_RD_ODT_BIT_OFFSET                                          4
#define ODTMAP_RANK1_WR_ODT_MASK                                       0x00000F00
#define ODTMAP_RANK1_WR_ODT_BIT_OFFSET                                          8
#define ODTMAP_RANK1_RD_ODT_MASK                                       0x0000F000
#define ODTMAP_RANK1_RD_ODT_BIT_OFFSET                                         12
#define ODTMAP_RANK2_WR_ODT_MASK                                       0x000F0000
#define ODTMAP_RANK2_WR_ODT_BIT_OFFSET                                         16
#define ODTMAP_RANK2_RD_ODT_MASK                                       0x00F00000
#define ODTMAP_RANK2_RD_ODT_BIT_OFFSET                                         20
#define ODTMAP_RANK3_WR_ODT_MASK                                       0x0F000000
#define ODTMAP_RANK3_WR_ODT_BIT_OFFSET                                         24
#define ODTMAP_RANK3_RD_ODT_MASK                                       0xF0000000
#define ODTMAP_RANK3_RD_ODT_BIT_OFFSET                                         28

#define DATACTL0                                                       0x00000CA0
#define DATACTL0_RD_DATA_COPY_EN_MASK                                  0x00010000
#define DATACTL0_RD_DATA_COPY_EN_BIT_OFFSET                                    16
#define DATACTL0_WR_DATA_COPY_EN_MASK                                  0x00020000
#define DATACTL0_WR_DATA_COPY_EN_BIT_OFFSET                                    17
#define DATACTL0_WR_DATA_X_EN_MASK                                     0x00040000
#define DATACTL0_WR_DATA_X_EN_BIT_OFFSET                                       18

#define SWCTLSTATIC                                                    0x00000CA4
#define SWCTLSTATIC_SW_STATIC_UNLOCK_MASK                              0x00000001
#define SWCTLSTATIC_SW_STATIC_UNLOCK_BIT_OFFSET                                 0

#define CGCTL                                                          0x00000CB0
#define CGCTL_FORCE_CLK_TE_EN_MASK                                     0x00000001
#define CGCTL_FORCE_CLK_TE_EN_BIT_OFFSET                                        0
#define CGCTL_FORCE_CLK_ARB_EN_MASK                                    0x00000010
#define CGCTL_FORCE_CLK_ARB_EN_BIT_OFFSET                                       4

#define INITTMG0                                                       0x00000D00
#define INITTMG0_PRE_CKE_X1024_MASK                                    0x00001FFF
#define INITTMG0_PRE_CKE_X1024_BIT_OFFSET                                       0
#define INITTMG0_POST_CKE_X1024_MASK                                   0x03FF0000
#define INITTMG0_POST_CKE_X1024_BIT_OFFSET                                     16
#define INITTMG0_SKIP_DRAM_INIT_MASK                                   0xC0000000
#define INITTMG0_SKIP_DRAM_INIT_BIT_OFFSET                                     30

#define INITTMG2                                                       0x00000D08
#define INITTMG2_DEV_ZQINIT_X32_MASK                                   0x00FF0000
#define INITTMG2_DEV_ZQINIT_X32_BIT_OFFSET                                     16

#define DS_DBG_CTRL0                                                   0x00000D80
#define DS_DBG_CTRL0_DBG_BSM_SEL_CTRL_MASK                             0x0000FFFF
#define DS_DBG_CTRL0_DBG_BSM_SEL_CTRL_BIT_OFFSET                                0
#define DS_DBG_CTRL0_DBG_LRSM_SEL_CTRL_MASK                            0xFFFF0000
#define DS_DBG_CTRL0_DBG_LRSM_SEL_CTRL_BIT_OFFSET                              16

#define DS_DBG_STAT0                                                   0x00000D84
#define DS_DBG_STAT0_DBG_STAT0_MASK                                    0xFFFFFFFF
#define DS_DBG_STAT0_DBG_STAT0_BIT_OFFSET                                       0

#define DS_DBG_STAT1                                                   0x00000D88
#define DS_DBG_STAT1_DBG_STAT1_MASK                                    0xFFFFFFFF
#define DS_DBG_STAT1_DBG_STAT1_BIT_OFFSET                                       0

#define DS_DBG_STAT2                                                   0x00000D8C
#define DS_DBG_STAT2_DBG_STAT2_MASK                                    0xFFFFFFFF
#define DS_DBG_STAT2_DBG_STAT2_BIT_OFFSET                                       0

#define DS_DBG_STAT3                                                   0x00000D90
#define DS_DBG_STAT3_DBG_STAT3_MASK                                    0xFFFFFFFF
#define DS_DBG_STAT3_DBG_STAT3_BIT_OFFSET                                       0

#define DU_DBG_STAT0                                                   0x00000D94
#define DU_DBG_STAT0_DU_CUR_BLK_UCODE_MASK                             0x0000FFFF
#define DU_DBG_STAT0_DU_CUR_BLK_UCODE_BIT_OFFSET                                0
#define DU_DBG_STAT0_DU_CUR_BLK_ADDR_MASK                              0x00FF0000
#define DU_DBG_STAT0_DU_CUR_BLK_ADDR_BIT_OFFSET                                16
#define DU_DBG_STAT0_DU_CUR_BLK_INDEX_MASK                             0x1F000000
#define DU_DBG_STAT0_DU_CUR_BLK_INDEX_BIT_OFFSET                               24
#define DU_DBG_STAT0_DU_CUR_BLK_SET_MASK                               0x20000000
#define DU_DBG_STAT0_DU_CUR_BLK_SET_BIT_OFFSET                                 29

#define DU_DBG_STAT1                                                   0x00000D98
#define DU_DBG_STAT1_DU_MAIN_FSM_STATE_MASK                            0x00000007
#define DU_DBG_STAT1_DU_MAIN_FSM_STATE_BIT_OFFSET                               0
#define DU_DBG_STAT1_DU_SCEU_FSM_STATE_MASK                            0x00000070
#define DU_DBG_STAT1_DU_SCEU_FSM_STATE_BIT_OFFSET                               4
#define DU_DBG_STAT1_DU_MCEU_FSM_STATE_MASK                            0x00000700
#define DU_DBG_STAT1_DU_MCEU_FSM_STATE_BIT_OFFSET                               8

#define LC_DBG_STAT0                                                   0x00000D9C
#define LC_DBG_STAT0_DBG_RANK_CTRL_MC_ADDR_0_MASK                      0x000000FF
#define LC_DBG_STAT0_DBG_RANK_CTRL_MC_ADDR_0_BIT_OFFSET                         0
#define LC_DBG_STAT0_DBG_RANK_CTRL_MC_CODE_0_MASK                      0xFFFF0000
#define LC_DBG_STAT0_DBG_RANK_CTRL_MC_CODE_0_BIT_OFFSET                        16

#define LC_DBG_STAT1                                                   0x00000DA0
#define LC_DBG_STAT1_DBG_RANK_CTRL_MC_ADDR_1_MASK                      0x000000FF
#define LC_DBG_STAT1_DBG_RANK_CTRL_MC_ADDR_1_BIT_OFFSET                         0
#define LC_DBG_STAT1_DBG_RANK_CTRL_MC_CODE_1_MASK                      0xFFFF0000
#define LC_DBG_STAT1_DBG_RANK_CTRL_MC_CODE_1_BIT_OFFSET                        16

#define LC_DBG_STAT2                                                   0x00000DA4
#define LC_DBG_STAT2_DBG_RANK_CTRL_MC_ADDR_2_MASK                      0x000000FF
#define LC_DBG_STAT2_DBG_RANK_CTRL_MC_ADDR_2_BIT_OFFSET                         0
#define LC_DBG_STAT2_DBG_RANK_CTRL_MC_CODE_2_MASK                      0xFFFF0000
#define LC_DBG_STAT2_DBG_RANK_CTRL_MC_CODE_2_BIT_OFFSET                        16

#define LC_DBG_STAT3                                                   0x00000DA8
#define LC_DBG_STAT3_DBG_RANK_CTRL_MC_ADDR_3_MASK                      0x000000FF
#define LC_DBG_STAT3_DBG_RANK_CTRL_MC_ADDR_3_BIT_OFFSET                         0
#define LC_DBG_STAT3_DBG_RANK_CTRL_MC_CODE_3_MASK                      0xFFFF0000
#define LC_DBG_STAT3_DBG_RANK_CTRL_MC_CODE_3_BIT_OFFSET                        16

#define LC_DBG_STAT4                                                   0x00000DAC
#define LC_DBG_STAT4_DBG_SCEU_CTRL_STATE_SCEU_0_MASK                   0x00000007
#define LC_DBG_STAT4_DBG_SCEU_CTRL_STATE_SCEU_0_BIT_OFFSET                      0
#define LC_DBG_STAT4_DBG_MCEU_CTRL_STATE_MCEU_0_MASK                   0x00000070
#define LC_DBG_STAT4_DBG_MCEU_CTRL_STATE_MCEU_0_BIT_OFFSET                      4
#define LC_DBG_STAT4_DBG_RANK_CTRL_STATE_RSM_0_MASK                    0x00000F00
#define LC_DBG_STAT4_DBG_RANK_CTRL_STATE_RSM_0_BIT_OFFSET                       8
#define LC_DBG_STAT4_DBG_SCEU_CTRL_STATE_SCEU_1_MASK                   0x00070000
#define LC_DBG_STAT4_DBG_SCEU_CTRL_STATE_SCEU_1_BIT_OFFSET                     16
#define LC_DBG_STAT4_DBG_MCEU_CTRL_STATE_MCEU_1_MASK                   0x00700000
#define LC_DBG_STAT4_DBG_MCEU_CTRL_STATE_MCEU_1_BIT_OFFSET                     20
#define LC_DBG_STAT4_DBG_RANK_CTRL_STATE_RSM_1_MASK                    0x0F000000
#define LC_DBG_STAT4_DBG_RANK_CTRL_STATE_RSM_1_BIT_OFFSET                      24

#define LC_DBG_STAT5                                                   0x00000DB0
#define LC_DBG_STAT5_DBG_SCEU_CTRL_STATE_SCEU_2_MASK                   0x00000007
#define LC_DBG_STAT5_DBG_SCEU_CTRL_STATE_SCEU_2_BIT_OFFSET                      0
#define LC_DBG_STAT5_DBG_MCEU_CTRL_STATE_MCEU_2_MASK                   0x00000070
#define LC_DBG_STAT5_DBG_MCEU_CTRL_STATE_MCEU_2_BIT_OFFSET                      4
#define LC_DBG_STAT5_DBG_RANK_CTRL_STATE_RSM_2_MASK                    0x00000F00
#define LC_DBG_STAT5_DBG_RANK_CTRL_STATE_RSM_2_BIT_OFFSET                       8
#define LC_DBG_STAT5_DBG_SCEU_CTRL_STATE_SCEU_3_MASK                   0x00070000
#define LC_DBG_STAT5_DBG_SCEU_CTRL_STATE_SCEU_3_BIT_OFFSET                     16
#define LC_DBG_STAT5_DBG_MCEU_CTRL_STATE_MCEU_3_MASK                   0x00700000
#define LC_DBG_STAT5_DBG_MCEU_CTRL_STATE_MCEU_3_BIT_OFFSET                     20
#define LC_DBG_STAT5_DBG_RANK_CTRL_STATE_RSM_3_MASK                    0x0F000000
#define LC_DBG_STAT5_DBG_RANK_CTRL_STATE_RSM_3_BIT_OFFSET                      24

#define LC_DBG_STAT6                                                   0x00000DB4
#define LC_DBG_STAT6_DBG_DFI_LP_STATE_DSM_MASK                         0x00000007
#define LC_DBG_STAT6_DBG_DFI_LP_STATE_DSM_BIT_OFFSET                            0
#define LC_DBG_STAT6_DBG_DFI_LP_DATA_ACK_MASK                          0x00000010
#define LC_DBG_STAT6_DBG_DFI_LP_DATA_ACK_BIT_OFFSET                             4
#define LC_DBG_STAT6_DBG_DFI_LP_CTRL_ACK_MASK                          0x00000020
#define LC_DBG_STAT6_DBG_DFI_LP_CTRL_ACK_BIT_OFFSET                             5
#define LC_DBG_STAT6_DBG_HW_LP_STATE_HSM_MASK                          0x00000700
#define LC_DBG_STAT6_DBG_HW_LP_STATE_HSM_BIT_OFFSET                             8

#define CAPAR_DBG_STAT0                                                0x00000DB8
#define CAPAR_DBG_STAT0_DBG_CAPAR_RETRY_MC_ADDR_MASK                   0x0000003F
#define CAPAR_DBG_STAT0_DBG_CAPAR_RETRY_MC_ADDR_BIT_OFFSET                      0
#define CAPAR_DBG_STAT0_DBG_CAPAR_RETRY_MC_CODE_MASK                   0xFFFF0000
#define CAPAR_DBG_STAT0_DBG_CAPAR_RETRY_MC_CODE_BIT_OFFSET                     16

#define CAPAR_DBG_STAT1                                                0x00000DBC
#define CAPAR_DBG_STAT1_DBG_CAPAR_RETRY_STATE_SCEU_MASK                0x00000007
#define CAPAR_DBG_STAT1_DBG_CAPAR_RETRY_STATE_SCEU_BIT_OFFSET                   0
#define CAPAR_DBG_STAT1_DBG_CAPAR_RETRY_STATE_MCEU_MASK                0x00000070
#define CAPAR_DBG_STAT1_DBG_CAPAR_RETRY_STATE_MCEU_BIT_OFFSET                   4
#define CAPAR_DBG_STAT1_DBG_CAPAR_RETRY_STATE_CSM_MASK                 0x00000300
#define CAPAR_DBG_STAT1_DBG_CAPAR_RETRY_STATE_CSM_BIT_OFFSET                    8

#define CAPAR_CMDFIFO_CTRL                                             0x00000DC0
#define CAPAR_CMDFIFO_CTRL_CMDFIFO_RD_ADDR_MASK                        0x00FF0000
#define CAPAR_CMDFIFO_CTRL_CMDFIFO_RD_ADDR_BIT_OFFSET                          16

#define CAPAR_CMDFIFO_STAT                                             0x00000DC4
#define CAPAR_CMDFIFO_STAT_CMDFIFO_RD_DATA_MASK                        0x00001FFF
#define CAPAR_CMDFIFO_STAT_CMDFIFO_RD_DATA_BIT_OFFSET                           0

#define CAPAR_CMDFIFO_LOG                                              0x00000DC8
#define CAPAR_CMDFIFO_LOG_CMDFIFO_WINDOW_CMD_NUM_MASK                  0x000001FF
#define CAPAR_CMDFIFO_LOG_CMDFIFO_WINDOW_CMD_NUM_BIT_OFFSET                     0
#define CAPAR_CMDFIFO_LOG_CMDFIFO_RECORDED_CMD_NUM_MASK                0x01FF0000
#define CAPAR_CMDFIFO_LOG_CMDFIFO_RECORDED_CMD_NUM_BIT_OFFSET                  16
#define CAPAR_CMDFIFO_LOG_CMDFIFO_OVERFLOW_MASK                        0x80000000
#define CAPAR_CMDFIFO_LOG_CMDFIFO_OVERFLOW_BIT_OFFSET                          31

#define ECCERRCNTCTL                                                   0x00000E80
#define ECCERRCNTCTL_ECC_CORR_THRESHOLD_MASK                           0x0000FFFF
#define ECCERRCNTCTL_ECC_CORR_THRESHOLD_BIT_OFFSET                              0
#define ECCERRCNTCTL_ECC_CORR_ERR_CNT_CLR_RANK0_MASK                   0x00010000
#define ECCERRCNTCTL_ECC_CORR_ERR_CNT_CLR_RANK0_BIT_OFFSET                     16
#define ECCERRCNTCTL_ECC_CORR_ERR_CNT_CLR_RANK1_MASK                   0x00020000
#define ECCERRCNTCTL_ECC_CORR_ERR_CNT_CLR_RANK1_BIT_OFFSET                     17
#define ECCERRCNTCTL_ECC_CORR_ERR_CNT_CLR_RANK2_MASK                   0x00040000
#define ECCERRCNTCTL_ECC_CORR_ERR_CNT_CLR_RANK2_BIT_OFFSET                     18
#define ECCERRCNTCTL_ECC_CORR_ERR_CNT_CLR_RANK3_MASK                   0x00080000
#define ECCERRCNTCTL_ECC_CORR_ERR_CNT_CLR_RANK3_BIT_OFFSET                     19
#define ECCERRCNTCTL_ECC_UNCORR_ERR_LOG_MODE_MASK                      0x00300000
#define ECCERRCNTCTL_ECC_UNCORR_ERR_LOG_MODE_BIT_OFFSET                        20
#define ECCERRCNTCTL_ECC_CORR_ERR_LOG_MODE_MASK                        0x0FC00000
#define ECCERRCNTCTL_ECC_CORR_ERR_LOG_MODE_BIT_OFFSET                          22
#define ECCERRCNTCTL_ECC_CORR_ERR_PER_RANK_INTR_EN_MASK                0xF0000000
#define ECCERRCNTCTL_ECC_CORR_ERR_PER_RANK_INTR_EN_BIT_OFFSET                  28

#define ECCERRCNTSTAT                                                  0x00000E84
#define ECCERRCNTSTAT_ECC_CORR_ERR_PER_RANK_INTR_MASK                  0xFFFFFFFF
#define ECCERRCNTSTAT_ECC_CORR_ERR_PER_RANK_INTR_BIT_OFFSET                     0

#define ECCERRCNT0                                                     0x00000E88
#define ECCERRCNT0_ECC_CORR_ERR_CNT_RANK0_MASK                         0x0000FFFF
#define ECCERRCNT0_ECC_CORR_ERR_CNT_RANK0_BIT_OFFSET                            0
#define ECCERRCNT0_ECC_CORR_ERR_CNT_RANK1_MASK                         0xFFFF0000
#define ECCERRCNT0_ECC_CORR_ERR_CNT_RANK1_BIT_OFFSET                           16

#define ECCERRCNT1                                                     0x00000E8C
#define ECCERRCNT1_ECC_CORR_ERR_CNT_RANK2_MASK                         0x0000FFFF
#define ECCERRCNT1_ECC_CORR_ERR_CNT_RANK2_BIT_OFFSET                            0
#define ECCERRCNT1_ECC_CORR_ERR_CNT_RANK3_MASK                         0xFFFF0000
#define ECCERRCNT1_ECC_CORR_ERR_CNT_RANK3_BIT_OFFSET                           16

#define PPT2CTRL0                                                      0x00000F00
#define PPT2CTRL0_PPT2_BURST_NUM_MASK                                  0x000003FF
#define PPT2CTRL0_PPT2_BURST_NUM_BIT_OFFSET                                     0
#define PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0_MASK                           0x0003F000
#define PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0_BIT_OFFSET                             12
#define PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1_MASK                           0x00FC0000
#define PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1_BIT_OFFSET                             18
#define PPT2CTRL0_PPT2_BURST_MASK                                      0x10000000
#define PPT2CTRL0_PPT2_BURST_BIT_OFFSET                                        28
#define PPT2CTRL0_PPT2_WAIT_REF_MASK                                   0x80000000
#define PPT2CTRL0_PPT2_WAIT_REF_BIT_OFFSET                                     31

#define PPT2STAT0                                                      0x00000F10
#define PPT2STAT0_PPT2_STATE_MASK                                      0x0000000F
#define PPT2STAT0_PPT2_STATE_BIT_OFFSET                                         0
#define PPT2STAT0_PPT2_BURST_BUSY_MASK                                 0x10000000
#define PPT2STAT0_PPT2_BURST_BUSY_BIT_OFFSET                                   28

#define DDRCTL_IMECFG0                                                 0x00000F80
#define DDRCTL_IMECFG0_IME_EN_MASK                                     0x00000001
#define DDRCTL_IMECFG0_IME_EN_BIT_OFFSET                                        0

#define DDRCTL_IMESTAT0                                                0x00000F90
#define DDRCTL_IMESTAT0_IME_FORCE_DISABLED_MASK                        0x00000001
#define DDRCTL_IMESTAT0_IME_FORCE_DISABLED_BIT_OFFSET                           0

#define DDRCTL_VER_NUMBER                                              0x00000FF8
#define DDRCTL_VER_NUMBER_VER_NUMBER_MASK                              0xFFFFFFFF
#define DDRCTL_VER_NUMBER_VER_NUMBER_BIT_OFFSET                                 0

#define DDRCTL_VER_TYPE                                                0x00000FFC
#define DDRCTL_VER_TYPE_VER_TYPE_MASK                                  0xFFFFFFFF
#define DDRCTL_VER_TYPE_VER_TYPE_BIT_OFFSET                                     0

#define REG_GROUP_DDRC_CH1                                             0x00011000

#define REG_GROUP_ADDR_MAP0                                            0x00030000

#define ADDRMAP0                                                       0x00000000
#define ADDRMAP0_ADDRMAP_DCH_BIT0_MASK                                 0x0000003F
#define ADDRMAP0_ADDRMAP_DCH_BIT0_BIT_OFFSET                                    0

#define ADDRMAP1                                                       0x00000004
#define ADDRMAP1_ADDRMAP_CS_BIT0_MASK                                  0x0000003F
#define ADDRMAP1_ADDRMAP_CS_BIT0_BIT_OFFSET                                     0
#define ADDRMAP1_ADDRMAP_CS_BIT1_MASK                                  0x00003F00
#define ADDRMAP1_ADDRMAP_CS_BIT1_BIT_OFFSET                                     8
#define ADDRMAP1_ADDRMAP_CS_BIT2_MASK                                  0x003F0000
#define ADDRMAP1_ADDRMAP_CS_BIT2_BIT_OFFSET                                    16
#define ADDRMAP1_ADDRMAP_CS_BIT3_MASK                                  0x3F000000
#define ADDRMAP1_ADDRMAP_CS_BIT3_BIT_OFFSET                                    24

#define ADDRMAP2                                                       0x00000008
#define ADDRMAP2_ADDRMAP_CID_B0_MASK                                   0x0000003F
#define ADDRMAP2_ADDRMAP_CID_B0_BIT_OFFSET                                      0
#define ADDRMAP2_ADDRMAP_CID_B1_MASK                                   0x00003F00
#define ADDRMAP2_ADDRMAP_CID_B1_BIT_OFFSET                                      8
#define ADDRMAP2_ADDRMAP_CID_B2_MASK                                   0x003F0000
#define ADDRMAP2_ADDRMAP_CID_B2_BIT_OFFSET                                     16
#define ADDRMAP2_ADDRMAP_CID_B3_MASK                                   0x3F000000
#define ADDRMAP2_ADDRMAP_CID_B3_BIT_OFFSET                                     24

#define ADDRMAP3                                                       0x0000000C
#define ADDRMAP3_ADDRMAP_BANK_B0_MASK                                  0x0000003F
#define ADDRMAP3_ADDRMAP_BANK_B0_BIT_OFFSET                                     0
#define ADDRMAP3_ADDRMAP_BANK_B1_MASK                                  0x00003F00
#define ADDRMAP3_ADDRMAP_BANK_B1_BIT_OFFSET                                     8
#define ADDRMAP3_ADDRMAP_BANK_B2_MASK                                  0x003F0000
#define ADDRMAP3_ADDRMAP_BANK_B2_BIT_OFFSET                                    16

#define ADDRMAP4                                                       0x00000010
#define ADDRMAP4_ADDRMAP_BG_B0_MASK                                    0x0000003F
#define ADDRMAP4_ADDRMAP_BG_B0_BIT_OFFSET                                       0
#define ADDRMAP4_ADDRMAP_BG_B1_MASK                                    0x00003F00
#define ADDRMAP4_ADDRMAP_BG_B1_BIT_OFFSET                                       8
#define ADDRMAP4_ADDRMAP_BG_B2_MASK                                    0x003F0000
#define ADDRMAP4_ADDRMAP_BG_B2_BIT_OFFSET                                      16

#define ADDRMAP5                                                       0x00000014
#define ADDRMAP5_ADDRMAP_COL_B7_MASK                                   0x0000001F
#define ADDRMAP5_ADDRMAP_COL_B7_BIT_OFFSET                                      0
#define ADDRMAP5_ADDRMAP_COL_B8_MASK                                   0x00001F00
#define ADDRMAP5_ADDRMAP_COL_B8_BIT_OFFSET                                      8
#define ADDRMAP5_ADDRMAP_COL_B9_MASK                                   0x001F0000
#define ADDRMAP5_ADDRMAP_COL_B9_BIT_OFFSET                                     16
#define ADDRMAP5_ADDRMAP_COL_B10_MASK                                  0x1F000000
#define ADDRMAP5_ADDRMAP_COL_B10_BIT_OFFSET                                    24

#define ADDRMAP6                                                       0x00000018
#define ADDRMAP6_ADDRMAP_COL_B3_MASK                                   0x0000000F
#define ADDRMAP6_ADDRMAP_COL_B3_BIT_OFFSET                                      0
#define ADDRMAP6_ADDRMAP_COL_B4_MASK                                   0x00000F00
#define ADDRMAP6_ADDRMAP_COL_B4_BIT_OFFSET                                      8
#define ADDRMAP6_ADDRMAP_COL_B5_MASK                                   0x000F0000
#define ADDRMAP6_ADDRMAP_COL_B5_BIT_OFFSET                                     16
#define ADDRMAP6_ADDRMAP_COL_B6_MASK                                   0x0F000000
#define ADDRMAP6_ADDRMAP_COL_B6_BIT_OFFSET                                     24

#define ADDRMAP7                                                       0x0000001C
#define ADDRMAP7_ADDRMAP_ROW_B14_MASK                                  0x0000001F
#define ADDRMAP7_ADDRMAP_ROW_B14_BIT_OFFSET                                     0
#define ADDRMAP7_ADDRMAP_ROW_B15_MASK                                  0x00001F00
#define ADDRMAP7_ADDRMAP_ROW_B15_BIT_OFFSET                                     8
#define ADDRMAP7_ADDRMAP_ROW_B16_MASK                                  0x001F0000
#define ADDRMAP7_ADDRMAP_ROW_B16_BIT_OFFSET                                    16
#define ADDRMAP7_ADDRMAP_ROW_B17_MASK                                  0x1F000000
#define ADDRMAP7_ADDRMAP_ROW_B17_BIT_OFFSET                                    24

#define ADDRMAP8                                                       0x00000020
#define ADDRMAP8_ADDRMAP_ROW_B10_MASK                                  0x0000001F
#define ADDRMAP8_ADDRMAP_ROW_B10_BIT_OFFSET                                     0
#define ADDRMAP8_ADDRMAP_ROW_B11_MASK                                  0x00001F00
#define ADDRMAP8_ADDRMAP_ROW_B11_BIT_OFFSET                                     8
#define ADDRMAP8_ADDRMAP_ROW_B12_MASK                                  0x001F0000
#define ADDRMAP8_ADDRMAP_ROW_B12_BIT_OFFSET                                    16
#define ADDRMAP8_ADDRMAP_ROW_B13_MASK                                  0x1F000000
#define ADDRMAP8_ADDRMAP_ROW_B13_BIT_OFFSET                                    24

#define ADDRMAP9                                                       0x00000024
#define ADDRMAP9_ADDRMAP_ROW_B6_MASK                                   0x0000001F
#define ADDRMAP9_ADDRMAP_ROW_B6_BIT_OFFSET                                      0
#define ADDRMAP9_ADDRMAP_ROW_B7_MASK                                   0x00001F00
#define ADDRMAP9_ADDRMAP_ROW_B7_BIT_OFFSET                                      8
#define ADDRMAP9_ADDRMAP_ROW_B8_MASK                                   0x001F0000
#define ADDRMAP9_ADDRMAP_ROW_B8_BIT_OFFSET                                     16
#define ADDRMAP9_ADDRMAP_ROW_B9_MASK                                   0x1F000000
#define ADDRMAP9_ADDRMAP_ROW_B9_BIT_OFFSET                                     24

#define ADDRMAP10                                                      0x00000028
#define ADDRMAP10_ADDRMAP_ROW_B2_MASK                                  0x0000001F
#define ADDRMAP10_ADDRMAP_ROW_B2_BIT_OFFSET                                     0
#define ADDRMAP10_ADDRMAP_ROW_B3_MASK                                  0x00001F00
#define ADDRMAP10_ADDRMAP_ROW_B3_BIT_OFFSET                                     8
#define ADDRMAP10_ADDRMAP_ROW_B4_MASK                                  0x001F0000
#define ADDRMAP10_ADDRMAP_ROW_B4_BIT_OFFSET                                    16
#define ADDRMAP10_ADDRMAP_ROW_B5_MASK                                  0x1F000000
#define ADDRMAP10_ADDRMAP_ROW_B5_BIT_OFFSET                                    24

#define ADDRMAP11                                                      0x0000002C
#define ADDRMAP11_ADDRMAP_ROW_B0_MASK                                  0x0000001F
#define ADDRMAP11_ADDRMAP_ROW_B0_BIT_OFFSET                                     0
#define ADDRMAP11_ADDRMAP_ROW_B1_MASK                                  0x00001F00
#define ADDRMAP11_ADDRMAP_ROW_B1_BIT_OFFSET                                     8

#define ADDRMAP12                                                      0x00000030
#define ADDRMAP12_NONBINARY_DEVICE_DENSITY_MASK                        0x00000007
#define ADDRMAP12_NONBINARY_DEVICE_DENSITY_BIT_OFFSET                           0
#define ADDRMAP12_BANK_HASH_EN_MASK                                    0x00000010
#define ADDRMAP12_BANK_HASH_EN_BIT_OFFSET                                       4
#define ADDRMAP12_LPDDR_MIXED_PKG_EN_MASK                              0x00000100
#define ADDRMAP12_LPDDR_MIXED_PKG_EN_BIT_OFFSET                                 8
#define ADDRMAP12_LPDDR_MIXED_PKG_X16_SIZE_MASK                        0x000F0000
#define ADDRMAP12_LPDDR_MIXED_PKG_X16_SIZE_BIT_OFFSET                          16

#define ADDRMAPLUTCFG                                                  0x00000080
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BYPASS_MASK                          0x00000001
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BYPASS_BIT_OFFSET                             0
#define ADDRMAPLUTCFG_ADDRMAP_USE_LUT_CS_MASK                          0x00000002
#define ADDRMAPLUTCFG_ADDRMAP_USE_LUT_CS_BIT_OFFSET                             1
#define ADDRMAPLUTCFG_ADDRMAP_LUT_RANK_TYPE_MASK                       0x000000F0
#define ADDRMAPLUTCFG_ADDRMAP_LUT_RANK_TYPE_BIT_OFFSET                          4
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BIT0_MASK                            0x00000700
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BIT0_BIT_OFFSET                               8
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BIT0_VALID_MASK                      0x00002000
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BIT0_VALID_BIT_OFFSET                        13
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BIT1_MASK                            0x0001C000
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BIT1_BIT_OFFSET                              14
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BIT1_VALID_MASK                      0x00080000
#define ADDRMAPLUTCFG_ADDRMAP_LUT_BIT1_VALID_BIT_OFFSET                        19
#define ADDRMAPLUTCFG_ADDRMAP_LUT_MAX_ACTIVE_HIF_ADDR_OFFSET_MASK      0x00F00000
#define ADDRMAPLUTCFG_ADDRMAP_LUT_MAX_ACTIVE_HIF_ADDR_OFFSET_BIT_OFFSET         20

#define ADDRMAPLUTCTRL                                                 0x00000084
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_WDATA0_MASK                         0x000000FF
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_WDATA0_BIT_OFFSET                            0
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_WDATA1_MASK                         0x0000FF00
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_WDATA1_BIT_OFFSET                            8
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_ADDR_MASK                           0x3F000000
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_ADDR_BIT_OFFSET                             24
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_RW_TYPE_MASK                        0x40000000
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_RW_TYPE_BIT_OFFSET                          30
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_RW_START_MASK                       0x80000000
#define ADDRMAPLUTCTRL_ADDRMAP_LUT_RW_START_BIT_OFFSET                         31

#define ADDRMAPLUTRDATA                                                0x00000088
#define ADDRMAPLUTRDATA_ADDRMAP_LUT_RDATA0_MASK                        0x000000FF
#define ADDRMAPLUTRDATA_ADDRMAP_LUT_RDATA0_BIT_OFFSET                           0
#define ADDRMAPLUTRDATA_ADDRMAP_LUT_RDATA1_MASK                        0x0000FF00
#define ADDRMAPLUTRDATA_ADDRMAP_LUT_RDATA1_BIT_OFFSET                           8
#define ADDRMAPLUTRDATA_ADDRMAP_RANK_VALID_MASK                        0xFFFF0000
#define ADDRMAPLUTRDATA_ADDRMAP_RANK_VALID_BIT_OFFSET                          16

#define REG_GROUP_ADDR_MAP1                                            0x00031000

#define REG_GROUP_ARB_PORT0                                            0x00020000

#define PCCFG                                                          0x00000000
#define PCCFG_GO2CRITICAL_EN_MASK                                      0x00000001
#define PCCFG_GO2CRITICAL_EN_BIT_OFFSET                                         0
#define PCCFG_PAGEMATCH_LIMIT_MASK                                     0x00000010
#define PCCFG_PAGEMATCH_LIMIT_BIT_OFFSET                                        4
#define PCCFG_DCH_DENSITY_RATIO_MASK                                   0x00003000
#define PCCFG_DCH_DENSITY_RATIO_BIT_OFFSET                                     12

#define PCFGR                                                          0x00000004
#define PCFGR_RD_PORT_PRIORITY_MASK                                    0x000003FF
#define PCFGR_RD_PORT_PRIORITY_BIT_OFFSET                                       0
#define PCFGR_READ_REORDER_BYPASS_EN_MASK                              0x00000800
#define PCFGR_READ_REORDER_BYPASS_EN_BIT_OFFSET                                11
#define PCFGR_RD_PORT_AGING_EN_MASK                                    0x00001000
#define PCFGR_RD_PORT_AGING_EN_BIT_OFFSET                                      12
#define PCFGR_RD_PORT_URGENT_EN_MASK                                   0x00002000
#define PCFGR_RD_PORT_URGENT_EN_BIT_OFFSET                                     13
#define PCFGR_RD_PORT_PAGEMATCH_EN_MASK                                0x00004000
#define PCFGR_RD_PORT_PAGEMATCH_EN_BIT_OFFSET                                  14
#define PCFGR_RDWR_ORDERED_EN_MASK                                     0x00010000
#define PCFGR_RDWR_ORDERED_EN_BIT_OFFSET                                       16
#define PCFGR_RRB_LOCK_THRESHOLD_MASK                                  0x00F00000
#define PCFGR_RRB_LOCK_THRESHOLD_BIT_OFFSET                                    20

#define PCFGW                                                          0x00000008
#define PCFGW_WR_PORT_PRIORITY_MASK                                    0x000003FF
#define PCFGW_WR_PORT_PRIORITY_BIT_OFFSET                                       0
#define PCFGW_WR_PORT_AGING_EN_MASK                                    0x00001000
#define PCFGW_WR_PORT_AGING_EN_BIT_OFFSET                                      12
#define PCFGW_WR_PORT_URGENT_EN_MASK                                   0x00002000
#define PCFGW_WR_PORT_URGENT_EN_BIT_OFFSET                                     13
#define PCFGW_WR_PORT_PAGEMATCH_EN_MASK                                0x00004000
#define PCFGW_WR_PORT_PAGEMATCH_EN_BIT_OFFSET                                  14
#define PCFGW_SNF_MODE_MASK                                            0x00008000
#define PCFGW_SNF_MODE_BIT_OFFSET                                              15

#define PCFGIDMASKCH0                                                  0x00000010
#define PCFGIDMASKCH0_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH0_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH0                                                 0x00000014
#define PCFGIDVALUECH0_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH0_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH1                                                  0x00000018
#define PCFGIDMASKCH1_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH1_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH1                                                 0x0000001C
#define PCFGIDVALUECH1_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH1_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH2                                                  0x00000020
#define PCFGIDMASKCH2_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH2_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH2                                                 0x00000024
#define PCFGIDVALUECH2_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH2_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH3                                                  0x00000028
#define PCFGIDMASKCH3_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH3_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH3                                                 0x0000002C
#define PCFGIDVALUECH3_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH3_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH4                                                  0x00000030
#define PCFGIDMASKCH4_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH4_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH4                                                 0x00000034
#define PCFGIDVALUECH4_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH4_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH5                                                  0x00000038
#define PCFGIDMASKCH5_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH5_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH5                                                 0x0000003C
#define PCFGIDVALUECH5_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH5_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH6                                                  0x00000040
#define PCFGIDMASKCH6_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH6_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH6                                                 0x00000044
#define PCFGIDVALUECH6_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH6_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH7                                                  0x00000048
#define PCFGIDMASKCH7_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH7_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH7                                                 0x0000004C
#define PCFGIDVALUECH7_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH7_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH8                                                  0x00000050
#define PCFGIDMASKCH8_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH8_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH8                                                 0x00000054
#define PCFGIDVALUECH8_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH8_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH9                                                  0x00000058
#define PCFGIDMASKCH9_ID_MASK_MASK                                     0xFFFFFFFF
#define PCFGIDMASKCH9_ID_MASK_BIT_OFFSET                                        0

#define PCFGIDVALUECH9                                                 0x0000005C
#define PCFGIDVALUECH9_ID_VALUE_MASK                                   0xFFFFFFFF
#define PCFGIDVALUECH9_ID_VALUE_BIT_OFFSET                                      0

#define PCFGIDMASKCH10                                                 0x00000060
#define PCFGIDMASKCH10_ID_MASK_MASK                                    0xFFFFFFFF
#define PCFGIDMASKCH10_ID_MASK_BIT_OFFSET                                       0

#define PCFGIDVALUECH10                                                0x00000064
#define PCFGIDVALUECH10_ID_VALUE_MASK                                  0xFFFFFFFF
#define PCFGIDVALUECH10_ID_VALUE_BIT_OFFSET                                     0

#define PCFGIDMASKCH11                                                 0x00000068
#define PCFGIDMASKCH11_ID_MASK_MASK                                    0xFFFFFFFF
#define PCFGIDMASKCH11_ID_MASK_BIT_OFFSET                                       0

#define PCFGIDVALUECH11                                                0x0000006C
#define PCFGIDVALUECH11_ID_VALUE_MASK                                  0xFFFFFFFF
#define PCFGIDVALUECH11_ID_VALUE_BIT_OFFSET                                     0

#define PCFGIDMASKCH12                                                 0x00000070
#define PCFGIDMASKCH12_ID_MASK_MASK                                    0xFFFFFFFF
#define PCFGIDMASKCH12_ID_MASK_BIT_OFFSET                                       0

#define PCFGIDVALUECH12                                                0x00000074
#define PCFGIDVALUECH12_ID_VALUE_MASK                                  0xFFFFFFFF
#define PCFGIDVALUECH12_ID_VALUE_BIT_OFFSET                                     0

#define PCFGIDMASKCH13                                                 0x00000078
#define PCFGIDMASKCH13_ID_MASK_MASK                                    0xFFFFFFFF
#define PCFGIDMASKCH13_ID_MASK_BIT_OFFSET                                       0

#define PCFGIDVALUECH13                                                0x0000007C
#define PCFGIDVALUECH13_ID_VALUE_MASK                                  0xFFFFFFFF
#define PCFGIDVALUECH13_ID_VALUE_BIT_OFFSET                                     0

#define PCFGIDMASKCH14                                                 0x00000080
#define PCFGIDMASKCH14_ID_MASK_MASK                                    0xFFFFFFFF
#define PCFGIDMASKCH14_ID_MASK_BIT_OFFSET                                       0

#define PCFGIDVALUECH14                                                0x00000084
#define PCFGIDVALUECH14_ID_VALUE_MASK                                  0xFFFFFFFF
#define PCFGIDVALUECH14_ID_VALUE_BIT_OFFSET                                     0

#define PCFGIDMASKCH15                                                 0x00000088
#define PCFGIDMASKCH15_ID_MASK_MASK                                    0xFFFFFFFF
#define PCFGIDMASKCH15_ID_MASK_BIT_OFFSET                                       0

#define PCFGIDVALUECH15                                                0x0000008C
#define PCFGIDVALUECH15_ID_VALUE_MASK                                  0xFFFFFFFF
#define PCFGIDVALUECH15_ID_VALUE_BIT_OFFSET                                     0

#define PCTRL                                                          0x00000090
#define PCTRL_PORT_EN_MASK                                             0x00000001
#define PCTRL_PORT_EN_BIT_OFFSET                                                0

#define PCFGQOS0                                                       0x00000094
#define PCFGQOS0_RQOS_MAP_LEVEL1_MASK                                  0x000000FF
#define PCFGQOS0_RQOS_MAP_LEVEL1_BIT_OFFSET                                     0
#define PCFGQOS0_RQOS_MAP_LEVEL2_MASK                                  0x0000FF00
#define PCFGQOS0_RQOS_MAP_LEVEL2_BIT_OFFSET                                     8
#define PCFGQOS0_RQOS_MAP_REGION0_MASK                                 0x000F0000
#define PCFGQOS0_RQOS_MAP_REGION0_BIT_OFFSET                                   16
#define PCFGQOS0_RQOS_MAP_REGION1_MASK                                 0x00F00000
#define PCFGQOS0_RQOS_MAP_REGION1_BIT_OFFSET                                   20
#define PCFGQOS0_RQOS_MAP_REGION2_MASK                                 0xFF000000
#define PCFGQOS0_RQOS_MAP_REGION2_BIT_OFFSET                                   24

#define PCFGQOS1                                                       0x00000098
#define PCFGQOS1_RQOS_MAP_TIMEOUTB_MASK                                0x0000FFFF
#define PCFGQOS1_RQOS_MAP_TIMEOUTB_BIT_OFFSET                                   0
#define PCFGQOS1_RQOS_MAP_TIMEOUTR_MASK                                0xFFFF0000
#define PCFGQOS1_RQOS_MAP_TIMEOUTR_BIT_OFFSET                                  16

#define PCFGWQOS0                                                      0x0000009C
#define PCFGWQOS0_WQOS_MAP_LEVEL1_MASK                                 0x000000FF
#define PCFGWQOS0_WQOS_MAP_LEVEL1_BIT_OFFSET                                    0
#define PCFGWQOS0_WQOS_MAP_LEVEL2_MASK                                 0x0000FF00
#define PCFGWQOS0_WQOS_MAP_LEVEL2_BIT_OFFSET                                    8
#define PCFGWQOS0_WQOS_MAP_REGION0_MASK                                0x000F0000
#define PCFGWQOS0_WQOS_MAP_REGION0_BIT_OFFSET                                  16
#define PCFGWQOS0_WQOS_MAP_REGION1_MASK                                0x00F00000
#define PCFGWQOS0_WQOS_MAP_REGION1_BIT_OFFSET                                  20
#define PCFGWQOS0_WQOS_MAP_REGION2_MASK                                0xFF000000
#define PCFGWQOS0_WQOS_MAP_REGION2_BIT_OFFSET                                  24

#define PCFGWQOS1                                                      0x000000A0
#define PCFGWQOS1_WQOS_MAP_TIMEOUT1_MASK                               0x0000FFFF
#define PCFGWQOS1_WQOS_MAP_TIMEOUT1_BIT_OFFSET                                  0
#define PCFGWQOS1_WQOS_MAP_TIMEOUT2_MASK                               0xFFFF0000
#define PCFGWQOS1_WQOS_MAP_TIMEOUT2_BIT_OFFSET                                 16

#define SARBASE0                                                       0x000000C0
#define SARBASE0_BASE_ADDR_MASK                                        0xFFFFFFFF
#define SARBASE0_BASE_ADDR_BIT_OFFSET                                           0

#define SARSIZE0                                                       0x000000C4
#define SARSIZE0_NBLOCKS_MASK                                          0xFFFFFFFF
#define SARSIZE0_NBLOCKS_BIT_OFFSET                                             0

#define SARBASE1                                                       0x000000C8
#define SARBASE1_BASE_ADDR_MASK                                        0xFFFFFFFF
#define SARBASE1_BASE_ADDR_BIT_OFFSET                                           0

#define SARSIZE1                                                       0x000000CC
#define SARSIZE1_NBLOCKS_MASK                                          0xFFFFFFFF
#define SARSIZE1_NBLOCKS_BIT_OFFSET                                             0

#define SARBASE2                                                       0x000000D0
#define SARBASE2_BASE_ADDR_MASK                                        0xFFFFFFFF
#define SARBASE2_BASE_ADDR_BIT_OFFSET                                           0

#define SARSIZE2                                                       0x000000D4
#define SARSIZE2_NBLOCKS_MASK                                          0xFFFFFFFF
#define SARSIZE2_NBLOCKS_BIT_OFFSET                                             0

#define SARBASE3                                                       0x000000D8
#define SARBASE3_BASE_ADDR_MASK                                        0xFFFFFFFF
#define SARBASE3_BASE_ADDR_BIT_OFFSET                                           0

#define SARSIZE3                                                       0x000000DC
#define SARSIZE3_NBLOCKS_MASK                                          0xFFFFFFFF
#define SARSIZE3_NBLOCKS_BIT_OFFSET                                             0

#define SBRCTL                                                         0x000000E0
#define SBRCTL_SCRUB_EN_MASK                                           0x00000001
#define SBRCTL_SCRUB_EN_BIT_OFFSET                                              0
#define SBRCTL_SCRUB_DURING_LOWPOWER_MASK                              0x00000002
#define SBRCTL_SCRUB_DURING_LOWPOWER_BIT_OFFSET                                 1
#define SBRCTL_SCRUB_EN_DCH1_MASK                                      0x00000008
#define SBRCTL_SCRUB_EN_DCH1_BIT_OFFSET                                         3
#define SBRCTL_SCRUB_BURST_LENGTH_NM_MASK                              0x00000070
#define SBRCTL_SCRUB_BURST_LENGTH_NM_BIT_OFFSET                                 4
#define SBRCTL_SCRUB_INTERVAL_MASK                                     0x00FFFF00
#define SBRCTL_SCRUB_INTERVAL_BIT_OFFSET                                        8
#define SBRCTL_SCRUB_CMD_TYPE_MASK                                     0x03000000
#define SBRCTL_SCRUB_CMD_TYPE_BIT_OFFSET                                       24
#define SBRCTL_SBR_CORRECTION_MODE_MASK                                0x0C000000
#define SBRCTL_SBR_CORRECTION_MODE_BIT_OFFSET                                  26
#define SBRCTL_SCRUB_BURST_LENGTH_LP_MASK                              0x70000000
#define SBRCTL_SCRUB_BURST_LENGTH_LP_BIT_OFFSET                                28
#define SBRCTL_SCRUB_UE_MASK                                           0x80000000
#define SBRCTL_SCRUB_UE_BIT_OFFSET                                             31

#define SBRSTAT                                                        0x000000E4
#define SBRSTAT_SCRUB_BUSY_MASK                                        0x00000001
#define SBRSTAT_SCRUB_BUSY_BIT_OFFSET                                           0
#define SBRSTAT_SCRUB_DONE_MASK                                        0x00000002
#define SBRSTAT_SCRUB_DONE_BIT_OFFSET                                           1
#define SBRSTAT_SCRUB_DROP_CNT_MASK                                    0x000001F0
#define SBRSTAT_SCRUB_DROP_CNT_BIT_OFFSET                                       4
#define SBRSTAT_SCRUB_BUSY_DCH1_MASK                                   0x00010000
#define SBRSTAT_SCRUB_BUSY_DCH1_BIT_OFFSET                                     16
#define SBRSTAT_SCRUB_DONE_DCH1_MASK                                   0x00020000
#define SBRSTAT_SCRUB_DONE_DCH1_BIT_OFFSET                                     17
#define SBRSTAT_SCRUB_DROP_CNT_DCH1_MASK                               0x01F00000
#define SBRSTAT_SCRUB_DROP_CNT_DCH1_BIT_OFFSET                                 20

#define SBRWDATA0                                                      0x000000E8
#define SBRWDATA0_SCRUB_PATTERN0_MASK                                  0xFFFFFFFF
#define SBRWDATA0_SCRUB_PATTERN0_BIT_OFFSET                                     0

#define SBRWDATA1                                                      0x000000EC
#define SBRWDATA1_SCRUB_PATTERN1_MASK                                  0xFFFFFFFF
#define SBRWDATA1_SCRUB_PATTERN1_BIT_OFFSET                                     0

#define SBRSTART0                                                      0x000000F0
#define SBRSTART0_SBR_ADDRESS_START_MASK_0_MASK                        0xFFFFFFFF
#define SBRSTART0_SBR_ADDRESS_START_MASK_0_BIT_OFFSET                           0

#define SBRSTART1                                                      0x000000F4
#define SBRSTART1_SBR_ADDRESS_START_MASK_1_MASK                        0xFFFFFFFF
#define SBRSTART1_SBR_ADDRESS_START_MASK_1_BIT_OFFSET                           0

#define SBRRANGE0                                                      0x000000F8
#define SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0_MASK                        0xFFFFFFFF
#define SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0_BIT_OFFSET                           0

#define SBRRANGE1                                                      0x000000FC
#define SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1_MASK                        0xFFFFFFFF
#define SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1_BIT_OFFSET                           0

#define SBRSTART0DCH1                                                  0x00000100
#define SBRSTART0DCH1_SBR_ADDRESS_START_MASK_DCH1_0_MASK               0xFFFFFFFF
#define SBRSTART0DCH1_SBR_ADDRESS_START_MASK_DCH1_0_BIT_OFFSET                  0

#define SBRSTART1DCH1                                                  0x00000104
#define SBRSTART1DCH1_SBR_ADDRESS_START_MASK_DCH1_1_MASK               0xFFFFFFFF
#define SBRSTART1DCH1_SBR_ADDRESS_START_MASK_DCH1_1_BIT_OFFSET                  0

#define SBRRANGE0DCH1                                                  0x00000108
#define SBRRANGE0DCH1_SBR_ADDRESS_RANGE_MASK_DCH1_0_MASK               0xFFFFFFFF
#define SBRRANGE0DCH1_SBR_ADDRESS_RANGE_MASK_DCH1_0_BIT_OFFSET                  0

#define SBRRANGE1DCH1                                                  0x0000010C
#define SBRRANGE1DCH1_SBR_ADDRESS_RANGE_MASK_DCH1_1_MASK               0xFFFFFFFF
#define SBRRANGE1DCH1_SBR_ADDRESS_RANGE_MASK_DCH1_1_BIT_OFFSET                  0

#define PDCH                                                           0x00000110
#define PDCH_PORT_DATA_CHANNEL_0_MASK                                  0x00000001
#define PDCH_PORT_DATA_CHANNEL_0_BIT_OFFSET                                     0
#define PDCH_PORT_DATA_CHANNEL_1_MASK                                  0x00000002
#define PDCH_PORT_DATA_CHANNEL_1_BIT_OFFSET                                     1
#define PDCH_PORT_DATA_CHANNEL_2_MASK                                  0x00000004
#define PDCH_PORT_DATA_CHANNEL_2_BIT_OFFSET                                     2
#define PDCH_PORT_DATA_CHANNEL_3_MASK                                  0x00000008
#define PDCH_PORT_DATA_CHANNEL_3_BIT_OFFSET                                     3
#define PDCH_PORT_DATA_CHANNEL_4_MASK                                  0x00000010
#define PDCH_PORT_DATA_CHANNEL_4_BIT_OFFSET                                     4
#define PDCH_PORT_DATA_CHANNEL_5_MASK                                  0x00000020
#define PDCH_PORT_DATA_CHANNEL_5_BIT_OFFSET                                     5
#define PDCH_PORT_DATA_CHANNEL_6_MASK                                  0x00000040
#define PDCH_PORT_DATA_CHANNEL_6_BIT_OFFSET                                     6
#define PDCH_PORT_DATA_CHANNEL_7_MASK                                  0x00000080
#define PDCH_PORT_DATA_CHANNEL_7_BIT_OFFSET                                     7
#define PDCH_PORT_DATA_CHANNEL_8_MASK                                  0x00000100
#define PDCH_PORT_DATA_CHANNEL_8_BIT_OFFSET                                     8
#define PDCH_PORT_DATA_CHANNEL_9_MASK                                  0x00000200
#define PDCH_PORT_DATA_CHANNEL_9_BIT_OFFSET                                     9
#define PDCH_PORT_DATA_CHANNEL_10_MASK                                 0x00000400
#define PDCH_PORT_DATA_CHANNEL_10_BIT_OFFSET                                   10
#define PDCH_PORT_DATA_CHANNEL_11_MASK                                 0x00000800
#define PDCH_PORT_DATA_CHANNEL_11_BIT_OFFSET                                   11
#define PDCH_PORT_DATA_CHANNEL_12_MASK                                 0x00001000
#define PDCH_PORT_DATA_CHANNEL_12_BIT_OFFSET                                   12
#define PDCH_PORT_DATA_CHANNEL_13_MASK                                 0x00002000
#define PDCH_PORT_DATA_CHANNEL_13_BIT_OFFSET                                   13
#define PDCH_PORT_DATA_CHANNEL_14_MASK                                 0x00004000
#define PDCH_PORT_DATA_CHANNEL_14_BIT_OFFSET                                   14
#define PDCH_PORT_DATA_CHANNEL_15_MASK                                 0x00008000
#define PDCH_PORT_DATA_CHANNEL_15_BIT_OFFSET                                   15

#define PSTAT                                                          0x00000114
#define PSTAT_RD_PORT_BUSY_0_MASK                                      0x00000001
#define PSTAT_RD_PORT_BUSY_0_BIT_OFFSET                                         0
#define PSTAT_RD_PORT_BUSY_1_MASK                                      0x00000002
#define PSTAT_RD_PORT_BUSY_1_BIT_OFFSET                                         1
#define PSTAT_RD_PORT_BUSY_2_MASK                                      0x00000004
#define PSTAT_RD_PORT_BUSY_2_BIT_OFFSET                                         2
#define PSTAT_RD_PORT_BUSY_3_MASK                                      0x00000008
#define PSTAT_RD_PORT_BUSY_3_BIT_OFFSET                                         3
#define PSTAT_RD_PORT_BUSY_4_MASK                                      0x00000010
#define PSTAT_RD_PORT_BUSY_4_BIT_OFFSET                                         4
#define PSTAT_RD_PORT_BUSY_5_MASK                                      0x00000020
#define PSTAT_RD_PORT_BUSY_5_BIT_OFFSET                                         5
#define PSTAT_RD_PORT_BUSY_6_MASK                                      0x00000040
#define PSTAT_RD_PORT_BUSY_6_BIT_OFFSET                                         6
#define PSTAT_RD_PORT_BUSY_7_MASK                                      0x00000080
#define PSTAT_RD_PORT_BUSY_7_BIT_OFFSET                                         7
#define PSTAT_RD_PORT_BUSY_8_MASK                                      0x00000100
#define PSTAT_RD_PORT_BUSY_8_BIT_OFFSET                                         8
#define PSTAT_RD_PORT_BUSY_9_MASK                                      0x00000200
#define PSTAT_RD_PORT_BUSY_9_BIT_OFFSET                                         9
#define PSTAT_RD_PORT_BUSY_10_MASK                                     0x00000400
#define PSTAT_RD_PORT_BUSY_10_BIT_OFFSET                                       10
#define PSTAT_RD_PORT_BUSY_11_MASK                                     0x00000800
#define PSTAT_RD_PORT_BUSY_11_BIT_OFFSET                                       11
#define PSTAT_RD_PORT_BUSY_12_MASK                                     0x00001000
#define PSTAT_RD_PORT_BUSY_12_BIT_OFFSET                                       12
#define PSTAT_RD_PORT_BUSY_13_MASK                                     0x00002000
#define PSTAT_RD_PORT_BUSY_13_BIT_OFFSET                                       13
#define PSTAT_RD_PORT_BUSY_14_MASK                                     0x00004000
#define PSTAT_RD_PORT_BUSY_14_BIT_OFFSET                                       14
#define PSTAT_RD_PORT_BUSY_15_MASK                                     0x00008000
#define PSTAT_RD_PORT_BUSY_15_BIT_OFFSET                                       15
#define PSTAT_WR_PORT_BUSY_0_MASK                                      0x00010000
#define PSTAT_WR_PORT_BUSY_0_BIT_OFFSET                                        16
#define PSTAT_WR_PORT_BUSY_1_MASK                                      0x00020000
#define PSTAT_WR_PORT_BUSY_1_BIT_OFFSET                                        17
#define PSTAT_WR_PORT_BUSY_2_MASK                                      0x00040000
#define PSTAT_WR_PORT_BUSY_2_BIT_OFFSET                                        18
#define PSTAT_WR_PORT_BUSY_3_MASK                                      0x00080000
#define PSTAT_WR_PORT_BUSY_3_BIT_OFFSET                                        19
#define PSTAT_WR_PORT_BUSY_4_MASK                                      0x00100000
#define PSTAT_WR_PORT_BUSY_4_BIT_OFFSET                                        20
#define PSTAT_WR_PORT_BUSY_5_MASK                                      0x00200000
#define PSTAT_WR_PORT_BUSY_5_BIT_OFFSET                                        21
#define PSTAT_WR_PORT_BUSY_6_MASK                                      0x00400000
#define PSTAT_WR_PORT_BUSY_6_BIT_OFFSET                                        22
#define PSTAT_WR_PORT_BUSY_7_MASK                                      0x00800000
#define PSTAT_WR_PORT_BUSY_7_BIT_OFFSET                                        23
#define PSTAT_WR_PORT_BUSY_8_MASK                                      0x01000000
#define PSTAT_WR_PORT_BUSY_8_BIT_OFFSET                                        24
#define PSTAT_WR_PORT_BUSY_9_MASK                                      0x02000000
#define PSTAT_WR_PORT_BUSY_9_BIT_OFFSET                                        25
#define PSTAT_WR_PORT_BUSY_10_MASK                                     0x04000000
#define PSTAT_WR_PORT_BUSY_10_BIT_OFFSET                                       26
#define PSTAT_WR_PORT_BUSY_11_MASK                                     0x08000000
#define PSTAT_WR_PORT_BUSY_11_BIT_OFFSET                                       27
#define PSTAT_WR_PORT_BUSY_12_MASK                                     0x10000000
#define PSTAT_WR_PORT_BUSY_12_BIT_OFFSET                                       28
#define PSTAT_WR_PORT_BUSY_13_MASK                                     0x20000000
#define PSTAT_WR_PORT_BUSY_13_BIT_OFFSET                                       29
#define PSTAT_WR_PORT_BUSY_14_MASK                                     0x40000000
#define PSTAT_WR_PORT_BUSY_14_BIT_OFFSET                                       30
#define PSTAT_WR_PORT_BUSY_15_MASK                                     0x80000000
#define PSTAT_WR_PORT_BUSY_15_BIT_OFFSET                                       31

#define SBRLPCTL                                                       0x00000118
#define SBRLPCTL_PERRANK_DIS_SCRUB_MASK                                0x0000000F
#define SBRLPCTL_PERRANK_DIS_SCRUB_BIT_OFFSET                                   0
#define SBRLPCTL_SCRUB_RESTORE_MASK                                    0x00000010
#define SBRLPCTL_SCRUB_RESTORE_BIT_OFFSET                                       4
#define SBRLPCTL_PERRANK_DIS_SCRUB_DCH1_MASK                           0x00000F00
#define SBRLPCTL_PERRANK_DIS_SCRUB_DCH1_BIT_OFFSET                              8
#define SBRLPCTL_SCRUB_RESTORE_DCH1_MASK                               0x00001000
#define SBRLPCTL_SCRUB_RESTORE_DCH1_BIT_OFFSET                                 12

#define SBRADDRLOG0                                                    0x0000011C
#define SBRADDRLOG0_SCRUB_ADDR_LOG0_MASK                               0xFFFFFFFF
#define SBRADDRLOG0_SCRUB_ADDR_LOG0_BIT_OFFSET                                  0

#define SBRADDRLOG1                                                    0x00000120
#define SBRADDRLOG1_SCRUB_ADDR_LOG1_MASK                               0xFFFFFFFF
#define SBRADDRLOG1_SCRUB_ADDR_LOG1_BIT_OFFSET                                  0

#define SBRADDRRESTORE0                                                0x00000124
#define SBRADDRRESTORE0_SCRUB_RESTORE_ADDRESS0_MASK                    0xFFFFFFFF
#define SBRADDRRESTORE0_SCRUB_RESTORE_ADDRESS0_BIT_OFFSET                       0

#define SBRADDRRESTORE1                                                0x00000128
#define SBRADDRRESTORE1_SCRUB_RESTORE_ADDRESS1_MASK                    0xFFFFFFFF
#define SBRADDRRESTORE1_SCRUB_RESTORE_ADDRESS1_BIT_OFFSET                       0

#define SBRADDRLOG0DCH1                                                0x0000012C
#define SBRADDRLOG0DCH1_SCRUB_ADDR_LOG0_DCH1_MASK                      0xFFFFFFFF
#define SBRADDRLOG0DCH1_SCRUB_ADDR_LOG0_DCH1_BIT_OFFSET                         0

#define SBRADDRLOG1DCH1                                                0x00000130
#define SBRADDRLOG1DCH1_SCRUB_ADDR_LOG1_DCH1_MASK                      0xFFFFFFFF
#define SBRADDRLOG1DCH1_SCRUB_ADDR_LOG1_DCH1_BIT_OFFSET                         0

#define SBRADDRRESTORE0DCH1                                            0x00000134
#define SBRADDRRESTORE0DCH1_SCRUB_RESTORE_ADDRESS0_DCH1_MASK           0xFFFFFFFF
#define SBRADDRRESTORE0DCH1_SCRUB_RESTORE_ADDRESS0_DCH1_BIT_OFFSET              0

#define SBRADDRRESTORE1DCH1                                            0x00000138
#define SBRADDRRESTORE1DCH1_SCRUB_RESTORE_ADDRESS1_DCH1_MASK           0xFFFFFFFF
#define SBRADDRRESTORE1DCH1_SCRUB_RESTORE_ADDRESS1_DCH1_BIT_OFFSET              0

#define PCHBLCTRL                                                      0x00000900
#define PCHBLCTRL_TXSACTIVE_EN_MASK                                    0x00000001
#define PCHBLCTRL_TXSACTIVE_EN_BIT_OFFSET                                       0

#define PCHBTCTRL                                                      0x00000904
#define PCHBTCTRL_DIS_PREFETCH_MASK                                    0x00000001
#define PCHBTCTRL_DIS_PREFETCH_BIT_OFFSET                                       0
#define PCHBTCTRL_CRC_UE_RSP_SEL_MASK                                  0x00000006
#define PCHBTCTRL_CRC_UE_RSP_SEL_BIT_OFFSET                                     1
#define PCHBTCTRL_DBG_FORCE_PCRD_STEAL_MODE_MASK                       0x00000010
#define PCHBTCTRL_DBG_FORCE_PCRD_STEAL_MODE_BIT_OFFSET                          4
#define PCHBTCTRL_DBG_WDC_EN_MASK                                      0x00000020
#define PCHBTCTRL_DBG_WDC_EN_BIT_OFFSET                                         5
#define PCHBTCTRL_CBUSY_SELECT_MASK                                    0x00000040
#define PCHBTCTRL_CBUSY_SELECT_BIT_OFFSET                                       6
#define PCHBTCTRL_DBG_DIS_WRPTL_RMW_BE_EVAL_MASK                       0x00000080
#define PCHBTCTRL_DBG_DIS_WRPTL_RMW_BE_EVAL_BIT_OFFSET                          7

#define PCHBPRCTMR                                                     0x00000908
#define PCHBPRCTMR_PRC_EXP_CNT_MASK                                    0x000003FF
#define PCHBPRCTMR_PRC_EXP_CNT_BIT_OFFSET                                       0
#define PCHBPRCTMR_EXP_CNT_DIV_MASK                                    0x00030000
#define PCHBPRCTMR_EXP_CNT_DIV_BIT_OFFSET                                      16

#define PCHBPROTQCTL                                                   0x0000090C
#define PCHBPROTQCTL_RPQ_LPR_MIN_MASK                                  0x0000007F
#define PCHBPROTQCTL_RPQ_LPR_MIN_BIT_OFFSET                                     0
#define PCHBPROTQCTL_RPQ_HPR_MIN_MASK                                  0x00007F00
#define PCHBPROTQCTL_RPQ_HPR_MIN_BIT_OFFSET                                     8

#define PCHBRQOS0                                                      0x00000910
#define PCHBRQOS0_CHB_RQOS_MAP_LEVEL1_MASK                             0x000000FF
#define PCHBRQOS0_CHB_RQOS_MAP_LEVEL1_BIT_OFFSET                                0
#define PCHBRQOS0_CHB_RQOS_MAP_LEVEL2_MASK                             0x0000FF00
#define PCHBRQOS0_CHB_RQOS_MAP_LEVEL2_BIT_OFFSET                                8
#define PCHBRQOS0_CHB_RQOS_MAP_REGION0_MASK                            0x000F0000
#define PCHBRQOS0_CHB_RQOS_MAP_REGION0_BIT_OFFSET                              16
#define PCHBRQOS0_CHB_RQOS_MAP_REGION1_MASK                            0x00F00000
#define PCHBRQOS0_CHB_RQOS_MAP_REGION1_BIT_OFFSET                              20
#define PCHBRQOS0_CHB_RQOS_MAP_REGION2_MASK                            0xFF000000
#define PCHBRQOS0_CHB_RQOS_MAP_REGION2_BIT_OFFSET                              24

#define PCHBRQOS1                                                      0x00000914
#define PCHBRQOS1_VPR_UNCRD_TIMEOUT_MASK                               0x0000FFFF
#define PCHBRQOS1_VPR_UNCRD_TIMEOUT_BIT_OFFSET                                  0
#define PCHBRQOS1_VPR_CRD_TIMEOUT_MASK                                 0xFFFF0000
#define PCHBRQOS1_VPR_CRD_TIMEOUT_BIT_OFFSET                                   16

#define PCHBWQOS0                                                      0x00000918
#define PCHBWQOS0_CHB_WQOS_MAP_LEVEL1_MASK                             0x000000FF
#define PCHBWQOS0_CHB_WQOS_MAP_LEVEL1_BIT_OFFSET                                0
#define PCHBWQOS0_CHB_WQOS_MAP_LEVEL2_MASK                             0x0000FF00
#define PCHBWQOS0_CHB_WQOS_MAP_LEVEL2_BIT_OFFSET                                8
#define PCHBWQOS0_CHB_WQOS_MAP_REGION0_MASK                            0x000F0000
#define PCHBWQOS0_CHB_WQOS_MAP_REGION0_BIT_OFFSET                              16
#define PCHBWQOS0_CHB_WQOS_MAP_REGION1_MASK                            0x00F00000
#define PCHBWQOS0_CHB_WQOS_MAP_REGION1_BIT_OFFSET                              20
#define PCHBWQOS0_CHB_WQOS_MAP_REGION2_MASK                            0xFF000000
#define PCHBWQOS0_CHB_WQOS_MAP_REGION2_BIT_OFFSET                              24

#define PCHBWQOS1                                                      0x0000091C
#define PCHBWQOS1_VPW_UNCRD_TIMEOUT_MASK                               0x0000FFFF
#define PCHBWQOS1_VPW_UNCRD_TIMEOUT_BIT_OFFSET                                  0
#define PCHBWQOS1_VPW_CRD_TIMEOUT_MASK                                 0xFFFF0000
#define PCHBWQOS1_VPW_CRD_TIMEOUT_BIT_OFFSET                                   16

#define PCHBCBUSYH                                                     0x00000920
#define PCHBCBUSYH_CAM_BUSY_THRESHOLD_HPR_MASK                         0x000003FF
#define PCHBCBUSYH_CAM_BUSY_THRESHOLD_HPR_BIT_OFFSET                            0
#define PCHBCBUSYH_CAM_FREE_THRESHOLD_HPR_MASK                         0x000FFC00
#define PCHBCBUSYH_CAM_FREE_THRESHOLD_HPR_BIT_OFFSET                           10
#define PCHBCBUSYH_CAM_MIDDLE_THRESHOLD_HPR_MASK                       0xFFF00000
#define PCHBCBUSYH_CAM_MIDDLE_THRESHOLD_HPR_BIT_OFFSET                         20

#define PCHBCBUSYL                                                     0x00000924
#define PCHBCBUSYL_CAM_BUSY_THRESHOLD_LPR_MASK                         0x000003FF
#define PCHBCBUSYL_CAM_BUSY_THRESHOLD_LPR_BIT_OFFSET                            0
#define PCHBCBUSYL_CAM_FREE_THRESHOLD_LPR_MASK                         0x000FFC00
#define PCHBCBUSYL_CAM_FREE_THRESHOLD_LPR_BIT_OFFSET                           10
#define PCHBCBUSYL_CAM_MIDDLE_THRESHOLD_LPR_MASK                       0xFFF00000
#define PCHBCBUSYL_CAM_MIDDLE_THRESHOLD_LPR_BIT_OFFSET                         20

#define PCHBCBUSYW                                                     0x00000928
#define PCHBCBUSYW_CAM_BUSY_THRESHOLD_WR_MASK                          0x000003FF
#define PCHBCBUSYW_CAM_BUSY_THRESHOLD_WR_BIT_OFFSET                             0
#define PCHBCBUSYW_CAM_FREE_THRESHOLD_WR_MASK                          0x000FFC00
#define PCHBCBUSYW_CAM_FREE_THRESHOLD_WR_BIT_OFFSET                            10
#define PCHBCBUSYW_CAM_MIDDLE_THRESHOLD_WR_MASK                        0xFFF00000
#define PCHBCBUSYW_CAM_MIDDLE_THRESHOLD_WR_BIT_OFFSET                          20

#define PCHBLSTAT0                                                     0x00000980
#define PCHBLSTAT0_TXSACTIVE_STATUS_MASK                               0x00000001
#define PCHBLSTAT0_TXSACTIVE_STATUS_BIT_OFFSET                                  0
#define PCHBLSTAT0_RXSACTIVE_STATUS_MASK                               0x00000002
#define PCHBLSTAT0_RXSACTIVE_STATUS_BIT_OFFSET                                  1
#define PCHBLSTAT0_TX_REQ_MASK                                         0x00000004
#define PCHBLSTAT0_TX_REQ_BIT_OFFSET                                            2
#define PCHBLSTAT0_TX_ACK_MASK                                         0x00000008
#define PCHBLSTAT0_TX_ACK_BIT_OFFSET                                            3
#define PCHBLSTAT0_RX_REQ_MASK                                         0x00000010
#define PCHBLSTAT0_RX_REQ_BIT_OFFSET                                            4
#define PCHBLSTAT0_RX_ACK_MASK                                         0x00000020
#define PCHBLSTAT0_RX_ACK_BIT_OFFSET                                            5

#define PCHBRLSTAT                                                     0x00000990
#define PCHBRLSTAT_RETRY_LIST_EMPTY_MASK                               0x00000001
#define PCHBRLSTAT_RETRY_LIST_EMPTY_BIT_OFFSET                                  0
#define PCHBRLSTAT_RETRY_LIST_FULL_MASK                                0x00000002
#define PCHBRLSTAT_RETRY_LIST_FULL_BIT_OFFSET                                   1
#define PCHBRLSTAT_PEND_QOS_TYPE_MASK                                  0xFFFFFFFC
#define PCHBRLSTAT_PEND_QOS_TYPE_BIT_OFFSET                                     2

#define PCHBTZCFG                                                      0x00000A00
#define PCHBTZCFG_TZ_NO_REGIONS_MASK                                   0x00000007
#define PCHBTZCFG_TZ_NO_REGIONS_BIT_OFFSET                                      0
#define PCHBTZCFG_TZ_NO_SUBREGIONS_MASK                                0x00000070
#define PCHBTZCFG_TZ_NO_SUBREGIONS_BIT_OFFSET                                   4
#define PCHBTZCFG_TZ_CHB_ADDRESS_WIDTH_MASK                            0x00003F00
#define PCHBTZCFG_TZ_CHB_ADDRESS_WIDTH_BIT_OFFSET                               8

#define PCHBTZACT                                                      0x00000A04
#define PCHBTZACT_TZ_INT_ENABLE_MASK                                   0x00000001
#define PCHBTZACT_TZ_INT_ENABLE_BIT_OFFSET                                      0
#define PCHBTZACT_TZ_RESPERR_ENABLE_MASK                               0x00000002
#define PCHBTZACT_TZ_RESPERR_ENABLE_BIT_OFFSET                                  1

#define PCHBTZINTSTS                                                   0x00000A08
#define PCHBTZINTSTS_TZ_INT_MASK                                       0x00000001
#define PCHBTZINTSTS_TZ_INT_BIT_OFFSET                                          0
#define PCHBTZINTSTS_TZ_OVERRUN_MASK                                   0x00000002
#define PCHBTZINTSTS_TZ_OVERRUN_BIT_OFFSET                                      1

#define PCHBTZINTCLR                                                   0x00000A0C
#define PCHBTZINTCLR_TZ_INT_CLEAR_MASK                                 0x00000001
#define PCHBTZINTCLR_TZ_INT_CLEAR_BIT_OFFSET                                    0

#define PCHBTZLOGADDR0                                                 0x00000A10
#define PCHBTZLOGADDR0_TZ_LOG_ADDR_LOW_MASK                            0xFFFFFFFF
#define PCHBTZLOGADDR0_TZ_LOG_ADDR_LOW_BIT_OFFSET                               0

#define PCHBTZLOGADDR1                                                 0x00000A14
#define PCHBTZLOGADDR1_TZ_LOG_ADDR_HIGH_MASK                           0xFFFFFFFF
#define PCHBTZLOGADDR1_TZ_LOG_ADDR_HIGH_BIT_OFFSET                              0

#define PCHBTZLOGOP                                                    0x00000A18
#define PCHBTZLOGOP_TZ_LOG_NONSECURE_MASK                              0x00200000
#define PCHBTZLOGOP_TZ_LOG_NONSECURE_BIT_OFFSET                                21
#define PCHBTZLOGOP_TZ_LOG_OPCODE_MASK                                 0x7F000000
#define PCHBTZLOGOP_TZ_LOG_OPCODE_BIT_OFFSET                                   24

#define PCHBTZLOGID0                                                   0x00000A1C
#define PCHBTZLOGID0_TZ_LOG_TXNID_MASK                                 0x00000FFF
#define PCHBTZLOGID0_TZ_LOG_TXNID_BIT_OFFSET                                    0
#define PCHBTZLOGID0_TZ_LOG_RETURNTXID_MASK                            0x007FF000
#define PCHBTZLOGID0_TZ_LOG_RETURNTXID_BIT_OFFSET                              12

#define PCHBTZLOGID1                                                   0x00000A20
#define PCHBTZLOGID1_TZ_LOG_SRCID_MASK                                 0x000007FF
#define PCHBTZLOGID1_TZ_LOG_SRCID_BIT_OFFSET                                    0
#define PCHBTZLOGID1_TZ_LOG_RETURNNID_MASK                             0x003FF800
#define PCHBTZLOGID1_TZ_LOG_RETURNNID_BIT_OFFSET                               11

#define PCHBTZCTRL                                                     0x00000A24
#define PCHBTZCTRL_TZ_SEC_INV_EN_MASK                                  0x00000001
#define PCHBTZCTRL_TZ_SEC_INV_EN_BIT_OFFSET                                     0

#define PCHBTZRSETL0                                                   0x00000B00
#define PCHBTZRSETL0_TZ_BASE_ADDR_LOW_MASK                             0xFFFF8000
#define PCHBTZRSETL0_TZ_BASE_ADDR_LOW_BIT_OFFSET                               15

#define PCHBTZRSETH0                                                   0x00000B04
#define PCHBTZRSETH0_TZ_BASE_ADDR_HIGH_MASK                            0xFFFFFFFF
#define PCHBTZRSETH0_TZ_BASE_ADDR_HIGH_BIT_OFFSET                               0

#define PCHBTZRATTR0                                                   0x00000B08
#define PCHBTZRATTR0_TZ_REG_SP_MASK                                    0xF0000000
#define PCHBTZRATTR0_TZ_REG_SP_BIT_OFFSET                                      28

#define PCHBTZRSETL1                                                   0x00000B10
#define PCHBTZRSETL1_TZ_BASE_ADDR_LOW_MASK                             0xFFFF8000
#define PCHBTZRSETL1_TZ_BASE_ADDR_LOW_BIT_OFFSET                               15

#define PCHBTZRSETH1                                                   0x00000B14
#define PCHBTZRSETH1_TZ_BASE_ADDR_HIGH_MASK                            0xFFFFFFFF
#define PCHBTZRSETH1_TZ_BASE_ADDR_HIGH_BIT_OFFSET                               0

#define PCHBTZRATTR1                                                   0x00000B18
#define PCHBTZRATTR1_TZ_REGION_EN_MASK                                 0x00000001
#define PCHBTZRATTR1_TZ_REGION_EN_BIT_OFFSET                                    0
#define PCHBTZRATTR1_TZ_REGION_SIZE_MASK                               0x0000007E
#define PCHBTZRATTR1_TZ_REGION_SIZE_BIT_OFFSET                                  1
#define PCHBTZRATTR1_TZ_SUBREGION_DISABLE_MASK                         0x0FFFFF00
#define PCHBTZRATTR1_TZ_SUBREGION_DISABLE_BIT_OFFSET                            8
#define PCHBTZRATTR1_TZ_REG_SP_MASK                                    0xF0000000
#define PCHBTZRATTR1_TZ_REG_SP_BIT_OFFSET                                      28

#define PCHBTZRSETL2                                                   0x00000B20
#define PCHBTZRSETL2_TZ_BASE_ADDR_LOW_MASK                             0xFFFF8000
#define PCHBTZRSETL2_TZ_BASE_ADDR_LOW_BIT_OFFSET                               15

#define PCHBTZRSETH2                                                   0x00000B24
#define PCHBTZRSETH2_TZ_BASE_ADDR_HIGH_MASK                            0xFFFFFFFF
#define PCHBTZRSETH2_TZ_BASE_ADDR_HIGH_BIT_OFFSET                               0

#define PCHBTZRATTR2                                                   0x00000B28
#define PCHBTZRATTR2_TZ_REGION_EN_MASK                                 0x00000001
#define PCHBTZRATTR2_TZ_REGION_EN_BIT_OFFSET                                    0
#define PCHBTZRATTR2_TZ_REGION_SIZE_MASK                               0x0000007E
#define PCHBTZRATTR2_TZ_REGION_SIZE_BIT_OFFSET                                  1
#define PCHBTZRATTR2_TZ_SUBREGION_DISABLE_MASK                         0x0FFFFF00
#define PCHBTZRATTR2_TZ_SUBREGION_DISABLE_BIT_OFFSET                            8
#define PCHBTZRATTR2_TZ_REG_SP_MASK                                    0xF0000000
#define PCHBTZRATTR2_TZ_REG_SP_BIT_OFFSET                                      28

#define PCHBTZRSETL3                                                   0x00000B30
#define PCHBTZRSETL3_TZ_BASE_ADDR_LOW_MASK                             0xFFFF8000
#define PCHBTZRSETL3_TZ_BASE_ADDR_LOW_BIT_OFFSET                               15

#define PCHBTZRSETH3                                                   0x00000B34
#define PCHBTZRSETH3_TZ_BASE_ADDR_HIGH_MASK                            0xFFFFFFFF
#define PCHBTZRSETH3_TZ_BASE_ADDR_HIGH_BIT_OFFSET                               0

#define PCHBTZRATTR3                                                   0x00000B38
#define PCHBTZRATTR3_TZ_REGION_EN_MASK                                 0x00000001
#define PCHBTZRATTR3_TZ_REGION_EN_BIT_OFFSET                                    0
#define PCHBTZRATTR3_TZ_REGION_SIZE_MASK                               0x0000007E
#define PCHBTZRATTR3_TZ_REGION_SIZE_BIT_OFFSET                                  1
#define PCHBTZRATTR3_TZ_SUBREGION_DISABLE_MASK                         0x0FFFFF00
#define PCHBTZRATTR3_TZ_SUBREGION_DISABLE_BIT_OFFSET                            8
#define PCHBTZRATTR3_TZ_REG_SP_MASK                                    0xF0000000
#define PCHBTZRATTR3_TZ_REG_SP_BIT_OFFSET                                      28

#define PCHBTZRSETL4                                                   0x00000B40
#define PCHBTZRSETL4_TZ_BASE_ADDR_LOW_MASK                             0xFFFF8000
#define PCHBTZRSETL4_TZ_BASE_ADDR_LOW_BIT_OFFSET                               15

#define PCHBTZRSETH4                                                   0x00000B44
#define PCHBTZRSETH4_TZ_BASE_ADDR_HIGH_MASK                            0xFFFFFFFF
#define PCHBTZRSETH4_TZ_BASE_ADDR_HIGH_BIT_OFFSET                               0

#define PCHBTZRATTR4                                                   0x00000B48
#define PCHBTZRATTR4_TZ_REGION_EN_MASK                                 0x00000001
#define PCHBTZRATTR4_TZ_REGION_EN_BIT_OFFSET                                    0
#define PCHBTZRATTR4_TZ_REGION_SIZE_MASK                               0x0000007E
#define PCHBTZRATTR4_TZ_REGION_SIZE_BIT_OFFSET                                  1
#define PCHBTZRATTR4_TZ_SUBREGION_DISABLE_MASK                         0x0FFFFF00
#define PCHBTZRATTR4_TZ_SUBREGION_DISABLE_BIT_OFFSET                            8
#define PCHBTZRATTR4_TZ_REG_SP_MASK                                    0xF0000000
#define PCHBTZRATTR4_TZ_REG_SP_BIT_OFFSET                                      28

#define PCHBTZRSETL5                                                   0x00000B50
#define PCHBTZRSETL5_TZ_BASE_ADDR_LOW_MASK                             0xFFFF8000
#define PCHBTZRSETL5_TZ_BASE_ADDR_LOW_BIT_OFFSET                               15

#define PCHBTZRSETH5                                                   0x00000B54
#define PCHBTZRSETH5_TZ_BASE_ADDR_HIGH_MASK                            0xFFFFFFFF
#define PCHBTZRSETH5_TZ_BASE_ADDR_HIGH_BIT_OFFSET                               0

#define PCHBTZRATTR5                                                   0x00000B58
#define PCHBTZRATTR5_TZ_REGION_EN_MASK                                 0x00000001
#define PCHBTZRATTR5_TZ_REGION_EN_BIT_OFFSET                                    0
#define PCHBTZRATTR5_TZ_REGION_SIZE_MASK                               0x0000007E
#define PCHBTZRATTR5_TZ_REGION_SIZE_BIT_OFFSET                                  1
#define PCHBTZRATTR5_TZ_SUBREGION_DISABLE_MASK                         0x0FFFFF00
#define PCHBTZRATTR5_TZ_SUBREGION_DISABLE_BIT_OFFSET                            8
#define PCHBTZRATTR5_TZ_REG_SP_MASK                                    0xF0000000
#define PCHBTZRATTR5_TZ_REG_SP_BIT_OFFSET                                      28

#define PCHBTZRSETL6                                                   0x00000B60
#define PCHBTZRSETL6_TZ_BASE_ADDR_LOW_MASK                             0xFFFF8000
#define PCHBTZRSETL6_TZ_BASE_ADDR_LOW_BIT_OFFSET                               15

#define PCHBTZRSETH6                                                   0x00000B64
#define PCHBTZRSETH6_TZ_BASE_ADDR_HIGH_MASK                            0xFFFFFFFF
#define PCHBTZRSETH6_TZ_BASE_ADDR_HIGH_BIT_OFFSET                               0

#define PCHBTZRATTR6                                                   0x00000B68
#define PCHBTZRATTR6_TZ_REGION_EN_MASK                                 0x00000001
#define PCHBTZRATTR6_TZ_REGION_EN_BIT_OFFSET                                    0
#define PCHBTZRATTR6_TZ_REGION_SIZE_MASK                               0x0000007E
#define PCHBTZRATTR6_TZ_REGION_SIZE_BIT_OFFSET                                  1
#define PCHBTZRATTR6_TZ_SUBREGION_DISABLE_MASK                         0x0FFFFF00
#define PCHBTZRATTR6_TZ_SUBREGION_DISABLE_BIT_OFFSET                            8
#define PCHBTZRATTR6_TZ_REG_SP_MASK                                    0xF0000000
#define PCHBTZRATTR6_TZ_REG_SP_BIT_OFFSET                                      28

#define PCHBTZRSETL7                                                   0x00000B70
#define PCHBTZRSETL7_TZ_BASE_ADDR_LOW_MASK                             0xFFFF8000
#define PCHBTZRSETL7_TZ_BASE_ADDR_LOW_BIT_OFFSET                               15

#define PCHBTZRSETH7                                                   0x00000B74
#define PCHBTZRSETH7_TZ_BASE_ADDR_HIGH_MASK                            0xFFFFFFFF
#define PCHBTZRSETH7_TZ_BASE_ADDR_HIGH_BIT_OFFSET                               0

#define PCHBTZRATTR7                                                   0x00000B78
#define PCHBTZRATTR7_TZ_REGION_EN_MASK                                 0x00000001
#define PCHBTZRATTR7_TZ_REGION_EN_BIT_OFFSET                                    0
#define PCHBTZRATTR7_TZ_REGION_SIZE_MASK                               0x0000007E
#define PCHBTZRATTR7_TZ_REGION_SIZE_BIT_OFFSET                                  1
#define PCHBTZRATTR7_TZ_SUBREGION_DISABLE_MASK                         0x0FFFFF00
#define PCHBTZRATTR7_TZ_SUBREGION_DISABLE_BIT_OFFSET                            8
#define PCHBTZRATTR7_TZ_REG_SP_MASK                                    0xF0000000
#define PCHBTZRATTR7_TZ_REG_SP_BIT_OFFSET                                      28

#define REG_GROUP_ARB_PORT1                                            0x00021000

#define REG_GROUP_ARB_PORT2                                            0x00022000

#define REG_GROUP_ARB_PORT3                                            0x00023000

#define REG_GROUP_ARB_PORT4                                            0x00024000

#define REG_GROUP_ARB_PORT5                                            0x00025000

#define REG_GROUP_ARB_PORT6                                            0x00026000

#define REG_GROUP_ARB_PORT7                                            0x00027000

#define REG_GROUP_ARB_PORT8                                            0x00028000

#define REG_GROUP_ARB_PORT9                                            0x00029000

#define REG_GROUP_ARB_PORT10                                           0x0002A000

#define REG_GROUP_ARB_PORT11                                           0x0002B000

#define REG_GROUP_ARB_PORT12                                           0x0002C000

#define REG_GROUP_ARB_PORT13                                           0x0002D000

#define REG_GROUP_ARB_PORT14                                           0x0002E000

#define REG_GROUP_ARB_PORT15                                           0x0002F000

#define REG_GROUP_FREQ0_CH0                                            0x00000000

#define DRAMSET1TMG0                                                   0x00000000
#define DRAMSET1TMG0_T_RAS_MIN_MASK                                    0x000000FF
#define DRAMSET1TMG0_T_RAS_MIN_BIT_OFFSET                                       0
#define DRAMSET1TMG0_T_RAS_MAX_MASK                                    0x0000FF00
#define DRAMSET1TMG0_T_RAS_MAX_BIT_OFFSET                                       8
#define DRAMSET1TMG0_T_FAW_MASK                                        0x00FF0000
#define DRAMSET1TMG0_T_FAW_BIT_OFFSET                                          16
#define DRAMSET1TMG0_WR2PRE_MASK                                       0xFF000000
#define DRAMSET1TMG0_WR2PRE_BIT_OFFSET                                         24

#define DRAMSET1TMG1                                                   0x00000004
#define DRAMSET1TMG1_T_RC_MASK                                         0x000000FF
#define DRAMSET1TMG1_T_RC_BIT_OFFSET                                            0
#define DRAMSET1TMG1_RD2PRE_MASK                                       0x0000FF00
#define DRAMSET1TMG1_RD2PRE_BIT_OFFSET                                          8
#define DRAMSET1TMG1_T_XP_MASK                                         0x003F0000
#define DRAMSET1TMG1_T_XP_BIT_OFFSET                                           16
#define DRAMSET1TMG1_T_RCD_WRITE_MASK                                  0xFF000000
#define DRAMSET1TMG1_T_RCD_WRITE_BIT_OFFSET                                    24

#define DRAMSET1TMG2                                                   0x00000008
#define DRAMSET1TMG2_WR2RD_MASK                                        0x000000FF
#define DRAMSET1TMG2_WR2RD_BIT_OFFSET                                           0
#define DRAMSET1TMG2_RD2WR_MASK                                        0x0000FF00
#define DRAMSET1TMG2_RD2WR_BIT_OFFSET                                           8
#define DRAMSET1TMG2_READ_LATENCY_MASK                                 0x007F0000
#define DRAMSET1TMG2_READ_LATENCY_BIT_OFFSET                                   16
#define DRAMSET1TMG2_WRITE_LATENCY_MASK                                0x7F000000
#define DRAMSET1TMG2_WRITE_LATENCY_BIT_OFFSET                                  24

#define DRAMSET1TMG3                                                   0x0000000C
#define DRAMSET1TMG3_WR2MR_MASK                                        0x000000FF
#define DRAMSET1TMG3_WR2MR_BIT_OFFSET                                           0
#define DRAMSET1TMG3_RD2MR_MASK                                        0x0000FF00
#define DRAMSET1TMG3_RD2MR_BIT_OFFSET                                           8
#define DRAMSET1TMG3_T_MR_MASK                                         0x007F0000
#define DRAMSET1TMG3_T_MR_BIT_OFFSET                                           16

#define DRAMSET1TMG4                                                   0x00000010
#define DRAMSET1TMG4_T_RP_MASK                                         0x0000007F
#define DRAMSET1TMG4_T_RP_BIT_OFFSET                                            0
#define DRAMSET1TMG4_T_RRD_MASK                                        0x00003F00
#define DRAMSET1TMG4_T_RRD_BIT_OFFSET                                           8
#define DRAMSET1TMG4_T_CCD_MASK                                        0x003F0000
#define DRAMSET1TMG4_T_CCD_BIT_OFFSET                                          16
#define DRAMSET1TMG4_T_RCD_MASK                                        0xFF000000
#define DRAMSET1TMG4_T_RCD_BIT_OFFSET                                          24

#define DRAMSET1TMG5                                                   0x00000014
#define DRAMSET1TMG5_T_CKE_MASK                                        0x0000003F
#define DRAMSET1TMG5_T_CKE_BIT_OFFSET                                           0
#define DRAMSET1TMG5_T_CKESR_MASK                                      0x00007F00
#define DRAMSET1TMG5_T_CKESR_BIT_OFFSET                                         8
#define DRAMSET1TMG5_T_CKSRE_MASK                                      0x007F0000
#define DRAMSET1TMG5_T_CKSRE_BIT_OFFSET                                        16
#define DRAMSET1TMG5_T_CKSRX_MASK                                      0x3F000000
#define DRAMSET1TMG5_T_CKSRX_BIT_OFFSET                                        24

#define DRAMSET1TMG6                                                   0x00000018
#define DRAMSET1TMG6_T_CKCSX_MASK                                      0x0000003F
#define DRAMSET1TMG6_T_CKCSX_BIT_OFFSET                                         0

#define DRAMSET1TMG7                                                   0x0000001C
#define DRAMSET1TMG7_T_CSH_MASK                                        0x0000000F
#define DRAMSET1TMG7_T_CSH_BIT_OFFSET                                           0
#define DRAMSET1TMG7_T_MRW_L_MASK                                      0x01FF0000
#define DRAMSET1TMG7_T_MRW_L_BIT_OFFSET                                        16

#define DRAMSET1TMG8                                                   0x00000020
#define DRAMSET1TMG8_T_XS_X32_MASK                                     0x0000007F
#define DRAMSET1TMG8_T_XS_X32_BIT_OFFSET                                        0
#define DRAMSET1TMG8_T_XS_DLL_X32_MASK                                 0x00007F00
#define DRAMSET1TMG8_T_XS_DLL_X32_BIT_OFFSET                                    8
#define DRAMSET1TMG8_T_XS_ABORT_X32_MASK                               0x007F0000
#define DRAMSET1TMG8_T_XS_ABORT_X32_BIT_OFFSET                                 16
#define DRAMSET1TMG8_T_XS_FAST_X32_MASK                                0x7F000000
#define DRAMSET1TMG8_T_XS_FAST_X32_BIT_OFFSET                                  24

#define DRAMSET1TMG9                                                   0x00000024
#define DRAMSET1TMG9_WR2RD_S_MASK                                      0x000000FF
#define DRAMSET1TMG9_WR2RD_S_BIT_OFFSET                                         0
#define DRAMSET1TMG9_T_RRD_S_MASK                                      0x00003F00
#define DRAMSET1TMG9_T_RRD_S_BIT_OFFSET                                         8
#define DRAMSET1TMG9_T_CCD_S_MASK                                      0x001F0000
#define DRAMSET1TMG9_T_CCD_S_BIT_OFFSET                                        16
#define DRAMSET1TMG9_DDR4_WR_PREAMBLE_MASK                             0x40000000
#define DRAMSET1TMG9_DDR4_WR_PREAMBLE_BIT_OFFSET                               30

#define DRAMSET1TMG10                                                  0x00000028
#define DRAMSET1TMG10_T_GEAR_HOLD_MASK                                 0x00000007
#define DRAMSET1TMG10_T_GEAR_HOLD_BIT_OFFSET                                    0
#define DRAMSET1TMG10_T_GEAR_SETUP_MASK                                0x00000070
#define DRAMSET1TMG10_T_GEAR_SETUP_BIT_OFFSET                                   4
#define DRAMSET1TMG10_T_CMD_GEAR_MASK                                  0x00003F00
#define DRAMSET1TMG10_T_CMD_GEAR_BIT_OFFSET                                     8
#define DRAMSET1TMG10_T_SYNC_GEAR_MASK                                 0x003F0000
#define DRAMSET1TMG10_T_SYNC_GEAR_BIT_OFFSET                                   16

#define DRAMSET1TMG11                                                  0x0000002C
#define DRAMSET1TMG11_T_CKMPE_MASK                                     0x0000003F
#define DRAMSET1TMG11_T_CKMPE_BIT_OFFSET                                        0
#define DRAMSET1TMG11_T_MPX_S_MASK                                     0x00000700
#define DRAMSET1TMG11_T_MPX_S_BIT_OFFSET                                        8
#define DRAMSET1TMG11_T_MPX_LH_MASK                                    0x003F0000
#define DRAMSET1TMG11_T_MPX_LH_BIT_OFFSET                                      16
#define DRAMSET1TMG11_POST_MPSM_GAP_X32_MASK                           0xFF000000
#define DRAMSET1TMG11_POST_MPSM_GAP_X32_BIT_OFFSET                             24

#define DRAMSET1TMG12                                                  0x00000030
#define DRAMSET1TMG12_T_MRD_PDA_MASK                                   0x0000003F
#define DRAMSET1TMG12_T_MRD_PDA_BIT_OFFSET                                      0
#define DRAMSET1TMG12_T_CMDCKE_MASK                                    0x000F0000
#define DRAMSET1TMG12_T_CMDCKE_BIT_OFFSET                                      16
#define DRAMSET1TMG12_T_WR_MPR_MASK                                    0x7F000000
#define DRAMSET1TMG12_T_WR_MPR_BIT_OFFSET                                      24

#define DRAMSET1TMG13                                                  0x00000034
#define DRAMSET1TMG13_T_PPD_MASK                                       0x0000000F
#define DRAMSET1TMG13_T_PPD_BIT_OFFSET                                          0
#define DRAMSET1TMG13_T_CCD_W2_MASK                                    0x00000FF0
#define DRAMSET1TMG13_T_CCD_W2_BIT_OFFSET                                       4
#define DRAMSET1TMG13_T_CCD_MW_MASK                                    0x007F0000
#define DRAMSET1TMG13_T_CCD_MW_BIT_OFFSET                                      16
#define DRAMSET1TMG13_ODTLOFF_MASK                                     0x7F000000
#define DRAMSET1TMG13_ODTLOFF_BIT_OFFSET                                       24

#define DRAMSET1TMG14                                                  0x00000038
#define DRAMSET1TMG14_T_XSR_MASK                                       0x00000FFF
#define DRAMSET1TMG14_T_XSR_BIT_OFFSET                                          0
#define DRAMSET1TMG14_T_OSCO_MASK                                      0x01FF0000
#define DRAMSET1TMG14_T_OSCO_BIT_OFFSET                                        16

#define DRAMSET1TMG15                                                  0x0000003C
#define DRAMSET1TMG15_T_STAB_X32_MASK                                  0x000003FF
#define DRAMSET1TMG15_T_STAB_X32_BIT_OFFSET                                     0
#define DRAMSET1TMG15_EN_HWFFC_T_STAB_MASK                             0x01000000
#define DRAMSET1TMG15_EN_HWFFC_T_STAB_BIT_OFFSET                               24
#define DRAMSET1TMG15_EN_DFI_LP_T_STAB_MASK                            0x80000000
#define DRAMSET1TMG15_EN_DFI_LP_T_STAB_BIT_OFFSET                              31

#define DRAMSET1TMG16                                                  0x00000040
#define DRAMSET1TMG16_T_CCD_DLR_MASK                                   0x0000003F
#define DRAMSET1TMG16_T_CCD_DLR_BIT_OFFSET                                      0
#define DRAMSET1TMG16_T_RRD_DLR_MASK                                   0x00000F00
#define DRAMSET1TMG16_T_RRD_DLR_BIT_OFFSET                                      8
#define DRAMSET1TMG16_T_FAW_DLR_MASK                                   0x00FF0000
#define DRAMSET1TMG16_T_FAW_DLR_BIT_OFFSET                                     16
#define DRAMSET1TMG16_T_RP_CA_PARITY_MASK                              0xFF000000
#define DRAMSET1TMG16_T_RP_CA_PARITY_BIT_OFFSET                                24

#define DRAMSET1TMG17                                                  0x00000044
#define DRAMSET1TMG17_T_VRCG_DISABLE_MASK                              0x000003FF
#define DRAMSET1TMG17_T_VRCG_DISABLE_BIT_OFFSET                                 0
#define DRAMSET1TMG17_T_VRCG_ENABLE_MASK                               0x03FF0000
#define DRAMSET1TMG17_T_VRCG_ENABLE_BIT_OFFSET                                 16

#define DRAMSET1TMG18                                                  0x00000048
#define DRAMSET1TMG18_T_MPSMX_MASK                                     0x007F0000
#define DRAMSET1TMG18_T_MPSMX_BIT_OFFSET                                       16
#define DRAMSET1TMG18_T_PD_MASK                                        0x7F000000
#define DRAMSET1TMG18_T_PD_BIT_OFFSET                                          24

#define DRAMSET1TMG20                                                  0x00000050
#define DRAMSET1TMG20_T_CSL_SREXIT_MASK                                0x000000FF
#define DRAMSET1TMG20_T_CSL_SREXIT_BIT_OFFSET                                   0
#define DRAMSET1TMG20_T_CSH_SREXIT_MASK                                0x0000FF00
#define DRAMSET1TMG20_T_CSH_SREXIT_BIT_OFFSET                                   8
#define DRAMSET1TMG20_T_CASRX_MASK                                     0x001F0000
#define DRAMSET1TMG20_T_CASRX_BIT_OFFSET                                       16
#define DRAMSET1TMG20_T_CPDED_MASK                                     0x3F000000
#define DRAMSET1TMG20_T_CPDED_BIT_OFFSET                                       24

#define DRAMSET1TMG21                                                  0x00000054
#define DRAMSET1TMG21_T_MPC_HOLD_MASK                                  0x0001C000
#define DRAMSET1TMG21_T_MPC_HOLD_BIT_OFFSET                                    14
#define DRAMSET1TMG21_T_MPC_SETUP_MASK                                 0x000E0000
#define DRAMSET1TMG21_T_MPC_SETUP_BIT_OFFSET                                   17
#define DRAMSET1TMG21_T_MPC_CS_MASK                                    0x01F00000
#define DRAMSET1TMG21_T_MPC_CS_BIT_OFFSET                                      20
#define DRAMSET1TMG21_T_CSL_MASK                                       0xFE000000
#define DRAMSET1TMG21_T_CSL_BIT_OFFSET                                         25

#define DRAMSET1TMG22                                                  0x00000058
#define DRAMSET1TMG22_T_RD2WR_DPR_MASK                                 0x0000007F
#define DRAMSET1TMG22_T_RD2WR_DPR_BIT_OFFSET                                    0
#define DRAMSET1TMG22_T_RD2WR_DLR_MASK                                 0x00003F80
#define DRAMSET1TMG22_T_RD2WR_DLR_BIT_OFFSET                                    7
#define DRAMSET1TMG22_T_WR2RD_DPR_MASK                                 0x003FC000
#define DRAMSET1TMG22_T_WR2RD_DPR_BIT_OFFSET                                   14
#define DRAMSET1TMG22_T_WR2RD_DLR_MASK                                 0x3FC00000
#define DRAMSET1TMG22_T_WR2RD_DLR_BIT_OFFSET                                   22

#define DRAMSET1TMG23                                                  0x0000005C
#define DRAMSET1TMG23_T_PDN_MASK                                       0x00000FFF
#define DRAMSET1TMG23_T_PDN_BIT_OFFSET                                          0
#define DRAMSET1TMG23_T_XSR_DSM_X1024_MASK                             0x00FF0000
#define DRAMSET1TMG23_T_XSR_DSM_X1024_BIT_OFFSET                               16

#define DRAMSET1TMG24                                                  0x00000060
#define DRAMSET1TMG24_MAX_WR_SYNC_MASK                                 0x000000FF
#define DRAMSET1TMG24_MAX_WR_SYNC_BIT_OFFSET                                    0
#define DRAMSET1TMG24_MAX_RD_SYNC_MASK                                 0x0000FF00
#define DRAMSET1TMG24_MAX_RD_SYNC_BIT_OFFSET                                    8
#define DRAMSET1TMG24_RD2WR_S_MASK                                     0x00FF0000
#define DRAMSET1TMG24_RD2WR_S_BIT_OFFSET                                       16
#define DRAMSET1TMG24_BANK_ORG_MASK                                    0x03000000
#define DRAMSET1TMG24_BANK_ORG_BIT_OFFSET                                      24

#define DRAMSET1TMG25                                                  0x00000064
#define DRAMSET1TMG25_RDA2PRE_MASK                                     0x000000FF
#define DRAMSET1TMG25_RDA2PRE_BIT_OFFSET                                        0
#define DRAMSET1TMG25_WRA2PRE_MASK                                     0x0000FF00
#define DRAMSET1TMG25_WRA2PRE_BIT_OFFSET                                        8
#define DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE_MASK                    0x00070000
#define DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE_BIT_OFFSET                      16

#define DRAMSET1TMG26                                                  0x00000068
#define DRAMSET1TMG26_T_CCD_R_MASK                                     0x000000FF
#define DRAMSET1TMG26_T_CCD_R_BIT_OFFSET                                        0
#define DRAMSET1TMG26_T_CCD_W_MASK                                     0x0000FF00
#define DRAMSET1TMG26_T_CCD_W_BIT_OFFSET                                        8
#define DRAMSET1TMG26_T_CCD_R_S_MASK                                   0x00FF0000
#define DRAMSET1TMG26_T_CCD_R_S_BIT_OFFSET                                     16
#define DRAMSET1TMG26_T_CCD_W_S_MASK                                   0xFF000000
#define DRAMSET1TMG26_T_CCD_W_S_BIT_OFFSET                                     24

#define DRAMSET1TMG27                                                  0x0000006C
#define DRAMSET1TMG27_T_MRR2MPC_MASK                                   0x000000FF
#define DRAMSET1TMG27_T_MRR2MPC_BIT_OFFSET                                      0
#define DRAMSET1TMG27_T_ECSC_MASK                                      0x01FF0000
#define DRAMSET1TMG27_T_ECSC_BIT_OFFSET                                        16

#define DRAMSET1TMG28                                                  0x00000070
#define DRAMSET1TMG28_T_SRX2SRX_MASK                                   0x0000007F
#define DRAMSET1TMG28_T_SRX2SRX_BIT_OFFSET                                      0
#define DRAMSET1TMG28_T_CPDED2SRX_MASK                                 0x00007F00
#define DRAMSET1TMG28_T_CPDED2SRX_BIT_OFFSET                                    8
#define DRAMSET1TMG28_T_CSSR_MASK                                      0x007F0000
#define DRAMSET1TMG28_T_CSSR_BIT_OFFSET                                        16

#define DRAMSET1TMG29                                                  0x00000074
#define DRAMSET1TMG29_T_CKACT_MASK                                     0x003F0000
#define DRAMSET1TMG29_T_CKACT_BIT_OFFSET                                       16
#define DRAMSET1TMG29_T_CKOFF_MASK                                     0x7F000000
#define DRAMSET1TMG29_T_CKOFF_BIT_OFFSET                                       24

#define DRAMSET1TMG30                                                  0x00000078
#define DRAMSET1TMG30_MRR2RD_MASK                                      0x000000FF
#define DRAMSET1TMG30_MRR2RD_BIT_OFFSET                                         0
#define DRAMSET1TMG30_MRR2WR_MASK                                      0x0000FF00
#define DRAMSET1TMG30_MRR2WR_BIT_OFFSET                                         8
#define DRAMSET1TMG30_MRR2MRW_MASK                                     0x00FF0000
#define DRAMSET1TMG30_MRR2MRW_BIT_OFFSET                                       16

#define DRAMSET1TMG31                                                  0x0000007C
#define DRAMSET1TMG31_RFM_RAAIMT_MASK                                  0x0000007F
#define DRAMSET1TMG31_RFM_RAAIMT_BIT_OFFSET                                     0
#define DRAMSET1TMG31_RFM_RAA_THR_MASK                                 0x0003FE00
#define DRAMSET1TMG31_RFM_RAA_THR_BIT_OFFSET                                    9
#define DRAMSET1TMG31_RFM_RAA_REF_DECR_MASK                            0x00180000
#define DRAMSET1TMG31_RFM_RAA_REF_DECR_BIT_OFFSET                              19

#define DRAMSET1TMG32                                                  0x00000080
#define DRAMSET1TMG32_WS_FS2WCK_SUS_MASK                               0x0000000F
#define DRAMSET1TMG32_WS_FS2WCK_SUS_BIT_OFFSET                                  0
#define DRAMSET1TMG32_T_WCKSUS_MASK                                    0x00000F00
#define DRAMSET1TMG32_T_WCKSUS_BIT_OFFSET                                       8
#define DRAMSET1TMG32_WS_OFF2WS_FS_MASK                                0x000F0000
#define DRAMSET1TMG32_WS_OFF2WS_FS_BIT_OFFSET                                  16

#define DRAMSET1TMG33                                                  0x00000084
#define DRAMSET1TMG33_T_CCD_R_M_MASK                                   0x000000FF
#define DRAMSET1TMG33_T_CCD_R_M_BIT_OFFSET                                      0
#define DRAMSET1TMG33_T_CCD_W_M_MASK                                   0x0000FF00
#define DRAMSET1TMG33_T_CCD_W_M_BIT_OFFSET                                      8
#define DRAMSET1TMG33_T_WR2RD_M_MASK                                   0x00FF0000
#define DRAMSET1TMG33_T_WR2RD_M_BIT_OFFSET                                     16

#define DRAMSET1TMG34                                                  0x00000088
#define DRAMSET1TMG34_T_CCD_MW_BLX2_MASK                               0x000000FF
#define DRAMSET1TMG34_T_CCD_MW_BLX2_BIT_OFFSET                                  0
#define DRAMSET1TMG34_RD2WR_BLX2_MASK                                  0x0000FF00
#define DRAMSET1TMG34_RD2WR_BLX2_BIT_OFFSET                                     8
#define DRAMSET1TMG34_WR2RD_BLX2_MASK                                  0x00FF0000
#define DRAMSET1TMG34_WR2RD_BLX2_BIT_OFFSET                                    16
#define DRAMSET1TMG34_T_CCD_BLX2_MASK                                  0x3F000000
#define DRAMSET1TMG34_T_CCD_BLX2_BIT_OFFSET                                    24

#define DRAMSET1TMG35                                                  0x0000008C
#define DRAMSET1TMG35_RDA2PRE_BLX2_MASK                                0x000000FF
#define DRAMSET1TMG35_RDA2PRE_BLX2_BIT_OFFSET                                   0
#define DRAMSET1TMG35_WRA2PRE_BLX2_MASK                                0x0000FF00
#define DRAMSET1TMG35_WRA2PRE_BLX2_BIT_OFFSET                                   8
#define DRAMSET1TMG35_RD2PRE_BLX2_MASK                                 0x00FF0000
#define DRAMSET1TMG35_RD2PRE_BLX2_BIT_OFFSET                                   16
#define DRAMSET1TMG35_WR2PRE_BLX2_MASK                                 0xFF000000
#define DRAMSET1TMG35_WR2PRE_BLX2_BIT_OFFSET                                   24

#define DRAMSET1TMG36                                                  0x00000090
#define DRAMSET1TMG36_RD2WR_S_BLX2_MASK                                0x000000FF
#define DRAMSET1TMG36_RD2WR_S_BLX2_BIT_OFFSET                                   0
#define DRAMSET1TMG36_WR2RD_S_BLX2_MASK                                0x0000FF00
#define DRAMSET1TMG36_WR2RD_S_BLX2_BIT_OFFSET                                   8
#define DRAMSET1TMG36_T_CCD_S_BLX2_MASK                                0x001F0000
#define DRAMSET1TMG36_T_CCD_S_BLX2_BIT_OFFSET                                  16

#define DRAMSET1TMG37                                                  0x00000094
#define DRAMSET1TMG37_MAX_WR_SYNC_BLX2_MASK                            0x000000FF
#define DRAMSET1TMG37_MAX_WR_SYNC_BLX2_BIT_OFFSET                               0
#define DRAMSET1TMG37_MAX_RD_SYNC_BLX2_MASK                            0x0000FF00
#define DRAMSET1TMG37_MAX_RD_SYNC_BLX2_BIT_OFFSET                               8
#define DRAMSET1TMG37_WR2MR_BLX2_MASK                                  0x00FF0000
#define DRAMSET1TMG37_WR2MR_BLX2_BIT_OFFSET                                    16
#define DRAMSET1TMG37_RD2MR_BLX2_MASK                                  0xFF000000
#define DRAMSET1TMG37_RD2MR_BLX2_BIT_OFFSET                                    24

#define DRAMSET1TMG38                                                  0x00000098
#define DRAMSET1TMG38_WR2RD_DR_BLX2_MASK                               0x000000FF
#define DRAMSET1TMG38_WR2RD_DR_BLX2_BIT_OFFSET                                  0
#define DRAMSET1TMG38_RD2WR_DR_BLX2_MASK                               0x0000FF00
#define DRAMSET1TMG38_RD2WR_DR_BLX2_BIT_OFFSET                                  8
#define DRAMSET1TMG38_DIFF_RANK_RD_GAP_BLX2_MASK                       0x00FF0000
#define DRAMSET1TMG38_DIFF_RANK_RD_GAP_BLX2_BIT_OFFSET                         16
#define DRAMSET1TMG38_DIFF_RANK_WR_GAP_BLX2_MASK                       0xFF000000
#define DRAMSET1TMG38_DIFF_RANK_WR_GAP_BLX2_BIT_OFFSET                         24

#define DRAMSET2TMG0                                                   0x00000100
#define DRAMSET2TMG0_T_RAS_MIN_2_MASK                                  0x000000FF
#define DRAMSET2TMG0_T_RAS_MIN_2_BIT_OFFSET                                     0
#define DRAMSET2TMG0_T_FAW_2_MASK                                      0x00FF0000
#define DRAMSET2TMG0_T_FAW_2_BIT_OFFSET                                        16
#define DRAMSET2TMG0_WR2PRE_2_MASK                                     0xFF000000
#define DRAMSET2TMG0_WR2PRE_2_BIT_OFFSET                                       24

#define DRAMSET2TMG1                                                   0x00000104
#define DRAMSET2TMG1_T_RC_2_MASK                                       0x000000FF
#define DRAMSET2TMG1_T_RC_2_BIT_OFFSET                                          0
#define DRAMSET2TMG1_RD2PRE_2_MASK                                     0x0000FF00
#define DRAMSET2TMG1_RD2PRE_2_BIT_OFFSET                                        8

#define DRAMSET2TMG2                                                   0x00000108
#define DRAMSET2TMG2_WR2RD_2_MASK                                      0x000000FF
#define DRAMSET2TMG2_WR2RD_2_BIT_OFFSET                                         0
#define DRAMSET2TMG2_RD2WR_2_MASK                                      0x0000FF00
#define DRAMSET2TMG2_RD2WR_2_BIT_OFFSET                                         8

#define DRAMSET2TMG3                                                   0x0000010C
#define DRAMSET2TMG3_T_MR_2_MASK                                       0x007F0000
#define DRAMSET2TMG3_T_MR_2_BIT_OFFSET                                         16

#define DRAMSET2TMG4                                                   0x00000110
#define DRAMSET2TMG4_T_RP_2_MASK                                       0x0000007F
#define DRAMSET2TMG4_T_RP_2_BIT_OFFSET                                          0
#define DRAMSET2TMG4_T_RRD_2_MASK                                      0x00003F00
#define DRAMSET2TMG4_T_RRD_2_BIT_OFFSET                                         8
#define DRAMSET2TMG4_T_RCD_2_MASK                                      0xFF000000
#define DRAMSET2TMG4_T_RCD_2_BIT_OFFSET                                        24

#define DRAMSET2TMG8                                                   0x00000120
#define DRAMSET2TMG8_T_XS_X32_2_MASK                                   0x0000007F
#define DRAMSET2TMG8_T_XS_X32_2_BIT_OFFSET                                      0
#define DRAMSET2TMG8_T_XS_DLL_X32_2_MASK                               0x00007F00
#define DRAMSET2TMG8_T_XS_DLL_X32_2_BIT_OFFSET                                  8

#define DRAMSET2TMG9                                                   0x00000124
#define DRAMSET2TMG9_WR2RD_S_2_MASK                                    0x000000FF
#define DRAMSET2TMG9_WR2RD_S_2_BIT_OFFSET                                       0
#define DRAMSET2TMG9_T_RRD_S_2_MASK                                    0x00003F00
#define DRAMSET2TMG9_T_RRD_S_2_BIT_OFFSET                                       8

#define DRAMSET2TMG13                                                  0x00000134
#define DRAMSET2TMG13_T_PPD_2_MASK                                     0x0000000F
#define DRAMSET2TMG13_T_PPD_2_BIT_OFFSET                                        0
#define DRAMSET2TMG13_T_CCD_W2_2_MASK                                  0x00000FF0
#define DRAMSET2TMG13_T_CCD_W2_2_BIT_OFFSET                                     4

#define DRAMSET2TMG16                                                  0x00000140
#define DRAMSET2TMG16_T_CCD_DLR_2_MASK                                 0x0000003F
#define DRAMSET2TMG16_T_CCD_DLR_2_BIT_OFFSET                                    0
#define DRAMSET2TMG16_T_RRD_DLR_2_MASK                                 0x00000F00
#define DRAMSET2TMG16_T_RRD_DLR_2_BIT_OFFSET                                    8
#define DRAMSET2TMG16_T_FAW_DLR_2_MASK                                 0x00FF0000
#define DRAMSET2TMG16_T_FAW_DLR_2_BIT_OFFSET                                   16
#define DRAMSET2TMG16_T_RP_CA_PARITY_2_MASK                            0xFF000000
#define DRAMSET2TMG16_T_RP_CA_PARITY_2_BIT_OFFSET                              24

#define DRAMSET2TMG22                                                  0x00000158
#define DRAMSET2TMG22_T_RD2WR_DPR_2_MASK                               0x0000007F
#define DRAMSET2TMG22_T_RD2WR_DPR_2_BIT_OFFSET                                  0
#define DRAMSET2TMG22_T_RD2WR_DLR_2_MASK                               0x00003F80
#define DRAMSET2TMG22_T_RD2WR_DLR_2_BIT_OFFSET                                  7
#define DRAMSET2TMG22_T_WR2RD_DPR_2_MASK                               0x003FC000
#define DRAMSET2TMG22_T_WR2RD_DPR_2_BIT_OFFSET                                 14
#define DRAMSET2TMG22_T_WR2RD_DLR_2_MASK                               0x3FC00000
#define DRAMSET2TMG22_T_WR2RD_DLR_2_BIT_OFFSET                                 22

#define DRAMSET2TMG26                                                  0x00000168
#define DRAMSET2TMG26_T_CCD_R_2_MASK                                   0x000000FF
#define DRAMSET2TMG26_T_CCD_R_2_BIT_OFFSET                                      0
#define DRAMSET2TMG26_T_CCD_W_2_MASK                                   0x0000FF00
#define DRAMSET2TMG26_T_CCD_W_2_BIT_OFFSET                                      8
#define DRAMSET2TMG26_T_CCD_R_S_2_MASK                                 0x00FF0000
#define DRAMSET2TMG26_T_CCD_R_S_2_BIT_OFFSET                                   16
#define DRAMSET2TMG26_T_CCD_W_S_2_MASK                                 0xFF000000
#define DRAMSET2TMG26_T_CCD_W_S_2_BIT_OFFSET                                   24

#define DRAMSET2TMG27                                                  0x0000016C
#define DRAMSET2TMG27_T_MRR2MPC_2_MASK                                 0x000000FF
#define DRAMSET2TMG27_T_MRR2MPC_2_BIT_OFFSET                                    0

#define DRAMSET2TMG31                                                  0x0000017C
#define DRAMSET2TMG31_RFM_RAAIMT_2_MASK                                0x0000007F
#define DRAMSET2TMG31_RFM_RAAIMT_2_BIT_OFFSET                                   0
#define DRAMSET2TMG31_RFM_RAA_THR_2_MASK                               0x0003FE00
#define DRAMSET2TMG31_RFM_RAA_THR_2_BIT_OFFSET                                  9
#define DRAMSET2TMG31_RFM_RAA_REF_DECR_2_MASK                          0x00180000
#define DRAMSET2TMG31_RFM_RAA_REF_DECR_2_BIT_OFFSET                            19

#define DRAMSET2TMG33                                                  0x00000184
#define DRAMSET2TMG33_T_CCD_R_M_2_MASK                                 0x000000FF
#define DRAMSET2TMG33_T_CCD_R_M_2_BIT_OFFSET                                    0
#define DRAMSET2TMG33_T_CCD_W_M_2_MASK                                 0x0000FF00
#define DRAMSET2TMG33_T_CCD_W_M_2_BIT_OFFSET                                    8
#define DRAMSET2TMG33_T_WR2RD_M_2_MASK                                 0x00FF0000
#define DRAMSET2TMG33_T_WR2RD_M_2_BIT_OFFSET                                   16

#define RANK_SWITCH_TIMING_CONTROL0                                    0x00000400
#define RANK_SWITCH_TIMING_CONTROL0_T_RD2RD_GAP_R0R1_MASK              0x0000000F
#define RANK_SWITCH_TIMING_CONTROL0_T_RD2RD_GAP_R0R1_BIT_OFFSET                 0
#define RANK_SWITCH_TIMING_CONTROL0_T_RD2RD_GAP_R1R0_MASK              0x000000F0
#define RANK_SWITCH_TIMING_CONTROL0_T_RD2RD_GAP_R1R0_BIT_OFFSET                 4
#define RANK_SWITCH_TIMING_CONTROL0_T_WR2RD_GAP_R0R1_MASK              0x00000F00
#define RANK_SWITCH_TIMING_CONTROL0_T_WR2RD_GAP_R0R1_BIT_OFFSET                 8
#define RANK_SWITCH_TIMING_CONTROL0_T_WR2RD_GAP_R1R0_MASK              0x0000F000
#define RANK_SWITCH_TIMING_CONTROL0_T_WR2RD_GAP_R1R0_BIT_OFFSET                12
#define RANK_SWITCH_TIMING_CONTROL0_T_RD2WR_GAP_R0R1_MASK              0x000F0000
#define RANK_SWITCH_TIMING_CONTROL0_T_RD2WR_GAP_R0R1_BIT_OFFSET                16
#define RANK_SWITCH_TIMING_CONTROL0_T_RD2WR_GAP_R1R0_MASK              0x00F00000
#define RANK_SWITCH_TIMING_CONTROL0_T_RD2WR_GAP_R1R0_BIT_OFFSET                20
#define RANK_SWITCH_TIMING_CONTROL0_T_WR2WR_GAP_R0R1_MASK              0x0F000000
#define RANK_SWITCH_TIMING_CONTROL0_T_WR2WR_GAP_R0R1_BIT_OFFSET                24
#define RANK_SWITCH_TIMING_CONTROL0_T_WR2WR_GAP_R1R0_MASK              0xF0000000
#define RANK_SWITCH_TIMING_CONTROL0_T_WR2WR_GAP_R1R0_BIT_OFFSET                28

#define RANK_SWITCH_TIMING_CONTROL1                                    0x00000404
#define RANK_SWITCH_TIMING_CONTROL1_T_RD2RD_GAP_R0R2_MASK              0x0000000F
#define RANK_SWITCH_TIMING_CONTROL1_T_RD2RD_GAP_R0R2_BIT_OFFSET                 0
#define RANK_SWITCH_TIMING_CONTROL1_T_RD2RD_GAP_R2R0_MASK              0x000000F0
#define RANK_SWITCH_TIMING_CONTROL1_T_RD2RD_GAP_R2R0_BIT_OFFSET                 4
#define RANK_SWITCH_TIMING_CONTROL1_T_WR2RD_GAP_R0R2_MASK              0x00000F00
#define RANK_SWITCH_TIMING_CONTROL1_T_WR2RD_GAP_R0R2_BIT_OFFSET                 8
#define RANK_SWITCH_TIMING_CONTROL1_T_WR2RD_GAP_R2R0_MASK              0x0000F000
#define RANK_SWITCH_TIMING_CONTROL1_T_WR2RD_GAP_R2R0_BIT_OFFSET                12
#define RANK_SWITCH_TIMING_CONTROL1_T_RD2WR_GAP_R0R2_MASK              0x000F0000
#define RANK_SWITCH_TIMING_CONTROL1_T_RD2WR_GAP_R0R2_BIT_OFFSET                16
#define RANK_SWITCH_TIMING_CONTROL1_T_RD2WR_GAP_R2R0_MASK              0x00F00000
#define RANK_SWITCH_TIMING_CONTROL1_T_RD2WR_GAP_R2R0_BIT_OFFSET                20
#define RANK_SWITCH_TIMING_CONTROL1_T_WR2WR_GAP_R0R2_MASK              0x0F000000
#define RANK_SWITCH_TIMING_CONTROL1_T_WR2WR_GAP_R0R2_BIT_OFFSET                24
#define RANK_SWITCH_TIMING_CONTROL1_T_WR2WR_GAP_R2R0_MASK              0xF0000000
#define RANK_SWITCH_TIMING_CONTROL1_T_WR2WR_GAP_R2R0_BIT_OFFSET                28

#define RANK_SWITCH_TIMING_CONTROL2                                    0x00000408
#define RANK_SWITCH_TIMING_CONTROL2_T_RD2RD_GAP_R0R3_MASK              0x0000000F
#define RANK_SWITCH_TIMING_CONTROL2_T_RD2RD_GAP_R0R3_BIT_OFFSET                 0
#define RANK_SWITCH_TIMING_CONTROL2_T_RD2RD_GAP_R3R0_MASK              0x000000F0
#define RANK_SWITCH_TIMING_CONTROL2_T_RD2RD_GAP_R3R0_BIT_OFFSET                 4
#define RANK_SWITCH_TIMING_CONTROL2_T_WR2RD_GAP_R0R3_MASK              0x00000F00
#define RANK_SWITCH_TIMING_CONTROL2_T_WR2RD_GAP_R0R3_BIT_OFFSET                 8
#define RANK_SWITCH_TIMING_CONTROL2_T_WR2RD_GAP_R3R0_MASK              0x0000F000
#define RANK_SWITCH_TIMING_CONTROL2_T_WR2RD_GAP_R3R0_BIT_OFFSET                12
#define RANK_SWITCH_TIMING_CONTROL2_T_RD2WR_GAP_R0R3_MASK              0x000F0000
#define RANK_SWITCH_TIMING_CONTROL2_T_RD2WR_GAP_R0R3_BIT_OFFSET                16
#define RANK_SWITCH_TIMING_CONTROL2_T_RD2WR_GAP_R3R0_MASK              0x00F00000
#define RANK_SWITCH_TIMING_CONTROL2_T_RD2WR_GAP_R3R0_BIT_OFFSET                20
#define RANK_SWITCH_TIMING_CONTROL2_T_WR2WR_GAP_R0R3_MASK              0x0F000000
#define RANK_SWITCH_TIMING_CONTROL2_T_WR2WR_GAP_R0R3_BIT_OFFSET                24
#define RANK_SWITCH_TIMING_CONTROL2_T_WR2WR_GAP_R3R0_MASK              0xF0000000
#define RANK_SWITCH_TIMING_CONTROL2_T_WR2WR_GAP_R3R0_BIT_OFFSET                28

#define RANK_SWITCH_TIMING_CONTROL3                                    0x0000040C
#define RANK_SWITCH_TIMING_CONTROL3_T_RD2RD_GAP_R1R2_MASK              0x0000000F
#define RANK_SWITCH_TIMING_CONTROL3_T_RD2RD_GAP_R1R2_BIT_OFFSET                 0
#define RANK_SWITCH_TIMING_CONTROL3_T_RD2RD_GAP_R2R1_MASK              0x000000F0
#define RANK_SWITCH_TIMING_CONTROL3_T_RD2RD_GAP_R2R1_BIT_OFFSET                 4
#define RANK_SWITCH_TIMING_CONTROL3_T_WR2RD_GAP_R1R2_MASK              0x00000F00
#define RANK_SWITCH_TIMING_CONTROL3_T_WR2RD_GAP_R1R2_BIT_OFFSET                 8
#define RANK_SWITCH_TIMING_CONTROL3_T_WR2RD_GAP_R2R1_MASK              0x0000F000
#define RANK_SWITCH_TIMING_CONTROL3_T_WR2RD_GAP_R2R1_BIT_OFFSET                12
#define RANK_SWITCH_TIMING_CONTROL3_T_RD2WR_GAP_R1R2_MASK              0x000F0000
#define RANK_SWITCH_TIMING_CONTROL3_T_RD2WR_GAP_R1R2_BIT_OFFSET                16
#define RANK_SWITCH_TIMING_CONTROL3_T_RD2WR_GAP_R2R1_MASK              0x00F00000
#define RANK_SWITCH_TIMING_CONTROL3_T_RD2WR_GAP_R2R1_BIT_OFFSET                20
#define RANK_SWITCH_TIMING_CONTROL3_T_WR2WR_GAP_R1R2_MASK              0x0F000000
#define RANK_SWITCH_TIMING_CONTROL3_T_WR2WR_GAP_R1R2_BIT_OFFSET                24
#define RANK_SWITCH_TIMING_CONTROL3_T_WR2WR_GAP_R2R1_MASK              0xF0000000
#define RANK_SWITCH_TIMING_CONTROL3_T_WR2WR_GAP_R2R1_BIT_OFFSET                28

#define RANK_SWITCH_TIMING_CONTROL4                                    0x00000410
#define RANK_SWITCH_TIMING_CONTROL4_T_RD2RD_GAP_R1R3_MASK              0x0000000F
#define RANK_SWITCH_TIMING_CONTROL4_T_RD2RD_GAP_R1R3_BIT_OFFSET                 0
#define RANK_SWITCH_TIMING_CONTROL4_T_RD2RD_GAP_R3R1_MASK              0x000000F0
#define RANK_SWITCH_TIMING_CONTROL4_T_RD2RD_GAP_R3R1_BIT_OFFSET                 4
#define RANK_SWITCH_TIMING_CONTROL4_T_WR2RD_GAP_R1R3_MASK              0x00000F00
#define RANK_SWITCH_TIMING_CONTROL4_T_WR2RD_GAP_R1R3_BIT_OFFSET                 8
#define RANK_SWITCH_TIMING_CONTROL4_T_WR2RD_GAP_R3R1_MASK              0x0000F000
#define RANK_SWITCH_TIMING_CONTROL4_T_WR2RD_GAP_R3R1_BIT_OFFSET                12
#define RANK_SWITCH_TIMING_CONTROL4_T_RD2WR_GAP_R1R3_MASK              0x000F0000
#define RANK_SWITCH_TIMING_CONTROL4_T_RD2WR_GAP_R1R3_BIT_OFFSET                16
#define RANK_SWITCH_TIMING_CONTROL4_T_RD2WR_GAP_R3R1_MASK              0x00F00000
#define RANK_SWITCH_TIMING_CONTROL4_T_RD2WR_GAP_R3R1_BIT_OFFSET                20
#define RANK_SWITCH_TIMING_CONTROL4_T_WR2WR_GAP_R1R3_MASK              0x0F000000
#define RANK_SWITCH_TIMING_CONTROL4_T_WR2WR_GAP_R1R3_BIT_OFFSET                24
#define RANK_SWITCH_TIMING_CONTROL4_T_WR2WR_GAP_R3R1_MASK              0xF0000000
#define RANK_SWITCH_TIMING_CONTROL4_T_WR2WR_GAP_R3R1_BIT_OFFSET                28

#define RANK_SWITCH_TIMING_CONTROL5                                    0x00000414
#define RANK_SWITCH_TIMING_CONTROL5_T_RD2RD_GAP_R2R3_MASK              0x0000000F
#define RANK_SWITCH_TIMING_CONTROL5_T_RD2RD_GAP_R2R3_BIT_OFFSET                 0
#define RANK_SWITCH_TIMING_CONTROL5_T_RD2RD_GAP_R3R2_MASK              0x000000F0
#define RANK_SWITCH_TIMING_CONTROL5_T_RD2RD_GAP_R3R2_BIT_OFFSET                 4
#define RANK_SWITCH_TIMING_CONTROL5_T_WR2RD_GAP_R2R3_MASK              0x00000F00
#define RANK_SWITCH_TIMING_CONTROL5_T_WR2RD_GAP_R2R3_BIT_OFFSET                 8
#define RANK_SWITCH_TIMING_CONTROL5_T_WR2RD_GAP_R3R2_MASK              0x0000F000
#define RANK_SWITCH_TIMING_CONTROL5_T_WR2RD_GAP_R3R2_BIT_OFFSET                12
#define RANK_SWITCH_TIMING_CONTROL5_T_RD2WR_GAP_R2R3_MASK              0x000F0000
#define RANK_SWITCH_TIMING_CONTROL5_T_RD2WR_GAP_R2R3_BIT_OFFSET                16
#define RANK_SWITCH_TIMING_CONTROL5_T_RD2WR_GAP_R3R2_MASK              0x00F00000
#define RANK_SWITCH_TIMING_CONTROL5_T_RD2WR_GAP_R3R2_BIT_OFFSET                20
#define RANK_SWITCH_TIMING_CONTROL5_T_WR2WR_GAP_R2R3_MASK              0x0F000000
#define RANK_SWITCH_TIMING_CONTROL5_T_WR2WR_GAP_R2R3_BIT_OFFSET                24
#define RANK_SWITCH_TIMING_CONTROL5_T_WR2WR_GAP_R3R2_MASK              0xF0000000
#define RANK_SWITCH_TIMING_CONTROL5_T_WR2WR_GAP_R3R2_BIT_OFFSET                28

#define MRAMTMG0                                                       0x00000480
#define MRAMTMG0_T_RAS_MIN_MRAM_MASK                                   0x000000FF
#define MRAMTMG0_T_RAS_MIN_MRAM_BIT_OFFSET                                      0
#define MRAMTMG0_T_FAW_MRAM_MASK                                       0x03FF0000
#define MRAMTMG0_T_FAW_MRAM_BIT_OFFSET                                         16

#define MRAMTMG1                                                       0x00000484
#define MRAMTMG1_T_RC_MRAM_MASK                                        0x000001FF
#define MRAMTMG1_T_RC_MRAM_BIT_OFFSET                                           0

#define MRAMTMG2                                                       0x00000488
#define MRAMTMG2_T_RP_MRAM_MASK                                        0x0000007F
#define MRAMTMG2_T_RP_MRAM_BIT_OFFSET                                           0
#define MRAMTMG2_T_RRD_MRAM_MASK                                       0x00003F00
#define MRAMTMG2_T_RRD_MRAM_BIT_OFFSET                                          8
#define MRAMTMG2_T_RCD_MRAM_MASK                                       0xFF000000
#define MRAMTMG2_T_RCD_MRAM_BIT_OFFSET                                         24

#define MRAMTMG3                                                       0x0000048C
#define MRAMTMG3_T_RRD_S_MRAM_MASK                                     0x00003F00
#define MRAMTMG3_T_RRD_S_MRAM_BIT_OFFSET                                        8

#define INITMR0                                                        0x00000500
#define INITMR0_EMR_MASK                                               0x0000FFFF
#define INITMR0_EMR_BIT_OFFSET                                                  0
#define INITMR0_MR_MASK                                                0xFFFF0000
#define INITMR0_MR_BIT_OFFSET                                                  16

#define INITMR1                                                        0x00000504
#define INITMR1_EMR3_MASK                                              0x0000FFFF
#define INITMR1_EMR3_BIT_OFFSET                                                 0
#define INITMR1_EMR2_MASK                                              0xFFFF0000
#define INITMR1_EMR2_BIT_OFFSET                                                16

#define INITMR2                                                        0x00000508
#define INITMR2_MR5_MASK                                               0x0000FFFF
#define INITMR2_MR5_BIT_OFFSET                                                  0
#define INITMR2_MR4_MASK                                               0xFFFF0000
#define INITMR2_MR4_BIT_OFFSET                                                 16

#define INITMR3                                                        0x0000050C
#define INITMR3_MR6_MASK                                               0x0000FFFF
#define INITMR3_MR6_BIT_OFFSET                                                  0
#define INITMR3_MR22_MASK                                              0xFFFF0000
#define INITMR3_MR22_BIT_OFFSET                                                16

#define DFITMG0                                                        0x00000580
#define DFITMG0_DFI_TPHY_WRLAT_MASK                                    0x0000007F
#define DFITMG0_DFI_TPHY_WRLAT_BIT_OFFSET                                       0
#define DFITMG0_DFI_TPHY_WRDATA_MASK                                   0x00003F00
#define DFITMG0_DFI_TPHY_WRDATA_BIT_OFFSET                                      8
#define DFITMG0_DFI_T_RDDATA_EN_MASK                                   0x007F0000
#define DFITMG0_DFI_T_RDDATA_EN_BIT_OFFSET                                     16
#define DFITMG0_DFI_T_CTRL_DELAY_MASK                                  0x1F000000
#define DFITMG0_DFI_T_CTRL_DELAY_BIT_OFFSET                                    24

#define DFITMG1                                                        0x00000584
#define DFITMG1_DFI_T_DRAM_CLK_ENABLE_MASK                             0x0000001F
#define DFITMG1_DFI_T_DRAM_CLK_ENABLE_BIT_OFFSET                                0
#define DFITMG1_DFI_T_DRAM_CLK_DISABLE_MASK                            0x00001F00
#define DFITMG1_DFI_T_DRAM_CLK_DISABLE_BIT_OFFSET                               8
#define DFITMG1_DFI_T_WRDATA_DELAY_MASK                                0x001F0000
#define DFITMG1_DFI_T_WRDATA_DELAY_BIT_OFFSET                                  16
#define DFITMG1_DFI_T_PARIN_LAT_MASK                                   0x03000000
#define DFITMG1_DFI_T_PARIN_LAT_BIT_OFFSET                                     24
#define DFITMG1_DFI_T_CMD_LAT_MASK                                     0xF0000000
#define DFITMG1_DFI_T_CMD_LAT_BIT_OFFSET                                       28

#define DFITMG2                                                        0x00000588
#define DFITMG2_DFI_TPHY_WRCSLAT_MASK                                  0x0000007F
#define DFITMG2_DFI_TPHY_WRCSLAT_BIT_OFFSET                                     0
#define DFITMG2_DFI_TPHY_RDCSLAT_MASK                                  0x00007F00
#define DFITMG2_DFI_TPHY_RDCSLAT_BIT_OFFSET                                     8
#define DFITMG2_DFI_TWCK_DELAY_MASK                                    0x003F0000
#define DFITMG2_DFI_TWCK_DELAY_BIT_OFFSET                                      16

#define DFITMG3                                                        0x0000058C
#define DFITMG3_DFI_T_GEARDOWN_DELAY_MASK                              0x0000001F
#define DFITMG3_DFI_T_GEARDOWN_DELAY_BIT_OFFSET                                 0

#define DFITMG4                                                        0x00000590
#define DFITMG4_DFI_TWCK_DIS_MASK                                      0x000000FF
#define DFITMG4_DFI_TWCK_DIS_BIT_OFFSET                                         0
#define DFITMG4_DFI_TWCK_EN_FS_MASK                                    0x0000FF00
#define DFITMG4_DFI_TWCK_EN_FS_BIT_OFFSET                                       8
#define DFITMG4_DFI_TWCK_EN_WR_MASK                                    0x00FF0000
#define DFITMG4_DFI_TWCK_EN_WR_BIT_OFFSET                                      16
#define DFITMG4_DFI_TWCK_EN_RD_MASK                                    0xFF000000
#define DFITMG4_DFI_TWCK_EN_RD_BIT_OFFSET                                      24

#define DFITMG5                                                        0x00000594
#define DFITMG5_DFI_TWCK_TOGGLE_POST_MASK                              0x000000FF
#define DFITMG5_DFI_TWCK_TOGGLE_POST_BIT_OFFSET                                 0
#define DFITMG5_DFI_TWCK_TOGGLE_CS_MASK                                0x0000FF00
#define DFITMG5_DFI_TWCK_TOGGLE_CS_BIT_OFFSET                                   8
#define DFITMG5_DFI_TWCK_TOGGLE_MASK                                   0x00FF0000
#define DFITMG5_DFI_TWCK_TOGGLE_BIT_OFFSET                                     16
#define DFITMG5_DFI_TWCK_FAST_TOGGLE_MASK                              0xFF000000
#define DFITMG5_DFI_TWCK_FAST_TOGGLE_BIT_OFFSET                                24

#define DFITMG6                                                        0x00000598
#define DFITMG6_DFI_TWCK_TOGGLE_POST_RD_MASK                           0x000000FF
#define DFITMG6_DFI_TWCK_TOGGLE_POST_RD_BIT_OFFSET                              0
#define DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN_MASK                        0x00000100
#define DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN_BIT_OFFSET                           8

#define DFITMG7                                                        0x0000059C
#define DFITMG7_DFI_T_2N_MODE_DELAY_MASK                               0x0000001F
#define DFITMG7_DFI_T_2N_MODE_DELAY_BIT_OFFSET                                  0
#define DFITMG7_DFI_T_INIT_START_MASK                                  0x0001FFE0
#define DFITMG7_DFI_T_INIT_START_BIT_OFFSET                                     5
#define DFITMG7_DFI_T_INIT_COMPLETE_MASK                               0xFFFE0000
#define DFITMG7_DFI_T_INIT_COMPLETE_BIT_OFFSET                                 17

#define DFILPTMG0                                                      0x000005A0
#define DFILPTMG0_DFI_LP_WAKEUP_PD_MASK                                0x0000001F
#define DFILPTMG0_DFI_LP_WAKEUP_PD_BIT_OFFSET                                   0
#define DFILPTMG0_DFI_LP_WAKEUP_SR_MASK                                0x00001F00
#define DFILPTMG0_DFI_LP_WAKEUP_SR_BIT_OFFSET                                   8
#define DFILPTMG0_DFI_LP_WAKEUP_DSM_MASK                               0x001F0000
#define DFILPTMG0_DFI_LP_WAKEUP_DSM_BIT_OFFSET                                 16
#define DFILPTMG0_DFI_LP_WAKEUP_MPSM_MASK                              0x1F000000
#define DFILPTMG0_DFI_LP_WAKEUP_MPSM_BIT_OFFSET                                24

#define DFILPTMG1                                                      0x000005A4
#define DFILPTMG1_DFI_LP_WAKEUP_DATA_MASK                              0x0000001F
#define DFILPTMG1_DFI_LP_WAKEUP_DATA_BIT_OFFSET                                 0
#define DFILPTMG1_DFI_TLP_RESP_MASK                                    0x00001F00
#define DFILPTMG1_DFI_TLP_RESP_BIT_OFFSET                                       8

#define DFIUPDTMG0                                                     0x000005A8
#define DFIUPDTMG0_DFI_T_CTRLUP_MIN_MASK                               0x000003FF
#define DFIUPDTMG0_DFI_T_CTRLUP_MIN_BIT_OFFSET                                  0
#define DFIUPDTMG0_DFI_T_CTRLUP_MAX_MASK                               0x03FF0000
#define DFIUPDTMG0_DFI_T_CTRLUP_MAX_BIT_OFFSET                                 16
#define DFIUPDTMG0_DFI_CTRLUP_GAP_MASK                                 0xFC000000
#define DFIUPDTMG0_DFI_CTRLUP_GAP_BIT_OFFSET                                   26

#define DFIUPDTMG1                                                     0x000005AC
#define DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024_MASK               0x000000FF
#define DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024_BIT_OFFSET                  0
#define DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024_MASK               0x00FF0000
#define DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024_BIT_OFFSET                 16

#define DFIMSGTMG0                                                     0x000005B0
#define DFIMSGTMG0_DFI_T_CTRLMSG_RESP_MASK                             0x000000FF
#define DFIMSGTMG0_DFI_T_CTRLMSG_RESP_BIT_OFFSET                                0

#define DFIUPDTMG2                                                     0x000005B4
#define DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_MASK                   0x00000FFF
#define DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_BIT_OFFSET                      0
#define DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC_MASK                           0x08000000
#define DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC_BIT_OFFSET                             27
#define DFIUPDTMG2_PPT2_OVERRIDE_MASK                                  0x10000000
#define DFIUPDTMG2_PPT2_OVERRIDE_BIT_OFFSET                                    28
#define DFIUPDTMG2_PPT2_EN_MASK                                        0x20000000
#define DFIUPDTMG2_PPT2_EN_BIT_OFFSET                                          29
#define DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_MASK              0xC0000000
#define DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_BIT_OFFSET                30

#define DFIUPDTMG3                                                     0x000005B8
#define DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8_MASK                0x000001FF
#define DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8_BIT_OFFSET                   0

#define RFSHSET1TMG0                                                   0x00000600
#define RFSHSET1TMG0_T_REFI_X1_X32_MASK                                0x0000FFFF
#define RFSHSET1TMG0_T_REFI_X1_X32_BIT_OFFSET                                   0
#define RFSHSET1TMG0_REFRESH_TO_X1_X32_MASK                            0x003F0000
#define RFSHSET1TMG0_REFRESH_TO_X1_X32_BIT_OFFSET                              16
#define RFSHSET1TMG0_REFRESH_MARGIN_MASK                               0x0F000000
#define RFSHSET1TMG0_REFRESH_MARGIN_BIT_OFFSET                                 24
#define RFSHSET1TMG0_REFRESH_TO_X1_SEL_MASK                            0x40000000
#define RFSHSET1TMG0_REFRESH_TO_X1_SEL_BIT_OFFSET                              30
#define RFSHSET1TMG0_T_REFI_X1_SEL_MASK                                0x80000000
#define RFSHSET1TMG0_T_REFI_X1_SEL_BIT_OFFSET                                  31

#define RFSHSET1TMG1                                                   0x00000604
#define RFSHSET1TMG1_T_RFC_MIN_MASK                                    0x00000FFF
#define RFSHSET1TMG1_T_RFC_MIN_BIT_OFFSET                                       0
#define RFSHSET1TMG1_T_RFC_MIN_AB_MASK                                 0x0FFF0000
#define RFSHSET1TMG1_T_RFC_MIN_AB_BIT_OFFSET                                   16

#define RFSHSET1TMG2                                                   0x00000608
#define RFSHSET1TMG2_T_RFC_MIN_DLR_MASK                                0x000003FF
#define RFSHSET1TMG2_T_RFC_MIN_DLR_BIT_OFFSET                                   0
#define RFSHSET1TMG2_T_PBR2PBR_MASK                                    0x00FF0000
#define RFSHSET1TMG2_T_PBR2PBR_BIT_OFFSET                                      16
#define RFSHSET1TMG2_T_PBR2ACT_MASK                                    0xFF000000
#define RFSHSET1TMG2_T_PBR2ACT_BIT_OFFSET                                      24

#define RFSHSET1TMG3                                                   0x0000060C
#define RFSHSET1TMG3_T_RFCSB_MASK                                      0x00000FFF
#define RFSHSET1TMG3_T_RFCSB_BIT_OFFSET                                         0
#define RFSHSET1TMG3_T_REFSBRD_MASK                                    0x00FF0000
#define RFSHSET1TMG3_T_REFSBRD_BIT_OFFSET                                      16
#define RFSHSET1TMG3_REFRESH_TO_AB_X32_MASK                            0x3F000000
#define RFSHSET1TMG3_REFRESH_TO_AB_X32_BIT_OFFSET                              24

#define RFSHSET1TMG4                                                   0x00000610
#define RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32_MASK               0x00000FFF
#define RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32_BIT_OFFSET                  0
#define RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32_MASK               0x0FFF0000
#define RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32_BIT_OFFSET                 16

#define RFSHSET1TMG5                                                   0x00000614
#define RFSHSET1TMG5_REFRESH_TIMER2_START_VALUE_X32_MASK               0x00000FFF
#define RFSHSET1TMG5_REFRESH_TIMER2_START_VALUE_X32_BIT_OFFSET                  0
#define RFSHSET1TMG5_REFRESH_TIMER3_START_VALUE_X32_MASK               0x0FFF0000
#define RFSHSET1TMG5_REFRESH_TIMER3_START_VALUE_X32_BIT_OFFSET                 16

#define RFSHSET1TMG6                                                   0x00000618
#define RFSHSET1TMG6_REFRESH_TIMER_LR_OFFSET_X32_MASK                  0x000007FF
#define RFSHSET1TMG6_REFRESH_TIMER_LR_OFFSET_X32_BIT_OFFSET                     0

#define RFSHSET1TMG7                                                   0x0000061C
#define RFSHSET1TMG7_T_RFCSB_DLR_MASK                                  0x00000FFF
#define RFSHSET1TMG7_T_RFCSB_DLR_BIT_OFFSET                                     0
#define RFSHSET1TMG7_T_REFSBRD_DLR_MASK                                0x00FF0000
#define RFSHSET1TMG7_T_REFSBRD_DLR_BIT_OFFSET                                  16

#define RFSHSET1TMG8                                                   0x00000620
#define RFSHSET1TMG8_T_RFC_MIN_HET_MASK                                0x000007FF
#define RFSHSET1TMG8_T_RFC_MIN_HET_BIT_OFFSET                                   0

#define RFSHSET1TMG9                                                   0x00000624
#define RFSHSET1TMG9_REFAB_HI_SCH_GAP_MASK                             0x00001FFF
#define RFSHSET1TMG9_REFAB_HI_SCH_GAP_BIT_OFFSET                                0
#define RFSHSET1TMG9_REFSB_HI_SCH_GAP_MASK                             0x0FFF0000
#define RFSHSET1TMG9_REFSB_HI_SCH_GAP_BIT_OFFSET                               16

#define RFSHSET1TMG10                                                  0x00000628
#define RFSHSET1TMG10_T_WIN_SIZE_1XTREFI_MASK                          0x00000FFF
#define RFSHSET1TMG10_T_WIN_SIZE_1XTREFI_BIT_OFFSET                             0

#define RFSHSET1TMG11                                                  0x0000062C
#define RFSHSET1TMG11_T_PBR2PBR_MP_MASK                                0x00FF0000
#define RFSHSET1TMG11_T_PBR2PBR_MP_BIT_OFFSET                                  16

#define RFSHSET1TMG12                                                  0x00000630
#define RFSHSET1TMG12_T_RFC_MIN_MP_MASK                                0x00000FFF
#define RFSHSET1TMG12_T_RFC_MIN_MP_BIT_OFFSET                                   0
#define RFSHSET1TMG12_T_RFC_MIN_AB_MP_MASK                             0x0FFF0000
#define RFSHSET1TMG12_T_RFC_MIN_AB_MP_BIT_OFFSET                               16

#define ECSSET1TMG0                                                    0x00000640
#define ECSSET1TMG0_T_ECS_INT_X1024_MASK                               0x00001FFF
#define ECSSET1TMG0_T_ECS_INT_X1024_BIT_OFFSET                                  0
#define ECSSET1TMG0_T_REFI_ECS_OFFSET_X1_X32_MASK                      0x00FF0000
#define ECSSET1TMG0_T_REFI_ECS_OFFSET_X1_X32_BIT_OFFSET                        16

#define RFMSET1TMG0                                                    0x00000650
#define RFMSET1TMG0_T_RFMPB_MASK                                       0x00000FFF
#define RFMSET1TMG0_T_RFMPB_BIT_OFFSET                                          0

#define RFMSET1TMG1                                                    0x00000654
#define RFMSET1TMG1_T_RFMPB_MP_MASK                                    0x00000FFF
#define RFMSET1TMG1_T_RFMPB_MP_BIT_OFFSET                                       0

#define RFSHSET2TMG0                                                   0x00000680
#define RFSHSET2TMG0_T_REFI_X1_X32_2_MASK                              0x00000FFF
#define RFSHSET2TMG0_T_REFI_X1_X32_2_BIT_OFFSET                                 0
#define RFSHSET2TMG0_REFRESH_TO_X1_X32_2_MASK                          0x003F0000
#define RFSHSET2TMG0_REFRESH_TO_X1_X32_2_BIT_OFFSET                            16
#define RFSHSET2TMG0_REFRESH_MARGIN_2_MASK                             0x0F000000
#define RFSHSET2TMG0_REFRESH_MARGIN_2_BIT_OFFSET                               24

#define RFSHSET2TMG1                                                   0x00000684
#define RFSHSET2TMG1_T_RFC_MIN_2_MASK                                  0x00000FFF
#define RFSHSET2TMG1_T_RFC_MIN_2_BIT_OFFSET                                     0

#define RFSHSET2TMG2                                                   0x00000688
#define RFSHSET2TMG2_T_RFC_MIN_DLR_2_MASK                              0x000003FF
#define RFSHSET2TMG2_T_RFC_MIN_DLR_2_BIT_OFFSET                                 0

#define RFSHSET2TMG3                                                   0x0000068C
#define RFSHSET2TMG3_T_RFCSB_2_MASK                                    0x00000FFF
#define RFSHSET2TMG3_T_RFCSB_2_BIT_OFFSET                                       0
#define RFSHSET2TMG3_T_REFSBRD_2_MASK                                  0x00FF0000
#define RFSHSET2TMG3_T_REFSBRD_2_BIT_OFFSET                                    16

#define RFSHSET2TMG6                                                   0x00000698
#define RFSHSET2TMG6_REFRESH_TIMER_LR_OFFSET_X32_2_MASK                0x000007FF
#define RFSHSET2TMG6_REFRESH_TIMER_LR_OFFSET_X32_2_BIT_OFFSET                   0

#define RFSHSET2TMG7                                                   0x0000069C
#define RFSHSET2TMG7_T_RFCSB_DLR_2_MASK                                0x00000FFF
#define RFSHSET2TMG7_T_RFCSB_DLR_2_BIT_OFFSET                                   0
#define RFSHSET2TMG7_T_REFSBRD_DLR_2_MASK                              0x00FF0000
#define RFSHSET2TMG7_T_REFSBRD_DLR_2_BIT_OFFSET                                16

#define RFSHSET2TMG9                                                   0x000006A4
#define RFSHSET2TMG9_REFAB_HI_SCH_GAP_2_MASK                           0x00001FFF
#define RFSHSET2TMG9_REFAB_HI_SCH_GAP_2_BIT_OFFSET                              0
#define RFSHSET2TMG9_REFSB_HI_SCH_GAP_2_MASK                           0x0FFF0000
#define RFSHSET2TMG9_REFSB_HI_SCH_GAP_2_BIT_OFFSET                             16

#define RFSHSET2TMG10                                                  0x000006A8
#define RFSHSET2TMG10_T_WIN_SIZE_1XTREFI_2_MASK                        0x00000FFF
#define RFSHSET2TMG10_T_WIN_SIZE_1XTREFI_2_BIT_OFFSET                           0

#define ECSSET2TMG0                                                    0x000006C0
#define ECSSET2TMG0_T_ECS_INT_X1024_2_MASK                             0x00001FFF
#define ECSSET2TMG0_T_ECS_INT_X1024_2_BIT_OFFSET                                0
#define ECSSET2TMG0_T_REFI_ECS_OFFSET_X1_X32_2_MASK                    0x00FF0000
#define ECSSET2TMG0_T_REFI_ECS_OFFSET_X1_X32_2_BIT_OFFSET                      16

#define ZQSET1TMG0                                                     0x00000800
#define ZQSET1TMG0_T_ZQ_LONG_NOP_MASK                                  0x00003FFF
#define ZQSET1TMG0_T_ZQ_LONG_NOP_BIT_OFFSET                                     0
#define ZQSET1TMG0_T_ZQ_SHORT_NOP_MASK                                 0x03FF0000
#define ZQSET1TMG0_T_ZQ_SHORT_NOP_BIT_OFFSET                                   16

#define ZQSET1TMG1                                                     0x00000804
#define ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024_MASK                      0x000FFFFF
#define ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024_BIT_OFFSET                         0
#define ZQSET1TMG1_T_ZQ_RESET_NOP_MASK                                 0x3FF00000
#define ZQSET1TMG1_T_ZQ_RESET_NOP_BIT_OFFSET                                   20

#define ZQSET1TMG2                                                     0x00000808
#define ZQSET1TMG2_T_ZQ_STOP_MASK                                      0x0000007F
#define ZQSET1TMG2_T_ZQ_STOP_BIT_OFFSET                                         0

#define ZQSET2TMG0                                                     0x00000880
#define ZQSET2TMG0_T_ZQ_LONG_NOP_2_MASK                                0x00003FFF
#define ZQSET2TMG0_T_ZQ_LONG_NOP_2_BIT_OFFSET                                   0
#define ZQSET2TMG0_T_ZQ_SHORT_NOP_2_MASK                               0x03FF0000
#define ZQSET2TMG0_T_ZQ_SHORT_NOP_2_BIT_OFFSET                                 16

#define RCDINIT1                                                       0x00000A00
#define RCDINIT1_CTRL_WORD_1_MASK                                      0x00001FFF
#define RCDINIT1_CTRL_WORD_1_BIT_OFFSET                                         0
#define RCDINIT1_CTRL_WORD_2_MASK                                      0x1FFF0000
#define RCDINIT1_CTRL_WORD_2_BIT_OFFSET                                        16

#define RCDINIT2                                                       0x00000A04
#define RCDINIT2_CTRL_WORD_3_MASK                                      0x00001FFF
#define RCDINIT2_CTRL_WORD_3_BIT_OFFSET                                         0
#define RCDINIT2_CTRL_WORD_4_MASK                                      0x1FFF0000
#define RCDINIT2_CTRL_WORD_4_BIT_OFFSET                                        16

#define RCDINIT3                                                       0x00000A08
#define RCDINIT3_CTRL_WORD_5_MASK                                      0x00001FFF
#define RCDINIT3_CTRL_WORD_5_BIT_OFFSET                                         0
#define RCDINIT3_CTRL_WORD_6_MASK                                      0x1FFF0000
#define RCDINIT3_CTRL_WORD_6_BIT_OFFSET                                        16

#define RCDINIT4                                                       0x00000A0C
#define RCDINIT4_CTRL_WORD_7_MASK                                      0x00001FFF
#define RCDINIT4_CTRL_WORD_7_BIT_OFFSET                                         0
#define RCDINIT4_CTRL_WORD_8_MASK                                      0x1FFF0000
#define RCDINIT4_CTRL_WORD_8_BIT_OFFSET                                        16

#define HWFFCEX_RANK1                                                  0x00000A10
#define HWFFCEX_RANK1_RANK1_MR1_RTT_NOM_MASK                           0x00000007
#define HWFFCEX_RANK1_RANK1_MR1_RTT_NOM_BIT_OFFSET                              0
#define HWFFCEX_RANK1_RANK1_MR2_RTT_WR_MASK                            0x00000700
#define HWFFCEX_RANK1_RANK1_MR2_RTT_WR_BIT_OFFSET                               8
#define HWFFCEX_RANK1_RANK1_MR5_RTT_PARK_MASK                          0x00070000
#define HWFFCEX_RANK1_RANK1_MR5_RTT_PARK_BIT_OFFSET                            16
#define HWFFCEX_RANK1_RANK1_MR6_VREF_VALUE_MASK                        0x3F000000
#define HWFFCEX_RANK1_RANK1_MR6_VREF_VALUE_BIT_OFFSET                          24
#define HWFFCEX_RANK1_RANK1_MR6_VREF_RANGE_MASK                        0x40000000
#define HWFFCEX_RANK1_RANK1_MR6_VREF_RANGE_BIT_OFFSET                          30

#define HWFFCEX_RANK2                                                  0x00000A14
#define HWFFCEX_RANK2_RANK2_MR1_RTT_NOM_MASK                           0x00000007
#define HWFFCEX_RANK2_RANK2_MR1_RTT_NOM_BIT_OFFSET                              0
#define HWFFCEX_RANK2_RANK2_MR2_RTT_WR_MASK                            0x00000700
#define HWFFCEX_RANK2_RANK2_MR2_RTT_WR_BIT_OFFSET                               8
#define HWFFCEX_RANK2_RANK2_MR5_RTT_PARK_MASK                          0x00070000
#define HWFFCEX_RANK2_RANK2_MR5_RTT_PARK_BIT_OFFSET                            16
#define HWFFCEX_RANK2_RANK2_MR6_VREF_VALUE_MASK                        0x3F000000
#define HWFFCEX_RANK2_RANK2_MR6_VREF_VALUE_BIT_OFFSET                          24
#define HWFFCEX_RANK2_RANK2_MR6_VREF_RANGE_MASK                        0x40000000
#define HWFFCEX_RANK2_RANK2_MR6_VREF_RANGE_BIT_OFFSET                          30

#define HWFFCEX_RANK3                                                  0x00000A18
#define HWFFCEX_RANK3_RANK3_MR1_RTT_NOM_MASK                           0x00000007
#define HWFFCEX_RANK3_RANK3_MR1_RTT_NOM_BIT_OFFSET                              0
#define HWFFCEX_RANK3_RANK3_MR2_RTT_WR_MASK                            0x00000700
#define HWFFCEX_RANK3_RANK3_MR2_RTT_WR_BIT_OFFSET                               8
#define HWFFCEX_RANK3_RANK3_MR5_RTT_PARK_MASK                          0x00070000
#define HWFFCEX_RANK3_RANK3_MR5_RTT_PARK_BIT_OFFSET                            16
#define HWFFCEX_RANK3_RANK3_MR6_VREF_VALUE_MASK                        0x3F000000
#define HWFFCEX_RANK3_RANK3_MR6_VREF_VALUE_BIT_OFFSET                          24
#define HWFFCEX_RANK3_RANK3_MR6_VREF_RANGE_MASK                        0x40000000
#define HWFFCEX_RANK3_RANK3_MR6_VREF_RANGE_BIT_OFFSET                          30

#define DQSOSCCTL0                                                     0x00000A80
#define DQSOSCCTL0_DQSOSC_ENABLE_MASK                                  0x00000001
#define DQSOSCCTL0_DQSOSC_ENABLE_BIT_OFFSET                                     0
#define DQSOSCCTL0_DQSOSC_INTERVAL_UNIT_MASK                           0x00000004
#define DQSOSCCTL0_DQSOSC_INTERVAL_UNIT_BIT_OFFSET                              2
#define DQSOSCCTL0_DQSOSC_INTERVAL_MASK                                0x0000FFF0
#define DQSOSCCTL0_DQSOSC_INTERVAL_BIT_OFFSET                                   4

#define DERATEINT                                                      0x00000B00
#define DERATEINT_MR4_READ_INTERVAL_MASK                               0xFFFFFFFF
#define DERATEINT_MR4_READ_INTERVAL_BIT_OFFSET                                  0

#define DERATEVAL0                                                     0x00000B04
#define DERATEVAL0_DERATED_T_RRD_MASK                                  0x0000003F
#define DERATEVAL0_DERATED_T_RRD_BIT_OFFSET                                     0
#define DERATEVAL0_DERATED_T_RP_MASK                                   0x00007F00
#define DERATEVAL0_DERATED_T_RP_BIT_OFFSET                                      8
#define DERATEVAL0_DERATED_T_RAS_MIN_MASK                              0x00FF0000
#define DERATEVAL0_DERATED_T_RAS_MIN_BIT_OFFSET                                16
#define DERATEVAL0_DERATED_T_RCD_MASK                                  0xFF000000
#define DERATEVAL0_DERATED_T_RCD_BIT_OFFSET                                    24

#define DERATEVAL1                                                     0x00000B08
#define DERATEVAL1_DERATED_T_RC_MASK                                   0x000000FF
#define DERATEVAL1_DERATED_T_RC_BIT_OFFSET                                      0
#define DERATEVAL1_DERATED_T_RCD_WRITE_MASK                            0x0000FF00
#define DERATEVAL1_DERATED_T_RCD_WRITE_BIT_OFFSET                               8

#define HWLPTMG0                                                       0x00000B80
#define HWLPTMG0_HW_LP_IDLE_X32_MASK                                   0x0FFF0000
#define HWLPTMG0_HW_LP_IDLE_X32_BIT_OFFSET                                     16

#define DVFSCTL0                                                       0x00000B84
#define DVFSCTL0_DVFSQ_ENABLE_MASK                                     0x00000004
#define DVFSCTL0_DVFSQ_ENABLE_BIT_OFFSET                                        2

#define SCHEDTMG0                                                      0x00000C00
#define SCHEDTMG0_PAGECLOSE_TIMER_MASK                                 0x000000FF
#define SCHEDTMG0_PAGECLOSE_TIMER_BIT_OFFSET                                    0
#define SCHEDTMG0_RDWR_IDLE_GAP_MASK                                   0x00007F00
#define SCHEDTMG0_RDWR_IDLE_GAP_BIT_OFFSET                                      8

#define PERFHPR1                                                       0x00000C80
#define PERFHPR1_HPR_MAX_STARVE_MASK                                   0x0000FFFF
#define PERFHPR1_HPR_MAX_STARVE_BIT_OFFSET                                      0
#define PERFHPR1_HPR_XACT_RUN_LENGTH_MASK                              0xFF000000
#define PERFHPR1_HPR_XACT_RUN_LENGTH_BIT_OFFSET                                24

#define PERFLPR1                                                       0x00000C84
#define PERFLPR1_LPR_MAX_STARVE_MASK                                   0x0000FFFF
#define PERFLPR1_LPR_MAX_STARVE_BIT_OFFSET                                      0
#define PERFLPR1_LPR_XACT_RUN_LENGTH_MASK                              0xFF000000
#define PERFLPR1_LPR_XACT_RUN_LENGTH_BIT_OFFSET                                24

#define PERFWR1                                                        0x00000C88
#define PERFWR1_W_MAX_STARVE_MASK                                      0x0000FFFF
#define PERFWR1_W_MAX_STARVE_BIT_OFFSET                                         0
#define PERFWR1_W_XACT_RUN_LENGTH_MASK                                 0xFF000000
#define PERFWR1_W_XACT_RUN_LENGTH_BIT_OFFSET                                   24

#define TMGCFG                                                         0x00000D00
#define TMGCFG_FREQUENCY_RATIO_MASK                                    0x00000001
#define TMGCFG_FREQUENCY_RATIO_BIT_OFFSET                                       0

#define RANKTMG0                                                       0x00000D04
#define RANKTMG0_DIFF_RANK_RD_GAP_MASK                                 0x000000FF
#define RANKTMG0_DIFF_RANK_RD_GAP_BIT_OFFSET                                    0
#define RANKTMG0_DIFF_RANK_WR_GAP_MASK                                 0x0000FF00
#define RANKTMG0_DIFF_RANK_WR_GAP_BIT_OFFSET                                    8

#define RANKTMG1                                                       0x00000D08
#define RANKTMG1_WR2RD_DR_MASK                                         0x000000FF
#define RANKTMG1_WR2RD_DR_BIT_OFFSET                                            0
#define RANKTMG1_RD2WR_DR_MASK                                         0x0000FF00
#define RANKTMG1_RD2WR_DR_BIT_OFFSET                                            8

#define PWRTMG                                                         0x00000D0C
#define PWRTMG_POWERDOWN_TO_X32_MASK                                   0x0000007F
#define PWRTMG_POWERDOWN_TO_X32_BIT_OFFSET                                      0
#define PWRTMG_SELFREF_TO_X32_MASK                                     0x03FF0000
#define PWRTMG_SELFREF_TO_X32_BIT_OFFSET                                       16

#define ODTCFG                                                         0x00000D10
#define ODTCFG_RD_ODT_DELAY_MASK                                       0x0000007C
#define ODTCFG_RD_ODT_DELAY_BIT_OFFSET                                          2
#define ODTCFG_RD_ODT_HOLD_MASK                                        0x00000F00
#define ODTCFG_RD_ODT_HOLD_BIT_OFFSET                                           8
#define ODTCFG_WR_ODT_DELAY_MASK                                       0x001F0000
#define ODTCFG_WR_ODT_DELAY_BIT_OFFSET                                         16
#define ODTCFG_WR_ODT_HOLD_MASK                                        0x0F000000
#define ODTCFG_WR_ODT_HOLD_BIT_OFFSET                                          24

#define CRCPARTMG0                                                     0x00000D14
#define CRCPARTMG0_T_WR_CRC_ALERT_PW_MAX_MASK                          0x03FF0000
#define CRCPARTMG0_T_WR_CRC_ALERT_PW_MAX_BIT_OFFSET                            16
#define CRCPARTMG0_T_WR_CRC_ALERT_PW_MIN_MASK                          0xF0000000
#define CRCPARTMG0_T_WR_CRC_ALERT_PW_MIN_BIT_OFFSET                            28

#define CRCPARTMG1                                                     0x00000D18
#define CRCPARTMG1_T_CSALT_MASK                                        0x0000001F
#define CRCPARTMG1_T_CSALT_BIT_OFFSET                                           0

#define RETRYTMG0                                                      0x00000D20
#define RETRYTMG0_CAPAR_RETRY_WINDOW_MASK                              0x0000003F
#define RETRYTMG0_CAPAR_RETRY_WINDOW_BIT_OFFSET                                 0
#define RETRYTMG0_T_WR_CRC_RETRY_WINDOW_MASK                           0x01FF0000
#define RETRYTMG0_T_WR_CRC_RETRY_WINDOW_BIT_OFFSET                             16

#define RETRYTMG1                                                      0x00000D24
#define RETRYTMG1_DFI_T_PHY_RDLAT_MASK                                 0x000000FF
#define RETRYTMG1_DFI_T_PHY_RDLAT_BIT_OFFSET                                    0
#define RETRYTMG1_EXTRA_RD_RETRY_WINDOW_MASK                           0x00003F00
#define RETRYTMG1_EXTRA_RD_RETRY_WINDOW_BIT_OFFSET                              8
#define RETRYTMG1_RETRY_ADD_RD_LAT_MASK                                0x00FF0000
#define RETRYTMG1_RETRY_ADD_RD_LAT_BIT_OFFSET                                  16
#define RETRYTMG1_RETRY_ADD_RD_LAT_EN_MASK                             0x01000000
#define RETRYTMG1_RETRY_ADD_RD_LAT_EN_BIT_OFFSET                               24

#define DDR4PPRTMG0                                                    0x00000D30
#define DDR4PPRTMG0_T_PGM_X1_X1024_MASK                                0x003FFFFF
#define DDR4PPRTMG0_T_PGM_X1_X1024_BIT_OFFSET                                   0
#define DDR4PPRTMG0_T_PGM_X1_SEL_MASK                                  0x80000000
#define DDR4PPRTMG0_T_PGM_X1_SEL_BIT_OFFSET                                    31

#define DDR4PPRTMG1                                                    0x00000D34
#define DDR4PPRTMG1_T_PGMPST_X32_MASK                                  0x0000FFFF
#define DDR4PPRTMG1_T_PGMPST_X32_BIT_OFFSET                                     0
#define DDR4PPRTMG1_T_PGM_EXIT_MASK                                    0x3F000000
#define DDR4PPRTMG1_T_PGM_EXIT_BIT_OFFSET                                      24

#define LNKECCCTL0                                                     0x00000D80
#define LNKECCCTL0_WR_LINK_ECC_ENABLE_MASK                             0x00000001
#define LNKECCCTL0_WR_LINK_ECC_ENABLE_BIT_OFFSET                                0
#define LNKECCCTL0_RD_LINK_ECC_ENABLE_MASK                             0x00000002
#define LNKECCCTL0_RD_LINK_ECC_ENABLE_BIT_OFFSET                                1

#define REG_GROUP_FREQ0_CH1                                            0x00001000

#define REG_GROUP_FREQ1_CH0                                            0x00100000

#define REG_GROUP_FREQ1_CH1                                            0x00101000

#define REG_GROUP_FREQ2_CH0                                            0x00200000

#define REG_GROUP_FREQ2_CH1                                            0x00201000

#define REG_GROUP_FREQ3_CH0                                            0x00300000

#define REG_GROUP_FREQ3_CH1                                            0x00301000

#define REG_GROUP_FREQ4_CH0                                            0x00400000

#define REG_GROUP_FREQ4_CH1                                            0x00401000

#define REG_GROUP_FREQ5_CH0                                            0x00500000

#define REG_GROUP_FREQ5_CH1                                            0x00501000

#define REG_GROUP_FREQ6_CH0                                            0x00600000

#define REG_GROUP_FREQ6_CH1                                            0x00601000

#define REG_GROUP_FREQ7_CH0                                            0x00700000

#define REG_GROUP_FREQ7_CH1                                            0x00701000

#define REG_GROUP_FREQ8_CH0                                            0x00800000

#define REG_GROUP_FREQ8_CH1                                            0x00801000

#define REG_GROUP_FREQ9_CH0                                            0x00900000

#define REG_GROUP_FREQ9_CH1                                            0x00901000

#define REG_GROUP_FREQ10_CH0                                           0x00A00000

#define REG_GROUP_FREQ10_CH1                                           0x00A01000

#define REG_GROUP_FREQ11_CH0                                           0x00B00000

#define REG_GROUP_FREQ11_CH1                                           0x00B01000

#define REG_GROUP_FREQ12_CH0                                           0x00C00000

#define REG_GROUP_FREQ12_CH1                                           0x00C01000

#define REG_GROUP_FREQ13_CH0                                           0x00D00000

#define REG_GROUP_FREQ13_CH1                                           0x00D01000

#define REG_GROUP_FREQ14_CH0                                           0x00E00000

#define REG_GROUP_FREQ14_CH1                                           0x00E01000

#define REG_GROUP_IME_CH0                                              0x000F0000

#define IME_VER_NUM                                                    0x00000000
#define IME_VER_NUM_VER_NUM_MASK                                       0x0000FFFF
#define IME_VER_NUM_VER_NUM_BIT_OFFSET                                          0

#define IME_VER_TYPE                                                   0x00000004
#define IME_VER_TYPE_TYPE_NUM_MASK                                     0x000000FF
#define IME_VER_TYPE_TYPE_NUM_BIT_OFFSET                                        0
#define IME_VER_TYPE_PKG_NUM_MASK                                      0x00000F00
#define IME_VER_TYPE_PKG_NUM_BIT_OFFSET                                         8
#define IME_VER_TYPE_TYPE_ENUM_MASK                                    0x0000F000
#define IME_VER_TYPE_TYPE_ENUM_BIT_OFFSET                                      12

#define IME_KEY_LOAD_IRQ_EN                                            0x00000008
#define IME_KEY_LOAD_IRQ_EN_KEY_DONE_EN_MASK                           0x00000001
#define IME_KEY_LOAD_IRQ_EN_KEY_DONE_EN_BIT_OFFSET                              0
#define IME_KEY_LOAD_IRQ_EN_KEY_MISS_ERR_EN_MASK                       0x00000040
#define IME_KEY_LOAD_IRQ_EN_KEY_MISS_ERR_EN_BIT_OFFSET                          6
#define IME_KEY_LOAD_IRQ_EN_KEY_COLLISION_ERR_EN_MASK                  0x00000080
#define IME_KEY_LOAD_IRQ_EN_KEY_COLLISION_ERR_EN_BIT_OFFSET                     7
#define IME_KEY_LOAD_IRQ_EN_APB_TIMING_ERR_EN_MASK                     0x00000100
#define IME_KEY_LOAD_IRQ_EN_APB_TIMING_ERR_EN_BIT_OFFSET                        8
#define IME_KEY_LOAD_IRQ_EN_KEY_SIZE_ERR_EN_MASK                       0x00000200
#define IME_KEY_LOAD_IRQ_EN_KEY_SIZE_ERR_EN_BIT_OFFSET                          9
#define IME_KEY_LOAD_IRQ_EN_REG_PARITY_ERR_EN_MASK                     0x00010000
#define IME_KEY_LOAD_IRQ_EN_REG_PARITY_ERR_EN_BIT_OFFSET                       16
#define IME_KEY_LOAD_IRQ_EN_GLBL_MASK                                  0x80000000
#define IME_KEY_LOAD_IRQ_EN_GLBL_BIT_OFFSET                                    31

#define IME_KEY_LOAD_IRQ_STAT                                          0x0000000C
#define IME_KEY_LOAD_IRQ_STAT_KEY_DONE_MASK                            0x00000001
#define IME_KEY_LOAD_IRQ_STAT_KEY_DONE_BIT_OFFSET                               0
#define IME_KEY_LOAD_IRQ_STAT_KEY_MISS_ERR_MASK                        0x00000040
#define IME_KEY_LOAD_IRQ_STAT_KEY_MISS_ERR_BIT_OFFSET                           6
#define IME_KEY_LOAD_IRQ_STAT_KEY_COLLISION_ERR_MASK                   0x00000080
#define IME_KEY_LOAD_IRQ_STAT_KEY_COLLISION_ERR_BIT_OFFSET                      7
#define IME_KEY_LOAD_IRQ_STAT_APB_TIMING_ERR_MASK                      0x00000100
#define IME_KEY_LOAD_IRQ_STAT_APB_TIMING_ERR_BIT_OFFSET                         8
#define IME_KEY_LOAD_IRQ_STAT_KEY_SIZE_ERR_MASK                        0x00000200
#define IME_KEY_LOAD_IRQ_STAT_KEY_SIZE_ERR_BIT_OFFSET                           9
#define IME_KEY_LOAD_IRQ_STAT_REG_PARITY_ERR_MASK                      0x00010000
#define IME_KEY_LOAD_IRQ_STAT_REG_PARITY_ERR_BIT_OFFSET                        16

#define IME_KEY_USAGE_IRQ_EN                                           0x00000010
#define IME_KEY_USAGE_IRQ_EN_KEY0_USAGE_HIT_EN_MASK                    0x00000001
#define IME_KEY_USAGE_IRQ_EN_KEY0_USAGE_HIT_EN_BIT_OFFSET                       0
#define IME_KEY_USAGE_IRQ_EN_KEY1_USAGE_HIT_EN_MASK                    0x00000002
#define IME_KEY_USAGE_IRQ_EN_KEY1_USAGE_HIT_EN_BIT_OFFSET                       1
#define IME_KEY_USAGE_IRQ_EN_KEY2_USAGE_HIT_EN_MASK                    0x00000004
#define IME_KEY_USAGE_IRQ_EN_KEY2_USAGE_HIT_EN_BIT_OFFSET                       2
#define IME_KEY_USAGE_IRQ_EN_KEY3_USAGE_HIT_EN_MASK                    0x00000008
#define IME_KEY_USAGE_IRQ_EN_KEY3_USAGE_HIT_EN_BIT_OFFSET                       3
#define IME_KEY_USAGE_IRQ_EN_KEY4_USAGE_HIT_EN_MASK                    0x00000010
#define IME_KEY_USAGE_IRQ_EN_KEY4_USAGE_HIT_EN_BIT_OFFSET                       4
#define IME_KEY_USAGE_IRQ_EN_KEY5_USAGE_HIT_EN_MASK                    0x00000020
#define IME_KEY_USAGE_IRQ_EN_KEY5_USAGE_HIT_EN_BIT_OFFSET                       5
#define IME_KEY_USAGE_IRQ_EN_KEY6_USAGE_HIT_EN_MASK                    0x00000040
#define IME_KEY_USAGE_IRQ_EN_KEY6_USAGE_HIT_EN_BIT_OFFSET                       6
#define IME_KEY_USAGE_IRQ_EN_KEY7_USAGE_HIT_EN_MASK                    0x00000080
#define IME_KEY_USAGE_IRQ_EN_KEY7_USAGE_HIT_EN_BIT_OFFSET                       7
#define IME_KEY_USAGE_IRQ_EN_KEY8_USAGE_HIT_EN_MASK                    0x00000100
#define IME_KEY_USAGE_IRQ_EN_KEY8_USAGE_HIT_EN_BIT_OFFSET                       8
#define IME_KEY_USAGE_IRQ_EN_KEY9_USAGE_HIT_EN_MASK                    0x00000200
#define IME_KEY_USAGE_IRQ_EN_KEY9_USAGE_HIT_EN_BIT_OFFSET                       9
#define IME_KEY_USAGE_IRQ_EN_KEY10_USAGE_HIT_EN_MASK                   0x00000400
#define IME_KEY_USAGE_IRQ_EN_KEY10_USAGE_HIT_EN_BIT_OFFSET                     10
#define IME_KEY_USAGE_IRQ_EN_KEY11_USAGE_HIT_EN_MASK                   0x00000800
#define IME_KEY_USAGE_IRQ_EN_KEY11_USAGE_HIT_EN_BIT_OFFSET                     11
#define IME_KEY_USAGE_IRQ_EN_KEY12_USAGE_HIT_EN_MASK                   0x00001000
#define IME_KEY_USAGE_IRQ_EN_KEY12_USAGE_HIT_EN_BIT_OFFSET                     12
#define IME_KEY_USAGE_IRQ_EN_KEY13_USAGE_HIT_EN_MASK                   0x00002000
#define IME_KEY_USAGE_IRQ_EN_KEY13_USAGE_HIT_EN_BIT_OFFSET                     13
#define IME_KEY_USAGE_IRQ_EN_KEY14_USAGE_HIT_EN_MASK                   0x00004000
#define IME_KEY_USAGE_IRQ_EN_KEY14_USAGE_HIT_EN_BIT_OFFSET                     14
#define IME_KEY_USAGE_IRQ_EN_KEY15_USAGE_HIT_EN_MASK                   0x00008000
#define IME_KEY_USAGE_IRQ_EN_KEY15_USAGE_HIT_EN_BIT_OFFSET                     15
#define IME_KEY_USAGE_IRQ_EN_KEY0_SWAPPED_EN_MASK                      0x00010000
#define IME_KEY_USAGE_IRQ_EN_KEY0_SWAPPED_EN_BIT_OFFSET                        16
#define IME_KEY_USAGE_IRQ_EN_KEY1_SWAPPED_EN_MASK                      0x00020000
#define IME_KEY_USAGE_IRQ_EN_KEY1_SWAPPED_EN_BIT_OFFSET                        17
#define IME_KEY_USAGE_IRQ_EN_KEY2_SWAPPED_EN_MASK                      0x00040000
#define IME_KEY_USAGE_IRQ_EN_KEY2_SWAPPED_EN_BIT_OFFSET                        18
#define IME_KEY_USAGE_IRQ_EN_KEY3_SWAPPED_EN_MASK                      0x00080000
#define IME_KEY_USAGE_IRQ_EN_KEY3_SWAPPED_EN_BIT_OFFSET                        19
#define IME_KEY_USAGE_IRQ_EN_KEY4_SWAPPED_EN_MASK                      0x00100000
#define IME_KEY_USAGE_IRQ_EN_KEY4_SWAPPED_EN_BIT_OFFSET                        20
#define IME_KEY_USAGE_IRQ_EN_KEY5_SWAPPED_EN_MASK                      0x00200000
#define IME_KEY_USAGE_IRQ_EN_KEY5_SWAPPED_EN_BIT_OFFSET                        21
#define IME_KEY_USAGE_IRQ_EN_KEY6_SWAPPED_EN_MASK                      0x00400000
#define IME_KEY_USAGE_IRQ_EN_KEY6_SWAPPED_EN_BIT_OFFSET                        22
#define IME_KEY_USAGE_IRQ_EN_KEY7_SWAPPED_EN_MASK                      0x00800000
#define IME_KEY_USAGE_IRQ_EN_KEY7_SWAPPED_EN_BIT_OFFSET                        23
#define IME_KEY_USAGE_IRQ_EN_KEY8_SWAPPED_EN_MASK                      0x01000000
#define IME_KEY_USAGE_IRQ_EN_KEY8_SWAPPED_EN_BIT_OFFSET                        24
#define IME_KEY_USAGE_IRQ_EN_KEY9_SWAPPED_EN_MASK                      0x02000000
#define IME_KEY_USAGE_IRQ_EN_KEY9_SWAPPED_EN_BIT_OFFSET                        25
#define IME_KEY_USAGE_IRQ_EN_KEY10_SWAPPED_EN_MASK                     0x04000000
#define IME_KEY_USAGE_IRQ_EN_KEY10_SWAPPED_EN_BIT_OFFSET                       26
#define IME_KEY_USAGE_IRQ_EN_KEY11_SWAPPED_EN_MASK                     0x08000000
#define IME_KEY_USAGE_IRQ_EN_KEY11_SWAPPED_EN_BIT_OFFSET                       27
#define IME_KEY_USAGE_IRQ_EN_KEY12_SWAPPED_EN_MASK                     0x10000000
#define IME_KEY_USAGE_IRQ_EN_KEY12_SWAPPED_EN_BIT_OFFSET                       28
#define IME_KEY_USAGE_IRQ_EN_KEY13_SWAPPED_EN_MASK                     0x20000000
#define IME_KEY_USAGE_IRQ_EN_KEY13_SWAPPED_EN_BIT_OFFSET                       29
#define IME_KEY_USAGE_IRQ_EN_KEY14_SWAPPED_EN_MASK                     0x40000000
#define IME_KEY_USAGE_IRQ_EN_KEY14_SWAPPED_EN_BIT_OFFSET                       30
#define IME_KEY_USAGE_IRQ_EN_KEY15_SWAPPED_EN_MASK                     0x80000000
#define IME_KEY_USAGE_IRQ_EN_KEY15_SWAPPED_EN_BIT_OFFSET                       31

#define IME_KEY_USAGE_IRQ_STAT                                         0x00000014
#define IME_KEY_USAGE_IRQ_STAT_KEY0_USAGE_HIT_MASK                     0x00000001
#define IME_KEY_USAGE_IRQ_STAT_KEY0_USAGE_HIT_BIT_OFFSET                        0
#define IME_KEY_USAGE_IRQ_STAT_KEY1_USAGE_HIT_MASK                     0x00000002
#define IME_KEY_USAGE_IRQ_STAT_KEY1_USAGE_HIT_BIT_OFFSET                        1
#define IME_KEY_USAGE_IRQ_STAT_KEY2_USAGE_HIT_MASK                     0x00000004
#define IME_KEY_USAGE_IRQ_STAT_KEY2_USAGE_HIT_BIT_OFFSET                        2
#define IME_KEY_USAGE_IRQ_STAT_KEY3_USAGE_HIT_MASK                     0x00000008
#define IME_KEY_USAGE_IRQ_STAT_KEY3_USAGE_HIT_BIT_OFFSET                        3
#define IME_KEY_USAGE_IRQ_STAT_KEY4_USAGE_HIT_MASK                     0x00000010
#define IME_KEY_USAGE_IRQ_STAT_KEY4_USAGE_HIT_BIT_OFFSET                        4
#define IME_KEY_USAGE_IRQ_STAT_KEY5_USAGE_HIT_MASK                     0x00000020
#define IME_KEY_USAGE_IRQ_STAT_KEY5_USAGE_HIT_BIT_OFFSET                        5
#define IME_KEY_USAGE_IRQ_STAT_KEY6_USAGE_HIT_MASK                     0x00000040
#define IME_KEY_USAGE_IRQ_STAT_KEY6_USAGE_HIT_BIT_OFFSET                        6
#define IME_KEY_USAGE_IRQ_STAT_KEY7_USAGE_HIT_MASK                     0x00000080
#define IME_KEY_USAGE_IRQ_STAT_KEY7_USAGE_HIT_BIT_OFFSET                        7
#define IME_KEY_USAGE_IRQ_STAT_KEY8_USAGE_HIT_MASK                     0x00000100
#define IME_KEY_USAGE_IRQ_STAT_KEY8_USAGE_HIT_BIT_OFFSET                        8
#define IME_KEY_USAGE_IRQ_STAT_KEY9_USAGE_HIT_MASK                     0x00000200
#define IME_KEY_USAGE_IRQ_STAT_KEY9_USAGE_HIT_BIT_OFFSET                        9
#define IME_KEY_USAGE_IRQ_STAT_KEY10_USAGE_HIT_MASK                    0x00000400
#define IME_KEY_USAGE_IRQ_STAT_KEY10_USAGE_HIT_BIT_OFFSET                      10
#define IME_KEY_USAGE_IRQ_STAT_KEY11_USAGE_HIT_MASK                    0x00000800
#define IME_KEY_USAGE_IRQ_STAT_KEY11_USAGE_HIT_BIT_OFFSET                      11
#define IME_KEY_USAGE_IRQ_STAT_KEY12_USAGE_HIT_MASK                    0x00001000
#define IME_KEY_USAGE_IRQ_STAT_KEY12_USAGE_HIT_BIT_OFFSET                      12
#define IME_KEY_USAGE_IRQ_STAT_KEY13_USAGE_HIT_MASK                    0x00002000
#define IME_KEY_USAGE_IRQ_STAT_KEY13_USAGE_HIT_BIT_OFFSET                      13
#define IME_KEY_USAGE_IRQ_STAT_KEY14_USAGE_HIT_MASK                    0x00004000
#define IME_KEY_USAGE_IRQ_STAT_KEY14_USAGE_HIT_BIT_OFFSET                      14
#define IME_KEY_USAGE_IRQ_STAT_KEY15_USAGE_HIT_MASK                    0x00008000
#define IME_KEY_USAGE_IRQ_STAT_KEY15_USAGE_HIT_BIT_OFFSET                      15
#define IME_KEY_USAGE_IRQ_STAT_KEY0_SWAPPED_MASK                       0x00010000
#define IME_KEY_USAGE_IRQ_STAT_KEY0_SWAPPED_BIT_OFFSET                         16
#define IME_KEY_USAGE_IRQ_STAT_KEY1_SWAPPED_MASK                       0x00020000
#define IME_KEY_USAGE_IRQ_STAT_KEY1_SWAPPED_BIT_OFFSET                         17
#define IME_KEY_USAGE_IRQ_STAT_KEY2_SWAPPED_MASK                       0x00040000
#define IME_KEY_USAGE_IRQ_STAT_KEY2_SWAPPED_BIT_OFFSET                         18
#define IME_KEY_USAGE_IRQ_STAT_KEY3_SWAPPED_MASK                       0x00080000
#define IME_KEY_USAGE_IRQ_STAT_KEY3_SWAPPED_BIT_OFFSET                         19
#define IME_KEY_USAGE_IRQ_STAT_KEY4_SWAPPED_MASK                       0x00100000
#define IME_KEY_USAGE_IRQ_STAT_KEY4_SWAPPED_BIT_OFFSET                         20
#define IME_KEY_USAGE_IRQ_STAT_KEY5_SWAPPED_MASK                       0x00200000
#define IME_KEY_USAGE_IRQ_STAT_KEY5_SWAPPED_BIT_OFFSET                         21
#define IME_KEY_USAGE_IRQ_STAT_KEY6_SWAPPED_MASK                       0x00400000
#define IME_KEY_USAGE_IRQ_STAT_KEY6_SWAPPED_BIT_OFFSET                         22
#define IME_KEY_USAGE_IRQ_STAT_KEY7_SWAPPED_MASK                       0x00800000
#define IME_KEY_USAGE_IRQ_STAT_KEY7_SWAPPED_BIT_OFFSET                         23
#define IME_KEY_USAGE_IRQ_STAT_KEY8_SWAPPED_MASK                       0x01000000
#define IME_KEY_USAGE_IRQ_STAT_KEY8_SWAPPED_BIT_OFFSET                         24
#define IME_KEY_USAGE_IRQ_STAT_KEY9_SWAPPED_MASK                       0x02000000
#define IME_KEY_USAGE_IRQ_STAT_KEY9_SWAPPED_BIT_OFFSET                         25
#define IME_KEY_USAGE_IRQ_STAT_KEY10_SWAPPED_MASK                      0x04000000
#define IME_KEY_USAGE_IRQ_STAT_KEY10_SWAPPED_BIT_OFFSET                        26
#define IME_KEY_USAGE_IRQ_STAT_KEY11_SWAPPED_MASK                      0x08000000
#define IME_KEY_USAGE_IRQ_STAT_KEY11_SWAPPED_BIT_OFFSET                        27
#define IME_KEY_USAGE_IRQ_STAT_KEY12_SWAPPED_MASK                      0x10000000
#define IME_KEY_USAGE_IRQ_STAT_KEY12_SWAPPED_BIT_OFFSET                        28
#define IME_KEY_USAGE_IRQ_STAT_KEY13_SWAPPED_MASK                      0x20000000
#define IME_KEY_USAGE_IRQ_STAT_KEY13_SWAPPED_BIT_OFFSET                        29
#define IME_KEY_USAGE_IRQ_STAT_KEY14_SWAPPED_MASK                      0x40000000
#define IME_KEY_USAGE_IRQ_STAT_KEY14_SWAPPED_BIT_OFFSET                        30
#define IME_KEY_USAGE_IRQ_STAT_KEY15_SWAPPED_MASK                      0x80000000
#define IME_KEY_USAGE_IRQ_STAT_KEY15_SWAPPED_BIT_OFFSET                        31

#define IME_BUILD_CONFIG_REG0                                          0x00000018
#define IME_BUILD_CONFIG_REG0_DP_WIDTH_MASK                            0x00000003
#define IME_BUILD_CONFIG_REG0_DP_WIDTH_BIT_OFFSET                               0
#define IME_BUILD_CONFIG_REG0_KEY256_EN_MASK                           0x00000200
#define IME_BUILD_CONFIG_REG0_KEY256_EN_BIT_OFFSET                              9
#define IME_BUILD_CONFIG_REG0_KEY512_EN_MASK                           0x00000400
#define IME_BUILD_CONFIG_REG0_KEY512_EN_BIT_OFFSET                             10
#define IME_BUILD_CONFIG_REG0_AES_ECB_EN_MASK                          0x00004000
#define IME_BUILD_CONFIG_REG0_AES_ECB_EN_BIT_OFFSET                            14
#define IME_BUILD_CONFIG_REG0_APB4_EN_MASK                             0x00080000
#define IME_BUILD_CONFIG_REG0_APB4_EN_BIT_OFFSET                               19
#define IME_BUILD_CONFIG_REG0_APB5_E_EN_MASK                           0x00100000
#define IME_BUILD_CONFIG_REG0_APB5_E_EN_BIT_OFFSET                             20

#define IME_SOFTWARE_BW_CTRL                                           0x0000001C
#define IME_SOFTWARE_BW_CTRL_SOFTWARE_BW_CTRL_MASK                     0x00000003
#define IME_SOFTWARE_BW_CTRL_SOFTWARE_BW_CTRL_BIT_OFFSET                        0

#define IME_REGION0_ADDR_LOW_31_0                                      0x00000020
#define IME_REGION0_ADDR_LOW_31_0_REGION0_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION0_ADDR_LOW_31_0_REGION0_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION0_ADDR_LOW_63_32                                     0x00000024
#define IME_REGION0_ADDR_LOW_63_32_REGION0_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION0_ADDR_LOW_63_32_REGION0_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION0_ADDR_HIGH_31_0                                     0x00000028
#define IME_REGION0_ADDR_HIGH_31_0_REGION0_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION0_ADDR_HIGH_31_0_REGION0_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION0_ADDR_HIGH_63_32                                    0x0000002C
#define IME_REGION0_ADDR_HIGH_63_32_REGION0_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION0_ADDR_HIGH_63_32_REGION0_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION1_ADDR_LOW_31_0                                      0x00000030
#define IME_REGION1_ADDR_LOW_31_0_REGION1_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION1_ADDR_LOW_31_0_REGION1_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION1_ADDR_LOW_63_32                                     0x00000034
#define IME_REGION1_ADDR_LOW_63_32_REGION1_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION1_ADDR_LOW_63_32_REGION1_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION1_ADDR_HIGH_31_0                                     0x00000038
#define IME_REGION1_ADDR_HIGH_31_0_REGION1_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION1_ADDR_HIGH_31_0_REGION1_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION1_ADDR_HIGH_63_32                                    0x0000003C
#define IME_REGION1_ADDR_HIGH_63_32_REGION1_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION1_ADDR_HIGH_63_32_REGION1_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION2_ADDR_LOW_31_0                                      0x00000040
#define IME_REGION2_ADDR_LOW_31_0_REGION2_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION2_ADDR_LOW_31_0_REGION2_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION2_ADDR_LOW_63_32                                     0x00000044
#define IME_REGION2_ADDR_LOW_63_32_REGION2_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION2_ADDR_LOW_63_32_REGION2_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION2_ADDR_HIGH_31_0                                     0x00000048
#define IME_REGION2_ADDR_HIGH_31_0_REGION2_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION2_ADDR_HIGH_31_0_REGION2_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION2_ADDR_HIGH_63_32                                    0x0000004C
#define IME_REGION2_ADDR_HIGH_63_32_REGION2_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION2_ADDR_HIGH_63_32_REGION2_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION3_ADDR_LOW_31_0                                      0x00000050
#define IME_REGION3_ADDR_LOW_31_0_REGION3_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION3_ADDR_LOW_31_0_REGION3_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION3_ADDR_LOW_63_32                                     0x00000054
#define IME_REGION3_ADDR_LOW_63_32_REGION3_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION3_ADDR_LOW_63_32_REGION3_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION3_ADDR_HIGH_31_0                                     0x00000058
#define IME_REGION3_ADDR_HIGH_31_0_REGION3_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION3_ADDR_HIGH_31_0_REGION3_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION3_ADDR_HIGH_63_32                                    0x0000005C
#define IME_REGION3_ADDR_HIGH_63_32_REGION3_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION3_ADDR_HIGH_63_32_REGION3_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION4_ADDR_LOW_31_0                                      0x00000060
#define IME_REGION4_ADDR_LOW_31_0_REGION4_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION4_ADDR_LOW_31_0_REGION4_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION4_ADDR_LOW_63_32                                     0x00000064
#define IME_REGION4_ADDR_LOW_63_32_REGION4_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION4_ADDR_LOW_63_32_REGION4_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION4_ADDR_HIGH_31_0                                     0x00000068
#define IME_REGION4_ADDR_HIGH_31_0_REGION4_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION4_ADDR_HIGH_31_0_REGION4_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION4_ADDR_HIGH_63_32                                    0x0000006C
#define IME_REGION4_ADDR_HIGH_63_32_REGION4_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION4_ADDR_HIGH_63_32_REGION4_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION5_ADDR_LOW_31_0                                      0x00000070
#define IME_REGION5_ADDR_LOW_31_0_REGION5_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION5_ADDR_LOW_31_0_REGION5_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION5_ADDR_LOW_63_32                                     0x00000074
#define IME_REGION5_ADDR_LOW_63_32_REGION5_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION5_ADDR_LOW_63_32_REGION5_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION5_ADDR_HIGH_31_0                                     0x00000078
#define IME_REGION5_ADDR_HIGH_31_0_REGION5_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION5_ADDR_HIGH_31_0_REGION5_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION5_ADDR_HIGH_63_32                                    0x0000007C
#define IME_REGION5_ADDR_HIGH_63_32_REGION5_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION5_ADDR_HIGH_63_32_REGION5_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION6_ADDR_LOW_31_0                                      0x00000080
#define IME_REGION6_ADDR_LOW_31_0_REGION6_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION6_ADDR_LOW_31_0_REGION6_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION6_ADDR_LOW_63_32                                     0x00000084
#define IME_REGION6_ADDR_LOW_63_32_REGION6_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION6_ADDR_LOW_63_32_REGION6_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION6_ADDR_HIGH_31_0                                     0x00000088
#define IME_REGION6_ADDR_HIGH_31_0_REGION6_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION6_ADDR_HIGH_31_0_REGION6_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION6_ADDR_HIGH_63_32                                    0x0000008C
#define IME_REGION6_ADDR_HIGH_63_32_REGION6_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION6_ADDR_HIGH_63_32_REGION6_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION7_ADDR_LOW_31_0                                      0x00000090
#define IME_REGION7_ADDR_LOW_31_0_REGION7_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION7_ADDR_LOW_31_0_REGION7_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION7_ADDR_LOW_63_32                                     0x00000094
#define IME_REGION7_ADDR_LOW_63_32_REGION7_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION7_ADDR_LOW_63_32_REGION7_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION7_ADDR_HIGH_31_0                                     0x00000098
#define IME_REGION7_ADDR_HIGH_31_0_REGION7_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION7_ADDR_HIGH_31_0_REGION7_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION7_ADDR_HIGH_63_32                                    0x0000009C
#define IME_REGION7_ADDR_HIGH_63_32_REGION7_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION7_ADDR_HIGH_63_32_REGION7_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION8_ADDR_LOW_31_0                                      0x000000A0
#define IME_REGION8_ADDR_LOW_31_0_REGION8_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION8_ADDR_LOW_31_0_REGION8_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION8_ADDR_LOW_63_32                                     0x000000A4
#define IME_REGION8_ADDR_LOW_63_32_REGION8_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION8_ADDR_LOW_63_32_REGION8_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION8_ADDR_HIGH_31_0                                     0x000000A8
#define IME_REGION8_ADDR_HIGH_31_0_REGION8_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION8_ADDR_HIGH_31_0_REGION8_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION8_ADDR_HIGH_63_32                                    0x000000AC
#define IME_REGION8_ADDR_HIGH_63_32_REGION8_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION8_ADDR_HIGH_63_32_REGION8_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION9_ADDR_LOW_31_0                                      0x000000B0
#define IME_REGION9_ADDR_LOW_31_0_REGION9_ADDR_LOW_31_0_MASK           0xFFFFFFFF
#define IME_REGION9_ADDR_LOW_31_0_REGION9_ADDR_LOW_31_0_BIT_OFFSET              0

#define IME_REGION9_ADDR_LOW_63_32                                     0x000000B4
#define IME_REGION9_ADDR_LOW_63_32_REGION9_ADDR_LOW_63_32_MASK         0xFFFFFFFF
#define IME_REGION9_ADDR_LOW_63_32_REGION9_ADDR_LOW_63_32_BIT_OFFSET            0

#define IME_REGION9_ADDR_HIGH_31_0                                     0x000000B8
#define IME_REGION9_ADDR_HIGH_31_0_REGION9_ADDR_HIGH_31_0_MASK         0xFFFFFFFF
#define IME_REGION9_ADDR_HIGH_31_0_REGION9_ADDR_HIGH_31_0_BIT_OFFSET            0

#define IME_REGION9_ADDR_HIGH_63_32                                    0x000000BC
#define IME_REGION9_ADDR_HIGH_63_32_REGION9_ADDR_HIGH_63_32_MASK       0xFFFFFFFF
#define IME_REGION9_ADDR_HIGH_63_32_REGION9_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION10_ADDR_LOW_31_0                                     0x000000C0
#define IME_REGION10_ADDR_LOW_31_0_REGION10_ADDR_LOW_31_0_MASK         0xFFFFFFFF
#define IME_REGION10_ADDR_LOW_31_0_REGION10_ADDR_LOW_31_0_BIT_OFFSET            0

#define IME_REGION10_ADDR_LOW_63_32                                    0x000000C4
#define IME_REGION10_ADDR_LOW_63_32_REGION10_ADDR_LOW_63_32_MASK       0xFFFFFFFF
#define IME_REGION10_ADDR_LOW_63_32_REGION10_ADDR_LOW_63_32_BIT_OFFSET          0

#define IME_REGION10_ADDR_HIGH_31_0                                    0x000000C8
#define IME_REGION10_ADDR_HIGH_31_0_REGION10_ADDR_HIGH_31_0_MASK       0xFFFFFFFF
#define IME_REGION10_ADDR_HIGH_31_0_REGION10_ADDR_HIGH_31_0_BIT_OFFSET          0

#define IME_REGION10_ADDR_HIGH_63_32                                   0x000000CC
#define IME_REGION10_ADDR_HIGH_63_32_REGION10_ADDR_HIGH_63_32_MASK     0xFFFFFFFF
#define IME_REGION10_ADDR_HIGH_63_32_REGION10_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION11_ADDR_LOW_31_0                                     0x000000D0
#define IME_REGION11_ADDR_LOW_31_0_REGION11_ADDR_LOW_31_0_MASK         0xFFFFFFFF
#define IME_REGION11_ADDR_LOW_31_0_REGION11_ADDR_LOW_31_0_BIT_OFFSET            0

#define IME_REGION11_ADDR_LOW_63_32                                    0x000000D4
#define IME_REGION11_ADDR_LOW_63_32_REGION11_ADDR_LOW_63_32_MASK       0xFFFFFFFF
#define IME_REGION11_ADDR_LOW_63_32_REGION11_ADDR_LOW_63_32_BIT_OFFSET          0

#define IME_REGION11_ADDR_HIGH_31_0                                    0x000000D8
#define IME_REGION11_ADDR_HIGH_31_0_REGION11_ADDR_HIGH_31_0_MASK       0xFFFFFFFF
#define IME_REGION11_ADDR_HIGH_31_0_REGION11_ADDR_HIGH_31_0_BIT_OFFSET          0

#define IME_REGION11_ADDR_HIGH_63_32                                   0x000000DC
#define IME_REGION11_ADDR_HIGH_63_32_REGION11_ADDR_HIGH_63_32_MASK     0xFFFFFFFF
#define IME_REGION11_ADDR_HIGH_63_32_REGION11_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION12_ADDR_LOW_31_0                                     0x000000E0
#define IME_REGION12_ADDR_LOW_31_0_REGION12_ADDR_LOW_31_0_MASK         0xFFFFFFFF
#define IME_REGION12_ADDR_LOW_31_0_REGION12_ADDR_LOW_31_0_BIT_OFFSET            0

#define IME_REGION12_ADDR_LOW_63_32                                    0x000000E4
#define IME_REGION12_ADDR_LOW_63_32_REGION12_ADDR_LOW_63_32_MASK       0xFFFFFFFF
#define IME_REGION12_ADDR_LOW_63_32_REGION12_ADDR_LOW_63_32_BIT_OFFSET          0

#define IME_REGION12_ADDR_HIGH_31_0                                    0x000000E8
#define IME_REGION12_ADDR_HIGH_31_0_REGION12_ADDR_HIGH_31_0_MASK       0xFFFFFFFF
#define IME_REGION12_ADDR_HIGH_31_0_REGION12_ADDR_HIGH_31_0_BIT_OFFSET          0

#define IME_REGION12_ADDR_HIGH_63_32                                   0x000000EC
#define IME_REGION12_ADDR_HIGH_63_32_REGION12_ADDR_HIGH_63_32_MASK     0xFFFFFFFF
#define IME_REGION12_ADDR_HIGH_63_32_REGION12_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION13_ADDR_LOW_31_0                                     0x000000F0
#define IME_REGION13_ADDR_LOW_31_0_REGION13_ADDR_LOW_31_0_MASK         0xFFFFFFFF
#define IME_REGION13_ADDR_LOW_31_0_REGION13_ADDR_LOW_31_0_BIT_OFFSET            0

#define IME_REGION13_ADDR_LOW_63_32                                    0x000000F4
#define IME_REGION13_ADDR_LOW_63_32_REGION13_ADDR_LOW_63_32_MASK       0xFFFFFFFF
#define IME_REGION13_ADDR_LOW_63_32_REGION13_ADDR_LOW_63_32_BIT_OFFSET          0

#define IME_REGION13_ADDR_HIGH_31_0                                    0x000000F8
#define IME_REGION13_ADDR_HIGH_31_0_REGION13_ADDR_HIGH_31_0_MASK       0xFFFFFFFF
#define IME_REGION13_ADDR_HIGH_31_0_REGION13_ADDR_HIGH_31_0_BIT_OFFSET          0

#define IME_REGION13_ADDR_HIGH_63_32                                   0x000000FC
#define IME_REGION13_ADDR_HIGH_63_32_REGION13_ADDR_HIGH_63_32_MASK     0xFFFFFFFF
#define IME_REGION13_ADDR_HIGH_63_32_REGION13_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION14_ADDR_LOW_31_0                                     0x00000100
#define IME_REGION14_ADDR_LOW_31_0_REGION14_ADDR_LOW_31_0_MASK         0xFFFFFFFF
#define IME_REGION14_ADDR_LOW_31_0_REGION14_ADDR_LOW_31_0_BIT_OFFSET            0

#define IME_REGION14_ADDR_LOW_63_32                                    0x00000104
#define IME_REGION14_ADDR_LOW_63_32_REGION14_ADDR_LOW_63_32_MASK       0xFFFFFFFF
#define IME_REGION14_ADDR_LOW_63_32_REGION14_ADDR_LOW_63_32_BIT_OFFSET          0

#define IME_REGION14_ADDR_HIGH_31_0                                    0x00000108
#define IME_REGION14_ADDR_HIGH_31_0_REGION14_ADDR_HIGH_31_0_MASK       0xFFFFFFFF
#define IME_REGION14_ADDR_HIGH_31_0_REGION14_ADDR_HIGH_31_0_BIT_OFFSET          0

#define IME_REGION14_ADDR_HIGH_63_32                                   0x0000010C
#define IME_REGION14_ADDR_HIGH_63_32_REGION14_ADDR_HIGH_63_32_MASK     0xFFFFFFFF
#define IME_REGION14_ADDR_HIGH_63_32_REGION14_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_REGION15_ADDR_LOW_31_0                                     0x00000110
#define IME_REGION15_ADDR_LOW_31_0_REGION15_ADDR_LOW_31_0_MASK         0xFFFFFFFF
#define IME_REGION15_ADDR_LOW_31_0_REGION15_ADDR_LOW_31_0_BIT_OFFSET            0

#define IME_REGION15_ADDR_LOW_63_32                                    0x00000114
#define IME_REGION15_ADDR_LOW_63_32_REGION15_ADDR_LOW_63_32_MASK       0xFFFFFFFF
#define IME_REGION15_ADDR_LOW_63_32_REGION15_ADDR_LOW_63_32_BIT_OFFSET          0

#define IME_REGION15_ADDR_HIGH_31_0                                    0x00000118
#define IME_REGION15_ADDR_HIGH_31_0_REGION15_ADDR_HIGH_31_0_MASK       0xFFFFFFFF
#define IME_REGION15_ADDR_HIGH_31_0_REGION15_ADDR_HIGH_31_0_BIT_OFFSET          0

#define IME_REGION15_ADDR_HIGH_63_32                                   0x0000011C
#define IME_REGION15_ADDR_HIGH_63_32_REGION15_ADDR_HIGH_63_32_MASK     0xFFFFFFFF
#define IME_REGION15_ADDR_HIGH_63_32_REGION15_ADDR_HIGH_63_32_BIT_OFFSET          0

#define IME_KEY0_USAGE_THR_31_0                                        0x00000120
#define IME_KEY0_USAGE_THR_31_0_KEY0_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY0_USAGE_THR_31_0_KEY0_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY0_USAGE_THR_63_32                                       0x00000124
#define IME_KEY0_USAGE_THR_63_32_KEY0_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY0_USAGE_THR_63_32_KEY0_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY1_USAGE_THR_31_0                                        0x00000128
#define IME_KEY1_USAGE_THR_31_0_KEY1_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY1_USAGE_THR_31_0_KEY1_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY1_USAGE_THR_63_32                                       0x0000012C
#define IME_KEY1_USAGE_THR_63_32_KEY1_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY1_USAGE_THR_63_32_KEY1_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY2_USAGE_THR_31_0                                        0x00000130
#define IME_KEY2_USAGE_THR_31_0_KEY2_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY2_USAGE_THR_31_0_KEY2_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY2_USAGE_THR_63_32                                       0x00000134
#define IME_KEY2_USAGE_THR_63_32_KEY2_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY2_USAGE_THR_63_32_KEY2_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY3_USAGE_THR_31_0                                        0x00000138
#define IME_KEY3_USAGE_THR_31_0_KEY3_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY3_USAGE_THR_31_0_KEY3_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY3_USAGE_THR_63_32                                       0x0000013C
#define IME_KEY3_USAGE_THR_63_32_KEY3_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY3_USAGE_THR_63_32_KEY3_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY4_USAGE_THR_31_0                                        0x00000140
#define IME_KEY4_USAGE_THR_31_0_KEY4_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY4_USAGE_THR_31_0_KEY4_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY4_USAGE_THR_63_32                                       0x00000144
#define IME_KEY4_USAGE_THR_63_32_KEY4_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY4_USAGE_THR_63_32_KEY4_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY5_USAGE_THR_31_0                                        0x00000148
#define IME_KEY5_USAGE_THR_31_0_KEY5_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY5_USAGE_THR_31_0_KEY5_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY5_USAGE_THR_63_32                                       0x0000014C
#define IME_KEY5_USAGE_THR_63_32_KEY5_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY5_USAGE_THR_63_32_KEY5_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY6_USAGE_THR_31_0                                        0x00000150
#define IME_KEY6_USAGE_THR_31_0_KEY6_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY6_USAGE_THR_31_0_KEY6_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY6_USAGE_THR_63_32                                       0x00000154
#define IME_KEY6_USAGE_THR_63_32_KEY6_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY6_USAGE_THR_63_32_KEY6_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY7_USAGE_THR_31_0                                        0x00000158
#define IME_KEY7_USAGE_THR_31_0_KEY7_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY7_USAGE_THR_31_0_KEY7_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY7_USAGE_THR_63_32                                       0x0000015C
#define IME_KEY7_USAGE_THR_63_32_KEY7_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY7_USAGE_THR_63_32_KEY7_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY8_USAGE_THR_31_0                                        0x00000160
#define IME_KEY8_USAGE_THR_31_0_KEY8_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY8_USAGE_THR_31_0_KEY8_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY8_USAGE_THR_63_32                                       0x00000164
#define IME_KEY8_USAGE_THR_63_32_KEY8_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY8_USAGE_THR_63_32_KEY8_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY9_USAGE_THR_31_0                                        0x00000168
#define IME_KEY9_USAGE_THR_31_0_KEY9_USAGE_THR_31_0_MASK               0xFFFFFFFF
#define IME_KEY9_USAGE_THR_31_0_KEY9_USAGE_THR_31_0_BIT_OFFSET                  0

#define IME_KEY9_USAGE_THR_63_32                                       0x0000016C
#define IME_KEY9_USAGE_THR_63_32_KEY9_USAGE_THR_63_32_MASK             0xFFFFFFFF
#define IME_KEY9_USAGE_THR_63_32_KEY9_USAGE_THR_63_32_BIT_OFFSET                0

#define IME_KEY10_USAGE_THR_31_0                                       0x00000170
#define IME_KEY10_USAGE_THR_31_0_KEY10_USAGE_THR_31_0_MASK             0xFFFFFFFF
#define IME_KEY10_USAGE_THR_31_0_KEY10_USAGE_THR_31_0_BIT_OFFSET                0

#define IME_KEY10_USAGE_THR_63_32                                      0x00000174
#define IME_KEY10_USAGE_THR_63_32_KEY10_USAGE_THR_63_32_MASK           0xFFFFFFFF
#define IME_KEY10_USAGE_THR_63_32_KEY10_USAGE_THR_63_32_BIT_OFFSET              0

#define IME_KEY11_USAGE_THR_31_0                                       0x00000178
#define IME_KEY11_USAGE_THR_31_0_KEY11_USAGE_THR_31_0_MASK             0xFFFFFFFF
#define IME_KEY11_USAGE_THR_31_0_KEY11_USAGE_THR_31_0_BIT_OFFSET                0

#define IME_KEY11_USAGE_THR_63_32                                      0x0000017C
#define IME_KEY11_USAGE_THR_63_32_KEY11_USAGE_THR_63_32_MASK           0xFFFFFFFF
#define IME_KEY11_USAGE_THR_63_32_KEY11_USAGE_THR_63_32_BIT_OFFSET              0

#define IME_KEY12_USAGE_THR_31_0                                       0x00000180
#define IME_KEY12_USAGE_THR_31_0_KEY12_USAGE_THR_31_0_MASK             0xFFFFFFFF
#define IME_KEY12_USAGE_THR_31_0_KEY12_USAGE_THR_31_0_BIT_OFFSET                0

#define IME_KEY12_USAGE_THR_63_32                                      0x00000184
#define IME_KEY12_USAGE_THR_63_32_KEY12_USAGE_THR_63_32_MASK           0xFFFFFFFF
#define IME_KEY12_USAGE_THR_63_32_KEY12_USAGE_THR_63_32_BIT_OFFSET              0

#define IME_KEY13_USAGE_THR_31_0                                       0x00000188
#define IME_KEY13_USAGE_THR_31_0_KEY13_USAGE_THR_31_0_MASK             0xFFFFFFFF
#define IME_KEY13_USAGE_THR_31_0_KEY13_USAGE_THR_31_0_BIT_OFFSET                0

#define IME_KEY13_USAGE_THR_63_32                                      0x0000018C
#define IME_KEY13_USAGE_THR_63_32_KEY13_USAGE_THR_63_32_MASK           0xFFFFFFFF
#define IME_KEY13_USAGE_THR_63_32_KEY13_USAGE_THR_63_32_BIT_OFFSET              0

#define IME_KEY14_USAGE_THR_31_0                                       0x00000190
#define IME_KEY14_USAGE_THR_31_0_KEY14_USAGE_THR_31_0_MASK             0xFFFFFFFF
#define IME_KEY14_USAGE_THR_31_0_KEY14_USAGE_THR_31_0_BIT_OFFSET                0

#define IME_KEY14_USAGE_THR_63_32                                      0x00000194
#define IME_KEY14_USAGE_THR_63_32_KEY14_USAGE_THR_63_32_MASK           0xFFFFFFFF
#define IME_KEY14_USAGE_THR_63_32_KEY14_USAGE_THR_63_32_BIT_OFFSET              0

#define IME_KEY15_USAGE_THR_31_0                                       0x00000198
#define IME_KEY15_USAGE_THR_31_0_KEY15_USAGE_THR_31_0_MASK             0xFFFFFFFF
#define IME_KEY15_USAGE_THR_31_0_KEY15_USAGE_THR_31_0_BIT_OFFSET                0

#define IME_KEY15_USAGE_THR_63_32                                      0x0000019C
#define IME_KEY15_USAGE_THR_63_32_KEY15_USAGE_THR_63_32_MASK           0xFFFFFFFF
#define IME_KEY15_USAGE_THR_63_32_KEY15_USAGE_THR_63_32_BIT_OFFSET              0

#define IME_KEY_USAGE_AUTO_CLEAR                                       0x000001A0
#define IME_KEY_USAGE_AUTO_CLEAR_KEY0_USAGE_AUTO_CLEAR_MASK            0x00000001
#define IME_KEY_USAGE_AUTO_CLEAR_KEY0_USAGE_AUTO_CLEAR_BIT_OFFSET               0
#define IME_KEY_USAGE_AUTO_CLEAR_KEY1_USAGE_AUTO_CLEAR_MASK            0x00000002
#define IME_KEY_USAGE_AUTO_CLEAR_KEY1_USAGE_AUTO_CLEAR_BIT_OFFSET               1
#define IME_KEY_USAGE_AUTO_CLEAR_KEY2_USAGE_AUTO_CLEAR_MASK            0x00000004
#define IME_KEY_USAGE_AUTO_CLEAR_KEY2_USAGE_AUTO_CLEAR_BIT_OFFSET               2
#define IME_KEY_USAGE_AUTO_CLEAR_KEY3_USAGE_AUTO_CLEAR_MASK            0x00000008
#define IME_KEY_USAGE_AUTO_CLEAR_KEY3_USAGE_AUTO_CLEAR_BIT_OFFSET               3
#define IME_KEY_USAGE_AUTO_CLEAR_KEY4_USAGE_AUTO_CLEAR_MASK            0x00000010
#define IME_KEY_USAGE_AUTO_CLEAR_KEY4_USAGE_AUTO_CLEAR_BIT_OFFSET               4
#define IME_KEY_USAGE_AUTO_CLEAR_KEY5_USAGE_AUTO_CLEAR_MASK            0x00000020
#define IME_KEY_USAGE_AUTO_CLEAR_KEY5_USAGE_AUTO_CLEAR_BIT_OFFSET               5
#define IME_KEY_USAGE_AUTO_CLEAR_KEY6_USAGE_AUTO_CLEAR_MASK            0x00000040
#define IME_KEY_USAGE_AUTO_CLEAR_KEY6_USAGE_AUTO_CLEAR_BIT_OFFSET               6
#define IME_KEY_USAGE_AUTO_CLEAR_KEY7_USAGE_AUTO_CLEAR_MASK            0x00000080
#define IME_KEY_USAGE_AUTO_CLEAR_KEY7_USAGE_AUTO_CLEAR_BIT_OFFSET               7
#define IME_KEY_USAGE_AUTO_CLEAR_KEY8_USAGE_AUTO_CLEAR_MASK            0x00000100
#define IME_KEY_USAGE_AUTO_CLEAR_KEY8_USAGE_AUTO_CLEAR_BIT_OFFSET               8
#define IME_KEY_USAGE_AUTO_CLEAR_KEY9_USAGE_AUTO_CLEAR_MASK            0x00000200
#define IME_KEY_USAGE_AUTO_CLEAR_KEY9_USAGE_AUTO_CLEAR_BIT_OFFSET               9
#define IME_KEY_USAGE_AUTO_CLEAR_KEY10_USAGE_AUTO_CLEAR_MASK           0x00000400
#define IME_KEY_USAGE_AUTO_CLEAR_KEY10_USAGE_AUTO_CLEAR_BIT_OFFSET             10
#define IME_KEY_USAGE_AUTO_CLEAR_KEY11_USAGE_AUTO_CLEAR_MASK           0x00000800
#define IME_KEY_USAGE_AUTO_CLEAR_KEY11_USAGE_AUTO_CLEAR_BIT_OFFSET             11
#define IME_KEY_USAGE_AUTO_CLEAR_KEY12_USAGE_AUTO_CLEAR_MASK           0x00001000
#define IME_KEY_USAGE_AUTO_CLEAR_KEY12_USAGE_AUTO_CLEAR_BIT_OFFSET             12
#define IME_KEY_USAGE_AUTO_CLEAR_KEY13_USAGE_AUTO_CLEAR_MASK           0x00002000
#define IME_KEY_USAGE_AUTO_CLEAR_KEY13_USAGE_AUTO_CLEAR_BIT_OFFSET             13
#define IME_KEY_USAGE_AUTO_CLEAR_KEY14_USAGE_AUTO_CLEAR_MASK           0x00004000
#define IME_KEY_USAGE_AUTO_CLEAR_KEY14_USAGE_AUTO_CLEAR_BIT_OFFSET             14
#define IME_KEY_USAGE_AUTO_CLEAR_KEY15_USAGE_AUTO_CLEAR_MASK           0x00008000
#define IME_KEY_USAGE_AUTO_CLEAR_KEY15_USAGE_AUTO_CLEAR_BIT_OFFSET             15

#define IME_KEY_USAGE_EN                                               0x000001A4
#define IME_KEY_USAGE_EN_KEY0_USAGE_EN_MASK                            0x00000001
#define IME_KEY_USAGE_EN_KEY0_USAGE_EN_BIT_OFFSET                               0
#define IME_KEY_USAGE_EN_KEY1_USAGE_EN_MASK                            0x00000002
#define IME_KEY_USAGE_EN_KEY1_USAGE_EN_BIT_OFFSET                               1
#define IME_KEY_USAGE_EN_KEY2_USAGE_EN_MASK                            0x00000004
#define IME_KEY_USAGE_EN_KEY2_USAGE_EN_BIT_OFFSET                               2
#define IME_KEY_USAGE_EN_KEY3_USAGE_EN_MASK                            0x00000008
#define IME_KEY_USAGE_EN_KEY3_USAGE_EN_BIT_OFFSET                               3
#define IME_KEY_USAGE_EN_KEY4_USAGE_EN_MASK                            0x00000010
#define IME_KEY_USAGE_EN_KEY4_USAGE_EN_BIT_OFFSET                               4
#define IME_KEY_USAGE_EN_KEY5_USAGE_EN_MASK                            0x00000020
#define IME_KEY_USAGE_EN_KEY5_USAGE_EN_BIT_OFFSET                               5
#define IME_KEY_USAGE_EN_KEY6_USAGE_EN_MASK                            0x00000040
#define IME_KEY_USAGE_EN_KEY6_USAGE_EN_BIT_OFFSET                               6
#define IME_KEY_USAGE_EN_KEY7_USAGE_EN_MASK                            0x00000080
#define IME_KEY_USAGE_EN_KEY7_USAGE_EN_BIT_OFFSET                               7
#define IME_KEY_USAGE_EN_KEY8_USAGE_EN_MASK                            0x00000100
#define IME_KEY_USAGE_EN_KEY8_USAGE_EN_BIT_OFFSET                               8
#define IME_KEY_USAGE_EN_KEY9_USAGE_EN_MASK                            0x00000200
#define IME_KEY_USAGE_EN_KEY9_USAGE_EN_BIT_OFFSET                               9
#define IME_KEY_USAGE_EN_KEY10_USAGE_EN_MASK                           0x00000400
#define IME_KEY_USAGE_EN_KEY10_USAGE_EN_BIT_OFFSET                             10
#define IME_KEY_USAGE_EN_KEY11_USAGE_EN_MASK                           0x00000800
#define IME_KEY_USAGE_EN_KEY11_USAGE_EN_BIT_OFFSET                             11
#define IME_KEY_USAGE_EN_KEY12_USAGE_EN_MASK                           0x00001000
#define IME_KEY_USAGE_EN_KEY12_USAGE_EN_BIT_OFFSET                             12
#define IME_KEY_USAGE_EN_KEY13_USAGE_EN_MASK                           0x00002000
#define IME_KEY_USAGE_EN_KEY13_USAGE_EN_BIT_OFFSET                             13
#define IME_KEY_USAGE_EN_KEY14_USAGE_EN_MASK                           0x00004000
#define IME_KEY_USAGE_EN_KEY14_USAGE_EN_BIT_OFFSET                             14
#define IME_KEY_USAGE_EN_KEY15_USAGE_EN_MASK                           0x00008000
#define IME_KEY_USAGE_EN_KEY15_USAGE_EN_BIT_OFFSET                             15

#define IME_KEY0_USAGE_CNT_STATUS_31_0                                 0x000001B0
#define IME_KEY0_USAGE_CNT_STATUS_31_0_KEY0_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY0_USAGE_CNT_STATUS_31_0_KEY0_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY0_USAGE_CNT_STATUS_63_32                                0x000001B4
#define IME_KEY0_USAGE_CNT_STATUS_63_32_KEY0_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY0_USAGE_CNT_STATUS_63_32_KEY0_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY1_USAGE_CNT_STATUS_31_0                                 0x000001B8
#define IME_KEY1_USAGE_CNT_STATUS_31_0_KEY1_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY1_USAGE_CNT_STATUS_31_0_KEY1_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY1_USAGE_CNT_STATUS_63_32                                0x000001BC
#define IME_KEY1_USAGE_CNT_STATUS_63_32_KEY1_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY1_USAGE_CNT_STATUS_63_32_KEY1_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY2_USAGE_CNT_STATUS_31_0                                 0x000001C0
#define IME_KEY2_USAGE_CNT_STATUS_31_0_KEY2_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY2_USAGE_CNT_STATUS_31_0_KEY2_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY2_USAGE_CNT_STATUS_63_32                                0x000001C4
#define IME_KEY2_USAGE_CNT_STATUS_63_32_KEY2_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY2_USAGE_CNT_STATUS_63_32_KEY2_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY3_USAGE_CNT_STATUS_31_0                                 0x000001C8
#define IME_KEY3_USAGE_CNT_STATUS_31_0_KEY3_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY3_USAGE_CNT_STATUS_31_0_KEY3_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY3_USAGE_CNT_STATUS_63_32                                0x000001CC
#define IME_KEY3_USAGE_CNT_STATUS_63_32_KEY3_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY3_USAGE_CNT_STATUS_63_32_KEY3_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY4_USAGE_CNT_STATUS_31_0                                 0x000001D0
#define IME_KEY4_USAGE_CNT_STATUS_31_0_KEY4_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY4_USAGE_CNT_STATUS_31_0_KEY4_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY4_USAGE_CNT_STATUS_63_32                                0x000001D4
#define IME_KEY4_USAGE_CNT_STATUS_63_32_KEY4_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY4_USAGE_CNT_STATUS_63_32_KEY4_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY5_USAGE_CNT_STATUS_31_0                                 0x000001D8
#define IME_KEY5_USAGE_CNT_STATUS_31_0_KEY5_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY5_USAGE_CNT_STATUS_31_0_KEY5_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY5_USAGE_CNT_STATUS_63_32                                0x000001DC
#define IME_KEY5_USAGE_CNT_STATUS_63_32_KEY5_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY5_USAGE_CNT_STATUS_63_32_KEY5_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY6_USAGE_CNT_STATUS_31_0                                 0x000001E0
#define IME_KEY6_USAGE_CNT_STATUS_31_0_KEY6_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY6_USAGE_CNT_STATUS_31_0_KEY6_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY6_USAGE_CNT_STATUS_63_32                                0x000001E4
#define IME_KEY6_USAGE_CNT_STATUS_63_32_KEY6_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY6_USAGE_CNT_STATUS_63_32_KEY6_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY7_USAGE_CNT_STATUS_31_0                                 0x000001E8
#define IME_KEY7_USAGE_CNT_STATUS_31_0_KEY7_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY7_USAGE_CNT_STATUS_31_0_KEY7_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY7_USAGE_CNT_STATUS_63_32                                0x000001EC
#define IME_KEY7_USAGE_CNT_STATUS_63_32_KEY7_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY7_USAGE_CNT_STATUS_63_32_KEY7_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY8_USAGE_CNT_STATUS_31_0                                 0x000001F0
#define IME_KEY8_USAGE_CNT_STATUS_31_0_KEY8_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY8_USAGE_CNT_STATUS_31_0_KEY8_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY8_USAGE_CNT_STATUS_63_32                                0x000001F4
#define IME_KEY8_USAGE_CNT_STATUS_63_32_KEY8_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY8_USAGE_CNT_STATUS_63_32_KEY8_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY9_USAGE_CNT_STATUS_31_0                                 0x000001F8
#define IME_KEY9_USAGE_CNT_STATUS_31_0_KEY9_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY9_USAGE_CNT_STATUS_31_0_KEY9_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY9_USAGE_CNT_STATUS_63_32                                0x000001FC
#define IME_KEY9_USAGE_CNT_STATUS_63_32_KEY9_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY9_USAGE_CNT_STATUS_63_32_KEY9_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY10_USAGE_CNT_STATUS_31_0                                0x00000200
#define IME_KEY10_USAGE_CNT_STATUS_31_0_KEY10_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY10_USAGE_CNT_STATUS_31_0_KEY10_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY10_USAGE_CNT_STATUS_63_32                               0x00000204
#define IME_KEY10_USAGE_CNT_STATUS_63_32_KEY10_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY10_USAGE_CNT_STATUS_63_32_KEY10_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY11_USAGE_CNT_STATUS_31_0                                0x00000208
#define IME_KEY11_USAGE_CNT_STATUS_31_0_KEY11_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY11_USAGE_CNT_STATUS_31_0_KEY11_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY11_USAGE_CNT_STATUS_63_32                               0x0000020C
#define IME_KEY11_USAGE_CNT_STATUS_63_32_KEY11_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY11_USAGE_CNT_STATUS_63_32_KEY11_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY12_USAGE_CNT_STATUS_31_0                                0x00000210
#define IME_KEY12_USAGE_CNT_STATUS_31_0_KEY12_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY12_USAGE_CNT_STATUS_31_0_KEY12_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY12_USAGE_CNT_STATUS_63_32                               0x00000214
#define IME_KEY12_USAGE_CNT_STATUS_63_32_KEY12_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY12_USAGE_CNT_STATUS_63_32_KEY12_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY13_USAGE_CNT_STATUS_31_0                                0x00000218
#define IME_KEY13_USAGE_CNT_STATUS_31_0_KEY13_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY13_USAGE_CNT_STATUS_31_0_KEY13_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY13_USAGE_CNT_STATUS_63_32                               0x0000021C
#define IME_KEY13_USAGE_CNT_STATUS_63_32_KEY13_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY13_USAGE_CNT_STATUS_63_32_KEY13_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY14_USAGE_CNT_STATUS_31_0                                0x00000220
#define IME_KEY14_USAGE_CNT_STATUS_31_0_KEY14_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY14_USAGE_CNT_STATUS_31_0_KEY14_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY14_USAGE_CNT_STATUS_63_32                               0x00000224
#define IME_KEY14_USAGE_CNT_STATUS_63_32_KEY14_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY14_USAGE_CNT_STATUS_63_32_KEY14_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY15_USAGE_CNT_STATUS_31_0                                0x00000228
#define IME_KEY15_USAGE_CNT_STATUS_31_0_KEY15_USAGE_CNT_STATUS_31_0_MASK 0xFFFFFFFF
#define IME_KEY15_USAGE_CNT_STATUS_31_0_KEY15_USAGE_CNT_STATUS_31_0_BIT_OFFSET          0

#define IME_KEY15_USAGE_CNT_STATUS_63_32                               0x0000022C
#define IME_KEY15_USAGE_CNT_STATUS_63_32_KEY15_USAGE_CNT_STATUS_63_32_MASK 0xFFFFFFFF
#define IME_KEY15_USAGE_CNT_STATUS_63_32_KEY15_USAGE_CNT_STATUS_63_32_BIT_OFFSET          0

#define IME_KEY_LOAD_CTRL                                              0x00000300
#define IME_KEY_LOAD_CTRL_KEY_IDX_MASK                                 0x0000FFFF
#define IME_KEY_LOAD_CTRL_KEY_IDX_BIT_OFFSET                                    0
#define IME_KEY_LOAD_CTRL_KEY_SLOT_SEL_MASK                            0x00010000
#define IME_KEY_LOAD_CTRL_KEY_SLOT_SEL_BIT_OFFSET                              16
#define IME_KEY_LOAD_CTRL_KEY_INVALIDATE_MASK                          0x00020000
#define IME_KEY_LOAD_CTRL_KEY_INVALIDATE_BIT_OFFSET                            17
#define IME_KEY_LOAD_CTRL_KEY_SZ_MASK                                  0x00100000
#define IME_KEY_LOAD_CTRL_KEY_SZ_BIT_OFFSET                                    20
#define IME_KEY_LOAD_CTRL_BYPASS_SEL_MASK                              0x00400000
#define IME_KEY_LOAD_CTRL_BYPASS_SEL_BIT_OFFSET                                22

#define IME_KEY_LOAD_STAT                                              0x00000308
#define IME_KEY_LOAD_STAT_BUSY_MASK                                    0x00000001
#define IME_KEY_LOAD_STAT_BUSY_BIT_OFFSET                                       0

#define IME_KEY_SWAP_FORCE_CTRL                                        0x0000030C
#define IME_KEY_SWAP_FORCE_CTRL_KEY0_SWAP_FORCE_MASK                   0x00000001
#define IME_KEY_SWAP_FORCE_CTRL_KEY0_SWAP_FORCE_BIT_OFFSET                      0
#define IME_KEY_SWAP_FORCE_CTRL_KEY1_SWAP_FORCE_MASK                   0x00000002
#define IME_KEY_SWAP_FORCE_CTRL_KEY1_SWAP_FORCE_BIT_OFFSET                      1
#define IME_KEY_SWAP_FORCE_CTRL_KEY2_SWAP_FORCE_MASK                   0x00000004
#define IME_KEY_SWAP_FORCE_CTRL_KEY2_SWAP_FORCE_BIT_OFFSET                      2
#define IME_KEY_SWAP_FORCE_CTRL_KEY3_SWAP_FORCE_MASK                   0x00000008
#define IME_KEY_SWAP_FORCE_CTRL_KEY3_SWAP_FORCE_BIT_OFFSET                      3
#define IME_KEY_SWAP_FORCE_CTRL_KEY4_SWAP_FORCE_MASK                   0x00000010
#define IME_KEY_SWAP_FORCE_CTRL_KEY4_SWAP_FORCE_BIT_OFFSET                      4
#define IME_KEY_SWAP_FORCE_CTRL_KEY5_SWAP_FORCE_MASK                   0x00000020
#define IME_KEY_SWAP_FORCE_CTRL_KEY5_SWAP_FORCE_BIT_OFFSET                      5
#define IME_KEY_SWAP_FORCE_CTRL_KEY6_SWAP_FORCE_MASK                   0x00000040
#define IME_KEY_SWAP_FORCE_CTRL_KEY6_SWAP_FORCE_BIT_OFFSET                      6
#define IME_KEY_SWAP_FORCE_CTRL_KEY7_SWAP_FORCE_MASK                   0x00000080
#define IME_KEY_SWAP_FORCE_CTRL_KEY7_SWAP_FORCE_BIT_OFFSET                      7
#define IME_KEY_SWAP_FORCE_CTRL_KEY8_SWAP_FORCE_MASK                   0x00000100
#define IME_KEY_SWAP_FORCE_CTRL_KEY8_SWAP_FORCE_BIT_OFFSET                      8
#define IME_KEY_SWAP_FORCE_CTRL_KEY9_SWAP_FORCE_MASK                   0x00000200
#define IME_KEY_SWAP_FORCE_CTRL_KEY9_SWAP_FORCE_BIT_OFFSET                      9
#define IME_KEY_SWAP_FORCE_CTRL_KEY10_SWAP_FORCE_MASK                  0x00000400
#define IME_KEY_SWAP_FORCE_CTRL_KEY10_SWAP_FORCE_BIT_OFFSET                    10
#define IME_KEY_SWAP_FORCE_CTRL_KEY11_SWAP_FORCE_MASK                  0x00000800
#define IME_KEY_SWAP_FORCE_CTRL_KEY11_SWAP_FORCE_BIT_OFFSET                    11
#define IME_KEY_SWAP_FORCE_CTRL_KEY12_SWAP_FORCE_MASK                  0x00001000
#define IME_KEY_SWAP_FORCE_CTRL_KEY12_SWAP_FORCE_BIT_OFFSET                    12
#define IME_KEY_SWAP_FORCE_CTRL_KEY13_SWAP_FORCE_MASK                  0x00002000
#define IME_KEY_SWAP_FORCE_CTRL_KEY13_SWAP_FORCE_BIT_OFFSET                    13
#define IME_KEY_SWAP_FORCE_CTRL_KEY14_SWAP_FORCE_MASK                  0x00004000
#define IME_KEY_SWAP_FORCE_CTRL_KEY14_SWAP_FORCE_BIT_OFFSET                    14
#define IME_KEY_SWAP_FORCE_CTRL_KEY15_SWAP_FORCE_MASK                  0x00008000
#define IME_KEY_SWAP_FORCE_CTRL_KEY15_SWAP_FORCE_BIT_OFFSET                    15

#define IME_KEY_RMW_SWAP_EN                                            0x00000310
#define IME_KEY_RMW_SWAP_EN_KEY0_RMW_SWAP_EN_MASK                      0x00000001
#define IME_KEY_RMW_SWAP_EN_KEY0_RMW_SWAP_EN_BIT_OFFSET                         0
#define IME_KEY_RMW_SWAP_EN_KEY1_RMW_SWAP_EN_MASK                      0x00000002
#define IME_KEY_RMW_SWAP_EN_KEY1_RMW_SWAP_EN_BIT_OFFSET                         1
#define IME_KEY_RMW_SWAP_EN_KEY2_RMW_SWAP_EN_MASK                      0x00000004
#define IME_KEY_RMW_SWAP_EN_KEY2_RMW_SWAP_EN_BIT_OFFSET                         2
#define IME_KEY_RMW_SWAP_EN_KEY3_RMW_SWAP_EN_MASK                      0x00000008
#define IME_KEY_RMW_SWAP_EN_KEY3_RMW_SWAP_EN_BIT_OFFSET                         3
#define IME_KEY_RMW_SWAP_EN_KEY4_RMW_SWAP_EN_MASK                      0x00000010
#define IME_KEY_RMW_SWAP_EN_KEY4_RMW_SWAP_EN_BIT_OFFSET                         4
#define IME_KEY_RMW_SWAP_EN_KEY5_RMW_SWAP_EN_MASK                      0x00000020
#define IME_KEY_RMW_SWAP_EN_KEY5_RMW_SWAP_EN_BIT_OFFSET                         5
#define IME_KEY_RMW_SWAP_EN_KEY6_RMW_SWAP_EN_MASK                      0x00000040
#define IME_KEY_RMW_SWAP_EN_KEY6_RMW_SWAP_EN_BIT_OFFSET                         6
#define IME_KEY_RMW_SWAP_EN_KEY7_RMW_SWAP_EN_MASK                      0x00000080
#define IME_KEY_RMW_SWAP_EN_KEY7_RMW_SWAP_EN_BIT_OFFSET                         7
#define IME_KEY_RMW_SWAP_EN_KEY8_RMW_SWAP_EN_MASK                      0x00000100
#define IME_KEY_RMW_SWAP_EN_KEY8_RMW_SWAP_EN_BIT_OFFSET                         8
#define IME_KEY_RMW_SWAP_EN_KEY9_RMW_SWAP_EN_MASK                      0x00000200
#define IME_KEY_RMW_SWAP_EN_KEY9_RMW_SWAP_EN_BIT_OFFSET                         9
#define IME_KEY_RMW_SWAP_EN_KEY10_RMW_SWAP_EN_MASK                     0x00000400
#define IME_KEY_RMW_SWAP_EN_KEY10_RMW_SWAP_EN_BIT_OFFSET                       10
#define IME_KEY_RMW_SWAP_EN_KEY11_RMW_SWAP_EN_MASK                     0x00000800
#define IME_KEY_RMW_SWAP_EN_KEY11_RMW_SWAP_EN_BIT_OFFSET                       11
#define IME_KEY_RMW_SWAP_EN_KEY12_RMW_SWAP_EN_MASK                     0x00001000
#define IME_KEY_RMW_SWAP_EN_KEY12_RMW_SWAP_EN_BIT_OFFSET                       12
#define IME_KEY_RMW_SWAP_EN_KEY13_RMW_SWAP_EN_MASK                     0x00002000
#define IME_KEY_RMW_SWAP_EN_KEY13_RMW_SWAP_EN_BIT_OFFSET                       13
#define IME_KEY_RMW_SWAP_EN_KEY14_RMW_SWAP_EN_MASK                     0x00004000
#define IME_KEY_RMW_SWAP_EN_KEY14_RMW_SWAP_EN_BIT_OFFSET                       14
#define IME_KEY_RMW_SWAP_EN_KEY15_RMW_SWAP_EN_MASK                     0x00008000
#define IME_KEY_RMW_SWAP_EN_KEY15_RMW_SWAP_EN_BIT_OFFSET                       15

#define IME_KEY_SWAP_STATUS                                            0x00000314
#define IME_KEY_SWAP_STATUS_KEY0_SWAP_STATUS_MASK                      0x00000001
#define IME_KEY_SWAP_STATUS_KEY0_SWAP_STATUS_BIT_OFFSET                         0
#define IME_KEY_SWAP_STATUS_KEY1_SWAP_STATUS_MASK                      0x00000002
#define IME_KEY_SWAP_STATUS_KEY1_SWAP_STATUS_BIT_OFFSET                         1
#define IME_KEY_SWAP_STATUS_KEY2_SWAP_STATUS_MASK                      0x00000004
#define IME_KEY_SWAP_STATUS_KEY2_SWAP_STATUS_BIT_OFFSET                         2
#define IME_KEY_SWAP_STATUS_KEY3_SWAP_STATUS_MASK                      0x00000008
#define IME_KEY_SWAP_STATUS_KEY3_SWAP_STATUS_BIT_OFFSET                         3
#define IME_KEY_SWAP_STATUS_KEY4_SWAP_STATUS_MASK                      0x00000010
#define IME_KEY_SWAP_STATUS_KEY4_SWAP_STATUS_BIT_OFFSET                         4
#define IME_KEY_SWAP_STATUS_KEY5_SWAP_STATUS_MASK                      0x00000020
#define IME_KEY_SWAP_STATUS_KEY5_SWAP_STATUS_BIT_OFFSET                         5
#define IME_KEY_SWAP_STATUS_KEY6_SWAP_STATUS_MASK                      0x00000040
#define IME_KEY_SWAP_STATUS_KEY6_SWAP_STATUS_BIT_OFFSET                         6
#define IME_KEY_SWAP_STATUS_KEY7_SWAP_STATUS_MASK                      0x00000080
#define IME_KEY_SWAP_STATUS_KEY7_SWAP_STATUS_BIT_OFFSET                         7
#define IME_KEY_SWAP_STATUS_KEY8_SWAP_STATUS_MASK                      0x00000100
#define IME_KEY_SWAP_STATUS_KEY8_SWAP_STATUS_BIT_OFFSET                         8
#define IME_KEY_SWAP_STATUS_KEY9_SWAP_STATUS_MASK                      0x00000200
#define IME_KEY_SWAP_STATUS_KEY9_SWAP_STATUS_BIT_OFFSET                         9
#define IME_KEY_SWAP_STATUS_KEY10_SWAP_STATUS_MASK                     0x00000400
#define IME_KEY_SWAP_STATUS_KEY10_SWAP_STATUS_BIT_OFFSET                       10
#define IME_KEY_SWAP_STATUS_KEY11_SWAP_STATUS_MASK                     0x00000800
#define IME_KEY_SWAP_STATUS_KEY11_SWAP_STATUS_BIT_OFFSET                       11
#define IME_KEY_SWAP_STATUS_KEY12_SWAP_STATUS_MASK                     0x00001000
#define IME_KEY_SWAP_STATUS_KEY12_SWAP_STATUS_BIT_OFFSET                       12
#define IME_KEY_SWAP_STATUS_KEY13_SWAP_STATUS_MASK                     0x00002000
#define IME_KEY_SWAP_STATUS_KEY13_SWAP_STATUS_BIT_OFFSET                       13
#define IME_KEY_SWAP_STATUS_KEY14_SWAP_STATUS_MASK                     0x00004000
#define IME_KEY_SWAP_STATUS_KEY14_SWAP_STATUS_BIT_OFFSET                       14
#define IME_KEY_SWAP_STATUS_KEY15_SWAP_STATUS_MASK                     0x00008000
#define IME_KEY_SWAP_STATUS_KEY15_SWAP_STATUS_BIT_OFFSET                       15

#define IME_CKEY_0                                                     0x00000330
#define IME_CKEY_0_CKEY_0_MASK                                         0xFFFFFFFF
#define IME_CKEY_0_CKEY_0_BIT_OFFSET                                            0

#define IME_CKEY_1                                                     0x00000334
#define IME_CKEY_1_CKEY_1_MASK                                         0xFFFFFFFF
#define IME_CKEY_1_CKEY_1_BIT_OFFSET                                            0

#define IME_CKEY_2                                                     0x00000338
#define IME_CKEY_2_CKEY_2_MASK                                         0xFFFFFFFF
#define IME_CKEY_2_CKEY_2_BIT_OFFSET                                            0

#define IME_CKEY_3                                                     0x0000033C
#define IME_CKEY_3_CKEY_3_MASK                                         0xFFFFFFFF
#define IME_CKEY_3_CKEY_3_BIT_OFFSET                                            0

#define IME_CKEY_4                                                     0x00000340
#define IME_CKEY_4_CKEY_4_MASK                                         0xFFFFFFFF
#define IME_CKEY_4_CKEY_4_BIT_OFFSET                                            0

#define IME_CKEY_5                                                     0x00000344
#define IME_CKEY_5_CKEY_5_MASK                                         0xFFFFFFFF
#define IME_CKEY_5_CKEY_5_BIT_OFFSET                                            0

#define IME_CKEY_6                                                     0x00000348
#define IME_CKEY_6_CKEY_6_MASK                                         0xFFFFFFFF
#define IME_CKEY_6_CKEY_6_BIT_OFFSET                                            0

#define IME_CKEY_7                                                     0x0000034C
#define IME_CKEY_7_CKEY_7_MASK                                         0xFFFFFFFF
#define IME_CKEY_7_CKEY_7_BIT_OFFSET                                            0

#define IME_TKEY_0                                                     0x00000350
#define IME_TKEY_0_TKEY_0_MASK                                         0xFFFFFFFF
#define IME_TKEY_0_TKEY_0_BIT_OFFSET                                            0

#define IME_TKEY_1                                                     0x00000354
#define IME_TKEY_1_TKEY_1_MASK                                         0xFFFFFFFF
#define IME_TKEY_1_TKEY_1_BIT_OFFSET                                            0

#define IME_TKEY_2                                                     0x00000358
#define IME_TKEY_2_TKEY_2_MASK                                         0xFFFFFFFF
#define IME_TKEY_2_TKEY_2_BIT_OFFSET                                            0

#define IME_TKEY_3                                                     0x0000035C
#define IME_TKEY_3_TKEY_3_MASK                                         0xFFFFFFFF
#define IME_TKEY_3_TKEY_3_BIT_OFFSET                                            0

#define IME_TKEY_4                                                     0x00000360
#define IME_TKEY_4_TKEY_4_MASK                                         0xFFFFFFFF
#define IME_TKEY_4_TKEY_4_BIT_OFFSET                                            0

#define IME_TKEY_5                                                     0x00000364
#define IME_TKEY_5_TKEY_5_MASK                                         0xFFFFFFFF
#define IME_TKEY_5_TKEY_5_BIT_OFFSET                                            0

#define IME_TKEY_6                                                     0x00000368
#define IME_TKEY_6_TKEY_6_MASK                                         0xFFFFFFFF
#define IME_TKEY_6_TKEY_6_BIT_OFFSET                                            0

#define IME_TKEY_7                                                     0x0000036C
#define IME_TKEY_7_TKEY_7_MASK                                         0xFFFFFFFF
#define IME_TKEY_7_TKEY_7_BIT_OFFSET                                            0

#define IME_POISON_CFG                                                 0x00000370
#define IME_POISON_CFG_WRCH_TKEY_POISON_EN_MASK                        0x00000001
#define IME_POISON_CFG_WRCH_TKEY_POISON_EN_BIT_OFFSET                           0
#define IME_POISON_CFG_WRCH_CKEY_POISON_EN_MASK                        0x00000002
#define IME_POISON_CFG_WRCH_CKEY_POISON_EN_BIT_OFFSET                           1
#define IME_POISON_CFG_WRCH_TVAL_POISON_EN_MASK                        0x00000004
#define IME_POISON_CFG_WRCH_TVAL_POISON_EN_BIT_OFFSET                           2
#define IME_POISON_CFG_RDCH_TKEY_POISON_EN_MASK                        0x00000008
#define IME_POISON_CFG_RDCH_TKEY_POISON_EN_BIT_OFFSET                           3
#define IME_POISON_CFG_RDCH_CKEY_POISON_EN_MASK                        0x00000010
#define IME_POISON_CFG_RDCH_CKEY_POISON_EN_BIT_OFFSET                           4
#define IME_POISON_CFG_RDCH_TVAL_POISON_EN_MASK                        0x00000020
#define IME_POISON_CFG_RDCH_TVAL_POISON_EN_BIT_OFFSET                           5
#define IME_POISON_CFG_WRCH_TKEY_POISON_BIT_MASK                       0x00000040
#define IME_POISON_CFG_WRCH_TKEY_POISON_BIT_BIT_OFFSET                          6
#define IME_POISON_CFG_WRCH_CKEY_POISON_BIT_MASK                       0x00000080
#define IME_POISON_CFG_WRCH_CKEY_POISON_BIT_BIT_OFFSET                          7
#define IME_POISON_CFG_WRCH_TVAL_POISON_BIT_MASK                       0x00000100
#define IME_POISON_CFG_WRCH_TVAL_POISON_BIT_BIT_OFFSET                          8
#define IME_POISON_CFG_RDCH_TKEY_POISON_BIT_MASK                       0x00000200
#define IME_POISON_CFG_RDCH_TKEY_POISON_BIT_BIT_OFFSET                          9
#define IME_POISON_CFG_RDCH_CKEY_POISON_BIT_MASK                       0x00000400
#define IME_POISON_CFG_RDCH_CKEY_POISON_BIT_BIT_OFFSET                         10
#define IME_POISON_CFG_RDCH_TVAL_POISON_BIT_MASK                       0x00000800
#define IME_POISON_CFG_RDCH_TVAL_POISON_BIT_BIT_OFFSET                         11

#define IME_WRCH_TKEY_FLIP_BIT_POS                                     0x00000374
#define IME_WRCH_TKEY_FLIP_BIT_POS_WRCH_TKEY_FLIP_BIT_POS0_MASK        0x0000FFFF
#define IME_WRCH_TKEY_FLIP_BIT_POS_WRCH_TKEY_FLIP_BIT_POS0_BIT_OFFSET           0
#define IME_WRCH_TKEY_FLIP_BIT_POS_WRCH_TKEY_FLIP_BIT_POS1_MASK        0xFFFF0000
#define IME_WRCH_TKEY_FLIP_BIT_POS_WRCH_TKEY_FLIP_BIT_POS1_BIT_OFFSET          16

#define IME_WRCH_CKEY_FLIP_BIT_POS                                     0x00000378
#define IME_WRCH_CKEY_FLIP_BIT_POS_WRCH_CKEY_FLIP_BIT_POS0_MASK        0x0000FFFF
#define IME_WRCH_CKEY_FLIP_BIT_POS_WRCH_CKEY_FLIP_BIT_POS0_BIT_OFFSET           0
#define IME_WRCH_CKEY_FLIP_BIT_POS_WRCH_CKEY_FLIP_BIT_POS1_MASK        0xFFFF0000
#define IME_WRCH_CKEY_FLIP_BIT_POS_WRCH_CKEY_FLIP_BIT_POS1_BIT_OFFSET          16

#define IME_WRCH_TVAL_FLIP_BIT_POS                                     0x0000037C
#define IME_WRCH_TVAL_FLIP_BIT_POS_WRCH_TVAL_FLIP_BIT_POS0_MASK        0x000000FF
#define IME_WRCH_TVAL_FLIP_BIT_POS_WRCH_TVAL_FLIP_BIT_POS0_BIT_OFFSET           0
#define IME_WRCH_TVAL_FLIP_BIT_POS_WRCH_TVAL_FLIP_BIT_POS1_MASK        0x00FF0000
#define IME_WRCH_TVAL_FLIP_BIT_POS_WRCH_TVAL_FLIP_BIT_POS1_BIT_OFFSET          16

#define IME_RDCH_TKEY_FLIP_BIT_POS                                     0x00000380
#define IME_RDCH_TKEY_FLIP_BIT_POS_RDCH_TKEY_FLIP_BIT_POS0_MASK        0x0000FFFF
#define IME_RDCH_TKEY_FLIP_BIT_POS_RDCH_TKEY_FLIP_BIT_POS0_BIT_OFFSET           0
#define IME_RDCH_TKEY_FLIP_BIT_POS_RDCH_TKEY_FLIP_BIT_POS1_MASK        0xFFFF0000
#define IME_RDCH_TKEY_FLIP_BIT_POS_RDCH_TKEY_FLIP_BIT_POS1_BIT_OFFSET          16

#define IME_RDCH_CKEY_FLIP_BIT_POS                                     0x00000384
#define IME_RDCH_CKEY_FLIP_BIT_POS_RDCH_CKEY_FLIP_BIT_POS0_MASK        0x0000FFFF
#define IME_RDCH_CKEY_FLIP_BIT_POS_RDCH_CKEY_FLIP_BIT_POS0_BIT_OFFSET           0
#define IME_RDCH_CKEY_FLIP_BIT_POS_RDCH_CKEY_FLIP_BIT_POS1_MASK        0xFFFF0000
#define IME_RDCH_CKEY_FLIP_BIT_POS_RDCH_CKEY_FLIP_BIT_POS1_BIT_OFFSET          16

#define IME_RDCH_TVAL_FLIP_BIT_POS                                     0x00000388
#define IME_RDCH_TVAL_FLIP_BIT_POS_RDCH_TVAL_FLIP_BIT_POS0_MASK        0x000000FF
#define IME_RDCH_TVAL_FLIP_BIT_POS_RDCH_TVAL_FLIP_BIT_POS0_BIT_OFFSET           0
#define IME_RDCH_TVAL_FLIP_BIT_POS_RDCH_TVAL_FLIP_BIT_POS1_MASK        0x00FF0000
#define IME_RDCH_TVAL_FLIP_BIT_POS_RDCH_TVAL_FLIP_BIT_POS1_BIT_OFFSET          16

#define IME_WRCH_TKEY_POISON_ADDR                                      0x0000038C
#define IME_WRCH_TKEY_POISON_ADDR_WRCH_TKEY_POISON_ADDR_MASK           0xFFFFFFFF
#define IME_WRCH_TKEY_POISON_ADDR_WRCH_TKEY_POISON_ADDR_BIT_OFFSET              0

#define IME_WRCH_CKEY_POISON_ADDR                                      0x00000390
#define IME_WRCH_CKEY_POISON_ADDR_WRCH_CKEY_POISON_ADDR_MASK           0xFFFFFFFF
#define IME_WRCH_CKEY_POISON_ADDR_WRCH_CKEY_POISON_ADDR_BIT_OFFSET              0

#define IME_WRCH_TVAL_POISON_ADDR                                      0x00000394
#define IME_WRCH_TVAL_POISON_ADDR_WRCH_TVAL_POISON_ADDR_MASK           0xFFFFFFFF
#define IME_WRCH_TVAL_POISON_ADDR_WRCH_TVAL_POISON_ADDR_BIT_OFFSET              0

#define IME_RDCH_TKEY_POISON_ADDR                                      0x00000398
#define IME_RDCH_TKEY_POISON_ADDR_RDCH_TKEY_POISON_ADDR_MASK           0xFFFFFFFF
#define IME_RDCH_TKEY_POISON_ADDR_RDCH_TKEY_POISON_ADDR_BIT_OFFSET              0

#define IME_RDCH_CKEY_POISON_ADDR                                      0x0000039C
#define IME_RDCH_CKEY_POISON_ADDR_RDCH_CKEY_POISON_ADDR_MASK           0xFFFFFFFF
#define IME_RDCH_CKEY_POISON_ADDR_RDCH_CKEY_POISON_ADDR_BIT_OFFSET              0

#define IME_RDCH_TVAL_POISON_ADDR                                      0x000003A0
#define IME_RDCH_TVAL_POISON_ADDR_RDCH_TVAL_POISON_ADDR_MASK           0xFFFFFFFF
#define IME_RDCH_TVAL_POISON_ADDR_RDCH_TVAL_POISON_ADDR_BIT_OFFSET              0

#define IME_ECC_ERR_STAT                                               0x000003A4
#define IME_ECC_ERR_STAT_WRCH_TKEY_ECCC_STAT_MASK                      0x00000001
#define IME_ECC_ERR_STAT_WRCH_TKEY_ECCC_STAT_BIT_OFFSET                         0
#define IME_ECC_ERR_STAT_WRCH_TKEY_ECCU_STAT_MASK                      0x00000002
#define IME_ECC_ERR_STAT_WRCH_TKEY_ECCU_STAT_BIT_OFFSET                         1
#define IME_ECC_ERR_STAT_WRCH_CKEY_ECCC_STAT_MASK                      0x00000004
#define IME_ECC_ERR_STAT_WRCH_CKEY_ECCC_STAT_BIT_OFFSET                         2
#define IME_ECC_ERR_STAT_WRCH_CKEY_ECCU_STAT_MASK                      0x00000008
#define IME_ECC_ERR_STAT_WRCH_CKEY_ECCU_STAT_BIT_OFFSET                         3
#define IME_ECC_ERR_STAT_WRCH_TVAL_ECCC_STAT_MASK                      0x00000010
#define IME_ECC_ERR_STAT_WRCH_TVAL_ECCC_STAT_BIT_OFFSET                         4
#define IME_ECC_ERR_STAT_WRCH_TVAL_ECCU_STAT_MASK                      0x00000020
#define IME_ECC_ERR_STAT_WRCH_TVAL_ECCU_STAT_BIT_OFFSET                         5
#define IME_ECC_ERR_STAT_RDCH_TKEY_ECCC_STAT_MASK                      0x00000040
#define IME_ECC_ERR_STAT_RDCH_TKEY_ECCC_STAT_BIT_OFFSET                         6
#define IME_ECC_ERR_STAT_RDCH_TKEY_ECCU_STAT_MASK                      0x00000080
#define IME_ECC_ERR_STAT_RDCH_TKEY_ECCU_STAT_BIT_OFFSET                         7
#define IME_ECC_ERR_STAT_RDCH_CKEY_ECCC_STAT_MASK                      0x00000100
#define IME_ECC_ERR_STAT_RDCH_CKEY_ECCC_STAT_BIT_OFFSET                         8
#define IME_ECC_ERR_STAT_RDCH_CKEY_ECCU_STAT_MASK                      0x00000200
#define IME_ECC_ERR_STAT_RDCH_CKEY_ECCU_STAT_BIT_OFFSET                         9
#define IME_ECC_ERR_STAT_RDCH_TVAL_ECCC_STAT_MASK                      0x00000400
#define IME_ECC_ERR_STAT_RDCH_TVAL_ECCC_STAT_BIT_OFFSET                        10
#define IME_ECC_ERR_STAT_RDCH_TVAL_ECCU_STAT_MASK                      0x00000800
#define IME_ECC_ERR_STAT_RDCH_TVAL_ECCU_STAT_BIT_OFFSET                        11

#define IME_WRCH_ECCC_SYN                                              0x000003A8
#define IME_WRCH_ECCC_SYN_WRCH_TKEY_ECCC_SYN_MASK                      0x000003FF
#define IME_WRCH_ECCC_SYN_WRCH_TKEY_ECCC_SYN_BIT_OFFSET                         0
#define IME_WRCH_ECCC_SYN_WRCH_CKEY_ECCC_SYN_MASK                      0x000FFC00
#define IME_WRCH_ECCC_SYN_WRCH_CKEY_ECCC_SYN_BIT_OFFSET                        10
#define IME_WRCH_ECCC_SYN_WRCH_TVAL_ECCC_SYN_MASK                      0x1FF00000
#define IME_WRCH_ECCC_SYN_WRCH_TVAL_ECCC_SYN_BIT_OFFSET                        20

#define IME_WRCH_ECCU_SYN                                              0x000003AC
#define IME_WRCH_ECCU_SYN_WRCH_TKEY_ECCU_SYN_MASK                      0x000003FF
#define IME_WRCH_ECCU_SYN_WRCH_TKEY_ECCU_SYN_BIT_OFFSET                         0
#define IME_WRCH_ECCU_SYN_WRCH_CKEY_ECCU_SYN_MASK                      0x000FFC00
#define IME_WRCH_ECCU_SYN_WRCH_CKEY_ECCU_SYN_BIT_OFFSET                        10
#define IME_WRCH_ECCU_SYN_WRCH_TVAL_ECCU_SYN_MASK                      0x1FF00000
#define IME_WRCH_ECCU_SYN_WRCH_TVAL_ECCU_SYN_BIT_OFFSET                        20

#define IME_RDCH_ECCC_SYN                                              0x000003B0
#define IME_RDCH_ECCC_SYN_RDCH_TKEY_ECCC_SYN_MASK                      0x000003FF
#define IME_RDCH_ECCC_SYN_RDCH_TKEY_ECCC_SYN_BIT_OFFSET                         0
#define IME_RDCH_ECCC_SYN_RDCH_CKEY_ECCC_SYN_MASK                      0x000FFC00
#define IME_RDCH_ECCC_SYN_RDCH_CKEY_ECCC_SYN_BIT_OFFSET                        10
#define IME_RDCH_ECCC_SYN_RDCH_TVAL_ECCC_SYN_MASK                      0x1FF00000
#define IME_RDCH_ECCC_SYN_RDCH_TVAL_ECCC_SYN_BIT_OFFSET                        20

#define IME_RDCH_ECCU_SYN                                              0x000003B4
#define IME_RDCH_ECCU_SYN_RDCH_TKEY_ECCU_SYN_MASK                      0x000003FF
#define IME_RDCH_ECCU_SYN_RDCH_TKEY_ECCU_SYN_BIT_OFFSET                         0
#define IME_RDCH_ECCU_SYN_RDCH_CKEY_ECCU_SYN_MASK                      0x000FFC00
#define IME_RDCH_ECCU_SYN_RDCH_CKEY_ECCU_SYN_BIT_OFFSET                        10
#define IME_RDCH_ECCU_SYN_RDCH_TVAL_ECCU_SYN_MASK                      0x1FF00000
#define IME_RDCH_ECCU_SYN_RDCH_TVAL_ECCU_SYN_BIT_OFFSET                        20

#define IME_WRCH_TKEY_ECC_ADDR                                         0x000003B8
#define IME_WRCH_TKEY_ECC_ADDR_WRCH_TKEY_ECCC_ADDR_MASK                0x0000FFFF
#define IME_WRCH_TKEY_ECC_ADDR_WRCH_TKEY_ECCC_ADDR_BIT_OFFSET                   0
#define IME_WRCH_TKEY_ECC_ADDR_WRCH_TKEY_ECCU_ADDR_MASK                0xFFFF0000
#define IME_WRCH_TKEY_ECC_ADDR_WRCH_TKEY_ECCU_ADDR_BIT_OFFSET                  16

#define IME_WRCH_CKEY_ECC_ADDR                                         0x000003BC
#define IME_WRCH_CKEY_ECC_ADDR_WRCH_CKEY_ECCC_ADDR_MASK                0x0000FFFF
#define IME_WRCH_CKEY_ECC_ADDR_WRCH_CKEY_ECCC_ADDR_BIT_OFFSET                   0
#define IME_WRCH_CKEY_ECC_ADDR_WRCH_CKEY_ECCU_ADDR_MASK                0xFFFF0000
#define IME_WRCH_CKEY_ECC_ADDR_WRCH_CKEY_ECCU_ADDR_BIT_OFFSET                  16

#define IME_WRCH_TVAL_ECC_ADDR                                         0x000003C0
#define IME_WRCH_TVAL_ECC_ADDR_WRCH_TVAL_ECCC_ADDR_MASK                0x0000FFFF
#define IME_WRCH_TVAL_ECC_ADDR_WRCH_TVAL_ECCC_ADDR_BIT_OFFSET                   0
#define IME_WRCH_TVAL_ECC_ADDR_WRCH_TVAL_ECCU_ADDR_MASK                0xFFFF0000
#define IME_WRCH_TVAL_ECC_ADDR_WRCH_TVAL_ECCU_ADDR_BIT_OFFSET                  16

#define IME_RDCH_TKEY_ECC_ADDR                                         0x000003C4
#define IME_RDCH_TKEY_ECC_ADDR_RDCH_TKEY_ECCC_ADDR_MASK                0x0000FFFF
#define IME_RDCH_TKEY_ECC_ADDR_RDCH_TKEY_ECCC_ADDR_BIT_OFFSET                   0
#define IME_RDCH_TKEY_ECC_ADDR_RDCH_TKEY_ECCU_ADDR_MASK                0xFFFF0000
#define IME_RDCH_TKEY_ECC_ADDR_RDCH_TKEY_ECCU_ADDR_BIT_OFFSET                  16

#define IME_RDCH_CKEY_ECC_ADDR                                         0x000003C8
#define IME_RDCH_CKEY_ECC_ADDR_RDCH_CKEY_ECCC_ADDR_MASK                0x0000FFFF
#define IME_RDCH_CKEY_ECC_ADDR_RDCH_CKEY_ECCC_ADDR_BIT_OFFSET                   0
#define IME_RDCH_CKEY_ECC_ADDR_RDCH_CKEY_ECCU_ADDR_MASK                0xFFFF0000
#define IME_RDCH_CKEY_ECC_ADDR_RDCH_CKEY_ECCU_ADDR_BIT_OFFSET                  16

#define IME_RDCH_TVAL_ECC_ADDR                                         0x000003CC
#define IME_RDCH_TVAL_ECC_ADDR_RDCH_TVAL_ECCC_ADDR_MASK                0x0000FFFF
#define IME_RDCH_TVAL_ECC_ADDR_RDCH_TVAL_ECCC_ADDR_BIT_OFFSET                   0
#define IME_RDCH_TVAL_ECC_ADDR_RDCH_TVAL_ECCU_ADDR_MASK                0xFFFF0000
#define IME_RDCH_TVAL_ECC_ADDR_RDCH_TVAL_ECCU_ADDR_BIT_OFFSET                  16

#define IME_ECC_IRQ_EN                                                 0x000003D0
#define IME_ECC_IRQ_EN_WRCH_TKEY_ECCC_IRQ_EN_MASK                      0x00000001
#define IME_ECC_IRQ_EN_WRCH_TKEY_ECCC_IRQ_EN_BIT_OFFSET                         0
#define IME_ECC_IRQ_EN_WRCH_TKEY_ECCU_IRQ_EN_MASK                      0x00000002
#define IME_ECC_IRQ_EN_WRCH_TKEY_ECCU_IRQ_EN_BIT_OFFSET                         1
#define IME_ECC_IRQ_EN_WRCH_CKEY_ECCC_IRQ_EN_MASK                      0x00000004
#define IME_ECC_IRQ_EN_WRCH_CKEY_ECCC_IRQ_EN_BIT_OFFSET                         2
#define IME_ECC_IRQ_EN_WRCH_CKEY_ECCU_IRQ_EN_MASK                      0x00000008
#define IME_ECC_IRQ_EN_WRCH_CKEY_ECCU_IRQ_EN_BIT_OFFSET                         3
#define IME_ECC_IRQ_EN_WRCH_TVAL_ECCC_IRQ_EN_MASK                      0x00000010
#define IME_ECC_IRQ_EN_WRCH_TVAL_ECCC_IRQ_EN_BIT_OFFSET                         4
#define IME_ECC_IRQ_EN_WRCH_TVAL_ECCU_IRQ_EN_MASK                      0x00000020
#define IME_ECC_IRQ_EN_WRCH_TVAL_ECCU_IRQ_EN_BIT_OFFSET                         5
#define IME_ECC_IRQ_EN_RDCH_TKEY_ECCC_IRQ_EN_MASK                      0x00000040
#define IME_ECC_IRQ_EN_RDCH_TKEY_ECCC_IRQ_EN_BIT_OFFSET                         6
#define IME_ECC_IRQ_EN_RDCH_TKEY_ECCU_IRQ_EN_MASK                      0x00000080
#define IME_ECC_IRQ_EN_RDCH_TKEY_ECCU_IRQ_EN_BIT_OFFSET                         7
#define IME_ECC_IRQ_EN_RDCH_CKEY_ECCC_IRQ_EN_MASK                      0x00000100
#define IME_ECC_IRQ_EN_RDCH_CKEY_ECCC_IRQ_EN_BIT_OFFSET                         8
#define IME_ECC_IRQ_EN_RDCH_CKEY_ECCU_IRQ_EN_MASK                      0x00000200
#define IME_ECC_IRQ_EN_RDCH_CKEY_ECCU_IRQ_EN_BIT_OFFSET                         9
#define IME_ECC_IRQ_EN_RDCH_TVAL_ECCC_IRQ_EN_MASK                      0x00000400
#define IME_ECC_IRQ_EN_RDCH_TVAL_ECCC_IRQ_EN_BIT_OFFSET                        10
#define IME_ECC_IRQ_EN_RDCH_TVAL_ECCU_IRQ_EN_MASK                      0x00000800
#define IME_ECC_IRQ_EN_RDCH_TVAL_ECCU_IRQ_EN_BIT_OFFSET                        11

#define IME_ECC_IRQ_STAT                                               0x000003D4
#define IME_ECC_IRQ_STAT_WRCH_TKEY_ECCC_IRQ_STAT_MASK                  0x00000001
#define IME_ECC_IRQ_STAT_WRCH_TKEY_ECCC_IRQ_STAT_BIT_OFFSET                     0
#define IME_ECC_IRQ_STAT_WRCH_TKEY_ECCU_IRQ_STAT_MASK                  0x00000002
#define IME_ECC_IRQ_STAT_WRCH_TKEY_ECCU_IRQ_STAT_BIT_OFFSET                     1
#define IME_ECC_IRQ_STAT_WRCH_CKEY_ECCC_IRQ_STAT_MASK                  0x00000004
#define IME_ECC_IRQ_STAT_WRCH_CKEY_ECCC_IRQ_STAT_BIT_OFFSET                     2
#define IME_ECC_IRQ_STAT_WRCH_CKEY_ECCU_IRQ_STAT_MASK                  0x00000008
#define IME_ECC_IRQ_STAT_WRCH_CKEY_ECCU_IRQ_STAT_BIT_OFFSET                     3
#define IME_ECC_IRQ_STAT_WRCH_TVAL_ECCC_IRQ_STAT_MASK                  0x00000010
#define IME_ECC_IRQ_STAT_WRCH_TVAL_ECCC_IRQ_STAT_BIT_OFFSET                     4
#define IME_ECC_IRQ_STAT_WRCH_TVAL_ECCU_IRQ_STAT_MASK                  0x00000020
#define IME_ECC_IRQ_STAT_WRCH_TVAL_ECCU_IRQ_STAT_BIT_OFFSET                     5
#define IME_ECC_IRQ_STAT_RDCH_TKEY_ECCC_IRQ_STAT_MASK                  0x00000040
#define IME_ECC_IRQ_STAT_RDCH_TKEY_ECCC_IRQ_STAT_BIT_OFFSET                     6
#define IME_ECC_IRQ_STAT_RDCH_TKEY_ECCU_IRQ_STAT_MASK                  0x00000080
#define IME_ECC_IRQ_STAT_RDCH_TKEY_ECCU_IRQ_STAT_BIT_OFFSET                     7
#define IME_ECC_IRQ_STAT_RDCH_CKEY_ECCC_IRQ_STAT_MASK                  0x00000100
#define IME_ECC_IRQ_STAT_RDCH_CKEY_ECCC_IRQ_STAT_BIT_OFFSET                     8
#define IME_ECC_IRQ_STAT_RDCH_CKEY_ECCU_IRQ_STAT_MASK                  0x00000200
#define IME_ECC_IRQ_STAT_RDCH_CKEY_ECCU_IRQ_STAT_BIT_OFFSET                     9
#define IME_ECC_IRQ_STAT_RDCH_TVAL_ECCC_IRQ_STAT_MASK                  0x00000400
#define IME_ECC_IRQ_STAT_RDCH_TVAL_ECCC_IRQ_STAT_BIT_OFFSET                    10
#define IME_ECC_IRQ_STAT_RDCH_TVAL_ECCU_IRQ_STAT_MASK                  0x00000800
#define IME_ECC_IRQ_STAT_RDCH_TVAL_ECCU_IRQ_STAT_BIT_OFFSET                    11

#define IME_WRCH_TKEY_ECC_ERR_CNT                                      0x000003D8
#define IME_WRCH_TKEY_ECC_ERR_CNT_WRCH_TKEY_ECCC_ERR_CNT_MASK          0x0000FFFF
#define IME_WRCH_TKEY_ECC_ERR_CNT_WRCH_TKEY_ECCC_ERR_CNT_BIT_OFFSET             0
#define IME_WRCH_TKEY_ECC_ERR_CNT_WRCH_TKEY_ECCU_ERR_CNT_MASK          0xFFFF0000
#define IME_WRCH_TKEY_ECC_ERR_CNT_WRCH_TKEY_ECCU_ERR_CNT_BIT_OFFSET            16

#define IME_WRCH_CKEY_ECC_ERR_CNT                                      0x000003DC
#define IME_WRCH_CKEY_ECC_ERR_CNT_WRCH_CKEY_ECCC_ERR_CNT_MASK          0x0000FFFF
#define IME_WRCH_CKEY_ECC_ERR_CNT_WRCH_CKEY_ECCC_ERR_CNT_BIT_OFFSET             0
#define IME_WRCH_CKEY_ECC_ERR_CNT_WRCH_CKEY_ECCU_ERR_CNT_MASK          0xFFFF0000
#define IME_WRCH_CKEY_ECC_ERR_CNT_WRCH_CKEY_ECCU_ERR_CNT_BIT_OFFSET            16

#define IME_WRCH_TVAL_ECC_ERR_CNT                                      0x000003E0
#define IME_WRCH_TVAL_ECC_ERR_CNT_WRCH_TVAL_ECCC_ERR_CNT_MASK          0x0000FFFF
#define IME_WRCH_TVAL_ECC_ERR_CNT_WRCH_TVAL_ECCC_ERR_CNT_BIT_OFFSET             0
#define IME_WRCH_TVAL_ECC_ERR_CNT_WRCH_TVAL_ECCU_ERR_CNT_MASK          0xFFFF0000
#define IME_WRCH_TVAL_ECC_ERR_CNT_WRCH_TVAL_ECCU_ERR_CNT_BIT_OFFSET            16

#define IME_RDCH_TKEY_ECC_ERR_CNT                                      0x000003E4
#define IME_RDCH_TKEY_ECC_ERR_CNT_RDCH_TKEY_ECCC_ERR_CNT_MASK          0x0000FFFF
#define IME_RDCH_TKEY_ECC_ERR_CNT_RDCH_TKEY_ECCC_ERR_CNT_BIT_OFFSET             0
#define IME_RDCH_TKEY_ECC_ERR_CNT_RDCH_TKEY_ECCU_ERR_CNT_MASK          0xFFFF0000
#define IME_RDCH_TKEY_ECC_ERR_CNT_RDCH_TKEY_ECCU_ERR_CNT_BIT_OFFSET            16

#define IME_RDCH_CKEY_ECC_ERR_CNT                                      0x000003E8
#define IME_RDCH_CKEY_ECC_ERR_CNT_RDCH_CKEY_ECCC_ERR_CNT_MASK          0x0000FFFF
#define IME_RDCH_CKEY_ECC_ERR_CNT_RDCH_CKEY_ECCC_ERR_CNT_BIT_OFFSET             0
#define IME_RDCH_CKEY_ECC_ERR_CNT_RDCH_CKEY_ECCU_ERR_CNT_MASK          0xFFFF0000
#define IME_RDCH_CKEY_ECC_ERR_CNT_RDCH_CKEY_ECCU_ERR_CNT_BIT_OFFSET            16

#define IME_RDCH_TVAL_ECC_ERR_CNT                                      0x000003EC
#define IME_RDCH_TVAL_ECC_ERR_CNT_RDCH_TVAL_ECCC_ERR_CNT_MASK          0x0000FFFF
#define IME_RDCH_TVAL_ECC_ERR_CNT_RDCH_TVAL_ECCC_ERR_CNT_BIT_OFFSET             0
#define IME_RDCH_TVAL_ECC_ERR_CNT_RDCH_TVAL_ECCU_ERR_CNT_MASK          0xFFFF0000
#define IME_RDCH_TVAL_ECC_ERR_CNT_RDCH_TVAL_ECCU_ERR_CNT_BIT_OFFSET            16

#define IME_WRCH_TKEY_ECC_ERR_THR                                      0x000003F0
#define IME_WRCH_TKEY_ECC_ERR_THR_WRCH_TKEY_ECCC_ERR_THR_MASK          0x0000FFFF
#define IME_WRCH_TKEY_ECC_ERR_THR_WRCH_TKEY_ECCC_ERR_THR_BIT_OFFSET             0
#define IME_WRCH_TKEY_ECC_ERR_THR_WRCH_TKEY_ECCU_ERR_THR_MASK          0xFFFF0000
#define IME_WRCH_TKEY_ECC_ERR_THR_WRCH_TKEY_ECCU_ERR_THR_BIT_OFFSET            16

#define IME_WRCH_CKEY_ECC_ERR_THR                                      0x000003F4
#define IME_WRCH_CKEY_ECC_ERR_THR_WRCH_CKEY_ECCC_ERR_THR_MASK          0x0000FFFF
#define IME_WRCH_CKEY_ECC_ERR_THR_WRCH_CKEY_ECCC_ERR_THR_BIT_OFFSET             0
#define IME_WRCH_CKEY_ECC_ERR_THR_WRCH_CKEY_ECCU_ERR_THR_MASK          0xFFFF0000
#define IME_WRCH_CKEY_ECC_ERR_THR_WRCH_CKEY_ECCU_ERR_THR_BIT_OFFSET            16

#define IME_WRCH_TVAL_ECC_ERR_THR                                      0x000003F8
#define IME_WRCH_TVAL_ECC_ERR_THR_WRCH_TVAL_ECCC_ERR_THR_MASK          0x0000FFFF
#define IME_WRCH_TVAL_ECC_ERR_THR_WRCH_TVAL_ECCC_ERR_THR_BIT_OFFSET             0
#define IME_WRCH_TVAL_ECC_ERR_THR_WRCH_TVAL_ECCU_ERR_THR_MASK          0xFFFF0000
#define IME_WRCH_TVAL_ECC_ERR_THR_WRCH_TVAL_ECCU_ERR_THR_BIT_OFFSET            16

#define IME_RDCH_TKEY_ECC_ERR_THR                                      0x000003FC
#define IME_RDCH_TKEY_ECC_ERR_THR_RDCH_TKEY_ECCC_ERR_THR_MASK          0x0000FFFF
#define IME_RDCH_TKEY_ECC_ERR_THR_RDCH_TKEY_ECCC_ERR_THR_BIT_OFFSET             0
#define IME_RDCH_TKEY_ECC_ERR_THR_RDCH_TKEY_ECCU_ERR_THR_MASK          0xFFFF0000
#define IME_RDCH_TKEY_ECC_ERR_THR_RDCH_TKEY_ECCU_ERR_THR_BIT_OFFSET            16

#define IME_RDCH_CKEY_ECC_ERR_THR                                      0x00000400
#define IME_RDCH_CKEY_ECC_ERR_THR_RDCH_CKEY_ECCC_ERR_THR_MASK          0x0000FFFF
#define IME_RDCH_CKEY_ECC_ERR_THR_RDCH_CKEY_ECCC_ERR_THR_BIT_OFFSET             0
#define IME_RDCH_CKEY_ECC_ERR_THR_RDCH_CKEY_ECCU_ERR_THR_MASK          0xFFFF0000
#define IME_RDCH_CKEY_ECC_ERR_THR_RDCH_CKEY_ECCU_ERR_THR_BIT_OFFSET            16

#define IME_RDCH_TVAL_ECC_ERR_THR                                      0x00000404
#define IME_RDCH_TVAL_ECC_ERR_THR_RDCH_TVAL_ECCC_ERR_THR_MASK          0x0000FFFF
#define IME_RDCH_TVAL_ECC_ERR_THR_RDCH_TVAL_ECCC_ERR_THR_BIT_OFFSET             0
#define IME_RDCH_TVAL_ECC_ERR_THR_RDCH_TVAL_ECCU_ERR_THR_MASK          0xFFFF0000
#define IME_RDCH_TVAL_ECC_ERR_THR_RDCH_TVAL_ECCU_ERR_THR_BIT_OFFSET            16

#define IME_ECC_CLR                                                    0x00000408
#define IME_ECC_CLR_WRCH_TKEY_ECCC_CLR_MASK                            0x00000001
#define IME_ECC_CLR_WRCH_TKEY_ECCC_CLR_BIT_OFFSET                               0
#define IME_ECC_CLR_WRCH_TKEY_ECCU_CLR_MASK                            0x00000002
#define IME_ECC_CLR_WRCH_TKEY_ECCU_CLR_BIT_OFFSET                               1
#define IME_ECC_CLR_WRCH_CKEY_ECCC_CLR_MASK                            0x00000004
#define IME_ECC_CLR_WRCH_CKEY_ECCC_CLR_BIT_OFFSET                               2
#define IME_ECC_CLR_WRCH_CKEY_ECCU_CLR_MASK                            0x00000008
#define IME_ECC_CLR_WRCH_CKEY_ECCU_CLR_BIT_OFFSET                               3
#define IME_ECC_CLR_WRCH_TVAL_ECCC_CLR_MASK                            0x00000010
#define IME_ECC_CLR_WRCH_TVAL_ECCC_CLR_BIT_OFFSET                               4
#define IME_ECC_CLR_WRCH_TVAL_ECCU_CLR_MASK                            0x00000020
#define IME_ECC_CLR_WRCH_TVAL_ECCU_CLR_BIT_OFFSET                               5
#define IME_ECC_CLR_RDCH_TKEY_ECCC_CLR_MASK                            0x00000040
#define IME_ECC_CLR_RDCH_TKEY_ECCC_CLR_BIT_OFFSET                               6
#define IME_ECC_CLR_RDCH_TKEY_ECCU_CLR_MASK                            0x00000080
#define IME_ECC_CLR_RDCH_TKEY_ECCU_CLR_BIT_OFFSET                               7
#define IME_ECC_CLR_RDCH_CKEY_ECCC_CLR_MASK                            0x00000100
#define IME_ECC_CLR_RDCH_CKEY_ECCC_CLR_BIT_OFFSET                               8
#define IME_ECC_CLR_RDCH_CKEY_ECCU_CLR_MASK                            0x00000200
#define IME_ECC_CLR_RDCH_CKEY_ECCU_CLR_BIT_OFFSET                               9
#define IME_ECC_CLR_RDCH_TVAL_ECCC_CLR_MASK                            0x00000400
#define IME_ECC_CLR_RDCH_TVAL_ECCC_CLR_BIT_OFFSET                              10
#define IME_ECC_CLR_RDCH_TVAL_ECCU_CLR_MASK                            0x00000800
#define IME_ECC_CLR_RDCH_TVAL_ECCU_CLR_BIT_OFFSET                              11

#define IME_FIFO_WARN_IRQ_EN                                           0x0000040C
#define IME_FIFO_WARN_IRQ_EN_WRCH_ENC_FIFO_WARN_EN_MASK                0x00000001
#define IME_FIFO_WARN_IRQ_EN_WRCH_ENC_FIFO_WARN_EN_BIT_OFFSET                   0
#define IME_FIFO_WARN_IRQ_EN_WRCH_DATA_FIFO_WARN_EN_MASK               0x00000002
#define IME_FIFO_WARN_IRQ_EN_WRCH_DATA_FIFO_WARN_EN_BIT_OFFSET                  1
#define IME_FIFO_WARN_IRQ_EN_RDCH_DEC_FIFO_WARN_EN_MASK                0x00000004
#define IME_FIFO_WARN_IRQ_EN_RDCH_DEC_FIFO_WARN_EN_BIT_OFFSET                   2
#define IME_FIFO_WARN_IRQ_EN_RDCH_DATA_FIFO_WARN_EN_MASK               0x00000008
#define IME_FIFO_WARN_IRQ_EN_RDCH_DATA_FIFO_WARN_EN_BIT_OFFSET                  3

#define IME_FIFO_WARN_IRQ_STAT                                         0x00000410
#define IME_FIFO_WARN_IRQ_STAT_WRCH_ENC_FIFO_WARN_STAT_MASK            0x00000001
#define IME_FIFO_WARN_IRQ_STAT_WRCH_ENC_FIFO_WARN_STAT_BIT_OFFSET               0
#define IME_FIFO_WARN_IRQ_STAT_WRCH_DATA_FIFO_WARN_STAT_MASK           0x00000002
#define IME_FIFO_WARN_IRQ_STAT_WRCH_DATA_FIFO_WARN_STAT_BIT_OFFSET              1
#define IME_FIFO_WARN_IRQ_STAT_RDCH_DEC_FIFO_WARN_STAT_MASK            0x00000004
#define IME_FIFO_WARN_IRQ_STAT_RDCH_DEC_FIFO_WARN_STAT_BIT_OFFSET               2
#define IME_FIFO_WARN_IRQ_STAT_RDCH_DATA_FIFO_WARN_STAT_MASK           0x00000008
#define IME_FIFO_WARN_IRQ_STAT_RDCH_DATA_FIFO_WARN_STAT_BIT_OFFSET              3

#define IME_CFG_LOCK_OVERRIDE                                          0x00000414
#define IME_CFG_LOCK_OVERRIDE_CFG_LOCK_OVERRIDE_MASK                   0x00000001
#define IME_CFG_LOCK_OVERRIDE_CFG_LOCK_OVERRIDE_BIT_OFFSET                      0

#define IME_GLOBAL_KEY_SIZE                                            0x00000418
#define IME_GLOBAL_KEY_SIZE_GLOBAL_KEY_SIZE_MASK                       0x00000001
#define IME_GLOBAL_KEY_SIZE_GLOBAL_KEY_SIZE_BIT_OFFSET                          0

#define IME_WRCH_UXTS_IRQ_EN                                           0x00000808
#define IME_WRCH_UXTS_IRQ_EN_WRCH_CTX_IDX_ERR_EN_MASK                  0x00000004
#define IME_WRCH_UXTS_IRQ_EN_WRCH_CTX_IDX_ERR_EN_BIT_OFFSET                     2
#define IME_WRCH_UXTS_IRQ_EN_WRCH_REG_PAR_ERR_EN_MASK                  0x00000008
#define IME_WRCH_UXTS_IRQ_EN_WRCH_REG_PAR_ERR_EN_BIT_OFFSET                     3
#define IME_WRCH_UXTS_IRQ_EN_WRCH_FSM_PAR_ERR_EN_MASK                  0x00000010
#define IME_WRCH_UXTS_IRQ_EN_WRCH_FSM_PAR_ERR_EN_BIT_OFFSET                     4
#define IME_WRCH_UXTS_IRQ_EN_WRCH_KEY_ERR_EN_MASK                      0x00000020
#define IME_WRCH_UXTS_IRQ_EN_WRCH_KEY_ERR_EN_BIT_OFFSET                         5
#define IME_WRCH_UXTS_IRQ_EN_WRCH_KEY_IDX_ERR_EN_MASK                  0x00000040
#define IME_WRCH_UXTS_IRQ_EN_WRCH_KEY_IDX_ERR_EN_BIT_OFFSET                     6
#define IME_WRCH_UXTS_IRQ_EN_WRCH_UXTS_IRQ_EN_MASK                     0x80000000
#define IME_WRCH_UXTS_IRQ_EN_WRCH_UXTS_IRQ_EN_BIT_OFFSET                       31

#define IME_WRCH_UXTS_IRQ_STAT                                         0x0000080C
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_CTX_IDX_ERR_MASK                   0x00000004
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_CTX_IDX_ERR_BIT_OFFSET                      2
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_REG_PAR_ERR_MASK                   0x00000008
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_REG_PAR_ERR_BIT_OFFSET                      3
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_FSM_PAR_ERR_MASK                   0x00000010
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_FSM_PAR_ERR_BIT_OFFSET                      4
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_KEY_ERR_MASK                       0x00000020
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_KEY_ERR_BIT_OFFSET                          5
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_KEY_IDX_ERR_MASK                   0x00000040
#define IME_WRCH_UXTS_IRQ_STAT_WRCH_KEY_IDX_ERR_BIT_OFFSET                      6

#define IME_WRCH_UXTS_BUILD_CONFIG_REG0                                0x00000810
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_DP_WIDTH_MASK             0x0000003F
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_DP_WIDTH_BIT_OFFSET                0
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_SK_EN_MASK                0x00000100
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_SK_EN_BIT_OFFSET                   8
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_KEY128_EN_MASK            0x00000200
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_KEY128_EN_BIT_OFFSET               9
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_KEY256_EN_MASK            0x00000400
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_KEY256_EN_BIT_OFFSET              10
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_ENC_EN_MASK               0x00000800
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_ENC_EN_BIT_OFFSET                 11
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_DEC_EN_MASK               0x00001000
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_DEC_EN_BIT_OFFSET                 12
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_AES_ECB_EN_MASK           0x00004000
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_AES_ECB_EN_BIT_OFFSET             14
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_RANDOM_BLK_SEQ_MASK       0x00040000
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_RANDOM_BLK_SEQ_BIT_OFFSET         18
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_AES_EN_MASK               0x00200000
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_AES_EN_BIT_OFFSET                 21
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_SM4_EN_MASK               0x00400000
#define IME_WRCH_UXTS_BUILD_CONFIG_REG0_WRCH_SM4_EN_BIT_OFFSET                 22

#define IME_WRCH_UXTS_BYPASS_CTL                                       0x0000081C
#define IME_WRCH_UXTS_BYPASS_CTL_WRCH_ENA_MASK                         0x00000001
#define IME_WRCH_UXTS_BYPASS_CTL_WRCH_ENA_BIT_OFFSET                            0

#define IME_WRCH_UXTS_MISC_CONFIG_REG                                  0x00000820
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_ENC_BYPASS_MASK             0x00000002
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_ENC_BYPASS_BIT_OFFSET                1
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_PIPE_BYPASS_MASK            0x00000004
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_PIPE_BYPASS_BIT_OFFSET               2
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_IDLE_BYPASS_MASK            0x00000008
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_IDLE_BYPASS_BIT_OFFSET               3
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_SELF_TEST_FAIL_ACT_MASK     0x00000020
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_SELF_TEST_FAIL_ACT_BIT_OFFSET          5
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_INHIBIT_OUTPUT_MASK         0x00000080
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_INHIBIT_OUTPUT_BIT_OFFSET            7
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_CLR_SSP_MASK                0x00000100
#define IME_WRCH_UXTS_MISC_CONFIG_REG_WRCH_CLR_SSP_BIT_OFFSET                   8

#define IME_WRCH_UXTS_HW_INIT_CTRL                                     0x00000824
#define IME_WRCH_UXTS_HW_INIT_CTRL_WRCH_HW_INIT_GO_MASK                0x00000001
#define IME_WRCH_UXTS_HW_INIT_CTRL_WRCH_HW_INIT_GO_BIT_OFFSET                   0

#define IME_WRCH_UXTS_STATUS                                           0x00000828
#define IME_WRCH_UXTS_STATUS_WRCH_HW_INIT_DONE_MASK                    0x00000004
#define IME_WRCH_UXTS_STATUS_WRCH_HW_INIT_DONE_BIT_OFFSET                       2

#define IME_WRCH_SELF_TEST_CTL                                         0x000008A0
#define IME_WRCH_SELF_TEST_CTL_WRCH_PIPE_NUM_MASK                      0x000001F0
#define IME_WRCH_SELF_TEST_CTL_WRCH_PIPE_NUM_BIT_OFFSET                         4
#define IME_WRCH_SELF_TEST_CTL_WRCH_CHK_DISABLE_MASK                   0x00000200
#define IME_WRCH_SELF_TEST_CTL_WRCH_CHK_DISABLE_BIT_OFFSET                      9
#define IME_WRCH_SELF_TEST_CTL_WRCH_ENC_BYPASS_1_MASK                  0x00001000
#define IME_WRCH_SELF_TEST_CTL_WRCH_ENC_BYPASS_1_BIT_OFFSET                    12

#define IME_WRCH_SELF_TEST_ATTRIB                                      0x000008A4
#define IME_WRCH_SELF_TEST_ATTRIB_WRCH_DU_START_MASK                   0x00000010
#define IME_WRCH_SELF_TEST_ATTRIB_WRCH_DU_START_BIT_OFFSET                      4
#define IME_WRCH_SELF_TEST_ATTRIB_WRCH_DU_END_MASK                     0x00000100
#define IME_WRCH_SELF_TEST_ATTRIB_WRCH_DU_END_BIT_OFFSET                        8
#define IME_WRCH_SELF_TEST_ATTRIB_WRCH_ECB_MASK                        0x00010000
#define IME_WRCH_SELF_TEST_ATTRIB_WRCH_ECB_BIT_OFFSET                          16

#define IME_WRCH_SELF_TEST_BSEQ                                        0x000008A8
#define IME_WRCH_SELF_TEST_BSEQ_WRCH_VAL_MASK                          0x000FFFFF
#define IME_WRCH_SELF_TEST_BSEQ_WRCH_VAL_BIT_OFFSET                             0

#define IME_WRCH_SELF_TEST_STAT                                        0x000008AC
#define IME_WRCH_SELF_TEST_STAT_WRCH_ST_DONE_MASK                      0x00000001
#define IME_WRCH_SELF_TEST_STAT_WRCH_ST_DONE_BIT_OFFSET                         0
#define IME_WRCH_SELF_TEST_STAT_WRCH_ST_FAIL_MASK                      0x00000002
#define IME_WRCH_SELF_TEST_STAT_WRCH_ST_FAIL_BIT_OFFSET                         1
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_1_MASK                 0x00000010
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_1_BIT_OFFSET                    4
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_2_MASK                 0x00000020
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_2_BIT_OFFSET                    5
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_3_MASK                 0x00000040
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_3_BIT_OFFSET                    6
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_4_MASK                 0x00000080
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_4_BIT_OFFSET                    7
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_5_MASK                 0x00000100
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_5_BIT_OFFSET                    8
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_6_MASK                 0x00000200
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_6_BIT_OFFSET                    9
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_7_MASK                 0x00000400
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_7_BIT_OFFSET                   10
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_8_MASK                 0x00000800
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_8_BIT_OFFSET                   11
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_9_MASK                 0x00001000
#define IME_WRCH_SELF_TEST_STAT_WRCH_FAIL_CAUSE_9_BIT_OFFSET                   12

#define IME_WRCH_SELF_TEST_VECT_PT_0                                   0x000008B0
#define IME_WRCH_SELF_TEST_VECT_PT_0_WRCH_PT_MASK                      0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_PT_0_WRCH_PT_BIT_OFFSET                         0

#define IME_WRCH_SELF_TEST_VECT_PT_1                                   0x000008B4
#define IME_WRCH_SELF_TEST_VECT_PT_1_WRCH_PT_1_MASK                    0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_PT_1_WRCH_PT_1_BIT_OFFSET                       0

#define IME_WRCH_SELF_TEST_VECT_PT_2                                   0x000008B8
#define IME_WRCH_SELF_TEST_VECT_PT_2_WRCH_PT_2_MASK                    0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_PT_2_WRCH_PT_2_BIT_OFFSET                       0

#define IME_WRCH_SELF_TEST_VECT_PT_3                                   0x000008BC
#define IME_WRCH_SELF_TEST_VECT_PT_3_WRCH_PT_3_MASK                    0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_PT_3_WRCH_PT_3_BIT_OFFSET                       0

#define IME_WRCH_SELF_TEST_VECT_CT_0                                   0x000008C0
#define IME_WRCH_SELF_TEST_VECT_CT_0_WRCH_CT_MASK                      0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_CT_0_WRCH_CT_BIT_OFFSET                         0

#define IME_WRCH_SELF_TEST_VECT_CT_1                                   0x000008C4
#define IME_WRCH_SELF_TEST_VECT_CT_1_WRCH_CT_1_MASK                    0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_CT_1_WRCH_CT_1_BIT_OFFSET                       0

#define IME_WRCH_SELF_TEST_VECT_CT_2                                   0x000008C8
#define IME_WRCH_SELF_TEST_VECT_CT_2_WRCH_CT_2_MASK                    0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_CT_2_WRCH_CT_2_BIT_OFFSET                       0

#define IME_WRCH_SELF_TEST_VECT_CT_3                                   0x000008CC
#define IME_WRCH_SELF_TEST_VECT_CT_3_WRCH_CT_3_MASK                    0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_CT_3_WRCH_CT_3_BIT_OFFSET                       0

#define IME_WRCH_SELF_TEST_VECT_RES_0                                  0x000008D0
#define IME_WRCH_SELF_TEST_VECT_RES_0_WRCH_CR_RES_MASK                 0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_RES_0_WRCH_CR_RES_BIT_OFFSET                    0

#define IME_WRCH_SELF_TEST_VECT_RES_1                                  0x000008D4
#define IME_WRCH_SELF_TEST_VECT_RES_1_WRCH_CR_RES_1_MASK               0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_RES_1_WRCH_CR_RES_1_BIT_OFFSET                  0

#define IME_WRCH_SELF_TEST_VECT_RES_2                                  0x000008D8
#define IME_WRCH_SELF_TEST_VECT_RES_2_WRCH_CR_RES_2_MASK               0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_RES_2_WRCH_CR_RES_2_BIT_OFFSET                  0

#define IME_WRCH_SELF_TEST_VECT_RES_3                                  0x000008DC
#define IME_WRCH_SELF_TEST_VECT_RES_3_WRCH_CR_RES_3_MASK               0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_RES_3_WRCH_CR_RES_3_BIT_OFFSET                  0

#define IME_WRCH_SELF_TEST_VECT_TWK_0                                  0x000008E0
#define IME_WRCH_SELF_TEST_VECT_TWK_0_WRCH_DSEQ_MASK                   0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_TWK_0_WRCH_DSEQ_BIT_OFFSET                      0

#define IME_WRCH_SELF_TEST_VECT_TWK_1                                  0x000008E4
#define IME_WRCH_SELF_TEST_VECT_TWK_1_WRCH_DSEQ_1_MASK                 0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_TWK_1_WRCH_DSEQ_1_BIT_OFFSET                    0

#define IME_WRCH_SELF_TEST_VECT_TWK_2                                  0x000008E8
#define IME_WRCH_SELF_TEST_VECT_TWK_2_WRCH_DSEQ_2_MASK                 0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_TWK_2_WRCH_DSEQ_2_BIT_OFFSET                    0

#define IME_WRCH_SELF_TEST_VECT_TWK_3                                  0x000008EC
#define IME_WRCH_SELF_TEST_VECT_TWK_3_WRCH_DSEQ_3_MASK                 0xFFFFFFFF
#define IME_WRCH_SELF_TEST_VECT_TWK_3_WRCH_DSEQ_3_BIT_OFFSET                    0

#define IME_WRCH_SELF_TEST_VECT_CTL                                    0x000008F0
#define IME_WRCH_SELF_TEST_VECT_CTL_WRCH_GO_MASK                       0x00000001
#define IME_WRCH_SELF_TEST_VECT_CTL_WRCH_GO_BIT_OFFSET                          0

#define IME_WRCH_BIST_VECT_MODE                                        0x000008F4
#define IME_WRCH_BIST_VECT_MODE_WRCH_FUNCT_MASK                        0x00000007
#define IME_WRCH_BIST_VECT_MODE_WRCH_FUNCT_BIT_OFFSET                           0
#define IME_WRCH_BIST_VECT_MODE_WRCH_KEY_SIZE_MASK                     0x00000010
#define IME_WRCH_BIST_VECT_MODE_WRCH_KEY_SIZE_BIT_OFFSET                        4

#define IME_WRCH_UXTS_BIST_VECT_ERR_INJ                                0x000008F8
#define IME_WRCH_UXTS_BIST_VECT_ERR_INJ_WRCH_BYP_ERR_INJ_MASK          0x00000001
#define IME_WRCH_UXTS_BIST_VECT_ERR_INJ_WRCH_BYP_ERR_INJ_BIT_OFFSET             0
#define IME_WRCH_UXTS_BIST_VECT_ERR_INJ_WRCH_ECB_ERR_INJ_MASK          0x00000002
#define IME_WRCH_UXTS_BIST_VECT_ERR_INJ_WRCH_ECB_ERR_INJ_BIT_OFFSET             1
#define IME_WRCH_UXTS_BIST_VECT_ERR_INJ_WRCH_XTS_ERR_INJ_MASK          0x00000004
#define IME_WRCH_UXTS_BIST_VECT_ERR_INJ_WRCH_XTS_ERR_INJ_BIT_OFFSET             2
#define IME_WRCH_UXTS_BIST_VECT_ERR_INJ_WRCH_CTS_ERR_INJ_MASK          0x00000008
#define IME_WRCH_UXTS_BIST_VECT_ERR_INJ_WRCH_CTS_ERR_INJ_BIT_OFFSET             3

#define IME_WRCH_UXTS_BIST_VECT_CTL                                    0x000008FC
#define IME_WRCH_UXTS_BIST_VECT_CTL_WRCH_BIST_GO_MASK                  0x00000001
#define IME_WRCH_UXTS_BIST_VECT_CTL_WRCH_BIST_GO_BIT_OFFSET                     0

#define IME_RDCH_UXTS_IRQ_EN                                           0x00000C08
#define IME_RDCH_UXTS_IRQ_EN_RDCH_CTX_IDX_ERR_EN_MASK                  0x00000004
#define IME_RDCH_UXTS_IRQ_EN_RDCH_CTX_IDX_ERR_EN_BIT_OFFSET                     2
#define IME_RDCH_UXTS_IRQ_EN_RDCH_REG_PAR_ERR_EN_MASK                  0x00000008
#define IME_RDCH_UXTS_IRQ_EN_RDCH_REG_PAR_ERR_EN_BIT_OFFSET                     3
#define IME_RDCH_UXTS_IRQ_EN_RDCH_FSM_PAR_ERR_EN_MASK                  0x00000010
#define IME_RDCH_UXTS_IRQ_EN_RDCH_FSM_PAR_ERR_EN_BIT_OFFSET                     4
#define IME_RDCH_UXTS_IRQ_EN_RDCH_KEY_ERR_EN_MASK                      0x00000020
#define IME_RDCH_UXTS_IRQ_EN_RDCH_KEY_ERR_EN_BIT_OFFSET                         5
#define IME_RDCH_UXTS_IRQ_EN_RDCH_KEY_IDX_ERR_EN_MASK                  0x00000040
#define IME_RDCH_UXTS_IRQ_EN_RDCH_KEY_IDX_ERR_EN_BIT_OFFSET                     6
#define IME_RDCH_UXTS_IRQ_EN_RDCH_UXTS_IRQ_EN_MASK                     0x80000000
#define IME_RDCH_UXTS_IRQ_EN_RDCH_UXTS_IRQ_EN_BIT_OFFSET                       31

#define IME_RDCH_UXTS_IRQ_STAT                                         0x00000C0C
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_CTX_IDX_ERR_MASK                   0x00000004
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_CTX_IDX_ERR_BIT_OFFSET                      2
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_REG_PAR_ERR_MASK                   0x00000008
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_REG_PAR_ERR_BIT_OFFSET                      3
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_FSM_PAR_ERR_MASK                   0x00000010
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_FSM_PAR_ERR_BIT_OFFSET                      4
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_KEY_ERR_MASK                       0x00000020
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_KEY_ERR_BIT_OFFSET                          5
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_KEY_IDX_ERR_MASK                   0x00000040
#define IME_RDCH_UXTS_IRQ_STAT_RDCH_KEY_IDX_ERR_BIT_OFFSET                      6

#define IME_RDCH_UXTS_BUILD_CONFIG_REG0                                0x00000C10
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_DP_WIDTH_MASK             0x0000003F
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_DP_WIDTH_BIT_OFFSET                0
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_SK_EN_MASK                0x00000100
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_SK_EN_BIT_OFFSET                   8
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_KEY128_EN_MASK            0x00000200
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_KEY128_EN_BIT_OFFSET               9
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_KEY256_EN_MASK            0x00000400
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_KEY256_EN_BIT_OFFSET              10
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_ENC_EN_MASK               0x00000800
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_ENC_EN_BIT_OFFSET                 11
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_DEC_EN_MASK               0x00001000
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_DEC_EN_BIT_OFFSET                 12
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_AES_ECB_EN_MASK           0x00004000
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_AES_ECB_EN_BIT_OFFSET             14
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_RANDOM_BLK_SEQ_MASK       0x00040000
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_RANDOM_BLK_SEQ_BIT_OFFSET         18
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_AES_EN_MASK               0x00200000
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_AES_EN_BIT_OFFSET                 21
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_SM4_EN_MASK               0x00400000
#define IME_RDCH_UXTS_BUILD_CONFIG_REG0_RDCH_SM4_EN_BIT_OFFSET                 22

#define IME_RDCH_UXTS_BYPASS_CTL                                       0x00000C1C
#define IME_RDCH_UXTS_BYPASS_CTL_RDCH_ENA_MASK                         0x00000001
#define IME_RDCH_UXTS_BYPASS_CTL_RDCH_ENA_BIT_OFFSET                            0

#define IME_RDCH_UXTS_MISC_CONFIG_REG                                  0x00000C20
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_ENC_BYPASS_MASK             0x00000002
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_ENC_BYPASS_BIT_OFFSET                1
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_PIPE_BYPASS_MASK            0x00000004
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_PIPE_BYPASS_BIT_OFFSET               2
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_IDLE_BYPASS_MASK            0x00000008
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_IDLE_BYPASS_BIT_OFFSET               3
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_SELF_TEST_FAIL_ACT_MASK     0x00000020
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_SELF_TEST_FAIL_ACT_BIT_OFFSET          5
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_INHIBIT_OUTPUT_MASK         0x00000080
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_INHIBIT_OUTPUT_BIT_OFFSET            7
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_CLR_SSP_MASK                0x00000100
#define IME_RDCH_UXTS_MISC_CONFIG_REG_RDCH_CLR_SSP_BIT_OFFSET                   8

#define IME_RDCH_UXTS_HW_INIT_CTRL                                     0x00000C24
#define IME_RDCH_UXTS_HW_INIT_CTRL_RDCH_HW_INIT_GO_MASK                0x00000001
#define IME_RDCH_UXTS_HW_INIT_CTRL_RDCH_HW_INIT_GO_BIT_OFFSET                   0

#define IME_RDCH_UXTS_STATUS                                           0x00000C28
#define IME_RDCH_UXTS_STATUS_RDCH_HW_INIT_DONE_MASK                    0x00000004
#define IME_RDCH_UXTS_STATUS_RDCH_HW_INIT_DONE_BIT_OFFSET                       2

#define IME_RDCH_SELF_TEST_CTL                                         0x00000CA0
#define IME_RDCH_SELF_TEST_CTL_RDCH_PIPE_NUM_MASK                      0x000001F0
#define IME_RDCH_SELF_TEST_CTL_RDCH_PIPE_NUM_BIT_OFFSET                         4
#define IME_RDCH_SELF_TEST_CTL_RDCH_CHK_DISABLE_MASK                   0x00000200
#define IME_RDCH_SELF_TEST_CTL_RDCH_CHK_DISABLE_BIT_OFFSET                      9
#define IME_RDCH_SELF_TEST_CTL_RDCH_ENC_BYPASS_1_MASK                  0x00001000
#define IME_RDCH_SELF_TEST_CTL_RDCH_ENC_BYPASS_1_BIT_OFFSET                    12

#define IME_RDCH_SELF_TEST_ATTRIB                                      0x00000CA4
#define IME_RDCH_SELF_TEST_ATTRIB_RDCH_DU_START_MASK                   0x00000010
#define IME_RDCH_SELF_TEST_ATTRIB_RDCH_DU_START_BIT_OFFSET                      4
#define IME_RDCH_SELF_TEST_ATTRIB_RDCH_DU_END_MASK                     0x00000100
#define IME_RDCH_SELF_TEST_ATTRIB_RDCH_DU_END_BIT_OFFSET                        8
#define IME_RDCH_SELF_TEST_ATTRIB_RDCH_ECB_MASK                        0x00010000
#define IME_RDCH_SELF_TEST_ATTRIB_RDCH_ECB_BIT_OFFSET                          16

#define IME_RDCH_SELF_TEST_BSEQ                                        0x00000CA8
#define IME_RDCH_SELF_TEST_BSEQ_RDCH_VAL_MASK                          0x000FFFFF
#define IME_RDCH_SELF_TEST_BSEQ_RDCH_VAL_BIT_OFFSET                             0

#define IME_RDCH_SELF_TEST_STAT                                        0x00000CAC
#define IME_RDCH_SELF_TEST_STAT_RDCH_ST_DONE_MASK                      0x00000001
#define IME_RDCH_SELF_TEST_STAT_RDCH_ST_DONE_BIT_OFFSET                         0
#define IME_RDCH_SELF_TEST_STAT_RDCH_ST_FAIL_MASK                      0x00000002
#define IME_RDCH_SELF_TEST_STAT_RDCH_ST_FAIL_BIT_OFFSET                         1
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_1_MASK                 0x00000010
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_1_BIT_OFFSET                    4
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_2_MASK                 0x00000020
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_2_BIT_OFFSET                    5
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_3_MASK                 0x00000040
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_3_BIT_OFFSET                    6
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_4_MASK                 0x00000080
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_4_BIT_OFFSET                    7
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_5_MASK                 0x00000100
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_5_BIT_OFFSET                    8
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_6_MASK                 0x00000200
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_6_BIT_OFFSET                    9
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_7_MASK                 0x00000400
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_7_BIT_OFFSET                   10
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_8_MASK                 0x00000800
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_8_BIT_OFFSET                   11
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_9_MASK                 0x00001000
#define IME_RDCH_SELF_TEST_STAT_RDCH_FAIL_CAUSE_9_BIT_OFFSET                   12

#define IME_RDCH_SELF_TEST_VECT_PT_0                                   0x00000CB0
#define IME_RDCH_SELF_TEST_VECT_PT_0_RDCH_PT_MASK                      0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_PT_0_RDCH_PT_BIT_OFFSET                         0

#define IME_RDCH_SELF_TEST_VECT_PT_1                                   0x00000CB4
#define IME_RDCH_SELF_TEST_VECT_PT_1_RDCH_PT_1_MASK                    0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_PT_1_RDCH_PT_1_BIT_OFFSET                       0

#define IME_RDCH_SELF_TEST_VECT_PT_2                                   0x00000CB8
#define IME_RDCH_SELF_TEST_VECT_PT_2_RDCH_PT_2_MASK                    0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_PT_2_RDCH_PT_2_BIT_OFFSET                       0

#define IME_RDCH_SELF_TEST_VECT_PT_3                                   0x00000CBC
#define IME_RDCH_SELF_TEST_VECT_PT_3_RDCH_PT_3_MASK                    0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_PT_3_RDCH_PT_3_BIT_OFFSET                       0

#define IME_RDCH_SELF_TEST_VECT_CT_0                                   0x00000CC0
#define IME_RDCH_SELF_TEST_VECT_CT_0_RDCH_CT_MASK                      0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_CT_0_RDCH_CT_BIT_OFFSET                         0

#define IME_RDCH_SELF_TEST_VECT_CT_1                                   0x00000CC4
#define IME_RDCH_SELF_TEST_VECT_CT_1_RDCH_CT_1_MASK                    0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_CT_1_RDCH_CT_1_BIT_OFFSET                       0

#define IME_RDCH_SELF_TEST_VECT_CT_2                                   0x00000CC8
#define IME_RDCH_SELF_TEST_VECT_CT_2_RDCH_CT_2_MASK                    0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_CT_2_RDCH_CT_2_BIT_OFFSET                       0

#define IME_RDCH_SELF_TEST_VECT_CT_3                                   0x00000CCC
#define IME_RDCH_SELF_TEST_VECT_CT_3_RDCH_CT_3_MASK                    0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_CT_3_RDCH_CT_3_BIT_OFFSET                       0

#define IME_RDCH_SELF_TEST_VECT_RES_0                                  0x00000CD0
#define IME_RDCH_SELF_TEST_VECT_RES_0_RDCH_CR_RES_MASK                 0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_RES_0_RDCH_CR_RES_BIT_OFFSET                    0

#define IME_RDCH_SELF_TEST_VECT_RES_1                                  0x00000CD4
#define IME_RDCH_SELF_TEST_VECT_RES_1_RDCH_CR_RES_1_MASK               0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_RES_1_RDCH_CR_RES_1_BIT_OFFSET                  0

#define IME_RDCH_SELF_TEST_VECT_RES_2                                  0x00000CD8
#define IME_RDCH_SELF_TEST_VECT_RES_2_RDCH_CR_RES_2_MASK               0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_RES_2_RDCH_CR_RES_2_BIT_OFFSET                  0

#define IME_RDCH_SELF_TEST_VECT_RES_3                                  0x00000CDC
#define IME_RDCH_SELF_TEST_VECT_RES_3_RDCH_CR_RES_3_MASK               0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_RES_3_RDCH_CR_RES_3_BIT_OFFSET                  0

#define IME_RDCH_SELF_TEST_VECT_TWK_0                                  0x00000CE0
#define IME_RDCH_SELF_TEST_VECT_TWK_0_RDCH_DSEQ_MASK                   0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_TWK_0_RDCH_DSEQ_BIT_OFFSET                      0

#define IME_RDCH_SELF_TEST_VECT_TWK_1                                  0x00000CE4
#define IME_RDCH_SELF_TEST_VECT_TWK_1_RDCH_DSEQ_1_MASK                 0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_TWK_1_RDCH_DSEQ_1_BIT_OFFSET                    0

#define IME_RDCH_SELF_TEST_VECT_TWK_2                                  0x00000CE8
#define IME_RDCH_SELF_TEST_VECT_TWK_2_RDCH_DSEQ_2_MASK                 0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_TWK_2_RDCH_DSEQ_2_BIT_OFFSET                    0

#define IME_RDCH_SELF_TEST_VECT_TWK_3                                  0x00000CEC
#define IME_RDCH_SELF_TEST_VECT_TWK_3_RDCH_DSEQ_3_MASK                 0xFFFFFFFF
#define IME_RDCH_SELF_TEST_VECT_TWK_3_RDCH_DSEQ_3_BIT_OFFSET                    0

#define IME_RDCH_SELF_TEST_VECT_CTL                                    0x00000CF0
#define IME_RDCH_SELF_TEST_VECT_CTL_RDCH_GO_MASK                       0x00000001
#define IME_RDCH_SELF_TEST_VECT_CTL_RDCH_GO_BIT_OFFSET                          0

#define IME_RDCH_BIST_VECT_MODE                                        0x00000CF4
#define IME_RDCH_BIST_VECT_MODE_RDCH_FUNCT_MASK                        0x00000007
#define IME_RDCH_BIST_VECT_MODE_RDCH_FUNCT_BIT_OFFSET                           0
#define IME_RDCH_BIST_VECT_MODE_RDCH_KEY_SIZE_MASK                     0x00000010
#define IME_RDCH_BIST_VECT_MODE_RDCH_KEY_SIZE_BIT_OFFSET                        4

#define IME_RDCH_UXTS_BIST_VECT_ERR_INJ                                0x00000CF8
#define IME_RDCH_UXTS_BIST_VECT_ERR_INJ_RDCH_BYP_ERR_INJ_MASK          0x00000001
#define IME_RDCH_UXTS_BIST_VECT_ERR_INJ_RDCH_BYP_ERR_INJ_BIT_OFFSET             0
#define IME_RDCH_UXTS_BIST_VECT_ERR_INJ_RDCH_ECB_ERR_INJ_MASK          0x00000002
#define IME_RDCH_UXTS_BIST_VECT_ERR_INJ_RDCH_ECB_ERR_INJ_BIT_OFFSET             1
#define IME_RDCH_UXTS_BIST_VECT_ERR_INJ_RDCH_XTS_ERR_INJ_MASK          0x00000004
#define IME_RDCH_UXTS_BIST_VECT_ERR_INJ_RDCH_XTS_ERR_INJ_BIT_OFFSET             2
#define IME_RDCH_UXTS_BIST_VECT_ERR_INJ_RDCH_CTS_ERR_INJ_MASK          0x00000008
#define IME_RDCH_UXTS_BIST_VECT_ERR_INJ_RDCH_CTS_ERR_INJ_BIT_OFFSET             3

#define IME_RDCH_UXTS_BIST_VECT_CTL                                    0x00000CFC
#define IME_RDCH_UXTS_BIST_VECT_CTL_RDCH_BIST_GO_MASK                  0x00000001
#define IME_RDCH_UXTS_BIST_VECT_CTL_RDCH_BIST_GO_BIT_OFFSET                     0

#define REG_GROUP_IME_CH1                                              0x000F1000

#endif /* __MODULES_CORE_INCLUDE_DWC_DDRCTL_REG_MAP_H__ */

