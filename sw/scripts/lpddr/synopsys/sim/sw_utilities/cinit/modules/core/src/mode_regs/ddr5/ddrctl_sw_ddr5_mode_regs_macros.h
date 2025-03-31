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


#ifndef __MODULES_CORE_INCLUDE_MODE_REGS_DDR5_DDRCTL_SW_DDR5_MODE_REGS_MACROS_H__
#define __MODULES_CORE_INCLUDE_MODE_REGS_DDR5_DDRCTL_SW_DDR5_MODE_REGS_MACROS_H__

///////////////     MR0     ///////////////
//
// Mode Register 0 - Burst Length and CAS Latency
//
// Burst Length
#define DDR5_MR0_BURST_LENGTH                                DDR5_MR0_BURST_LENGTH
#define DDR5_MR0_BURST_LENGTH_MASK                                      0x00000003
#define DDR5_MR0_BURST_LENGTH_BIT_OFFSET                                         0
// CAS Latency (RL)
#define DDR5_MR0_CAS_LATENCY                                  DDR5_MR0_CAS_LATENCY
#define DDR5_MR0_CAS_LATENCY_MASK                                       0x0000007C
#define DDR5_MR0_CAS_LATENCY_BIT_OFFSET                                          2


///////////////     MR2     ///////////////
//
// Mode Register 2
//
// Read Preamble Training
#define DDR5_MR2_READ_PREAMBLE_EN                        DDR5_MR2_READ_PREAMBLE_EN
#define DDR5_MR2_READ_PREAMBLE_EN_MASK                                  0x00000001
#define DDR5_MR2_READ_PREAMBLE_EN_BIT_OFFSET                                     0
// Write Leveling
#define DDR5_MR2_WRITE_LEVELING                            DDR5_MR2_WRITE_LEVELING
#define DDR5_MR2_WRITE_LEVELING_MASK                                    0x00000002
#define DDR5_MR2_WRITE_LEVELING_BIT_OFFSET                                       1
// 2N Mode
#define DDR5_MR2_2N_MODE                                          DDR5_MR2_2N_MODE
#define DDR5_MR2_2N_MODE_MASK                                           0x00000004
#define DDR5_MR2_2N_MODE_BIT_OFFSET                                              2
// Max Power Saving Mode
#define DDR5_MR2_MAX_POWER_SAVING_MODE              DDR5_MR2_MAX_POWER_SAVING_MODE
#define DDR5_MR2_MAX_POWER_SAVING_MODE_MASK                             0x00000008
#define DDR5_MR2_MAX_POWER_SAVING_MODE_BIT_OFFSET                                3
// CS Assertion Duration (MPC)
#define DDR5_MR2_CS_ASSERT_DURATION                    DDR5_MR2_CS_ASSERT_DURATION
#define DDR5_MR2_CS_ASSERT_DURATION_MASK                                0x00000010
#define DDR5_MR2_CS_ASSERT_DURATION_BIT_OFFSET                                   4
// Device 15 Maximum Power Savings Mode
#define DDR5_MR2_DEV_15_MPSM                                  DDR5_MR2_DEV_15_MPSM
#define DDR5_MR2_DEV_15_MPSM_MASK                                       0x00000020
#define DDR5_MR2_DEV_15_MPSM_BIT_OFFSET                                          5
// Internal Write Timing
#define DDR5_MR2_INTERNAL_WRITE_TIMMING            DDR5_MR2_INTERNAL_WRITE_TIMMING
#define DDR5_MR2_INTERNAL_WRITE_TIMMING_MASK                            0x00000080
#define DDR5_MR2_INTERNAL_WRITE_TIMMING_BIT_OFFSET                               7


///////////////     MR4     ///////////////
//
// Mode Register 4 - Refresh Settings
//
// Minimum Refresh Rate
#define DDR5_MR4_REFRESH_RATE                                DDR5_MR4_REFRESH_RATE
#define DDR5_MR4_REFRESH_RATE_MASK                                            0x07u
#define DDR5_MR4_REFRESH_RATE_BIT_OFFSET                                         0u
// Refresh Interval Rate Indicator
#define DDR5_MR4_REFRESH_INTVL_RATE_IND            DDR5_MR4_REFRESH_INTVL_RATE_IND
#define DDR5_MR4_REFRESH_INTVL_RATE_IND_MASK                                  0x08u
#define DDR5_MR4_REFRESH_INTVL_RATE_IND_BIT_OFFSET                               3u
// Refresh tRFC Mode
#define DDR5_MR4_REFRESH_TRFC_MODE                      DDR5_MR4_REFRESH_TRFC_MODE
#define DDR5_MR4_REFRESH_TRFC_MODE_MASK                                       0x10u
#define DDR5_MR4_REFRESH_TRFC_MODE_BIT_OFFSET                                    4u
// Temperature Update Flag (TUF)
#define DDR5_MR4_TUF                                                  DDR5_MR4_TUF
#define DDR5_MR4_TUF_MASK                                                     0x80u
#define DDR5_MR4_TUF_BIT_OFFSET                                                  7u

///////////////     MR14     ///////////////
//
// Mode Register 14 - Transparency ECC Configuration
//
// ECS Error Register Index/MBIST Rank Select
#define DDR5_MR14_CID                                                DDR5_MR14_CID
#define DDR5_MR14_CID_MASK                                                    0x08u
#define DDR5_MR14_CID_BIT_OFFSET                                                 0u
// Code Word/Row Count
#define DDR5_MR14_CODE_WORD_ROW_COUNT                DDR5_MR14_CODE_WORD_ROW_COUNT
#define DDR5_MR14_CODE_WORD_ROW_COUNT_MASK                                    0x20u
#define DDR5_MR14_CODE_WORD_ROW_COUNT_BIT_OFFSET                                 5u
// ECS Reset Counter
#define DDR5_MR14_ECS_RESET_COUNTER                    DDR5_MR14_ECS_RESET_COUNTER
#define DDR5_MR14_ECS_RESET_COUNTER_MASK                                      0x40u
#define DDR5_MR14_ECS_RESET_COUNTER_BIT_OFFSET                                   6u
// ECS Mode
#define DDR5_MR14_ECS_MODE                                      DDR5_MR14_ECS_MODE
#define DDR5_MR14_ECS_MODE_MASK                                               0x80u
#define DDR5_MR14_ECS_MODE_BIT_OFFSET                                            7u


#endif  // __MODULES_CORE_INCLUDE_MODE_REGS_DDR5_DDRCTL_SW_DDR5_MODE_REGS_MACROS_H__
