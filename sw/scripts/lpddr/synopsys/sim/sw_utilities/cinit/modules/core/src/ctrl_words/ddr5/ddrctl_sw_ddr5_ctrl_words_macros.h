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


///////////////     RW00    ///////////////
//
// Register Write 00 - Global Features Control Word
//
// Command Address Rate
#define DDR5_RW00_CMD_ADDR_RATE                            DDR5_RW00_CMD_ADDR_RATE
#define DDR5_RW00_CMD_ADDR_RATE_MASK                                    0x00000001
#define DDR5_RW00_CMD_ADDR_RATE_BIT_OFFSET                                       0
// SDR Modes
#define DDR5_RW00_SDR_MODE                                      DDR5_RW00_SDR_MODE
#define DDR5_RW00_SDR_MODE_MASK                                         0x00000002
#define DDR5_RW00_SDR_MODE_BIT_OFFSET                                            1


///////////////     RW01    ///////////////
//
// Register Write 01 - Parity, CMD Blocking, and Alert Global Control Word
//
// Parity Checking
#define DDR5_RW01_PARITY_CHECKING                        DDR5_RW01_PARITY_CHECKING
#define DDR5_RW01_PARITY_CHECKING_MASK                                  0x00000001
#define DDR5_RW01_PARITY_CHECKING_BIT_OFFSET                                     0
// DRAM Interface Forward All CMDS
#define DDR5_RW01_DRAM_IF_CMDS                              DDR5_RW01_DRAM_IF_CMDS
#define DDR5_RW01_DRAM_IF_CMDS_MASK                                     0x00000002
#define DDR5_RW01_DRAM_IF_CMDS_BIT_OFFSET                                        1
// Data Buffer Interface Forward All CMDs
#define DDR5_RW01_DATABUFFER_CMDS                        DDR5_RW01_DATABUFFER_CMDS
#define DDR5_RW01_DATABUFFER_CMDS_MASK                                  0x00000008
#define DDR5_RW01_DATABUFFER_CMDS_BIT_OFFSET                                     3
// ALERT_n Assertion
#define DDR5_RW01_ALERT_N_ASSERTION                    DDR5_RW01_ALERT_N_ASSERTION
#define DDR5_RW01_ALERT_N_ASSERTION_MASK                                0x00000040
#define DDR5_RW01_ALERT_N_ASSERTION_BIT_OFFSET                                   6
// ALERT_n Re-enable
#define DDR5_RW01_ALERT_N_RE_ENABLE                    DDR5_RW01_ALERT_N_RE_ENABLE
#define DDR5_RW01_ALERT_N_RE_ENABLE_MASK                                0x00000080
#define DDR5_RW01_ALERT_N_RE_ENABLE_BIT_OFFSET                                   7


///////////////     RW05    ///////////////
//
// Register Write 05 - DIMM Operating Speed Global Control Word
//
// Parity Checking
#define DDR5_RW05_OPERATING_SPEED                        DDR5_RW05_OPERATING_SPEED
#define DDR5_RW05_OPERATING_SPEED_MASK                                  0x0000000F
#define DDR5_RW05_OPERATING_SPEED_BIT_OFFSET                                     0


///////////////     RW06    ///////////////
//
// Register Write 06 - DIMM Operating Speed Global Control Word
//
// Parity Checking
#define DDR5_RW06_FINE_GRAIN_SPEED_GRADE          DDR5_RW06_FINE_GRAIN_SPEED_GRADE
#define DDR5_RW06_FINE_GRAIN_SPEED_GRADE_MASK                           0x0000000F
#define DDR5_RW06_FINE_GRAIN_SPEED_GRADE_BIT_OFFSET                              0

///////////////     RW11    ///////////////
//
// Register Write 11 - Command Latency Adder Configuration Control Word
//
// Latency adder nLadd to all DRAM commands
#define DDR5_RW11_LATENCY_ADDER_NLADD                DDR5_RW11_LATENCY_ADDER_NLADD
#define DDR5_RW11_LATENCY_ADDER_NLADD_MASK                              0x0000000F
#define DDR5_RW11_LATENCY_ADDER_NLADD_BIT_OFFSET                                 0


#endif  // __MODULES_CORE_INCLUDE_MODE_REGS_DDR5_DDRCTL_SW_DDR5_MODE_REGS_MACROS_H__
