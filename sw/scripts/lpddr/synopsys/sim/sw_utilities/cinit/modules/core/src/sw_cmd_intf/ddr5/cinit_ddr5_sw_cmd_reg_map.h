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


#ifndef __MODULES_CORE_INCLUDE_CINIT_DDR5_SW_CMD_H__
#define __MODULES_CORE_INCLUDE_CINIT_DDR5_SW_CMD_H__


///////////////     CMDSTAT register     ///////////////
// DFIUPD
// [14]: Command done to DFI CTRL UPD request (For another channel in sync mode)
#define CMDSTAT_CMD_RSLT_DFIUPD_CH_S_DONE                         CMDSTAT_CMD_RSLT_DFIUPD_CH_S_DONE
#define CMDSTAT_CMD_RSLT_DFIUPD_CH_S_DONE_MASK          (0x00004000 << CMDSTAT_CMD_RSLT_BIT_OFFSET)
#define CMDSTAT_CMD_RSLT_DFIUPD_CH_S_DONE_BIT_OFFSET            (14  + CMDSTAT_CMD_RSLT_BIT_OFFSET)
// [15]: Command done to DFI CTRL UPD request
#define CMDSTAT_CMD_RSLT_DFIUPD_DONE                                   CMDSTAT_CMD_RSLT_DFIUPD_DONE
#define CMDSTAT_CMD_RSLT_DFIUPD_DONE_MASK               (0x00008000 << CMDSTAT_CMD_RSLT_BIT_OFFSET)
#define CMDSTAT_CMD_RSLT_DFIUPD_DONE_BIT_OFFSET                 (15  + CMDSTAT_CMD_RSLT_BIT_OFFSET)
// DFIFC
// For DFIFC command 2 bits in the CMDSTAT_CMD_RSLT field needs to be checked
// [16]: Command done to DFI FC entry/exit request (For another channel in sync mode)
#define CMDSTAT_CMD_RSLT_DFIFC_CH_S_DONE                            CMDSTAT_CMD_RSLT_DFIFC_CH_S_DONE
#define CMDSTAT_CMD_RSLT_DFIFC_CH_S_DONE_MASK            (0x00010000 << CMDSTAT_CMD_RSLT_BIT_OFFSET)
#define CMDSTAT_CMD_RSLT_DFIFC_CH_S_DONE_BIT_OFFSET              (16  + CMDSTAT_CMD_RSLT_BIT_OFFSET)
// [17]: Command done to DFI FC entry/exit request
#define CMDSTAT_CMD_RSLT_DFIFC_DONE                                 CMDSTAT_CMD_RSLT_DFIFC_CH_0_DONE
#define CMDSTAT_CMD_RSLT_DFIFC_DONE_MASK                 (0x00020000 << CMDSTAT_CMD_RSLT_BIT_OFFSET)
#define CMDSTAT_CMD_RSLT_DFIFC_DONE_BIT_OFFSET                   (17  + CMDSTAT_CMD_RSLT_BIT_OFFSET)



///////////////     MRW     ///////////////
//
// Mode Register Write command (0x00 -  0)
//
// Mode Register Address
#define SW_CMD_MRW_MR_ADDR                                              SW_CMD_MRW_MR_ADDR
#define SW_CMD_MRW_MR_ADDR_MASK                                         0x000000FF
#define SW_CMD_MRW_MR_ADDR_BIT_OFFSET                                            0
// Op Code
#define SW_CMD_MRW_OP                                                   SW_CMD_MRW_OP
#define SW_CMD_MRW_OP_MASK                                              0x0000FF00
#define SW_CMD_MRW_OP_BIT_OFFSET                                                 8
// Control Word
#define SW_CMD_MRW_CW                                                   SW_CMD_MRW_CW
#define SW_CMD_MRW_CW_MASK                                              0x00010000
#define SW_CMD_MRW_CW_BIT_OFFSET                                                16
// Dual-Die Packaging (DDP)
#define SW_CMD_MRW_DDPID                                                SW_CMD_MRW_DDPID
#define SW_CMD_MRW_DDPID_MASK                                           0x00020000
#define SW_CMD_MRW_DDPID_BIT_OFFSET                                             17
// Pause Refresh Enable, refresh to the target rank will be paused before
// the MRR command is executed. Refresh will be resumed after the MRR is done
#define SW_CMD_MRW_PAUSE_REF_EN                                         SW_CMD_MRW_PAUSE_REF_EN
#define SW_CMD_MRW_PAUSE_REF_EN_MASK                                    0x00080000
#define SW_CMD_MRW_PAUSE_REF_EN_BIT_OFFSET                                      19
// CSn[3:0] is low active and is used to select target ranks
#define SW_CMD_MRW_CS_N                                                 SW_CMD_MRW_CS_N
#define SW_CMD_MRW_CS_N_MASK                                            0x00F00000
#define SW_CMD_MRW_CS_N_BIT_OFFSET                                              20


///////////////     MRR     ///////////////
//
// Mode Register Write command (0x01 -  1)
//
// Mode Register Address
#define SW_CMD_MRR_MR_ADDR                                              SW_CMD_MRR_MR_ADDR
#define SW_CMD_MRR_MR_ADDR_MASK                                         0x000000FF
#define SW_CMD_MRR_MR_ADDR_BIT_OFFSET                                            0
// TCR
#define SW_CMD_MRR_TCR                                                  SW_CMD_MRR_TCR
#define SW_CMD_MRR_TCR_MASK                                             0x00000100
#define SW_CMD_MRR_TCR_BIT_OFFSET                                                8
// Control Word
#define SW_CMD_MRR_CW                                                   SW_CMD_MRR_CW
#define SW_CMD_MRR_CW_MASK                                              0x00010000
#define SW_CMD_MRR_CW_BIT_OFFSET                                                16
// Dual-Die Packaging (DDP)
#define SW_CMD_MRR_DDPID                                                SW_CMD_MRR_DDPID
#define SW_CMD_MRR_DDPID_MASK                                           0x00020000
#define SW_CMD_MRR_DDPID_BIT_OFFSET                                             17
// PHY snoop enable
// PHY_SNOOP_EN is to enable DDR PHY to snoop the MRR result. For example,
//           MRR46/47 to read back DQS Osc result from DDR, if this bit is 1,
//           Controller will signal PHY to snoop the MRR results.
#define SW_CMD_MRR_PHY_SNOOP_EN                                         SW_CMD_MRR_PHY_SNOOP_EN
#define SW_CMD_MRR_PHY_SNOOP_EN_MASK                                    0x00040000
#define SW_CMD_MRR_PHY_SNOOP_EN_BIT_OFFSET                                      18
// Pause Refresh Enable, refresh to the target rank will be paused before
// the MRR command is executed. Refresh will be resumed after the MRR is done
#define SW_CMD_MRR_PAUSE_REF_EN                                         SW_CMD_MRR_PAUSE_REF_EN
#define SW_CMD_MRR_PAUSE_REF_EN_MASK                                    0x00080000
#define SW_CMD_MRR_PAUSE_REF_EN_BIT_OFFSET                                      19
// CSn[3:0] is low active and is used to select target ranks
#define SW_CMD_MRR_RANK_NUM                                             SW_CMD_MRR_RANK_NUM
#define SW_CMD_MRR_RANK_NUM_MASK                                        0x00300000
#define SW_CMD_MRR_RANK_NUM_BIT_OFFSET                                          20


///////////////   SR_CTRL   ///////////////
//
// DDR Self Refresh Control command (0x02 -  2)
// Control Self-Refresh entry and exit per rank.
//
// [3:0]: SRE, when bit[i] is ‘1’, an SRE command is sent to rank[i], i=0..3
#define SW_CMD_SR_CTRL_SRE                                              SW_CMD_SR_CTRL_SRE
#define SW_CMD_SR_CTRL_SRE_MASK                                         0x0000000F
#define SW_CMD_SR_CTRL_SRE_BIT_OFFSET                                            0
// [7:4]: SRX, when bit[i] is ‘1’, an SRX command is sent to rank[i], i=0..3
#define SW_CMD_SR_CTRL_SRX                                              SW_CMD_SR_CTRL_SRX
#define SW_CMD_SR_CTRL_SRX_MASK                                         0x000000F0
#define SW_CMD_SR_CTRL_SRX_BIT_OFFSET                                            4
// [8]: FC. Frequency Change Flag.
// When FC bit is ‘1’, SREF command is sent.
// When FC bit is ‘0’, SRE command is sent.
#define SW_CMD_SR_CTRL_FC                                               SW_CMD_SR_CTRL_FC
#define SW_CMD_SR_CTRL_FC_MASK                                          0x00000100
#define SW_CMD_SR_CTRL_FC_BIT_OFFSET                                             8


///////////////  RST_CTRL   ///////////////
//
// DDR Reset Control command (0x04 -  4)
// Control DDR Reset entry and exit for all physical ranks
//
// RSTE, when setting this bit to ‘1’, an RSTE command is sent to all physical ranks,
// and the RESETn Pin of all ranks will be reset to ’0’
#define SW_CMD_RST_CTRL_RSTE                                            SW_CMD_RST_CTRL_RSTE
#define SW_CMD_RST_CTRL_RSTE_MASK                                       0x00000001
#define SW_CMD_RST_CTRL_RSTE_BIT_OFFSET                                          0
// [4]: RSTX, when setting this bit to ‘1’, an RSTX command is sent to all ranks, and the
// RESETn Pin of all ranks will be pulled high.
#define SW_CMD_RST_CTRL_RSTX                                            SW_CMD_RST_CTRL_RSTX
#define SW_CMD_RST_CTRL_RSTX_MASK                                       0x00000010
#define SW_CMD_RST_CTRL_RSTX_BIT_OFFSET                                          4


///////////////     MPC     ///////////////
//
//  DDR MPC command sent to the ranks selected by CSn. (0x05 -  5)
//  Note; 1. Multi-cycle MPC can be sent based on the MR configuration. CMD_CTRL will
//           control the CS timing for tMC_MPC_Setup, tMPC_CS and tMC_MPC_Hold for
//           multi-cycle MPC.
//        2. For MPC commands which require idle state of target rank, software should guarantee
//           the rank state before sending MPC.
//        3. For MPC commands operating the manual ECS sequence, software must guarantee
//           and control the timing tECSc after sending MPC.
//
// [7]: DDPID - Dual-Die Packaging (DDP)
#define SW_CMD_MPC_DDPID                                                SW_CMD_MPC_DDPID
#define SW_CMD_MPC_DDPID_MASK                                           0x00000080
#define SW_CMD_MPC_DDPID_BIT_OFFSET                                              7
// [15:8]: OP[7:0]
#define SW_CMD_MPC_OP                                                   SW_CMD_MPC_OP
#define SW_CMD_MPC_OP_MASK                                              0x0000FF00
#define SW_CMD_MPC_OP_BIT_OFFSET                                                 8
// [19]: Pause_Ref_En: When this field is ‘1’, refresh to the target rank will be paused
//       before the MPC command is executed. Refresh will be resumed after the MPC is done.
//       0: disable, 1: enable
#define SW_CMD_MPC_PAUSE_REF_EN                                         SW_CMD_MPC_PAUSE_REF_EN
#define SW_CMD_MPC_PAUSE_REF_EN_MASK                                    0x00080000
#define SW_CMD_MPC_PAUSE_REF_EN_BIT_OFFSET                                      19
// [23:20]: CSn[3:0]
#define SW_CMD_MPC_CS_N                                                 SW_CMD_MPC_CS_N
#define SW_CMD_MPC_CS_N_MASK                                            0x00F00000
#define SW_CMD_MPC_CS_N_BIT_OFFSET                                              20


///////////////     PRE     ///////////////
//
// DDR Precharge All Bank command (0x06 -  6)
//
// [3:0]: CID (aka LRANK[3:0])
#define SW_CMD_PRE_CID                                                  SW_CMD_PRE_CID
#define SW_CMD_PRE_CID_MASK                                             0x0000000F
#define SW_CMD_PRE_CID_BIT_OFFSET                                                0
// [5:4]: PRE_TYPE (only PREab supported), 00: PREab, Others: Reserved
#define SW_CMD_PRE_TYPE                                                 SW_CMD_PRE_TYPE
#define SW_CMD_PRE_TYPE_MASK                                            0x00000030
#define SW_CMD_PRE_TYPE_BIT_OFFSET                                               4
#define SW_CMD_PRE_TYPE_PREAB                                                    0
// [23:20]: CSn
#define SW_CMD_PRE_CS_N                                                 SW_CMD_PRE_CS_N
#define SW_CMD_PRE_CS_N_MASK                                            0x00F00000
#define SW_CMD_PRE_CS_N_BIT_OFFSET                                              20


///////////////     REF     ///////////////
//
// DDR Refresh All Bank command  (0x07 -  7)
//
// [3:0]: CID (aka LRANK[3:0])
#define SW_CMD_REF_CID                                                  SW_CMD_REF_CID
#define SW_CMD_REF_CID_MASK                                             0x0000000F
#define SW_CMD_REF_CID_BIT_OFFSET                                                0
// [5:4]: REF_TYPE (only REFab supported), 00: REFab, Others: Reserved
#define SW_CMD_REF_TYPE                                                 SW_CMD_REF_TYPE
#define SW_CMD_REF_TYPE_MASK                                            0x00000030
#define SW_CMD_REF_TYPE_BIT_OFFSET                                               4
#define SW_CMD_REF_TYPE_REFAB                                                    0
// [23:20]: CSn
#define SW_CMD_REF_CS_N                                                 SW_CMD_REF_CS_N
#define SW_CMD_REF_CS_N_MASK                                            0x00F00000
#define SW_CMD_REF_CS_N_BIT_OFFSET                                              20


///////////////     NOP     ///////////////
//
//  Send continuous NOP to particular Ranks. (0x09 -  9)
//
// [11:0]: command count (0 means one NOP command, 1 means 2 consecutive NOPs,
//         2 means 3 consecutive NOPs, etc)
#define SW_CMD_NOP_COUNT                                                SW_CMD_NOP_COUNT
#define SW_CMD_NOP_COUNT_MASK                                           0x00000FFF
#define SW_CMD_NOP_COUNT_BIT_OFFSET                                              0
// [23:20]: CSn
#define SW_CMD_NOP_CS_N                                                 SW_CMD_NOP_CS_N
#define SW_CMD_NOP_CS_N_MASK                                            0x00F00000
#define SW_CMD_NOP_CS_N_BIT_OFFSET                                              20


///////////////  DisDqRef   ///////////////
//
// Disable De-Queue Refresh command (0x0B - 11)
//
// [3:0] Disable De-Queue Set, when CMD_START is high and bit[i] is 1, dis_dq[i] will be set to 1, i=0..3
#define SW_CMD_DISDQREF_DIS_DQ_SET                                      SW_CMD_DISDQREF_DIS_DQ_SET
#define SW_CMD_DISDQREF_DIS_DQ_SET_MASK                                 0x0000000F
#define SW_CMD_DISDQREF_DIS_DQ_SET_BIT_OFFSET                                    0
// [7:4] Disable De-Queue Reset, when CMD_START is high and bit[i] is 1, dis_dq[i] will be reset to 0, i=0..3
#define SW_CMD_DISDQREF_DIS_DQ_RESET                                    SW_CMD_DISDQREF_DIS_DQ_RESET
#define SW_CMD_DISDQREF_DIS_DQ_RESET_MASK                               0x000000F0
#define SW_CMD_DISDQREF_DIS_DQ_RESET_BIT_OFFSET                                  4
// [11:8] Disable Refresh Set, when CMD_START is high and bit[i] is 1, dis_ref[i] will be set to 1, i=0..3
#define SW_CMD_DISDQREF_DIS_REF_SET                                     SW_CMD_DISDQREF_DIS_REF_SET
#define SW_CMD_DISDQREF_DIS_REF_SET_MASK                                0x00000F00
#define SW_CMD_DISDQREF_DIS_REF_SET_BIT_OFFSET                                   8
// [15:12]: Disable Refresh reset, when CMD_START is high and bit[i] is 1, dis_ref[i] will be reset to 0, i=0..3
#define SW_CMD_DISDQREF_DIS_REF_RESET                                   SW_CMD_DISDQREF_DIS_REF_RESET
#define SW_CMD_DISDQREF_DIS_REF_RESET_MASK                              0x0000F000
#define SW_CMD_DISDQREF_DIS_REF_RESET_BIT_OFFSET                                12
// [16]: Disable Refresh type, 0: PauseRef, block Refresh requests and pause refresh counters; 1:
//       BlockRef, block Refresh requests only without pausing refresh counters
#define SW_CMD_DISDQREF_DIS_REF_TYPE                                    SW_CMD_DISDQREF_DIS_REF_TYPE
#define SW_CMD_DISDQREF_DIS_REF_TYPE_MASK                               0x00010000
#define SW_CMD_DISDQREF_DIS_REF_TYPE_BIT_OFFSET                                 16



///////////////  FORCE_CS   ///////////////
//
// Force and release corresponding CSn command (0x0C - 12)
// 1. FORCE_CSE and FORCE_CSX can be issued at the same time for different CSn.
// 2. If FORCE_CSE[i] and FORCE_CSX[i] are all high in same command,
//    FORCE_CSX[i] will take the priority, CSn[i] shall be set to ’1’.
//
// [3:0]: FORCE_CSE, when bit[i] is ‘1’, CSn[i] will be reset to ‘0’, i=0..3
#define SW_CMD_FORCE_CS_CSE                                             SW_CMD_FORCE_CS_CSE
#define SW_CMD_FORCE_CS_CSE_MASK                                        0x0000000F
#define SW_CMD_FORCE_CS_CSE_BIT_OFFSET                                           0
// 7:4]: FORCE_CSX, when bit[i] is ‘1’, CSn[i] will be set to ‘1’, i=0..3
#define SW_CMD_FORCE_CS_CSX                                             SW_CMD_FORCE_CS_CSX
#define SW_CMD_FORCE_CS_CSX_MASK                                        0x000000F0
#define SW_CMD_FORCE_CS_CSX_BIT_OFFSET                                           4


///////////////   OP_CTRL   ///////////////
//
// Operation control command  (0x0D - 13)
//
#define SW_CMD_OP_CTRL_SRX_DONE_TXSDLL                                  SW_CMD_OP_CTRL_SRX_DONE_TXSDLL
#define SW_CMD_OP_CTRL_SRX_DONE_TXSDLL_MASK                             0x0000000F
#define SW_CMD_OP_CTRL_SRX_DONE_TXSDLL_BIT_OFFSET                                0
#define SW_CMD_OP_CTRL_SRX_DONE_TXS                                     SW_CMD_OP_CTRL_SRX_DONE_TXS
#define SW_CMD_OP_CTRL_SRX_DONE_TXS_MASK                                0x000000F0
#define SW_CMD_OP_CTRL_SRX_DONE_TXS_BIT_OFFSET                                   4
#define SW_CMD_OP_CTRL_PDX_DONE                                         SW_CMD_OP_CTRL_PDX_DONE
#define SW_CMD_OP_CTRL_PDX_DONE_MASK                                    0x00000F00
#define SW_CMD_OP_CTRL_PDX_DONE_BIT_OFFSET                                       8
#define SW_CMD_OP_CTRL_MPSMX_DONE                                       SW_CMD_OP_CTRL_MPSMX_DONE
#define SW_CMD_OP_CTRL_MPSMX_DONE_MASK                                  0x0000F000
#define SW_CMD_OP_CTRL_MPSMX_DONE_BIT_OFFSET                                    12
#define SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_EN                           SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_EN
#define SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_EN_MASK                      0x000F0000
#define SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_EN_BIT_OFFSET                        16
#define SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_DIS                          SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_DIS
#define SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_DIS_MASK                     0x00F00000
#define SW_CMD_OP_CTRL_NON_TARGET_ODT_CTRL_DIS_BIT_OFFSET                       20


///////////////    DFIUPD   ///////////////
//
// DFI update command  (0x17 - 23)
//
// Notes:
//   1. ctrlupd_done in CMDSTAT.cmd_rslt[15]
//   2. ctrlupd_ack  in CMDSTAT.cmd_rslt[14]
//   3. The ctrlupd_req will be cleared by ctrlupd_ack. When ctrlupd_ack is ‘1’, the
//      DFIUPD/ctrlupd command is sent/executed. When ctrlupd_ack is ‘1’, ctrlupd_done
//      must be checked to determent if the command is executed successfully. When
//      ctrlupd_done is ‘1’, the ctrlupd command is executed successfully, otherwise the
//      ctrlupd command is rejected by PHY.
// [0]: ctrlupd_req_set. When command starts, if this bit is 1, the ctrlupd_req will be set by controller.
#define SW_CMD_DFIUPD_CTRL_UPD_REQ_SET                                  SW_CMD_DFIUPD_CTRL_UPD_REQ_SET
#define SW_CMD_DFIUPD_CTRL_UPD_REQ_SET_MASK                             0x00000001
#define SW_CMD_DFIUPD_CTRL_UPD_REQ_SET_BIT_OFFSET                                0
// [1]: [1]: ctrlupd_retry_en. 0-disabled, 1-enabled. When ctrlupd_retry_en is 1, controller
//                             will retry controller update request if the previous request gets rejected by PHY.
//                             If the controller update still fails after REG_CTRLUPD_RETRY_THR times retry, an
//                             interrupt will be set and ctrlupd_ack is set to ’1’, but ctrlupd_done is
//                             set to ’0’.
#define SW_CMD_DFIUPD_CTRL_UPD_RETRY_EN                                 SW_CMD_DFIUPD_CTRL_UPD_REQ_SET
#define SW_CMD_DFIUPD_CTRL_UPD_RETRY_EN_MASK                            0x00000002
#define SW_CMD_DFIUPD_CTRL_UPD_RETRY_EN_BIT_OFFSET                               1


///////////////    DFIFC    ///////////////
//
// DFI Frequency Change command  (0x17 - 23)
//
// Notes:
//   1. dfi_init_done in CMDSTAT.cmd_rslt[17]
//   2. dfi_init_ack  in CMDSTAT.cmd_rslt[16]
//   3. When dfi_init_ack is ‘1’, dfi_ini_done must be checked to determent if the command
//      is executed successfully. When dfi_init_done is ‘1’, the DFILP command is
//      executed successfully. Otherwise the DFIFC command is rejected by PHY.
//
// [0]: dfi_init_start_set. When this bit is ‘1’, set dfi_init_start of DFI Frequency Change interface
#define SW_CMD_DFIFC_DFI_INIT_START_SET                                 SW_CMD_DFIFC_DFI_INIT_START_SET
#define SW_CMD_DFIFC_DFI_INIT_START_SET_MASK                            0x00000001
#define SW_CMD_DFIFC_DFI_INIT_START_SET_BIT_OFFSET                               0
// [1]: dfi_init_start_clear. When this bit is ‘1’, clear dfi_init_start of DFI Frequency Change interface
#define SW_CMD_DFIFC_DFI_INIT_START_CLEAR                               SW_CMD_DFIFC_DFI_INIT_START_CLEAR
#define SW_CMD_DFIFC_DFI_INIT_START_CLEAR_MASK                          0x00000002
#define SW_CMD_DFIFC_DFI_INIT_START_CLEAR_BIT_OFFSET                             1
// [5:4]: dfi_freq_ratio of DFI Frequency Change Interface
#define SW_CMD_DFIFC_DFI_FREQ_RATIO                                     SW_CMD_DFIFC_DFI_FREQ_RATIO
#define SW_CMD_DFIFC_DFI_FREQ_RATIO_MASK                                0x00000030
#define SW_CMD_DFIFC_DFI_FREQ_RATIO_BIT_OFFSET                                   4
// [10:6]: dfi_frequency of DFI Frequency Change Interface
#define SW_CMD_DFIFC_DFI_FREQUENCY                                      SW_CMD_DFIFC_DFI_FREQUENCY
#define SW_CMD_DFIFC_DFI_FREQUENCY_MASK                                 0x000007C0
#define SW_CMD_DFIFC_DFI_FREQUENCY_BIT_OFFSET                                    6
// [16:11]: dfi_freq_fsp of DFI Frequency Change Interface. Support up to 64 FSPs
#define SW_CMD_DFIFC_DFI_FREQ_FSP                                       SW_CMD_DFIFC_DFI_FREQ_FSP
#define SW_CMD_DFIFC_DFI_FREQ_FSP_MASK                                  0x0001F800
#define SW_CMD_DFIFC_DFI_FREQ_FSP_BIT_OFFSET                                    11


///////////////   DFICLK    ///////////////
//
// DFI clock disable control command  (0x19 - 25)
// dfi_clk_dis_ctrl: 1-disable DDR clock, 0-enable DDR clock.
// This command will disable DDR clock for full DFI clock cycle. The default value of
// dfi_clk_dis_ctrl is ‘0’.
// Notes
// 1. Bits [0] and [1] can not be all ‘1’ in the same command
// 2. CSn[3:0] is low active to determine which rank the command is set to
// 3. dfi_clk_dis_req will be defined in CMDSTAT.cmd_rslt
//
// [0]: dfi_clk_disable_set. When this bit is ‘1’, the command set dfi_clk_clk_ctrl to disable DDR clock.
#define SW_CMD_DFICLK_DISABLE_SET                                       SW_CMD_DFICLK_DISABLE_SET
#define SW_CMD_DFICLK_DISABLE_SET_MASK                                  0x00000001
#define SW_CMD_DFICLK_DISABLE_SET_BIT_OFFSET                                     0
// [1]: dfi_clk_disable_clear. When this bit is ‘1’, the command reset dfi_clk_clk_ctrl to enable DDR clock.
#define SW_CMD_DFICLK_DISABLE_CLEAR                                     SW_CMD_DFICLK_DISABLE_CLEAR
#define SW_CMD_DFICLK_DISABLE_CLEAR_MASK                                0x00000002
#define SW_CMD_DFICLK_DISABLE_CLEAR_BIT_OFFSET                                   1
// [23:20]: CSn
#define SW_CMD_DFICLK_CS_N                                              SW_CMD_DFICLK_CS_N
#define SW_CMD_DFICLK_CS_N_MASK                                         0x00F00000
#define SW_CMD_DFICLK_CS_N_BIT_OFFSET                                           20


/////////////// DFI_2N_MODE ///////////////
//
// Command to control the dfi_2n_mode output to DDR PHY (0x1A - 26)
//  When dfi_2n_mode is 0, DDR and PHY operate in 1N mode.
//  When dfi_2n_mode is 1, DDR and PHY operate in 2N mode
//
// [0]: dfi_2n_mode_set. When this bit is 1, the command starts 2N mode entry
//                       sequence to put PHY in 2N mode.
#define SW_CMD_DFI_2N_MODE_SET                                          SW_CMD_DFI_2N_MODE_SET
#define SW_CMD_DFI_2N_MODE_SET_MASK                                     0x00000001
#define SW_CMD_DFI_2N_MODE_SET_BIT_OFFSET                                        0
// [1]: dfi_2n_mode_clear. When this bit is 1, the command starts a 2N mode exit
//                         sequence to put PHY in 1N mode.
#define SW_CMD_DFI_2N_MODE_CLEAR                                        SW_CMD_DFI_2N_MODE_CLEAR
#define SW_CMD_DFI_2N_MODE_CLEAR_MASK                                   0x00000002
#define SW_CMD_DFI_2N_MODE_CLEAR_BIT_OFFSET                                      1


///////////////  REF_FLUSH  ///////////////
// Flush all postponed refreshes command  (0x1B - 27)
//  REF_FLUSH can not be used in the middle of atomic SCI sequences. In other
//  words, the software command interface command issued before REF_FLUSH
//  should have CMDCTL.cmd_seq_last set to '1
//
// [23:20]: CSn
#define SW_CMD_REF_FLUSH_CS_N                                           SW_CMD_REF_FLUSH_CS_N
#define SW_CMD_REF_FLUSH_CS_N_MASK                                      0x00F00000
#define SW_CMD_REF_FLUSH_CS_N_BIT_OFFSET                                        20


#endif  // __MODULES_CORE_INCLUDE_CINIT_DDR5_SW_CMD_H__
