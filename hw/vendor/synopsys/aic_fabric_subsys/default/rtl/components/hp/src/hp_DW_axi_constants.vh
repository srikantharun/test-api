/* ---------------------------------------------------------------------
**
// ------------------------------------------------------------------------------
// 
// Copyright 2001 - 2020 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// 
// Component Name   : DW_axi
// Component Version: 4.04a
// Release Type     : GA
// ------------------------------------------------------------------------------

// 
// Release version :  4.04a
// File Version     :        $Revision: #1 $ 
// Revision: $Id: //dwh/DW_ocb/DW_axi/amba_dev/src/DW_axi_constants.vh#1 $ 
**
** ---------------------------------------------------------------------
**h
** File     : DW_axi_constants.v
//
//
** Created  : Tue May 24 17:09:09 MEST 2005
** Modified : $Date: 2020/03/22 $
** Abstract : Some static macro's for DW_axi.
**
** ---------------------------------------------------------------------
*/

//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`define hp___GUARD__DW_AXI_CONSTANTS__VH__

// Burst Size Width
`define hp_AXI_BSW 3
// Burst Type Width
`define hp_AXI_BTW 2
// Locked Type Width
`define hp_AXI_LTW ((`hp_AXI_INTERFACE_TYPE >0)? 1 :2)
//`define hp_AXI_LTW 2 
// Cache Type Width
`define hp_AXI_CTW 4
// Protection Type Width
`define hp_AXI_PTW 3
// Buffered Response Width
`define hp_AXI_BRW 2
// Read Response Width
`define hp_AXI_RRW 2
// The width of the write strobe bus
`define hp_AXI_SW        (`hp_AXI_DW/8)

// Maximum number of masters or slaves.
// Including default slave.
`define hp_AXI_MAX_NUM_MST_SLVS 17

// Maximum number of user masters.
`define hp_AXI_MAX_NUM_USR_MSTS 16

// Maximum number of user slaves.
`define hp_AXI_MAX_NUM_USR_SLVS 16

// Locked type field macros.
`define hp_AXI_LT_NORM  2'b00
`define hp_AXI_LT_EX    2'b01
`define hp_AXI_LT_LOCK  2'b10

// Protection type field macros.
`define hp_AXI_PT_PRVLGD    3'bxx1
`define hp_AXI_PT_NORM      3'bxx0
`define hp_AXI_PT_SECURE    3'bx1x
`define hp_AXI_PT_NSECURE   3'bx0x
`define hp_AXI_PT_INSTRUCT  3'b1xx
`define hp_AXI_PT_DATA      3'b0xx

`define hp_AXI_PT_PRVLGD_BIT   0
`define hp_AXI_PT_INSTRUCT_BIT 2

// Encoding definition of RESP signals.
`define hp_AXI_RESP_OKAY     2'b00
`define hp_AXI_RESP_EXOKAY   2'b01
`define hp_AXI_RESP_SLVERR   2'b10
`define hp_AXI_RESP_DECERR   2'b11

// Encoding definition of timing option parameters.
`define hp_AXI_TMO_COMB  2'b00
`define hp_AXI_TMO_FRWD  2'b01
`define hp_AXI_TMO_FULL  2'b10

// Macros used as parameter inputs to blocks,
`define hp_AXI_NOREQ_LOCKING  0 // No locking functionality required.
`define hp_AXI_REQ_LOCKING    1 // Locking functionality required.

// Macros to define the encoding of the the AXI arbitration type
// paramters e.g. AXI_AR_ARBITER_S0.
`define hp_AXI_ARB_TYPE_DP   0
`define hp_AXI_ARB_TYPE_FCFS 1
`define hp_AXI_ARB_TYPE_2T   2
`define hp_AXI_ARB_TYPE_USER 3
`define hp_AXI_ARB_TYPE_QOS  4

// Some blocks need to implement different logic depending
// on what type of channel they are implementing, these macros
// are used for that purpose.
`define hp_AXI_W_CH 1      // This channel is a write data channel.
`define hp_AXI_NOT_W_CH  0 // This channel is not a write data channel.

`define hp_AXI_AW_CH 1      // This channel is a write address channel.
`define hp_AXI_NOT_AW_CH  0 // This channel is not a write address channel.

`define hp_AXI_R_CH 1      // This channel is a read data channel.
`define hp_AXI_NOT_R_CH  0 // This channel is not a read data channel.

`define hp_AXI_ADDR_CH 1     // This channel is an address channel.
`define hp_AXI_NOT_ADDR_CH 0 // This channel is not an address channel.

// Macros to pass to the USE_INT_GRANT_INDEX parameter of the
// DW_axi_arb block.
`define hp_USE_INT_GI  1 // Use internal grant index.
`define hp_USE_EXT_GI  0 // Use external grant index.

// Macros, encoding of shared parameters.
`define hp_AXI_SHARED 1
`define hp_AXI_NOT_SHARED 0

// Width of buses containing hold valid status bits for all 
// sources at all other destinations, from master annd slave 
// perspective.
`define hp_AXI_HOLD_VLD_OTHER_S_W (`hp_AXI_NUM_MASTERS*(`hp_AXI_NSP1-1))
`define hp_AXI_HOLD_VLD_OTHER_M_W ((`hp_AXI_NUM_MASTERS > 1) ? (`hp_AXI_NSP1*(`hp_AXI_NUM_MASTERS-1)) : 1)


// Macros for bit field position of components of
// read address channel payload vector.
`define hp_AXI_ARPYLD_PROT_RHS 0
`define hp_AXI_ARPYLD_PROT_LHS ((`hp_AXI_PTW-1) + `hp_AXI_ARPYLD_PROT_RHS)
`define hp_AXI_ARPYLD_PROT    1 
 
`define hp_AXI_ARPYLD_CACHE_RHS (`hp_AXI_ARPYLD_PROT_LHS + 1)
`define hp_AXI_ARPYLD_CACHE_LHS ((`hp_AXI_CTW-1) + `hp_AXI_ARPYLD_CACHE_RHS)
`define hp_AXI_ARPYLD_CACHE     `hp_AXI_ARPYLD_CACHE_LHS:`hp_AXI_ARPYLD_CACHE_RHS
 
`define hp_AXI_ARPYLD_LOCK_RHS (`hp_AXI_ARPYLD_CACHE_LHS + 1)
`define hp_AXI_ARPYLD_LOCK_LHS ((`hp_AXI_LTW-1) + `hp_AXI_ARPYLD_LOCK_RHS)
`define hp_AXI_ARPYLD_LOCK     `hp_AXI_ARPYLD_LOCK_LHS:`hp_AXI_ARPYLD_LOCK_RHS
 
`define hp_AXI_ARPYLD_BURST_RHS (`hp_AXI_ARPYLD_LOCK_LHS + 1)
`define hp_AXI_ARPYLD_BURST_LHS ((`hp_AXI_BTW-1) + `hp_AXI_ARPYLD_BURST_RHS)
`define hp_AXI_ARPYLD_BURST     `hp_AXI_ARPYLD_BURST_LHS:`hp_AXI_ARPYLD_BURST_RHS
 
`define hp_AXI_ARPYLD_SIZE_RHS (`hp_AXI_ARPYLD_BURST_LHS + 1)
`define hp_AXI_ARPYLD_SIZE_LHS ((`hp_AXI_BSW-1) + `hp_AXI_ARPYLD_SIZE_RHS)
`define hp_AXI_ARPYLD_SIZE     `hp_AXI_ARPYLD_SIZE_LHS:`hp_AXI_ARPYLD_SIZE_RHS
 
`define hp_AXI_ARPYLD_LEN_RHS (`hp_AXI_ARPYLD_SIZE_LHS + 1)
`define hp_AXI_ARPYLD_LEN_LHS ((`hp_AXI_BLW-1) + `hp_AXI_ARPYLD_LEN_RHS)
`define hp_AXI_ARPYLD_LEN     `hp_AXI_ARPYLD_LEN_LHS:`hp_AXI_ARPYLD_LEN_RHS
 
`define hp_AXI_ARPYLD_ADDR_RHS (`hp_AXI_ARPYLD_LEN_LHS + 1)
`define hp_AXI_ARPYLD_ADDR_LHS ((`hp_AXI_AW-1) + `hp_AXI_ARPYLD_ADDR_RHS)
`define hp_AXI_ARPYLD_ADDR     `hp_AXI_ARPYLD_ADDR_LHS:`hp_AXI_ARPYLD_ADDR_RHS
 
// Note : Different ID widths in master and slave ports.
`define hp_AXI_ARPYLD_ID_RHS_M (`hp_AXI_ARPYLD_ADDR_LHS + 1)
`define hp_AXI_ARPYLD_ID_LHS_M ((`hp_AXI_MIDW-1) + `hp_AXI_ARPYLD_ID_RHS_M)
`define hp_AXI_ARPYLD_ID_M     `hp_AXI_ARPYLD_ID_LHS_M:`hp_AXI_ARPYLD_ID_RHS_M
 
`define hp_AXI_ARPYLD_ID_RHS_S (`hp_AXI_ARPYLD_ADDR_LHS + 1)
`define hp_AXI_ARPYLD_ID_LHS_S ((`hp_AXI_SIDW-1) + `hp_AXI_ARPYLD_ID_RHS_S)
`define hp_AXI_ARPYLD_ID_S     `hp_AXI_ARPYLD_ID_LHS_S:`hp_AXI_ARPYLD_ID_RHS_S
 
 
// Macros for bit field position of components of
// read data channel payload vector.
`define hp_AXI_RPYLD_LAST_LHS 0
`define hp_AXI_RPYLD_LAST     `hp_AXI_RPYLD_LAST_LHS
 
`define hp_AXI_RPYLD_RESP_RHS (`hp_AXI_RPYLD_LAST_LHS + 1)
`define hp_AXI_RPYLD_RESP_LHS ((`hp_AXI_RRW-1) + `hp_AXI_RPYLD_RESP_RHS)
`define hp_AXI_RPYLD_RESP     `hp_AXI_RPYLD_RESP_LHS:`hp_AXI_RPYLD_RESP_RHS
 
`define hp_AXI_RPYLD_DATA_RHS (`hp_AXI_RPYLD_RESP_LHS + 1)
`define hp_AXI_RPYLD_DATA_LHS ((`hp_AXI_DW-1) + `hp_AXI_RPYLD_DATA_RHS)
`define hp_AXI_RPYLD_DATA     `hp_AXI_RPYLD_DATA_LHS:`hp_AXI_RPYLD_DATA_RHS
 
// Note : Different ID widths in master and slave ports.
`define hp_AXI_RPYLD_ID_RHS_M (`hp_AXI_RPYLD_DATA_LHS + 1)
`define hp_AXI_RPYLD_ID_LHS_M ((`hp_AXI_MIDW-1) + `hp_AXI_RPYLD_ID_RHS_M)
`define hp_AXI_RPYLD_ID_M     `hp_AXI_RPYLD_ID_LHS_M:`hp_AXI_RPYLD_ID_RHS_M
 
`define hp_AXI_RPYLD_ID_RHS_S (`hp_AXI_RPYLD_DATA_LHS + 1)
`define hp_AXI_RPYLD_ID_LHS_S ((`hp_AXI_SIDW-1) + `hp_AXI_RPYLD_ID_RHS_S)
`define hp_AXI_RPYLD_ID_S     `hp_AXI_RPYLD_ID_LHS_S:`hp_AXI_RPYLD_ID_RHS_S
 
 
// Macros for bit field position of components of
// write address channel payload vector.
`define hp_AXI_AWPYLD_PROT_RHS 0
`define hp_AXI_AWPYLD_PROT_LHS ((`hp_AXI_PTW-1) + `hp_AXI_AWPYLD_PROT_RHS)
`define hp_AXI_AWPYLD_PROT     `hp_AXI_AWPYLD_PROT_LHS:`hp_AXI_AWPYLD_PROT_RHS
 
`define hp_AXI_AWPYLD_CACHE_RHS (`hp_AXI_AWPYLD_PROT_LHS + 1)
`define hp_AXI_AWPYLD_CACHE_LHS ((`hp_AXI_CTW-1) + `hp_AXI_AWPYLD_CACHE_RHS)
`define hp_AXI_AWPYLD_CACHE     `hp_AXI_AWPYLD_CACHE_LHS:`hp_AXI_AWPYLD_CACHE_RHS
 
`define hp_AXI_AWPYLD_LOCK_RHS (`hp_AXI_AWPYLD_CACHE_LHS + 1)
`define hp_AXI_AWPYLD_LOCK_LHS ((`hp_AXI_LTW-1) + `hp_AXI_AWPYLD_LOCK_RHS)
`define hp_AXI_AWPYLD_LOCK     `hp_AXI_AWPYLD_LOCK_LHS:`hp_AXI_AWPYLD_LOCK_RHS
 
`define hp_AXI_AWPYLD_BURST_RHS (`hp_AXI_AWPYLD_LOCK_LHS + 1)
`define hp_AXI_AWPYLD_BURST_LHS ((`hp_AXI_BTW-1) + `hp_AXI_AWPYLD_BURST_RHS)
`define hp_AXI_AWPYLD_BURST     `hp_AXI_AWPYLD_BURST_LHS:`hp_AXI_AWPYLD_BURST_RHS
 
`define hp_AXI_AWPYLD_SIZE_RHS (`hp_AXI_AWPYLD_BURST_LHS + 1)
`define hp_AXI_AWPYLD_SIZE_LHS ((`hp_AXI_BSW-1) + `hp_AXI_AWPYLD_SIZE_RHS)
`define hp_AXI_AWPYLD_SIZE     `hp_AXI_AWPYLD_SIZE_LHS:`hp_AXI_AWPYLD_SIZE_RHS
 
`define hp_AXI_AWPYLD_LEN_RHS (`hp_AXI_AWPYLD_SIZE_LHS + 1)
`define hp_AXI_AWPYLD_LEN_LHS ((`hp_AXI_BLW-1) + `hp_AXI_AWPYLD_LEN_RHS)
`define hp_AXI_AWPYLD_LEN     `hp_AXI_AWPYLD_LEN_LHS:`hp_AXI_AWPYLD_LEN_RHS
 
`define hp_AXI_AWPYLD_ADDR_RHS (`hp_AXI_AWPYLD_LEN_LHS + 1)
`define hp_AXI_AWPYLD_ADDR_LHS ((`hp_AXI_AW-1) + `hp_AXI_AWPYLD_ADDR_RHS)
`define hp_AXI_AWPYLD_ADDR     `hp_AXI_AWPYLD_ADDR_LHS:`hp_AXI_AWPYLD_ADDR_RHS
 
// Note : Different ID widths in master and slave ports.
`define hp_AXI_AWPYLD_ID_RHS_M (`hp_AXI_AWPYLD_ADDR_LHS + 1)
`define hp_AXI_AWPYLD_ID_LHS_M ((`hp_AXI_MIDW-1) + `hp_AXI_AWPYLD_ID_RHS_M)
`define hp_AXI_AWPYLD_ID_M     `hp_AXI_AWPYLD_ID_LHS_M:`hp_AXI_AWPYLD_ID_RHS_M
 
`define hp_AXI_AWPYLD_ID_RHS_S (`hp_AXI_AWPYLD_ADDR_LHS + 1)
`define hp_AXI_AWPYLD_ID_LHS_S ((`hp_AXI_SIDW-1) + `hp_AXI_AWPYLD_ID_RHS_S)
`define hp_AXI_AWPYLD_ID_S     `hp_AXI_AWPYLD_ID_LHS_S:`hp_AXI_AWPYLD_ID_RHS_S
 
 
// Macros for bit field position of components of
// write data channel payload vector.
`define hp_AXI_WPYLD_LAST_LHS 0
`define hp_AXI_WPYLD_LAST     `hp_AXI_WPYLD_LAST_LHS
 
`define hp_AXI_WPYLD_STRB_RHS (`hp_AXI_WPYLD_LAST_LHS + 1)
`define hp_AXI_WPYLD_STRB_LHS ((`hp_AXI_SW-1) + `hp_AXI_WPYLD_STRB_RHS)
`define hp_AXI_WPYLD_STRB     `hp_AXI_WPYLD_STRB_LHS:`hp_AXI_WPYLD_STRB_RHS
 
`define hp_AXI_WPYLD_DATA_RHS (`hp_AXI_WPYLD_STRB_LHS + 1)
`define hp_AXI_WPYLD_DATA_LHS ((`hp_AXI_DW-1) + `hp_AXI_WPYLD_DATA_RHS)
`define hp_AXI_WPYLD_DATA     `hp_AXI_WPYLD_DATA_LHS:`hp_AXI_WPYLD_DATA_RHS
 
// Note : Different ID widths in master and slave ports.
`define hp_AXI_WPYLD_ID_RHS_M (`hp_AXI_WPYLD_DATA_LHS + 1)
`define hp_AXI_WPYLD_ID_LHS_M ((`hp_AXI_MIDW-1) + `hp_AXI_WPYLD_ID_RHS_M)
`define hp_AXI_WPYLD_ID_M     `hp_AXI_WPYLD_ID_LHS_M:`hp_AXI_WPYLD_ID_RHS_M
 
`define hp_AXI_WPYLD_ID_RHS_S (`hp_AXI_WPYLD_DATA_LHS + 1)
`define hp_AXI_WPYLD_ID_LHS_S ((`hp_AXI_SIDW-1) + `hp_AXI_WPYLD_ID_RHS_S)
`define hp_AXI_WPYLD_ID_S     `hp_AXI_WPYLD_ID_LHS_S:`hp_AXI_WPYLD_ID_RHS_S
 
 
// Macros for bit field position of components of
// burst response channel payload vector.
`define hp_AXI_BPYLD_RESP_RHS 0
`define hp_AXI_BPYLD_RESP_LHS ((`hp_AXI_BRW-1) + `hp_AXI_BPYLD_RESP_RHS)
`define hp_AXI_BPYLD_RESP     `hp_AXI_BPYLD_RESP_LHS:`hp_AXI_BPYLD_RESP_RHS
 
// Note : Different ID widths in master and slave ports.
`define hp_AXI_BPYLD_ID_RHS_M (`hp_AXI_BPYLD_RESP_LHS + 1)
`define hp_AXI_BPYLD_ID_LHS_M ((`hp_AXI_MIDW-1) + `hp_AXI_BPYLD_ID_RHS_M)
`define hp_AXI_BPYLD_ID_M     `hp_AXI_BPYLD_ID_LHS_M:`hp_AXI_BPYLD_ID_RHS_M
 
`define hp_AXI_BPYLD_ID_RHS_S (`hp_AXI_BPYLD_RESP_LHS + 1)
`define hp_AXI_BPYLD_ID_LHS_S ((`hp_AXI_SIDW-1) + `hp_AXI_BPYLD_ID_RHS_S)
`define hp_AXI_BPYLD_ID_S     `hp_AXI_BPYLD_ID_LHS_S:`hp_AXI_BPYLD_ID_RHS_S
 
// QOS Signal width
`define hp_AXI_QOSW  4
 // APB constant
`define hp_IC_ADDR_SLICE_LHS  5
`define hp_MAX_APB_DATA_WIDTH 32
`define hp_REG_XCT_RATE_W      12
`define hp_REG_BURSTINESS_W    8
`define hp_REG_PEAK_RATE_W     12
`define hp_APB_ADDR_WIDTH      32

//AXI 4 specific constant
`define hp_AXI_ALSW 4 
`define hp_AXI_ALDW 2
`define hp_AXI_ALBW 2
`define hp_AXI_REGIONW 4


`define hp_PL_BUF_AW 1


`define hp_PL_BUF_AR 1


// Active IDs buffer pointer width

`define hp_ACT_ID_BUF_POINTER_W_AW_M1 198


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M1 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M1 198


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M1 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M2 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M2 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M2 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M2 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M3 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M3 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M3 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M3 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M4 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M4 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M4 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M4 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M5 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M5 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M5 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M5 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M6 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M6 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M6 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M6 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M7 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M7 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M7 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M7 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M8 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M8 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M8 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M8 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M9 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M9 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M9 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M9 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M10 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M10 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M10 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M10 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M11 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M11 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M11 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M11 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M12 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M12 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M12 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M12 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M13 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M13 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M13 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M13 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M14 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M14 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M14 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M14 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M15 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M15 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M15 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M15 8


`define hp_ACT_ID_BUF_POINTER_W_AW_M16 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AW_M16 8


`define hp_ACT_ID_BUF_POINTER_W_AR_M16 132


`define hp_LOG2_ACT_ID_BUF_POINTER_W_AR_M16 8

//==============================================================================
// End Guard
//==============================================================================  
