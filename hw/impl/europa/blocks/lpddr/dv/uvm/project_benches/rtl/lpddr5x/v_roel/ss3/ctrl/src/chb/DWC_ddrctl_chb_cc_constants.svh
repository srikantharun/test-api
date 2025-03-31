//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/chb/DWC_ddrctl_chb_cc_constants.svh#10 $
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
// Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
// ------------------------------------------------------------------------------


`ifndef __GUARD__DWC_DDRCTL_CHB_CC_CONSTANTS__SVH__
`define __GUARD__DWC_DDRCTL_CHB_CC_CONSTANTS__SVH__


`define DDRCTL_HAS_CHB 0


`define DDRCTL_HAS_CHB_CHIE 0


// Name:         DDRCTL_CHB_QOSW
// Default:      4
// Values:       -2147483648, ..., 2147483647
// 
// QoS Width.
`define DDRCTL_CHB_QOSW 4


// Name:         DDRCTL_CHB_BEW
// Default:      32 (DDRCTL_CHB_DW/8)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Data flit ByteEnable Width.
`define DDRCTL_CHB_BEW 32


// Name:         DDRCTL_CHB_NIDW
// Default:      7
// Values:       7, ..., 11
// 
// CHI Flit NodeID Width
`define DDRCTL_CHB_NIDW 7


// Name:         DDRCTL_CHB_ENDW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// StashNIDValid / Endian Width.
`define DDRCTL_CHB_ENDW 1


// Name:         DDRCTL_CHB_REQ_OPCW
// Default:      6 ((DDRCTL_CHB_CHIE_EN==1)? 7 : 6)
// Values:       6 7
// 
// Request Opcode Width.
`define DDRCTL_CHB_REQ_OPCW 6



// Name:         DDRCTL_CHB_REQ_SZW
// Default:      3
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Number of bits required to represent clog2(Max HIF Burst Size in Bytes).
`define DDRCTL_CHB_REQ_SZW 3


// Name:         DDRCTL_CHB_NSW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// NS Width.
`define DDRCTL_CHB_NSW 1


// Name:         DDRCTL_CHB_NSEW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// NSE Width.
`define DDRCTL_CHB_NSEW 1


// Name:         DDRCTL_CHB_MPAM_NSW
// Default:      1 ((DDRCTL_CHB_CHIF_EN==1)? 2 : 1)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// MPAM_NS/MPAMSP Width.
`define DDRCTL_CHB_MPAM_NSW 1


// Name:         DDRCTL_CHB_PBHA_EN
// Default:      0
// Values:       0, 1
// Enabled:      0
// 
// Enables PBHA field in the RXREQ channel. 
// This new filed is unused in the controller, but provided for interface compatibility.
// `define DDRCTL_CHB_PBHA_EN


// Name:         DDRCTL_CHB_PBHAW
// Default:      4
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// PBHA filed width in RXREQ flit.
`define DDRCTL_CHB_PBHAW 4


// Name:         DDRCTL_CHB_CAHW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// CAH field width in TXDAT/RXDAT flit.
`define DDRCTL_CHB_CAHW 1


// Name:         DDRCTL_CHB_LSW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Likely Shared Width.
`define DDRCTL_CHB_LSW 1


// Name:         DDRCTL_CHB_ARW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Allow Retry Width.
`define DDRCTL_CHB_ARW 1


// Name:         DDRCTL_CHB_ORW
// Default:      2
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Order Width.
`define DDRCTL_CHB_ORW 2


// Name:         DDRCTL_CHB_PCRDW
// Default:      4
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// P credit Type Width.
`define DDRCTL_CHB_PCRDW 4


// Name:         DDRCTL_INT_CHB_PCRDW
// Default:      2
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Number of valid bits used internally in CHB
`define DDRCTL_INT_CHB_PCRDW 2


// Name:         DDRCTL_CHB_MATTW
// Default:      4
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Mem Attribute Width.
`define DDRCTL_CHB_MATTW 4



// Name:         DDRCTL_CHB_SATTW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Snp Attr Width.
`define DDRCTL_CHB_SATTW 1



// Name:         DDRCTL_CHB_LPIDW
// Default:      5
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// LPID field Width.
`define DDRCTL_CHB_LPIDW 5


// Name:         DDRCTL_CHB_LPIDEXW
// Default:      5 (DDRCTL_CHB_CHIE_EN==1 ? 8 : 5)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// DDRCTL_CHB_LPIDW: 
// LPID / PGroupID extended Width.
`define DDRCTL_CHB_LPIDEXW 5


// Name:         DDRCTL_CHB_XSNPW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Exclude / SnoopMe Width.
`define DDRCTL_CHB_XSNPW 1


// Name:         DDRCTL_CHB_EXCAW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// ExpCompack Width.
`define DDRCTL_CHB_EXCAW 1



// Name:         DDRCTL_CHB_TTW
// Default:      1
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Trace Tag Width.
`define DDRCTL_CHB_TTW 1



// Name:         DDRCTL_MPAM_APB_NS_FIRST_ADDRESS
// Default:      0x40000
// Values:       0x40000, ..., 0x40000
// Enabled:      0
// 
// First Register Address of APB MPAM Non-Secure Reg
`define DDRCTL_MPAM_APB_NS_FIRST_ADDRESS 20'h40000


// Name:         DDRCTL_MPAM_APB_NS_LAST_ADDRES
// Default:      0x4ffff
// Values:       0x4ffff, ..., 0x4ffff
// Enabled:      0
// 
// Last Register Address of APB MPAM Non-Secure Reg
`define DDRCTL_MPAM_APB_NS_LAST_ADDRES 20'h4ffff


// Name:         DDRCTL_MPAM_APB_S_FIRST_ADDRESS
// Default:      0x50000
// Values:       0x50000, ..., 0x50000
// Enabled:      0
// 
// First Register Address of APB MPAM Secure Reg
`define DDRCTL_MPAM_APB_S_FIRST_ADDRESS 20'h50000


// Name:         DDRCTL_MPAM_APB_S_LAST_ADDRES
// Default:      0x5ffff
// Values:       0x5ffff, ..., 0x5ffff
// Enabled:      0
// 
// Last Register Address of APB MPAM Secure Reg
`define DDRCTL_MPAM_APB_S_LAST_ADDRES 20'h5ffff


// Name:         DDRCTL_MPAM_APB_RT_FIRST_ADDRESS
// Default:      0x60000
// Values:       0x60000, ..., 0x60000
// Enabled:      0
// 
// First Register Address of APB MPAM Root Reg
`define DDRCTL_MPAM_APB_RT_FIRST_ADDRESS 20'h60000


// Name:         DDRCTL_MPAM_APB_RT_LAST_ADDRES
// Default:      0x6ffff
// Values:       0x6ffff, ..., 0x6ffff
// Enabled:      0
// 
// Last Register Address of APB MPAM Root Reg
`define DDRCTL_MPAM_APB_RT_LAST_ADDRES 20'h6ffff


// Name:         DDRCTL_MPAM_APB_RL_FIRST_ADDRESS
// Default:      0x70000
// Values:       0x70000, ..., 0x70000
// Enabled:      0
// 
// First Register Address of APB MPAM Root Reg
`define DDRCTL_MPAM_APB_RL_FIRST_ADDRESS 20'h70000


// Name:         DDRCTL_MPAM_APB_RL_LAST_ADDRES
// Default:      0x7ffff
// Values:       0x7ffff, ..., 0x7ffff
// Enabled:      0
// 
// Last Register Address of APB MPAM Root Reg
`define DDRCTL_MPAM_APB_RL_LAST_ADDRES 20'h7ffff




// Name:         DDRCTL_MPAM_MAX_NONSECURE_PMG
// Default:      0x0 ((DDRCTL_CHB_MPAM_NSMON_EN==1) ? 0x01 : 0x00)
// Values:       0x0, ..., (DDRCTL_CHB_MPAM_NSMON_EN==1) ? 0x01 : 0xFF
// Enabled:      DDRCTL_CHB_MPAM_EN == 1
// 
// Maximum value of non-secure PMG
`define DDRCTL_MPAM_MAX_NONSECURE_PMG 8'h0


// Name:         DDRCTL_MPAM_MAX_SECURE_PMG
// Default:      0x0 ((DDRCTL_CHB_MPAM_SMON_EN==1) ? 0x01 : 0x00)
// Values:       0x0, ..., (DDRCTL_CHB_MPAM_SMON_EN==1) ? 0x01 : 0xFF
// Enabled:      DDRCTL_CHB_MPAM_EN == 1
// 
// Maximum value of secure PMG
`define DDRCTL_MPAM_MAX_SECURE_PMG 8'h0


// Name:         DDRCTL_MPAM_MAX_RT_PMG
// Default:      0x0 ((DDRCTL_CHB_MPAM_RTMON_EN==1) ? 0x01 : 0x00)
// Values:       0x0, ..., (DDRCTL_CHB_MPAM_RTMON_EN==1) ? 0x01 : 0xFF
// Enabled:      0
// 
// Maximum value of Root PMG
`define DDRCTL_MPAM_MAX_RT_PMG 8'h0



// Name:         DDRCTL_MPAM_MAX_RL_PMG
// Default:      0x0 ((DDRCTL_CHB_MPAM_RLMON_EN==1) ? 0x01 : 0x00)
// Values:       0x0, ..., (DDRCTL_CHB_MPAM_RLMON_EN==1) ? 0x01 : 0xFF
// Enabled:      0
// 
// Maximum value of Realm PMG
`define DDRCTL_MPAM_MAX_RL_PMG 8'h0


// Name:         DDRCTL_MPAM_MAX_NONSECURE_PARTID
// Default:      0x80
// Values:       0x1, ..., 0xff
// Enabled:      DDRCTL_CHB_MPAM_EN == 1
// 
// Maximum value of non-secure PARTID
`define DDRCTL_MPAM_MAX_NONSECURE_PARTID 8'h80



// Name:         DDRCTL_MPAM_MAX_SECURE_PARTID
// Default:      0x80
// Values:       0x1, ..., 0xff
// Enabled:      DDRCTL_CHB_MPAM_EN == 1
// 
// Maximum value of secure PARTID
`define DDRCTL_MPAM_MAX_SECURE_PARTID 8'h80


// Name:         DDRCTL_MPAMCFG_MBW_MIN_CYC_CNT
// Default:      11
// Values:       0, ..., 16777215
// Enabled:      DDRCTL_CHB_MPAM_EN==1
// 
// MBW Min Threshold in cycle counter
`define DDRCTL_MPAMCFG_MBW_MIN_CYC_CNT 11


// Name:         DDRCTL_MPAMCFG_MBW_MAX_CYC_CNT
// Default:      31
// Values:       0, ..., 16777215
// Enabled:      DDRCTL_CHB_MPAM_EN==1
// 
// MBW Max Threshold in cycle counter
`define DDRCTL_MPAMCFG_MBW_MAX_CYC_CNT 31


// Name:         DDRCTL_CHB_BWCWINWD
// Default:      24
// Values:       8, ..., 32
// Enabled:      DDRCTL_CHB_MPAM_EN==1
// 
// MPAM BW counter window width  
// Size of DDRCTL_MBW_WINWD_US_FRAC + DDRCTL_MBW_WINWD_US_INT
`define DDRCTL_CHB_BWCWINWD 24


// Name:         DDRCTL_CHB_MPAMW
// Default:      0 ((DDRCTL_CHB_MPAM_EN==1) ? ((DDRCTL_CHB_CHIF_EN==1) ? 12 : 11) : 
//               0)
// Values:       0 11 12
// Enabled:      DDRCTL_CHB_MPAM_EN==1
// 
// MPAM-ID flit field width
`define DDRCTL_CHB_MPAMW 0



`define DDRCTL_CHB_MPAM_WIDTH 0


// Name:         DDRCTL_CHB_RRSVDCW
// Default:      0
// Values:       0 4 12
// 
// Req flit RSVDC Width.
`define DDRCTL_CHB_RRSVDCW 0


// Name:         DDRCTL_CHB_RRSVDC_EN
// Default:      0 ((DDRCTL_CHB_RRSVDCW == 0)?0:1)
// Values:       0, 1
// 
// Req flit RSVDC enable.
// `define DDRCTL_CHB_RRSVDC_EN


// Name:         DDRCTL_CHB_RSP_OPCW
// Default:      4 ((DDRCTL_CHB_CHIE_EN==1)? 5 : 4)
// Values:       4 5
// 
// Resp Opcode Width.
`define DDRCTL_CHB_RSP_OPCW 4


// Name:         DDRCTL_CHB_RPERW
// Default:      2
// Values:       -2147483648, ..., 2147483647
// 
// Response Error Width.
`define DDRCTL_CHB_RPERW 2


// Name:         DDRCTL_CHB_RPW
// Default:      3
// Values:       -2147483648, ..., 2147483647
// 
// Resp Width.
`define DDRCTL_CHB_RPW 3


// Name:         DDRCTL_CHB_FSDW
// Default:      3
// Values:       -2147483648, ..., 2147483647
// 
// FwdState / DataPull Width.
`define DDRCTL_CHB_FSDW 3


// Name:         DDRCTL_CHB_TGOPW
// Default:      0 ((DDRCTL_CHB_CHIE_EN==1)?2 : 0)
// Values:       -2147483648, ..., 2147483647
// 
// Tag OP Width.
`define DDRCTL_CHB_TGOPW 0


// Name:         DDRCTL_CHB_DSRCW
// Default:      4 ((DDRCTL_CHB_VERSION > 4)? 5 : (DDRCTL_CHB_VERSION > 2)? 4 : 3)
// Values:       3 4 5
// 
// FwdState/DataPull/DataSource Width.
`define DDRCTL_CHB_DSRCW 4


// Name:         DDRCTL_CHB_CBSYW
// Default:      3 ((DDRCTL_CHB_VERSION > 2) ? 3 : 0)
// Values:       -2147483648, ..., 2147483647
// 
// C Busy Width.
`define DDRCTL_CHB_CBSYW 3


// Name:         DDRCTL_CHB_DRSVDCW
// Default:      0 ((DDRCTL_CHB_METADATA_EN == 1) ? (DDRCTL_CHB_METADATA_WIDTH <= 4) 
//               ? 4 : (DDRCTL_CHB_METADATA_WIDTH <= 8) ? 8 : 
//               (DDRCTL_CHB_METADATA_WIDTH <= 12) ? 12 : 16 : 0)
// Values:       0 4 8 12 16
// 
// Data flit RSVDC Width.
`define DDRCTL_CHB_DRSVDCW 0


// Name:         DDRCTL_CHB_DRSVDC_EN
// Default:      0 ((DDRCTL_CHB_DRSVDCW == 0)?0:1)
// Values:       0, 1
// 
// DDRCTL_CHB_RRSVDC_EN: 
// Data RSVDC enable.
// `define DDRCTL_CHB_DRSVDC_EN


// Name:         DDRCTL_CHB_DCHKW
// Default:      0 (DDRCTL_NUM_BITS_PER_KBD==64 ? 
//               (DDRCTL_CHB_DCHK_EN*DDRCTL_CHB_BEW) : (DDRCTL_CHB_DCHK_EN*DDRCTL_CHB_CHI_ECCW) )
// Values:       -2147483648, ..., 2147483647
// 
// Data Check Width.
`define DDRCTL_CHB_DCHKW 0


// Name:         DDRCTL_CHB_POISW
// Default:      0 (DDRCTL_CHB_POIS_EN ? (DDRCTL_CHB_DW/DDRCTL_NUM_BITS_PER_KBD) : 
//               0)
// Values:       -2147483648, ..., 2147483647
// 
// RXDAT/TXDAT Poison Flit Width.
`define DDRCTL_CHB_POISW 0


// Name:         DDRCTL_CHB_HIF_POISW
// Default:      0 (DDRCTL_NUM_BITS_PER_KBD==64 ? MEMC_DFI_DATA_WIDTH/64 : 
//               DDRCTL_CHB_KBD_ECC_EN ? DDRCTL_HIF_KBD_WIDTH : 0)
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_HIF POISW: 
// HIF Write/Read Data Interface Poison Width
`define DDRCTL_CHB_HIF_POISW 0


// `define DDRCTL_CHB_HIF_POISW_GT_2


// Name:         DDRCTL_CHB_RTLSTOST
// Default:      1024 ((DDRCTL_CHB_VERSION > 2) ? 1024 : 256)
// Values:       32, ..., 8192
// Enabled:      0
// 
// Max Outstandinge.
`define DDRCTL_CHB_RTLSTOST 1024


// Name:         DDRCTL_CHB_RTADRW
// Default:      10 ((DDRCTL_CHB_VERSION > 2) ? 10 : 8)
// Values:       5, ..., 16
// Enabled:      0
// 
// LOG2(DDRCTL_CHB_RTLSTOST)
`define DDRCTL_CHB_RTADRW 10


// Name:         DDRCTL_CHB_DAT_OPCW
// Default:      4
// Values:       -2147483648, ..., 2147483647
// 
// Data Channel Opcode Width.
`define DDRCTL_CHB_DAT_OPCW 4


// Name:         DDRCTL_CHB_DAT_CCFWO
// Default:      0
// Values:       0, 1
// Enabled:      0
// 
// DDRCTL_CHB_CCFWO:  
// CCF_WRAP_ORDER Status, this is a read-only parameter
// `define DDRCTL_CHB_DAT_CCFWO


// Name:         DDRCTL_CHB_CDBID
// Default:      True
// Values:       False (0), True (1)
// Enabled:      0
// 
//  
// DBID response type status 
// - 0 seperate DBIDresp and Comp 
// - 1 Combined CompDBID response
`define DDRCTL_CHB_CDBID 1


// Name:         DDRCTL_CHB_MAX_LCRD
// Default:      15
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// CHI Max number of supported Lcredits by individual links. 
// Common configuration applicable for all DDRCTL links
`define DDRCTL_CHB_MAX_LCRD 15


// Name:         DDRCTL_CHB_BRW
// Default:      5
// Values:       -2147483648, ..., 2147483647
// 
// DWC_DDRCTL_CHB_BRW.
`define DDRCTL_CHB_BRW 5


// Name:         DDRCTL_CHB_DBW
// Default:      2
// Values:       -2147483648, ..., 2147483647
// 
// DWC_DDRCTL_CHB_DBW.
`define DDRCTL_CHB_DBW 2


// Name:         DDRCTL_CHB_EARLY_PUSH
// Default:      0
// Values:       -2147483648, ..., 2147483647
// 
// Registered versions of push status signals.
`define DDRCTL_CHB_EARLY_PUSH 0


// Name:         DDRCTL_CHB_EARLY_POP
// Default:      0
// Values:       -2147483648, ..., 2147483647
// 
// Registered versions of pop status signals.
`define DDRCTL_CHB_EARLY_POP 0


// Name:         DDRCTL_CHB_REQ_AQ_DEPTH
// Default:      128 (2*MEMC_NO_OF_ENTRY)
// Values:       -2147483648, ..., 2147483647
// 
// Depth of CHB Address queue.
`define DDRCTL_CHB_REQ_AQ_DEPTH 128


// Name:         DDRCTL_CHB_REQ_AQ_DEPTH_LG2
// Default:      7 ([ <functionof> DDRCTL_CHB_REQ_AQ_DEPTH ])
// Values:       -2147483648, ..., 2147483647
// 
// Depth of CHB Address queue.
`define DDRCTL_CHB_REQ_AQ_DEPTH_LG2 7


// Name:         DDRCTL_CHB_NUM_RSPPORTS
// Default:      5
// Values:       -2147483648, ..., 2147483647
// 
// Number of TXRESP ARB PORTS
`define DDRCTL_CHB_NUM_RSPPORTS 5


// Name:         DDRCTL_CHB_TXRESP_SRC4_PRIO
// Default:      0
// Values:       -2147483648, ..., 2147483647
// 
// Arbitration priority for Source no. 4 of TXRESP block
`define DDRCTL_CHB_TXRESP_SRC4_PRIO 0


// Name:         DDRCTL_CHB_TXRESP_SRC3_PRIO
// Default:      0
// Values:       -2147483648, ..., 2147483647
// 
// Arbitration priority for Source no. 3 of TXRESP block
`define DDRCTL_CHB_TXRESP_SRC3_PRIO 0


// Name:         DDRCTL_CHB_TXRESP_SRC2_PRIO
// Default:      0
// Values:       -2147483648, ..., 2147483647
// 
// Arbitration priority for Source no. 2 of TXRESP block
`define DDRCTL_CHB_TXRESP_SRC2_PRIO 0


// Name:         DDRCTL_CHB_TXRESP_SRC1_PRIO
// Default:      0
// Values:       -2147483648, ..., 2147483647
// 
// Arbitration priority for Source no. 1 of TXRESP block
`define DDRCTL_CHB_TXRESP_SRC1_PRIO 0


// Name:         DDRCTL_CHB_TXRESP_SRC0_PRIO
// Default:      0
// Values:       -2147483648, ..., 2147483647
// 
// Arbitration priority for Source no. 0 of TXRESP block
`define DDRCTL_CHB_TXRESP_SRC0_PRIO 0


// Name:         DDRCTL_CHB_TXRESP_FIFO_4_DEPTH
// Default:      8
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_TXRESP_FIFO_4_DEPTH 
// TXRESP incoming data fifo depth for Source 4.
`define DDRCTL_CHB_TXRESP_FIFO_4_DEPTH 8


// Name:         DDRCTL_CHB_TXRESP_FIFO_3_DEPTH
// Default:      8
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_TXRESP_FIFO_3_DEPTH 
// TXRESP incoming data fifo depth for Source 3.
`define DDRCTL_CHB_TXRESP_FIFO_3_DEPTH 8


// Name:         DDRCTL_CHB_TXRESP_FIFO_2_DEPTH
// Default:      8
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_TXRESP_FIFO_2_DEPTH 
// TXRESP incoming data fifo depth for Source 2.
`define DDRCTL_CHB_TXRESP_FIFO_2_DEPTH 8


// Name:         DDRCTL_CHB_TXRESP_FIFO_1_DEPTH
// Default:      8
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_TXRESP_FIFO_1_DEPTH 
// TXRESP incoming data fifo depth for Source 1.
`define DDRCTL_CHB_TXRESP_FIFO_1_DEPTH 8


// Name:         DDRCTL_CHB_TXRESP_FIFO_0_DEPTH
// Default:      8
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_TXRESP_FIFO_0_DEPTH 
// TXRESP incoming data fifo depth for Source 0.
`define DDRCTL_CHB_TXRESP_FIFO_0_DEPTH 8


`define DDRCTL_CHB_UPSZ_RT_1


// `define DDRCTL_CHB_UPSZ_RT_2


// `define DDRCTL_CHB_UPSZ_RT_4


// Name:         DDRCTL_CHB_WRB_DBID_RLS_LAT
// Default:      8
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies WRB's DBID ready to DBID release latency 
//  Extra DBID tokens and WRB depth is needed to handle this DBID release latency.
`define DDRCTL_CHB_WRB_DBID_RLS_LAT 8


// Name:         DDRCTL_CHB_WRB_SIZE
// Default:      4608 
//               ((DDRCTL_CHB_WR_PROTQ_SIZE+DDRCTL_CHB_WRB_DBID_RLS_LAT)*DDRCTL_CHB_XFRSZ)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Write Buffer Size in Bytes. 
// The buffer size equates to the number of outstanding CHI write requests 
// (DDRCTL_CHB_WR_PROTQ_SIZE+DDRCTL_CHB_WRB_DBID_RLS_LAT) times the CHI cache line size (DDRCTL_CHB_XFRSZ).
`define DDRCTL_CHB_WRB_SIZE 4608


// Name:         DDRCTL_CHB_WRB_RAM_DP
// Default:      144 (DDRCTL_CHB_WRB_SIZE*8/(DDRCTL_CHB_DW*DDRCTL_CHB_UPSZ_RT))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Write Buffer RAM depth.
`define DDRCTL_CHB_WRB_RAM_DP 144


// Name:         DDRCTL_CHB_WRB_RAM_ADDR_WD
// Default:      8 ([ <functionof> DDRCTL_CHB_WRB_RAM_DP ])
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Write Buffer RAM address width.
`define DDRCTL_CHB_WRB_RAM_ADDR_WD 8


// Name:         DDRCTL_CHB_WRB_RAM_RAW_DATA_WD
// Default:      256 (DDRCTL_CHB_DW)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Write Buffer RAM raw data width, no protection.
`define DDRCTL_CHB_WRB_RAM_RAW_DATA_WD 256


// Name:         DDRCTL_CHB_WRB_RAM_PROTW
// Default:      0 (DDRCTL_NUM_BITS_PER_KBD==64 ? 
//               (DDRCTL_CHB_DCHK_EN*DDRCTL_CHB_BEW) : (DDRCTL_CHB_DCHK_EN*DDRCTL_CHB_CHI_ECCW) )
// Values:       -2147483648, ..., 2147483647
// 
// Specifies the CHB Write Buffer RAM Interface Protection width.
`define DDRCTL_CHB_WRB_RAM_PROTW 0


// Name:         DDRCTL_CHB_WRB_RAM_POISW
// Default:      0 (DDRCTL_CHB_POIS_EN ? (DDRCTL_CHB_DW/DDRCTL_NUM_BITS_PER_KBD) : 
//               0)
// Values:       -2147483648, ..., 2147483647
// 
// Specifies the CHB Write Buffer RAM Interface Poison width.
`define DDRCTL_CHB_WRB_RAM_POISW 0


// Name:         DDRCTL_CHB_WRB_RAM_PYLD_DATA_WD
// Default:      288 (DDRCTL_CHB_WRB_RAM_RAW_DATA_WD + 
//               (DDRCTL_CHB_WRB_RAM_RAW_DATA_WD/8) + (DDRCTL_CHB_POIS_EN*DDRCTL_CHB_WRB_RAM_POISW))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Write Buffer RAM  payload width without protection. 
// Includes Byte Enables, Poison and Data.
`define DDRCTL_CHB_WRB_RAM_PYLD_DATA_WD 288


// Name:         DDRCTL_CHB_WRB_RAM_WR_DATA_WD
// Default:      288 (DDRCTL_CHB_WRB_RAM_PYLD_DATA_WD + 
//               (DDRCTL_CHB_DCHK_EN*DDRCTL_CHB_WRB_RAM_PROTW) + 
//               (DDRCTL_CHB_METADATA_EN*DDRCTL_CHB_METADATA_WIDTH))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Write Buffer RAM Write Interface data width.
`define DDRCTL_CHB_WRB_RAM_WR_DATA_WD 288


// Name:         DDRCTL_CHB_WRB_RAM_RD_DATA_WD
// Default:      288 (DDRCTL_CHB_WRB_RAM_RAW_DATA_WD + DDRCTL_CHB_BEW + 
//               (DDRCTL_CHB_POIS_EN*DDRCTL_CHB_WRB_RAM_POISW) + 
//               (DDRCTL_CHB_METADATA_EN*DDRCTL_CHB_METADATA_WIDTH))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Write Buffer RAM Read Interface Data Width.
`define DDRCTL_CHB_WRB_RAM_RD_DATA_WD 288


// Name:         DDRCTL_CHB_WRB_RAM_DATA_WD
// Default:      288 (DDRCTL_CHB_WRB_RAM_WR_DATA_WD)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Write Buffer RAM Data Width.  
// Include ECC and poison bits if end to end data error tracking enabled.
`define DDRCTL_CHB_WRB_RAM_DATA_WD 288


// Name:         DDRCTL_CHB_WRB_RAM_WR_LATENCY
// Default:      0
// Values:       0 1
// Enabled:      0
// 
// Specifies the Write Buffer RAM write latency in core_clk cycles. 
// The write latency is defined at the Write Buffer RAM interface port and 
// sets the number of core clock cycles from the RAM write address/data valid, 
// chb_wrb_ram_wr_[addr|data]_p*, to write address/data valid at the RAM write port.
`define DDRCTL_CHB_WRB_RAM_WR_LATENCY 0


// Name:         DDRCTL_CHB_WRB_RAM_RD_LATENCY
// Default:      1
// Values:       1 2
// Enabled:      0
// 
// Specifies the Write Buffer RAM read latency in core_clk cycles. 
// The read latency is defined at the Read Buffer RAM interface port and 
// sets the number of core clock cycles from RAM read address valid, 
// chb_wrb_ram_rd_addr_p*, to RAM read data valid, chb_wrb_ram_rd_data_p*.
`define DDRCTL_CHB_WRB_RAM_RD_LATENCY 1


// Name:         DDRCTL_CHB_WRB_RAM_WR_REG_OUT
// Default:      1
// Values:       0, 1
// Enabled:      0
// 
// Register the CHB Write Buffer RAM write address and data interface signals. 
// Enabling this register stage allows you to trade latency and gates for ease of timing closure.
`define DDRCTL_CHB_WRB_RAM_WR_REG_OUT 1


// Name:         DDRCTL_CHB_WRB_RAM_RD_ADDR_REG_OUT
// Default:      1
// Values:       0, 1
// Enabled:      0
// 
// Register the CHB Write Buffer RAM read address interface signals. 
// Enabling this register stage allows you to trade latency and gates for ease of timing closure.
`define DDRCTL_CHB_WRB_RAM_RD_ADDR_REG_OUT 1


// Name:         DDRCTL_CHB_WRB_RAM_RD_DATA_REG_IN
// Default:      0
// Values:       0, 1
// Enabled:      0
// 
// Register the CHB Write Buffer RAM read data interface signals. 
// Enabling this register stage allows you to trade latency and gates for ease of timing closure. 
//  Pipe register is implemented inside CHB
`define DDRCTL_CHB_WRB_RAM_RD_DATA_REG_IN 0


// Name:         DDRCTL_CHB_WRB_RAM_RD_REQ_INFO_REG_OUT
// Default:      0
// Values:       0, 1
// Enabled:      0
// 
// Hidden CHB Write Buffer RAM Read Request Information Pipeline. Defaults to 0.
`define DDRCTL_CHB_WRB_RAM_RD_REQ_INFO_REG_OUT 0


// Name:         DDRCTL_CHB_RDB_PREF_RD_MAX_RAM_DP
// Default:      16 (DDRCTL_CHB_XFRSZ*8)/MEMC_DFI_DATA_WIDTH > 
//               DDRCTL_CHB_NUM_BEATS_BL ? 
//               (DDRCTL_CHB_MAX_PRC_LINES*DDRCTL_CHB_XFRSZ*8)/MEMC_DFI_DATA_WIDTH : (DDRCTL_CHB_MAX_PRC_LINES*DDRCTL_CHB_NUM_BEATS_BL)
// Values:       -2147483648, ..., 2147483647
// 
// Calculate the maximum CHB Prefetch Read Buffer RAM depth. 
// If the eHIF Buffer size is greather than the cache line size then the cache size is number of cache lines 
// times the eHIF buffer size else its the number of cache lines times the cache line size. 
// If the eHIF Buffer size is greather than the cache line size then to scale the size of prefetcg buffer with  
// the cache line an enhancment is required to mask the redundant HIF data beat on the write side versus the read size of 
// the buffer.
`define DDRCTL_CHB_RDB_PREF_RD_MAX_RAM_DP 16


// Name:         DDRCTL_CHB_RDB_PREF_RD_RAM_DP
// Default:      16 (DDRCTL_CHB_DDR4F5HBW_AREA_OPT ? 
//               DDRCTL_CHB_RDB_PREF_RD_MAX_RAM_DP/2 : DDRCTL_CHB_RDB_PREF_RD_MAX_RAM_DP)
// Values:       -2147483648, ..., 2147483647
// 
// Specifies the CHB Prefetch Read Buffer RAM depth. 
// When DDRCTL_CHB_DDR4F5HBW_AREA_OPT is true then the max CHI request size or cache size correlates to one DDR4 FBW HIF 
// burst or one DDR5 HBW burst. In this scenario the physical size of the prefetch buffer can be reduced by half.
`define DDRCTL_CHB_RDB_PREF_RD_RAM_DP 16


// Name:         DDRCTL_CHB_RDB_DMD_RD_RAM_DP
// Default:      128 (DDRCTL_CHB_DDR4F5HBW_AREA_OPT ? 
//               MEMC_NO_OF_RD_ENTRY_CHB*DDRCTL_CHB_NUM_BEATS_BL/2 : 
//               MEMC_NO_OF_RD_ENTRY_CHB*DDRCTL_CHB_NUM_BEATS_BL)
// Values:       -2147483648, ..., 2147483647
// 
// Specifies the CHB Demand Read Buffer RAM depth. 
// Depth equates to number of HIF bursts for demand reads times the HIF burst length.
`define DDRCTL_CHB_RDB_DMD_RD_RAM_DP 128


// Name:         DDRCTL_CHB_RDB_RAM_DP
// Default:      128 (DDRCTL_CHB_RDB_DMD_RD_RAM_DP + 
//               DDRCTL_CHB_PREFETCH_EN*DDRCTL_CHB_RDB_PREF_RD_RAM_DP)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Read Buffer RAM depth. 
// Depth equates to number of HIF bursts for demand reads and prefetch reads times the HIF burst length.
`define DDRCTL_CHB_RDB_RAM_DP 128


// Name:         DDRCTL_CHB_RDB_RAM_ADDR_WD
// Default:      7 ([ <functionof> DDRCTL_CHB_RDB_RAM_DP ])
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Read Buffer RAM address width.  
// log2ceil[DDRCTL_CHB_RDB_RAM_DP]
`define DDRCTL_CHB_RDB_RAM_ADDR_WD 7


// Name:         DDRCTL_CHB_RDB_RAM_RAW_DATA_WD
// Default:      256 (MEMC_DFI_DATA_WIDTH/DDRCTL_CHB_HIF_TO_CHI_DW_RATIO)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Read Buffer RAM raw data width, no protection.  
// The number of RAMs scales with the HIF to CHI data width ratio.
`define DDRCTL_CHB_RDB_RAM_RAW_DATA_WD 256


// Name:         DDRCTL_CHB_RDB_RAM_PROTW
// Default:      0 (DDRCTL_NUM_BITS_PER_KBD==64 ? 
//               (DDRCTL_CHB_DCHK_EN*DDRCTL_CHB_BEW) : (DDRCTL_CHB_DCHK_EN*DDRCTL_CHB_CHI_ECCW) )
// Values:       -2147483648, ..., 2147483647
// 
// Specifies the CHB Read Buffer RAM Interface Protection  width.
`define DDRCTL_CHB_RDB_RAM_PROTW 0


// Name:         DDRCTL_CHB_RDB_RAM_POISW
// Default:      1 ((DDRCTL_CHB_HIF_POISW>1) ? 
//               DDRCTL_CHB_HIF_POISW/DDRCTL_CHB_HIF_TO_CHI_DW_RATIO : 1)
// Values:       -2147483648, ..., 2147483647
// 
// Specifies the CHB Read Buffer RAM Interface Poison width.
`define DDRCTL_CHB_RDB_RAM_POISW 1


// Name:         DDRCTL_CHB_RDB_RAM_WR_DATA_WD
// Default:      256 (DDRCTL_CHB_RDB_RAM_RAW_DATA_WD + 
//               (DDRCTL_CHB_POIS_EN*DDRCTL_CHB_RDB_RAM_POISW) + 
//               (DDRCTL_CHB_METADATA_EN*DDRCTL_CHB_METADATA_WIDTH))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Read Buffer RAM Write Interface data width.
`define DDRCTL_CHB_RDB_RAM_WR_DATA_WD 256


// Name:         DDRCTL_CHB_RDB_RAM_PYLD_DATA_WD
// Default:      256 (DDRCTL_CHB_RDB_RAM_RAW_DATA_WD + 
//               (DDRCTL_CHB_POIS_EN*DDRCTL_CHB_RDB_RAM_POISW))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Read Buffer RAM Interface payload data width i.e without protection.
`define DDRCTL_CHB_RDB_RAM_PYLD_DATA_WD 256


// Name:         DDRCTL_CHB_RDB_RAM_RD_DATA_WD
// Default:      256 (DDRCTL_CHB_RDB_RAM_RAW_DATA_WD + 
//               (DDRCTL_CHB_DCHK_EN*DDRCTL_CHB_RDB_RAM_PROTW) + (DDRCTL_CHB_POIS_EN*DDRCTL_CHB_RDB_RAM_POISW) + 
//               (DDRCTL_CHB_METADATA_EN*DDRCTL_CHB_METADATA_WIDTH))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Read Buffer RAM Read Interface data width.
`define DDRCTL_CHB_RDB_RAM_RD_DATA_WD 256


// Name:         DDRCTL_CHB_RDB_RAM_DATA_WD
// Default:      256 (DDRCTL_CHB_RDB_RAM_RD_DATA_WD)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Read Buffer RAM Data Width.  
// Include ECC and poison bits if end to end data error tracking enabled.
`define DDRCTL_CHB_RDB_RAM_DATA_WD 256


// Name:         DDRCTL_CHB_RDB_RAM_WR_LATENCY
// Default:      0
// Values:       0 1
// Enabled:      0
// 
// Specifies the Read Buffer RAM write latency in core_clk cycles. 
// The write latency is defined at the Read Buffer RAM interface port and 
// sets the number of core clock cycles from the RAM write address/data valid, 
// chb_rdb_ram_wr_[addr|data]_p*, to write address/data valid at the RAM write port.
`define DDRCTL_CHB_RDB_RAM_WR_LATENCY 0


// Name:         DDRCTL_CHB_RDB_RAM_RD_LATENCY
// Default:      1
// Values:       1 2
// Enabled:      0
// 
// Specifies the Read Buffer RAM read latency in core_clk cycles. 
// The read latency is defined at the Read Buffer RAM interface port and 
// sets the number of core clock cycles from RAM read address valid, 
// chb_rdb_ram_rd_addr_p*, to RAM read data valid, chb_rdb_ram_rd_data_p*.
`define DDRCTL_CHB_RDB_RAM_RD_LATENCY 1


// Name:         DDRCTL_CHB_RDB_RAM_WR_REG_OUT
// Default:      0
// Values:       0, 1
// Enabled:      0
// 
// Register the CHB Read Buffer RAM write address and data interface signals. 
// Enabling this register stage allows you to trade latency and gates for ease of timing closure.
`define DDRCTL_CHB_RDB_RAM_WR_REG_OUT 0


// Name:         DDRCTL_CHB_RDB_RAM_RD_ADDR_REG_OUT
// Default:      0 (DDRCTL_CHB_RDB_RAM_WR_REG_OUT)
// Values:       0, 1
// Enabled:      0
// 
// Register the CHB Read Buffer RAM read address interface signals. 
// Enabling this register stage allows you to trade latency and gates for ease of timing closure.
`define DDRCTL_CHB_RDB_RAM_RD_ADDR_REG_OUT 0


// Name:         DDRCTL_CHB_RDB_RAM_RD_DATA_REG_IN
// Default:      0
// Values:       0, 1
// Enabled:      0
// 
// Register the CHB Read Buffer RAM read data interface signals. 
// Enabling this register stage allows you to trade latency and gates for ease of timing closure. 
//  Pipe register is implemented inside CHB
`define DDRCTL_CHB_RDB_RAM_RD_DATA_REG_IN 0


// Name:         DDRCTL_CHB_RDB_RAM_RD_REQ_INFO_REG_OUT
// Default:      0 ((DDRCTL_CHB_RDB_RAM_WR_LATENCY==1) ? 1 : 0)
// Values:       0, 1
// Enabled:      0
// 
// CHB Read Buffer RAM Demand Read Request Information Pipeline
`define DDRCTL_CHB_RDB_RAM_RD_REQ_INFO_REG_OUT 0


// Name:         DDRCTL_CHB_RDB_RAM_PREF_RD_REQ_INFO_REG_OUT
// Default:      0 ((DDRCTL_CHB_RDB_RAM_WR_LATENCY==1) ? 1 : 0)
// Values:       0, 1
// Enabled:      0
// 
// CHB Read Buffer RAM Prefetch Read Request Information Pipeline
`define DDRCTL_CHB_RDB_RAM_PREF_RD_REQ_INFO_REG_OUT 0


// Name:         DDRCTL_CHB_RRB_DIDMW
// Default:      2 (MEMC_BURST_LENGTH==32 ? DDRCTL_CHB_NUM_BEATS_BL32 : 
//               (MEMC_BURST_LENGTH==16 ? DDRCTL_CHB_NUM_BEATS_BL16 : DDRCTL_CHB_NUM_BEATS_BL8))
// Values:       -2147483648, ..., 2147483647
// 
// CHB Read Token "HIFBeatMask" field width. 
// The HIFBeatMask marks valid data beats within the HIF read data buffer. 
// The max number of HIF beats scales with the SDRAM burst length and DFI to core clock ratio.
`define DDRCTL_CHB_RRB_DIDMW 2


// Name:         DDRCTL_CHB_RRB_DIDAW
// Default:      2 (DDRCTL_CHB_DIDW)
// Values:       -2147483648, ..., 2147483647
// 
// CHB Read Token "DataIDAlgn" field width. 
// Width aligned to CHI Data ID width which scales with the cache line size
`define DDRCTL_CHB_RRB_DIDAW 2


// Name:         DDRCTL_CHB_RRB_NHIFBW
// Default:      3
// Values:       -2147483648, ..., 2147483647
// 
// CHB Read info Number of HIF bursts field width.
`define DDRCTL_CHB_RRB_NHIFBW 3


// Name:         USE_FOUNDATION
// Default:      0
// Values:       -2147483648, ..., 2147483647
// 
// USE_FOUNDATION 
// Enables usage of DW_minmax inside the TCRESP Arbiter
`define USE_FOUNDATION 0



// Name:         DDRCTL_CHB_MPAM_MBWWIN_STEPS
// Default:      4
// Values:       1 2 4 8 16
// 
// Number of steps of accounting window.
`define DDRCTL_CHB_MPAM_MBWWIN_STEPS 4


// Name:         DDRCTL_CHB_RT_RAM_ECC_EN
// Default:      0
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// DDRCTL_CHB_RT_RAM_ECC_EN 
//  
// Enables ECC protection of data stored in Retry-List RAM
`define DDRCTL_CHB_RT_RAM_ECC_EN 0


// Name:         DDRCTL_CHB_MPAM_HAS_NONSEC_PARTS
// Default:      1 ((DDRCTL_CHB_MPAM_NONSEC_PARTS>0) ? 1 : 0)
// Values:       0, 1
// Enabled:      0
// 
// MPAM has Non-Secure Partitions; defined only for DDRCTL_CHB_MPAM_NONSEC_PARTS>0
`define DDRCTL_CHB_MPAM_HAS_NONSEC_PARTS


// Name:         DDRCTL_CHB_MPAM_HAS_SEC_PARTS
// Default:      1 ((DDRCTL_CHB_MPAM_SEC_PARTS>0) ? 1 : 0)
// Values:       0, 1
// Enabled:      0
// 
// MPAM has Secure Partitions; defined only for DDRCTL_CHB_MPAM_SEC_PARTS>0
`define DDRCTL_CHB_MPAM_HAS_SEC_PARTS


// Name:         DDRCTL_CHB_MPAM_HAS_RT_PARTS
// Default:      1 ((DDRCTL_CHB_MPAM_RT_PARTS>0) ? 1 : 0)
// Values:       0, 1
// Enabled:      0
// 
// MPAM has Root Partitions; defined only for DDRCTL_CHB_MPAM_RT_PARTS>0
`define DDRCTL_CHB_MPAM_HAS_RT_PARTS


// Name:         DDRCTL_CHB_MPAM_HAS_RL_PARTS
// Default:      1 ((DDRCTL_CHB_MPAM_RL_PARTS>0) ? 1 : 0)
// Values:       0, 1
// Enabled:      0
// 
// DDRCTL_CHB_MPAM_HAS_REALM_PARTS: 
// MPAM has Realm Partitions; defined only for DDRCTL_CHB_MPAM_RL_PARTS>0
`define DDRCTL_CHB_MPAM_HAS_RL_PARTS



// Name:         DDRCTL_CHB_PARTIDW
// Default:      7 ((DDRCTL_CHB_MPAM_NONSEC_PARTS> 
//               DDRCTL_CHB_MPAM_SEC_PARTS)?[<functionof> [<functionof> DDRCTL_CHB_MPAM_NONSEC_PARTS]]:[<functionof> 
//               [<functionof> DDRCTL_CHB_MPAM_SEC_PARTS]])
// Values:       0, ..., 16
// Enabled:      0
// 
// PARTID width used by MBWC
`define DDRCTL_CHB_PARTIDW 7


// Name:         DDRCTL_CHB_RT_RAM_ECC_SEC
// Default:      1
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_RT_RAM_ECC_SEC 
//  
// Enables correction of single bit ECC errors found in Retry-List RAM
`define DDRCTL_CHB_RT_RAM_ECC_SEC 1


// Name:         DDRCTL_CHB_TXSACT_EN
// Default:      1
// Values:       0, 1
// 
// When '1' allows PCHBLCTRL.txsactive_en to control individual CHI Port's tx_scative output assertion 
//  - 0 : txsactive_en has no affect on tx_sactive assertion 
//  - 1 : 0 to 1 transition of PCHBLCTRL.txsactive_en necessary for tx_sactive assertion
`define DDRCTL_CHB_TXSACT_EN


// Name:         DDRCTL_CHB_RXREQ_DELAY_CYCLES
// Default:      0
// Values:       0 1
// 
// Number of delay cycles on input signals of RXREQ path.
`define DDRCTL_CHB_RXREQ_DELAY_CYCLES 0


// Name:         DDRCTL_CHB_RXDAT_DELAY_CYCLES
// Default:      0
// Values:       0 1
// 
// Number of delay cycles on input signals of RXDAT path.
`define DDRCTL_CHB_RXDAT_DELAY_CYCLES 0


// Name:         DDRCTL_CHB_TXDAT_DELAY_CYCLES
// Default:      1 ((DDRCTL_CHB_SYNC_MODE == 1) ? 0 : 1)
// Values:       0 1
// Enabled:      (DDRCTL_CHB_SYNC_MODE == 1) ? 1 : 0
// 
// Number of delay cycles on output signals of TXDAT path.
`define DDRCTL_CHB_TXDAT_DELAY_CYCLES 1


`define DDRCTL_CHB_TXDAT_DELAY_CYCLES_EN


// Name:         DDRCTL_CHB_TXRSP_DELAY_CYCLES
// Default:      1 ((DDRCTL_CHB_SYNC_MODE == 1) ? 0 : 1)
// Values:       0 1
// Enabled:      (DDRCTL_CHB_SYNC_MODE == 1) ? 1 : 0
// 
// Number of delay cycles on output signals of TXRSP path.
`define DDRCTL_CHB_TXRSP_DELAY_CYCLES 1


// Name:         DWC_DDRCTL_CHB_BEATTRK_EN
// Default:      0 (DDRCTL_CHB_DW < UMCTL2_A_DW)
// Values:       0 1
// Enabled:      DDRCTL_CHB_DW < UMCTL2_A_DW
// 
// Beat Tracker LUT enable for upsize configs.
// `define DWC_DDRCTL_CHB_BEATTRK_EN


// Name:         DDRCTL_CHB_PCLS_RETIME_EN
// Default:      0
// Values:       0, 1
// 
// When selected it adds a register retime/pipeline stage in DWC_ddrctl_chb_pclass module
`define DDRCTL_CHB_PCLS_RETIME_EN 0


// `define DDRCTL_CHB_PCLS_RETIME_EN_1


// Name:         DDRCTL_CHB_RT_RAM_RAW_DATA_WD
// Default:      19 (DDRCTL_CHB_NIDW + DDRCTL_CHB_NIDW + 4 + 1 + (DDRCTL_CHB_MPAM_EN 
//               * (DDRCTL_CHB_PARTIDW + DDRCTL_CHB_MPAM_NSW)) + 
//               (DDRCTL_CHB_MPAM_MON_EN ? 1 : 0))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Retry-list RAM data payload width.  
//  Sum of SrcID + TgtID + Qos + TraceTag + (MPAM_EN ? (mpam_partid + mpam_ns/mpamsp[0] (rme_en ? mpamsp[1]) + mpam_pmg) : 
//  0)
`define DDRCTL_CHB_RT_RAM_RAW_DATA_WD 19


// Name:         DDRCTL_CHB_RT_RAM_ECCW
// Default:      6 ((DDRCTL_CHB_RT_RAM_RAW_DATA_WD) <= 11  ? 5 : 
//               (DDRCTL_CHB_RT_RAM_RAW_DATA_WD) <= 26  ? 6 : (DDRCTL_CHB_RT_RAM_RAW_DATA_WD) <= 57  ? 7 
//               : (DDRCTL_CHB_RT_RAM_RAW_DATA_WD) <= 120 ? 8 :  9)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Retry-list RAM data width.  
// Includes protection bits, if on-chip ECC enabled.
`define DDRCTL_CHB_RT_RAM_ECCW 6


// Name:         DDRCTL_CHB_RT_RAM_DATA_WD
// Default:      19 (DDRCTL_CHB_RT_RAM_RAW_DATA_WD + (DDRCTL_CHB_RT_RAM_ECC_EN * 
//               DDRCTL_CHB_RT_RAM_ECCW))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// Specifies the CHB Retry-list RAM data interface width. 
//  includes ECC in when OCECC is enabled
`define DDRCTL_CHB_RT_RAM_DATA_WD 19


// Name:         DDRCTL_CHB_RT_RAM_WR_REG_OUT
// Default:      0
// Values:       0, 1
// Enabled:      (DDRCTL_CHB_RT_RAM_WR_LATENCY==1) ? 0 : 1
// 
// When enabled,Retrylist RAM Write interface is registered  
//  Registered outputs : ram_wr_en,ram_wr_addr,ram_wr_data 
//  Limitation : There can only be one pipe state on this interface 
//  If external pipe state is selected (DDRCTL_CHB_RT_RAM_WR_LATENCY==1), then this cannot be enabled
`define DDRCTL_CHB_RT_RAM_WR_REG_OUT 0


// Name:         DDRCTL_CHB_RT_RAM_WR_LATENCY
// Default:      0
// Values:       0 1
// Enabled:      0
// 
// Specifies the Retry-List RAM's write latency in core_clk cycles. 
// The write latency is defined at the CHB Retry-list RAM interface port and 
// sets the number of core clock cycles from CHB RAM write address/data valid, 
// chb_rt_ram_wr_[addr|data]_p*, to write address/data valid at the RAM write port.
`define DDRCTL_CHB_RT_RAM_WR_LATENCY 0


// Name:         DDRCTL_CHB_RT_RAM_RD_LATENCY
// Default:      1
// Values:       1 2
// Enabled:      0
// 
// Specifies the Retry-List RAM Wrapper read latency in core_clk cycles. 
// The read latency is defined at the CHB Retry-List RAM interface port and 
// sets the number of core clock cycles from RAM read address valid, 
// chb_rt_ram_rd_addr_p*, to RAM read data valid, chb_rt_ram_rd_data_p*.
`define DDRCTL_CHB_RT_RAM_RD_LATENCY 1


// Name:         DDRCTL_CHB_RT_RAM_RD_ADDR_REG_OUT
// Default:      1
// Values:       0, 1
// Enabled:      (DDRCTL_CHB_RT_RAM_WR_LATENCY==1 || 
//               DDRCTL_CHB_RT_RAM_WR_REG_OUT==1) ? 0 : 1
// 
// DDRCTL_CHB_RTRAM_WADR_REG: 
// When enabled,Retrylist RAM Read interface is registered  
//   Registered outputs : ram_rd_en,ram_rd_addr 
//   Defaulted to 1 to handle critical path from rxreq flitq to rt_ram_rd_addr 
//   Should be set if rt_ram's wr latency is 1 ore RT_RAM_WR_REG_OUT is 1
`define DDRCTL_CHB_RT_RAM_RD_ADDR_REG_OUT 1


// Name:         DDRCTL_CHB_RT_RAM_RD_DATA_REG_IN
// Default:      0
// Values:       0, 1
// 
// When enabled, Retrylist RAM Read data is registered inside CHB  
//   Registered input : ram_rd_data 
//  Pipe register is implemented inside CHB
`define DDRCTL_CHB_RT_RAM_RD_DATA_REG_IN 0
 

// Name:         DDRCTL_CHB_PSTORE_RETIME_RT_GRANT
// Default:      0
// Values:       0, 1
// 
// When enabled, the output of Retrylist Grant Arbiter is registered  
//   Registered output : grant
`define DDRCTL_CHB_PSTORE_RETIME_RT_GRANT 0


// Name:         DDRCTL_CHB_PRC_TIMER_MAX_DIV
// Default:      64
// Values:       -2147483648, ..., 2147483647
// 
// Max value of PRC_REC_ENTRY timer divider
`define DDRCTL_CHB_PRC_TIMER_MAX_DIV 64

//`define DDRCTL_CHB_LAT_TIMER_WIDTH 11



// Name:         DDRCTL_CHB_LAT_ERROR_MARGIN
// Default:      8
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_LAT_ERROR_MARGIN 
// Number of periods that add up to the latency interval
`define DDRCTL_CHB_LAT_ERROR_MARGIN 8


// Name:         DDRCTL_CHB_NUM_TMR_GROUPS
// Default:      2
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_NUM_TMR_GROUPS 
// Number of VP timer groups
`define DDRCTL_CHB_NUM_TMR_GROUPS 2


// Name:         DDRCTL_CHB_DMT_EXT
// Default:      0
// Values:       0, 1
// Enabled:      DDRCTL_HAS_CHB
// 
// DDRCTL_CHB_DMT_EXT 
// Enable CHI DMT Extension
// `define DDRCTL_CHB_DMT_EXT


// Name:         DDRCTL_CHB_OPT_WPQ_RDY
// Default:      0
// Values:       0, 1
// Enabled:      DDRCTL_HAS_CHB
// 
// DDRCTL_CHB_OPT_WPQ_RDY 
// Enable DataID based REQ ADDR update
// `define DDRCTL_CHB_OPT_WPQ_RDY


// Name:         DDRCTL_CHB_MAX_DATFLITS
// Default:      2 ((DDRCTL_CHB_XFRSZ*8)/DDRCTL_CHB_DW)
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// DDRCTL_CHB_MAX_DATFLITS 
// Max number of RxDAT or TxDAT flits possible per CHI request
`define DDRCTL_CHB_MAX_DATFLITS 2



// Name:         DDRCTL_CHB_WPQ_PCMO_DP
// Default:      4
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_WPQ_PCMO_DP 
// Set aside additional depth for PMCO req in WPQ
`define DDRCTL_CHB_WPQ_PCMO_DP 4


// Name:         DDRCTL_CHB_WR_PROTQ_EXTRA_DP
// Default:      12 (DDRCTL_CHB_WPQ_PCMO_DP + DDRCTL_CHB_WRB_DBID_RLS_LAT)
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_WR_PROTQ_EXTRA_DP 
//  Total WPQ additional/Extra depth needed apart from user setting
`define DDRCTL_CHB_WR_PROTQ_EXTRA_DP 12


// Name:         DDRCTL_CHB_NUM_DBID
// Default:      76 (DDRCTL_CHB_WR_PROTQ_SIZE+DDRCTL_CHB_WR_PROTQ_EXTRA_DP)
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_NUM_DBID 
//  Number of unique DBID values needed
`define DDRCTL_CHB_NUM_DBID 76


// Name:         DDRCTL_CHB_INT_DBIDW
// Default:      7 ([ <functionof> DDRCTL_CHB_NUM_DBID])
// Values:       -2147483648, ..., 2147483647
// 
// DDRCTL_CHB_INT_DBIDW 
// DBIDW width for internal wiring ($clog2(WR_PROTQ_SIZE+EXTRA_DP))
`define DDRCTL_CHB_INT_DBIDW 7


// Name:         DDRCTL_CHB_PCLS_OVER_RT
// Default:      0
// Values:       0, 1
// Enabled:      0
// 
// DDRCTL_CHB_PCLS_OVER_RT 
// When true, Pclass request has higher priority as compared to Retry-list req on a given cycle 
// Needed for internal testing purpose.
// `define DDRCTL_CHB_PCLS_OVER_RT


// Name:         DDRCTL_VALID_CHI_ADDRW
// Default:      35 ( MEMC_HIF_ADDR_WIDTH + MEMC_DRAM_NBYTES_LG2 )
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// DDRCTL_VALID_CHI_ADDRW 
// Number of valid bits of CHI address considering DRAM DW
`define DDRCTL_VALID_CHI_ADDRW 35


// Name:         DDRCTL_CHB_DWT_EN
// Default:      0 (DDRCTL_CHB_CHIE_EN)
// Values:       0, 1
// Enabled:      DDRCTL_CHB_CHIE_EN
// 
// DDRCTL_CHB_DWT_EN 
// CHB Direct Write-data Transfer Enable
// `define DDRCTL_CHB_DWT_EN


// Name:         DDRCTL_CHB_MTE_EN
// Default:      0 (DDRCTL_CHB_CHIE_EN)
// Values:       0, 1
// Enabled:      DDRCTL_CHB_CHIE_EN
// 
// DDRCTL_CHB_MTE_EN 
// CHB MTE Enable
// `define DDRCTL_CHB_MTE_EN


// Name:         DDRCTL_MAX_CHI_CLK_RATIO
// Default:      16
// Values:       4 8 16 32
// 
// defines the max clock freq difference between CHI clock and Core clock 
// This is used by debounce counter running in chi_clk domain in chb_link_rx block
`define DDRCTL_MAX_CHI_CLK_RATIO 16


// Name:         DDRCTL_CHB_RETIME_WPQ_IN
// Default:      1
// Values:       0, 1
// 
// Enables retime state at WPQ input. 
// Since store and forward mode is used this does not add any addition latency on write request path
`define DDRCTL_CHB_RETIME_WPQ_IN


// Name:         DDRCTL_CHB_WR_TOKENMGR_REG_EN
// Default:      1
// Values:       0, 1
// Enabled:      0
// 
// Enable register stage on tokengr arb to improve timing
`define DDRCTL_CHB_WR_TOKENMGR_REG_EN 1


// Name:         DDRCTL_CHB_RD_TOKENMGR_REG_EN
// Default:      0
// Values:       0, 1
// Enabled:      0
// 
// Enable register stage on tokengr arb to improve timing
`define DDRCTL_CHB_RD_TOKENMGR_REG_EN 0


// Name:         DDRCTL_CHB_RRB_CBGINFOW
// Default:      2 (DDRCTL_CHB_NUM_BEATS_BL * (DDRCTL_CHB_PREFETCH_EN + 
//               MEMC_ADDR_ERR_EN))
// Values:       -2147483648, ..., 2147483647
// Enabled:      0
// 
// DDRCTL_CHB_RRB_CBGINFOW is used define the width of info bus that connects wif to cbg
`define DDRCTL_CHB_RRB_CBGINFOW 2


`define DDRCTL_CHB_MPAM_SPACES 2


`define DDRCTL_CHB_MPAM_NS 0


`define DDRCTL_CHB_MPAM_S 1


`define DDRCTL_CHB_MPAM_RT 2


`define DDRCTL_CHB_MPAM_RL 3


`define MPAM_MMR_RDATA_OP_REG 0


// `define MPAM_MMR_RDATA_OP_REG_1


`define DDRCTL_CCX_RXREQ_ENDVLD_START 33


`define DDRCTL_CCX_RXREQ_ENDVLD_END 33


`define DDRCTL_CCX_RXREQ_LIKELY_SHARED_START 96


`define DDRCTL_CCX_RXREQ_LIKELY_SHARED_END 96


`define DDRCTL_CCX_RXREQ_ADDR_START 92


`define DDRCTL_CCX_RXREQ_ADDR_END 94


`define DDRCTL_CCX_RXREQ_TAG_OP_START 0


`define DDRCTL_CCX_RXREQ_TAG_OP_END 0


`define DDRCTL_CCX_RXREQ_ORDER_START 99


`define DDRCTL_CCX_RXREQ_ORDER_END 99


`define DDRCTL_CCX_RXREQ_MEM_ATTR_START 105


`define DDRCTL_CCX_RXREQ_MEM_ATTR_END 105


`define DDRCTL_CCX_RXREQ_XSNP_START 114


`define DDRCTL_CCX_RXREQ_XSNP_END 114


`define DDRCTL_CCX_RXREQ_EXP_COMP_ACK_START 115


`define DDRCTL_CCX_RXREQ_EXP_COMP_ACK_END 115


`define DDRCTL_CCX_TXDAT_RESP_0_START 39


`define DDRCTL_CCX_TXDAT_RESP_0_END 39


`define DDRCTL_CCX_TXDAT_RESP_2_START 41


`define DDRCTL_CCX_TXDAT_RESP_2_END 41


`define DDRCTL_CCX_TXDAT_DSRC_START 45


`define DDRCTL_CCX_TXDAT_DSRC_END 45


`define DDRCTL_CCX_TXDAT_CBUSY_START 0


`define DDRCTL_CCX_TXDAT_CBUSY_END 0


`define DDRCTL_CCX_TXDAT_DATA_ID_START 56


`define DDRCTL_CCX_TXDAT_DATA_ID_END 56


`define DDRCTL_CCX_TXDAT_TAG_OP_START 0


`define DDRCTL_CCX_TXDAT_TAG_OP_END 0


`define DDRCTL_CCX_TXDAT_TAG_START 0


`define DDRCTL_CCX_TXDAT_TAG_END 0


`define DDRCTL_CCX_TXDAT_TU_START 0


`define DDRCTL_CCX_TXDAT_TU_END 0


`define DDRCTL_CCX_TXDAT_BE_START 59


`define DDRCTL_CCX_TXDAT_BE_END 90


`define DDRCTL_CCX_RXDAT_TXN_ID_START 25


`define DDRCTL_CCX_RXDAT_TXN_ID_END 29


`define DDRCTL_CCX_RXDAT_HOME_NID_START 26


`define DDRCTL_CCX_RXDAT_HOME_NID_END 32


`define DDRCTL_CCX_RXDAT_OPCODE_START 36


`define DDRCTL_CCX_RXDAT_OPCODE_END 36


`define DDRCTL_CCX_RXDAT_RESP_START 39


`define DDRCTL_CCX_RXDAT_RESP_END 41


`define DDRCTL_CCX_RXDAT_DSRC_START 42


`define DDRCTL_CCX_RXDAT_DSRC_END 45


`define DDRCTL_CCX_RXDAT_CBUSY_START 0


`define DDRCTL_CCX_RXDAT_CBUSY_END 0


`define DDRCTL_CCX_RXDAT_DATA_ID_START 56


`define DDRCTL_CCX_RXDAT_DATA_ID_END 56


`define DDRCTL_CCX_RXDAT_TAG_OP_START 0


`define DDRCTL_CCX_RXDAT_TAG_OP_END 0


`define DDRCTL_CCX_RXDAT_TAG_START 0


`define DDRCTL_CCX_RXDAT_TAG_END 0


`define DDRCTL_CCX_RXDAT_TU_START 0


`define DDRCTL_CCX_RXDAT_TU_END 0


`define DDRCTL_CCX_TXRSP_OPCODE_START 30


`define DDRCTL_CCX_TXRSP_OPCODE_END 30


`define DDRCTL_CCX_TXRSP_RESP_ERR_START 30


`define DDRCTL_CCX_TXRSP_RESP_ERR_END 31


`define DDRCTL_CCX_TXRSP_RESP_START 32


`define DDRCTL_CCX_TXRSP_RESP_END 34


`define DDRCTL_CCX_TXRSP_FS_DP_START 35


`define DDRCTL_CCX_TXRSP_FS_DP_END 37


`define DDRCTL_CCX_TXRSP_CBUSY_START 0


`define DDRCTL_CCX_TXRSP_CBUSY_END 0


`define DDRCTL_CCX_TXRSP_DBID_START 45


`define DDRCTL_CCX_TXRSP_DBID_END 45


`define DDRCTL_CCX_TXRSP_PCRD_TYPE_START 48


`define DDRCTL_CCX_TXRSP_PCRD_TYPE_END 49


`define DDRCTL_CCX_TXRSP_TAG_OP_START 0


`define DDRCTL_CCX_TXRSP_TAG_OP_END 0


`define DDRCTL_CCX_RAM_WR_DATA_START 12


`define DDRCTL_CCX_RAM_WR_DATA_END 18


`define DDRCTL_CCX_RAM_RD_DATA_START 12


`define DDRCTL_CCX_RAM_RD_DATA_END 18

`endif  // __GUARD__DWC_DDRCTL_CHB_CC_CONSTANTS__SVH__
