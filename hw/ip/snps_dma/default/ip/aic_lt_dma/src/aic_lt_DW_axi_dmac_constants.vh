/*
--------------------------------------------------------------------------
// ------------------------------------------------------------------------------
// 
// Copyright 2013 - 2024 Synopsys, INC.
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
// Component Name   : DW_axi_dmac
// Component Version: 2.03a
// Release Type     : GA
// Build ID         : 39.65.47.15
// ------------------------------------------------------------------------------

// 
// Release version :  2.03a
// Revision: $Id: //dwh/DW_ocb/DW_axi_dmac/amba_sfty_dev_br/src/DW_axi_dmac_constants.vh#11 $ 
//
-- File :                       DW_axi_dmac_constants.vh
-- Abstract     :               DW_axi_dmac constants file
--------------------------------------------------------------------------

*/

//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`ifndef AIC_LT___GUARD__DW_AXI_DMAC_CONSTANTS__VH__
`define AIC_LT___GUARD__DW_AXI_DMAC_CONSTANTS__VH__

// DMAC_MDATA_WIDTH Encoded in terms to TR WIDTH

`define AIC_LT_DMAX_HAS_M_DATA_WIDTH_ENC 3'h3

// DMAX_M_DATA_WIDTH>32 define
`define AIC_LT_DMAX_HAS_M_DATA_WIDTH_32_ABOVE

// DMAX_M_DATA_WIDTH>64 define

// DMAX_M_DATA_WIDTH>128 define

// DMAX_M_DATA_WIDTH>256 define

// DMAX_M_DATA_WIDTH>512 define

`define AIC_LT_DMAX_HAS_BURSTLEN_GT_16BEATS

`define AIC_LT_DMAX_HAS_BURSTLEN_GT_32BEATS

`define AIC_LT_DMAX_HAS_BURSTLEN_GT_64BEATS

`define AIC_LT_DMAX_HAS_BURSTLEN_GT_128BEATS

//DMAC Has DMAX_INTR_SYNC2SLVCLK define

// DMAC has interrupt polarity high define
`define AIC_LT_DMAX_HAS_INTR_POL_HIGH

//Burst Length to be used in order to fetch LLI

`define AIC_LT_DMAX_BURST_LEN_LLI_FETCH 5

//LLI Auto Resume Request Enable

//DMAC has 1 channel
`define AIC_LT_DMAX_HAS_1_CHANNEL

//DMAC has more than 1 channel

//DMAC has more than 8 channels

//DMAC has more than 16 channels

//Include Virtual Machine ID Feature define

//Reorganize Channel Priority Field define



//Reorganize the Channel Enable fields define


//DMAC has LLI Define
`define AIC_LT_DMAX_HAS_LLI

`define AIC_LT_DMAX_HAS_CH1_LLI
































//DMAC has AXI4 interface Define
`define AIC_LT_DMAX_HAS_MSTIF_MODE_AXI4

//DMAC has AXI3 interface Define

//DMAC has QOS Define

//DMAC has Debug Ports Define 
`define AIC_LT_DMAX_HAS_DEBUG_PORTS

//AXI DMAC has CRC support - DMAX_CHx_CRC_EN=1 for at least 1 channel


`define AIC_LT_DMAX_CRC_EN 0

//Set this parameter to 1 to register the data before CRC calculation
//This breaks the timing path between data shifting logic and CRC engine

`define AIC_LT_DMAX_CRC_DATA_RS 0




`define AIC_LT_DMAX_8BIT_CRC1_EN 1

`define AIC_LT_DMAX_8BIT_CRC2_EN 0

`define AIC_LT_DMAX_16BIT_CRC1_EN 0

`define AIC_LT_DMAX_16BIT_CRC2_EN 0

`define AIC_LT_DMAX_32BIT_CRC1_EN 0

`define AIC_LT_DMAX_32BIT_CRC2_EN 0

`define AIC_LT_DMAX_64BIT_CRC_EN 0

`define AIC_LT_DMAX_MIN_CRC_POLYNOMIAL 3'h0

//DMAC has Master 2 interface Define

//Define to tell if Master Interface 1 clock is Asynchronous with Core Clock

//Define to tell if Master Interface 2 clock is Asynchronous with Core Clock

`define AIC_LT_DMAX_HAS_OPT_TIMING

//DMAC has more than 24 channels

//DMAC has more than 8 or 16 channels

//Define for DMAC Handshake interface (Used in TB)







































































`define AIC_LT_DMAX_HAS_LLI_AXCTRL

`define AIC_LT_DMAX_HAS_CKG_OPT_UPDT

`define AIC_LT_DMAX_HAS_STATUSREG_UPDT

//Define to indicate Slave Interface clock is synchronous or Parity Protection is enabled
`define AIC_LT_DMAX_HAS_WUID_OR_STATUREGUPDT




// Name:         DMAX_S_ADDR_WIDTH
// Default:      32
// Values:       -2147483648, ..., 2147483647
// 
// Slave AHB address Width
`define AIC_LT_DMAX_S_ADDR_WIDTH 32

//Slave Data Width 32 Define

//Safety Feature Enable

//Advanced Safety Feature Enable

//Manager Interface Safety Soft Reset Enable

//Advanced Safety Feature Error Injection Enable


`define AIC_LT_TIMEOUT_CNT_WIDTH 8

//Correctable Errors define

//Correctable Errors define

//Slave Data Parity Check Enable?

//Define to indicate Slave Interface clock is synchronous or Parity Protection is enabled
`define AIC_LT_DMAX_HAS_SLVIFSYNC_OR_PARPROT_EN

//The Parity Check is done after a Pipeline stage?


//ECC protection Enable?

//ECC protection Enable - FIFO Memory Interface?

//ECC protection Enable - UID Memory Interface?

//ECC protection Enable - Channel or UID Memory Interface?

//ECC protection Enable - AXI Interface?

//ECC and Parity protection Enable - AXI Interface?




`define AIC_LT_DMAX_HAS_ECC_MODE_1

`define AIC_LT_DMAX_HAS_ECC_MODE_1_2


`define AIC_LT_MXIF_VLD_RDY_ERRINTR_WIDTH 5


`define AIC_LT_MXIF_TIMEOUT_ERRINTR_WIDTH 5

//Include ECC additional diagnostic features?



//Lock Step Enable?

//Lock Step Diagnostic Feature Enable?


//Include SVA assertions



`define AIC_LT_DMAX_SFTY_ERR_INJ_CTRL_RS 23


`define AIC_LT_DMAX_DELAY_COUNT 2

//Define for Hold interface IO signals or Safety Feature enabled



`define AIC_LT_DMAX_HAS_DBGIF_IN_ENABLED 

//Enable Unaligned Transfer Support Define
`define AIC_LT_DMAX_HAS_UNALIGNED_XFER_EN


`define AIC_LT_DMAX_UNALIGNED_DFC_XFER 1
// `define AIC_LT_DMAX_UNALIGNED_DFC_XFER 0

//Enable Unaligned Transfer Support Define
`define AIC_LT_DMAX_HAS_UNALIGNED_DFC_XFER

//Enable Context Sensitive Low Power Feature define
`define AIC_LT_DMAX_HAS_CSLP_EN

//Enable DMA Channel Context Sensitive Low Power Feature define
`define AIC_LT_DMAX_HAS_CHNL_CSLP_EN


//Enable SBIU Context Sensitive Low Power Feature define
`define AIC_LT_DMAX_HAS_SBIU_CSLP_EN

//Enable AXI Channel Context Sensitive Low Power Feature define
`define AIC_LT_DMAX_HAS_MXIF_CSLP_EN




// AXI signal Widths
`define AIC_LT_DMAX_AXI_PROT_WIDTH          3
`define AIC_LT_DMAX_AXI_CACHE_WIDTH         4
`define AIC_LT_DMAX_AXI_SIZE_WIDTH          3
`define AIC_LT_DMAX_AXI_QOS_WIDTH           4

// Write Strobe width

`define AIC_LT_DMAX_AXI_WSTRB_WIDTH 8


`define AIC_LT_LOG2_NUM_BYTES_WIDTH 4


`define AIC_LT_DMAX_AXI_LOCK_WIDTH 1

//AXI DMAC VM ID suffix width

`define AIC_LT_DMAX_VMID_SUFFIX_WIDTH 4


`define AIC_LT_DMAX_VMID_SUFFIX_WIDTH_WUID_EN 4


`define AIC_LT_DMAX_VMID_SUFFIX_WIDTH_RUID_EN 4

//AXI DMAC ID suffix width

`define AIC_LT_DMAX_AXI_ID_SUFFIX_WIDTH 4

//AXI DMAC has ID suffix
`define AIC_LT_DMAX_HAS_ID_SUFFIX

//AXI DMAC has Last Write Feature

//AXI DMAC has Static Endianness
`define AIC_LT_DMAX_HAS_STATIC_ENDIAN_SELECT_MSTIF

//AXI DMAC has Dynamic Endianness

//AXI DMAC has LLI Endian Selection Pin

//AXI DMAC has Core Status Output

// Master Address FIFO Address width Log2( DMAX_M_ADDR_FIFO_DEPTH)

`define AIC_LT_DMAX_M_ADDR_FIFO_ADDR_WIDTH 2

// Master Address FIFO Address width Log2( DMAX_M_DATA_FIFO_DEPTH)

`define AIC_LT_DMAX_M_DATA_FIFO_ADDR_WIDTH 2

// Master Address FIFO Address width Log2( DMAX_M_DATA_FIFO_DEPTH)

`define AIC_LT_DMAX_M_BRESP_FIFO_ADDR_WIDTH 2


//Master Interface Read Address FIFO Width

`define AIC_LT_MSTIF_AR_FIFO_WIDTH 52

//Master Interface Write Address FIFO Width

`define AIC_LT_MSTIF_AW_FIFO_WIDTH 54

//Master Interface Write Data FIFO Width

`define AIC_LT_MSTIF_WDATA_FIFO_WIDTH 75

//Master Interface Read Data FIFO Width

`define AIC_LT_MSTIF_RDATA_FIFO_WIDTH 69

//Master Interface Write Response FIFO Width

`define AIC_LT_MSTIF_WRESP_FIFO_WIDTH 4


//Signal Widths used for Register interface
`define AIC_LT_DMAX_MLTBLK_TFR_WIDTH        2


`define AIC_LT_DMAX_HAS_UID_OR_UNALIGN

`define AIC_LT_DMAX_OSR_LMT_WIDTH           4

`define AIC_LT_DMAX_CH_PRIORITY_WIDTH 3
`define AIC_LT_DMAX_TFR_TYPE_WIDTH          3


`define AIC_LT_DMAX_M_DATA_WIDTH_SIZE 3

// Maximum Source Transfer width based on DMAX_M_DATA_WIDTH

`define AIC_LT_DMAX_MAX_TR_WIDTH 3


`define AIC_LT_DMAX_REG_INCR_VALUE_WIDTH    16
`define AIC_LT_DMAX_CMPLT_BLK_TFR_WIDTH     22
`define AIC_LT_DMAX_DATA_LEFT_FIFO_WIDTH    15
`define AIC_LT_DMAX_MSIZE_WIDTH 4
`define AIC_LT_CH_LLI_LOC_ADDR_WIDTH  58

// AHB Signal Widths
// hsize width
`define AIC_LT_DMAX_S_AHB_SIZE_WIDTH  3
// htrans width
`define AIC_LT_DMAX_S_AHB_TRANS_WIDTH 2
// hresp width
`define AIC_LT_DMAX_S_ERR_WIDTH       2

// Data Strobe width Slave interface DMAX_REG_DATA_WIDTH/8
`define AIC_LT_DMAX_S_BYTE_WIDTH 8

//Register Data width

`define AIC_LT_DMAX_REG_DATA_WIDTH 64

//Interrupt status register Data width

`define AIC_LT_DMAX_INTSTATUSREG_WIDTH 16

//Number of register Blocks
`define AIC_LT_DMAX_NUM_REG_BLOCKS (`AIC_LT_DMAX_NUM_CHANNELS + 1)

// Slave bus Interface Defines  

`define AIC_LT_REG_ADDR_SLICE 9

`define AIC_LT_REG_SLICE_LHS 11
`define AIC_LT_REG_SLICE_RHS 3


//Define to tell if Slave interface is AHB
`define AIC_LT_DMAX_HAS_SLVIF_AHB

//Define to tell if Slave interface is APB4

//Log2(DMAX_MSTIF1_OSR_LMT) 

`define AIC_LT_LOG2_DMAX_MSTIF1_OSR_LMT 4

//Log2(DMAX_MSTIF2_OSR_LMT) 

`define AIC_LT_LOG2_DMAX_MSTIF2_OSR_LMT 4

//Log2(DMAX_S_DATA_WIDTH) 

`define AIC_LT_LOG2_DMAX_S_DATA_WIDTH 6

//LOG2 DMAX_NUM_HS_IF

`define AIC_LT_LOG2_DMAX_NUM_HS_IF 1

//Source and Destination peripherial bit width

`define AIC_LT_DMAX_PER_WIDTH 4

//dst_per_i and src_per_i signal width in handshaking interfac

`define AIC_LT_DMAX_CH_PER_WIDTH 4


//Define to tell if Slave Interface clock is Asynchronous with Core Clock

//Define for Common Interrupt
`define AIC_LT_DMAX_HAS_INTR_CH_AND_CMN

//Define for Combined interrupt

//Define for Seperate safety Interrupt

//Define for Combined Safety Interrupt
`define AIC_LT_DMAX_HAS_COMBINED_SFTY_INTR

//Define for Slave Status OP Enable

//Define for Channel Abort Feature

//Define for Debug Registers 

//Define for Encoding Parameters in Register 

//Define for Hold interface IO signals

//Read data bus width from all channel and common register
`define AIC_LT_DMAX_REG_RD_WIDTH ((`AIC_LT_DMAX_NUM_CHANNELS+1)*`AIC_LT_DMAX_REG_DATA_WIDTH)

// DMAX_NUM_CHANNELS *3

`define AIC_LT_DMAX_NUM_CHANNELS_MUL_3 3

//Log 2 3*@DMAX_NUM_CHANNELS

`define AIC_LT_LOG2_3_DMAX_NUM_CHANNELS 2

//Log 2 2*@DMAX_NUM_CHANNELS

`define AIC_LT_LOG2_2_DMAX_NUM_CHANNELS 2

//Log 2 Arbiter Read Request Width

`define AIC_LT_LOG2_DMAX_ARB_RD_REQ_WIDTH 2

//Log 2 Arbiter Write Request Width

`define AIC_LT_LOG2_DMAX_ARB_WR_REQ_WIDTH 2

//Channel Address slice width
//Depending on the DMAX_M_DATA_WIDTH we derive the value
//for write strobes generation

`define AIC_LT_DMAX_M_ADDR_SLICE_WIDTH 3

// Read Address Channel control information for a block - Width 
//Depending on the following : 
// - Source Address - ARADDR bits = 7 (to support 128 bytes)

`define AIC_LT_DMAX_ARCTL_ADDR_WIDTH 8

// Write Address Channel control information for a block - Width 
//Depending on the following : 
// - Destination Address - AWADDR bits = 7 (to support 128 bytes)

`define AIC_LT_DMAX_AWCTL_ADDR_WIDTH 8

//Use External and Top level Channel FIFO memory
`define AIC_LT_DMAX_HAS_CH_MEM_EXT

`define AIC_LT_DMAX_HAS_FIFO_UID_MEM_EXT

//Use External Channel FIFO memory
`define AIC_LT_DMAX_HAS_MEM_EXT

//Use Top Level Channel FIFO memory

//Add Pipeline Register for read data of Channel FIFO memory
`define AIC_LT_DMAX_HAS_CH_MEM_REGOUT

//Channel 1 FIFO Depth

`define AIC_LT_DMAX_CH1_FIFO_WIDTH 64

//Channel 1 FIFO Width Encoded Value

`define AIC_LT_DMAX_CH1_FIFO_WIDTH_ENC 3'h3

//Log2(DMAX_CH1_FIFO_WIDTH)

`define AIC_LT_LOG2_DMAX_CH1_FIFO_WIDTH 6

//Log2(DMAX_CH1_FIFO_DEPTH)

`define AIC_LT_LOG2_DMAX_CH1_FIFO_DEPTH 7


//Channel 1 STW Encoded Value

`define AIC_LT_DMAX_CH1_STW_ENC 4'h3

//Channel 1 DTW Encoded Value

`define AIC_LT_DMAX_CH1_DTW_ENC 4'h3

//Channel 1 MAX MSIZE Encoded Value

`define AIC_LT_DMAX_CH1_MAX_MSIZE_ENC 4'h7

//Channel 1 FIFO level Width
`define AIC_LT_CH1_FIFO_LEVEL_WIDTH ( (`AIC_LT_LOG2_DMAX_CH1_FIFO_DEPTH+`AIC_LT_LOG2_DMAX_CH1_FIFO_WIDTH -2) > (`AIC_LT_DMAX_M_BURSTLEN_WIDTH+8) ? (`AIC_LT_LOG2_DMAX_CH1_FIFO_DEPTH+`AIC_LT_LOG2_DMAX_CH1_FIFO_WIDTH -2) : (`AIC_LT_DMAX_M_BURSTLEN_WIDTH+8) ) 


//Define for channel 2


//Define for channel 3


//Define for channel 4


//Define for channel 5


//Define for channel 6


//Define for channel 7


//Define for channel 8


//Define for channel 9


//Define for channel 10


//Define for channel 11


//Define for channel 12


//Define for channel 13


//Define for channel 14


//Define for channel 15


//Define for channel 16


//Define for channel 17


//Define for channel 18


//Define for channel 19


//Define for channel 20


//Define for channel 21


//Define for channel 22


//Define for channel 23


//Define for channel 24


//Define for channel 25


//Define for channel 26


//Define for channel 27


//Define for channel 28


//Define for channel 29


//Define for channel 30


//Define for channel 31


//Define for channel 32


//Channel FIFO Level BUS signal Width
`define AIC_LT_FIFO_LEVEL_BUS_WIDTH `AIC_LT_CH1_FIFO_LEVEL_WIDTH 


//Default Channel Priority Value
`define AIC_LT_CH_PRIOR_DEF_VAL 1'h0 

//Default Virtual Machine ID Value
`define AIC_LT_VM_ID_DEF_VAL 0 

// BCM Constants
`define AIC_LT_DWC_NO_TST_MODE

`define AIC_LT_DWC_NO_CDC_INIT

`define AIC_LT_DWC_BCM06_NO_DIAG_N


// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-1

`define AIC_LT_DMAX_CH1_EXTMEM_DATA_WIDTH 64

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-2

`define AIC_LT_DMAX_CH2_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-3

`define AIC_LT_DMAX_CH3_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-4

`define AIC_LT_DMAX_CH4_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-5

`define AIC_LT_DMAX_CH5_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-6

`define AIC_LT_DMAX_CH6_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-7

`define AIC_LT_DMAX_CH7_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-8

`define AIC_LT_DMAX_CH8_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-9

`define AIC_LT_DMAX_CH9_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-10

`define AIC_LT_DMAX_CH10_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-11

`define AIC_LT_DMAX_CH11_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-12

`define AIC_LT_DMAX_CH12_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-13

`define AIC_LT_DMAX_CH13_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-14

`define AIC_LT_DMAX_CH14_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-15

`define AIC_LT_DMAX_CH15_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-16

`define AIC_LT_DMAX_CH16_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-17

`define AIC_LT_DMAX_CH17_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-18

`define AIC_LT_DMAX_CH18_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-19

`define AIC_LT_DMAX_CH19_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-20

`define AIC_LT_DMAX_CH20_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-21

`define AIC_LT_DMAX_CH21_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-22

`define AIC_LT_DMAX_CH22_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-23

`define AIC_LT_DMAX_CH23_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-24

`define AIC_LT_DMAX_CH24_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-25

`define AIC_LT_DMAX_CH25_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-26

`define AIC_LT_DMAX_CH26_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-27

`define AIC_LT_DMAX_CH27_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-28

`define AIC_LT_DMAX_CH28_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-29

`define AIC_LT_DMAX_CH29_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-30

`define AIC_LT_DMAX_CH30_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-31

`define AIC_LT_DMAX_CH31_EXTMEM_DATA_WIDTH 32

// Channel FIFO Data + ECC (if ECC is enabled) bit width for Channel-32

`define AIC_LT_DMAX_CH32_EXTMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-1

`define AIC_LT_DMAX_CH1_UIDMEM_DATA_WIDTH 64

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-2

`define AIC_LT_DMAX_CH2_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-3

`define AIC_LT_DMAX_CH3_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-4

`define AIC_LT_DMAX_CH4_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-5

`define AIC_LT_DMAX_CH5_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-6

`define AIC_LT_DMAX_CH6_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-7

`define AIC_LT_DMAX_CH7_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-8

`define AIC_LT_DMAX_CH8_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-9

`define AIC_LT_DMAX_CH9_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-10

`define AIC_LT_DMAX_CH10_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-11

`define AIC_LT_DMAX_CH11_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-12

`define AIC_LT_DMAX_CH12_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-13

`define AIC_LT_DMAX_CH13_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-14

`define AIC_LT_DMAX_CH14_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-15

`define AIC_LT_DMAX_CH15_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-16

`define AIC_LT_DMAX_CH16_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-17

`define AIC_LT_DMAX_CH17_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-18

`define AIC_LT_DMAX_CH18_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-19

`define AIC_LT_DMAX_CH19_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-20

`define AIC_LT_DMAX_CH20_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-21

`define AIC_LT_DMAX_CH21_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-22

`define AIC_LT_DMAX_CH22_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-23

`define AIC_LT_DMAX_CH23_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-24

`define AIC_LT_DMAX_CH24_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-25

`define AIC_LT_DMAX_CH25_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-26

`define AIC_LT_DMAX_CH26_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-27

`define AIC_LT_DMAX_CH27_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-28

`define AIC_LT_DMAX_CH28_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-29

`define AIC_LT_DMAX_CH29_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-30

`define AIC_LT_DMAX_CH30_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-31

`define AIC_LT_DMAX_CH31_UIDMEM_DATA_WIDTH 32

//Re-ordering Buffer Data + ECC (if ECC is enabled) bit width for Channel-32

`define AIC_LT_DMAX_CH32_UIDMEM_DATA_WIDTH 32


`define AIC_LT_DMAX_HWHS_BUSIN_WIDTH 0


`define AIC_LT_DMAX_SBIU_BUSIN_WIDTH 104


`define AIC_LT_DMAX_DBGIF_BUSIN_WIDTH 1


`define AIC_LT_DMAX_MXIF1_BUSIN_WIDTH 86


`define AIC_LT_DMAX_MXIF2_BUSIN_WIDTH 86


`define AIC_LT_DMAX_CHMEM1_BUSIN_WIDTH 64

































`define AIC_LT_DMAX_HWHS_BUSOUT_WIDTH 0


`define AIC_LT_DMAX_SBIU_BUSOUT_WIDTH 67


`define AIC_LT_DMAX_STATUSIF_BUSOUT_WIDTH 0


`define AIC_LT_DMAX_MXIF1_BUSOUT_WIDTH 212


`define AIC_LT_DMAX_MXIF2_BUSOUT_WIDTH 212


`define AIC_LT_DMAX_INTR_BUSOUT_WIDTH 2


`define AIC_LT_DMAX_LP_BUSOUT_WIDTH 15


`define AIC_LT_DMAX_ASYNCHS_BUSOUT_WIDTH 14


`define AIC_LT_DMAX_CHMEM1_BUSOUT_WIDTH 82
































//Reset Value CFG Register

`define AIC_LT_CH1_CFG_RST_VAL 64'he001800000000

//Reset Value CFG Register

`define AIC_LT_CH2_CFG_RST_VAL 64'hc001b00000000

//Reset Value CFG Register

`define AIC_LT_CH3_CFG_RST_VAL 64'ha001b00000000

//Reset Value CFG Register

`define AIC_LT_CH4_CFG_RST_VAL 64'h8001b00000000

//Reset Value CFG Register

`define AIC_LT_CH5_CFG_RST_VAL 64'h6001b00000000

//Reset Value CFG Register

`define AIC_LT_CH6_CFG_RST_VAL 64'h4001b00000000

//Reset Value CFG Register

`define AIC_LT_CH7_CFG_RST_VAL 64'h2001b00000000

//Reset Value CFG Register

`define AIC_LT_CH8_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH9_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH10_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH11_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH12_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH13_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH14_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH15_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH16_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH17_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH18_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH19_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH20_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH21_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH22_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH23_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH24_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH25_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH26_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH27_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH28_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH29_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH30_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH31_CFG_RST_VAL 64'h1b00000000

//Reset Value CFG Register

`define AIC_LT_CH32_CFG_RST_VAL 64'h1b00000000

//Reset Value CTL Register

`define AIC_LT_CH1_CTL_RST_VAL 64'h1b00

//Reset Value CTL Register

`define AIC_LT_CH2_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH3_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH4_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH5_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH6_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH7_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH8_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH9_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH10_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH11_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH12_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH13_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH14_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH15_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH16_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH17_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH18_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH19_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH20_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH21_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH22_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH23_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH24_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH25_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH26_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH27_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH28_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH29_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH30_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH31_CTL_RST_VAL 64'h1200

//Reset Value CTL Register

`define AIC_LT_CH32_CTL_RST_VAL 64'h1200

//Reset Value LLP Register

`define AIC_LT_CH1_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH2_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH3_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH4_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH5_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH6_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH7_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH8_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH9_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH10_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH11_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH12_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH13_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH14_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH15_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH16_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH17_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH18_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH19_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH20_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH21_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH22_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH23_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH24_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH25_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH26_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH27_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH28_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH29_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH30_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH31_LLP_RST_VAL 64'h0

//Reset Value LLP Register

`define AIC_LT_CH32_LLP_RST_VAL 64'h0


`define AIC_LT_DMAX_INT_COMMENT 0



`define AIC_LT_DMAX_LOWPOWER_CFG_RESET_VAL 64'h404040000000f

`define AIC_LT_DMAX_HAS_MXIF_LPDLY_WIDTH_8_BELOW

`define AIC_LT_DMAX_HAS_SBIU_LPDLY_WIDTH_8_BELOW

`define AIC_LT_DMAX_HAS_GLCH_LPDLY_WIDTH_8_BELOW


`define AIC_LT_DMAX_CH1_PRIOR 0


`define AIC_LT_DMAX_CH2_PRIOR -1


`define AIC_LT_DMAX_CH3_PRIOR -2


`define AIC_LT_DMAX_CH4_PRIOR -3


`define AIC_LT_DMAX_CH5_PRIOR -4


`define AIC_LT_DMAX_CH6_PRIOR -5


`define AIC_LT_DMAX_CH7_PRIOR -6


`define AIC_LT_DMAX_CH8_PRIOR -7



`define AIC_LT_DMAX_CH1_RST_SRC_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH2_RST_SRC_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH3_RST_SRC_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH4_RST_SRC_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH5_RST_SRC_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH6_RST_SRC_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH7_RST_SRC_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH8_RST_SRC_MULTBLK_TYPE 0



`define AIC_LT_DMAX_CH1_RST_DST_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH2_RST_DST_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH3_RST_DST_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH4_RST_DST_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH5_RST_DST_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH6_RST_DST_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH7_RST_DST_MULTBLK_TYPE 0


`define AIC_LT_DMAX_CH8_RST_DST_MULTBLK_TYPE 0



`define AIC_LT_DMAX_CH1_RST_SMS 0


`define AIC_LT_DMAX_CH2_RST_SMS 0


`define AIC_LT_DMAX_CH3_RST_SMS 0


`define AIC_LT_DMAX_CH4_RST_SMS 0


`define AIC_LT_DMAX_CH5_RST_SMS 0


`define AIC_LT_DMAX_CH6_RST_SMS 0


`define AIC_LT_DMAX_CH7_RST_SMS 0


`define AIC_LT_DMAX_CH8_RST_SMS 0



`define AIC_LT_DMAX_CH1_RST_DMS 0


`define AIC_LT_DMAX_CH2_RST_DMS 0


`define AIC_LT_DMAX_CH3_RST_DMS 0


`define AIC_LT_DMAX_CH4_RST_DMS 0


`define AIC_LT_DMAX_CH5_RST_DMS 0


`define AIC_LT_DMAX_CH6_RST_DMS 0


`define AIC_LT_DMAX_CH7_RST_DMS 0


`define AIC_LT_DMAX_CH8_RST_DMS 0



`define AIC_LT_DMAX_CH1_RST_STW 3


`define AIC_LT_DMAX_CH2_RST_STW 2


`define AIC_LT_DMAX_CH3_RST_STW 2


`define AIC_LT_DMAX_CH4_RST_STW 2


`define AIC_LT_DMAX_CH5_RST_STW 2


`define AIC_LT_DMAX_CH6_RST_STW 2


`define AIC_LT_DMAX_CH7_RST_STW 2


`define AIC_LT_DMAX_CH8_RST_STW 2



`define AIC_LT_DMAX_CH1_RST_DTW 3


`define AIC_LT_DMAX_CH2_RST_DTW 2


`define AIC_LT_DMAX_CH3_RST_DTW 2


`define AIC_LT_DMAX_CH4_RST_DTW 2


`define AIC_LT_DMAX_CH5_RST_DTW 2


`define AIC_LT_DMAX_CH6_RST_DTW 2


`define AIC_LT_DMAX_CH7_RST_DTW 2


`define AIC_LT_DMAX_CH8_RST_DTW 2



`define AIC_LT_DMAX_CH1_RST_TT_FC 0


`define AIC_LT_DMAX_CH2_RST_TT_FC 3


`define AIC_LT_DMAX_CH3_RST_TT_FC 3


`define AIC_LT_DMAX_CH4_RST_TT_FC 3


`define AIC_LT_DMAX_CH5_RST_TT_FC 3


`define AIC_LT_DMAX_CH6_RST_TT_FC 3


`define AIC_LT_DMAX_CH7_RST_TT_FC 3


`define AIC_LT_DMAX_CH8_RST_TT_FC 3



`define AIC_LT_DMAX_CH1_RST_RD_UID 0


`define AIC_LT_DMAX_CH2_RST_RD_UID 0


`define AIC_LT_DMAX_CH3_RST_RD_UID 0


`define AIC_LT_DMAX_CH4_RST_RD_UID 0


`define AIC_LT_DMAX_CH5_RST_RD_UID 0


`define AIC_LT_DMAX_CH6_RST_RD_UID 0


`define AIC_LT_DMAX_CH7_RST_RD_UID 0


`define AIC_LT_DMAX_CH8_RST_RD_UID 0



`define AIC_LT_DMAX_CH1_RST_WR_UID 0


`define AIC_LT_DMAX_CH2_RST_WR_UID 0


`define AIC_LT_DMAX_CH3_RST_WR_UID 0


`define AIC_LT_DMAX_CH4_RST_WR_UID 0


`define AIC_LT_DMAX_CH5_RST_WR_UID 0


`define AIC_LT_DMAX_CH6_RST_WR_UID 0


`define AIC_LT_DMAX_CH7_RST_WR_UID 0


`define AIC_LT_DMAX_CH8_RST_WR_UID 0


//Define for channel 1 Read UID Enable

//Define for channel 2 Read UID Enable

//Define for channel 3 Read UID Enable

//Define for channel 4 Read UID Enable

//Define for channel 5 Read UID Enable

//Define for channel 6 Read UID Enable

//Define for channel 7 Read UID Enable

//Define for channel 8 Read UID Enable




//==============================================================================
// End Guard
//==============================================================================
`endif
