/*
------------------------------------------------------------------------
--
--
// ------------------------------------------------------------------------------
// 
// Copyright 2002 - 2020 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// 
// Component Name   : DW_apb_ssi
// Component Version: 4.03a
// Release Type     : GA
// ------------------------------------------------------------------------------

// 
// Release version :  4.03a
// File Version     :        $Revision: #2 $ 
// Revision: $Id: //dwh/DW_ocb/DW_apb_ssi/amba_dev/src/DW_apb_ssi_cc_constants.vh#2 $ 
--
//
//
-- File :                       DW_apb_ssi_cc_constants.v
-- Abstract     :               parameter file for the SSI.
--
-- =====================================================================
*/
//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`ifndef soc_periph_dw_ssi___GUARD__DW_APB_SSI_CC_CONSTANTS__VH__
`define soc_periph_dw_ssi___GUARD__DW_APB_SSI_CC_CONSTANTS__VH__


// Name:         APB_DATA_WIDTH
// Default:      32
// Values:       8 16 32
// 
// Width of APB data bus
`define soc_periph_dw_ssi_APB_DATA_WIDTH 32


// Name:         SSI_XIP_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      (SSI_SPI_MODE != 0) && (SSI_APBIF_TYPE != 0)
// 
// If selected DW_apb_ssi will be able to perform eXecute In Place (XIP) commands 
// while working in SPI protocol. A new sideband signal (xip_en) will be included as a part of APB interface 
// which can be used to select if slave interface is used to perform register read/write or in XIP mode.
`define soc_periph_dw_ssi_SSI_XIP_EN 0


// Name:         SSI_APBIF_TYPE
// Default:      APB 2.0
// Values:       APB 2.0 (0), APB 3.0 (1), APB 4.0 (2)
// 
// Selects the APB slave interface type.
`define soc_periph_dw_ssi_SSI_APBIF_TYPE 2


// Name:         SSI_APB3_ERR_RESP_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      SSI_APBIF_TYPE != 0
// 
// Configures if APB 3.0 interface should provide error response for invalid 
// read and write accesses. If this parameter is set to 0 then pslverr will  
// always be driven to 0.
`define soc_periph_dw_ssi_SSI_APB3_ERR_RESP_EN 0



// Name:         XIP_BASE_ADDR
// Default:      0x0
// Values:       0x0, ..., 0xffffffff
// Enabled:      SSI_XIP_EN
// 
// 32 bit Base Address for XIP slave to be used. 
// This address will be added to paddr signal to get the final address to be sent to SPI slave.
`define soc_periph_dw_ssi_XIP_BASE_ADDR 32'h0


// Name:         SSI_IS_MASTER
// Default:      Serial Master
// Values:       Serial Slave (0), Serial Master (1)
// 
// Configure the device as a master or a slave serial peripheral
`define soc_periph_dw_ssi_SSI_IS_MASTER 1


// Name:         SSI_SCPH0_SSTOGGLE
// Default:      Yes
// Values:       No (0), Yes (1)
// Enabled:      (SSI_DFLT_FRF==0) || (SSI_HC_FRF==0)
// 
// When operating in SPI mode with clock phase (SCPH) set to 0, this parameter  
// controls the behavior of the slave select line (ss_*_n) between data frames. 
//  - If this parameter is set to "Yes" and CTRLR0.SSTE is "1" the ss_*_n line will toggle between consecutive data 
//  frames, with the serial clock (sclk) being held to its default value while ss_*_n is high. 
//  - If this parameter is set to "Yes" and CTRLR0.SSTE is "0" the ss_*_n will stay low and sclk will run continuously for 
//  the duration of the transfer;  
//  - If this parameter is set to 0 the ss_*_n will stay low and sclk will run continuously for the duration of the 
//  transfer
`define soc_periph_dw_ssi_SSI_SCPH0_SSTOGGLE 1


// Name:         SSI_ENH_CLK_RATIO
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      SSI_IS_MASTER==0 && [<functionof> %item]
// 
// Configures the device to include new architecture for Transmit and Receive FIFO. 
// This will enable the device to work in clock ratio of 4 and 6 between ssi_clk and sclk_in signals.
`define soc_periph_dw_ssi_SSI_ENH_CLK_RATIO 0



// Name:         SSI_HAS_DDR
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      SSI_SPI_MODE != 0 && SSI_IS_MASTER==1 && [<functionof> %item]
// 
// Configures the device to support Dual Data transmission on both 
// positive and negative edge of sclk_out
`define soc_periph_dw_ssi_SSI_HAS_DDR 0


// Name:         SSI_HAS_RXDS
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      SSI_HAS_DDR ==1  && SSI_IS_MASTER==1 && [<functionof> %item]
// 
// Configures the device to include data strobe signaling 
// for rxd signal. This signal can be included only when DW_apb_ssi support dual data rate transfers
`define soc_periph_dw_ssi_SSI_HAS_RXDS 0


// Name:         SSI_SPI_DM_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      (SSI_SPI_MODE != 0) && (SSI_APBIF_TYPE == 2)
// 
// Selects if data mask signal should be included on SPI interface.  
// Data mask signal, when active, will mask the write data on SPI interface
`define soc_periph_dw_ssi_SSI_SPI_DM_EN 0


// Name:         SSI_MAX_XFER_SIZE
// Default:      16 Bits
// Values:       16 Bits (16), 32 Bits (32)
// 
// Configures the Maximum Transfer Size supported by device. 
// The Receive amd Transmit FIFO widths will be equal to configured value
`define soc_periph_dw_ssi_SSI_MAX_XFER_SIZE 16


// Name:         SSI_NUM_SLAVES
// Default:      1
// Values:       1, ..., 16
// Enabled:      SSI_IS_MASTER==1
// 
// Configures the number of slave select lines from the DW_apb_ssi master.
`define soc_periph_dw_ssi_SSI_NUM_SLAVES 4


// Name:         SSI_HAS_DMA
// Default:      false
// Values:       false (0), true (1)
// 
// Configures the inclusion of DMA handshaking interface signals. 
// Check the box to include the DMA interface signals.
`define soc_periph_dw_ssi_SSI_HAS_DMA 0


// Name:         SSI_RX_FIFO_DEPTH
// Default:      0x8
// Values:       0x2, ..., 0x100
// 
// Configures the depth of the receive FIFO buffer. 
//  - If SSI_SYNC_CLK == 0 or SSI_SPI_MODE != 0, minimum FIFO depth is 4. 
//  - Else minimum FIFO depth is 2.
`define soc_periph_dw_ssi_SSI_RX_FIFO_DEPTH 9'h8


// Name:         SSI_TX_FIFO_DEPTH
// Default:      0x8
// Values:       0x2, ..., 0x100
// 
// Configures the depth of the transmit FIFO buffer. 
//  - If SSI_SPI_MODE == 0, minimum FIFO depth is 2. 
//  - If SSI_SPI_MODE != 0 and SSI_MAX_XFER_SIZE == 16, minimum FIFO depth is 5. 
//  - If SSI_SPI_MODE != 0 and SSI_MAX_XFER_SIZE == 32, minimum FIFO depth is 3.
`define soc_periph_dw_ssi_SSI_TX_FIFO_DEPTH 9'h8


// Name:         SSI_INTR_POL
// Default:      Active Low
// Values:       Active Low (0), Active High (1)
// 
// Configures the active level of the output interrupt lines.
`define soc_periph_dw_ssi_SSI_INTR_POL 1


// Name:         SSI_INTR_IO
// Default:      Individual Interrupts
// Values:       Individual Interrupts (0), Combined Interrupt (1)
// 
// Selects which interrupt related pins appear as outputs of the design. 
// The user has a choice of either a single combined interrupt (the logical 
// OR of all DW_apb_ssi interrupt outputs) or have each individual interrupt 
// appear as a separate output pin on the component. 
//  - When configurated as a master there are 6 individual interrupts. 
//  - When configurated as a slave  there are 5 individual interrupts.
`define soc_periph_dw_ssi_SSI_INTR_IO 0


// Name:         SSI_CLK_EN_MODE
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      SSI_SYNC_CLK==1
// 
// When enabled, the ssi_clk_en signal enables data propagation 
// through ssi_clk flip-flops.  When disabled, the ssi_clk flip-flops 
// are always enabled.
`define soc_periph_dw_ssi_SSI_CLK_EN_MODE 0


// Name:         SSI_SYNC_CLK
// Default:      Yes
// Values:       No (0), Yes (1)
// 
// Defines if the pclk is synchronous to the ssi_clk. 
// If they are synchronous then one does not need to retime signals 
// across the clock domains.
`define soc_periph_dw_ssi_SSI_SYNC_CLK 1


// Name:         SSI_P2S_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// 
// Defines the number of synchronization register stages for signals passing from the DW_apb_ssi Slave clock domain (pclk) 
// to DW_apb_ssi Core Clock domain (ssi_clk). 
//  - 2: Two-stage synchronization, both stages positive edge. 
//  - 3: Three-stage synchronization, all stages positive edge. 
//  - 4: Four-stage synchronization, all stages positive edge. 
// across the clock domains.
`define soc_periph_dw_ssi_SSI_P2S_SYNC_DEPTH 2


// Name:         SSI_S2P_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// 
// Defines the number of synchronization register stages for signals passing from the DW_apb_ssi Core Clock domain 
// (ssi_clk) to Slave clock domain (pclk). 
//  - 2: Two-stage synchronization, both stages positive edge. 
//  - 3: Three-stage synchronization, all stages positive edge. 
//  - 4: Four-stage synchronization, all stages positive edge. 
// across the clock domains.
`define soc_periph_dw_ssi_SSI_S2P_SYNC_DEPTH 2


// Name:         SSI_HAS_RX_SAMPLE_DELAY
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      SSI_IS_MASTER==1
// 
// Include logic to allow programmable delay on the sample time of 
// the rxd input. When this logic is included, the default sample 
// time of the rxd input can be delayed by a programmable number 
// of ssi_clk cycles.
`define soc_periph_dw_ssi_SSI_HAS_RX_SAMPLE_DELAY 0


// Name:         SSI_RX_DLY_SR_DEPTH
// Default:      4
// Values:       4, ..., 255
// Enabled:      SSI_HAS_RX_SAMPLE_DELAY==1
// 
// Defines the maximum number of ssi_clk cycles that can 
// be used to delay the sampling of the rxd input 
//  - 2 flip-flops added to design logic for each value
`define soc_periph_dw_ssi_SSI_RX_DLY_SR_DEPTH 4


// Name:         SSI_ID
// Default:      0xffffffff
// Values:       0x0, ..., 0xffffffff
// 
// Individual peripheral Identification code.
`define soc_periph_dw_ssi_SSI_ID 32'hffffffff


// Name:         SSI_HC_FRF
// Default:      No
// Values:       No (0), Yes (1)
// 
// When set, the frame format (serial protocol) can be fixed so that the user cannot dynamically 
// program it. This setting restricts the use of DW_apb_ssi to be only a single-frame 
// format peripheral.
`define soc_periph_dw_ssi_SSI_HC_FRF 0


// Name:         SSI_DFLT_FRF
// Default:      Motorola SPI
// Values:       Motorola SPI (0x0), TI SSP (0x1), NatSemi Microwire (0x2)
// 
// Selects the frame format that will be available directly after reset. 
// User can configure any of the frame formats to be the default frame format. 
// If the frame format is hardcoded, the default frame format is the only 
// frame format possible.
`define soc_periph_dw_ssi_SSI_DFLT_FRF 2'h0



// Name:         SSI_SPI_MODE
// Default:      Standard SPI Mode
// Values:       Standard SPI Mode (0), SPI Dual Mode (1), SPI Quad Mode (2), SPI 
//               Octal Mode (3)
// Enabled:      ((SSI_DFLT_FRF==0) || (SSI_HC_FRF==0)) && (SSI_IS_MASTER==1) && 
//               [<functionof> %item]
// 
// Configures whether the core works in Standard or Dual or Quad or Octal SPI Mode. 
//  - In Dual Mode - width of txd and rxd signals will be 2-bits. 
//  - In Quad Mode - width of txd and rxd signals will be 4-bits. 
//  - In Octal Mode - width of txd and rxd signals will be 8-bits.
`define soc_periph_dw_ssi_SSI_SPI_MODE 2


// Name:         SSI_IO_MAP_EN
// Default:      No
// Values:       No (0), Yes (1)
// Enabled:      SSI_SPI_MODE!=0
// 
// Configures whether user wants to hardcode the I/O Mapping inside the controller. 
// After selecting this option the RXD[1] signal will be used to sample the incoming data 
// during SPI standard mode of operation.
`define soc_periph_dw_ssi_SSI_IO_MAP_EN 0


// Name:         SSI_INC_ENDCONV
// Default:      No
// Values:       No (0), Use sideband signal (1), Use register programming (2)
// Enabled:      SSI_IS_MASTER==1
// 
// When enabled user can choose whether a sideband signal or register programming is used to select the endianness for XIP 
// and data register reads. 
//  - 0 - No  
//  - 1 - Use sideband signal endconv_en 
//  - 2 - Programming SECONV field in CTRLR0 register
`define soc_periph_dw_ssi_SSI_INC_ENDCONV 0


// Name:         SSI_DFLT_SCPOL
// Default:      0
// Values:       0 1
// Enabled:      SSI_DFLT_FRF==0
// 
// Controls the default state of the clock polarity. 
// Defines the level of the serial clock when in-active (not toggling). 
// Only used when the frame format is Motorola SPI.
`define soc_periph_dw_ssi_SSI_DFLT_SCPOL 1'h0


// Name:         SSI_DFLT_SECONV
// Default:      Endian Conversion Disabled
// Values:       Endian Conversion Disabled (0x0), Endian Conversion Enabled (0x1)
// Enabled:      SSI_INC_ENDCONV==2
// 
// Controls the default state of the endian conversion feature.  
// Defines the reset value of the CTRLR0.SECONV register field. 
// Only used in Master mode.
`define soc_periph_dw_ssi_SSI_DFLT_SECONV 1'h0


// Name:         SSI_DFLT_SCPH
// Default:      0
// Values:       0 1
// Enabled:      SSI_DFLT_FRF==0
// 
// Controls the default state of the clock phase. 
// Only used when the frame format is Motorola SPI. 
// The serial clock phase selects the relationship of the serial clock with the 
// serial data. When 0, data is captured on the first edge of the serial clock. 
// When 1, data is captured on the second edge of the serial clock.
`define soc_periph_dw_ssi_SSI_DFLT_SCPH 1'h0

//Setting up a clock period for the SSI.

`define soc_periph_dw_ssi_SSI_CLK_PERIOD 100

//Setting up a clock period for the AHB.

`define soc_periph_dw_ssi_HCLK_PERIOD 100

//Include SVA assertions

//Qualifies the operation of the dma_tx_single output.
//When unchecked the 'dma_tx_single' output is held inactive (logic 0).
//The 'dma_tx_req' output will always request a multiple transaction.
//The transaction length is programmed into the DMA controller.
//This mode must be used if the DMA block
//length is NOT a multiple of the DMA transaction length.
//When checked the 'dma_tx_single' output is a status signal indicating
//to the dma controller that it can complete at least a single transaction
//to the DW_apb_ssi transmit fifo.
//This mode should be used if the DMA block length is a multiple of the
//DMA transaction length.

`define soc_periph_dw_ssi_SSI_DMA_TX_SGL_STATUS 1

//Qualifies the operation of the dma_rx_single output.
//When unchecked the 'dma_rx_single' output is held inactive (logic 0).
//The 'dma_rx_req' output will always request a multiple transaction.
//The transaction length is programmed into the DMA controller.
//This mode must be used if the DMA block
//length is NOT a multiple of the DMA transaction length.
//When checked the 'dma_rx_single' output is a status signal indicating
//to the dma controller that it can complete at least a single transaction
//to the DW_apb_ssi receive fifo.
//This mode should be used if the DMA block length is a multiple of the
//DMA transaction length.

`define soc_periph_dw_ssi_SSI_DMA_RX_SGL_STATUS 1


//Internal Define for APB Data Width 8

// `define soc_periph_dw_ssi_APB_DATA_WIDTH_8

//Internal Define for APB Data Width 16

// `define soc_periph_dw_ssi_APB_DATA_WIDTH_16


//Internal Define for APB Data Width 32

`define soc_periph_dw_ssi_APB_DATA_WIDTH_32

//APB Strobe width
`define soc_periph_dw_ssi_PSTRB_WIDTH  `soc_periph_dw_ssi_APB_DATA_WIDTH/8

//Set SSI_INDIVIDUAL

`define soc_periph_dw_ssi_SSI_INDIVIDUAL 0

//set SSI_COMBINED

`define soc_periph_dw_ssi_SSI_COMBINED 1


// `define soc_periph_dw_ssi_SSI_HAS_RX_SAMPLE_LOGIC

//Internal Define for 32 bit mode

// `define soc_periph_dw_ssi_SSI_HAS_32_BIT_XFER_SIZE


`define soc_periph_dw_ssi_DM_FIFO_W 2

//Internal Define for Data Frame Size (DFS) width

`define soc_periph_dw_ssi_DFS_W 4

//Reset Value of CTRLR0 Registers bits for DQ mode
`define soc_periph_dw_ssi_SSI_DFLT_SPI_FRF 2'b00

//Reset Value of CTRLR0 Registers bits for DQ mode
`define soc_periph_dw_ssi_SSI_DFLT_SPI_TRANS 2'b00

//Reset Value of CTRLR0 Registers bits for DQ mode
`define soc_periph_dw_ssi_SSI_DFLT_DQ_INST 2'b10

//Reset Value of CTRLR0 Registers bits for DQ mode
`define soc_periph_dw_ssi_SSI_DFLT_DQ_WAIT 4'b00

//Reset Field for SCPH_TOGGLE_EN bit

`define soc_periph_dw_ssi_SSI_SCPH0_SSTOGGLE_RST 1'h1

//Reset Value of CTRLR0 Registers in  Dual/Quad SPI Mode.

`define soc_periph_dw_ssi_SSI_CTRLR0_RST_19 25'h1070000

//Reset Value of CTRLR0 Registers in  Dual/Quad SPI Mode.

`define soc_periph_dw_ssi_SSI_CTRLR0_RST_18 25'h1000007

//Reset Value of CTRLR0 Registers in 32 bit mode.

`define soc_periph_dw_ssi_SSI_CTRLR0_RST_21 25'h1070000

//Reset Value of CTRLR0 Registers in 16 bit mode.

`define soc_periph_dw_ssi_SSI_CTRLR0_RST_16 25'h1000007

//CTRLR0 reset value.

`define soc_periph_dw_ssi_SSI_CTRLR0_RST 32'h1000007

//Width of irpdata

`define soc_periph_dw_ssi_MAX_APB_DATA_WIDTH 32

//Width of MWCR register

`define soc_periph_dw_ssi_MWCR_RS 3

//Width of Interrupt register

`define soc_periph_dw_ssi_INT_RS 6

//Receive data width of FIFO

`define soc_periph_dw_ssi_RX_ABW 3

//Write data width of FIFO

`define soc_periph_dw_ssi_TX_ABW 3

//Address Slice LHS

`define soc_periph_dw_ssi_SSI_ADDR_SLICE_LHS 8


`define soc_periph_dw_ssi_APB_ADDR_WIDTH 8

//Default Value of SCLK OUT.

`define soc_periph_dw_ssi_SSI_DFLT_SCLK_OUT 1'h0

//Default Value of SSI_DFLT_SS_N

`define soc_periph_dw_ssi_SSI_DFLT_SS_N 1'h1

//Each corekit has a version number.
//This is relected in the ascii version number which needs to get translated.
// 0 => 48 -> 30
// 1 => 49 -> 31
// 2 => 50 -> 32
// A => 65 -> 41
// B => 66 -> 42
// C => 67 -> 43
//
//Current Version is 4.03* => 34_30_33_2A
//

`define soc_periph_dw_ssi_SSI_VERSION_ID 32'h3430332a

//Random seed used in the testbench

`define soc_periph_dw_ssi_SSI_RAND_SEED 32'h0



`define soc_periph_dw_ssi_SSI_OE_LEGACY_MODE 1

//Creates a define for enabling low power interface

`define soc_periph_dw_ssi_SSI_SCPH0_SSTOGGLE_IS_ONE

//Internal Define for dual/quad mode

`define soc_periph_dw_ssi_SSI_HAS_EXTD_SPI

//Internal define for SPI IO maping

// `define soc_periph_dw_ssi_SSI_SPI_HAS_ENH_IO_MAP

//Parameter to define number of IOs in multi mode (dual/quad) for SPI

`define soc_periph_dw_ssi_SSI_SPI_MULTIIO 4

//SSI Has Quad Mode Enabled
`define soc_periph_dw_ssi_SSI_SPI_HAS_QUAD

//SSI Has Quad Mode Enabled

//Creates a define for Master config

`define soc_periph_dw_ssi_SSI_MASTER_EN

//Creates a define for Slave config

// `define soc_periph_dw_ssi_INC_ENH_CLK_RATIO

//Creates a define synchronization type

`define soc_periph_dw_ssi_BCM_SYNC_TYPE 2


`define soc_periph_dw_ssi_SSI_HAS_SYNC_CLK


// `define soc_periph_dw_ssi_SSI_HAS_ASYNC_RX_FIFO

//Creating define for ASYNC clock

// `define soc_periph_dw_ssi_SSI_HAS_ASYNC_CLK


`define soc_periph_dw_ssi_SSI_HAS_ASYNC_CLK_NDEF


// `define soc_periph_dw_ssi_SSI_INC_DTR


// `define soc_periph_dw_ssi_SSI_INC_RXDS


`define soc_periph_dw_ssi_SSI_HAS_APB3


`define soc_periph_dw_ssi_SSI_HAS_APB4


// `define soc_periph_dw_ssi_SSI_HAS_SPI_DM


// `define soc_periph_dw_ssi_SSI_APB3_HAS_ERR_RESP


// `define soc_periph_dw_ssi_SSI_HAS_XIP

//CTRLR0 Register width

`define soc_periph_dw_ssi_CTRLR0_RS 19

//SPI_CTRLR0 Register width

`define soc_periph_dw_ssi_SPI_CTRLR0_RS 13

//32 bit Base Address for APB Slave

`define soc_periph_dw_ssi_APB3_SLV_BASE_ADDR 32'h0


`define soc_periph_dw_ssi_RX_RAM_DEPTH 8


`define soc_periph_dw_ssi_TX_RAM_DEPTH 8

//**************************************************************************************************
// Parameters to remove init and test ports in bcm
//**************************************************************************************************


`define soc_periph_dw_ssi_DWC_NO_TST_MODE

`define soc_periph_dw_ssi_DWC_NO_CDC_INIT

// BCM Constants
`define soc_periph_dw_ssi_DWC_BCM06_NO_DIAG_N

//Width of TX FIFO 

`define soc_periph_dw_ssi_TX_FIFO_WIDTH 16

//Width of TX FIFO 

// `define soc_periph_dw_ssi_DM_PORTS_REMOVAL

//Control switch to enable Clock Frequency Utilization

`define soc_periph_dw_ssi_SSI_USE_FREQ_SWITCH 0

// This parameter is set if Clock Frequency Utilization is enabled


`define soc_periph_dw_ssi_SSIC_S2P_VERIF_EN 1


`define soc_periph_dw_ssi_SSIC_P2S_VERIF_EN 1




//Used to insert internal tests

//==============================================================================
// End Guard
//==============================================================================
 `endif

