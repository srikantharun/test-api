// ------------------------------------------------------------------------
//
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
// Component Name   : DW_apb_uart
// Component Version: 4.03a
// Release Type     : GA
// ------------------------------------------------------------------------------

// 
// Release version :  4.03a
// File Version     :        $Revision: #1 $ 
// Revision: $Id: //dwh/DW_ocb/DW_apb_uart/amba_dev/src/DW_apb_uart_cc_constants.vh#1 $ 
//
//  File :                       DW_apb_uart_cc_constants.vh
//  Author:                      LehKui Ong & Marc Wall
//
//
//  Date :                       $Date: 2020/12/09 $
//  Abstract     :               parameter file for the UART.
//
//  =====================================================================
//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`ifndef soc_periph_dw_uart___GUARD__DW_APB_UART_CC_CONSTANTS__VH__
`define soc_periph_dw_uart___GUARD__DW_APB_UART_CC_CONSTANTS__VH__


// Name:         SLAVE_INTERFACE_TYPE
// Default:      APB2
// Values:       APB2 (0), APB3 (1), APB4 (2)
// Enabled:      [<functionof> %item]
// 
// Selects Register Interface type as APB2, APB3 or APB4. 
// By default, DW_apb_uart supports APB2 interface.
`define soc_periph_dw_uart_SLAVE_INTERFACE_TYPE 2


// Name:         FIFO_MODE
// Default:      16
// Values:       0 16 32 64 128 256 512 1024 2048
// 
// Receiver and Transmitter FIFO depth in bytes. A setting of NONE means 
// no FIFOs, which implies the 16450-compatible mode of operation. Most 
// enhanced features are unavailable in the 16450 mode such as the Auto 
// Flow Control and Programmable THRE interrupt modes. Setting a FIFO 
// depth greater than 256 restricts the FIFO Memory to External only. For 
// more details, refer to the "FIFO Support" section of the databook.
`define soc_periph_dw_uart_FIFO_MODE 16

//APB Interface has APB3 signals

`define soc_periph_dw_uart_UART_HAS_APB3_IF_SIGNALS

//APB Interface has APB4 signals

`define soc_periph_dw_uart_UART_HAS_APB4_IF_SIGNALS


// Name:         PSLVERR_RESP_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>0
// 
// Enable Slave Error response signaling. The component will refrain 
// From signaling an error response if this parameter is disabled.  
// This will result in disabling all features that require SLVERR functionality to be implemented.
`define soc_periph_dw_uart_PSLVERR_RESP_EN 0

//Component has slave error response enabled

// `define soc_periph_dw_uart_UART_HAS_SLVERR_RESP_EN


// Name:         PROT_LEVEL_RST
// Default:      0x2
// Values:       0x0, ..., 0x7
// Enabled:      SLAVE_INTERFACE_TYPE>1 && PSLVERR_RESP_EN==1
// 
// Reset Value of UART_PROT_LEVEL register. 
// A high on any bit of UART protection level requires a high on the 
// corresponding pprot input bit to gain access to the protected registers. 
// Else, SLVERR response is triggered. A zero on the protection bit will 
// provide access to the register if other protection levels are satisfied.
`define soc_periph_dw_uart_PROT_LEVEL_RST 3'h2


// Name:         HC_PROT_LEVEL
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>1 && PSLVERR_RESP_EN==1
// 
// Setting this parameter to 1 makes UART_PROT_LEVEL a read-only register. 
// The register can be programmed at run-time by a user if this 
// hard-code option is set to 0.
`define soc_periph_dw_uart_HC_PROT_LEVEL 0

//Component has hard-coded protection level enabled

// `define soc_periph_dw_uart_UART_HAS_PROT_HC

//Component has protection functionality enabled

// `define soc_periph_dw_uart_UART_HAS_PROT_FN

//Component has protection functionality enabled

// `define soc_periph_dw_uart_UART_HAS_APB3_PSLVERR_FIFO


// Name:         REG_TIMEOUT_WIDTH
// Default:      0 ((SLAVE_INTERFACE_TYPE > 0 && PSLVERR_RESP_EN==1 && FIFO_MODE!=0) 
//               ? 4 : 0)
// Values:       0 4 5 6 7 8
// Enabled:      SLAVE_INTERFACE_TYPE>0 && PSLVERR_RESP_EN==1 && FIFO_MODE!=0
// 
// Defines the width of Register timeout counter. If set to zero, 
// the timeout counter register is disabled, and timeout is triggered 
// as soon as the transaction tries to read an empty RX FIFO or write 
// to a full TX FIFO. These are the only cases where PREADY signal 
// goes low, in all other cases PREADY is tied high. Setting 
// values from 4 to 8 for this parameter configures the timeout 
// period from 2^4 to 2^8 pclk cycles.
`define soc_periph_dw_uart_REG_TIMEOUT_WIDTH 0

//Component has protection functionality enabled

// `define soc_periph_dw_uart_UART_HAS_APB3_PSLVERR_FIFO_TW_NOT_0

//Slave has non-zero reg_timeout_width

// `define soc_periph_dw_uart_UART_HAS_POSITIVE_REG_TIMEOUT_WIDTH


// Name:         HC_REG_TIMEOUT_VALUE
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>0 && PSLVERR_RESP_EN==1 && REG_TIMEOUT_WIDTH>0 
//               && FIFO_MODE!=0
// 
// Checking this parameter makes Register timeout counter a read-only register. 
// The register can be programmed by user if the hardcode option is turned off.
`define soc_periph_dw_uart_HC_REG_TIMEOUT_VALUE 0

//APB Interface has hardcoded timeout reset value

// `define soc_periph_dw_uart_UART_HAS_HC_REG_TIMEOUT_VALUE


`define soc_periph_dw_uart_POW_2_REG_TIMEOUT_WIDTH 0


// Name:         REG_TIMEOUT_VALUE
// Default:      8
// Values:       0, ..., POW_2_REG_TIMEOUT_WIDTH
// Enabled:      SLAVE_INTERFACE_TYPE>0 && PSLVERR_RESP_EN==1 && REG_TIMEOUT_WIDTH>0 
//               && FIFO_MODE!=0
// 
// Defines the reset value of Register timeout counter.
`define soc_periph_dw_uart_REG_TIMEOUT_VALUE 8


// Name:         UART_RS485_INTERFACE_EN
// Default:      Disabled
// Values:       Disabled (0), Enabled (1)
// Enabled:      [<functionof> %item]
// 
// Configures the peripheral for RS485 Interface support. 
// If enabled, new signals 'de', 're' and 'rs485_en' are included in the interface 
// to support RS485 transceiver.
`define soc_periph_dw_uart_UART_RS485_INTERFACE_EN 0

//APB Interface has APB3 signals

// `define soc_periph_dw_uart_UART_HAS_RS485_INTF


// Name:         UART_DE_POL
// Default:      true
// Values:       false (0x0), true (0x1)
// Enabled:      UART_RS485_INTERFACE_EN==1
// 
// Selects the polarity of the RS485 Driver Enable (de) signal.
`define soc_periph_dw_uart_UART_DE_POL 1'h1


// Name:         UART_RE_POL
// Default:      true
// Values:       false (0x0), true (0x1)
// Enabled:      UART_RS485_INTERFACE_EN==1
// 
// Selects the polarity of the RS485 Receiver Enable (re) signal.
`define soc_periph_dw_uart_UART_RE_POL 1'h1


// Name:         UART_9BIT_DATA_EN
// Default:      Disabled
// Values:       Disabled (0), Enabled (1)
// Enabled:      [<functionof> %item]
// 
// Configures the peripheral to have 9-bits of data per character. 
// The 9th-bit of the data byte sent from the master is set to 1  
// to indicate the address byte while cleared to 0 to indicate  
// the data byte.
`define soc_periph_dw_uart_UART_9BIT_DATA_EN 0


// `define soc_periph_dw_uart_UART_HAS_9BIT_DATA


// Name:         APB_DATA_WIDTH
// Default:      32
// Values:       8 16 32
// 
// Width of APB data bus to which this component is attached. 
// The data width can be set to 8, 16 or 32. Register access 
// is on 32-bit boundaries, unused bits are held at static 0.
`define soc_periph_dw_uart_APB_DATA_WIDTH 32


// `define soc_periph_dw_uart_APB_DATA_WIDTH_8


// `define soc_periph_dw_uart_APB_DATA_WIDTH_16


`define soc_periph_dw_uart_APB_DATA_WIDTH_32

//Maximum allowed APB Data bus width.

`define soc_periph_dw_uart_MAX_APB_DATA_WIDTH 32

`define soc_periph_dw_uart_FIFO_MODE_ENABLED


// Name:         MEM_SELECT_USER
// Default:      External
// Values:       External (0), Internal (1)
// Enabled:      FIFO_MODE!=0 && FIFO_MODE<=256
// 
// Selects between external, user-supplied memory or internal DesignWare 
// memory (DW_ram_r_w_s_dff) for the receiver and transmitter FIFOs. FIFO 
// depths greater than 256 restrict FIFO Memory selection to external. In 
// addition, selection of internal memory restricts the Memory Read Port 
// Type to Dflip-flop-based, synchronous read port RAMs.
`define soc_periph_dw_uart_MEM_SELECT_USER 0


`define soc_periph_dw_uart_MEM_SELECT 0


// `define soc_periph_dw_uart_MEM_SELECT_EQ_1

`define soc_periph_dw_uart_MEM_SELECT_EQ_0

//This non-changeable parameter has been retained in this release of the
//DW_apb_uart for backward compatibility with pre-3.00a versions of this
//component.

`define soc_periph_dw_uart_MEM_MODE_USER 0


`define soc_periph_dw_uart_MEM_MODE 0


// Name:         SIR_MODE
// Default:      Disabled
// Values:       Disabled (0x0), Enabled (0x1)
// 
// Configures the peripheral to have IrDA 1.0 SIR infrared mode. For more details, 
// refer to the "IrDA 1.0 SIR Protocol" section of data book.
`define soc_periph_dw_uart_SIR_MODE 1'h0


// Name:         SIR_LP_MODE
// Default:      Disabled
// Values:       Disabled (0x0), Enabled (0x1)
// Enabled:      SIR_MODE==1
// 
// Configures the peripheral to operate in a low-power IrDA SIR mode. As 
// the DW_apb_uart does not support a low-power mode with a counter system 
// to maintain a 1.63us infrared pulse, Asynchronous Serial Clock Support 
// will be automatically enabled, and the sclk must be fixed to 1.8432Mhz. 
// This provides a 1.63us sir_out_n pulse at 115.2kbaud.
`define soc_periph_dw_uart_SIR_LP_MODE 1'h0


// Name:         SIR_LP_RX
// Default:      Disabled
// Values:       Disabled (0), Enabled (1)
// Enabled:      SIR_MODE==1
// 
// Configures the peripheral to to have SIR low power pulse reception 
// capabalities. Two additional Low power Divisor Registers are implemented 
// and must be written with a divisor that will give a baud rate of 115.2k 
// for the low power pulse detection functionality to operate correctly.  
// Asynchronous Serial Clock support is automatically enabled in this mode.
`define soc_periph_dw_uart_SIR_LP_RX 0


// Name:         CLOCK_MODE
// Default:      Disabled ([<functionof> SIR_LP_MODE SIR_LP_RX])
// Values:       Disabled (1), Enabled (2)
// Enabled:      SIR_LP_MODE!=1 && SIR_LP_RX!=1
// 
// When set to Disabled, the DW_apb_uart is implemented with one system 
// clock (pclk). When set to Enabled, two system clocks (pclk and sclk) 
// are implemented in order to accommodate accurate serial baud rate 
// settings, as well as APB bus interface requirements. Selecting Disabled, 
// or a one-system clock, greatly restricts system clock settings 
// available for accurate baud rates. For more details, refer to 
// "Synchronization" section of the databook.
`define soc_periph_dw_uart_CLOCK_MODE 1



// Name:         SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define soc_periph_dw_uart_SYNC_DEPTH 2


`define soc_periph_dw_uart_UART_VERIF_EN 1


// Name:         AFCE_MODE
// Default:      Disabled
// Values:       Disabled (0x0), Enabled (0x1)
// Enabled:      FIFO_MODE!=0
// 
// Configures the peripheral to have the 16750-compatible auto flow control 
// mode. For more details, refer to "Auto Flow Control" section of the 
// data book.
`define soc_periph_dw_uart_AFCE_MODE 1'h1


// Name:         RTC_FCT
// Default:      RX FIFO Threshold Trigger
// Values:       RX FIFO Threshold Trigger (0x0), RX FIFO Almost-Full Trigger (0x1)
// Enabled:      AFCE_MODE!=0
// 
// When set to 0, the DW_apb_uart uses the same receiver trigger level described in FCR.RCVR  
// register both for generating a DMA request and a handshake signal (rts_n). When  
// set to 1, the DW_apb_uart uses two separate trigger levels for a DMA request and handshake 
// signal (rts_n) in order to maximize throughput on the interface. 
// NOTE:  Almost-Full Trigger refers to two available slots in the FIFO.
`define soc_periph_dw_uart_RTC_FCT 1'h0


// Name:         THRE_MODE_USER
// Default:      Disabled
// Values:       Disabled (0x0), Enabled (0x1)
// Enabled:      FIFO_MODE!=0
// 
// Configures the peripheral to have a programmable Transmitter Hold 
// Register Empty (THRE) interrupt mode. For more information, refer to 
// "Programmable THRE Interrupt" section of the data book.
`define soc_periph_dw_uart_THRE_MODE_USER 1'h0


`define soc_periph_dw_uart_THRE_MODE 1'h0

//THRE_MODE Reset Value

`define soc_periph_dw_uart_THRE_MODE_RST 1'h0



// Name:         CLK_GATE_EN
// Default:      false
// Values:       false (0), true (1)
// 
// Configures the peripheral to have a clock gate enable output signal on 
// the interface that indicates that the device is inactive, so clocks 
// may be gated.
`define soc_periph_dw_uart_CLK_GATE_EN 0




// Name:         FIFO_ACCESS
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Configures the peripheral to have a programmable FIFO access mode. 
// This is used for test purposes to allow the receiver FIFO to be 
// written and the transmit FIFO to be read when FIFO's are implemented 
// and enabled. When FIFO's are not implemented or not enabled it allows 
// the RBR to be written and the THR to be read. For more details, refer 
// to "FIFO Support" section in the data book.
`define soc_periph_dw_uart_FIFO_ACCESS 1'h0


// Name:         DMA_EXTRA
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Configures the peripheral to have four additional DMA signals on the 
// interface so that the device is compatible with the DesignWare DMA 
// controller interface requirements.
`define soc_periph_dw_uart_DMA_EXTRA 1'h0


// Name:         DMA_POL
// Default:      true
// Values:       false (0), true (1)
// 
// Selects the polarity of the DMA interface signals.
`define soc_periph_dw_uart_DMA_POL 1


// Name:         DMA_HS_REQ_ON_RESET
// Default:      true
// Values:       false (0), true (1)
// 
// Selects the DMA Tx Request assertion logic. 
// When set to 1, DMA Tx Request will be asserted upon reset. 
// When set to 0, DMA Tx Request will not be asserted upon reset.   
// It will be asserted only after LCR register is written.
`define soc_periph_dw_uart_DMA_HS_REQ_ON_RESET 1


`define soc_periph_dw_uart_HAS_DMA_HS_REQ_ON_RESET

`define soc_periph_dw_uart_DMA_IF_ACTIVE_LOW 1



// Name:         DEBUG
// Default:      false
// Values:       false (0), true (1)
// 
// Configures the peripheral to have on-chip debug pins on the interface.
`define soc_periph_dw_uart_DEBUG 0

// Define for debug interface


// Name:         BAUD_CLK
// Default:      true
// Values:       false (0), true (1)
// 
// Configures the peripheral to have a baud clock reference output 
// (baudout_n) pin on the interface.
`define soc_periph_dw_uart_BAUD_CLK 1


// Name:         ADDITIONAL_FEATURES
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Configures the peripheral to have the option to include the FIFO status 
// registers, shadow registers and encoded parameter register. Also configures 
// the peripheral to have the UART component version and the peripheral ID registers.
`define soc_periph_dw_uart_ADDITIONAL_FEATURES 1'h0


// Name:         FIFO_STAT
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      FIFO_MODE!=0 && ADDITIONAL_FEATURES==1
// 
// Configures the peripheral to have three additional FIFO status registers.
`define soc_periph_dw_uart_FIFO_STAT 1'h0


// Name:         SHADOW
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      ADDITIONAL_FEATURES==1
// 
// Configures the peripheral to have nine additional registers that 
// shadow some of the existing register bits that are regularly modified 
// by software. These can be used to reduce the software overhead that is 
// introduced by having to perform read-modify writes.
`define soc_periph_dw_uart_SHADOW 1'h0


// Name:         UART_ADD_ENCODED_PARAMS
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      ADDITIONAL_FEATURES==1
// 
// Configures the peripheral to have a component parameter register.
`define soc_periph_dw_uart_UART_ADD_ENCODED_PARAMS 1'h0


// Name:         UART_16550_COMPATIBLE
// Default:      false
// Values:       false (0), true (1)
// 
// Configures the peripheral to be fully 16550 compatible. This is achieved 
// by not having the busy functionality implemented.
`define soc_periph_dw_uart_UART_16550_COMPATIBLE 0


// Name:         FRACTIONAL_BAUD_DIVISOR_EN
// Default:      Disabled
// Values:       Disabled (0), Enabled (1)
// Enabled:      [<functionof> %item]
// 
// Configures the peripheral to have Fractional Baud Rate Divisor. If enabled, new  
// Fractional divisor latch register (DLF) is included to program the fractional divisor 
// values. For more information about this feature, see "Fractional Baud Rate Support" section in the data book.
`define soc_periph_dw_uart_FRACTIONAL_BAUD_DIVISOR_EN 0


// Name:         DLF_SIZE
// Default:      4
// Values:       4, ..., 6
// Enabled:      FRACTIONAL_BAUD_DIVISOR_EN==1
// 
// Specifies the width of the fractional divisor. A high value means more precision but long averaging period. 
// For more information about this feature, see "Fractional Baud Rate Support" section in the data book.
`define soc_periph_dw_uart_DLF_SIZE 4


// Name:         LSR_STATUS_CLEAR
// Default:      RBR Read or LSR Read
// Values:       RBR Read or LSR Read (0), LSR Read (1)
// Enabled:      FIFO_MODE!=0
// 
// Adds a register field IER.ELCOLR and selects the method for clearing the status in the LSR register. 
// This is applicable only for Overrun Error (OE), Parity Error (PE), Framing Error (FE), and Break Interrupt (BI) status 
// bits. 
// For more information, refer to Table 2-6 of the DW_apb_uart databook. 
//  
// When set to 0: 
//  - LSR status bits (PE, FE and BI) are cleared either on reading Rx FIFO (RBR Read) or On reading LSR register. 
//  - The Overrun Error Interrupt status is cleared only on reading LSR register. 
// When set to 1: 
//  - If register field IER.ELCOLR = 0: LSR status bits (OE, PE, FE and BI) are cleared either on reading Rx FIFO (RBR 
//  Read) or On reading LSR register. 
//  - If register field IER.ELCOLR = 1: LSR status bits (OE, PE, FE and BI) are cleared only on reading LSR register.
`define soc_periph_dw_uart_LSR_STATUS_CLEAR 0

// This parameter is set if Avoide LSR clear is enabled

//This is a non-changeable parameter that is only included for software-
//backwards compatibility. That is so that no errors will arise when the
//peripheral is used with existing software.

`define soc_periph_dw_uart_LATCH_MODE_USER 0


`define soc_periph_dw_uart_LATCH_MODE 0

//This non-changeable parameter has been retained in this release of the
//DW_apb_uart for backward compatibility with pre-3.00a versions of this
//component.

`define soc_periph_dw_uart_PCLK_PER 30

//This non-changeable parameter has been retained in this release of the
//DW_apb_uart for backward compatibility with pre-3.00a versions of this
//component.

`define soc_periph_dw_uart_SCLK_PER 40

//Size of the FIFO address bus. Calculated by log2(FIFO depth).

`define soc_periph_dw_uart_FIFO_ADDR_WIDTH 4

//Timeout detect counter enables width, that is the number of signals
//required for counter enable purposes in the timeout detection block.
//If clock gate enable signal(s) have been configured 8 signals are
//required else 3 signals are required.

`define soc_periph_dw_uart_TO_DET_CNT_ENS_WIDTH 3


`define soc_periph_dw_uart_UART_ADDR_SLICE_LHS 8

//Each corekit has a component version.
//This is reflected in the ASCII version number which needs to get translated.
//
// 0 => 48 -> 30
// 1 => 49 -> 31
// 2 => 50 -> 32
// A => 65 -> 41
// B => 66 -> 42
// C => 67 -> 43
//
//Current Version is 4.03* => 34_30_33_2A (ASCII values for 4.03*)
//

`define soc_periph_dw_uart_UART_COMP_VERSION 32'h3430332a

//Software Component Type.
//The first 16 bits represents "DW" in ASCII

`define soc_periph_dw_uart_UART_COMP_TYPE 32'h44570110

//Encoded value of FIFO_MODE parameter for Configuration ID

`define soc_periph_dw_uart_UART_ENCODED_FIFO_MODE 8'h1

//Encoded value of APB_DATA_WIDTH parameter for Configuration ID

`define soc_periph_dw_uart_UART_ENCODED_APB_WIDTH 2'h2

//Component Parameter Register Reset Value.

`define soc_periph_dw_uart_UART_COMP_PARAM_RST 32'h0

//Hardware reset value for XFER_MODE bit field in TCR register

`define soc_periph_dw_uart_UART_RS485_XFER_MODE_DFLT 2'h0

//TCR Register Reset Value.

`define soc_periph_dw_uart_UART_TCR_RST 5'h6

//DE assertion time Register Reset Value.

`define soc_periph_dw_uart_UART_DE_AT_RST 8'h0

//DE de-assertion time Register Reset Value.

`define soc_periph_dw_uart_UART_DE_DAT_RST 8'h0

//Turnaround time Register Reset Value.

`define soc_periph_dw_uart_UART_TAT_RST 32'h0

//Number of baud clock samples per serial bit (bit period)

`define soc_periph_dw_uart_UART_NUM_SAMPLES 5'h10

//APB write data width based on APB_DATA_WDTH

`define soc_periph_dw_uart_WR_DATA_WIDTH 10


//Controls the amount of information being displayed

`define soc_periph_dw_uart_UART_SIM_REPORT_DEBUG 0

//Controls if simulations will terminate on a checker failure.

`define soc_periph_dw_uart_UART_SIM_TERMINATE_ON_CHECKER_FAILURE 1

//Controls the max number of character exchanged during transmit/receive.

`define soc_periph_dw_uart_UART_SIM_SHORT_CHARACTER_STREAM_LENGTH 1

//Controls functional coverage,coverage_group_collect in Vera.

`define soc_periph_dw_uart_UART_SIM_FUNCTIONAL_COVERAGE 0

//Controls seed for srandom() in UartTestLib.vr

`define soc_periph_dw_uart_UART_SIM_RANDOM_SEED 1

//Determines if simulations terminate when the SIOMonitor detects an error

`define soc_periph_dw_uart_UART_SIM_TERMINATE_ON_SIOMON_ERROR 1

//Control SCLK : PCLK Relationship

`define soc_periph_dw_uart_UART_SIM_SCLK_PCLK_RELATIONSHIP 0

//Control SCLK period

`define soc_periph_dw_uart_UART_SIM_SCLK_PERIOD 13

//Control switch to enable/disable special condition testing

`define soc_periph_dw_uart_UART_SIM_DO_SPECIAL_CONDITION 1

//Control switch to enable/disable special condition testing

`define soc_periph_dw_uart_UART_SIM_SIOMON_ACTIVE_ON_SIN 0

//Override parameter: determines the MAXIMUM number of iterations performed for verification

`define soc_periph_dw_uart_UART_SIM_MAX_ITERATION_VAL 2

//Override control switch; if enabled, all other Override parameters make sense.

`define soc_periph_dw_uart_UART_SIM_OVERRIDE 0

//Enable directed control of TB

`define soc_periph_dw_uart_UART_SIM_USE_DIRECTED_CONTROL 0

//Override parameter: determines the TRANSFER_DIRECTION

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_TRANSFER_DIRECTION_VAL 0

//Override parameter: determines the MAXIMUM number of iterations performed for verification

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_MAX_ITERATION_VAL 2

//Override parameter: determines the MAXIMUM number of rounds for each iteration

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_MAX_ROUND_VAL 2

//Override parameter: determines if the UART IER parameters are overriden

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_IER 0

//Override parameter: determines the override-value for IER's PTIME

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_IER_PTIME_VAL 0

//Override parameter: determines the override-value for IER's EDSSI

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_IER_EDSSI_VAL 0

//Override parameter: determines the override-value for IER's ELSI

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_IER_ELSI_VAL 0

//Override parameter: determines the override-value for IER's ETBEI

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_IER_ETBEI_VAL 0

//Override parameter: determines the override-value for IER's ERBFI

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_IER_ERBFI_VAL 0

//Override parameter: determines if the UART FCR parameters are overriden

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_FCR 0

//Override parameter: determines the override-value for FCR's FIFO_EN

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_FCR_FIFO_EN_VAL 0

//Override parameter: determines the override-value for FCR's DMA MODE

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_FCR_DMAM_VAL 0

//Override parameter: determines the override-value for FCR's RCVR TRIGGER

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_FCR_RT_VAL 0

//Override parameter: determines the override-value for FCR's TXEMPTY TRIGGER

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_FCR_TET_VAL 0

//Override parameter: determines if the UART LCR parameters are overriden

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_LCR 0

//Override parameter: determines the override-value for LCR's Stick Parity

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_LCR_SP_VAL 0

//Override parameter: determines the override-value for LCR's EPS

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_LCR_EPS_VAL 0

//Override parameter: determines the override-value for LCR's PEN

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_LCR_PEN_VAL 0

//Override parameter: determines the override-value for LCR's STOP

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_LCR_STOP_VAL 0

//Override parameter: determines the override-value for LCR's DLS

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_LCR_DLS_VAL 0

//Override parameter: determines the override-value for LCR's BREAK

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_LCR_BREAK_VAL 0

//Override parameter: determines if the UART DLL,DLH parameters are overriden

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_DLL_DLH 0

//Override parameter: determines the override-value for DLL's value

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_DLL_VAL 1

//Override parameter: determines the override-value for DLH's value

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_DLH_VAL 0

//Override parameter: determines if the UART MCR parameters are overriden

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_MCR 0

//Override parameter: determines the override-value for MCR's SIRE

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_MCR_SIRE_VAL 0

//Override parameter: determines the override-value for MCR's AFCE

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_MCR_AFCE_VAL 0

//Override parameter: determines the override-value for MCR's LOOPBACK

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_MCR_LOOPBACK_VAL 0

//Override parameter: determines if Rx errors are to be sent to the UART/DUT

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_RX_ERROR 0

//Override parameter: determines if PARITY errors are to be sent to the UART/DUT

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_RX_PARITY_ERROR 0

//Override parameter: determines if FRAMING errors are to be sent to the UART/DUT

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_RX_FRAMING_ERROR 0

//Override parameter: determines if BREAK characters are to be sent to the UART/DUT

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_RX_BREAK_CHAR 0

//Override parameter: determines if the DCD/DSR/RI inputs are driven by SIOTxrx

`define soc_periph_dw_uart_UART_SIM_OVERRIDE_SIOTXRX_DRIVE_DCD_DSR_RI 0

//Instantiate legacy UART block in testbench

`define soc_periph_dw_uart_UART_INCLUDE_LEGACY_BLOCK 0







`define soc_periph_dw_uart_WIRE_SIN_TO_SIO 1



//Used to insert internal tests

//width for tfl and rfl count

`define soc_periph_dw_uart_CNT_WIDTH 5

//This parameter is enabled when UART_RS485_INTERFACE_EN=1.

// This parameter is set if Fractional Baud Rate Divisor support is enabled

// This parameter is set if 9-bit data support is enabled

//TX FIFO RW width. Width of data passed from TX block to FIFO

`define soc_periph_dw_uart_TXFIFO_RW 8

//RX FIFO RW width. Width of data passed from RX block to FIFO

`define soc_periph_dw_uart_RXFIFO_RW 10

//Extarnal TX RAM read/write data width based
// Normally TX RAM width is same as TX FIFO width since external RAM is used only
// for FIFOs. However, defined it here seperatly for flexibility since it is used for IO width

`define soc_periph_dw_uart_TX_RAM_DATA_WIDTH 8

//Extarnal RX RAM read/write data width based
// Normally RX RAM width is same as RX FIFO width since external RAM is used only
// for FIFOs. However, defined it here seperatly for flexibility since it is used for IO width

`define soc_periph_dw_uart_RX_RAM_DATA_WIDTH 10

//Control switch to enable ALT_UART instantiation

`define soc_periph_dw_uart_UART_USE_ALT_DUT 0

// This parameter is set if Fractional Baud Rate Divisor support is enabled

//RX FIFO RW width. Width of data passed from RX block to FIFO

`define soc_periph_dw_uart_SRBRN_REG_SIZE 8


//RX FIFO RW width. Width of data passed from RX block to FIFO

`define soc_periph_dw_uart_STHRN_REG_SIZE 8

//32 bit Base Address for APB Slave

`define soc_periph_dw_uart_APB3_SLV_BASE_ADDR 32'h0

//**************************************************************************************************
// Parameters to remove init and test ports in bcm
//**************************************************************************************************


//BCM defines
`define soc_periph_dw_uart_DWC_NO_TST_MODE

`define soc_periph_dw_uart_DWC_NO_CDC_INIT

`define soc_periph_dw_uart_DWC_BCM06_NO_DIAG_N

//==============================================================================
// End Guard
//==============================================================================
 `endif

