// ------------------------------------------------------------------------------
// 
// Copyright 2003 - 2020 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// 
// Component Name   : DW_apb_i2c
// Component Version: 2.03a
// Release Type     : GA
// ------------------------------------------------------------------------------

// 
// Release version :  2.03a
// File Version     :        $Revision: #4 $ 
// Revision: $Id: //dwh/DW_ocb/DW_apb_i2c/amba_dev/src/DW_apb_i2c_cc_constants.vh#4 $ 
//
//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`ifndef soc_periph_dw_i2c_0___GUARD__DW_APB_I2C_CC_CONSTANTS__VH__
`define soc_periph_dw_i2c_0___GUARD__DW_APB_I2C_CC_CONSTANTS__VH__


// Name:         SLAVE_INTERFACE_TYPE
// Default:      APB2
// Values:       APB2 (0), APB3 (1), APB4 (2)
// Enabled:      [<functionof> %item]
// 
// Select Register Interface type as APB2, APB3 or APB4. 
// By default, DW_apb_i2c supports APB2 interface.
`define soc_periph_dw_i2c_0_SLAVE_INTERFACE_TYPE 2


// Name:         SLVERR_RESP_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>0
// 
// Enable Slave Error response signaling. The component will refrain 
// From signaling an error response if this parameter is disabled.
`define soc_periph_dw_i2c_0_SLVERR_RESP_EN 0

//APB Interface has APB3 signals

`define soc_periph_dw_i2c_0_IC_HAS_APB3_IF_SIGNALS

//APB Interface has APB4 signals

`define soc_periph_dw_i2c_0_IC_HAS_APB4_IF_SIGNALS

//Component has slave error response enabled

// `define soc_periph_dw_i2c_0_IC_HAS_SLVERR_RESP_EN


// Name:         IC_ULTRA_FAST_MODE
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      [<functionof> %item]
// 
// This parameter is used to control whether DW_apb_i2c supports Ultra-Fast speed mode or not. 
//  
// If this Parameter is enabled, the Master 
//  - Disables the Arbitration, clock synchronization features. 
//  - Support only write transfers. 
//  - Does not check the validity of ACK/NACK for each byte. 
// The Slave  
//  - Supports only write transfers. 
//  - Disables the logic to generate ACK/NACK after the end of each byte. 
//  - Disables the logic to stretch the clock if RX-FIFO is full.
`define soc_periph_dw_i2c_0_IC_ULTRA_FAST_MODE 1'h0

//Internal Define for Ic CLK Frequency optimization

// `define soc_periph_dw_i2c_0_IC_ULTRA_FAST_MODE_EN


// Name:         IC_CLK_FREQ_OPTIMIZATION
// Default:      false (IC_ULTRA_FAST_MODE == 1 ? 1 : 0)
// Values:       false (0x0), true (0x1)
// Enabled:      ([<functionof> %item]) && (IC_ULTRA_FAST_MODE ==0)
// 
// This parameter is used to reduce the system clock frequency (ic_clk)  
// by reducing the internal latency required to generate the high period  
// and low period of the SCL line.
`define soc_periph_dw_i2c_0_IC_CLK_FREQ_OPTIMIZATION 1'h0

//Internal Define for Ic CLK Frequency optimization

// `define soc_periph_dw_i2c_0_IC_CLK_FREQ_OPTIMIZATION_EN


// Name:         IC_SMBUS
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      ([<functionof> %item]) && (IC_ULTRA_FAST_MODE ==0)
// 
// Controls whether DW_apb_i2c Master/Slave supports SMBus mode. 
// If checked, the DW_apb_i2c includes the SMBus mode related registers, real-time checks,  
// timeout interrupts, and SMBus optional signals. 
//  
// Note: If this parameter is selected (1), then the user can set the parameter 
// IC_MAX_SPEED_MODE to Standard mode(1) or Fast Mode/Fast Mode Plus (2).
`define soc_periph_dw_i2c_0_IC_SMBUS 1'h1


// Name:         IC_MULTI_SAR_EN
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      ([<functionof> %item]) && (IC_SMBUS == 1)
// 
// This parameter allows user to include Multiple SAR feature in the DW_apb_i2c.
`define soc_periph_dw_i2c_0_IC_MULTI_SAR_EN 1'h0


// Name:         IC_NUM_SARS
// Default:      2
// Values:       2 3 4
// Enabled:      IC_MULTI_SAR_EN == 1
// 
// This parameter determines the number of SARs supported by DW_apb_i2c.
`define soc_periph_dw_i2c_0_IC_NUM_SARS 2


// Name:         IC_CLK_STRETCH_MSAR
// Default:      false (IC_MULTI_SAR_EN == 1 ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      IC_MULTI_SAR_EN == 1
// 
// This parameter allows user to include clock stretching feature with Multiple SAR feature. 
// For more information on this, refer to the section "Multiple SAR Feature" of DW_apb_i2c databook.
`define soc_periph_dw_i2c_0_IC_CLK_STRETCH_MSAR 0





`define soc_periph_dw_i2c_0_IC_NUM_SARS_GE2



//SMBus General Get UDID command

`define soc_periph_dw_i2c_0_LOG2_IC_NUM_SARS 1

//Lower limit of number of clocks used for high count
//
//

`define soc_periph_dw_i2c_0_IC_HCNT_LO_LIMIT 16'h6

//Lower limit of number of clocks used for low count

`define soc_periph_dw_i2c_0_IC_LCNT_LO_LIMIT 16'h8


// Name:         IC_ADD_ENCODED_PARAMS
// Default:      true
// Values:       false (0x0), true (0x1)
// 
// Adding the encoded parameters gives firmware an easy and quick  
// way of identifying the DesignWare component within an I/O memory  
// map. Some critical design-time options determine how a driver  
// should interact with the peripheral. There is a minimal area  
// overhead by including these parameters. Allows a single driver  
// to be developed for each component which will be self-configurable. 
//  
// When bit 7 of the IC_COMP_PARAM_1 is read and contains a '1'  
// the encoded parameters can be read via software. If this bit  
// is a '0' then the entire register is '0' regardless of the  
// setting of any of the other parameters that are encoded in  
// the register's bits.  For details about this register, 
// see the IC_COMP_PARAM_1 register. 
//  
// Note: Unique drivers must be developed for each configuration of the 
// DW_apb_i2c. Based on the configuration, the registers in the IP can differ;  
// thus the same driver cannot be used with different configurations of the IP.
`define soc_periph_dw_i2c_0_IC_ADD_ENCODED_PARAMS 1'h1


// Name:         APB_DATA_WIDTH
// Default:      8
// Values:       8 16 32
// 
// Width of the APB data bus.
`define soc_periph_dw_i2c_0_APB_DATA_WIDTH 32

//Internal Define for APB Data Width 8

// `define soc_periph_dw_i2c_0_APB_DATA_WIDTH_8

//Internal Define for APB Data Width != 8

`define soc_periph_dw_i2c_0_APB_DATA_WIDTH_NOT_8

//Internal Define for APB Data Width 16

// `define soc_periph_dw_i2c_0_APB_DATA_WIDTH_16

//Internal Define for APB Data Width 32

`define soc_periph_dw_i2c_0_APB_DATA_WIDTH_32


// Name:         IC_MAX_SPEED_MODE
// Default:      Fast Mode or Fast Mode Plus ((IC_ULTRA_FAST_MODE ==1)? 1 : 
//               (IC_SMBUS == 1 ? 2 : 3))
// Values:       Standard Mode (0x1), Fast Mode or Fast Mode Plus (0x2), High Speed 
//               Mode (0x3)
// Enabled:      IC_ULTRA_FAST_MODE == 0
// 
// Maximum I2C mode supported. 
// Controls the reset value of the SPEED bit field [2:1] of the I2C Control Register (IC_CON). 
// Count registers are used to generate the outgoing clock SCL on the I2C interface.  
// For speed modes faster than the configured maximum speed mode, the corresponding 
// registers are not present in the top-level RTL. 
//  
// For unsupported speed modes those registers are not present as described below. 
//  - If this parameter is set to "Standard Mode" then the IC_FS_SCL_*, IC_HS_MADDR, and IC_HS_SCL_* registers are not 
//  present. 
//  - If this parameter is set to "Fast Mode" then the IC_HS_MADDR, and IC_HS_SCL_* registers are not present.
`define soc_periph_dw_i2c_0_IC_MAX_SPEED_MODE 2'h2


// Name:         IC_10BITADDR_MASTER
// Default:      false (IC_SMBUS == 1 ? 0 : 1)
// Values:       false (0x0), true (0x1)
// 
// Controls whether DW_apb_i2c supports 7 or 10 bit addressing on the I2C  
// interface after reset when acting as a master.  
// Controls reset value of part of Register IC_CON.  
// Master generated transfers will use this number of address bits. Additionally, it  
// can be reprogrammed by software by writing to the IC_CON register.
`define soc_periph_dw_i2c_0_IC_10BITADDR_MASTER 1'h0


// Name:         IC_RESTART_EN
// Default:      true
// Values:       false (0x0), true (0x1)
// 
// Controls the reset value of bit 5 (IC_RESTART_EN) in the 
// IC_CON register. By default, this parameter is checked, which allows 
// RESTART conditions to be sent when DW_apb_i2c is acting as a master. 
// Some older slaves do not support handling RESTART conditions; however, 
// RESTART conditions are used in several I2C operations. When the RESTART 
// is disabled, the DW_apb_i2c master is incapable of performing the following 
// functions: 
//  - Sending a START BYTE 
//  - Performing any high-speed mode operation 
//  - Performing direction changes in combined format mode 
//  - Performing a read operation with a 10-bit address
`define soc_periph_dw_i2c_0_IC_RESTART_EN 1'h1


// Name:         IC_10BITADDR_SLAVE
// Default:      false (IC_SMBUS == 1 ? 0 : 1)
// Values:       false (0x0), true (0x1)
// 
// Controls whether DW_apb_i2c slave supports 7 or 10 bit addressing on the I2C  
// interface after reset when acting as a slave.   
// Controls reset value of part of Register IC_CON.  
// The DW_apb_i2c module will respond to this number of address bits when 
// acting as a slave; it can be reprogrammed by software.
`define soc_periph_dw_i2c_0_IC_10BITADDR_SLAVE 1'h0



// Name:         IC_MASTER_MODE
// Default:      true
// Values:       false (0x0), true (0x1)
// 
// Controls whether DW_apb_i2c has its master enabled to be a master after reset.  
// This parameter controls the reset value of bit 0 of the I2C Control  
// Register (IC_CON). To enable the component to be a master, you must  
// write a 1 in bit 0 of the IC_CON register.  
//  
// Note: If this parameter is checked (1), then you must ensure that the  
// parameter IC_SLAVE_DISABLE is checked (1) as well.
`define soc_periph_dw_i2c_0_IC_MASTER_MODE 1'h1


// Name:         IC_SLAVE_DISABLE
// Default:      true
// Values:       false (0x0), true (0x1)
// 
// Controls whether DW_apb_i2c has its slave enabled or disabled after reset. 
// If checked, the DW_apb_i2c slave interface is disabled after reset. 
// The slave also can be disabled by programming a 1 into IC_CON[6]. 
// By default the slave is enabled. 
//  
// Note: If this parameter is unchecked (0), then you must ensure that the 
// parameter IC_MASTER_MODE is unchecked (0) as well.
`define soc_periph_dw_i2c_0_IC_SLAVE_DISABLE 1'h1

//A user is not allowed to assign any reserved addresses 
//or have the lower seven bits the same as a reserved 
//address.

// Name:         IC_DEFAULT_SLAVE_ADDR
// Default:      0x055
// Values:       0x000, ..., 0x3ff
// 
// Reset Value of DW_apb_i2c Slave Address.  
// Controls the reset value of Register (IC_SAR).  
// The default values cannot be any of the reserved  
// address locations: 0x00 to 0x07 or 0x78 to 0x7f.
`define soc_periph_dw_i2c_0_IC_DEFAULT_SLAVE_ADDR 10'h055

//A user is not allowed to assign any reserved addresses 
//or have the lower seven bits the same as a reserved 
//address.

// Name:         IC_DEFAULT_SLAVE_ADDR2
// Default:      0x056
// Values:       0x000, ..., 0x3ff
// Enabled:      (IC_MULTI_SAR_EN == 1) && (IC_NUM_SARS >= 2)
// 
// Reset Value of DW_apb_i2c Slave Address 2.  
// Controls the reset value of Register (IC_SAR2).  
// The default values cannot be any of the reserved  
// address locations: 0x00 to 0x07 or 0x78 to 0x7f.
`define soc_periph_dw_i2c_0_IC_DEFAULT_SLAVE_ADDR2 10'h056

//A user is not allowed to assign any reserved addresses 
//or have the lower seven bits the same as a reserved 
//address.

// Name:         IC_DEFAULT_SLAVE_ADDR3
// Default:      0x057
// Values:       0x000, ..., 0x3ff
// Enabled:      (IC_MULTI_SAR_EN == 1) && (IC_NUM_SARS >= 3)
// 
// Reset Value of DW_apb_i2c Slave Address 3.  
// Controls the reset value of Register (IC_SAR3).  
// The default values cannot be any of the reserved  
// address locations: 0x00 to 0x07 or 0x78 to 0x7f.
`define soc_periph_dw_i2c_0_IC_DEFAULT_SLAVE_ADDR3 10'h057

//A user is not allowed to assign any reserved addresses 
//or have the lower seven bits the same as a reserved 
//address.

// Name:         IC_DEFAULT_SLAVE_ADDR4
// Default:      0x058
// Values:       0x000, ..., 0x3ff
// Enabled:      (IC_MULTI_SAR_EN == 1) && (IC_NUM_SARS >= 4)
// 
// Reset Value of DW_apb_i2c Slave Address 4.  
// Controls the reset value of Register (IC_SAR4).  
// The default values cannot be any of the reserved  
// address locations: 0x00 to 0x07 or 0x78 to 0x7f.
`define soc_periph_dw_i2c_0_IC_DEFAULT_SLAVE_ADDR4 10'h058

//A user is not allowed assign any reserved addresses or have the lower 
//seven bits the same as a reserved address.

// Name:         IC_DEFAULT_TAR_SLAVE_ADDR
// Default:      0x055
// Values:       0x000, ..., 0x3ff
// 
// Reset value of DW_apb_i2c target slave address. Controls the reset value  
// of the IC_TAR bit field (9:0) of the I2C Target Address Register (IC_TAR).  
// The default values cannot be any of the reserved address locations: 
// 0x00 to 0x07 or 0x78 to 0x7f.
`define soc_periph_dw_i2c_0_IC_DEFAULT_TAR_SLAVE_ADDR 10'h055


// Name:         IC_HS_MASTER_CODE
// Default:      0x1
// Values:       0x0, ..., 0x7
// Enabled:      (IC_MAX_SPEED_MODE == 3) && (IC_ULTRA_FAST_MODE ==0)
// 
// High Speed mode master code of the DW_apb_i2c block. 
// Controls the reset value of I2C HS Master Mode Code Address Register (IC_HS_MADDR). 
// This is a unique code that alerts other masters on the I2C  
// bus that a high-speed mode transfer is going to begin. For more information 
// about this code, refer to "Multiple Master Arbitration" section in data 
// book.
`define soc_periph_dw_i2c_0_IC_HS_MASTER_CODE 3'h1


// Name:         IC_TX_BUFFER_DEPTH
// Default:      8
// Values:       2, ..., 256
// 
// Depth of transmit buffer. The buffer is 9 bits wide; 
// 8 bits for the data, and 1 bit for the read or write command.
`define soc_periph_dw_i2c_0_IC_TX_BUFFER_DEPTH 8


// Name:         IC_RX_BUFFER_DEPTH
// Default:      8
// Values:       2, ..., 256
// 
// Depth of receive buffer, the buffer is 8 bits wide.
`define soc_periph_dw_i2c_0_IC_RX_BUFFER_DEPTH 8

//Receive data width of FIFO

`define soc_periph_dw_i2c_0_RX_ABW 3


`define soc_periph_dw_i2c_0_RX_ABW_P1 4

//Write data width of FIFO

`define soc_periph_dw_i2c_0_TX_ABW 3


`define soc_periph_dw_i2c_0_TX_ABW_P1 4


// Name:         IC_INTR_POL
// Default:      true
// Values:       false (0x0), true (0x1)
// 
// Configures the active level of the output interrupt lines.
`define soc_periph_dw_i2c_0_IC_INTR_POL 1'h1


// Name:         IC_INTR_IO
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// If unchecked, each interrupt source has its own output. If 
// checked, all interrupt sources are combined into a single output.
`define soc_periph_dw_i2c_0_IC_INTR_IO 1'h0

`define soc_periph_dw_i2c_0_IC_HAS_INTR_IO0_POL1



// Name:         IC_HAS_DMA
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Configures the inclusion of DMA handshaking interface signals. 
// When checked, includes the DMA handshaking interface signals 
// at the top-level I/O. For more information about these signals,  
// see "Signal Descriptions" in data book.
`define soc_periph_dw_i2c_0_IC_HAS_DMA 1'h0


//DW_apb_i2c module version ID

`define soc_periph_dw_i2c_0_IC_VERSION_ID 32'h3230332a


// Name:         IC_TX_TL
// Default:      0x0
// Values:       0x0, ..., IC_TX_BUFFER_DEPTH-1
// 
// Reset value for threshold level of transmit buffer. 
// This parameter controls the reset value of the I2C  
// Transmit FIFO Threshold Level Register (IC_TX_TL).
`define soc_periph_dw_i2c_0_IC_TX_TL 8'h0


// Name:         IC_RX_TL
// Default:      0x0
// Values:       0x0, ..., IC_RX_BUFFER_DEPTH-1
// 
// Reset value for threshold level of receive buffer. 
// This parameter controls the reset value of the I2C  
// Receive FIFO Threshold Level Register (IC_RX_TL).
`define soc_periph_dw_i2c_0_IC_RX_TL 8'h0


// Name:         IC_USE_COUNTS
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Determines whether *CNT values are provided directly or by specifying the ic_clk  
// clock frequency and letting coreConsultant (or coreAssembler) calculate the count values. 
//  
// When this parameter is checked, the reset values of the *CNT registers are specified by 
// the corresponding *COUNT configuration parameters which may be user-defined or derived  
// (see standard, fast, fast mode plus, and high speed mode parameters later in this table).  
//  
// When unchecked (default setting), the reset values of the *CNT registers are calculated 
// from the configuration parameter IC_CLOCK_PERIOD. 
//  
// Note: For fast mode plus, reprogram the IC_FS_SCL_*CNT register to achieve 
// the required data rate when unchecked.
`define soc_periph_dw_i2c_0_IC_USE_COUNTS 1'h0


// Name:         IC_CLOCK_PERIOD
// Default:      100 ([<functionof> IC_MAX_SPEED_MODE IC_ULTRA_FAST_MODE])
// Values:       2, ..., 2147483647
// Enabled:      IC_USE_COUNTS == 0
// 
// Specifies the period of incoming ic_clk, used to generate outgoing I2C 
// interface SCL clock. (ns integers only) 
//  
// When the count values are used to generate the IC_CLOCK_PERIOD then 
// the IC_MAX_SPEED_MODE setting determines the actual period 
//  
//   IC_MAX_SPEED_MODE = Standard => 500ns 
//  
//   IC_MAX_SPEED_MODE = Fast     => 100ns 
//  
//   IC_MAX_SPEED_MODE = High     => 10ns 
//  
//   IC_ULTRA_FAST_MODE = 1       => 25ns 
//  
// Note: For fast mode plus, user has to reprogram the IC_FS_SCL_*CNT register to achieve required data rate.
`define soc_periph_dw_i2c_0_IC_CLOCK_PERIOD 100


// Name:         IC_SS_SCL_HIGH_COUNT
// Default:      0x0028 ([<functionof> IC_USE_COUNTS IC_HCNT_LO_LIMIT 
//               IC_CLOCK_PERIOD])
// Values:       IC_HCNT_LO_LIMIT, ..., 0xffff
// Enabled:      (IC_USE_COUNTS==1) && (IC_ULTRA_FAST_MODE ==0)
// 
// Reset value of Standard Speed I2C Clock SCL High Count 
// register (IC_SS_SCL_HCNT). The value must be calculated  
// based on the I2C data rate desired and I2C clock frequency.  
// When parameter IC_USE_COUNTS = 0, this parameter is automatically calculated using the  
// IC_CLOCK_PERIOD parameter. For more information, see the IC_SS_SCL_HCNT register.
`define soc_periph_dw_i2c_0_IC_SS_SCL_HIGH_COUNT 16'h0028


// Name:         IC_SS_SCL_LOW_COUNT
// Default:      0x002f ([<functionof> IC_USE_COUNTS IC_LCNT_LO_LIMIT 
//               IC_CLOCK_PERIOD])
// Values:       IC_LCNT_LO_LIMIT, ..., 0xffff
// Enabled:      (IC_USE_COUNTS==1) && (IC_ULTRA_FAST_MODE ==0)
// 
// Reset value of Standard Speed I2C Clock SCL Low Count register (IC_SS_SCL_LCNT). 
// Value must be calculated based on I2C data rate desired and I2C clock frequency. 
// When parameter IC_USE_COUNTS = 0, this parameter is automatically calculated using  
// the IC_CLOCK_PERIOD parameter. For more information, see IC_SS_SCL_LCNT register.
`define soc_periph_dw_i2c_0_IC_SS_SCL_LOW_COUNT 16'h002f


// Name:         IC_FS_SCL_HIGH_COUNT
// Default:      0x0006 ([<functionof> IC_MAX_SPEED_MODE IC_USE_COUNTS 
//               IC_HCNT_LO_LIMIT IC_CLOCK_PERIOD])
// Values:       IC_HCNT_LO_LIMIT, ..., 0xffff
// Enabled:      (IC_MAX_SPEED_MODE>=2 && IC_USE_COUNTS==1) && 
//               (IC_ULTRA_FAST_MODE==0)
// 
// Reset value of Fast Mode or Fast Mode Plus I2C Clock SCL High Count register (IC_FS_SCL_HCNT). 
// The value must be calculated based on I2C data rate desired and I2C clock frequency. 
// When parameter IC_USE_COUNTS = 0, this parameter is automatically calculated using  
// the IC_CLOCK_PERIOD parameter. For more information, see IC_FS_SCL_HCNT register.
`define soc_periph_dw_i2c_0_IC_FS_SCL_HIGH_COUNT 16'h0006


// Name:         IC_FS_SCL_LOW_COUNT
// Default:      0x000d ([<functionof> IC_MAX_SPEED_MODE IC_USE_COUNTS 
//               IC_LCNT_LO_LIMIT IC_CLOCK_PERIOD])
// Values:       IC_LCNT_LO_LIMIT, ..., 0xffff
// Enabled:      (IC_MAX_SPEED_MODE>=2 && IC_USE_COUNTS==1) && 
//               (IC_ULTRA_FAST_MODE==0)
// 
// Reset value of Fast Mode or Fast Mode Plus I2C Clock SCL Low Count register (IC_FS_SCL_LCNT). 
// The value must be calculated based on I2C data rate desired and I2C clock frequency. 
// When parameter IC_USE_COUNTS = 0, this parameter is automatically calculated using  
// the IC_CLOCK_PERIOD parameter. For more information, see the IC_FS_SCL_LCNT register
`define soc_periph_dw_i2c_0_IC_FS_SCL_LOW_COUNT 16'h000d


// Name:         IC_CAP_LOADING
// Default:      100
// Values:       100 400
// Enabled:      (IC_MAX_SPEED_MODE==3) && (IC_ULTRA_FAST_MODE ==0)
// 
// For high speed mode, the bus loading affects the high and low 
// pulse width of SCL.
`define soc_periph_dw_i2c_0_IC_CAP_LOADING 100


// Name:         IC_HS_SCL_HIGH_COUNT
// Default:      0x0006 ([<functionof> IC_MAX_SPEED_MODE IC_USE_COUNTS 
//               IC_HCNT_LO_LIMIT IC_CLOCK_PERIOD IC_CAP_LOADING])
// Values:       IC_HCNT_LO_LIMIT, ..., 0xffff
// Enabled:      (IC_MAX_SPEED_MODE==3 && IC_USE_COUNTS==1) && 
//               (IC_ULTRA_FAST_MODE==0)
// 
// Reset value of High Speed I2C Clock SCL High Count register (IC_HS_SCL_HCNT). 
// The value must be calculated based on I2C data rate desired and high speed 
// I2C clock frequency. When parameter IC_USE_COUNTS = 0, this parameter is  
// automatically calculated using the IC_CLOCK_PERIOD parameter.  
// For more information, see IC_HS_SCL_HCNT register.
`define soc_periph_dw_i2c_0_IC_HS_SCL_HIGH_COUNT 16'h0006


// Name:         IC_HS_SCL_LOW_COUNT
// Default:      0x0008 ([<functionof> IC_MAX_SPEED_MODE IC_USE_COUNTS 
//               IC_LCNT_LO_LIMIT IC_CLOCK_PERIOD IC_CAP_LOADING])
// Values:       IC_LCNT_LO_LIMIT, ..., 0xffff
// Enabled:      (IC_MAX_SPEED_MODE==3 && IC_USE_COUNTS==1) && 
//               (IC_ULTRA_FAST_MODE==0)
// 
// Reset value of High Speed I2C Clock SCL Low Count register (IC_HS_SCL_LCNT). 
// The value must be calculated based on I2C data rate and I2C clock 
// frequency. 
// When parameter IC_USE_COUNTS = 0, this parameter is automatically calculated using  
// the IC_CLOCK_PERIOD parameter. For more information, see IC_HS_SCL_LCNT register.
`define soc_periph_dw_i2c_0_IC_HS_SCL_LOW_COUNT 16'h0008


// Name:         IC_HC_COUNT_VALUES
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// By checking this parameter, the *CNT registers are set to read 
// only. Unchecking this parameter (default setting) allows the *CNT registers to 
// be writable. 
//  
// Regardless of the setting, the *CNT registers are always readable and 
// have reset values from the corresponding *COUNT configuration parameters, which 
// may be user defined or derived (see standard, fast, fast mode plus, or high 
// speed mode parameters later in this table). 
//  
// Note: Since the DW_apb_i2c uses the same high and low count registers for fast mode and fast mode plus operation,  
// if this parameter is checked (1) the IC_FS_SCL_*CNT registers are hard coded to either one of the fast mode and fast 
// mode plus.  
// Consequently, DW_apb_i2c can operate in either fast mode or fast mode plus, but not in both modes simultaneously. 
//  
// For fast mode plus, it is recommended that this parameter be Unchecked (0).
`define soc_periph_dw_i2c_0_IC_HC_COUNT_VALUES 1'h0


`define soc_periph_dw_i2c_0_IDENT 2'h0

//Asynchronous clock relationship

`define soc_periph_dw_i2c_0_ASYNC 2'h1

//Synchronous clock relationship

`define soc_periph_dw_i2c_0_SYNC 2'h3


// Name:         IC_CLK_TYPE
// Default:      Asynchronous (0x1)
// Values:       Identical (0x0), Asynchronous (0x1)
// 
// Specifies the relationship between pclk and ic_clk 
//  
// Identical (0): clocks are identical; no meta-stability flops 
// used for data passing between clock domains. 
//  
// Asynchronous (1): clocks may be completely asynchronous to 
// each other, meta-stability flops are required for data passing between clock domains.
`define soc_periph_dw_i2c_0_IC_CLK_TYPE 2'h1


`define soc_periph_dw_i2c_0_IC_SYNC_DEPTH 2


`define soc_periph_dw_i2c_0_IC_VERIF_EN 1


// Name:         IC_HAS_ASYNC_FIFO
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      IC_CLK_TYPE==ASYNC
// 
// This parameter controls whether DW_apb_i2c consist of Asynchronous or Synchronous 
// FIFO's for the Transmit and Receive Data Buffers.
`define soc_periph_dw_i2c_0_IC_HAS_ASYNC_FIFO 1'h0


//Modified Depth of the Transmit buffer

`define soc_periph_dw_i2c_0_IC_TX_BUFFER_MOD_DEPTH 8

//Modified Depth of the Receive buffer

`define soc_periph_dw_i2c_0_IC_RX_BUFFER_MOD_DEPTH 8

`define soc_periph_dw_i2c_0_IC_HAS_ASYNC_CLK

//Setting up a clock period for the I2C.

`define soc_periph_dw_i2c_0_IC_CLK_FREQ 100

//LHS of Paddr bus

`define soc_periph_dw_i2c_0_IC_ADDR_SLICE_LHS 4'h7

//LHS of Paddr bus

`define soc_periph_dw_i2c_0_MAX_APB_DATA_WIDTH 6'h20


// Name:         I2C_DYNAMIC_TAR_UPDATE
// Default:      false
// Values:       false (0), true (1)
// 
// When checked, allows the IC_TAR register to be updated 
// dynamically. Setting this parameter affects the operation  
// of DW_apb_i2c when it is in master mode. For more details,  
// see "Master Mode Operation".
`define soc_periph_dw_i2c_0_I2C_DYNAMIC_TAR_UPDATE 0


`define soc_periph_dw_i2c_0_IC_HAS_MST_ON_HOLD_INTR_OR_SMBUS


// Name:         IC_SLV_DATA_NACK_ONLY
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      IC_ULTRA_FAST_MODE ==0
// 
// Enables an additional register which controls whether the DW_apb_i2c generates a NACK 
// after a data byte has been transferred to it. This NACK generation only occurs when 
// the DW_apb_i2c is a Slave-Receiver. If this register is set to a value of 1, it can 
// only generate a NACK after a data byte is received; hence, the data transfer is aborted. 
// Also, the data received is not pushed to the receive buffer. 
//  
// When the register is set to a value of 0, it generates NACK/ACK depending on  
// normal criteria. 
// If this option is selected, the default value of the register IC_SLV_DATA_NACK_ONLY is always 0. 
// The register must be explicitly programmed to a value of 1 if NACKs are to be generated. The 
// register can only be written to successfully if DW_apb_i2c is disabled (IC_ENABLE[0] = 0) or the  
// slave part is inactive (IC_STATUS[6] = 0).
`define soc_periph_dw_i2c_0_IC_SLV_DATA_NACK_ONLY 1'h0




// Name:         IC_RX_FULL_GEN_NACK
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      (IC_ULTRA_FAST_MODE ==0) && (IC_SLV_DATA_NACK_ONLY ==0)
// 
// This parameter enables DW_apb_i2c in Slave mode to generate NACK for a data byte received  
// when Receive FIFO is physically full. The new data byte will not be pushed to the Receive 
// FIFO, hence no overflow happens and rx_over interrupt will not be set. 
// This works only when DW_apb_i2c is in Slave/Receiver mode (data being written 
// to the slave) and is not applicable in Master mode.
`define soc_periph_dw_i2c_0_IC_RX_FULL_GEN_NACK 1'h0




// Name:         IC_EMPTYFIFO_HOLD_MASTER_EN
// Default:      true (IC_SMBUS == 1 ? 1 : 0)
// Values:       false (0), true (1)
// 
// If this parameter is set, the master will only complete a transfer - that is issues a STOP -  
// when it finds a Tx FIFO entry tagged with a Stop bit. If the Tx FIFO becomes 
// empty and the last byte does not have the Stop bit set, the master stalls 
// the transfer by holding the SCL line low. 
//  
// If this parameter is not set, the master completes a transfer when the  
// Tx FIFO is empty. In SMbus Mode (IC_SMBUS=1), 
// IC_EMPTYFIFO_HOLD_MASTER_EN should be always enabled.
`define soc_periph_dw_i2c_0_IC_EMPTYFIFO_HOLD_MASTER_EN 1

`define soc_periph_dw_i2c_0_IC_HAS_EMPTYFIFO_HOLD


// Name:         IC_DEFAULT_SDA_SETUP
// Default:      0x64
// Values:       0x02, ..., 0xff
// Enabled:      IC_ULTRA_FAST_MODE ==0
// 
// Determines the reset value for the register IC_SDA_SETUP, which in 
// turn controls the time delay - in terms of number of ic_clk clock periods - introduced 
// in the rising edge of SCL, relative to SDA changing when a read-request is serviced. 
// The relevant I2C requirement is t[su:DAT] as detailed in the I2C Bus Specifications.
`define soc_periph_dw_i2c_0_IC_DEFAULT_SDA_SETUP 8'h64


// Name:         IC_DEFAULT_SDA_HOLD
// Default:      0x000001 ([<functionof> IC_USE_COUNTS IC_CLOCK_PERIOD 
//               IC_ULTRA_FAST_MODE])
// Values:       0x000001, ..., 0xffffff
// 
// Determines the reset value for the register IC_SDA_HOLD, which in 
// turn controls the SDA hold time implemented by DW_apb_i2c (when 
// transmitting or receiving, as either master or slave) 
// as a master/slave transmitter or Master/Slave Receiver). 
// The relevant I2C requirement is t[HD:DAT] as detailed in the I2C Bus Specifications. 
//  
// The programmed SDA hold time as transmitter cannot exceed at any time the 
// duration of the low part of scl. Therefore it is recommended that the configured 
// default value should not be larger than N_SCL_LOW-2, where N_SCL_LOW is 
// the duration of the low part of the scl period measured in ic_clk cycles, for the 
// maximum speed mode the component is configured for.
`define soc_periph_dw_i2c_0_IC_DEFAULT_SDA_HOLD 24'h000001


`define soc_periph_dw_i2c_0_IC_DEFAULT_SDA_TX_HOLD 16'h1


`define soc_periph_dw_i2c_0_IC_DEFAULT_SDA_RX_HOLD 8'h0


// Name:         IC_DEFAULT_ACK_GENERAL_CALL
// Default:      true
// Values:       false (0x0), true (0x1)
// Enabled:      IC_ULTRA_FAST_MODE == 0
// 
// This parameter determines the reset value for the register IC_ACK_GENERAL_CALL, which 
// in turn controls whether I2C general call addresses are to be responded or not.
`define soc_periph_dw_i2c_0_IC_DEFAULT_ACK_GENERAL_CALL 1'h1


// Name:         IC_RX_FULL_HLD_BUS_EN
// Default:      false ((IC_MULTI_SAR_EN == 1) ? 1 : 0)
// Values:       false (0x0), true (0x1)
// Enabled:      (IC_ULTRA_FAST_MODE ==0) && (IC_MULTI_SAR_EN == 0)
// 
// When the Rx FIFO is physically full to its RX_BUFFER_DEPTH,  
// this parameter provides a hardware method to hold the bus till Rx FIFO data  
// is read out and there is a space available in the FIFO. 
// This parameter can be used when DW_apb_i2c is either a slave-receiver (that 
// is, data is written to the device) or a master-receiver (that is, the device reads 
// data from a slave). 
//  
// Note: If parameter "IC_RX_FULL_GEN_NACK" is enabled, then setting this parameter 
// has no impact in slave-receiver mode since, the controller NACK's the Data byte if Rx-FIFO 
// has no empty space. 
//  
// Note: If this parameter is checked and bit 9 of the IC_CON register (RX_FIFO_FULL_HLD_CTRL) is programmed to HIGH, then 
// the RX_OVER interrupt is never set to 1  
// as the criteria to set this interrupt is never met. The RX_OVER interrupt can be found  
// in IC_INTR_STAT and IC_RAW_INTR_STAT registers. It is also an optional output signal, 
//  ic_rx_over_intr(_n).
`define soc_periph_dw_i2c_0_IC_RX_FULL_HLD_BUS_EN 1'h0




`define soc_periph_dw_i2c_0_IC_HAS_RX_HOLD



// Name:         IC_SLV_RESTART_DET_EN
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// When checked, allows the slave to detect and issue the restart interrupt when slave is  
// addressed. Setting this parameter affects the operation of DW_apb_i2c only when it is in slave mode.  
// This controls the "RESTART_DET" bit in the IC_RAW_INTR_STAT, IC_INTR_MASK, IC_INTR_STAT,  
// and IC_CLR_RESTART_DET registers.This also controls the ic_restart_det_intr(_n)  
// and ic_intr(_n) signals.
`define soc_periph_dw_i2c_0_IC_SLV_RESTART_DET_EN 1'h0




// Name:         IC_STOP_DET_IF_MASTER_ACTIVE
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      IC_ULTRA_FAST_MODE ==0
// 
// Controls whether DW_apb_i2c generates STOP_DET interrupt when master is active: 
//  - Checked (1): Allows the master to detect and issue the stop interrupt when master is active. 
//  - Unchecked (0): The master always detects and issues the stop interrupt irrespective of whether it is active. 
// This parameter affects the operation of DW_apb_i2c when it is in master mode.  
// This controls the STOP_DET bit of the IC_RAW_INTR_STAT, IC_INTR_MASK,   
// IC_INTR_STAT and IC_CLR_STOP_DET registers. This also controls the ic_stop_det_intr(_n) and  
// ic_intr(_n) signals.
`define soc_periph_dw_i2c_0_IC_STOP_DET_IF_MASTER_ACTIVE 1'h0




// Name:         IC_STAT_FOR_CLK_STRETCH
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      IC_ULTRA_FAST_MODE ==0
// 
// If this parameter is set, the DW_apb_i2c consists of status bits indicating 
// the reason for clock stretching in the IC_STATUS Register.
`define soc_periph_dw_i2c_0_IC_STAT_FOR_CLK_STRETCH 1'h0





// Name:         IC_TX_CMD_BLOCK
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Controls whether DW_apb_i2c transmits data on I2C bus as soon as data is available in  
// Tx FIFO. When checked, allows the master to hold the transmission of data on  
// I2C bus when Tx FIFO has data to transmit.
`define soc_periph_dw_i2c_0_IC_TX_CMD_BLOCK 1'h0



// Name:         IC_TX_CMD_BLOCK_DEFAULT
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      IC_TX_CMD_BLOCK==1
// 
// Controls whether DW_apb_i2c has its transmit command block enabled or disabled after reset. 
// If checked, the DW_apb_i2c blocks the transmission of data on I2C bus.
`define soc_periph_dw_i2c_0_IC_TX_CMD_BLOCK_DEFAULT 1'h0


// Name:         IC_FIRST_DATA_BYTE_STATUS
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Controls whether DW_apb_i2c generates FIRST_DATA_BYTE status bit in IC_DATA_CMD register. 
// When checked, the master/slave receiver to set the FIRST_DATA_BYTE status bit 
// in IC_DATA_CMD register to indicate whether the data present in IC_DATA_CMD register is  
// first data byte after the address phase of a receive transfer. 
//  
// Note: In the case when APB_DATA_WIDTH is set to 8, you must perform two 
// APB reads to the IC_DATA_CMD register to get status on bit 11.
`define soc_periph_dw_i2c_0_IC_FIRST_DATA_BYTE_STATUS 1'h0



// Name:         IC_AVOID_RX_FIFO_FLUSH_ON_TX_ABRT
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      IC_ULTRA_FAST_MODE ==0
// 
// This Parameter controls the Rx FIFO Flush during the Transmit Abort. 
// If this parameter is checked(1), only the Tx FIFO is flushed (not the Rx FIFO) 
// Flush on the Transmit Abort. 
// If this parameter is unchecked(0), both Tx FIFO and Rx FIFO are flushed on Transmit Abort.
`define soc_periph_dw_i2c_0_IC_AVOID_RX_FIFO_FLUSH_ON_TX_ABRT 1'h0



// Name:         IC_BUS_CLEAR_FEATURE
// Default:      true (IC_SMBUS==1 ? 1 : 0)
// Values:       false (0x0), true (0x1)
// Enabled:      IC_ULTRA_FAST_MODE ==0
// 
// This parameter will enable the Bus clear feature for the DW_apb_i2c core. 
//  
//  
// If this parameter is set: 
//  - If an SDA line is stuck at low for IC_SDA_STUCK_LOW_TIMEOUT period of ic_clk, DW_apb_i2c master generates a master 
//  transmit abort (IC_TX_ABRT_SOURCE[17]: ABRT_SDA_STUCK_AT_LOW) to indicate SDA stuck at low. 
// User can enable the SDA_STUCK_RECOVERY_EN (IC_ENABLE[3]) register bit to recover the SDA by sending at most 9 SCL 
// clocks. 
// If SDA line is recovered, then the master generates a STOP and auto clear the 'SDA_STUCK_RECOVERY_EN' register bit and 
// resume the normal I2C transfers. 
// If an SDA line is not recovered, then the master auto clears the SDA_STUCK_RECOVERY_EN register bit and asserts the 
// SDA_STUCK_NOT_RECOVERED (IC_STATUS[11]) status bit to indicate the SDA is not recovered after sending 9 SCL clocks which 
// intimate the user for system reset. 
//  - If SCL line is stuck at low for IC_SCL_STUCK_LOW_TIMEOUT period of ic_clk, DW_apb_i2c Master will generate an 
//  SCL_STUCK_AT_LOW (IC_INTR_RAW_STATUS[14]) interrupt to intimate the user for system reset.
`define soc_periph_dw_i2c_0_IC_BUS_CLEAR_FEATURE 1'h1

`define soc_periph_dw_i2c_0_IC_BUS_CLEAR_FEATURE_EN


// Name:         IC_SCL_STUCK_TIMEOUT_DEFAULT
// Default:      0xffffffff
// Values:       0x0, ..., 0xffffffff
// Enabled:      IC_BUS_CLEAR_FEATURE==1
// 
// Default value of the IC_SCL_STUCK_LOW_TIMEOUT Register.
`define soc_periph_dw_i2c_0_IC_SCL_STUCK_TIMEOUT_DEFAULT 32'hffffffff


// Name:         IC_SDA_STUCK_TIMEOUT_DEFAULT
// Default:      0xffffffff
// Values:       0x0, ..., 0xffffffff
// Enabled:      IC_BUS_CLEAR_FEATURE==1
// 
// Default value of the IC_SDA_STUCK_LOW_TIMEOUT Register.
`define soc_periph_dw_i2c_0_IC_SDA_STUCK_TIMEOUT_DEFAULT 32'hffffffff


// Name:         IC_DEVICE_ID
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      IC_ULTRA_FAST_MODE ==0
// 
// If this Parameter is enabled, the DW_apb_i2c slave includes a 24-bit  
// IC_DEVICE_ID Register to store the value of 
// Device-ID and transmits whenever master is requested. 
//  
// The Master mode includes a DEVICE_ID bit 13 in IC_TAR register to initiate 
// the Device ID read for a particular slave address mentioned in IC_TAR[6:0] 
// register.
`define soc_periph_dw_i2c_0_IC_DEVICE_ID 1'h0



// Name:         IC_DEVICE_ID_VALUE
// Default:      0x0
// Values:       0x0, ..., 0xffffff
// Enabled:      IC_DEVICE_ID==1
// 
// Device ID Value of the I2C Slave stored in the IC_DEVICE_ID Register (24 bit, MSB is transferred first 
// on the Device ID read from the master).
`define soc_periph_dw_i2c_0_IC_DEVICE_ID_VALUE 24'h0

`define soc_periph_dw_i2c_0_IC_SMBUS_EN


// Name:         IC_SMBUS_CLK_LOW_SEXT_DEFAULT
// Default:      0xffffffff
// Values:       0x0, ..., 0xffffffff
// Enabled:      IC_SMBUS==1
// 
// Default value of the IC_SMBUS_CLK_LOW_SEXT Register.
`define soc_periph_dw_i2c_0_IC_SMBUS_CLK_LOW_SEXT_DEFAULT 32'hffffffff


// Name:         IC_SMBUS_CLK_LOW_MEXT_DEFAULT
// Default:      0xffffffff
// Values:       0x0, ..., 0xffffffff
// Enabled:      IC_SMBUS==1
// 
// Default value of the IC_SMBUS_CLK_LOW_MEXT Register.
`define soc_periph_dw_i2c_0_IC_SMBUS_CLK_LOW_MEXT_DEFAULT 32'hffffffff


// Name:         IC_SMBUS_RST_IDLE_CNT_DEFAULT
// Default:      0xffff
// Values:       0x0, ..., 0xffff
// Enabled:      IC_SMBUS==1
// 
// Default value of the IC_SMBUS_THIGH_MAX_IDLE_COUNT Register.
`define soc_periph_dw_i2c_0_IC_SMBUS_RST_IDLE_CNT_DEFAULT 16'hffff


// Name:         IC_SMBUS_SUSPEND_ALERT
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      IC_SMBUS==1
// 
// This parameter controls whether DW_apb_i2c includes  
// Optional SMBus Suspend and Alert signals on the interface.
`define soc_periph_dw_i2c_0_IC_SMBUS_SUSPEND_ALERT 1'h0

//Internal Define for SMBus optional signals

// `define soc_periph_dw_i2c_0_IC_SMBUS_SUSPEND_ALERT_EN


// Name:         IC_OPTIONAL_SAR
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      (IC_SMBUS == 1) && (IC_MULTI_SAR_EN==0)
// 
// This parameter controls whether to include optional  
// Slave Address Register in SMBus Mode.
`define soc_periph_dw_i2c_0_IC_OPTIONAL_SAR 1'h0



// Name:         IC_OPTIONAL_SAR_DEFAULT
// Default:      0x0
// Values:       0x0, ..., 0x7f
// Enabled:      IC_OPTIONAL_SAR==1
// 
// Controls whether to include Optional Slave Address Register in 
// SMBus Mode. A user is not allowed to assign any reserved  
// addresses. The reserved address are as follows: 
//  
// 0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07 
//  
// 0x78 0x79 0x7a 0x7b 0x7c 0x7d 0x7e 0x7f
`define soc_periph_dw_i2c_0_IC_OPTIONAL_SAR_DEFAULT 7'h0


// Name:         IC_SMBUS_ARP
// Default:      0x0
// Values:       0x0, 0x1
// Enabled:      IC_SMBUS==1
// 
// Controls whether DW_apb_i2c includes logic to detect and 
// respond ARP commands in Slave mode. It also includes logic to 
// generate/validate the PEC byte at the end of the transfer in  
// Slave mode only.
`define soc_periph_dw_i2c_0_IC_SMBUS_ARP 1'h0



// Name:         IC_SMBUS_UDID_HC
// Default:      0x1
// Values:       0x0, 0x1
// Enabled:      IC_SMBUS_ARP==1
// 
// Controls whether Unique Device Identifier (UDID) used for Dynamic 
// Address Resolution process in SMBus ARP Mode is Hardcoded  
// (Upper 96-bits) or Complete UDID is Software Programmable.
`define soc_periph_dw_i2c_0_IC_SMBUS_UDID_HC 1'h1

//DMAC has Debug Ports Define 
`define soc_periph_dw_i2c_0_IC_SMBUS_HAS_UDID_HC

//`ifndef soc_periph_dw_i2c_0_IC_SMBUS_HAS_UDID_HC
//UDID width

`define soc_periph_dw_i2c_0_IC_SMBUS_UDID_BITS 128
//`endif


// Name:         IC_SMBUS_UDID_MSB
// Default:      0x0
// Values:       0x0, ..., 0xffffffffffffffffffffffff
// Enabled:      IC_SMBUS_ARP==1
// 
// If the parameter IC_SMBUS_UDID_HC is 1, stores the Static Unique  
// Device Identifier used for Dynamic Address Resolution process in  
// SMBus ARP Mode (Upper 96bits of UDID). 
// If the parameter IC_SMBUS_UDID_HC is 0, then this field is used as the 
// default value of the upper 96bits of the UDID Registers 
// {IC_SMBUS_UDID_WORD3, IC_SMBUS_UDID_WORD2, IC_SMBUS_UDID_WORD1}
`define soc_periph_dw_i2c_0_IC_SMBUS_UDID_MSB 96'h0


// Name:         IC_SMBUS_UDID_LSB_DEFAULT
// Default:      0xffffffff
// Values:       0x0, ..., 0xffffffff
// Enabled:      IC_SMBUS_ARP==1
// 
// If the parameter IC_SMBUS_UDID_HC is 1, specifies default value of  
// the IC_SMBUS_UDID_LSB register used for Dynamic Address Resolution  
// process in SMBus ARP mode (Lower 32bits of UDID). 
// If the parameter IC_SMBUS_UDID_HC is 0, specifies default value of  
// the IC_SMBUS_UDID_WORD0 register used for Dynamic Address Resolution  
// process in SMBus ARP mode (Lower 32bits of UDID).
`define soc_periph_dw_i2c_0_IC_SMBUS_UDID_LSB_DEFAULT 32'hffffffff



// Name:         IC_PERSISTANT_SLV_ADDR_DEFAULT
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      IC_SMBUS_ARP==1
// 
// Default value of the Persistent Slave Address register bit in IC_CON Register.
`define soc_periph_dw_i2c_0_IC_PERSISTANT_SLV_ADDR_DEFAULT 1'h0


// Name:         IC_PERSISTANT_SLV_ADDR2_DEFAULT
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      (IC_MULTI_SAR_EN == 1) && (IC_NUM_SARS >= 2) && (IC_SMBUS_ARP==1)
// 
// Default value of the Persistent Slave Address register (IC_SAR2) bit in IC_CON Register.
`define soc_periph_dw_i2c_0_IC_PERSISTANT_SLV_ADDR2_DEFAULT 1'h0


// Name:         IC_PERSISTANT_SLV_ADDR3_DEFAULT
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      (IC_MULTI_SAR_EN == 1) && (IC_NUM_SARS >= 3) && (IC_SMBUS_ARP==1)
// 
// Default value of the Persistent Slave Address register (IC_SAR3) bit in IC_CON Register.
`define soc_periph_dw_i2c_0_IC_PERSISTANT_SLV_ADDR3_DEFAULT 1'h0


// Name:         IC_PERSISTANT_SLV_ADDR4_DEFAULT
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      (IC_MULTI_SAR_EN == 1) && (IC_NUM_SARS >= 4) && (IC_SMBUS_ARP==1)
// 
// Default value of the Persistent Slave Address register (IC_SAR4) bit in IC_CON Register.
`define soc_periph_dw_i2c_0_IC_PERSISTANT_SLV_ADDR4_DEFAULT 1'h0


// Name:         IC_UFM_SCL_HIGH_COUNT
// Default:      0x0006 ([<functionof> IC_USE_COUNTS IC_HCNT_LO_LIMIT 
//               IC_CLOCK_PERIOD IC_ULTRA_FAST_MODE])
// Values:       IC_HCNT_LO_LIMIT, ..., 0xffff
// Enabled:      (IC_USE_COUNTS==1) && (IC_ULTRA_FAST_MODE==1)
// 
// Reset value of Ultra-Fast Speed I2C Clock SCL High Count register (IC_UFM_SCL_HCNT).  
// The value must be calculated based on the I2C data rate desired and I2C clock frequency. 
// When parameter IC_USE_COUNTS = 0, this parameter is automatically calculated using the IC_CLOCK_PERIOD parameter.
`define soc_periph_dw_i2c_0_IC_UFM_SCL_HIGH_COUNT 16'h0006


// Name:         IC_UFM_SCL_LOW_COUNT
// Default:      0x0008 ([<functionof> IC_USE_COUNTS IC_LCNT_LO_LIMIT 
//               IC_CLOCK_PERIOD IC_ULTRA_FAST_MODE])
// Values:       IC_LCNT_LO_LIMIT, ..., 0xffff
// Enabled:      (IC_USE_COUNTS==1) && (IC_ULTRA_FAST_MODE==1)
// 
// Reset value of Ultra-Fast Speed I2C Clock SCL Low Count register (IC_UFM_SCL_LCNT).  
// The value must be calculated based on the I2C data rate desired and I2C clock frequency. 
// When parameter IC_USE_COUNTS = 0, this parameter is automatically calculated using the IC_CLOCK_PERIOD parameter.
`define soc_periph_dw_i2c_0_IC_UFM_SCL_LOW_COUNT 16'h0008


// Name:         IC_UFM_TBUF_CNT_DEFAULT
// Default:      0x8 ([<functionof> IC_USE_COUNTS IC_CLOCK_PERIOD])
// Values:       0x0, ..., 0xffff
// Enabled:      (IC_USE_COUNTS==1) && (IC_ULTRA_FAST_MODE==1)
// 
// Default value of the IC_UFM_TBUF_CNT Register. This parameter is active when the IC_USE_COUNTS and 
// IC_ULTRA_FAST_MODE parameters are checked (1); otherwise, this value is automatically calculated  
// using the IC_CLOCK_PERIOD parameter.
`define soc_periph_dw_i2c_0_IC_UFM_TBUF_CNT_DEFAULT 16'h8
// -----------------------------------------------------------
// -- Regsiter bit Width macros
// -----------------------------------------------------------
//ic_con register bit width

`define soc_periph_dw_i2c_0_IC_CON_RS 12

//SMB extension for ic_con register bit width

`define soc_periph_dw_i2c_0_IC_SMBUS_CON_EXT_RS 4

//ic_tar register bit width

`define soc_periph_dw_i2c_0_IC_TAR_RS 12


`define soc_periph_dw_i2c_0_IC_TAR_RS_INT 12

//ic_sar optional register bit width

`define soc_periph_dw_i2c_0_IC_SAR_OPT_RS 7

//ic_sar register bit width

`define soc_periph_dw_i2c_0_IC_SAR_RS 10

//ic_hs_maddr register bit width

`define soc_periph_dw_i2c_0_IC_HS_MADDR_RS 3

//ic_data_cmd Receiver register bit width

`define soc_periph_dw_i2c_0_IC_DATA_CMD_RS 11

//ic_data_cmd Transmit register bit width

`define soc_periph_dw_i2c_0_IC_DATA_TX_CMD_RS 11

//ic_data_cmd register valid data bit width

`define soc_periph_dw_i2c_0_IC_DATA_RS 8

//ic_data_cmd register register FIFO bit width

`define soc_periph_dw_i2c_0_IC_DATA_FIFO_RS 8

//ic_ss_hcnt register bit width

`define soc_periph_dw_i2c_0_IC_SS_HCNT_RS 16

//ic_ss_lcnt register bit width

`define soc_periph_dw_i2c_0_IC_SS_LCNT_RS 16

//ic_fs_hcnt register bit width

`define soc_periph_dw_i2c_0_IC_FS_HCNT_RS 16

//ic_fs_lcnt register bit width

`define soc_periph_dw_i2c_0_IC_FS_LCNT_RS 16

//ic_hs_hcnt register bit width

`define soc_periph_dw_i2c_0_IC_HS_HCNT_RS 16

//ic_hs_lcnt register bit width

`define soc_periph_dw_i2c_0_IC_HS_LCNT_RS 16

//ic_intr_stat register bit width

`define soc_periph_dw_i2c_0_IC_INTR_STAT_RS 15

//ic_intr_mask register bit width

`define soc_periph_dw_i2c_0_IC_INTR_MASK_RS 15

//ic_raw_intr_stat register bit width

`define soc_periph_dw_i2c_0_IC_RAW_INTR_STAT_RS 15

//ic_smbus_intr_* register bit width

`define soc_periph_dw_i2c_0_IC_SMBUS_INTR_RS 4

//ic_rx_tl register bit width

`define soc_periph_dw_i2c_0_IC_RX_TL_RS 8

//ic_tx_tl register bit width

`define soc_periph_dw_i2c_0_IC_TX_TL_RS 8

//ic_clr_intr register bit width

`define soc_periph_dw_i2c_0_IC_CLR_INTR_RS 1

//ic_clr_rx_under register bit width

`define soc_periph_dw_i2c_0_IC_CLR_RX_UNDER_RS 1

//ic_clr_rx_over register bit width

`define soc_periph_dw_i2c_0_IC_CLR_RX_OVER_RS 1

//ic_clr_tx_over register bit width

`define soc_periph_dw_i2c_0_IC_CLR_TX_OVER_RS 1

//ic_clr_rd_req register bit width

`define soc_periph_dw_i2c_0_IC_CLR_RD_REQ_RS 1

//ic_clr_tx_abrt register bit width

`define soc_periph_dw_i2c_0_IC_CLR_TX_ABRT_RS 1

//ic_clr_rx_done register bit width

`define soc_periph_dw_i2c_0_IC_CLR_RX_DONE_RS 1

//ic_clr_activity register bit width

`define soc_periph_dw_i2c_0_IC_CLR_ACTIVITY_RS 1

//ic_clr_stop_det register bit width

`define soc_periph_dw_i2c_0_IC_CLR_STOP_DET_RS 1

//ic_clr_stop_det register bit width

`define soc_periph_dw_i2c_0_IC_CLR_RESTART_DET_RS 1

//ic_clr_start_det register bit width

`define soc_periph_dw_i2c_0_IC_CLR_START_DET_RS 1

//ic_clr_gen_call register bit width

`define soc_periph_dw_i2c_0_IC_CLR_GEN_CALL_RS 1

//ic_enable register bit width

`define soc_periph_dw_i2c_0_IC_ENABLE_RS 4


`define soc_periph_dw_i2c_0_IC_ENABLE_SMBUS_RS 3

//ic_enable internal register bit width for sync module

`define soc_periph_dw_i2c_0_IC_ENABLE_RS_INT 2

// ic_status register bit width

`define soc_periph_dw_i2c_0_IC_STATUS_RS 12

//ic_sreset register bit width

`define soc_periph_dw_i2c_0_IC_SRESET_RS 3

//ic_device_id register width

//ic_tx_abrt_source register bit width

`define soc_periph_dw_i2c_0_IC_TX_ABRT_SOURCE_RS 18

//PAT START
//ic_slv_data_nack_only register bit width

`define soc_periph_dw_i2c_0_IC_SLV_DATA_NACK_ONLY_RS 1
//PAT END

//ic_version_id register bit width

`define soc_periph_dw_i2c_0_IC_VERSION_ID_RS 32

//ic_version_id register bit width

`define soc_periph_dw_i2c_0_IC_DMA_CR_RS 2

//ic_version_id register bit width

`define soc_periph_dw_i2c_0_IC_DMA_TDLR_RS 3

//ic_version_id register bit width

`define soc_periph_dw_i2c_0_IC_DMA_RDLR_RS 3

//SDA setup time setting; used when SCL is held

`define soc_periph_dw_i2c_0_IC_SDA_SETUP_RS 8

//internal SDA hold time setting; used when I2C acts as transmitter

`define soc_periph_dw_i2c_0_IC_SDA_TX_HOLD_RS 16

//internal SDA hold time setting; used when I2C acts as receiver

`define soc_periph_dw_i2c_0_IC_SDA_RX_HOLD_RS 8

//SDA hold time setting; used when I2cis acting as either Master or receiver

`define soc_periph_dw_i2c_0_IC_SDA_HOLD_RS 24

//Acknowledgement of General Call addresses

`define soc_periph_dw_i2c_0_IC_ACK_GENERAL_CALL_RS 1

//IC_ENABLE_STATUS

`define soc_periph_dw_i2c_0_IC_ENABLE_STATUS_RS 3

//IC_SMBUS_TIMEOUT Register size

`define soc_periph_dw_i2c_0_IC_SMBUS_TIMEOUT_RS 32

//IC_SMBUS_RST_IDLE_CNT Register size

`define soc_periph_dw_i2c_0_IC_SMBUS_RST_IDLE_CNT_RS 16

//IC_SMBUS_SUS_ALERT_CTRL Register size

`define soc_periph_dw_i2c_0_IC_SMBUS_SUS_ALERT_RS 2

//IC_SMBUS_UDID_LSB Register size

`define soc_periph_dw_i2c_0_IC_SMBUS_UDID_LSB_RS 32

//ic_con_smbus register width value

`define soc_periph_dw_i2c_0_IC_SMBUS_UDID_RS 144

//SMBus Host Slave Address

`define soc_periph_dw_i2c_0_IC_SMBUS_HOST_SLAVE_ADDRESS 7'h8

//SMBus write Device Default Address

`define soc_periph_dw_i2c_0_IC_SMBUS_DEVICE_DEFAULT_ADDRESS 8'hc2

//SMBus Read Device Default Address

`define soc_periph_dw_i2c_0_IC_SMBUS_RD_DEVICE_DEFAULT_ADDRESS 8'hc3

//SMBus Prepare to ARP command

`define soc_periph_dw_i2c_0_IC_SMBUS_PREPARE_TO_ARP_CMD 8'h1

//SMBus General Reset command

`define soc_periph_dw_i2c_0_IC_SMBUS_GEN_RESET_CMD 8'h2

//SMBus General Get UDID command

`define soc_periph_dw_i2c_0_IC_SMBUS_GEN_GET_UDID_CMD 8'h3

//SMBus General Assign address command

`define soc_periph_dw_i2c_0_IC_SMBUS_ASSGN_ADDR_CMD 8'h4

//SMBus UDID byte count

`define soc_periph_dw_i2c_0_IC_SMBUS_UDID_BYTE_COUNT 5'h11

//SMBus UDID byte count plus 1

`define soc_periph_dw_i2c_0_IC_SMBUS_UDID_BYTE_COUNT_PLS1 5'h12

//SMBus UDID byte count width

`define soc_periph_dw_i2c_0_IC_SMBUS_UDID_BYTE_COUNT_LOG2 5

//SMBUS Alert Response address

`define soc_periph_dw_i2c_0_SMB_ALERT_ADDRESS 7'hc

// -----------------------------------------------------------
// -- Register reset value  macros
// -----------------------------------------------------------
//ic_con register reset value

`define soc_periph_dw_i2c_0_IC_CON_IN 20'h65

//ic_tar register reset value

`define soc_periph_dw_i2c_0_IC_TAR_IN 13'h55

//ic_tar register reset value

`define soc_periph_dw_i2c_0_IC_TAR_IN_RAL 44'h55

//ic_sar register reset value

`define soc_periph_dw_i2c_0_IC_SAR_IN 10'h55

//ic_sar2 register reset value

`define soc_periph_dw_i2c_0_IC_SAR2_IN 10'h56



//ic_sar register reset value

`define soc_periph_dw_i2c_0_IC_SAR_OPT_IN 7'h0

//ic_hs_maddr register reset value

`define soc_periph_dw_i2c_0_IC_HS_MADDR_IN 3'h1

//ic_ss_hcnt register reset value

`define soc_periph_dw_i2c_0_IC_SS_HCNT_IN 16'h28

//ic_ss_lcnt register reset value

`define soc_periph_dw_i2c_0_IC_SS_LCNT_IN 16'h2f

//ic_fs_hcnt register reset value

`define soc_periph_dw_i2c_0_IC_FS_HCNT_IN 16'h6

//ic_fs_lcnt register reset value

`define soc_periph_dw_i2c_0_IC_FS_LCNT_IN 16'hd

//ic_hs_hcnt register reset value

`define soc_periph_dw_i2c_0_IC_HS_HCNT_IN 16'h6

//ic_hs_lcnt register reset value

`define soc_periph_dw_i2c_0_IC_HS_LCNT_IN 16'h8

//ic_rx_tl register reset value

`define soc_periph_dw_i2c_0_IC_RX_TL_IN 8'h0

//ic_tx_tl register reset value

`define soc_periph_dw_i2c_0_IC_TX_TL_IN 8'h0

//ic_status register reset value

`define soc_periph_dw_i2c_0_IC_STATUS_IN 21'h6

//IC_ENABLE register reset value

`define soc_periph_dw_i2c_0_IC_ENABLE_IN 3'h0

//Indicates a High Speed Mode Address value

`define soc_periph_dw_i2c_0_IC_HS_CODE 5'h1

//Indicates a 10 bit address transfer

`define soc_periph_dw_i2c_0_IC_SLV_ADDR_10BIT 5'h1e

//General Call I2C bus Code

`define soc_periph_dw_i2c_0_IC_GENERAL_CALL 8'h0

//Start Byte I2C bus Code

`define soc_periph_dw_i2c_0_IC_START_BYTE 8'h1

//DEVICE-ID I2C bus Code

`define soc_periph_dw_i2c_0_IC_DEVICE_ID_BYTE 7'h7c

//I2C Version ID

`define soc_periph_dw_i2c_0_IC_VERSION_ID_IN 32'h3230332a

//Speed up my simulation

`define soc_periph_dw_i2c_0_IC_SPEED_SIM 1'h1

//Random Seed For Simulations. Anything between 1 and 500.

`define soc_periph_dw_i2c_0_IC_RAND_SEED 1

//Determines if simulation max is one hour

`define soc_periph_dw_i2c_0_IC_RUN_FOR_ONE_HOUR 1'h1

//Determines if the I2C VIP VMT models are instaniated

`define soc_periph_dw_i2c_0_IC_VMT_MODEL_INCLUDED 1'h0

//Encoded APB Data Width

`define soc_periph_dw_i2c_0_ENCODED_APB_DATA_WIDTH 2'h2

//Encoded value of the transmit buffer depth

`define soc_periph_dw_i2c_0_ENCODED_IC_TX_BUFFER_DEPTH 8'h7

//Encoded value of the receiver buffer depth

`define soc_periph_dw_i2c_0_ENCODED_IC_RX_BUFFER_DEPTH 8'h7

//ic_comp_param_1 register reset value

`define soc_periph_dw_i2c_0_IC_COMP_PARAM_1_IN 24'h7078a

//ic_comp_param_1 register reset value

`define soc_periph_dw_i2c_0_IC_COMP_PARAM_UFM_1_IN 24'h70782

//Lower limit of number of clocks used for spike suppression in SS and FS

`define soc_periph_dw_i2c_0_IC_FS_SPKLEN_LO_LIMIT 8'h1

//Lower limit of number of clocks used for spike suppression in HS

`define soc_periph_dw_i2c_0_IC_HS_SPKLEN_LO_LIMIT 8'h1

//Duration (in ns) of longest spike to be suppressed in SS and FS

`define soc_periph_dw_i2c_0_IC_FS_MAX_SPKLEN 50

//Duration (in ns) of longest spike to be suppressed in HS

`define soc_periph_dw_i2c_0_IC_HS_MAX_SPKLEN 10


// Name:         IC_DEFAULT_FS_SPKLEN
// Default:      0x1 ([<functionof> IC_CLOCK_PERIOD IC_FS_MAX_SPKLEN])
// Values:       0x1, ..., 0xff
// Enabled:      IC_ULTRA_FAST_MODE==0
// 
// Reset value of maximum suppressed spike length register in  
// Standard Mode, Fast Mode, and Fast Mode Plus modes (IC_FS_SPKLEN Register). 
// Spike length is expressed in ic_clk cycles and this value is calculated based 
// on the value of IC_CLOCK_PERIOD.
`define soc_periph_dw_i2c_0_IC_DEFAULT_FS_SPKLEN 8'h1


// Name:         IC_DEFAULT_HS_SPKLEN
// Default:      0x1 ([<functionof> IC_CLOCK_PERIOD IC_HS_MAX_SPKLEN])
// Values:       0x1, ..., 0xff
// Enabled:      (IC_MAX_SPEED_MODE==3) && (IC_ULTRA_FAST_MODE ==0)
// 
// Reset value of maximum suppressed spike length register in HS modes (Register IC_HS_SPKLEN). 
// Spike length is expressed in ic_clk cycles and this value is calculated based on the value 
// of IC_CLOCK_PERIOD.
`define soc_periph_dw_i2c_0_IC_DEFAULT_HS_SPKLEN 8'h1


// Name:         IC_DEFAULT_UFM_SPKLEN
// Default:      0x1 ([<functionof> IC_CLOCK_PERIOD IC_HS_MAX_SPKLEN])
// Values:       0x1, ..., 0xff
// Enabled:      IC_ULTRA_FAST_MODE ==1
// 
// Reset value of maximum suppressed spike length register in Ultra-Fast Mode (IC_UFM_SPKLEN Register). 
// Spike length is expressed in ic_clk cycles and this value is calculated based on the value of IC_CLOCK_PERIOD.
`define soc_periph_dw_i2c_0_IC_DEFAULT_UFM_SPKLEN 8'h1


//ic_fs_spklen width

`define soc_periph_dw_i2c_0_IC_FS_SPKLEN_RS 8

//ic_hs_spklen width

`define soc_periph_dw_i2c_0_IC_HS_SPKLEN_RS 8

//Larger of IC_HS_SPKLEN_RS and IC_FS_SPKLEN_RS

`define soc_periph_dw_i2c_0_IC_SPKLEN_RS 8

//ic_scl_sda_timeout width

`define soc_periph_dw_i2c_0_IC_SCL_SDA_TIMEOUT_RS 32

//Creates a define for enabling low power interface

// `define soc_periph_dw_i2c_0_IC_HIGHSPEED_MODE_EN

//Include SVA assertions


//Used to insert internal tests


// Name:         REG_TIMEOUT_WIDTH
// Default:      4
// Values:       0 4 5 6 7 8
// Enabled:      SLAVE_INTERFACE_TYPE>0 && SLVERR_RESP_EN==1
// 
// Defines the width of Register timeout counter. If set to zero, 
// the timeout counter register is disabled, and timeout is triggered 
// as soon as the transaction tries to read an empty RX_FIFO or write 
// to a full TX_FIFO. As these are the only cases where PREADY signal 
// goes low, it ensures that PREADY is tied high throughout. Setting 
// values from 4 through 32 for this parameter configures the timeout 
// period from 2^4 to 2^8 pclk cycles.
`define soc_periph_dw_i2c_0_REG_TIMEOUT_WIDTH 4

//Slave has non-zero reg_timeout_width

// `define soc_periph_dw_i2c_0_IC_HAS_POSITIVE_REG_TIMEOUT_WIDTH


// Name:         HC_REG_TIMEOUT_VALUE
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>0 && SLVERR_RESP_EN==1 && REG_TIMEOUT_WIDTH>0
// 
// Checking this parameter makes Register timeout counter a read-only register. 
// The register can be programmed by user if the hardcode option is turned off.
`define soc_periph_dw_i2c_0_HC_REG_TIMEOUT_VALUE 0

//APB Interface has hardcoded timeout reset value

// `define soc_periph_dw_i2c_0_IC_HAS_HC_REG_TIMEOUT_VALUE


`define soc_periph_dw_i2c_0_POW_2_REG_TIMEOUT_WIDTH 15


// Name:         REG_TIMEOUT_VALUE
// Default:      8
// Values:       1, ..., POW_2_REG_TIMEOUT_WIDTH
// Enabled:      SLAVE_INTERFACE_TYPE>0 && SLVERR_RESP_EN==1 && REG_TIMEOUT_WIDTH>0
// 
// Defines the reset value of Register timeout counter register. This value can 
// be over - ridden by programming the timeout counter register before 
// enabling the component, if the HC_REG_TIMEOUT_VALUE is left un-checked
`define soc_periph_dw_i2c_0_REG_TIMEOUT_VALUE 8

//**************************************************************************************************
// Parameters to remove init and test ports in bcm
//**************************************************************************************************


//BCM defines
`define soc_periph_dw_i2c_0_DWC_NO_TST_MODE

`define soc_periph_dw_i2c_0_DWC_NO_CDC_INIT

`define soc_periph_dw_i2c_0_DWC_BCM06_NO_DIAG_N


// Name:         IC_MULTI_SAR_UDID_CTRL
// Default:      false ((IC_SMBUS_ARP==1 && IC_MULTI_SAR_EN==1) ? 1 : 0)
// Values:       false (0x0), true (0x1)
// Enabled:      IC_SMBUS_ARP==1 && IC_MULTI_SAR_EN==1
// 
// When set to 0, the DW_apb_i2c uses UDID[LOG2_IC_NUM_SARS-1:0] bits to identify each slave during the 
// SMBus ARP sequence. When set to 1, the DW_apb_i2c incorporates separate UDID registers for each slave. 
// The DW_apb_i2c uses these values to identify each slave during the SMBus ARP sequence.
`define soc_periph_dw_i2c_0_IC_MULTI_SAR_UDID_CTRL 1'h0



// Name:         IC_SAR2_SMBUS_UDID_HC
// Default:      true
// Values:       false (0x0), true (0x1)
// Enabled:      IC_MULTI_SAR_UDID_CTRL==1
// 
// When set to 1, the UDID of the IC_SAR2 slave address is hardcoded and registers IC_SAR2_SMBUS_UDID_WORD0/1/2/3 are 
// removed. 
// When set to 0, the UDID of IC_SAR2 is programmable through registers IC_SAR2_SMBUS_UDID_WORD0/1/2/3.
`define soc_periph_dw_i2c_0_IC_SAR2_SMBUS_UDID_HC 1'h1


// Name:         IC_SAR2_SMBUS_UDID_DEFAULT
// Default:      0xffff0000ffff0000ffff00003fff0000
// Values:       0x0, ..., 0xffffffffffffffffffffffffffffffff
// Enabled:      IC_MULTI_SAR_UDID_CTRL==1
// 
// If the parameter IC_SAR2_SMBUS_UDID_HC is 1, stores the Static Unique Device Identifier used for 
// Dynamic Address Resolution process in SMBus ARP Mode for IC_SAR2 slave address. If the parameter 
// IC_SAR2_SMBUS_UDID_HC is 0, then this field is used as the default value of the IC_SAR2 UDID Registers 
// {IC_SAR2_SMBUS_UDID_WORD3, IC_SAR2_SMBUS_UDID_WORD2, IC_SAR2_SMBUS_UDID_WORD1, IC_SAR2_SMBUS_UDID_WORD0}.
`define soc_periph_dw_i2c_0_IC_SAR2_SMBUS_UDID_DEFAULT 128'hffff0000ffff0000ffff00003fff0000


// Name:         IC_SAR3_SMBUS_UDID_HC
// Default:      true
// Values:       false (0x0), true (0x1)
// Enabled:      IC_NUM_SARS>=3 && IC_MULTI_SAR_UDID_CTRL==1
// 
// When set to 1, the UDID of the IC_SAR3 slave address is hardcoded and registers IC_SAR3_SMBUS_UDID_WORD0/1/2/3 are 
// removed. 
// When set to 0, the UDID of IC_SAR3 is programmable through registers IC_SAR3_SMBUS_UDID_WORD0/1/2/3.
`define soc_periph_dw_i2c_0_IC_SAR3_SMBUS_UDID_HC 1'h1


// Name:         IC_SAR3_SMBUS_UDID_DEFAULT
// Default:      0xffff0000ffff0000ffff00007fff0000
// Values:       0x0, ..., 0xffffffffffffffffffffffffffffffff
// Enabled:      IC_NUM_SARS>=3 && IC_MULTI_SAR_UDID_CTRL==1
// 
// If the parameter IC_SAR3_SMBUS_UDID_HC is 1, stores the Static Unique Device Identifier used for 
// Dynamic Address Resolution process in SMBus ARP Mode for IC_SAR3 slave address. If the parameter 
// IC_SAR3_SMBUS_UDID_HC is 0, then this field is used as the default value of the IC_SAR3 UDID Registers 
// {IC_SAR3_SMBUS_UDID_WORD3, IC_SAR3_SMBUS_UDID_WORD2, IC_SAR3_SMBUS_UDID_WORD1, IC_SAR3_SMBUS_UDID_WORD0}.
`define soc_periph_dw_i2c_0_IC_SAR3_SMBUS_UDID_DEFAULT 128'hffff0000ffff0000ffff00007fff0000


// Name:         IC_SAR4_SMBUS_UDID_HC
// Default:      true
// Values:       false (0x0), true (0x1)
// Enabled:      IC_NUM_SARS>=4 && IC_MULTI_SAR_UDID_CTRL==1
// 
// When set to 1, the UDID of the IC_SAR4 slave address is hardcoded and registers IC_SAR4_SMBUS_UDID_WORD0/1/2/3 are 
// removed. 
// When set to 0, the UDID of IC_SAR4 is programmable through registers IC_SAR4_SMBUS_UDID_WORD0/1/2/3.
`define soc_periph_dw_i2c_0_IC_SAR4_SMBUS_UDID_HC 1'h1


// Name:         IC_SAR4_SMBUS_UDID_DEFAULT
// Default:      0xffff0000ffff0000ffff0000bfff0000
// Values:       0x0, ..., 0xffffffffffffffffffffffffffffffff
// Enabled:      IC_NUM_SARS>=4 && IC_MULTI_SAR_UDID_CTRL==1
// 
// If the parameter IC_SAR4_SMBUS_UDID_HC is 1, stores the Static Unique Device Identifier used for 
// Dynamic Address Resolution process in SMBus ARP Mode for IC_SAR4 slave address. If the parameter 
// IC_SAR4_SMBUS_UDID_HC is 0, then this field is used as the default value of the IC_SAR4 UDID Registers 
// {IC_SAR4_SMBUS_UDID_WORD3, IC_SAR4_SMBUS_UDID_WORD2, IC_SAR4_SMBUS_UDID_WORD1, IC_SAR4_SMBUS_UDID_WORD0}.
`define soc_periph_dw_i2c_0_IC_SAR4_SMBUS_UDID_DEFAULT 128'hffff0000ffff0000ffff0000bfff0000








// Name:         IC_MSAR_SMBUS_ARP_EN_BITS
// Default:      false ((IC_MULTI_SAR_EN==1 && IC_SMBUS_ARP==1) ? 1 : 0)
// Values:       false (0), true (1)
// Enabled:      IC_MULTI_SAR_EN==1 && IC_SMBUS_ARP==1
// 
// When this parameter is set to 1 - The DW_apb_i2c includes ARP enable/disable bit for 
// each of the IC_SAR2, IC_SAR3 and IC_SAR4 slave addresses. The slave addresses will  
// participate into SMBus ARP process only if their individual ARP bit is enabled (set to 1). 
//  
// when this parameter is set to 0 - The DW_apb_i2c has ARP enable/disable for IC_SAR slave address only. 
// If the ARP is enabled for IC_SAR slave address, all other slave addresses (IC_SAR2, I_SAR3 and IC_SAR4)  
// will also automatically participate into SMBus ARP process.
`define soc_periph_dw_i2c_0_IC_MSAR_SMBUS_ARP_EN_BITS 0


//==============================================================================
// End Guard
//==============================================================================
 `endif
