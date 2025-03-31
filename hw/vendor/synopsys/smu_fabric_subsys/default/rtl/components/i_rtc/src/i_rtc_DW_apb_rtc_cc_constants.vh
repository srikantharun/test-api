/*
------------------------------------------------------------------------
--
// ------------------------------------------------------------------------------
// 
// Copyright 2002 - 2023 Synopsys, INC.
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
// Component Name   : DW_apb_rtc
// Component Version: 2.09a
// Release Type     : GA
// Build ID         : 14.21.24.12
// ------------------------------------------------------------------------------

// 
// Release version :  2.09a
// File Version     :        $Revision: #3 $ 
// Revision: $Id: //dwh/DW_ocb/DW_apb_rtc/amba_dev/src/DW_apb_rtc_cc_constants.vh#3 $ 
--
-- File     :               DW_apb_rtc_cc_constants.vh
//
//
-- Author   :               Marc Wall
-- Abstract :               Parameter File
--
------------------------------------------------------------------------
*/

//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`ifndef __GUARD__DW_APB_RTC_CC_CONSTANTS__VH__
`define __GUARD__DW_APB_RTC_CC_CONSTANTS__VH__


// Name:         SLAVE_INTERFACE_TYPE
// Default:      APB2
// Values:       APB2 (0), APB3 (1), APB4 (2)
// 
// Selects the Register Interface type as APB2, APB3 or APB4. 
// By default, DW_apb_rtc supports APB2 interface.
`define SLAVE_INTERFACE_TYPE 2

//APB Interface has APB3 signals

`define RTC_HAS_APB3_IF_SIGNALS

//APB Interface has APB4 signals

`define RTC_HAS_APB4_IF_SIGNALS


// Name:         SLVERR_RESP_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>1
// 
// Enables Completer Error response signaling. DW_apb_rtc will refrain 
// from signaling an error response if this parameter is disabled.
`define SLVERR_RESP_EN 0
 
//Component has completer error response enabled

// `define RTC_HAS_SLVERR_RESP_EN


// Name:         PROT_LEVEL_RST
// Default:      0x0
// Values:       0x0, ..., 0x7
// Enabled:      SLAVE_INTERFACE_TYPE>1 && SLVERR_RESP_EN==1
// 
// Reset Value of RTC_PROT_LEVEL register. 
// A high on any bit of RTC protection level requires a high on the 
// corresponding pprot input bit to gain access to the load-count registers. 
// Else, SLVERR response is triggered. A zero on the protection bit will 
// provide access to the register if other protection levels are satisfied.
`define PROT_LEVEL_RST 3'h0


`define RTC_CCR_RST_VAL 32'h0


// Name:         HC_PROT_LEVEL
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>1 && SLVERR_RESP_EN==1
// 
// Checking this parameter makes RTC_PROT_LEVEL a read-only register. 
// The register can be programmed at run-time by a user if this 
// hard-code option is turned off.
`define HC_PROT_LEVEL 0

//Component has hard-coded protection level enabled

// `define RTC_HAS_PROT_HC

//Component has hard-coded protection level enabled

// `define RTC_HAS_PROT_HC_OFF

//Component has protection functionality enabled

// `define RTC_HAS_PROT_FN


// Name:         APB_DATA_WIDTH
// Default:      32
// Values:       8 16 32
// 
// Width of APB Data Bus to which this peripheral is attached.
`define APB_DATA_WIDTH 32

//Component has 08 bit APB Data Width

// `define APB_DATA_WIDTH_08

//Component has 16 bit APB Data Width

// `define APB_DATA_WIDTH_16

//Component has 32 bit APB Data Width

`define APB_DATA_WIDTH_32

// TCL GENERATED CONSTANT

`define PADDR_RHS 2

//Maximum allowed APB Data bus width

`define MAX_APB_DATA_WIDTH 32


// Name:         RTC_EN_MODE
// Default:      false
// Values:       false (0), true (1)
// 
// Includes RTC enable bit in the control register, which can be programmed 
// and the value reflected on the interface signal rtc_en. This signal indicates that the RTC 
// is enabled and requires a free-running pclk, and can therefore be used by a clock generator. 
//  
// Note: If RTC_EN_MODE is True, the RTC Counter enable/disable depends on the 
// RTC_CCR register. If presetn is asserted, the RTC_CCR register is reset and the Counter is disabled.
`define RTC_EN_MODE 0


// Name:         RTC_CNT_WIDTH
// Default:      32
// Values:       8, ..., 32
// 
// Size of the internal counter.
`define RTC_CNT_WIDTH 32


`define COHERENCY 1

//Identical clock relationship

`define IDENT 2'h0

//Asynchronous clock relationship

`define ASYNC 2'h1

//Synchronous clock relationship

`define SYNC 2'h3


// Name:         RTC_CLK_EN
// Default:      false
// Values:       false (0), true (1)
// 
// Includes the rtc_clk_en signal on the interface (rtc_clk is not included). Along with pclk, this signal allows the RTC 
// to be clocked.
`define RTC_CLK_EN 0


// Name:         RTC_CLK_TYPE
// Default:      Asynchronous ([<functionof> RTC_CLK_EN SYNC ASYNC])
// Values:       Identical (0), Synchronous (3), Asynchronous (1)
// Enabled:      RTC_CLK_EN==0
// 
// Describes the relationship between pclk and rtc_clk.
`define RTC_CLK_TYPE 1

//Component has RTC has Aynchronous clock

`define RTC_HAS_ASYNC_CLK


`define RTC_SYNC_DEPTH 2


`define RTC_VERIF_EN 1

//RTC clock generated interrupt

`define RTC_CLK 0

//pclk generated interrupt

`define PCLK 1


// Name:         RTC_INT_LOC
// Default:      true
// Values:       false (0), true (1)
// 
// Describes the clock domain in which the interrupt is generated. When an 
// interrupt is generated in the pclk domain, a free-running pclk is required to transfer the 
// counter value each time it changes. When generated in the rtc_clk domain, then only 
// the rtc_clk must be present to detect the interrupt.
`define RTC_INT_LOC 1


// Name:         RTC_FREE_PCLK
// Default:      false
// Values:       false (0), true (1)
// 
// Describes whether pclk is a free-running clock and always available to the 
// DW_apb_rtc for re-timing the counter clock into the pclk domain. When pclk is not a 
// free-running clock, then a free-running implementation must be connected to rtc_fpclk. 
// This is used to transfer values across clock domains.
`define RTC_FREE_PCLK 0


// Name:         RTC_INT_POL
// Default:      true
// Values:       false (0), true (1)
// 
// Describes the polarity of the generated interrupt.
`define RTC_INT_POL 0


// Name:         RTC_WRAP_MODE
// Default:      false
// Values:       false (0), true (1)
// 
// Includes the counter wrap enable bit in the control register (RTC_CCR), which 
// can be programmed to enable the counter to wrap after it has reached the match value, 
// instead of only wrapping at the maximum count.
`define RTC_WRAP_MODE 0


// Name:         RTC_WRAP_2_ZERO
// Default:      true
// Values:       false (0), true (1)
// Enabled:      RTC_WRAP_MODE==1
// 
// When this option is enabled, the counter wraps to 0 when the counter 
// reaches the match value and the counter wrap enable is set; otherwise, it wraps to the 
// last value loaded to the counter.
`define RTC_WRAP_2_ZERO 1


// Name:         RTC_PRESCLR_EN
// Default:      false
// Values:       false (0), true (1)
// 
// This parameter is used to enable the RTC Prescaler Counter logic in  
// the DW_apb_rtc.
`define RTC_PRESCLR_EN 0

//Component has RTC Prescaler Counter Logic

// `define RTC_HAS_PRESCLR_LOGIC

// This parameter is used for hardcoding or adding a software programmable 
// enable/disable bit in the RTC_CCR Register for RTC Prescaler Counter logic.
// Note: This feature is disabled to reduce the number of parameters visible.
// This can be enabled based on the customer request

`define RTC_PRESCLR_EN_HC 0


// Name:         RTC_PRESCLR_WIDTH
// Default:      16
// Values:       2, ..., 32
// Enabled:      RTC_PRESCLR_EN
// 
// Defines width of RTC Prescaler Counter register. This is used for both  
// RTC Prescaler Counter and RTC_CPSR Registers.
`define RTC_PRESCLR_WIDTH 16


// Name:         RTC_PRESCLR_VAL
// Default:      2 ((RTC_PRESCLR_EN ==1) ? 32768:2)
// Values:       2, ..., 4294967295
// Enabled:      RTC_PRESCLR_EN
// 
// Defines the default value of RTC Prescaler Counter register.
`define RTC_PRESCLR_VAL 16'd2


// Name:         RTC_PRESCLR_VAL_HC
// Default:      false
// Values:       false (0), true (1)
// Enabled:      RTC_PRESCLR_EN
// 
// This parameter is used for hardcoding the RTC_CPSR. 
//  If this is true, then RTC_CPSR register will become read-only. Otherwise, the register is  
// read/write capable.
`define RTC_PRESCLR_VAL_HC 0

//Width of control register

`define RTC_CR_WIDTH 4


`define RTC_CR_WIDTH_2 4


`define RTC_ADDR_SLICE_LHS 4

//Setting up a clock period for the RTC.

`define RTC_CLK_PERIOD 450

//Each corekit has a version number.
//This is relected in the ascii version number which needs to get translated.
//0 => 48 -> 30
//1 => 49 -> 31
//2 => 50 -> 32
//A => 65 -> 41
//B => 66 -> 42
//C => 67 -> 43
//
//Current Version is 2.09* => 32_30_39_2A
//

`define RTC_VERSION_ID 32'h3230392a

// Parameter required for the testbench to indicate Identical clock relationship

// `define PCLK_RTC_CLK_IDENT

//Used to insert VMM testbench

//Control switch to enable Clock Frequency Utilization

`define RTC_USE_FREQ_SWITCH 0

// This parameter is set if Clock Frequency Utilization is enabled

// Parameter required for the testbench to indicate Identical clock relationship

// `define RTC_EN_MODE_SIGNAL

//Random seed used in the testbench

`define SIM_RAND_SEED 1

`define RTC_CLK_EN_IS_0


`define RTC_FREE_PCLK_IS_0

`define SLAVE_INTERFACE_TYPE_MORE_THAN_1

`define HAS_SCAN_MODE



`define RTC_INT_POL_L

`define SLAVE_INTERFACE_TYPE_MORE_THAN_0

//Used to insert internal tests

//Used to insert internal tests for functional coverage

`define DW_FUNC_COV_EN 0

//==============================================================================
// End Guard
//==============================================================================
 `endif
