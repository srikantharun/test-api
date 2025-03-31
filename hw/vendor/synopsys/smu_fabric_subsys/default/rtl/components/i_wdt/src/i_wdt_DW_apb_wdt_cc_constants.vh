//----------------------------------------------------------------------
//
// ------------------------------------------------------------------------------
// 
// Copyright 2003 - 2023 Synopsys, INC.
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
// Component Name   : DW_apb_wdt
// Component Version: 1.13a
// Release Type     : GA
// Build ID         : 23.38.39.16
// ------------------------------------------------------------------------------

// 
// Release version :  1.13a
// File Version     :        $Revision: #4 $ 
// Revision: $Id: //dwh/DW_ocb/DW_apb_wdt/amba_dev/src/DW_apb_wdt_cc_constants.vh#4 $ 
//
// File :                       DW_apb_wdt_cc_constants.vh
// Author:                      Marc Wall
//
//
// Date :                       $Date: 2023/04/02 $
// Abstract     :               parameter file for the WDT.
//
// =====================================================================

//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`ifndef __GUARD__DW_APB_WDT_CC_CONSTANTS__VH__
`define __GUARD__DW_APB_WDT_CC_CONSTANTS__VH__


// Name:         SLAVE_INTERFACE_TYPE
// Default:      APB2
// Values:       APB2 (0), APB3 (1), APB4 (2)
// 
// Select Register Interface type as APB2, APB3 or APB4. 
// By default, DW_apb_wdt supports APB2 interface.
`define SLAVE_INTERFACE_TYPE 2


// Name:         SLVERR_RESP_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>1 || WDT_PAR_PROT_EN>0
// 
// Enable Completer Error response signaling. The component will refrain 
// From signaling an error response if this parameter is disabled. This will result 
// in disabling all features that require PSLVERR functionality to be implemented.
`define SLVERR_RESP_EN 0
 
//APB Interface has APB3 signals

`define WDT_HAS_APB3_IF_SIGNALS

//APB Interface has APB4 signals

`define WDT_HAS_APB4_IF_SIGNALS


// Name:         PROT_LEVEL_RST
// Default:      0x2
// Values:       0x0, ..., 0x7
// Enabled:      SLAVE_INTERFACE_TYPE>1 && SLVERR_RESP_EN==1
// 
// Reset Value of WDT_PROT_LEVEL register. 
// A high on any bit of WDT protection level requires a high on the 
// corresponding pprot input bit to gain access to the load-count registers. 
// Else, SLVERR response is triggered. A zero on the protection bit will 
// provide access to the register if other protection levels are satisfied.
`define PROT_LEVEL_RST 3'h2


// Name:         HC_PROT_LEVEL
// Default:      false
// Values:       false (0), true (1)
// Enabled:      SLAVE_INTERFACE_TYPE>1 && SLVERR_RESP_EN==1
// 
// Checking this parameter makes WDT_PROT_LEVEL a read-only register. 
// The register can be programmed at run-time by a user if this 
// hard-code option is set to zero.
`define HC_PROT_LEVEL 0

//Component has hard-coded protection level enabled

// `define WDT_HAS_PROT_HC

//Component has protection functionality enabled

// `define WDT_HAS_PROT_FN


// Name:         APB_DATA_WIDTH
// Default:      32
// Values:       8 16 32
// 
// Width of the APB Data Bus to which this component is attached.
`define APB_DATA_WIDTH 32

//Maximum allowed APB Data bus width

`define MAX_APB_DATA_WIDTH 32

//Internal Define for APB Data Width 8

// `define APB_DATA_WIDTH_8

//Internal Define for APB Data Width != 8

`define APB_DATA_WIDTH_NOT_8

//Internal Define for APB Data Width 16

// `define APB_DATA_WIDTH_16

//Internal Define for APB Data Width 32

`define APB_DATA_WIDTH_32


// Name:         WDT_CNT_WIDTH
// Default:      32
// Values:       16, ..., 32
// 
// The Watchdog Timer counter width.
`define WDT_CNT_WIDTH 32


// Name:         WDT_INT_POL
// Default:      true
// Values:       false (0), true (1)
// Enabled:      !(WDT_HC_RMOD==1 && WDT_DFLT_RMOD==0) || (WDT_PAR_PROT_EN>0) || 
//               (WDT_LS_PROT_EN==1)
// 
// This parameter sets the polarity of the generated interrupt. 
// When set to 1, Active-high interrupts are included on the interface. 
// When set to 0, Active-low interrupts are included on the interface.
`define WDT_INT_POL 0


// Name:         WDT_RST_POL
// Default:      true
// Values:       false (0), true (1)
// 
// This parameter sets the polarity of the generated reset. When set to 1, 
// wdt_sys_rst is included on the interface. When set to 0, wdt_sys_rst_n 
// is included on the interface.
`define WDT_RST_POL 1


// Name:         WDT_HC_TOP
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// When set to 1, the selected timeout period(s) is set to be hard coded.
`define WDT_HC_TOP 1'h0


// Name:         WDT_DUAL_TOP
// Default:      false
// Values:       false (0), true (1)
// 
// When set to 1, includes a second timeout period that is used for 
// initialization prior to the first kick.
`define WDT_DUAL_TOP 0


// Name:         WDT_DFLT_TOP
// Default:      0
// Values:       0, ..., 15
// 
// Selects the timeout period that is available directly after reset. 
// It controls the reset value of the register. If WDT_HC_TOP is set to 1,  
// then the default timeout period is the only possible timeout period. 
// Can choose one of 16 values.
`define WDT_DFLT_TOP 15


// Name:         WDT_DFLT_TOP_INIT
// Default:      0
// Values:       0, ..., 15
// Enabled:      WDT_DUAL_TOP==1
// 
// Describes the initial timeout period that is available directly after reset. 
// It controls the reset value of the register. If WDT_HC_TOP is 1, then the 
// default initial time period is the only possible period.
`define WDT_DFLT_TOP_INIT 0


// Name:         WDT_USE_FIX_TOP
// Default:      true
// Values:       false (0x0), true (0x1)
// 
// When this parameter is set to 1, timeout period range is fixed. The range increments by 
// the power of 2 from 2^16 to 2^(WDT_CNT_WIDTH-1). When this 
// parameter is set to 0, the user must define the timeout period range (2^8 
// to 2^(WDT_CNT_WIDTH)-1) using the WDT_USER_TOP_(i) parameter.
`define WDT_USE_FIX_TOP 1'h1

//MaxValue for WDT_USER_TOP_0

`define WDT_USER_TOP_MAXVALUE 32'hffffffff


// Name:         WDT_USER_TOP_0
// Default:      0xffff
// Values:       0xff, ..., WDT_USER_TOP_MAXVALUE
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=0)
// 
// Describes the user-defined main timeout period for range i that is selected when 
// WDT_TORR bits [3:0] (TOP) are equal to i.
`define WDT_USER_TOP_0 32'hffff


// Name:         WDT_USER_TOP_1
// Default:      0x1ffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=1)
// 
// User defined main timeout period for range 1 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_1 32'h1ffff


// Name:         WDT_USER_TOP_2
// Default:      0x3ffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=2)
// 
// User defined main timeout period for range 2 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_2 32'h3ffff


// Name:         WDT_USER_TOP_3
// Default:      0x7ffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=3)
// 
// User defined main timeout period for range 3 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_3 32'h7ffff


// Name:         WDT_USER_TOP_4
// Default:      0xfffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=4)
// 
// User defined main timeout period for range 4 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_4 32'hfffff


// Name:         WDT_USER_TOP_5
// Default:      0x1fffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=5)
// 
// User defined main timeout period for range 5 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_5 32'h1fffff


// Name:         WDT_USER_TOP_6
// Default:      0x3fffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=6)
// 
// User defined main timeout period for range 6 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_6 32'h3fffff


// Name:         WDT_USER_TOP_7
// Default:      0x7fffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=7)
// 
// User defined main timeout period for range 7 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_7 32'h7fffff


// Name:         WDT_USER_TOP_8
// Default:      0xffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=8)
// 
// User defined main timeout period for range 8 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_8 32'hffffff


// Name:         WDT_USER_TOP_9
// Default:      0x1ffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=9)
// 
// User defined main timeout period for range 9 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_9 32'h1ffffff


// Name:         WDT_USER_TOP_10
// Default:      0x3ffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=10)
// 
// User defined main timeout period for range 10 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_10 32'h3ffffff


// Name:         WDT_USER_TOP_11
// Default:      0x7ffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=11)
// 
// User defined main timeout period for range 11 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_11 32'h7ffffff


// Name:         WDT_USER_TOP_12
// Default:      0xfffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=12)
// 
// User defined main timeout period for range 12 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_12 32'hfffffff


// Name:         WDT_USER_TOP_13
// Default:      0x1fffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=13)
// 
// User defined main timeout period for range 13 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_13 32'h1fffffff


// Name:         WDT_USER_TOP_14
// Default:      0x3fffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=14)
// 
// User defined main timeout period for range 14 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_14 32'h3fffffff


// Name:         WDT_USER_TOP_15
// Default:      0x7fffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && WDT_DFLT_TOP!=15)
// 
// User defined main timeout period for range 15 described by the WDT_TORR 
// register bits[3:0] (TOP).
`define WDT_USER_TOP_15 32'h7fffffff


// Name:         WDT_USER_TOP_INIT_0
// Default:      0xffff
// Values:       0xff, ..., WDT_USER_TOP_MAXVALUE
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=0) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=0)
// 
// Describes the user-defined initial timeout period for range i that is selected 
// when WDT_TORR bits [7:4] (TOP_INIT) are equal to i.
`define WDT_USER_TOP_INIT_0 32'hffff


// Name:         WDT_USER_TOP_INIT_1
// Default:      0x1ffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=1) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=1)
// 
// User defined initial timeout period for range 1 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_1 32'h1ffff


// Name:         WDT_USER_TOP_INIT_2
// Default:      0x3ffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=2) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=2)
// 
// User defined initial timeout period for range 2 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_2 32'h3ffff


// Name:         WDT_USER_TOP_INIT_3
// Default:      0x7ffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=3) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=3)
// 
// User defined initial timeout period for range 3 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_3 32'h7ffff


// Name:         WDT_USER_TOP_INIT_4
// Default:      0xfffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=4) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=4)
// 
// User defined initial timeout period for range 4 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_4 32'hfffff


// Name:         WDT_USER_TOP_INIT_5
// Default:      0x1fffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=5) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=5)
// 
// User defined initial timeout period for range 5 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_5 32'h1fffff


// Name:         WDT_USER_TOP_INIT_6
// Default:      0x3fffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=6) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=6)
// 
// User defined initial timeout period for range 6 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_6 32'h3fffff


// Name:         WDT_USER_TOP_INIT_7
// Default:      0x7fffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=7) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=7)
// 
// User defined initial timeout period for range 7 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_7 32'h7fffff


// Name:         WDT_USER_TOP_INIT_8
// Default:      0xffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=8) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=8)
// 
// User defined initial timeout period for range 8 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_8 32'hffffff


// Name:         WDT_USER_TOP_INIT_9
// Default:      0x1ffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=9) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=9)
// 
// User defined initial timeout period for range 9 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_9 32'h1ffffff


// Name:         WDT_USER_TOP_INIT_10
// Default:      0x3ffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=10) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=10)
// 
// User defined initial timeout period for range 10 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_10 32'h3ffffff


// Name:         WDT_USER_TOP_INIT_11
// Default:      0x7ffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=11) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=11)
// 
// User defined initial timeout period for range 11 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_11 32'h7ffffff


// Name:         WDT_USER_TOP_INIT_12
// Default:      0xfffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=12) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=12)
// 
// User defined initial timeout period for range 12 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_12 32'hfffffff


// Name:         WDT_USER_TOP_INIT_13
// Default:      0x1fffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=13) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=13)
// 
// User defined initial timeout period for range 13 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_13 32'h1fffffff


// Name:         WDT_USER_TOP_INIT_14
// Default:      0x3fffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=14) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=14)
// 
// User defined initial timeout period for range 14 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_14 32'h3fffffff


// Name:         WDT_USER_TOP_INIT_15
// Default:      0x7fffffff
// Values:       0xff, ..., [::DW_apb_wdt::calc_user_top_limit WDT_CNT_WIDTH]
// Enabled:      WDT_DUAL_TOP==1 && WDT_USE_FIX_TOP==0 && !(WDT_HC_TOP==1 && 
//               WDT_DFLT_TOP_INIT!=15) && !(WDT_ALWAYS_EN==1 && WDT_DFLT_TOP_INIT!=15)
// 
// User defined initial timeout period for range 15 described by the 
// WDT_TORR register bits[7:4] (TOP_INIT).
`define WDT_USER_TOP_INIT_15 32'h7fffffff


// Name:         WDT_DFLT_RPL
// Default:      2 pclk cycles
// Values:       2 pclk cycles (0x0), 4 pclk cycles (0x1), 8 pclk cycles (0x2), 16 
//               pclk cycles (0x3), 32 pclk cycles (0x4), 64 pclk cycles (0x5), 128 
//               pclk cycles (0x6), 256 pclk cycles (0x7)
// 
// The reset pulse length that is available directly after reset. If  
// WDT_HC_RPL is 1, then the default reset pulse length is the only  
// possible reset pulse length (2^(WDT_DFLT_RPL+1) pclk cycles). 
//  
// Note: When WDT_ASYNC_CLK_MODE_ENABLE = 1, the total reset pulse length also includes  
// the reset synchronization delay and the time taken for pclk to be made available. 
// For details, refer to "System Resets" section of DW_apb_wdt Databook.
`define WDT_DFLT_RPL 3'h0


// Name:         WDT_HC_RPL
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Configures the reset pulse length to be hard coded.
`define WDT_HC_RPL 1'h0


// Name:         WDT_DFLT_RMOD
// Default:      System reset only
// Values:       System reset only (0x0), Interrupt and system reset (0x1)
// 
// Describes the output response mode that is available directly after reset. Indicates the output 
// response the WDT gives if a zero count is reached; that is, a system reset if equals 0 
// and an interrupt followed by a system reset, if equals 1. If WDT_HC_RMOD is 1, then  
// default response mode is the only possible output response mode.
`define WDT_DFLT_RMOD 1'h0


// Name:         WDT_NEW_RMOD
// Default:      false
// Values:       false (0x0), true (0x1)
// Enabled:      (WDT_HC_RMOD==0)||(WDT_HC_RMOD==1 && WDT_DFLT_RMOD==1)
// 
// If this parameter is enabled, generate an interrupt when first timeout occurs. 
// Irrespective of interrupt got cleared or not by the time a second timeout 
// occurs, generate the system reset.
`define WDT_NEW_RMOD 1'h0

//WDT_NEW_RMOD bit value

// `define WDT_HAS_NEW_RMOD


// Name:         WDT_HC_RMOD
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Configures the output response mode to be hard coded.
`define WDT_HC_RMOD 1'h0


// Name:         WDT_ALWAYS_EN
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Configures the WDT to be enabled from reset. If this setting is 1, the WDT 
// is always enabled and a write to the WDT_EN field (bit 0) of the Watchdog 
// Timer Control Register (WDT_CR) to disable it has no effect.
`define WDT_ALWAYS_EN 1'h0


// Name:         WDT_CLK_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      WDT_ASYNC_CLK_MODE_ENABLE==0
// 
// Configures the peripheral to have an external counter clock enable signal  
// (wdt_clk_en) on the interface that can be used to control the rate at which 
// the counter decrements.
`define WDT_CLK_EN 0


// Name:         WDT_ASYNC_CLK_MODE_ENABLE
// Default:      false
// Values:       false (0), true (1)
// 
// To operate the counter with a clock that is asynchronous from the peripheral 
// clock (pclk) select this parameter. When this parameter is selected the tclk 
// and tresetn ports are added to the top-level port list.
`define WDT_ASYNC_CLK_MODE_ENABLE 0


// Name:         WDT_ASYNC_CLK_SYNC_DEPTH
// Default:      2
// Values:       2 3 4
// Enabled:      WDT_ASYNC_CLK_MODE_ENABLE==1
// 
// Sets the number of synchronization stages to be placed on clock domain crossing signals. 
//  - 2: 2-stage synchronization with positive-edge capturing at both the stages 
//  - 3: 3-stage synchronization with positive-edge capturing at all stages 
//  - 4: 4-stage synchronization with positive-edge capturing at all stages
`define WDT_ASYNC_CLK_SYNC_DEPTH 2


`define WDT_VERIF_EN 1


// `define WDT_ASYNC_CLK_MODE


`define WDT_RESTART_CNT_WIDTH 16


// Name:         WDT_PAUSE
// Default:      false
// Values:       false (0x0), true (0x1)
// 
// Configures the peripheral to have a pause enable signal (pause) on the  
// interface that can be used to freeze the watchdog counter during pause mode.
`define WDT_PAUSE 1'h1

//**************************************************************************************************
// Safety Parameters
//**************************************************************************************************

// Name:         WDT_SAFETY_PKG_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      <DWC-APB-WDT-SAFETY feature authorize>==1
// 
// Select this parameter to include the following safety features in DW_apb_wdt. 
//  - APB Completer interface parity protection 
//  - Lock Step protection
`define WDT_SAFETY_PKG_EN 0


// Name:         WDT_PAR_PROT_EN
// Default:      No parity check
// Values:       No parity check (0), Check parity for data (1), Check parity for 
//               address and data (2)
// Enabled:      WDT_SAFETY_PKG_EN==1 && SLAVE_INTERFACE_TYPE>0
// 
// Configures DW_apb_wdt to include the Parity generation and checking mechanism on the APB Completer interface. 
//  
// Read data parity is generated when WDT_PAR_PROT_EN>=1
`define WDT_PAR_PROT_EN 0


// Name:         WDT_PAR_TYPE
// Default:      Even
// Values:       Even (0), Odd (1)
// Enabled:      WDT_PAR_PROT_EN>0
// 
// This parameter selects the parity type on the APB Completer interface.
`define WDT_PAR_TYPE 0


// Name:         WDT_LS_PROT_EN
// Default:      false
// Values:       false (0), true (1)
// Enabled:      WDT_SAFETY_PKG_EN==1
// 
// Configures DW_apb_wdt to include Lock step protection feature.
`define WDT_LS_PROT_EN 0

//Component has Completer error response enabled

// `define WDT_HAS_SLVERR_RESP_EN

//Width of the timeout range register

`define WDT_TORR_WIDTH 4

//Reset timeout period select value

`define WDT_TOP_RST 15

//Reset WD counter value

`define WDT_CNT_RST 32'h7fffffff

//Reset WD counter value

`define WDT_GRAY_CNT_RST 32'h40000000


`define WDT_ADDR_SLICE_LHS 8

//Each corekit has a version number.
//This is relected in the ascii version number which needs to get translated.
// 0 => 48 -> 30
// 1 => 49 -> 31
// 2 => 50 -> 32
// A => 65 -> 41
// B => 66 -> 42
// C => 67 -> 43
//
//Current Version is 1.13* => 31_31_33_2A
//

`define WDT_VERSION_ID 32'h3131332a

//Software Peripheral ID Value

`define WDT_PERIPHERAL_ID 32'h44570120

//Maximum Value of WDT_USER_TOP_x parameter family

`define WDT_USER_TOP_MAX 32'h0


//Maximum Value of WDT_USER_TOP_INIT_x parameter family

`define WDT_USER_TOP_INIT_MAX 32'h0

//Number of 32-bit registers in peripheral address space

`define WDT_NUM_REGISTERS 64

//Encoded value of WDT_CNT_WIDTH parameter for Configuration ID Reg 1

`define WDT_ENCODED_CNT_WIDTH 5'h10

//Encoded value of APB_DATA_WIDTH parameter for Configuration ID Reg 1

`define WDT_ENCODED_APB_WIDTH 2'h2

//WDT_DFLT_RPL bit value

`define WDT_DFLT_RPL_BIT 3'h0

//WDT_DFLT_RMOD bit value

`define WDT_DFLT_RMOD_BIT 1'h0

//WDT_ALWAYS_EN bit value

//Control Register Reset Value

`define WDT_CR_RST 6'h0


//Used to insert internal tests

//Width of the timeout range register

`define INT_CNT_WIDTH 32

//Width of the timeout range register

`define TORR_WIDTH 4

//BCM defines

//Random seed used in the testbench

`define SIM_RAND_SEED 1

`define WDT_USE_PAUSE



`define WDT_ACTIVE_H_RST_POL


`define WDT_USE_SYS_RESET_DFLT_RMOD







`define WDT_HAS_INTR


`define WDT_CORE_BUSIN_W 62


`define WDT_CORE_BUSOUT_W 71


`define WDT_ISRC_BUSIN_W 36


`define WDT_ISRC_BUSOUT_W 33


`define WDT_CNT_RST_VAL 32'h7fffffff


`define WDT_LS_DELAY_COUNT 2


`define PRUSER_WIDTH 4

//Include SVA assertions

//Used to insert internal tests for functional coverage

`define DW_FUNC_COV_EN 0

//==============================================================================
// End Guard
//==============================================================================
 `endif
