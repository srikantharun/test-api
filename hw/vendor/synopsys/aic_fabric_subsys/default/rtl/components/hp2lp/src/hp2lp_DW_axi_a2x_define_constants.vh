/* --------------------------------------------------------------------
**
// ------------------------------------------------------------------------------
// 
// Copyright 2012 - 2023 Synopsys, INC.
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
// Component Name   : DW_axi_a2x
// Component Version: 2.06a
// Release Type     : GA
// Build ID         : 15.22.13.5
// ------------------------------------------------------------------------------

// 
// Release version :  2.06a
// File Version     :        $Revision: #4 $ 
// Revision: $Id: //dwh/DW_ocb/DW_axi_a2x/axi_dev_br/src/DW_axi_a2x_define_constants.vh#4 $ 
**
** --------------------------------------------------------------------
**
** File     : DW_axi_a2x_define_constants.v
** Created  : Thu Jan 27 11:01:40 MET 2011
** Abstract :
**
** --------------------------------------------------------------------
*/

//==============================================================================
// Start Guard: prevent re-compilation of includes
//==============================================================================
`ifndef hp2lp___GUARD__DW_AXI_A2X_DEFINE_CONSTANTS__VH__
`define hp2lp___GUARD__DW_AXI_A2X_DEFINE_CONSTANTS__VH__

//*****************************************************************************
// Software Interface
//*****************************************************************************

//*****************************************************************************
// A2X Address Channel
//*****************************************************************************

`define hp2lp_A2X_BSW            3    // Burst Size Width
`define hp2lp_A2X_BTW            2    // Burst Type Width
`define hp2lp_A2X_LTW            2    // Locked Type Width
`define hp2lp_A2X_CTW            4    // Cache Type Width
`define hp2lp_A2X_PTW            3    // Protection Type Width
`define hp2lp_A2X_RSW            1    // A2X Resize bit

`define hp2lp_A2X_BRESPW         2    // AXI Buffered Response Width
`define hp2lp_A2X_RRESPW         2    // AXI Buffered Response Width

`define hp2lp_A2X_HIDW            4
`define hp2lp_A2X_HBLW            3    // AHB Burst Width
`define hp2lp_A2X_HBTYPE_W        1    // AHB Burst Type Width

`define hp2lp_A2X_MAX_BSBW        32

//*****************************************************************************
// H2X Defines
//*****************************************************************************
`define hp2lp_CT_MODE             1'b0          
`define hp2lp_SNF_MODE            1'b1

//*****************************************************************************
// AXI Defines
//*****************************************************************************
`define hp2lp_ABURST_FIXED        2'b00
`define hp2lp_ABURST_INCR         2'b01
`define hp2lp_ABURST_WRAP         2'b10

//*****************************************************************************
// AHB Defines
//*****************************************************************************
`define hp2lp_HTRANS_IDLE         2'b00
`define hp2lp_HTRANS_BUSY         2'b01
`define hp2lp_HTRANS_NSEQ         2'b10
`define hp2lp_HTRANS_SEQ          2'b11
`define hp2lp_HBURST_SINGLE       3'b000
`define hp2lp_HBURST_INCR         3'b001
`define hp2lp_HBURST_WRAP4        3'b010
`define hp2lp_HBURST_INCR4        3'b011
`define hp2lp_HBURST_WRAP8        3'b100
`define hp2lp_HBURST_INCR8        3'b101
`define hp2lp_HBURST_WRAP16       3'b110
`define hp2lp_HBURST_INCR16       3'b111
`define hp2lp_HSIZE_8             3'b000
`define hp2lp_HSIZE_16            3'b001
`define hp2lp_HSIZE_32            3'b010
`define hp2lp_HSIZE_64            3'b011
`define hp2lp_HSIZE_128           3'b100
`define hp2lp_HSIZE_256           3'b101
`define hp2lp_HSIZE_512           3'b110
`define hp2lp_HSIZE_1024          3'b111
`define hp2lp_HSIZE_8BIT          3'b000
`define hp2lp_HSIZE_16BIT         3'b001
`define hp2lp_HSIZE_32BIT         3'b010
`define hp2lp_HSIZE_64BIT         3'b011
`define hp2lp_HSIZE_128BIT        3'b100
`define hp2lp_HSIZE_256BIT        3'b101
`define hp2lp_HSIZE_512BIT        3'b110
`define hp2lp_HSIZE_1024BIT       3'b111
`define hp2lp_HSIZE_BYTE          3'b000
`define hp2lp_HSIZE_WORD16        3'b001
`define hp2lp_HSIZE_WORD32        3'b010
`define hp2lp_HSIZE_WORD64        3'b011
`define hp2lp_HSIZE_WORD128       3'b100
`define hp2lp_HSIZE_WORD256       3'b101
`define hp2lp_HSIZE_WORD512       3'b110
`define hp2lp_HSIZE_WORD1024      3'b111
`define hp2lp_HPROT_DATA          0
`define hp2lp_HPROT_PRIV          1
`define hp2lp_HPROT_BUFF          2
`define hp2lp_HPROT_CACHE         3


`define hp2lp_HRESP_OKAY          2'b00
`define hp2lp_HRESP_ERROR         2'b01
`define hp2lp_HRESP_RETRY         2'b10
`define hp2lp_HRESP_SPLIT         2'b11

//*****************************************************************************
//  AXI Defines
//*****************************************************************************
`define hp2lp_AFIXED 2'b00
`define hp2lp_AINCR  2'b01
`define hp2lp_AWRAP  2'b10

`define hp2lp_AOKAY   2'b00
`define hp2lp_AEXOKAY 2'b10
`define hp2lp_ASLVERR 2'b10
`define hp2lp_ADECERR 2'b11

//==============================================================================
// End Guard
//==============================================================================  
`endif
