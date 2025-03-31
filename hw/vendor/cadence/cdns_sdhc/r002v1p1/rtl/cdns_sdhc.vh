//------------------------------------------------------------------------------
// Copyright (c) 2017 Cadence Design Systems, Inc.
//
// The information herein (Cadence IP) contains confidential and proprietary
// information of Cadence Design Systems, Inc. Cadence IP may not be modified,
// copied, reproduced, distributed, or disclosed to third parties in any manner,
// medium, or form, in whole or in part, without the prior written consent of
// Cadence Design Systems Inc. Cadence IP is for use by Cadence Design Systems,
// Inc. customers only. Cadence Design Systems, Inc. reserves the right to make
// changes to Cadence IP at any time and without notice.
//------------------------------------------------------------------------------
//
//   Filename:           cdns_sdhc.vh
//   Module Name:        Not Applicable
//
//   Release Revision:   cdn_nv5401__ip6061___r602v2p1
//   Release SVN Tag:    cdn_nv5401__ip6061___r602v2p1
//
//   IP Name:            cdns_sdhc
//   IP Part Number:     N/A
//
//   Product Type:       Off-the-shelf
//   IP Type:            Soft IP
//   IP Family:          Flash
//   Technology:         n/a
//   Protocol:           n/a
//   Architecture:       n/a
//   Licensable IP:      n/a
//
//------------------------------------------------------------------------------
//   Description: 
//                
//                sd_host header file
//------------------------------------------------------------------------------

//----------------------------------------------------------------------
// ocp interface parameters
//----------------------------------------------------------------------
localparam [2:0] OCP_CMD_IDLE  = 3'd0;
localparam [2:0] OCP_CMD_WRITE = 3'd1;
localparam [2:0] OCP_CMD_READ  = 3'd2;

localparam [1:0] OCP_RESP_NULL   = 2'b00;
localparam [1:0] OCP_RESP_DVA    = 2'b01;
localparam [1:0] OCP_RESP_DVA_RD = 2'b01;
localparam [1:0] OCP_RESP_DVA_WR = 2'b00;

localparam [2:0] OCP_BRST_INCR = 3'b000;

//--------------------------------------------------------------------
//
//--------------------------------------------------------------------
localparam DMASEL_SDMA  = 1'b0;  // standard DMA
localparam DMASEL_ADMA2 = 1'b1;  // advanced DMA mode 2

localparam DMAADR_32 = 1'b0;
localparam DMAADR_64 = 1'b1;

localparam XFRENGINE_NONE   = 3'd0;
localparam XFRENGINE_NONDMA = 3'd1;
localparam XFRENGINE_SDMA   = 3'd2;
localparam XFRENGINE_ADMA2  = 3'd3;
localparam XFRENGINE_TUNE   = 3'd7;

//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
localparam IMPLEMENT_SLOT0 = 1'b1;

//----------------------------------------------------------------------
// debouncing
//----------------------------------------------------------------------
localparam DEBOUNCE_PERIOD = 24'd50;

//----------------------------------------------------------------------
// relative address
//----------------------------------------------------------------------
localparam HRS_ADDR05 = 13'h014;

localparam SRS_ADDR00 = 13'h000;
localparam SRS_ADDR01 = 13'h004;
localparam SRS_ADDR03 = 13'h00c;
localparam SRS_ADDR04 = 13'h010;
localparam SRS_ADDR05 = 13'h014;
localparam SRS_ADDR06 = 13'h018;
localparam SRS_ADDR07 = 13'h01c;
localparam SRS_ADDR08 = 13'h020;
localparam SRS_ADDR10 = 13'h028;
localparam SRS_ADDR11 = 13'h02c;
localparam SRS_ADDR15 = 13'h03c;
localparam SRS_ADDR20 = 13'h050;
localparam SRS_ADDR22 = 13'h058;
localparam SRS_ADDR23 = 13'h05c;
localparam SRS_ADDR30 = 13'h078;
localparam SRS_ADDR31 = 13'h07c;
localparam FIU_ADDR08 = 13'h020;

localparam CQRS_ADDR02 = 13'h408;
localparam CQRS_ADDR03 = 13'h40c;
localparam CQRS_ADDR07 = 13'h41c;
localparam CQRS_ADDR10 = 13'h428;
localparam CQRS_ADDR14 = 13'h438;
localparam CQRS_ADDR16 = 13'h440;

//----------------------------------------------------------------------
// Capabilities
//----------------------------------------------------------------------
// 'b00 - Removable Card
// 'b01 - Embedded Slot for One Device
// 'b10 - Shared Bus Slot
// 'b11 - Reserved
localparam CAPABILITY_S0_SLOTTYPE   = 2'd0; // Slot Type

// 1'b1 - device supports the feature
// 1'b0 - device does not support the feature
localparam CAPABILITY_S0_AIS   = 1'b0; // Asynchronous Interrupt Support
localparam CAPABILITY_S0_VS18  = 1'b1; // Voltage Suport for 1.8V
localparam CAPABILITY_S0_VS30  = 1'b1; // Voltage Suport for 3.0V
localparam CAPABILITY_S0_VS33  = 1'b1; // Voltage Suport for 3.3V
localparam CAPABILITY_S0_SRS   = 1'b0; // Suspend/Resume Support
localparam CAPABILITY_S0_SDMA  = 1'b1; // DMA Support
localparam CAPABILITY_S0_ADMA1 = 1'b0; // ADMA1 Support
localparam CAPABILITY_S0_ADMA2 = 1'b1; // ADMA2 Support
localparam CAPABILITY_S0_8EDS  = 1'b0; // 8-bit Embedded Device Support
localparam CAPABILITY_S0_HSS   = 1'b1; // High Speed Support

// 2'b00 - 512 bytes
// 2'b01 - 1024 bytes
// 2'b10 - 2048 bytes
// 2'b11 - reserved
localparam CAPABILITY_S0_MBL   = 2'b10; // Max Block Lenght

// 8'b00000000 - get info via other method
// 8'bnnnnnnnn - 1-255MHz
localparam CAPABILITY_S0_BCSDCLK = 8'd200; // Base sdmclk frequency

// 1'b0 - kHz
// 1'b1 - MHz
localparam CAPABILITY_S0_TCU   = 1'b1;     // Timeout Clock Unit.

// 6'b000000 - get info via other method
// 6'bnnnnnn - 1-63(k/M)Hz
// The timeout counter works with sdmclk/4 clock.
localparam CAPABILITY_S0_TCF    = 6'd50;   // Timeout clock frequency

// 8'b00000000 - get info via other method
// 8'b00000001 -    4 mA
// 8'b00000010 -    8 mA
// 8'b00000011 -   12 mA
// ....
// 8'b11111111 - 1020 mA
localparam CAPABILITY_S0_MC18   = 8'd32; // Maximum current for 1.8V VDD1
localparam CAPABILITY_S0_MC30   = 8'd32; // Maximum current for 3.0V VDD1
localparam CAPABILITY_S0_MC33   = 8'd32; // Maximum current for 3.3V VDD1
localparam CAPABILITY_S0_MC18V2 = 8'd32; // Maximum current for 1.8V VDD2

// *64-bit support* --- Setting 1 to this bit indicates that the Host
// Controller supports 64-bit address descriptor mode and is connected
// to 64-bit address system bus
localparam CAPABILITY_S0_64B  = 1'b1;  // 64-bit not supported

// LVS Host Supported
localparam CAPABILITY_S0_LVSH     = 1'b1;
// VDD2 Supported
localparam CAPABILITY_S0_VDD2S    = 1'b0;
// ADMA3 Supported
localparam CAPABILITY_S0_ADMA3S   = 1'b1;
// Retuning mode
localparam CAPABILITY_S0_RTNGM    = 2'b00;
// Use tuning for SDR50
localparam CAPABILITY_S0_UTSM50   = 1'b0;
// Timer Count for Re-Tuning
localparam CAPABILITY_S0_RTNGCNT  = 4'b0000;
// Driver Type D Supported
localparam CAPABILITY_S0_DRVD     = 1'b1;
// Driver Type C Supported
localparam CAPABILITY_S0_DRVC     = 1'b1;
// Driver Type A Supported
localparam CAPABILITY_S0_DRVA     = 1'b1;
// UHS-II Supported
localparam CAPABILITY_S0_UHSII    = 1'b0;
// DDR50 Supported
localparam CAPABILITY_S0_DDR50    = 1'b1;
// SDR104 Supported
localparam CAPABILITY_S0_SDR104   = 1'b1;
// SDR50 Supported
localparam CAPABILITY_S0_SDR50    = 1'b1;

localparam DRV_STR_SEL_S0_INIT = 2'd0;
localparam CLK_DIV_SEL_S0_INIT = 10'd250;

localparam DRV_STR_SEL_S0_DS = 2'd0;
localparam CLK_DIV_SEL_S0_DS = 10'd4;

localparam DRV_STR_SEL_S0_HS = 2'd0;
localparam CLK_DIV_SEL_S0_HS = 10'd2;

localparam DRV_STR_SEL_S0_SDR12 = 2'd0;
localparam CLK_DIV_SEL_S0_SDR12 = 10'd4;

localparam DRV_STR_SEL_S0_SDR25 = 2'd0;
localparam CLK_DIV_SEL_S0_SDR25 = 10'd2;

localparam DRV_STR_SEL_S0_SDR50 = 2'd0;
localparam CLK_DIV_SEL_S0_SDR50 = 10'd1;

localparam DRV_STR_SEL_S0_SDR104 = 2'd0;
localparam CLK_DIV_SEL_S0_SDR104 = 10'd0;

localparam DRV_STR_SEL_S0_DDR50 = 2'd0;
localparam CLK_DIV_SEL_S0_DDR50 = 10'd2;

// Capabilities Registers (RO)
localparam S0_HWINIT_SRS16_H
  = {
     CAPABILITY_S0_SLOTTYPE, // 31:30 - 15:14
     CAPABILITY_S0_AIS,      // 29    - 13
     CAPABILITY_S0_64B,      // 28    - 12
     CAPABILITY_S0_64B,      // 27    - 11
     CAPABILITY_S0_VS18,     // 26    - 10
     CAPABILITY_S0_VS30,     // 25    - 9
     CAPABILITY_S0_VS33,     // 24    - 8
     CAPABILITY_S0_SRS,      // 23    - 7
     CAPABILITY_S0_SDMA,     // 22    - 6
     CAPABILITY_S0_HSS,      // 21    - 5
     CAPABILITY_S0_ADMA1,    // 20    - 4
     CAPABILITY_S0_ADMA2,    // 19    - 3
     CAPABILITY_S0_8EDS,     // 18    - 2
     CAPABILITY_S0_MBL       // 17:16 - 1:0
     };
localparam S0_HWINIT_SRS16_L
  = {
     CAPABILITY_S0_BCSDCLK,  // 15:8
     CAPABILITY_S0_TCU,      // 7
     1'd0,                   // 6
     CAPABILITY_S0_TCF       // 5:0
     };
localparam S0_HWINIT_SRS17_H
  = {
     CAPABILITY_S0_LVSH,     // 15      31
     2'd0,                   // 14:13   30:29
     CAPABILITY_S0_VDD2S,    // 12      28
     CAPABILITY_S0_ADMA3S,   // 11      27
     3'd0,                   // 10:8    26:24
     8'd0                    // 7:0     23:16
     };
localparam S0_HWINIT_SRS17_L
  = {
     CAPABILITY_S0_RTNGM,    // 15:14
     CAPABILITY_S0_UTSM50,   // 13
     1'b0,                   // 12
     CAPABILITY_S0_RTNGCNT,  // 11:8
     1'b0,                   // 7
     CAPABILITY_S0_DRVD,     // 6
     CAPABILITY_S0_DRVC,     // 5
     CAPABILITY_S0_DRVA,     // 4
     CAPABILITY_S0_UHSII,    // 3
     CAPABILITY_S0_DDR50,    // 2
     CAPABILITY_S0_SDR104,   // 1
     CAPABILITY_S0_SDR50     // 0
     };
localparam S0_HWINIT_SRS18_H
  = {
     8'd0,                   // 31:24
     CAPABILITY_S0_MC18      // 23:16
     };
localparam S0_HWINIT_SRS18_L
  = {
     CAPABILITY_S0_MC30,     // 15:8
     CAPABILITY_S0_MC33      // 7:0
     };
localparam S0_HWINIT_SRS19_H = 16'd0;
localparam S0_HWINIT_SRS19_L
  = {
     8'd0,
     CAPABILITY_S0_MC18V2    // 7:0
     };
// Preset Value Registers (RO)
localparam S0_HWINIT_SRS24_L
  = {
     DRV_STR_SEL_S0_INIT,    // 15:14
     3'd0,                   // 13:11
     1'b0,                   // 10
     CLK_DIV_SEL_S0_INIT     //  9: 0
     };
localparam S0_HWINIT_SRS24_H
  = {
     DRV_STR_SEL_S0_DS,      // 15:14
     3'd0,                   // 13:11
     1'b0,                   // 10
     CLK_DIV_SEL_S0_DS       //  9: 0
     };
localparam S0_HWINIT_SRS25_L
  = {
     DRV_STR_SEL_S0_HS,      // 15:14
     3'd0, // 13:11
     1'b0,                   // 10
     CLK_DIV_SEL_S0_HS       //  9: 0
     };
localparam S0_HWINIT_SRS25_H
  = {
     DRV_STR_SEL_S0_SDR12,   // 15:14
     3'd0,                   // 13:11
     1'b0,                   // 10
     CLK_DIV_SEL_S0_SDR12    //  9: 0
     };
localparam S0_HWINIT_SRS26_L
  = {
     DRV_STR_SEL_S0_SDR25,   // 15:14
     3'd0,                   // 13:11
     1'b0,                   // 10
     CLK_DIV_SEL_S0_SDR25    //  9: 0
     };
localparam S0_HWINIT_SRS26_H
  = {
     DRV_STR_SEL_S0_SDR50,   // 15:14
     3'd0,                   // 13:11
     1'b0,                   // 10
     CLK_DIV_SEL_S0_SDR50    //  9: 0
     };
localparam S0_HWINIT_SRS27_L
  = {
     DRV_STR_SEL_S0_SDR104,  // 15:14
     3'd0,                   // 13:11
     1'b0,                   // 10
     CLK_DIV_SEL_S0_SDR104   //  9: 0
     };
localparam S0_HWINIT_SRS27_H
  = {
     DRV_STR_SEL_S0_DDR50,   // 15:14
     3'd0,                   // 13:11
     1'b0,                   // 10
     CLK_DIV_SEL_S0_DDR50    //  9: 0
     };

//----------------------------------------------------------------------
// registers reset value
//----------------------------------------------------------------------
localparam [31:0] RSTV_DEFAULT = 32'h0;

//----------------------------------------------------------------------
// interface speed mode
//----------------------------------------------------------------------
localparam [5:0] SM_DEFAULT      = 6'b000000;
localparam [5:0] SM_HIGHSPD      = 6'b000001;
localparam [5:0] SM_UHSI_SDR12   = 6'b001000;
localparam [5:0] SM_UHSI_SDR25   = 6'b001001;
localparam [5:0] SM_UHSI_SDR50   = 6'b001010;
localparam [5:0] SM_UHSI_SDR104  = 6'b001011;
localparam [5:0] SM_UHSI_DDR50   = 6'b001100;
localparam [5:0] SM_UHSII        = 6'b010000;
localparam [5:0] SM_MMC_LEGACY   = 6'b100000;
localparam [5:0] SM_MMC_SDR      = 6'b100001;
localparam [5:0] SM_MMC_DDR      = 6'b100010;
localparam [5:0] SM_MMC_HS200    = 6'b100011;
localparam [5:0] SM_MMC_HS400    = 6'b100100;
localparam [5:0] SM_MMC_HS400_ES = 6'b100101;

localparam [2:0] SM_HRS_MMC_LEGACY   = 3'b001;
localparam [2:0] SM_HRS_MMC_SDR      = 3'b010;
localparam [2:0] SM_HRS_MMC_DDR      = 3'b011;
localparam [2:0] SM_HRS_MMC_HS200    = 3'b100;
localparam [2:0] SM_HRS_MMC_HS400    = 3'b101;
localparam [2:0] SM_HRS_MMC_HS400_ES = 3'b110;
