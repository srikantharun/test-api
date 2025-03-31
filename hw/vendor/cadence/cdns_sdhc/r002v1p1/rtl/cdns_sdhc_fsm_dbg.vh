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
//   Filename:           cdns_sdhc_fsm_dbg.vh
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
//                FSM monitor module
//------------------------------------------------------------------------------


  // State machines address - CIU (sdmclk)
  localparam FDBG_ADDR_CIU_FSM_IP                        = 12'h000;
  localparam FDBG_ADDR_CIU_FSM_CMD                       = 12'h001;
  localparam FDBG_ADDR_CIU_FSM_CMD_CTRL                  = 12'h002;
  localparam FDBG_ADDR_CIU_FSM_CMD2                      = 12'h003;
  localparam FDBG_ADDR_CIU_FSM_BLOCK                     = 12'h004;
  localparam FDBG_ADDR_CIU_FSM_INF_XFER_END              = 12'h005;
  localparam FDBG_ADDR_CIU_FSM_INF_XFER_REND             = 12'h006;

  // State machines address - BIU (clk)
  localparam FDBG_ADDR_BIU_FSM_DEB                       = 12'h000;
  localparam FDBG_ADDR_BIU_FSM_APB_OCP_WRAP              = 12'h001;
  localparam FDBG_ADDR_BIU_FSM_BUFFER                    = 12'h002;
  localparam FDBG_ADDR_BIU_FSM_BUSY                      = 12'h003;
  localparam FDBG_ADDR_BIU_FSM_WRX                       = 12'h004;
  localparam FDBG_ADDR_BIU_FSM_RDX                       = 12'h005;
  localparam FDBG_ADDR_BIU_FSM_XFR                       = 12'h006;
  localparam FDBG_ADDR_BIU_FSM_BIU                       = 12'h007;
  localparam FDBG_ADDR_BIU_FSM_ABORT                     = 12'h008;
  localparam FDBG_ADDR_BIU_FSM_ADMA                      = 12'h009;
  localparam FDBG_ADDR_BIU_FSM_DCTRL                     = 12'h00a;
  localparam FDBG_ADDR_BIU_FSM_DMA_DATAPATH              = 12'h00b;
  localparam FDBG_ADDR_BIU_FSM_DMA_CTRL                  = 12'h00c;
  localparam FDBG_ADDR_BIU_FSM_TUNE_CTRL                 = 12'h00d;
  localparam FDBG_ADDR_BIU_FSM_STEP                      = 12'h00e;
  localparam FDBG_ADDR_BIU_FSM_STATUS                    = 12'h00f;
  localparam FDBG_ADDR_BIU_FSM_READ_PATTERN              = 12'h010;
  localparam FDBG_ADDR_BIU_FSM_BOOT                      = 12'h011;
  localparam FDBG_ADDR_BIU_FSM_CQE                       = 12'h012;
  localparam FDBG_ADDR_BIU_FSM_EXEC                      = 12'h013;
  localparam FDBG_ADDR_BIU_FSM_CITIMER                   = 12'h014;
  localparam FDBG_ADDR_BIU_FSM_QUEUE1                    = 12'h015;
  localparam FDBG_ADDR_BIU_FSM_AXI2AHBLITE               = 12'h016;
