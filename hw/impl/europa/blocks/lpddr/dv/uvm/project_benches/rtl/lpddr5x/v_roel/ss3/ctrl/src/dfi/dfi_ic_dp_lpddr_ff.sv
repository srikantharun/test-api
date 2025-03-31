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

// -------------------------------------------------------------------------
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/dfi/dfi_ic_dp_lpddr_ff.sv#1 $
// -------------------------------------------------------------------------
// Description:
//            dfi data path signal swaping
//            dfi data path signal flipflop
//            dfi data path signal OCCAP protection
`include "DWC_ddrctl_all_defs.svh"
module dfi_ic_dp_lpddr_ff
#(
    parameter     NUM_RANKS                     = `MEMC_NUM_RANKS
   ,parameter     DFI0_CS_WIDTH                 = `DDRCTL_DFI0_CS_WIDTH
   ,parameter     DFI1_CS_WIDTH                 = `DDRCTL_DFI1_CS_WIDTH
   ,parameter     DFI2_CS_WIDTH                 = `DDRCTL_DFI2_CS_WIDTH
   ,parameter     DFI3_CS_WIDTH                 = `DDRCTL_DFI3_CS_WIDTH
   ,parameter     FREQ_RATIO                    = `MEMC_FREQ_RATIO
   ,parameter     DDRC_TOTAL_DATA_WIDTH         = `MEMC_DFI_TOTAL_DATA_WIDTH
   ,parameter     DDRC_TOTAL_DATAEN_WIDTH       = `MEMC_DFI_TOTAL_DATAEN_WIDTH
   ,parameter     NUM_DFI                       = `UMCTL2_NUM_DFI
   ,parameter     NUM_CHANNEL                   = `UMCTL2_NUM_DATA_CHANNEL
   ,parameter     DFI_DATA_WIDTH                = `DDRCTL_DFI_DATA_WIDTH
   ,parameter     DFI_MASK_WIDTH                = `DDRCTL_DFI_MASK_WIDTH
   ,parameter     DFI_DATAEN_WIDTH              = `DDRCTL_DFI_DATAEN_WIDTH
   ,parameter     REG_DFI_OUT_VAL               = `MEMC_REG_DFI_OUT_VAL
   ,parameter     REG_DFI_IN_RD_DATA_VAL        = `MEMC_REG_DFI_IN_RD_DATA_VAL
   ,parameter     OCCAP_EN                      = `UMCTL2_OCCAP_EN
   ,parameter     OCCAP_PIPELINE_EN             = 0
)
(
   input logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi0_wrdata_P0
  ,input logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi0_wrdata_P1
  ,input logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi0_wrdata_P2
  ,input logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi0_wrdata_P3
  ,input logic [DFI_MASK_WIDTH-1:0]                               dp0_dfi0_wrdata_mask_P0
  ,input logic [DFI_MASK_WIDTH-1:0]                               dp0_dfi0_wrdata_mask_P1
  ,input logic [DFI_MASK_WIDTH-1:0]                               dp0_dfi0_wrdata_mask_P2
  ,input logic [DFI_MASK_WIDTH-1:0]                               dp0_dfi0_wrdata_mask_P3
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_wrdata_en_P0
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_wrdata_en_P1
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_wrdata_en_P2
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_wrdata_en_P3
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi0_wrdata_cs_P0
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi0_wrdata_cs_P1
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi0_wrdata_cs_P2
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi0_wrdata_cs_P3
  ,input logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi0_wrdata_ecc_P0
  ,input logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi0_wrdata_ecc_P1
  ,input logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi0_wrdata_ecc_P2
  ,input logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi0_wrdata_ecc_P3
  ,input logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi1_wrdata_P0
  ,input logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi1_wrdata_P1
  ,input logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi1_wrdata_P2
  ,input logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi1_wrdata_P3
  ,input logic [DFI_MASK_WIDTH-1:0]                               dp0_dfi1_wrdata_mask_P0
  ,input logic [DFI_MASK_WIDTH-1:0]                               dp0_dfi1_wrdata_mask_P1
  ,input logic [DFI_MASK_WIDTH-1:0]                               dp0_dfi1_wrdata_mask_P2
  ,input logic [DFI_MASK_WIDTH-1:0]                               dp0_dfi1_wrdata_mask_P3
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_wrdata_en_P0
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_wrdata_en_P1
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_wrdata_en_P2
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_wrdata_en_P3
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi1_wrdata_cs_P0
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi1_wrdata_cs_P1
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi1_wrdata_cs_P2
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi1_wrdata_cs_P3
  ,input logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi1_wrdata_ecc_P0
  ,input logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi1_wrdata_ecc_P1
  ,input logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi1_wrdata_ecc_P2
  ,input logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi1_wrdata_ecc_P3


   ,output  logic [DFI_DATA_WIDTH-1:0]                               dfi0_wrdata_P0_out
   ,output  logic [DFI_DATA_WIDTH-1:0]                               dfi0_wrdata_P1_out
   ,output  logic [DFI_DATA_WIDTH-1:0]                               dfi0_wrdata_P2_out
   ,output  logic [DFI_DATA_WIDTH-1:0]                               dfi0_wrdata_P3_out
   ,output  logic [DFI_MASK_WIDTH-1:0]                               dfi0_wrdata_mask_P0_out
   ,output  logic [DFI_MASK_WIDTH-1:0]                               dfi0_wrdata_mask_P1_out
   ,output  logic [DFI_MASK_WIDTH-1:0]                               dfi0_wrdata_mask_P2_out
   ,output  logic [DFI_MASK_WIDTH-1:0]                               dfi0_wrdata_mask_P3_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_wrdata_en_P0_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_wrdata_en_P1_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_wrdata_en_P2_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_wrdata_en_P3_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI0_CS_WIDTH)-1:0]             dfi0_wrdata_cs_P0_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI0_CS_WIDTH)-1:0]             dfi0_wrdata_cs_P1_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI0_CS_WIDTH)-1:0]             dfi0_wrdata_cs_P2_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI0_CS_WIDTH)-1:0]             dfi0_wrdata_cs_P3_out
   ,output  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_wrdata_ecc_P0_out
   ,output  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_wrdata_ecc_P1_out
   ,output  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_wrdata_ecc_P2_out
   ,output  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_wrdata_ecc_P3_out
   ,output  logic [DFI_DATA_WIDTH-1:0]                               dfi1_wrdata_P0_out
   ,output  logic [DFI_DATA_WIDTH-1:0]                               dfi1_wrdata_P1_out
   ,output  logic [DFI_DATA_WIDTH-1:0]                               dfi1_wrdata_P2_out
   ,output  logic [DFI_DATA_WIDTH-1:0]                               dfi1_wrdata_P3_out
   ,output  logic [DFI_MASK_WIDTH-1:0]                               dfi1_wrdata_mask_P0_out
   ,output  logic [DFI_MASK_WIDTH-1:0]                               dfi1_wrdata_mask_P1_out
   ,output  logic [DFI_MASK_WIDTH-1:0]                               dfi1_wrdata_mask_P2_out
   ,output  logic [DFI_MASK_WIDTH-1:0]                               dfi1_wrdata_mask_P3_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_wrdata_en_P0_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_wrdata_en_P1_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_wrdata_en_P2_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_wrdata_en_P3_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_wrdata_cs_P0_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_wrdata_cs_P1_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_wrdata_cs_P2_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_wrdata_cs_P3_out
   ,output  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_wrdata_ecc_P0_out
   ,output  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_wrdata_ecc_P1_out
   ,output  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_wrdata_ecc_P2_out
   ,output  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_wrdata_ecc_P3_out

   ,input   logic [DFI_DATA_WIDTH-1:0]                               dfi0_rddata_W0
   ,input   logic [DFI_DATA_WIDTH-1:0]                               dfi0_rddata_W1
   ,input   logic [DFI_DATA_WIDTH-1:0]                               dfi0_rddata_W2
   ,input   logic [DFI_DATA_WIDTH-1:0]                               dfi0_rddata_W3
   ,input   logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_rddata_dbi_W0
   ,input   logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_rddata_dbi_W1
   ,input   logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_rddata_dbi_W2
   ,input   logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_rddata_dbi_W3
   ,input   logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_valid_W0
   ,input   logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_valid_W1
   ,input   logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_valid_W2
   ,input   logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_valid_W3

   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_en_P0_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_en_P1_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_en_P2_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_en_P3_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI0_CS_WIDTH)-1:0]             dfi0_rddata_cs_P0_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI0_CS_WIDTH)-1:0]             dfi0_rddata_cs_P1_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI0_CS_WIDTH)-1:0]             dfi0_rddata_cs_P2_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI0_CS_WIDTH)-1:0]             dfi0_rddata_cs_P3_out
   ,input   logic [DFI_DATA_WIDTH-1:0]                               dfi1_rddata_W0
   ,input   logic [DFI_DATA_WIDTH-1:0]                               dfi1_rddata_W1
   ,input   logic [DFI_DATA_WIDTH-1:0]                               dfi1_rddata_W2
   ,input   logic [DFI_DATA_WIDTH-1:0]                               dfi1_rddata_W3
   ,input   logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_rddata_dbi_W0
   ,input   logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_rddata_dbi_W1
   ,input   logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_rddata_dbi_W2
   ,input   logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_rddata_dbi_W3
   ,input   logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_valid_W0
   ,input   logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_valid_W1
   ,input   logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_valid_W2
   ,input   logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_valid_W3

   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_en_P0_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_en_P1_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_en_P2_out
   ,output  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_en_P3_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_rddata_cs_P0_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_rddata_cs_P1_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_rddata_cs_P2_out
   ,output  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_rddata_cs_P3_out


  ,output logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi0_rddata_W0
  ,output logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi0_rddata_W1
  ,output logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi0_rddata_W2
  ,output logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi0_rddata_W3
  ,output logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi0_rddata_dbi_W0
  ,output logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi0_rddata_dbi_W1
  ,output logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi0_rddata_dbi_W2
  ,output logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi0_rddata_dbi_W3
  ,output logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_rddata_valid_W0
  ,output logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_rddata_valid_W1
  ,output logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_rddata_valid_W2
  ,output logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_rddata_valid_W3

  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_rddata_en_P0
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_rddata_en_P1
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_rddata_en_P2
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi0_rddata_en_P3
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi0_rddata_cs_P0
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi0_rddata_cs_P1
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi0_rddata_cs_P2
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi0_rddata_cs_P3

  ,output logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi1_rddata_W0
  ,output logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi1_rddata_W1
  ,output logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi1_rddata_W2
  ,output logic [DFI_DATA_WIDTH-1:0]                               dp0_dfi1_rddata_W3
  ,output logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi1_rddata_dbi_W0
  ,output logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi1_rddata_dbi_W1
  ,output logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi1_rddata_dbi_W2
  ,output logic [(DFI_DATA_WIDTH/8)-1:0]                           dp0_dfi1_rddata_dbi_W3
  ,output logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_rddata_valid_W0
  ,output logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_rddata_valid_W1
  ,output logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_rddata_valid_W2
  ,output logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_rddata_valid_W3

  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_rddata_en_P0
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_rddata_en_P1
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_rddata_en_P2
  ,input logic [DFI_DATAEN_WIDTH-1:0]                             dp0_dfi1_rddata_en_P3
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi1_rddata_cs_P0
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi1_rddata_cs_P1
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi1_rddata_cs_P2
  ,input logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dp0_dfi1_rddata_cs_P3


  ,input logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dp0_dwc_ddrphy0_snoop_en_P0
  ,input logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dp0_dwc_ddrphy0_snoop_en_P1
  ,input logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dp0_dwc_ddrphy0_snoop_en_P2
  ,input logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dp0_dwc_ddrphy0_snoop_en_P3
  ,output  logic [(DFI_DATAEN_WIDTH*4)-1:0]                       dwc_ddrphy0_snoop_en_P0_out
  ,output  logic [(DFI_DATAEN_WIDTH*4)-1:0]                       dwc_ddrphy0_snoop_en_P1_out
  ,output  logic [(DFI_DATAEN_WIDTH*4)-1:0]                       dwc_ddrphy0_snoop_en_P2_out
  ,output  logic [(DFI_DATAEN_WIDTH*4)-1:0]                       dwc_ddrphy0_snoop_en_P3_out

  ,input logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dp0_dwc_ddrphy1_snoop_en_P0
  ,input logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dp0_dwc_ddrphy1_snoop_en_P1
  ,input logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dp0_dwc_ddrphy1_snoop_en_P2
  ,input logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dp0_dwc_ddrphy1_snoop_en_P3
  ,output  logic [(DFI_DATAEN_WIDTH*4)-1:0]                       dwc_ddrphy1_snoop_en_P0_out
  ,output  logic [(DFI_DATAEN_WIDTH*4)-1:0]                       dwc_ddrphy1_snoop_en_P1_out
  ,output  logic [(DFI_DATAEN_WIDTH*4)-1:0]                       dwc_ddrphy1_snoop_en_P2_out
  ,output  logic [(DFI_DATAEN_WIDTH*4)-1:0]                       dwc_ddrphy1_snoop_en_P3_out

  ,input   logic                                                  core_ddrc_core_clk
  ,input   logic                                                  core_ddrc_rstn


);

   //--------------------------------------------------------------------------
   // Local Parameters
   //--------------------------------------------------------------------------


//LPDDRC 64bit FBW mode:straiht through  HBW mode:exchange DFI1 and DFI2 
//There is a selector added in dfi_ic.sv for HBW mode,so move FF from dfi_ic_dp_lpddr.sv to dfi_ic.sv 
  logic [DFI_DATA_WIDTH-1:0]                               dfi0_wrdata_P0_w;
  logic [DFI_DATA_WIDTH-1:0]                               dfi0_wrdata_P1_w;
  logic [DFI_DATA_WIDTH-1:0]                               dfi0_wrdata_P2_w;
  logic [DFI_DATA_WIDTH-1:0]                               dfi0_wrdata_P3_w;
  logic [DFI_MASK_WIDTH-1:0]                               dfi0_wrdata_mask_P0_w;
  logic [DFI_MASK_WIDTH-1:0]                               dfi0_wrdata_mask_P1_w;
  logic [DFI_MASK_WIDTH-1:0]                               dfi0_wrdata_mask_P2_w;
  logic [DFI_MASK_WIDTH-1:0]                               dfi0_wrdata_mask_P3_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_wrdata_en_P0_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_wrdata_en_P1_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_wrdata_en_P2_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_wrdata_en_P3_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi0_wrdata_cs_P0_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi0_wrdata_cs_P1_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi0_wrdata_cs_P2_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi0_wrdata_cs_P3_w;
  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_wrdata_ecc_P0_w;
  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_wrdata_ecc_P1_w;
  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_wrdata_ecc_P2_w;
  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi0_wrdata_ecc_P3_w;
  logic [DFI_DATA_WIDTH-1:0]                               dfi1_wrdata_P0_w;
  logic [DFI_DATA_WIDTH-1:0]                               dfi1_wrdata_P1_w;
  logic [DFI_DATA_WIDTH-1:0]                               dfi1_wrdata_P2_w;
  logic [DFI_DATA_WIDTH-1:0]                               dfi1_wrdata_P3_w;
  logic [DFI_MASK_WIDTH-1:0]                               dfi1_wrdata_mask_P0_w;
  logic [DFI_MASK_WIDTH-1:0]                               dfi1_wrdata_mask_P1_w;
  logic [DFI_MASK_WIDTH-1:0]                               dfi1_wrdata_mask_P2_w;
  logic [DFI_MASK_WIDTH-1:0]                               dfi1_wrdata_mask_P3_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_wrdata_en_P0_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_wrdata_en_P1_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_wrdata_en_P2_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_wrdata_en_P3_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_wrdata_cs_P0_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_wrdata_cs_P1_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_wrdata_cs_P2_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_wrdata_cs_P3_w;
  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_wrdata_ecc_P0_w;
  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_wrdata_ecc_P1_w;
  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_wrdata_ecc_P2_w;
  logic [(DFI_DATA_WIDTH/8)-1:0]                           dfi1_wrdata_ecc_P3_w;


  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_en_P0_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_en_P1_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_en_P2_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi0_rddata_en_P3_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi0_rddata_cs_P0_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi0_rddata_cs_P1_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi0_rddata_cs_P2_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi0_rddata_cs_P3_w;

  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_en_P0_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_en_P1_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_en_P2_w;
  logic [DFI_DATAEN_WIDTH-1:0]                             dfi1_rddata_en_P3_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_rddata_cs_P0_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_rddata_cs_P1_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_rddata_cs_P2_w;
  logic [(DFI_DATAEN_WIDTH*DFI1_CS_WIDTH)-1:0]             dfi1_rddata_cs_P3_w;


  logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dwc_ddrphy0_snoop_en_P0_w;
  logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dwc_ddrphy0_snoop_en_P1_w;
  logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dwc_ddrphy0_snoop_en_P2_w;
  logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dwc_ddrphy0_snoop_en_P3_w;

  logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dwc_ddrphy1_snoop_en_P0_w;
  logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dwc_ddrphy1_snoop_en_P1_w;
  logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dwc_ddrphy1_snoop_en_P2_w;
  logic [(DFI_DATAEN_WIDTH*4)-1:0]                         dwc_ddrphy1_snoop_en_P3_w;



//dfi data path signal swaping
  assign dfi0_wrdata_P0_w                   = dp0_dfi0_wrdata_P0 ;
  assign dfi0_wrdata_P1_w                   = dp0_dfi0_wrdata_P1 ;
  assign dfi0_wrdata_P2_w                   = dp0_dfi0_wrdata_P2 ;
  assign dfi0_wrdata_P3_w                   = dp0_dfi0_wrdata_P3 ;
  assign dfi0_wrdata_mask_P0_w              = dp0_dfi0_wrdata_mask_P0;
  assign dfi0_wrdata_mask_P1_w              = dp0_dfi0_wrdata_mask_P1;
  assign dfi0_wrdata_mask_P2_w              = dp0_dfi0_wrdata_mask_P2;
  assign dfi0_wrdata_mask_P3_w              = dp0_dfi0_wrdata_mask_P3;
  assign dfi0_wrdata_en_P0_w                = dp0_dfi0_wrdata_en_P0;
  assign dfi0_wrdata_en_P1_w                = dp0_dfi0_wrdata_en_P1;
  assign dfi0_wrdata_en_P2_w                = dp0_dfi0_wrdata_en_P2;
  assign dfi0_wrdata_en_P3_w                = dp0_dfi0_wrdata_en_P3;
  assign dfi0_wrdata_cs_P0_w                = dp0_dfi0_wrdata_cs_P0;
  assign dfi0_wrdata_cs_P1_w                = dp0_dfi0_wrdata_cs_P1;
  assign dfi0_wrdata_cs_P2_w                = dp0_dfi0_wrdata_cs_P2;
  assign dfi0_wrdata_cs_P3_w                = dp0_dfi0_wrdata_cs_P3;
  assign dfi0_wrdata_ecc_P0_w               = dp0_dfi0_wrdata_ecc_P0;
  assign dfi0_wrdata_ecc_P1_w               = dp0_dfi0_wrdata_ecc_P1;
  assign dfi0_wrdata_ecc_P2_w               = dp0_dfi0_wrdata_ecc_P2;
  assign dfi0_wrdata_ecc_P3_w               = dp0_dfi0_wrdata_ecc_P3;
  assign dp0_dfi0_rddata_W0              = dfi0_rddata_W0     ;
  assign dp0_dfi0_rddata_W1              = dfi0_rddata_W1     ;
  assign dp0_dfi0_rddata_W2              = dfi0_rddata_W2     ;
  assign dp0_dfi0_rddata_W3              = dfi0_rddata_W3     ;
  assign dp0_dfi0_rddata_dbi_W0          = dfi0_rddata_dbi_W0  ;
  assign dp0_dfi0_rddata_dbi_W1          = dfi0_rddata_dbi_W1  ;
  assign dp0_dfi0_rddata_dbi_W2          = dfi0_rddata_dbi_W2  ;
  assign dp0_dfi0_rddata_dbi_W3          = dfi0_rddata_dbi_W3  ;
  assign dp0_dfi0_rddata_valid_W0        = dfi0_rddata_valid_W0;
  assign dp0_dfi0_rddata_valid_W1        = dfi0_rddata_valid_W1;
  assign dp0_dfi0_rddata_valid_W2        = dfi0_rddata_valid_W2;
  assign dp0_dfi0_rddata_valid_W3        = dfi0_rddata_valid_W3;
  assign dfi0_rddata_en_P0_w                = dp0_dfi0_rddata_en_P0;
  assign dfi0_rddata_en_P1_w                = dp0_dfi0_rddata_en_P1;
  assign dfi0_rddata_en_P2_w                = dp0_dfi0_rddata_en_P2;
  assign dfi0_rddata_en_P3_w                = dp0_dfi0_rddata_en_P3;
  assign dfi0_rddata_cs_P0_w                = dp0_dfi0_rddata_cs_P0;
  assign dfi0_rddata_cs_P1_w                = dp0_dfi0_rddata_cs_P1;
  assign dfi0_rddata_cs_P2_w                = dp0_dfi0_rddata_cs_P2;
  assign dfi0_rddata_cs_P3_w                = dp0_dfi0_rddata_cs_P3;
  assign dwc_ddrphy0_snoop_en_P0_w          = dp0_dwc_ddrphy0_snoop_en_P0;
  assign dwc_ddrphy0_snoop_en_P1_w          = dp0_dwc_ddrphy0_snoop_en_P1;
  assign dwc_ddrphy0_snoop_en_P2_w          = dp0_dwc_ddrphy0_snoop_en_P2;
  assign dwc_ddrphy0_snoop_en_P3_w          = dp0_dwc_ddrphy0_snoop_en_P3;
  assign dfi1_wrdata_P0_w                     = dp0_dfi1_wrdata_P0;
  assign dfi1_wrdata_P1_w                     = dp0_dfi1_wrdata_P1;
  assign dfi1_wrdata_P2_w                     = dp0_dfi1_wrdata_P2;
  assign dfi1_wrdata_P3_w                     = dp0_dfi1_wrdata_P3;
  assign dfi1_wrdata_mask_P0_w                = dp0_dfi1_wrdata_mask_P0;
  assign dfi1_wrdata_mask_P1_w                = dp0_dfi1_wrdata_mask_P1;
  assign dfi1_wrdata_mask_P2_w                = dp0_dfi1_wrdata_mask_P2;
  assign dfi1_wrdata_mask_P3_w                = dp0_dfi1_wrdata_mask_P3;
  assign dfi1_wrdata_en_P0_w                  = dp0_dfi1_wrdata_en_P0;
  assign dfi1_wrdata_en_P1_w                  = dp0_dfi1_wrdata_en_P1;
  assign dfi1_wrdata_en_P2_w                  = dp0_dfi1_wrdata_en_P2;
  assign dfi1_wrdata_en_P3_w                  = dp0_dfi1_wrdata_en_P3;
  assign dfi1_wrdata_cs_P0_w                  = dp0_dfi1_wrdata_cs_P0;
  assign dfi1_wrdata_cs_P1_w                  = dp0_dfi1_wrdata_cs_P1;
  assign dfi1_wrdata_cs_P2_w                  = dp0_dfi1_wrdata_cs_P2;
  assign dfi1_wrdata_cs_P3_w                  = dp0_dfi1_wrdata_cs_P3;
  assign dfi1_wrdata_ecc_P0_w                 = dp0_dfi1_wrdata_ecc_P0;
  assign dfi1_wrdata_ecc_P1_w                 = dp0_dfi1_wrdata_ecc_P1;
  assign dfi1_wrdata_ecc_P2_w                 = dp0_dfi1_wrdata_ecc_P2;
  assign dfi1_wrdata_ecc_P3_w                 = dp0_dfi1_wrdata_ecc_P3;
  assign dp0_dfi1_rddata_W0                = dfi1_rddata_W0      ;
  assign dp0_dfi1_rddata_W1                = dfi1_rddata_W1      ;
  assign dp0_dfi1_rddata_W2                = dfi1_rddata_W2      ;
  assign dp0_dfi1_rddata_W3                = dfi1_rddata_W3      ;
  assign dp0_dfi1_rddata_dbi_W0            = dfi1_rddata_dbi_W0  ;
  assign dp0_dfi1_rddata_dbi_W1            = dfi1_rddata_dbi_W1  ;
  assign dp0_dfi1_rddata_dbi_W2            = dfi1_rddata_dbi_W2  ;
  assign dp0_dfi1_rddata_dbi_W3            = dfi1_rddata_dbi_W3  ;
  assign dp0_dfi1_rddata_valid_W0          = dfi1_rddata_valid_W0;
  assign dp0_dfi1_rddata_valid_W1          = dfi1_rddata_valid_W1;
  assign dp0_dfi1_rddata_valid_W2          = dfi1_rddata_valid_W2;
  assign dp0_dfi1_rddata_valid_W3          = dfi1_rddata_valid_W3;
  assign dfi1_rddata_en_P0_w                  = dp0_dfi1_rddata_en_P0;
  assign dfi1_rddata_en_P1_w                  = dp0_dfi1_rddata_en_P1;
  assign dfi1_rddata_en_P2_w                  = dp0_dfi1_rddata_en_P2;
  assign dfi1_rddata_en_P3_w                  = dp0_dfi1_rddata_en_P3;
  assign dfi1_rddata_cs_P0_w                  = dp0_dfi1_rddata_cs_P0;
  assign dfi1_rddata_cs_P1_w                  = dp0_dfi1_rddata_cs_P1;
  assign dfi1_rddata_cs_P2_w                  = dp0_dfi1_rddata_cs_P2;
  assign dfi1_rddata_cs_P3_w                  = dp0_dfi1_rddata_cs_P3;
  assign dwc_ddrphy1_snoop_en_P0_w            = dp0_dwc_ddrphy1_snoop_en_P0;
  assign dwc_ddrphy1_snoop_en_P1_w            = dp0_dwc_ddrphy1_snoop_en_P1;
  assign dwc_ddrphy1_snoop_en_P2_w            = dp0_dwc_ddrphy1_snoop_en_P2;
  assign dwc_ddrphy1_snoop_en_P3_w            = dp0_dwc_ddrphy1_snoop_en_P3;

// dfi data path signal flipflop
logic dfi0_rddata_en_out_update;
assign dfi0_rddata_en_out_update = (dfi0_rddata_en_P0_out != dfi0_rddata_en_P0_w)
                                  |(dfi0_rddata_en_P1_out != dfi0_rddata_en_P1_w)
                                  |(dfi0_rddata_en_P2_out != dfi0_rddata_en_P2_w)
                                  |(dfi0_rddata_en_P3_out != dfi0_rddata_en_P3_w) ;
logic dfi0_wrdata_en_out_update;
assign dfi0_wrdata_en_out_update = (dfi0_wrdata_en_P0_out != dfi0_wrdata_en_P0_w)
                                  |(dfi0_wrdata_en_P1_out != dfi0_wrdata_en_P1_w)
                                  |(dfi0_wrdata_en_P2_out != dfi0_wrdata_en_P2_w)
                                  |(dfi0_wrdata_en_P3_out != dfi0_wrdata_en_P3_w) ;

logic dfi1_rddata_en_out_update;
assign dfi1_rddata_en_out_update = (dfi1_rddata_en_P0_out != dfi1_rddata_en_P0_w)
                                  |(dfi1_rddata_en_P1_out != dfi1_rddata_en_P1_w)
                                  |(dfi1_rddata_en_P2_out != dfi1_rddata_en_P2_w)
                                  |(dfi1_rddata_en_P3_out != dfi1_rddata_en_P3_w) ;
logic dfi1_wrdata_en_out_update;
assign dfi1_wrdata_en_out_update = (dfi1_wrdata_en_P0_out != dfi1_wrdata_en_P0_w)
                                  |(dfi1_wrdata_en_P1_out != dfi1_wrdata_en_P1_w)
                                  |(dfi1_wrdata_en_P2_out != dfi1_wrdata_en_P2_w)
                                  |(dfi1_wrdata_en_P3_out != dfi1_wrdata_en_P3_w) ;

   always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         dfi0_wrdata_P0_out            <= '0;
         dfi0_wrdata_P1_out            <= '0;
         dfi0_wrdata_P2_out            <= '0;
         dfi0_wrdata_P3_out            <= '0;
         dfi0_wrdata_mask_P0_out       <= '0;
         dfi0_wrdata_mask_P1_out       <= '0;
         dfi0_wrdata_mask_P2_out       <= '0;
         dfi0_wrdata_mask_P3_out       <= '0;
         dfi1_wrdata_P0_out            <= '0;
         dfi1_wrdata_P1_out            <= '0;
         dfi1_wrdata_P2_out            <= '0;
         dfi1_wrdata_P3_out            <= '0;
         dfi1_wrdata_mask_P0_out       <= '0;
         dfi1_wrdata_mask_P1_out       <= '0;
         dfi1_wrdata_mask_P2_out       <= '0;
         dfi1_wrdata_mask_P3_out       <= '0;
         dfi0_wrdata_ecc_P0_out        <= '0;
         dfi0_wrdata_ecc_P1_out        <= '0;
         dfi0_wrdata_ecc_P2_out        <= '0;
         dfi0_wrdata_ecc_P3_out        <= '0;
         dfi1_wrdata_ecc_P0_out        <= '0;
         dfi1_wrdata_ecc_P1_out        <= '0;
         dfi1_wrdata_ecc_P2_out        <= '0;
         dfi1_wrdata_ecc_P3_out        <= '0;
         dfi0_wrdata_en_P0_out         <= '0;
         dfi0_wrdata_en_P1_out         <= '0;
         dfi0_wrdata_en_P2_out         <= '0;
         dfi0_wrdata_en_P3_out         <= '0;
         dfi0_wrdata_cs_P0_out         <= '0;
         dfi0_wrdata_cs_P1_out         <= '0;
         dfi0_wrdata_cs_P2_out         <= '0;
         dfi0_wrdata_cs_P3_out         <= '0;
         dfi1_wrdata_en_P0_out         <= '0;
         dfi1_wrdata_en_P1_out         <= '0;
         dfi1_wrdata_en_P2_out         <= '0;
         dfi1_wrdata_en_P3_out         <= '0;
         dfi1_wrdata_cs_P0_out         <= '0;
         dfi1_wrdata_cs_P1_out         <= '0;
         dfi1_wrdata_cs_P2_out         <= '0;
         dfi1_wrdata_cs_P3_out         <= '0;
      end else begin
         if (|(dfi0_wrdata_P0_out ^ dfi0_wrdata_P0_w)) begin
            dfi0_wrdata_P0_out            <= dfi0_wrdata_P0_w;
         end
         if (|(dfi0_wrdata_P1_out ^ dfi0_wrdata_P1_w)) begin
            dfi0_wrdata_P1_out            <= dfi0_wrdata_P1_w;
         end
         if (|(dfi0_wrdata_P2_out ^ dfi0_wrdata_P2_w)) begin
            dfi0_wrdata_P2_out            <= dfi0_wrdata_P2_w;
         end
         if (|(dfi0_wrdata_P3_out ^ dfi0_wrdata_P3_w)) begin
            dfi0_wrdata_P3_out            <= dfi0_wrdata_P3_w;
         end
         if (|(dfi0_wrdata_mask_P0_out ^ dfi0_wrdata_mask_P0_w)) begin
            dfi0_wrdata_mask_P0_out       <= dfi0_wrdata_mask_P0_w;
         end
         if (|(dfi0_wrdata_mask_P1_out ^ dfi0_wrdata_mask_P1_w)) begin
            dfi0_wrdata_mask_P1_out       <= dfi0_wrdata_mask_P1_w;
         end
         if (|(dfi0_wrdata_mask_P2_out ^ dfi0_wrdata_mask_P2_w)) begin
            dfi0_wrdata_mask_P2_out       <= dfi0_wrdata_mask_P2_w;
         end
         if (|(dfi0_wrdata_mask_P3_out ^ dfi0_wrdata_mask_P3_w)) begin
            dfi0_wrdata_mask_P3_out       <= dfi0_wrdata_mask_P3_w;
         end
         if (|(dfi1_wrdata_P0_out ^ dfi1_wrdata_P0_w)) begin
            dfi1_wrdata_P0_out            <= dfi1_wrdata_P0_w;
         end
         if (|(dfi1_wrdata_P1_out ^ dfi1_wrdata_P1_w)) begin
            dfi1_wrdata_P1_out            <= dfi1_wrdata_P1_w;
         end
         if (|(dfi1_wrdata_P2_out ^ dfi1_wrdata_P2_w)) begin
            dfi1_wrdata_P2_out            <= dfi1_wrdata_P2_w;
         end
         if (|(dfi1_wrdata_P3_out ^ dfi1_wrdata_P3_w)) begin
            dfi1_wrdata_P3_out            <= dfi1_wrdata_P3_w;
         end
         if (|(dfi1_wrdata_mask_P0_out ^ dfi1_wrdata_mask_P0_w)) begin
            dfi1_wrdata_mask_P0_out       <= dfi1_wrdata_mask_P0_w;
         end
         if (|(dfi1_wrdata_mask_P1_out ^ dfi1_wrdata_mask_P1_w)) begin
            dfi1_wrdata_mask_P1_out       <= dfi1_wrdata_mask_P1_w;
         end
         if (|(dfi1_wrdata_mask_P2_out ^ dfi1_wrdata_mask_P2_w)) begin
            dfi1_wrdata_mask_P2_out       <= dfi1_wrdata_mask_P2_w;
         end
         if (|(dfi1_wrdata_mask_P3_out ^ dfi1_wrdata_mask_P3_w)) begin
            dfi1_wrdata_mask_P3_out       <= dfi1_wrdata_mask_P3_w;
         end
         if (|(dfi0_wrdata_ecc_P0_out ^ dfi0_wrdata_ecc_P0_w)) begin
            dfi0_wrdata_ecc_P0_out        <= dfi0_wrdata_ecc_P0_w;
         end
         if (|(dfi0_wrdata_ecc_P1_out ^ dfi0_wrdata_ecc_P1_w)) begin
            dfi0_wrdata_ecc_P1_out        <= dfi0_wrdata_ecc_P1_w;
         end
         if (|(dfi0_wrdata_ecc_P2_out ^ dfi0_wrdata_ecc_P2_w)) begin
            dfi0_wrdata_ecc_P2_out        <= dfi0_wrdata_ecc_P2_w;
         end
         if (|(dfi0_wrdata_ecc_P3_out ^ dfi0_wrdata_ecc_P3_w)) begin
            dfi0_wrdata_ecc_P3_out        <= dfi0_wrdata_ecc_P3_w;
         end
         if (|(dfi1_wrdata_ecc_P0_out ^ dfi1_wrdata_ecc_P0_w)) begin
            dfi1_wrdata_ecc_P0_out        <= dfi1_wrdata_ecc_P0_w;
         end
         if (|(dfi1_wrdata_ecc_P1_out ^ dfi1_wrdata_ecc_P1_w)) begin
            dfi1_wrdata_ecc_P1_out        <= dfi1_wrdata_ecc_P1_w;
         end
         if (|(dfi1_wrdata_ecc_P2_out ^ dfi1_wrdata_ecc_P2_w)) begin
            dfi1_wrdata_ecc_P2_out        <= dfi1_wrdata_ecc_P2_w;
         end
         if (|(dfi1_wrdata_ecc_P3_out ^ dfi1_wrdata_ecc_P3_w)) begin
            dfi1_wrdata_ecc_P3_out        <= dfi1_wrdata_ecc_P3_w;
         end
         if (dfi0_wrdata_en_out_update) begin
            dfi0_wrdata_en_P0_out         <= dfi0_wrdata_en_P0_w;
            dfi0_wrdata_en_P1_out         <= dfi0_wrdata_en_P1_w;
            dfi0_wrdata_en_P2_out         <= dfi0_wrdata_en_P2_w;
            dfi0_wrdata_en_P3_out         <= dfi0_wrdata_en_P3_w;
         end
         if (|(dfi0_wrdata_cs_P0_out ^ dfi0_wrdata_cs_P0_w)) begin
            dfi0_wrdata_cs_P0_out         <= dfi0_wrdata_cs_P0_w;
         end
         if (|(dfi0_wrdata_cs_P1_out ^ dfi0_wrdata_cs_P1_w)) begin
            dfi0_wrdata_cs_P1_out         <= dfi0_wrdata_cs_P1_w;
         end         
         if (|(dfi0_wrdata_cs_P2_out ^ dfi0_wrdata_cs_P2_w)) begin
            dfi0_wrdata_cs_P2_out         <= dfi0_wrdata_cs_P2_w;
         end
         if (|(dfi0_wrdata_cs_P3_out ^ dfi0_wrdata_cs_P3_w)) begin
            dfi0_wrdata_cs_P3_out         <= dfi0_wrdata_cs_P3_w;
         end
         if (dfi1_wrdata_en_out_update) begin
            dfi1_wrdata_en_P0_out         <= dfi1_wrdata_en_P0_w;
            dfi1_wrdata_en_P1_out         <= dfi1_wrdata_en_P1_w;
            dfi1_wrdata_en_P2_out         <= dfi1_wrdata_en_P2_w;
            dfi1_wrdata_en_P3_out         <= dfi1_wrdata_en_P3_w;
         end
         if (|(dfi1_wrdata_cs_P0_out ^ dfi1_wrdata_cs_P0_w)) begin
            dfi1_wrdata_cs_P0_out         <= dfi1_wrdata_cs_P0_w;
         end
         if (|(dfi1_wrdata_cs_P1_out ^ dfi1_wrdata_cs_P1_w)) begin
            dfi1_wrdata_cs_P1_out         <= dfi1_wrdata_cs_P1_w;
         end         
         if (|(dfi1_wrdata_cs_P2_out ^ dfi1_wrdata_cs_P2_w)) begin
            dfi1_wrdata_cs_P2_out         <= dfi1_wrdata_cs_P2_w;
         end
         if (|(dfi1_wrdata_cs_P3_out ^ dfi1_wrdata_cs_P3_w)) begin
            dfi1_wrdata_cs_P3_out         <= dfi1_wrdata_cs_P3_w;
         end
      end
   end


   always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         dfi0_rddata_en_P0_out         <= '0;
         dfi0_rddata_en_P1_out         <= '0;
         dfi0_rddata_en_P2_out         <= '0;
         dfi0_rddata_en_P3_out         <= '0;
         dfi0_rddata_cs_P0_out         <= '0;
         dfi0_rddata_cs_P1_out         <= '0;
         dfi0_rddata_cs_P2_out         <= '0;
         dfi0_rddata_cs_P3_out         <= '0;
         dwc_ddrphy0_snoop_en_P0_out   <= '0;
         dwc_ddrphy0_snoop_en_P1_out   <= '0;
         dwc_ddrphy0_snoop_en_P2_out   <= '0;
         dwc_ddrphy0_snoop_en_P3_out   <= '0;
         dfi1_rddata_en_P0_out         <= '0;
         dfi1_rddata_en_P1_out         <= '0;
         dfi1_rddata_en_P2_out         <= '0;
         dfi1_rddata_en_P3_out         <= '0;
         dfi1_rddata_cs_P0_out         <= '0;
         dfi1_rddata_cs_P1_out         <= '0;
         dfi1_rddata_cs_P2_out         <= '0;
         dfi1_rddata_cs_P3_out         <= '0;
         dwc_ddrphy1_snoop_en_P0_out   <= '0;
         dwc_ddrphy1_snoop_en_P1_out   <= '0;
         dwc_ddrphy1_snoop_en_P2_out   <= '0;
         dwc_ddrphy1_snoop_en_P3_out   <= '0;
      end else begin
         if (dfi0_rddata_en_out_update) begin
            dfi0_rddata_en_P0_out         <= dfi0_rddata_en_P0_w;
            dfi0_rddata_en_P1_out         <= dfi0_rddata_en_P1_w;
            dfi0_rddata_en_P2_out         <= dfi0_rddata_en_P2_w;
            dfi0_rddata_en_P3_out         <= dfi0_rddata_en_P3_w;
         end
         if (|(dfi0_rddata_cs_P0_out ^ dfi0_rddata_cs_P0_w)) begin
            dfi0_rddata_cs_P0_out         <= dfi0_rddata_cs_P0_w;
         end
         if (|(dfi0_rddata_cs_P1_out ^ dfi0_rddata_cs_P1_w)) begin
            dfi0_rddata_cs_P1_out         <= dfi0_rddata_cs_P1_w;
         end
         if (|(dfi0_rddata_cs_P2_out ^ dfi0_rddata_cs_P2_w)) begin
            dfi0_rddata_cs_P2_out         <= dfi0_rddata_cs_P2_w;
         end
         if (|(dfi0_rddata_cs_P3_out ^ dfi0_rddata_cs_P3_w)) begin
            dfi0_rddata_cs_P3_out         <= dfi0_rddata_cs_P3_w;
         end
         if (|(dwc_ddrphy0_snoop_en_P0_out ^ dwc_ddrphy0_snoop_en_P0_w)) begin
            dwc_ddrphy0_snoop_en_P0_out   <= dwc_ddrphy0_snoop_en_P0_w;
         end
         if (|(dwc_ddrphy0_snoop_en_P1_out ^ dwc_ddrphy0_snoop_en_P1_w)) begin
            dwc_ddrphy0_snoop_en_P1_out   <= dwc_ddrphy0_snoop_en_P1_w;
         end
         if (|(dwc_ddrphy0_snoop_en_P2_out ^ dwc_ddrphy0_snoop_en_P2_w)) begin
            dwc_ddrphy0_snoop_en_P2_out   <= dwc_ddrphy0_snoop_en_P2_w;
         end
         if (|(dwc_ddrphy0_snoop_en_P3_out ^ dwc_ddrphy0_snoop_en_P3_w)) begin
            dwc_ddrphy0_snoop_en_P3_out   <= dwc_ddrphy0_snoop_en_P3_w;
         end
         if (dfi1_rddata_en_out_update) begin
            dfi1_rddata_en_P0_out         <= dfi1_rddata_en_P0_w;
            dfi1_rddata_en_P1_out         <= dfi1_rddata_en_P1_w;
            dfi1_rddata_en_P2_out         <= dfi1_rddata_en_P2_w;
            dfi1_rddata_en_P3_out         <= dfi1_rddata_en_P3_w;
         end
         if (|(dfi1_rddata_cs_P0_out ^ dfi1_rddata_cs_P0_w)) begin
            dfi1_rddata_cs_P0_out         <= dfi1_rddata_cs_P0_w;
         end
         if (|(dfi1_rddata_cs_P1_out ^ dfi1_rddata_cs_P1_w)) begin
            dfi1_rddata_cs_P1_out         <= dfi1_rddata_cs_P1_w;
         end
         if (|(dfi1_rddata_cs_P2_out ^ dfi1_rddata_cs_P2_w)) begin
            dfi1_rddata_cs_P2_out         <= dfi1_rddata_cs_P2_w;
         end
         if (|(dfi1_rddata_cs_P3_out ^ dfi1_rddata_cs_P3_w)) begin
            dfi1_rddata_cs_P3_out         <= dfi1_rddata_cs_P3_w;
         end
         if (|(dwc_ddrphy1_snoop_en_P0_out ^ dwc_ddrphy1_snoop_en_P0_w)) begin
            dwc_ddrphy1_snoop_en_P0_out   <= dwc_ddrphy1_snoop_en_P0_w;
         end
         if (|(dwc_ddrphy1_snoop_en_P1_out ^ dwc_ddrphy1_snoop_en_P1_w)) begin
            dwc_ddrphy1_snoop_en_P1_out   <= dwc_ddrphy1_snoop_en_P1_w;
         end
         if (|(dwc_ddrphy1_snoop_en_P2_out ^ dwc_ddrphy1_snoop_en_P2_w)) begin
            dwc_ddrphy1_snoop_en_P2_out   <= dwc_ddrphy1_snoop_en_P2_w;
         end
         if (|(dwc_ddrphy1_snoop_en_P3_out ^ dwc_ddrphy1_snoop_en_P3_w)) begin
            dwc_ddrphy1_snoop_en_P3_out   <= dwc_ddrphy1_snoop_en_P3_w;
         end
      end
   end

//dfi data path signal OCCAP protection



endmodule : dfi_ic_dp_lpddr_ff
