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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/dfi/dfi_ic_cp_ff.sv#1 $
// -------------------------------------------------------------------------
// Description:
//            dfi command path signal swaping
//            dfi command path signal flipflop
//            dfi command path signal OCCAP protection
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module dfi_ic_cp_ff
import DWC_ddrctl_reg_pkg::*;
#(
    parameter     NUM_RANKS                     = `MEMC_NUM_RANKS
   ,parameter     DFI0_CS_WIDTH                 = `DDRCTL_DFI0_CS_WIDTH
   ,parameter     DFI1_CS_WIDTH                 = `DDRCTL_DFI1_CS_WIDTH
   ,parameter     DFI2_CS_WIDTH                 = `DDRCTL_DFI2_CS_WIDTH
   ,parameter     DFI3_CS_WIDTH                 = `DDRCTL_DFI3_CS_WIDTH
   ,parameter     FREQ_RATIO                    = `MEMC_FREQ_RATIO
   ,parameter     LPDDR_DUAL_CHANNEL_EN         = `DDRCTL_LPDDR_DUAL_CHANNEL_EN
   ,parameter     RESET_WIDTH                   = `UMCTL2_RESET_WIDTH
   ,parameter     NUM_CLKS                      = `MEMC_NUM_CLKS
   ,parameter     BANK_BITS                     = `MEMC_BANK_BITS
   ,parameter     BG_BITS                       = `MEMC_BG_BITS
   ,parameter     CID_WIDTH                     = `UMCTL2_CID_WIDTH
   ,parameter     DFI_DATA_WIDTH                = `DDRCTL_DFI_DATA_WIDTH
   ,parameter     DFI_ADDR_WIDTH                = `MEMC_DFI_ADDR_WIDTH
   ,parameter     DFI_BG_WIDTH                  = `DDRCTL_DFI_BG_WIDTH
   ,parameter     DFI_CID_WIDTH                 = `DDRCTL_DFI_CID_WIDTH
   ,parameter     DFI_LP_WAKEUP_WIDTH           = 4
   ,parameter     DFI_PARITY_IN_WIDTH           = 2
   ,parameter     REG_DFI_OUT_VAL               = `MEMC_REG_DFI_OUT_VAL
   ,parameter     OCCAP_EN                      = `UMCTL2_OCCAP_EN
   ,parameter     OCCAP_PIPELINE_EN             = 0
   ,parameter     BCM_VERIF_EN                  = 1
   ,parameter     BCM_DDRC_N_SYNC               = 2
   ,parameter     HIF_KEYID_WIDTH               = `DDRCTL_HIF_KEYID_WIDTH
)
(
    input logic [`MEMC_DFI_ADDR_WIDTH_P0-1:0]                      dfi0_address_P0
   ,input logic [`MEMC_DFI_ADDR_WIDTH_P1-1:0]                      dfi0_address_P1
   ,input logic [`MEMC_DFI_ADDR_WIDTH_P2-1:0]                      dfi0_address_P2
   ,input logic [`MEMC_DFI_ADDR_WIDTH_P3-1:0]                      dfi0_address_P3
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_cke_P0
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_cke_P1
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_cke_P2
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_cke_P3
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_cs_P0
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_cs_P1
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_cs_P2
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_cs_P3

   ,input logic [`MEMC_DFI_ADDR_WIDTH_P0-1:0]                      dfi1_address_P0
   ,input logic [`MEMC_DFI_ADDR_WIDTH_P1-1:0]                      dfi1_address_P1
   ,input logic [`MEMC_DFI_ADDR_WIDTH_P2-1:0]                      dfi1_address_P2
   ,input logic [`MEMC_DFI_ADDR_WIDTH_P3-1:0]                      dfi1_address_P3

   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_cke_P0 
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_cke_P1
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_cke_P2
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_cke_P3
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_cs_P0
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_cs_P1
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_cs_P2
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_cs_P3

   ,input logic [RESET_WIDTH-1:0]                                  dfi_reset_n
   ,input logic                                                    dfi0_init_start
   ,input logic [4:0]                                              dfi0_frequency
   ,input logic [1:0]                                              dfi0_freq_ratio
   ,input logic [1:0]                                              dfi0_freq_fsp

   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P0
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P1
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P2
   ,input logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P3
   ,input logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P0
   ,input logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P1
   ,input logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P2
   ,input logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P3
   ,input logic [1:0]                                              dfi0_wck_toggle_P0
   ,input logic [1:0]                                              dfi0_wck_toggle_P1
   ,input logic [1:0]                                              dfi0_wck_toggle_P2
   ,input logic [1:0]                                              dfi0_wck_toggle_P3
   ,input logic                                                    dwc_ddrphy0_snoop_running
   ,input logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P0
   ,input logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P1
   ,input logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P2
   ,input logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P3
   ,input logic                                                    dfi0_lp_ctrl_req
   ,input logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi0_lp_ctrl_wakeup
   ,input logic                                                    dfi0_lp_data_req
   ,input logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi0_lp_data_wakeup
   ,input logic                                                    dfi0_ctrlupd_req
   ,input logic [1:0]                                              dfi0_ctrlupd_type
   ,input logic                                                    dfi0_phyupd_ack
   ,input logic                                                    dfi0_phymstr_ack

   ,input logic                                                    dfi1_init_start
   ,input logic [4:0]                                              dfi1_frequency
   ,input logic [1:0]                                              dfi1_freq_ratio
   ,input logic [1:0]                                              dfi1_freq_fsp

   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P0 
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P1
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P2
   ,input logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P3
   ,input logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P0
   ,input logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P1
   ,input logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P2
   ,input logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P3
   ,input logic [1:0]                                              dfi1_wck_toggle_P0 
   ,input logic [1:0]                                              dfi1_wck_toggle_P1
   ,input logic [1:0]                                              dfi1_wck_toggle_P2
   ,input logic [1:0]                                              dfi1_wck_toggle_P3
   ,input logic                                                    dwc_ddrphy1_snoop_running

   ,input logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P0 
   ,input logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P1
   ,input logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P2
   ,input logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P3
   ,input logic                                                    dfi1_lp_ctrl_req
   ,input logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi1_lp_ctrl_wakeup
   ,input logic                                                    dfi1_lp_data_req
   ,input logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi1_lp_data_wakeup
   ,input logic                                                    dfi1_ctrlupd_req
   ,input logic [1:0]                                              dfi1_ctrlupd_type
   ,input logic                                                    dfi1_phyupd_ack
   ,input logic                                                    dfi1_phymstr_ack

   ,output  logic [`MEMC_DFI_ADDR_WIDTH_P0-1:0]                dfi0_address_P0_out
   ,output  logic [`MEMC_DFI_ADDR_WIDTH_P1-1:0]                dfi0_address_P1_out
   ,output  logic [`MEMC_DFI_ADDR_WIDTH_P2-1:0]                dfi0_address_P2_out
   ,output  logic [`MEMC_DFI_ADDR_WIDTH_P3-1:0]                dfi0_address_P3_out
   
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_cke_P0_out 
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_cke_P1_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_cke_P2_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_cke_P3_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_cs_P0_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_cs_P1_out 
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_cs_P2_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_cs_P3_out
   
   ,output  logic [`MEMC_DFI_ADDR_WIDTH_P0-1:0]                dfi1_address_P0_out 
   ,output  logic [`MEMC_DFI_ADDR_WIDTH_P1-1:0]                dfi1_address_P1_out
   ,output  logic [`MEMC_DFI_ADDR_WIDTH_P2-1:0]                dfi1_address_P2_out
   ,output  logic [`MEMC_DFI_ADDR_WIDTH_P3-1:0]                dfi1_address_P3_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_cke_P0_out 
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_cke_P1_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_cke_P2_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_cke_P3_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_cs_P0_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_cs_P1_out 
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_cs_P2_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_cs_P3_out
   
   ,output  logic [RESET_WIDTH-1:0]                                  dfi_reset_n_out
   ,output  logic                                                    dfi0_init_start_out
   ,output  logic [4:0]                                              dfi0_frequency_out
   ,output  logic [1:0]                                              dfi0_freq_ratio_out
   ,output  logic [1:0]                                              dfi0_freq_fsp_out
   
   ,output  logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P0_out 
   ,output  logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P1_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P2_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P3_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P0_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P1_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P2_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P3_out
   ,output  logic [1:0]                                              dfi0_wck_toggle_P0_out 
   ,output  logic [1:0]                                              dfi0_wck_toggle_P1_out
   ,output  logic [1:0]                                              dfi0_wck_toggle_P2_out
   ,output  logic [1:0]                                              dfi0_wck_toggle_P3_out
   ,output  logic                                                    dwc_ddrphy0_snoop_running_out
   
   ,output  logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P0_out  
   ,output  logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P1_out
   ,output  logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P2_out
   ,output  logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P3_out
   ,output  logic                                                    dfi0_lp_ctrl_req_out
   ,output  logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi0_lp_ctrl_wakeup_out
   ,output  logic                                                    dfi0_lp_data_req_out
   ,output  logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi0_lp_data_wakeup_out
   ,output  logic                                                    dfi0_ctrlupd_req_out
   ,output  logic [1:0]                                              dfi0_ctrlupd_type_out
   ,output  logic                                                    dfi0_phyupd_ack_out
   ,output  logic                                                    dfi0_phymstr_ack_out
   
   ,output  logic                                                    dfi1_init_start_out
   ,output  logic [4:0]                                              dfi1_frequency_out
   ,output  logic [1:0]                                              dfi1_freq_ratio_out
   ,output  logic [1:0]                                              dfi1_freq_fsp_out
   
   ,output  logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P0_out 
   ,output  logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P1_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P2_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P3_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P0_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P1_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P2_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P3_out
   ,output  logic [1:0]                                              dfi1_wck_toggle_P0_out 
   ,output  logic [1:0]                                              dfi1_wck_toggle_P1_out
   ,output  logic [1:0]                                              dfi1_wck_toggle_P2_out
   ,output  logic [1:0]                                              dfi1_wck_toggle_P3_out
   ,output  logic                                                    dwc_ddrphy1_snoop_running_out
   
   ,output  logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P0_out
   ,output  logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P1_out
   ,output  logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P2_out
   ,output  logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P3_out
   ,output  logic                                                    dfi1_lp_ctrl_req_out
   ,output  logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi1_lp_ctrl_wakeup_out
   ,output  logic                                                    dfi1_lp_data_req_out
   ,output  logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi1_lp_data_wakeup_out
   ,output  logic                                                    dfi1_ctrlupd_req_out
   ,output  logic [1:0]                                              dfi1_ctrlupd_type_out
   ,output  logic                                                    dfi1_phyupd_ack_out
   ,output  logic                                                    dfi1_phymstr_ack_out
   

   ,input   logic                                              core_ddrc_core_clk
   ,input   logic                                              core_ddrc_rstn



);

   //--------------------------------------------------------------------------
   // Local Parameters
   //--------------------------------------------------------------------------

   logic [`MEMC_DFI_ADDR_WIDTH_P0-1:0]                      dfi0_address_P0_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P1-1:0]                      dfi0_address_P1_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P2-1:0]                      dfi0_address_P2_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P3-1:0]                      dfi0_address_P3_w;
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_cke_P0_w; 
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_cke_P1_w;
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_cke_P2_w;
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_cke_P3_w;
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_cs_P0_w;
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_cs_P1_w; 
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_cs_P2_w;
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_cs_P3_w;

   logic [`MEMC_DFI_ADDR_WIDTH_P0-1:0]                      dfi1_address_P0_w; 
   logic [`MEMC_DFI_ADDR_WIDTH_P1-1:0]                      dfi1_address_P1_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P2-1:0]                      dfi1_address_P2_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P3-1:0]                      dfi1_address_P3_w;
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_cke_P0_w; 
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_cke_P1_w;
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_cke_P2_w;
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_cke_P3_w;
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_cs_P0_w;
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_cs_P1_w; 
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_cs_P2_w;
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_cs_P3_w;

   logic                                                    dfi0_init_start_w;
   logic [4:0]                                              dfi0_frequency_w;
   logic [1:0]                                              dfi0_freq_ratio_w;
   logic [1:0]                                              dfi0_freq_fsp_w;

   logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P0_w; 
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P1_w;
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P2_w;
   logic [DFI0_CS_WIDTH-1:0]                                dfi0_wck_cs_P3_w;
   logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P0_w;
   logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P1_w;
   logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P2_w;
   logic [DFI_DATA_WIDTH/16-1:0]                            dfi0_wck_en_P3_w;
   logic [1:0]                                              dfi0_wck_toggle_P0_w; 
   logic [1:0]                                              dfi0_wck_toggle_P1_w;
   logic [1:0]                                              dfi0_wck_toggle_P2_w;
   logic [1:0]                                              dfi0_wck_toggle_P3_w;
   logic                                                    dwc_ddrphy0_snoop_running_w;
   logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P0_w; 
   logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P1_w;
   logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P2_w;
   logic [NUM_CLKS-1:0]                                     dfi0_dram_clk_disable_P3_w;
   logic                                                    dfi0_lp_ctrl_req_w;
   logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi0_lp_ctrl_wakeup_w;
   logic                                                    dfi0_lp_data_req_w;
   logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi0_lp_data_wakeup_w;
   logic                                                    dfi0_ctrlupd_req_w;
   logic [1:0]                                              dfi0_ctrlupd_type_w;
   logic                                                    dfi0_phyupd_ack_w;
   logic                                                    dfi0_phymstr_ack_w;

   logic                                                    dfi1_init_start_w;
   logic [4:0]                                              dfi1_frequency_w;
   logic [1:0]                                              dfi1_freq_ratio_w;
   logic [1:0]                                              dfi1_freq_fsp_w;

   logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P0_w; 
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P1_w;
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P2_w;
   logic [DFI1_CS_WIDTH-1:0]                                dfi1_wck_cs_P3_w;
   logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P0_w;
   logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P1_w;
   logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P2_w;
   logic [DFI_DATA_WIDTH/16-1:0]                            dfi1_wck_en_P3_w;
   logic [1:0]                                              dfi1_wck_toggle_P0_w; 
   logic [1:0]                                              dfi1_wck_toggle_P1_w;
   logic [1:0]                                              dfi1_wck_toggle_P2_w;
   logic [1:0]                                              dfi1_wck_toggle_P3_w;
   logic                                                    dwc_ddrphy1_snoop_running_w;

   logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P0_w; 
   logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P1_w;
   logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P2_w;
   logic [NUM_CLKS-1:0]                                     dfi1_dram_clk_disable_P3_w;
   logic                                                    dfi1_lp_ctrl_req_w;
   logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi1_lp_ctrl_wakeup_w;
   logic                                                    dfi1_lp_data_req_w;
   logic [DFI_LP_WAKEUP_WIDTH-1:0]                          dfi1_lp_data_wakeup_w;
   logic                                                    dfi1_ctrlupd_req_w;
   logic [1:0]                                              dfi1_ctrlupd_type_w;
   logic                                                    dfi1_phyupd_ack_w;
   logic                                                    dfi1_phymstr_ack_w;

//dfi command path signal swaping
   assign dfi1_address_P0_w                = dfi1_address_P0;
   assign dfi1_address_P1_w                = dfi1_address_P1;
   assign dfi1_address_P2_w                = dfi1_address_P2;
   assign dfi1_address_P3_w                = dfi1_address_P3;
   assign dfi1_cke_P0_w                    = dfi1_cke_P0; 
   assign dfi1_cke_P1_w                    = dfi1_cke_P1;
   assign dfi1_cke_P2_w                    = dfi1_cke_P2;
   assign dfi1_cke_P3_w                    = dfi1_cke_P3;
   assign dfi1_cs_P0_w                     = dfi1_cs_P0;
   assign dfi1_cs_P1_w                     = dfi1_cs_P1;
   assign dfi1_cs_P2_w                     = dfi1_cs_P2;
   assign dfi1_cs_P3_w                     = dfi1_cs_P3;

   assign dfi1_init_start_w                = dfi1_init_start;
   assign dfi1_frequency_w                 = dfi1_frequency;
   assign dfi1_freq_ratio_w                = dfi1_freq_ratio;
   assign dfi1_freq_fsp_w                  = dfi1_freq_fsp;

   assign dfi1_wck_cs_P0_w                 = dfi1_wck_cs_P0; 
   assign dfi1_wck_cs_P1_w                 = dfi1_wck_cs_P1;
   assign dfi1_wck_cs_P2_w                 = dfi1_wck_cs_P2;
   assign dfi1_wck_cs_P3_w                 = dfi1_wck_cs_P3;
   assign dfi1_wck_en_P0_w                 = dfi1_wck_en_P0;
   assign dfi1_wck_en_P1_w                 = dfi1_wck_en_P1;
   assign dfi1_wck_en_P2_w                 = dfi1_wck_en_P2;
   assign dfi1_wck_en_P3_w                 = dfi1_wck_en_P3;
   assign dfi1_wck_toggle_P0_w             = dfi1_wck_toggle_P0; 
   assign dfi1_wck_toggle_P1_w             = dfi1_wck_toggle_P1;
   assign dfi1_wck_toggle_P2_w             = dfi1_wck_toggle_P2;
   assign dfi1_wck_toggle_P3_w             = dfi1_wck_toggle_P3;
   assign dwc_ddrphy1_snoop_running_w      = dwc_ddrphy1_snoop_running;

   assign dfi1_dram_clk_disable_P0_w       = dfi1_dram_clk_disable_P0; 
   assign dfi1_dram_clk_disable_P1_w       = dfi1_dram_clk_disable_P1;
   assign dfi1_dram_clk_disable_P2_w       = dfi1_dram_clk_disable_P2;
   assign dfi1_dram_clk_disable_P3_w       = dfi1_dram_clk_disable_P3;
   assign dfi1_lp_ctrl_req_w               = dfi1_lp_ctrl_req;
   assign dfi1_lp_ctrl_wakeup_w            = dfi1_lp_ctrl_wakeup;
   assign dfi1_lp_data_req_w               = dfi1_lp_data_req;
   assign dfi1_lp_data_wakeup_w            = dfi1_lp_data_wakeup;
   assign dfi1_ctrlupd_req_w               = dfi1_ctrlupd_req;
   assign dfi1_ctrlupd_type_w              = dfi1_ctrlupd_type;
   assign dfi1_phyupd_ack_w                = dfi1_phyupd_ack;
   assign dfi1_phymstr_ack_w               = dfi1_phymstr_ack;


   assign dfi0_address_P0_w                = dfi0_address_P0;
   assign dfi0_address_P1_w                = dfi0_address_P1;
   assign dfi0_address_P2_w                = dfi0_address_P2;
   assign dfi0_address_P3_w                = dfi0_address_P3;
   assign dfi0_cke_P0_w                    = dfi0_cke_P0;
   assign dfi0_cke_P1_w                    = dfi0_cke_P1;
   assign dfi0_cke_P2_w                    = dfi0_cke_P2;
   assign dfi0_cke_P3_w                    = dfi0_cke_P3;
   assign dfi0_cs_P0_w                     = dfi0_cs_P0;
   assign dfi0_cs_P1_w                     = dfi0_cs_P1;
   assign dfi0_cs_P2_w                     = dfi0_cs_P2;
   assign dfi0_cs_P3_w                     = dfi0_cs_P3;

   assign dfi_reset_n_w                    = dfi_reset_n;
   assign dfi0_init_start_w                = dfi0_init_start;
   assign dfi0_frequency_w                 = dfi0_frequency;
   assign dfi0_freq_ratio_w                = dfi0_freq_ratio;
   assign dfi0_freq_fsp_w                  = dfi0_freq_fsp;

   assign dfi0_wck_cs_P0_w                 = dfi0_wck_cs_P0;
   assign dfi0_wck_cs_P1_w                 = dfi0_wck_cs_P1;
   assign dfi0_wck_cs_P2_w                 = dfi0_wck_cs_P2;
   assign dfi0_wck_cs_P3_w                 = dfi0_wck_cs_P3;
   assign dfi0_wck_en_P0_w                 = dfi0_wck_en_P0;
   assign dfi0_wck_en_P1_w                 = dfi0_wck_en_P1;
   assign dfi0_wck_en_P2_w                 = dfi0_wck_en_P2;
   assign dfi0_wck_en_P3_w                 = dfi0_wck_en_P3;
   assign dfi0_wck_toggle_P0_w             = dfi0_wck_toggle_P0;
   assign dfi0_wck_toggle_P1_w             = dfi0_wck_toggle_P1;
   assign dfi0_wck_toggle_P2_w             = dfi0_wck_toggle_P2;
   assign dfi0_wck_toggle_P3_w             = dfi0_wck_toggle_P3;
   assign dwc_ddrphy0_snoop_running_w      = dwc_ddrphy0_snoop_running;

   assign dfi0_dram_clk_disable_P0_w       = dfi0_dram_clk_disable_P0;
   assign dfi0_dram_clk_disable_P1_w       = dfi0_dram_clk_disable_P1;
   assign dfi0_dram_clk_disable_P2_w       = dfi0_dram_clk_disable_P2;
   assign dfi0_dram_clk_disable_P3_w       = dfi0_dram_clk_disable_P3;
   assign dfi0_lp_ctrl_req_w               = dfi0_lp_ctrl_req;
   assign dfi0_lp_ctrl_wakeup_w            = dfi0_lp_ctrl_wakeup;
   assign dfi0_lp_data_req_w               = dfi0_lp_data_req;
   assign dfi0_lp_data_wakeup_w            = dfi0_lp_data_wakeup;
   assign dfi0_ctrlupd_req_w               = dfi0_ctrlupd_req;
   assign dfi0_ctrlupd_type_w              = dfi0_ctrlupd_type;
   assign dfi0_phyupd_ack_w                = dfi0_phyupd_ack;
   assign dfi0_phymstr_ack_w               = dfi0_phymstr_ack;



//dfi command path signal flipflop
logic lpddr_share_enable;
   assign lpddr_share_enable =  ( dfi0_freq_fsp_out      !=  dfi0_freq_fsp_w      )
                               |( dfi0_wck_cs_P0_out     !=  dfi0_wck_cs_P0_w     )
                               |( dfi0_wck_cs_P1_out     !=  dfi0_wck_cs_P1_w     )
                               |( dfi0_wck_cs_P2_out     !=  dfi0_wck_cs_P2_w     )
                               |( dfi0_wck_cs_P3_out     !=  dfi0_wck_cs_P3_w     )
                               |( dfi0_wck_en_P0_out     !=  dfi0_wck_en_P0_w     )
                               |( dfi0_wck_en_P1_out     !=  dfi0_wck_en_P1_w     )
                               |( dfi0_wck_en_P2_out     !=  dfi0_wck_en_P2_w     )
                               |( dfi0_wck_en_P3_out     !=  dfi0_wck_en_P3_w     )
                               |( dfi0_wck_toggle_P0_out !=  dfi0_wck_toggle_P0_w )
                               |( dfi0_wck_toggle_P1_out !=  dfi0_wck_toggle_P1_w )
                               |( dfi0_wck_toggle_P2_out !=  dfi0_wck_toggle_P2_w )
                               |( dfi0_wck_toggle_P3_out !=  dfi0_wck_toggle_P3_w );


logic or_lpddr_share_enable;
   assign or_lpddr_share_enable =   (dfi0_cke_P0_out    !=  dfi0_cke_P0_w)
                                   |(dfi0_cke_P1_out    !=  dfi0_cke_P1_w)
                                   |(dfi0_cke_P2_out    !=  dfi0_cke_P2_w)
                                   |(dfi0_cke_P3_out    !=  dfi0_cke_P3_w) ;
logic nodef_share_enable;
assign nodef_share_enable = (dfi0_freq_ratio_out   !=  dfi0_freq_ratio_w )
                          | (dfi0_cs_P0_out        !=  dfi0_cs_P0_w )
                          | (dfi0_cs_P1_out        !=  dfi0_cs_P1_w )
                          | (dfi0_cs_P2_out        !=  dfi0_cs_P2_w )
                          | (dfi0_cs_P3_out        !=  dfi0_cs_P3_w )
                          | (dfi0_ctrlupd_req_out  !=  dfi0_ctrlupd_req_w )
                          | (dfi0_phyupd_ack_out   !=  dfi0_phyupd_ack_w )
                          | (dfi0_phymstr_ack_out  !=  dfi0_phymstr_ack_w )
                          | (dfi0_lp_ctrl_req_out  !=  dfi0_lp_ctrl_req_w )
                          | (dfi0_lp_data_req_out  !=  dfi0_lp_data_req_w )
                          | (dfi_reset_n_out       !=  dfi_reset_n_w )
                          | (dfi0_init_start_out   !=  dfi0_init_start_w ) ;

   always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         // -------- Init and Frequency Change
         dfi_reset_n_out                     <= {RESET_WIDTH{1'b0}}; 
         dfi0_init_start_out                 <= 1'b0;
         dfi0_freq_fsp_out                   <= 2'd0;
         dfi0_frequency_out                  <= 5'd0;
         dfi0_freq_ratio_out                 <= 2'd0;
         dfi1_init_start_out                 <= 1'b0;
         dfi1_freq_fsp_out                   <= 2'd0;
         dfi1_frequency_out                  <= 5'd0;
         dfi1_freq_ratio_out                 <= 2'd0;
         // -------- Command
         dfi0_address_P0_out                 <= '0;
         dfi0_address_P1_out                 <= '0;
         dfi0_address_P2_out                 <= '0;
         dfi0_address_P3_out                 <= '0;
         dfi0_cs_P0_out                      <= (`DDRCTL_DDR_EN == 1) ? '1 : '0;
         dfi0_cs_P1_out                      <= (`DDRCTL_DDR_EN == 1) ? '1 : '0;
         dfi0_cs_P2_out                      <= (`DDRCTL_DDR_EN == 1) ? '1 : '0;
         dfi0_cs_P3_out                      <= (`DDRCTL_DDR_EN == 1) ? '1 : '0;
         dfi0_cke_P0_out                     <= '0;
         dfi0_cke_P1_out                     <= '0;
         dfi0_cke_P2_out                     <= '0;
         dfi0_cke_P3_out                     <= '0;
         dfi1_address_P0_out                 <= '0;
         dfi1_address_P1_out                 <= '0;
         dfi1_address_P2_out                 <= '0;
         dfi1_address_P3_out                 <= '0;
         dfi1_cs_P0_out                      <= (`DDRCTL_DDR_EN == 1) ? '1 : '0;
         dfi1_cs_P1_out                      <= (`DDRCTL_DDR_EN == 1) ? '1 : '0;
         dfi1_cs_P2_out                      <= (`DDRCTL_DDR_EN == 1) ? '1 : '0;
         dfi1_cs_P3_out                      <= (`DDRCTL_DDR_EN == 1) ? '1 : '0;
         dfi1_cke_P0_out                     <= '0;
         dfi1_cke_P1_out                     <= '0;
         dfi1_cke_P2_out                     <= '0;
         dfi1_cke_P3_out                     <= '0;
         // -------- Control Update
         dfi0_ctrlupd_req_out                <= 1'b0;
         dfi1_ctrlupd_req_out                <= 1'b0;
         dfi0_ctrlupd_type_out               <= 2'b00;
         dfi1_ctrlupd_type_out               <= 2'b00;
         // -------- PHY Update
         dfi0_phyupd_ack_out                 <= 1'b0;
         dfi1_phyupd_ack_out                 <= 1'b0;
         // -------- PHY master
         dfi0_phymstr_ack_out                <= 1'b0;
         dfi1_phymstr_ack_out                <= 1'b0;
         // -------- Low power
         dfi0_lp_ctrl_req_out                <= 1'b0;
         dfi0_lp_ctrl_wakeup_out             <= '0;
         dfi0_lp_data_req_out                <= 1'b0;
         dfi0_lp_data_wakeup_out             <= '0;
         dfi1_lp_ctrl_req_out                <= 1'b0;
         dfi1_lp_ctrl_wakeup_out             <= '0;
         dfi1_lp_data_req_out                <= 1'b0;
         dfi1_lp_data_wakeup_out             <= '0;
         // -------- DRAM clock disable
         dfi0_dram_clk_disable_P0_out        <= '0;
         dfi0_dram_clk_disable_P1_out        <= '0;
         dfi0_dram_clk_disable_P2_out        <= '0;
         dfi0_dram_clk_disable_P3_out        <= '0;
         dfi1_dram_clk_disable_P0_out        <= '0;
         dfi1_dram_clk_disable_P1_out        <= '0;
         dfi1_dram_clk_disable_P2_out        <= '0;
         dfi1_dram_clk_disable_P3_out        <= '0;
         // -------- WCK Control
         dfi0_wck_cs_P0_out                  <= '0;
         dfi0_wck_cs_P1_out                  <= '0;
         dfi0_wck_cs_P2_out                  <= '0;
         dfi0_wck_cs_P3_out                  <= '0;
         dfi0_wck_en_P0_out                  <= '0;
         dfi0_wck_en_P1_out                  <= '0;
         dfi0_wck_en_P2_out                  <= '0;
         dfi0_wck_en_P3_out                  <= '0;
         dfi0_wck_toggle_P0_out              <= '0;
         dfi0_wck_toggle_P1_out              <= '0;
         dfi0_wck_toggle_P2_out              <= '0;
         dfi0_wck_toggle_P3_out              <= '0;
         dwc_ddrphy0_snoop_running_out       <= '0;
         dfi1_wck_cs_P0_out                  <= '0;
         dfi1_wck_cs_P1_out                  <= '0;
         dfi1_wck_cs_P2_out                  <= '0;
         dfi1_wck_cs_P3_out                  <= '0;
         dfi1_wck_en_P0_out                  <= '0;
         dfi1_wck_en_P1_out                  <= '0;
         dfi1_wck_en_P2_out                  <= '0;
         dfi1_wck_en_P3_out                  <= '0;
         dfi1_wck_toggle_P0_out              <= '0;
         dfi1_wck_toggle_P1_out              <= '0;
         dfi1_wck_toggle_P2_out              <= '0;
         dfi1_wck_toggle_P3_out              <= '0;
         dwc_ddrphy1_snoop_running_out       <= '0;
      end else begin
         // -------- Init and Frequency Change
         if (nodef_share_enable) begin 
            dfi_reset_n_out                     <= dfi_reset_n_w;
            dfi0_init_start_out                 <= dfi0_init_start_w;
         end
         if (lpddr_share_enable) begin
            dfi0_freq_fsp_out                <= dfi0_freq_fsp_w;
         end
         if (|(dfi0_frequency_out ^ dfi0_frequency_w)) begin
            dfi0_frequency_out               <= dfi0_frequency_w;
         end
         if (nodef_share_enable) begin
            dfi0_freq_ratio_out              <= dfi0_freq_ratio_w;
         end
         dfi1_init_start_out                 <= dfi1_init_start_w;
         dfi1_freq_fsp_out                   <= dfi1_freq_fsp_w;
         dfi1_frequency_out                  <= dfi1_frequency_w;
         dfi1_freq_ratio_out                 <= dfi1_freq_ratio_w;

         // -------- Command
         if (|(dfi0_address_P0_out ^ dfi0_address_P0_w)) begin
            dfi0_address_P0_out                 <= dfi0_address_P0_w;
         end
         if (|(dfi0_address_P1_out ^ dfi0_address_P1_w)) begin
            dfi0_address_P1_out                 <= dfi0_address_P1_w;
         end
         if (|(dfi0_address_P2_out ^ dfi0_address_P2_w)) begin
            dfi0_address_P2_out                 <= dfi0_address_P2_w;
         end
         if (|(dfi0_address_P3_out ^ dfi0_address_P3_w)) begin
            dfi0_address_P3_out                 <= dfi0_address_P3_w;
         end
         if (nodef_share_enable) begin
            dfi0_cs_P0_out                      <= dfi0_cs_P0_w;
            dfi0_cs_P1_out                      <= dfi0_cs_P1_w;
            dfi0_cs_P2_out                      <= dfi0_cs_P2_w;
            dfi0_cs_P3_out                      <= dfi0_cs_P3_w;
         end
         if (or_lpddr_share_enable) begin
            dfi0_cke_P0_out                     <= dfi0_cke_P0_w;
            dfi0_cke_P1_out                     <= dfi0_cke_P1_w;
            dfi0_cke_P2_out                     <= dfi0_cke_P2_w;
            dfi0_cke_P3_out                     <= dfi0_cke_P3_w;
         end
         if (|(dfi1_address_P0_out ^ dfi1_address_P0_w)) begin
            dfi1_address_P0_out                 <= dfi1_address_P0_w;
         end
         if (|(dfi1_address_P1_out ^ dfi1_address_P1_w)) begin
            dfi1_address_P1_out                 <= dfi1_address_P1_w;
         end
         if (|(dfi1_address_P2_out ^ dfi1_address_P2_w)) begin
            dfi1_address_P2_out                 <= dfi1_address_P2_w;
         end
         if (|(dfi1_address_P3_out ^ dfi1_address_P3_w)) begin
            dfi1_address_P3_out                 <= dfi1_address_P3_w;
         end
         dfi1_cs_P0_out                      <= dfi1_cs_P0_w;
         dfi1_cs_P1_out                      <= dfi1_cs_P1_w;
         dfi1_cs_P2_out                      <= dfi1_cs_P2_w;
         dfi1_cs_P3_out                      <= dfi1_cs_P3_w;
         dfi1_cke_P0_out                     <= dfi1_cke_P0_w;
         dfi1_cke_P1_out                     <= dfi1_cke_P1_w;
         dfi1_cke_P2_out                     <= dfi1_cke_P2_w;
         dfi1_cke_P3_out                     <= dfi1_cke_P3_w;

         // -------- Control Update
         if (nodef_share_enable) begin
            dfi0_ctrlupd_req_out                <= dfi0_ctrlupd_req_w;
         end
         dfi1_ctrlupd_req_out                <= dfi1_ctrlupd_req_w;
         dfi0_ctrlupd_type_out               <= dfi0_ctrlupd_type_w;
         dfi1_ctrlupd_type_out               <= dfi1_ctrlupd_type_w;
         // -------- PHY Update
         if (nodef_share_enable) begin
            dfi0_phyupd_ack_out                 <= dfi0_phyupd_ack_w;
         end
         dfi1_phyupd_ack_out                 <= dfi1_phyupd_ack_w;
         // -------- PHY master
         if (nodef_share_enable) begin
            dfi0_phymstr_ack_out                <= dfi0_phymstr_ack_w;
         end
         dfi1_phymstr_ack_out                <= dfi1_phymstr_ack_w;
         // -------- Low power
         if (nodef_share_enable) begin
            dfi0_lp_ctrl_req_out                <= dfi0_lp_ctrl_req_w;
         end
         if (|(dfi0_lp_ctrl_wakeup_out ^ dfi0_lp_ctrl_wakeup_w)) begin
            dfi0_lp_ctrl_wakeup_out             <= dfi0_lp_ctrl_wakeup_w;
         end
         if (nodef_share_enable) begin
            dfi0_lp_data_req_out                <= dfi0_lp_data_req_w;
         end
         if (|(dfi0_lp_data_wakeup_out ^ dfi0_lp_data_wakeup_w)) begin
            dfi0_lp_data_wakeup_out             <= dfi0_lp_data_wakeup_w;
         end
         dfi1_lp_ctrl_req_out                <= dfi1_lp_ctrl_req_w;
         dfi1_lp_ctrl_wakeup_out             <= dfi1_lp_ctrl_wakeup_w;
         dfi1_lp_data_req_out                <= dfi1_lp_data_req_w;
         dfi1_lp_data_wakeup_out             <= dfi1_lp_data_wakeup_w;
         // -------- DRAM clock disable
         dfi0_dram_clk_disable_P0_out        <= dfi0_dram_clk_disable_P0_w;
         dfi0_dram_clk_disable_P1_out        <= dfi0_dram_clk_disable_P1_w;
         dfi0_dram_clk_disable_P2_out        <= dfi0_dram_clk_disable_P2_w;
         dfi0_dram_clk_disable_P3_out        <= dfi0_dram_clk_disable_P3_w;
         dfi1_dram_clk_disable_P0_out        <= dfi1_dram_clk_disable_P0_w;
         dfi1_dram_clk_disable_P1_out        <= dfi1_dram_clk_disable_P1_w;
         dfi1_dram_clk_disable_P2_out        <= dfi1_dram_clk_disable_P2_w;
         dfi1_dram_clk_disable_P3_out        <= dfi1_dram_clk_disable_P3_w;
         // -------- WCK Control
         if (lpddr_share_enable) begin
            dfi0_wck_cs_P0_out                  <= dfi0_wck_cs_P0_w;
            dfi0_wck_cs_P1_out                  <= dfi0_wck_cs_P1_w;
            dfi0_wck_cs_P2_out                  <= dfi0_wck_cs_P2_w;
            dfi0_wck_cs_P3_out                  <= dfi0_wck_cs_P3_w;
            dfi0_wck_en_P0_out                  <= dfi0_wck_en_P0_w;
            dfi0_wck_en_P1_out                  <= dfi0_wck_en_P1_w;
            dfi0_wck_en_P2_out                  <= dfi0_wck_en_P2_w;
            dfi0_wck_en_P3_out                  <= dfi0_wck_en_P3_w;
            dfi0_wck_toggle_P0_out              <= dfi0_wck_toggle_P0_w;
            dfi0_wck_toggle_P1_out              <= dfi0_wck_toggle_P1_w;
            dfi0_wck_toggle_P2_out              <= dfi0_wck_toggle_P2_w;
            dfi0_wck_toggle_P3_out              <= dfi0_wck_toggle_P3_w;
         end
         dwc_ddrphy0_snoop_running_out       <= dwc_ddrphy0_snoop_running_w;
         dfi1_wck_cs_P0_out                  <= dfi1_wck_cs_P0_w;
         dfi1_wck_cs_P1_out                  <= dfi1_wck_cs_P1_w;
         dfi1_wck_cs_P2_out                  <= dfi1_wck_cs_P2_w;
         dfi1_wck_cs_P3_out                  <= dfi1_wck_cs_P3_w;
         dfi1_wck_en_P0_out                  <= dfi1_wck_en_P0_w;
         dfi1_wck_en_P1_out                  <= dfi1_wck_en_P1_w;
         dfi1_wck_en_P2_out                  <= dfi1_wck_en_P2_w;
         dfi1_wck_en_P3_out                  <= dfi1_wck_en_P3_w;
         dfi1_wck_toggle_P0_out              <= dfi1_wck_toggle_P0_w;
         dfi1_wck_toggle_P1_out              <= dfi1_wck_toggle_P1_w;
         dfi1_wck_toggle_P2_out              <= dfi1_wck_toggle_P2_w;
         dfi1_wck_toggle_P3_out              <= dfi1_wck_toggle_P3_w;
         dwc_ddrphy1_snoop_running_out       <= dwc_ddrphy1_snoop_running_w;
      end
   end


//dfi command path signal OCCAP protection

endmodule : dfi_ic_cp_ff
