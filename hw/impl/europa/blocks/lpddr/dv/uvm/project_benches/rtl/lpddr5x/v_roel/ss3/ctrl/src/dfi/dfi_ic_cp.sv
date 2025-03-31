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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/dfi/dfi_ic_cp.sv#9 $
// -------------------------------------------------------------------------
// Description:
//            DFI interconnect - command path
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module dfi_ic_cp
import DWC_ddrctl_reg_pkg::*;
#(
    parameter     NUM_RANKS                     = `MEMC_NUM_RANKS
   ,parameter     DFI0_CS_WIDTH                 = `DDRCTL_DFI0_CS_WIDTH
   ,parameter     DFI1_CS_WIDTH                 = `DDRCTL_DFI1_CS_WIDTH
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
   // DDRC0 interface
    dwc_ddrctl_ddrc_cpedfi_if.dfi_ic_mp                        cp_dfiif_dch0

   ,input   logic [FREQ_RATIO*NUM_RANKS-1:0]                   dfi_wck_cs_dch0
   ,input   logic [FREQ_RATIO-1:0]                             dfi_wck_en_dch0
   ,input   logic [2*FREQ_RATIO-1:0]                           dfi_wck_toggle_dch0


// clk/rstn should be defined only when they are used. See P80001562-506106
   ,input   logic                                              core_ddrc_core_clk
   ,input   logic                                              core_ddrc_rstn


   // DFI interface
   ,output  logic [RESET_WIDTH-1:0]                            dfi_reset_n_out

   ,output  logic                                              dfi0_init_start_out
   ,output  logic [1:0]                                        dfi0_freq_fsp_out
   ,output  logic [4:0]                                        dfi0_frequency_out
   ,output  logic [1:0]                                        dfi0_freq_ratio_out
   ,input   logic                                              dfi0_init_complete_in
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
   ,output  logic [NUM_CLKS-1:0]                               dfi0_dram_clk_disable_P0_out
   ,output  logic [NUM_CLKS-1:0]                               dfi0_dram_clk_disable_P1_out
   ,output  logic [NUM_CLKS-1:0]                               dfi0_dram_clk_disable_P2_out
   ,output  logic [NUM_CLKS-1:0]                               dfi0_dram_clk_disable_P3_out
   ,output  logic                                              dfi0_lp_ctrl_req_out
   ,output  logic [DFI_LP_WAKEUP_WIDTH-1:0]                    dfi0_lp_ctrl_wakeup_out
   ,input   logic                                              dfi0_lp_ctrl_ack_in
   ,output  logic                                              dfi0_lp_data_req_out
   ,output  logic [DFI_LP_WAKEUP_WIDTH-1:0]                    dfi0_lp_data_wakeup_out
   ,input   logic                                              dfi0_lp_data_ack_in
   ,output  logic                                              dfi0_ctrlupd_req_out
   ,output  logic [1:0]                                        dfi0_ctrlupd_type_out
   ,input   logic                                              dfi0_ctrlupd_ack_in
   ,input   logic                                              dfi0_phyupd_req_in
   ,input   logic [1:0]                                        dfi0_phyupd_type_in
   ,output  logic                                              dfi0_phyupd_ack_out
   ,input   logic                                              dfi0_phymstr_req_in
   ,input   logic [NUM_RANKS-1:0]                              dfi0_phymstr_cs_state_in
   ,input   logic                                              dfi0_phymstr_state_sel_in
   ,input   logic [1:0]                                        dfi0_phymstr_type_in
   ,output  logic                                              dfi0_phymstr_ack_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_wck_cs_P0_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_wck_cs_P1_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_wck_cs_P2_out
   ,output  logic [DFI0_CS_WIDTH-1:0]                          dfi0_wck_cs_P3_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                      dfi0_wck_en_P0_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                      dfi0_wck_en_P1_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                      dfi0_wck_en_P2_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                      dfi0_wck_en_P3_out
   ,output  logic [1:0]                                        dfi0_wck_toggle_P0_out
   ,output  logic [1:0]                                        dfi0_wck_toggle_P1_out
   ,output  logic [1:0]                                        dfi0_wck_toggle_P2_out
   ,output  logic [1:0]                                        dfi0_wck_toggle_P3_out
   ,output  logic                                              dwc_ddrphy0_snoop_running_out
   ,output  logic                                              dfi1_init_start_out
   ,output  logic [1:0]                                        dfi1_freq_fsp_out
   ,output  logic [4:0]                                        dfi1_frequency_out
   ,output  logic [1:0]                                        dfi1_freq_ratio_out
   ,input   logic                                              dfi1_init_complete_in
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
   ,output  logic [NUM_CLKS-1:0]                               dfi1_dram_clk_disable_P0_out
   ,output  logic [NUM_CLKS-1:0]                               dfi1_dram_clk_disable_P1_out
   ,output  logic [NUM_CLKS-1:0]                               dfi1_dram_clk_disable_P2_out
   ,output  logic [NUM_CLKS-1:0]                               dfi1_dram_clk_disable_P3_out
   ,output  logic                                              dfi1_lp_ctrl_req_out
   ,output  logic [DFI_LP_WAKEUP_WIDTH-1:0]                    dfi1_lp_ctrl_wakeup_out
   ,input   logic                                              dfi1_lp_ctrl_ack_in
   ,output  logic                                              dfi1_lp_data_req_out
   ,output  logic [DFI_LP_WAKEUP_WIDTH-1:0]                    dfi1_lp_data_wakeup_out
   ,input   logic                                              dfi1_lp_data_ack_in
   ,output  logic                                              dfi1_ctrlupd_req_out
   ,output  logic [1:0]                                        dfi1_ctrlupd_type_out
   ,input   logic                                              dfi1_ctrlupd_ack_in
   ,input   logic                                              dfi1_phyupd_req_in
   ,input   logic [1:0]                                        dfi1_phyupd_type_in
   ,output  logic                                              dfi1_phyupd_ack_out
   ,input   logic                                              dfi1_phymstr_req_in
   ,input   logic [NUM_RANKS-1:0]                              dfi1_phymstr_cs_state_in
   ,input   logic                                              dfi1_phymstr_state_sel_in
   ,input   logic [1:0]                                        dfi1_phymstr_type_in
   ,output  logic                                              dfi1_phymstr_ack_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_wck_cs_P0_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_wck_cs_P1_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_wck_cs_P2_out
   ,output  logic [DFI1_CS_WIDTH-1:0]                          dfi1_wck_cs_P3_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                      dfi1_wck_en_P0_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                      dfi1_wck_en_P1_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                      dfi1_wck_en_P2_out
   ,output  logic [DFI_DATA_WIDTH/16-1:0]                      dfi1_wck_en_P3_out
   ,output  logic [1:0]                                        dfi1_wck_toggle_P0_out
   ,output  logic [1:0]                                        dfi1_wck_toggle_P1_out
   ,output  logic [1:0]                                        dfi1_wck_toggle_P2_out
   ,output  logic [1:0]                                        dfi1_wck_toggle_P3_out
   ,output  logic                                              dwc_ddrphy1_snoop_running_out



   ,input  logic [2:0]                                         dbg_dfi_ie_cmd_type_w
   ,output logic [2:0]                                         dbg_dfi_ie_cmd_type


);


   //----------------------------------------------------------------------------
   // Signal Declaration
   //----------------------------------------------------------------------------

   logic                                              dfi0_init_start_w;
   logic [1:0]                                        dfi0_freq_fsp_w;
   logic [4:0]                                        dfi0_frequency_w;
   logic [1:0]                                        dfi0_freq_ratio_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P0-1:0]                dfi0_address_P0_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P1-1:0]                dfi0_address_P1_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P2-1:0]                dfi0_address_P2_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P3-1:0]                dfi0_address_P3_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_cke_P0_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_cke_P1_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_cke_P2_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_cke_P3_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_cs_P0_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_cs_P1_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_cs_P2_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_cs_P3_w;
   logic [NUM_CLKS-1:0]                               dfi0_dram_clk_disable_P0_w;
   logic [NUM_CLKS-1:0]                               dfi0_dram_clk_disable_P1_w;
   logic [NUM_CLKS-1:0]                               dfi0_dram_clk_disable_P2_w;
   logic [NUM_CLKS-1:0]                               dfi0_dram_clk_disable_P3_w;
   logic                                              dfi0_lp_ctrl_req_w;
   logic [DFI_LP_WAKEUP_WIDTH-1:0]                    dfi0_lp_ctrl_wakeup_w;
   logic                                              dfi0_lp_data_req_w;
   logic [DFI_LP_WAKEUP_WIDTH-1:0]                    dfi0_lp_data_wakeup_w;
   logic                                              dfi0_ctrlupd_req_w;
   logic [1:0]                                        dfi0_ctrlupd_type_w;
   logic                                              dfi0_phyupd_ack_w;
   logic                                              dfi0_phymstr_ack_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_wck_cs_P0_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_wck_cs_P1_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_wck_cs_P2_w;
   logic [DFI0_CS_WIDTH-1:0]                          dfi0_wck_cs_P3_w;
   logic [DFI_DATA_WIDTH/16-1:0]                      dfi0_wck_en_P0_w;
   logic [DFI_DATA_WIDTH/16-1:0]                      dfi0_wck_en_P1_w;
   logic [DFI_DATA_WIDTH/16-1:0]                      dfi0_wck_en_P2_w;
   logic [DFI_DATA_WIDTH/16-1:0]                      dfi0_wck_en_P3_w;
   logic [1:0]                                        dfi0_wck_toggle_P0_w;
   logic [1:0]                                        dfi0_wck_toggle_P1_w;
   logic [1:0]                                        dfi0_wck_toggle_P2_w;
   logic [1:0]                                        dfi0_wck_toggle_P3_w;
   logic                                              dwc_ddrphy0_snoop_running_w;
   logic                                              dfi1_init_start_w;
   logic [1:0]                                        dfi1_freq_fsp_w;
   logic [4:0]                                        dfi1_frequency_w;
   logic [1:0]                                        dfi1_freq_ratio_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P0-1:0]                dfi1_address_P0_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P1-1:0]                dfi1_address_P1_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P2-1:0]                dfi1_address_P2_w;
   logic [`MEMC_DFI_ADDR_WIDTH_P3-1:0]                dfi1_address_P3_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_cke_P0_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_cke_P1_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_cke_P2_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_cke_P3_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_cs_P0_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_cs_P1_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_cs_P2_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_cs_P3_w;
   logic [NUM_CLKS-1:0]                               dfi1_dram_clk_disable_P0_w;
   logic [NUM_CLKS-1:0]                               dfi1_dram_clk_disable_P1_w;
   logic [NUM_CLKS-1:0]                               dfi1_dram_clk_disable_P2_w;
   logic [NUM_CLKS-1:0]                               dfi1_dram_clk_disable_P3_w;
   logic                                              dfi1_lp_ctrl_req_w;
   logic [DFI_LP_WAKEUP_WIDTH-1:0]                    dfi1_lp_ctrl_wakeup_w;
   logic                                              dfi1_lp_data_req_w;
   logic [DFI_LP_WAKEUP_WIDTH-1:0]                    dfi1_lp_data_wakeup_w;
   logic                                              dfi1_ctrlupd_req_w;
   logic [1:0]                                        dfi1_ctrlupd_type_w;
   logic                                              dfi1_phyupd_ack_w;
   logic                                              dfi1_phymstr_ack_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_wck_cs_P0_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_wck_cs_P1_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_wck_cs_P2_w;
   logic [DFI1_CS_WIDTH-1:0]                          dfi1_wck_cs_P3_w;
   logic [DFI_DATA_WIDTH/16-1:0]                      dfi1_wck_en_P0_w;
   logic [DFI_DATA_WIDTH/16-1:0]                      dfi1_wck_en_P1_w;
   logic [DFI_DATA_WIDTH/16-1:0]                      dfi1_wck_en_P2_w;
   logic [DFI_DATA_WIDTH/16-1:0]                      dfi1_wck_en_P3_w;
   logic [1:0]                                        dfi1_wck_toggle_P0_w;
   logic [1:0]                                        dfi1_wck_toggle_P1_w;
   logic [1:0]                                        dfi1_wck_toggle_P2_w;
   logic [1:0]                                        dfi1_wck_toggle_P3_w;
   logic                                              dwc_ddrphy1_snoop_running_w;




   //----------------------------------------------------------------------------
   // Circuit Description
   //----------------------------------------------------------------------------
   //----------------------------
   // DFI reset
   //----------------------------
   assign dfi_reset_n_w                      = cp_dfiif_dch0.dfi_reset_n
                                             ;

   //----------------------------
   // Init and Frequency Change
   //----------------------------
   // DFI output has to be synchronized between DFI0 and DFI1 (PHY's requirement)
   assign dfi0_init_start_w                  = 
                                                cp_dfiif_dch0.dfi_init_start;
   assign dfi0_freq_fsp_w                    = cp_dfiif_dch0.dfi_freq_fsp;
   assign dfi0_frequency_w                   = 
                                                cp_dfiif_dch0.dfi_frequency;
   assign dfi0_freq_ratio_w                  = cp_dfiif_dch0.dfi_freq_ratio;
   assign dfi1_init_start_w                  =
                                                cp_dfiif_dch0.dfi_init_start;
   assign dfi1_frequency_w                   =
                                                cp_dfiif_dch0.dfi_frequency;
   assign dfi1_freq_ratio_w                  =
                                                cp_dfiif_dch0.dfi_freq_ratio;
   assign dfi1_freq_fsp_w                    =
                                                cp_dfiif_dch0.dfi_freq_fsp
                                             ;

   assign cp_dfiif_dch0.dfi_init_complete    = 
                                                dfi0_init_complete_in;


//----------------------------
// DFI Error Signals Begin
//----------------------------



//----------------------------
// DFI Error Signals End
//----------------------------


   //----------------------------
   // Command
   //----------------------------
   // Address
   assign dfi0_address_P0_w                  = 
                                                cp_dfiif_dch0.dfi_address.p0;
   assign dfi0_address_P1_w                  =
                                                cp_dfiif_dch0.dfi_address.p1
                                             ;
   assign dfi0_address_P2_w                  = 
                                                cp_dfiif_dch0.dfi_address.p2;
   assign dfi0_address_P3_w                  = 
                                                cp_dfiif_dch0.dfi_address.p3;
   assign dfi1_address_P0_w                  = 
                                               cp_dfiif_dch0.dfi_address.p0;
   assign dfi1_address_P1_w                  =
                                               cp_dfiif_dch0.dfi_address.p1;
   assign dfi1_address_P2_w                  = 
                                               cp_dfiif_dch0.dfi_address.p2;
   assign dfi1_address_P3_w                  = 
                                               cp_dfiif_dch0.dfi_address.p3;

   // CS
   assign  dfi0_cs_P0_w                      =
                                                cp_dfiif_dch0.dfi_cs[0*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi0_cs_P1_w                       =
                                                cp_dfiif_dch0.dfi_cs[1*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi0_cs_P2_w                       =
                                                cp_dfiif_dch0.dfi_cs[2*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi0_cs_P3_w                       =
                                                cp_dfiif_dch0.dfi_cs[3*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi1_cs_P0_w                       =
                                                cp_dfiif_dch0.dfi_cs[0*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi1_cs_P1_w                       =
                                                cp_dfiif_dch0.dfi_cs[1*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi1_cs_P2_w                       =
                                                cp_dfiif_dch0.dfi_cs[2*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi1_cs_P3_w                       =
                                                cp_dfiif_dch0.dfi_cs[3*NUM_RANKS +: NUM_RANKS]
                                             ;

   // CKE
   assign dfi0_cke_P0_w                      =
                                                cp_dfiif_dch0.dfi_cke[0*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi0_cke_P1_w                      =
                                                cp_dfiif_dch0.dfi_cke[1*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi0_cke_P2_w                      = {
                                                cp_dfiif_dch0.dfi_cke[2*NUM_RANKS +: NUM_RANKS]
                                             };
   assign dfi0_cke_P3_w                      = {
                                                cp_dfiif_dch0.dfi_cke[3*NUM_RANKS +: NUM_RANKS]
                                             };
   // CKE on DFI1 exists in LPDDR controller
   assign dfi1_cke_P0_w                      =
                                                cp_dfiif_dch0.dfi_cke[0*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi1_cke_P1_w                      =
                                                cp_dfiif_dch0.dfi_cke[1*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi1_cke_P2_w                      =
                                                cp_dfiif_dch0.dfi_cke[2*NUM_RANKS +: NUM_RANKS]
                                             ;
   assign dfi1_cke_P3_w                      =
                                                cp_dfiif_dch0.dfi_cke[3*NUM_RANKS +: NUM_RANKS]
                                             ;

   //----------------------------
   // Control Update
   //----------------------------
   // DFI output can be independent between DFI0 and DFI1
   // Not supported in Shared-AC
   assign dfi0_ctrlupd_req_w                 = 
                                               (cp_dfiif_dch0.dfi_ctrlupd_req & cp_dfiif_dch0.dfi_ctrlupd_target[0]);
   assign dfi1_ctrlupd_req_w                 =
                                               cp_dfiif_dch0.dfi_ctrlupd_req & cp_dfiif_dch0.dfi_ctrlupd_target[1]
                                             ;

   assign dfi0_ctrlupd_type_w                = cp_dfiif_dch0.dfi_ctrlupd_type;
   assign dfi1_ctrlupd_type_w                =
                                               cp_dfiif_dch0.dfi_ctrlupd_type
                                             ;

   assign cp_dfiif_dch0.dfi_ctrlupd_ack      = 
                                               (dfi0_ctrlupd_ack_in
                                             | dfi1_ctrlupd_ack_in
                                             );

   //----------------------------
   // PHY Update
   //----------------------------
   // DFI output can be independent between DFI0 and DFI1
   assign cp_dfiif_dch0.dfi_phyupd_req       = dfi0_phyupd_req_in;
   assign cp_dfiif_dch0.dfi_phyupd_type      = dfi0_phyupd_type_in;

   assign dfi0_phyupd_ack_w                  =
                                               cp_dfiif_dch0.dfi_phyupd_ack;
   assign dfi1_phyupd_ack_w                  =
                                               cp_dfiif_dch0.dfi_phyupd_ack
                                             ;

   //----------------------------
   // PHY master
   //----------------------------
   // DFI output has to be synchronized between DFI0 and DFI1 (PHY's requirement)
   // Not supported in Shared-AC
   assign cp_dfiif_dch0.dfi_phymstr_req         = dfi0_phymstr_req_in;
   assign cp_dfiif_dch0.dfi_phymstr_cs_state    = dfi0_phymstr_cs_state_in;
   assign cp_dfiif_dch0.dfi_phymstr_state_sel   = dfi0_phymstr_state_sel_in;
   assign cp_dfiif_dch0.dfi_phymstr_type        = dfi0_phymstr_type_in;

   assign dfi0_phymstr_ack_w                    = cp_dfiif_dch0.dfi_phymstr_ack;
   assign dfi1_phymstr_ack_w                    =
                                                   cp_dfiif_dch0.dfi_phymstr_ack;

   //----------------------------
   // CTRL message
   //----------------------------


   //----------------------------
   // Low power
   //----------------------------
   // DFI output can be independent between DFI0 and DFI1
   assign dfi0_lp_ctrl_req_w                 =
                                               cp_dfiif_dch0.dfi_lp_ctrl_req;
   assign dfi0_lp_ctrl_wakeup_w              = cp_dfiif_dch0.dfi_lp_ctrl_wakeup;
   assign dfi0_lp_data_req_w                 =
                                               cp_dfiif_dch0.dfi_lp_data_req;
   assign dfi0_lp_data_wakeup_w              = cp_dfiif_dch0.dfi_lp_data_wakeup;

   assign dfi1_lp_ctrl_req_w                 =
                                               cp_dfiif_dch0.dfi_lp_ctrl_req
                                             ;
   assign dfi1_lp_ctrl_wakeup_w              =
                                               cp_dfiif_dch0.dfi_lp_ctrl_wakeup
                                             ;
   assign dfi1_lp_data_req_w                 =
                                               cp_dfiif_dch0.dfi_lp_data_req
                                             ;
   assign dfi1_lp_data_wakeup_w              =
                                               cp_dfiif_dch0.dfi_lp_data_wakeup
                                             ;

   assign cp_dfiif_dch0.dfi_lp_ctrl_ack      = dfi0_lp_ctrl_ack_in;
   assign cp_dfiif_dch0.dfi_lp_data_ack      = dfi0_lp_data_ack_in;

   //----------------------------
   // DRAM clock disable
   //----------------------------
   assign dfi0_dram_clk_disable_P0_w         =
                                               cp_dfiif_dch0.dfi_dram_clk_disable;
   assign dfi0_dram_clk_disable_P1_w         = dfi0_dram_clk_disable_P0_w;
   assign dfi0_dram_clk_disable_P2_w         = dfi0_dram_clk_disable_P0_w;
   assign dfi0_dram_clk_disable_P3_w         = dfi0_dram_clk_disable_P0_w;

   assign dfi1_dram_clk_disable_P0_w         =
                                               cp_dfiif_dch0.dfi_dram_clk_disable
                                             ;
   assign dfi1_dram_clk_disable_P1_w         = dfi1_dram_clk_disable_P0_w;
   assign dfi1_dram_clk_disable_P2_w         = dfi1_dram_clk_disable_P0_w;
   assign dfi1_dram_clk_disable_P3_w         = dfi1_dram_clk_disable_P0_w;

   //----------------------------
   // WCK Control
   //----------------------------
   assign dfi0_wck_cs_P0_w                   = dfi_wck_cs_dch0[0*NUM_RANKS +: NUM_RANKS];
   assign dfi0_wck_cs_P1_w                   = dfi_wck_cs_dch0[1*NUM_RANKS +: NUM_RANKS];
   assign dfi0_wck_en_P0_w                   = {(DFI_DATA_WIDTH/16){dfi_wck_en_dch0[0]}};
   assign dfi0_wck_en_P1_w                   = {(DFI_DATA_WIDTH/16){dfi_wck_en_dch0[1]}};
   assign dfi0_wck_toggle_P0_w               = dfi_wck_toggle_dch0[1:0];
   assign dfi0_wck_toggle_P1_w               = dfi_wck_toggle_dch0[3:2];
   assign dfi0_wck_cs_P2_w                   = dfi_wck_cs_dch0[2*NUM_RANKS +: NUM_RANKS];
   assign dfi0_wck_cs_P3_w                   = dfi_wck_cs_dch0[3*NUM_RANKS +: NUM_RANKS];
   assign dfi0_wck_en_P2_w                   = {(DFI_DATA_WIDTH/16){dfi_wck_en_dch0[2]}};
   assign dfi0_wck_en_P3_w                   = {(DFI_DATA_WIDTH/16){dfi_wck_en_dch0[3]}};
   assign dfi0_wck_toggle_P2_w               = dfi_wck_toggle_dch0[5:4];
   assign dfi0_wck_toggle_P3_w               = dfi_wck_toggle_dch0[7:6];

            always_comb begin
               begin
                  dfi1_wck_cs_P0_w                   = dfi_wck_cs_dch0[0*NUM_RANKS+:NUM_RANKS];
                  dfi1_wck_cs_P1_w                   = dfi_wck_cs_dch0[1*NUM_RANKS+:NUM_RANKS];
                  dfi1_wck_en_P0_w                   = {(DFI_DATA_WIDTH/16){dfi_wck_en_dch0[0]}};
                  dfi1_wck_en_P1_w                   = {(DFI_DATA_WIDTH/16){dfi_wck_en_dch0[1]}};
                  dfi1_wck_toggle_P0_w               = dfi_wck_toggle_dch0[1:0];
                  dfi1_wck_toggle_P1_w               = dfi_wck_toggle_dch0[3:2];
                  dfi1_wck_cs_P2_w                   = dfi_wck_cs_dch0[2*NUM_RANKS+:NUM_RANKS];
                  dfi1_wck_cs_P3_w                   = dfi_wck_cs_dch0[3*NUM_RANKS+:NUM_RANKS];
                  dfi1_wck_en_P2_w                   = {(DFI_DATA_WIDTH/16){dfi_wck_en_dch0[2]}};
                  dfi1_wck_en_P3_w                   = {(DFI_DATA_WIDTH/16){dfi_wck_en_dch0[3]}};
                  dfi1_wck_toggle_P2_w               = dfi_wck_toggle_dch0[5:4];
                  dfi1_wck_toggle_P3_w               = dfi_wck_toggle_dch0[7:6];
               end
            end

   // currently not considering dual data channgel. DDRC dch0 drives both dfi0 and dfi1.
      always_comb begin
         dwc_ddrphy0_snoop_running_w = cp_dfiif_dch0.dfi_snoop_running;
               begin
                  dwc_ddrphy1_snoop_running_w = cp_dfiif_dch0.dfi_snoop_running;
               end
      end







   //----------------------------
   // DFI output signals
   //----------------------------



//There is a selector added in dfi_ic.sv for HBW mode,so move FF to dfi_ic.sv 
//These selector and FF in dfi_ic have been move to new module dfi_ic_cp_ff.sv for dfi_ic module is too large.
   // -------- Init and Frequency Change
   assign dfi_reset_n_out                    = dfi_reset_n_w;
   assign dfi0_init_start_out                = dfi0_init_start_w;
   assign dfi0_freq_fsp_out                  = dfi0_freq_fsp_w;
   assign dfi0_frequency_out                 = dfi0_frequency_w;
   assign dfi0_freq_ratio_out                = dfi0_freq_ratio_w;
   assign dfi1_init_start_out                = dfi1_init_start_w;
   assign dfi1_freq_fsp_out                  = dfi1_freq_fsp_w;
   assign dfi1_frequency_out                 = dfi1_frequency_w;
   assign dfi1_freq_ratio_out                = dfi1_freq_ratio_w;
   // -------- Command
   assign dfi0_address_P0_out                = dfi0_address_P0_w;
   assign dfi0_address_P1_out                = dfi0_address_P1_w;
   assign dfi0_address_P2_out                = dfi0_address_P2_w;
   assign dfi0_address_P3_out                = dfi0_address_P3_w;
   assign dfi0_cs_P0_out                     = dfi0_cs_P0_w;
   assign dfi0_cs_P1_out                     = dfi0_cs_P1_w;
   assign dfi0_cs_P2_out                     = dfi0_cs_P2_w;
   assign dfi0_cs_P3_out                     = dfi0_cs_P3_w;
   assign dfi0_cke_P0_out                    = dfi0_cke_P0_w;
   assign dfi0_cke_P1_out                    = dfi0_cke_P1_w;
   assign dfi0_cke_P2_out                    = dfi0_cke_P2_w;
   assign dfi0_cke_P3_out                    = dfi0_cke_P3_w;
   assign dfi1_address_P0_out                = dfi1_address_P0_w;
   assign dfi1_address_P1_out                = dfi1_address_P1_w;
   assign dfi1_address_P2_out                = dfi1_address_P2_w;
   assign dfi1_address_P3_out                = dfi1_address_P3_w;
   assign dfi1_cs_P0_out                     = dfi1_cs_P0_w;
   assign dfi1_cs_P1_out                     = dfi1_cs_P1_w;
   assign dfi1_cs_P2_out                     = dfi1_cs_P2_w;
   assign dfi1_cs_P3_out                     = dfi1_cs_P3_w;
   assign dfi1_cke_P0_out                    = dfi1_cke_P0_w;
   assign dfi1_cke_P1_out                    = dfi1_cke_P1_w;
   assign dfi1_cke_P2_out                    = dfi1_cke_P2_w;
   assign dfi1_cke_P3_out                    = dfi1_cke_P3_w;
   // -------- Control Update
   assign dfi0_ctrlupd_req_out               = dfi0_ctrlupd_req_w;
   assign dfi1_ctrlupd_req_out               = dfi1_ctrlupd_req_w;
   assign dfi0_ctrlupd_type_out              = dfi0_ctrlupd_type_w;
   assign dfi1_ctrlupd_type_out              = dfi1_ctrlupd_type_w;
   // -------- PHY Update
   assign dfi0_phyupd_ack_out                = dfi0_phyupd_ack_w;
   assign dfi1_phyupd_ack_out                = dfi1_phyupd_ack_w;
   // -------- PHY master
   assign dfi0_phymstr_ack_out               = dfi0_phymstr_ack_w;
   assign dfi1_phymstr_ack_out               = dfi1_phymstr_ack_w;
   // -------- Low power
   assign dfi0_lp_ctrl_req_out               = dfi0_lp_ctrl_req_w;
   assign dfi0_lp_ctrl_wakeup_out            = dfi0_lp_ctrl_wakeup_w;
   assign dfi0_lp_data_req_out               = dfi0_lp_data_req_w;
   assign dfi0_lp_data_wakeup_out            = dfi0_lp_data_wakeup_w;
   assign dfi1_lp_ctrl_req_out               = dfi1_lp_ctrl_req_w;
   assign dfi1_lp_ctrl_wakeup_out            = dfi1_lp_ctrl_wakeup_w;
   assign dfi1_lp_data_req_out               = dfi1_lp_data_req_w;
   assign dfi1_lp_data_wakeup_out            = dfi1_lp_data_wakeup_w;
   // -------- DRAM clock disable
   assign dfi0_dram_clk_disable_P0_out       = dfi0_dram_clk_disable_P0_w;
   assign dfi0_dram_clk_disable_P1_out       = dfi0_dram_clk_disable_P1_w;
   assign dfi0_dram_clk_disable_P2_out       = dfi0_dram_clk_disable_P2_w;
   assign dfi0_dram_clk_disable_P3_out       = dfi0_dram_clk_disable_P3_w;
   assign dfi1_dram_clk_disable_P0_out       = dfi1_dram_clk_disable_P0_w;
   assign dfi1_dram_clk_disable_P1_out       = dfi1_dram_clk_disable_P1_w;
   assign dfi1_dram_clk_disable_P2_out       = dfi1_dram_clk_disable_P2_w;
   assign dfi1_dram_clk_disable_P3_out       = dfi1_dram_clk_disable_P3_w;
   // -------- WCK Control
   assign dfi0_wck_cs_P0_out                 = dfi0_wck_cs_P0_w;
   assign dfi0_wck_cs_P1_out                 = dfi0_wck_cs_P1_w;
   assign dfi0_wck_cs_P2_out                 = dfi0_wck_cs_P2_w;
   assign dfi0_wck_cs_P3_out                 = dfi0_wck_cs_P3_w;
   assign dfi0_wck_en_P0_out                 = dfi0_wck_en_P0_w;
   assign dfi0_wck_en_P1_out                 = dfi0_wck_en_P1_w;
   assign dfi0_wck_en_P2_out                 = dfi0_wck_en_P2_w;
   assign dfi0_wck_en_P3_out                 = dfi0_wck_en_P3_w;
   assign dfi0_wck_toggle_P0_out             = dfi0_wck_toggle_P0_w;
   assign dfi0_wck_toggle_P1_out             = dfi0_wck_toggle_P1_w;
   assign dfi0_wck_toggle_P2_out             = dfi0_wck_toggle_P2_w;
   assign dfi0_wck_toggle_P3_out             = dfi0_wck_toggle_P3_w;
   assign dwc_ddrphy0_snoop_running_out      = dwc_ddrphy0_snoop_running_w;
   assign dfi1_wck_cs_P0_out                 = dfi1_wck_cs_P0_w;
   assign dfi1_wck_cs_P1_out                 = dfi1_wck_cs_P1_w;
   assign dfi1_wck_cs_P2_out                 = dfi1_wck_cs_P2_w;
   assign dfi1_wck_cs_P3_out                 = dfi1_wck_cs_P3_w;
   assign dfi1_wck_en_P0_out                 = dfi1_wck_en_P0_w;
   assign dfi1_wck_en_P1_out                 = dfi1_wck_en_P1_w;
   assign dfi1_wck_en_P2_out                 = dfi1_wck_en_P2_w;
   assign dfi1_wck_en_P3_out                 = dfi1_wck_en_P3_w;
   assign dfi1_wck_toggle_P0_out             = dfi1_wck_toggle_P0_w;
   assign dfi1_wck_toggle_P1_out             = dfi1_wck_toggle_P1_w;
   assign dfi1_wck_toggle_P2_out             = dfi1_wck_toggle_P2_w;
   assign dfi1_wck_toggle_P3_out             = dfi1_wck_toggle_P3_w;
   assign dwc_ddrphy1_snoop_running_out      = dwc_ddrphy1_snoop_running_w;




   logic  [2:0] dbg_dfi_ie_cmd_type_r;
   always @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin 
      if (!core_ddrc_rstn) begin 
         dbg_dfi_ie_cmd_type_r      <= {$bits(dbg_dfi_ie_cmd_type_r){1'b0}};
      end else begin 
        if (|(dbg_dfi_ie_cmd_type_r ^ dbg_dfi_ie_cmd_type_w)) begin
           dbg_dfi_ie_cmd_type_r      <= dbg_dfi_ie_cmd_type_w;
        end
      end 
   end

      assign dbg_dfi_ie_cmd_type      = dbg_dfi_ie_cmd_type_r;



endmodule : dfi_ic_cp
