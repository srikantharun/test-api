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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_ddrc_cpedfi_if.svh#11 $
// -------------------------------------------------------------------------
// Description:
//    SV interface for CPE-DFI signals
//

`ifndef __GUARD__DWC_DDRCTL_DDRC_CPEDFI_IF__SVH__
`define __GUARD__DWC_DDRCTL_DDRC_CPEDFI_IF__SVH__

`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
`include "dfi/DWC_ddrctl_dfi_pkg.svh"

interface dwc_ddrctl_ddrc_cpedfi_if 
  import DWC_ddrctl_reg_pkg::*;
  import DWC_ddrctl_dfi_pkg::*;
  #(
      parameter NUM_RANKS                   = `MEMC_NUM_RANKS
     ,parameter FREQ_RATIO                  = `MEMC_FREQ_RATIO
     ,parameter BANK_BITS                   = `MEMC_BANK_BITS
     ,parameter BG_BITS                     = `MEMC_BG_BITS
     ,parameter CID_WIDTH                   = `UMCTL2_CID_WIDTH
     ,parameter ADDR_WIDTH                  = `MEMC_DFI_ADDR_WIDTH
     ,parameter RESET_WIDTH                 = `UMCTL2_RESET_WIDTH
     ,parameter NUM_LANES                   = 4
     ,parameter DATA_CS_BITS                = FREQ_RATIO*NUM_RANKS*NUM_LANES
     ,parameter PARITY_IN_WIDTH             = 2
     ,parameter NUM_DRAM_CLKS               = `MEMC_NUM_CLKS
     ,parameter HIF_ADDR_WIDTH              = `MEMC_HIF_ADDR_WIDTH
     ,parameter HIF_KEYID_WIDTH             = `DDRCTL_HIF_KEYID_WIDTH
  );

   dfi_address_s                          dfi_address;                        //
     // ccx_tgl: ; dfi_bank; ; The bits are not used for both LPDDR4 and LPDDR5.
   logic [FREQ_RATIO*BANK_BITS-1:0]       dfi_bank;                           //
   logic [1:0]                            dfi_freq_ratio;                     //
     // ccx_tgl: ; dfi_bg; ; The bits are not used for both LPDDR4 and LPDDR5.
   logic [FREQ_RATIO*BG_BITS-1:0]         dfi_bg;                             //
     // ccx_tgl: ; dfi_act_n; ; SystemVerilog Interface(redundant): LPDDR5/4/4X Controller doesn't require dfi_act_n
   logic [FREQ_RATIO-1:0]                 dfi_act_n;                          //
     // ccx_tgl: ; dfi_cid; ; SystemVerilog Interface(redundant): LPDDR5/4/4X Controller doesn't require dfi_cid
   logic [FREQ_RATIO*CID_WIDTH-1:0]       dfi_cid;                            //
     // ccx_tgl: ; dfi_cas_n; ; The bits are not used for both LPDDR4 and LPDDR5.
   logic [FREQ_RATIO-1:0]                 dfi_cas_n;                          //
     // ccx_tgl: ; dfi_ras_n; ; SystemVerilg Interface(redundant): LPDDR5/4/4X Controller doesn't require dfi_ras_n
   logic [FREQ_RATIO-1:0]                 dfi_ras_n;                          //
     // ccx_tgl: ; dfi_we_n; ; SystemVerilg Interface(redundant): LPDDR5/4/4X Controller doesn't require dfi_we_n
   logic [FREQ_RATIO-1:0]                 dfi_we_n;                           //
   logic [FREQ_RATIO*NUM_RANKS-1:0]       dfi_cke;                            //
       // ccx_tgl: ; dfi_cs[3:2]; ; The bits are assigned to dfi0_cs_P1[1:0] and is not toggled because P1/P3 is never toggled according to LPDDR4 command encoding..
       // ccx_tgl: ; dfi_cs[7:6]; ; The bits are assigned to dfi0_cs_P3[1:0] and is not toggled because P1/P3 is never toggled according to LPDDR4 command encoding..
   logic [FREQ_RATIO*NUM_RANKS-1:0]       dfi_cs;                             //
     // ccx_tgl: ; dfi_odt; ; SystemVerilog Interface(redundant): LPDDR5/4/4X Controller doesn't require dfi_odt
   logic [FREQ_RATIO*NUM_RANKS-1:0]       dfi_odt;                            //
   logic [RESET_WIDTH-1:0]                dfi_reset_n;                        //
     // ccx_tgl: ; dfi_parity_in; ; SystemVerilog Interface(redundant): LPDDR5/4/4X Controller doesn't require dfi_parity_in
   logic [FREQ_RATIO*PARITY_IN_WIDTH-1:0] dfi_parity_in;                      //
     // ccx_tgl: ; dfi_alert_n; ; SystemVerilog Interface(redundant): LPDDR5/4/4X Controller doesn't require dfi_alert_n
   logic [FREQ_RATIO-1:0]                 dfi_alert_n;                        //
   logic                                  dfi_init_complete;                  //
   logic                                  dfi_init_start;                     //
   logic [DFI_FREQ_FSP_WIDTH-1:0]         dfi_freq_fsp;                       // 
   logic [4:0]                            dfi_frequency;                      //
     // ccx_tgl: ; dfi_2n_mode; ; SystemVerilog Interface(redundant): LPDDR5/4/4X Controller doesn't require dfi_2n_mode
   logic                                  dfi_2n_mode;                        // dfi_2n_mode in PAS_CPE, dfi_geardown_en in DDRC_CPE
   logic                                  dfi_ctrlupd_req;                    //
    // ccx_tgl: ; dfi_ctrlupd_type[1]; ; ctrlupd_type2/ctrlup_type3 aren't used, so dfi_ctrlupd_type[1] can be excluded. P80001562-341728 
   logic [1:0]                            dfi_ctrlupd_type;                   //
   logic [1:0]                            dfi_ctrlupd_target;                 // select dfi0 and/or dfi1
   logic                                  dfi_ctrlupd_ack;                    //
   logic                                  dfi_phyupd_req;                     //
     // ccx_tgl: ; dfi_phyupd_type[1:0]; ; Both DDR5/4 and LPDDR5/4/4X SNPS PHY only employ tphyupd_type0 (2'b00)
   logic [1:0]                            dfi_phyupd_type;                    // exists in DDRC_CPE only
   logic                                  dfi_phyupd_ack;                     //
   logic                                  dfi_lp_ctrl_req;                    //
   logic [DFI_LP_WAKEUP_PD_WIDTH-1:0]     dfi_lp_ctrl_wakeup;                 //
   logic                                  dfi_lp_ctrl_ack;                    //
   logic                                  dfi_lp_data_req;                    //
   logic [DFI_LP_WAKEUP_PD_WIDTH-1:0]     dfi_lp_data_wakeup;                 //
   logic                                  dfi_lp_data_ack;                    //
   logic [NUM_DRAM_CLKS-1:0]              dfi_dram_clk_disable;               //
   logic                                  dfi_phymstr_req;                    // exists in DDRC_CPE only
     //ccx_tgl : ; dfi_phymstr_cs_state; ; When the dfi_phymstr_req signal is asserted, dfi_phymstr_cs_state will always be set to 0 as long as LPDDR5/4/4X PHY is used.
   logic [NUM_RANKS-1:0]                  dfi_phymstr_cs_state;               // exists in DDRC_CPE only
   logic                                  dfi_phymstr_state_sel;              // exists in DDRC_CPE only
   logic [1:0]                            dfi_phymstr_type;                   // exists in DDRC_CPE only
   logic                                  dfi_phymstr_ack;                    // exists in DDRC_CPE only
   logic [DATA_CS_BITS-1:0]               dfi_wrdata_cs;                      //
   logic [DATA_CS_BITS-1:0]               dfi_rddata_cs;                      //
   // ccx_tgl: u_DWC_ddrctl.cp_dfiif_dch0 ; dbg_dfi_ie_cmd_type ;  ; This signal is only interfaced inside U_ddrc, so it can not toggle on u_DWC_ddrctl.
   logic [2:0]                           dbg_dfi_ie_cmd_type;
   logic                                 dfi_snoop_running;

   modport ddrc_cpe_mp (
       output        dfi_address
      ,output        dfi_bank
      ,output        dfi_freq_ratio
      ,output        dfi_bg
      ,output        dfi_act_n
      ,output        dfi_2n_mode // dfi_geardown_en
      ,output        dfi_cid
      ,output        dfi_cas_n
      ,output        dfi_ras_n
      ,output        dfi_we_n
      ,output        dfi_cke
      ,output        dfi_cs
      ,output        dfi_odt
      ,output        dfi_reset_n
      ,output        dfi_parity_in
      ,output        dfi_init_start
      ,input         dfi_init_complete
      ,output        dfi_frequency
      ,output        dfi_ctrlupd_req
      ,output        dfi_ctrlupd_type
      ,output        dfi_ctrlupd_target
      ,input         dfi_ctrlupd_ack
      ,input         dfi_phyupd_req
      ,output        dfi_phyupd_ack
      ,input         dfi_phymstr_req
      ,input         dfi_phymstr_cs_state
      ,input         dfi_phymstr_state_sel
      ,input         dfi_phymstr_type
      ,output        dfi_phymstr_ack
      ,output        dfi_lp_ctrl_req // dfi_lp_req
      ,output        dfi_lp_ctrl_wakeup // dfi_lp_wakeup
      ,input         dfi_lp_ctrl_ack // dfi_lp_ack
      ,output        dfi_lp_data_req // dfi_lp_req
      ,output        dfi_lp_data_wakeup // dfi_lp_wakeup
      ,input         dfi_lp_data_ack // dfi_lp_ack
      ,output        dfi_dram_clk_disable
      ,output        dfi_wrdata_cs
      ,output        dfi_rddata_cs
      ,output        dbg_dfi_ie_cmd_type 
   );

   modport ddrc_dfi_mp (
       input         dfi_address
      ,input         dfi_bank
      ,input         dfi_freq_ratio
      ,input         dfi_bg
      ,input         dfi_act_n
      ,input         dfi_2n_mode // dfi_geardown_en
      ,input         dfi_cid
      ,input         dfi_cas_n
      ,input         dfi_ras_n
      ,input         dfi_we_n
      ,input         dfi_cke
      ,input         dfi_cs
      ,input         dfi_odt
      ,input         dfi_reset_n
      ,input         dfi_parity_in
      ,input         dfi_init_start
      ,output        dfi_init_complete
      ,input         dfi_frequency
      ,input         dfi_ctrlupd_req
      ,input         dfi_ctrlupd_type
      ,input         dfi_ctrlupd_target
      ,output        dfi_ctrlupd_ack
      ,output        dfi_phyupd_req
      ,input         dfi_phyupd_ack
      ,output        dfi_phymstr_req
      ,output        dfi_phymstr_cs_state
      ,output        dfi_phymstr_state_sel
      ,output        dfi_phymstr_type
      ,input         dfi_phymstr_ack
      ,input         dfi_lp_ctrl_req // dfi_lp_req
      ,input         dfi_lp_ctrl_wakeup // dfi_lp_wakeup
      ,output        dfi_lp_ctrl_ack // dfi_lp_ack
      ,input         dfi_lp_data_req // dfi_lp_req
      ,input         dfi_lp_data_wakeup // dfi_lp_wakeup
      ,output        dfi_lp_data_ack // dfi_lp_ack
      ,input         dfi_dram_clk_disable
      ,input         dfi_wrdata_cs
      ,input         dfi_rddata_cs
      ,input         dbg_dfi_ie_cmd_type 
   );


   modport cp_dfi_mp (
       output        dfi_address
      ,output        dfi_freq_ratio
      ,output        dfi_cke
      ,output        dfi_cs
      ,output        dfi_reset_n
      ,output        dfi_init_start
      ,input         dfi_init_complete
      ,output        dfi_frequency
      ,output        dfi_freq_fsp
      ,output        dfi_ctrlupd_req
      ,output        dfi_ctrlupd_type
      ,output        dfi_ctrlupd_target
      ,input         dfi_ctrlupd_ack
      ,input         dfi_phyupd_req
      ,output        dfi_phyupd_ack
      ,input         dfi_phymstr_req
      ,input         dfi_phymstr_cs_state
      ,input         dfi_phymstr_state_sel
      ,input         dfi_phymstr_type
      ,output        dfi_phymstr_ack
      ,output        dfi_lp_ctrl_req
      ,output        dfi_lp_ctrl_wakeup
      ,input         dfi_lp_ctrl_ack
      ,output        dfi_lp_data_req
      ,output        dfi_lp_data_wakeup
      ,input         dfi_lp_data_ack
      ,output        dfi_dram_clk_disable
      ,output        dfi_wrdata_cs
      ,output        dfi_rddata_cs
      ,output        dfi_snoop_running
   );

   modport dfi_ic_mp (
       input         dfi_address
      ,input         dfi_freq_ratio
      ,input         dfi_cke
      ,input         dfi_cs
      ,input         dfi_reset_n
      ,input         dfi_init_start
      ,output        dfi_init_complete
      ,input         dfi_freq_fsp
      ,input         dfi_frequency
      ,input         dfi_ctrlupd_req
      ,input         dfi_ctrlupd_type
      ,input         dfi_ctrlupd_target
      ,output        dfi_ctrlupd_ack
      ,output        dfi_phyupd_req
      ,output        dfi_phyupd_type
      ,input         dfi_phyupd_ack
      ,output        dfi_phymstr_req
      ,output        dfi_phymstr_cs_state
      ,output        dfi_phymstr_state_sel
      ,output        dfi_phymstr_type
      ,input         dfi_phymstr_ack
      ,input         dfi_lp_ctrl_req
      ,input         dfi_lp_ctrl_wakeup
      ,output        dfi_lp_ctrl_ack
      ,input         dfi_lp_data_req
      ,input         dfi_lp_data_wakeup
      ,output        dfi_lp_data_ack
      ,input         dfi_dram_clk_disable
      ,input         dfi_wrdata_cs
      ,input         dfi_rddata_cs
      ,input         dfi_snoop_running
   );

endinterface : dwc_ddrctl_ddrc_cpedfi_if

`endif // __GUARD__DWC_DDRCTL_DDRC_CPEDFI_IF__SVH__
