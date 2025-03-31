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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_tb_hif_mux.sv#6 $
// -------------------------------------------------------------------------
// Description:
//
`define __dwc_ddrctl_tb_hif_mux__sv__

/** 
 * ------------------------------------------------------------------------------------
 * this module is used to mux hif signals between arb_top and ddrc/ddrc_dch1 in umctl2
 * for verification purpose
 * ------------------------------------------------------------------------------------
 */


`include "DWC_ddrctl_all_defs.svh"
module dwc_ddrctl_tb_hif_mux #(
     parameter OCECC_EN                          =               `UMCTL2_OCECC_EN                                ,
     parameter A_DW                              =               `UMCTL2_A_DW                                    ,
     parameter A_STRBW                           =               `UMCTL2_A_DW/8                                  ,
     parameter A_PARW                            =               (OCECC_EN == 1) ? 5*A_STRBW : A_STRBW           ,
     parameter XPI_RQOS_RW                       =               `UMCTL2_XPI_RQOS_RW                             ,
     parameter UMCTL2_WDATARAM_PAR_DW            =               `UMCTL2_WDATARAM_PAR_DW                         ,
     parameter HIF_ADDR_WIDTH                    =               `MEMC_HIF_ADDR_WIDTH                            ,
     parameter HIF_CREDIT_BITS                   =               `MEMC_HIF_CREDIT_BITS                           ,
     parameter HIF_RQOS_TW                       =               `UMCTL2_XPI_RQOS_TW                             ,
     parameter MEMC_TAGBITS                      =               `MEMC_TAGBITS                                   ,
     parameter UMCTL2_CMD_LEN_BITS               =               `UMCTL2_CMD_LEN_BITS                            ,
     parameter MEMC_WDATA_PTR_BITS               =               `MEMC_WDATA_PTR_BITS                            ,
     parameter WRDATA_CYCLES                     =               `MEMC_WRDATA_CYCLES                             ,
     parameter MEMC_HIF_ADDR_WIDTH_MAX           =               `MEMC_HIF_ADDR_WIDTH_MAX                        ,
     parameter HIF_KEYID_WIDTH                   =               `DDRCTL_HIF_KEYID_WIDTH

)
(
     input                                                       hif_hif_wdata_valid                             ,
     input                                                       hif_hif_wdata_end                               ,
     input [A_DW-1:0]                                            hif_hif_wdata                                   ,
     input [A_STRBW-1:0]                                         hif_hif_wdata_mask                              ,
     input [A_PARW-1:0]                                          hif_hif_wdata_parity                            ,
     input                                                       pa_hif_go2critical_lpr                          ,
     input                                                       pa_hif_go2critical_hpr                          ,
     input                                                       pa_hif_go2critical_wr                           ,
     input                                                       pa_hif_go2critical_l1_lpr                       ,
     input                                                       pa_hif_go2critical_l1_hpr                       ,
     input                                                       pa_hif_go2critical_l1_wr                        ,
     input                                                       pa_hif_go2critical_l2_lpr                       ,
     input                                                       pa_hif_go2critical_l2_hpr                       ,
     input                                                       pa_hif_go2critical_l2_wr                        ,

     input                                                       hif_hif_cmd_valid                               ,
     input [1:0]                                                 hif_hif_cmd_type                                ,
         // ccx_tgl: ; hif_hif_cmd_addr[31]; ; If AXI address width is 33 and MEMC_DRAM_DATA_WIDTH is 32(4bytes), then only HIF address  [30:0] can be toggled.
     input [`MEMC_HIF_ADDR_WIDTH_MAX-1:0]                        hif_hif_cmd_addr                                ,
     input [XPI_RQOS_RW-1:0]                                     hif_hif_cmd_pri                                 ,
     input [HIF_RQOS_TW-1:0]                                     hif_hif_cmd_latency                             ,
     input [MEMC_TAGBITS-1:0]                                    hif_hif_cmd_token                               ,
     input [UMCTL2_CMD_LEN_BITS-1:0]                             hif_hif_cmd_length                              ,
     input [MEMC_WDATA_PTR_BITS-1:0]                             hif_hif_cmd_wdata_ptr                           ,


     input                                                       hif_hif_cmd_autopre                             ,
     input                                                       hif_hif_cmd_ecc_region                          ,
     input [WRDATA_CYCLES-1:0]                                   hif_hif_cmd_wdata_mask_full_ie                  ,


 //JIRA___ID
  //   input                                                       hif_hif_cmd_awlast                              ,
  //   input                                                       hif_hif_cmd_short_burst                         ,
  //  `ifdef UMCTL2_DUAL_CHANNEL
  //   input                                                       hif_hif_cmd_awlast_dch1                         ,
  //   input                                                       hif_hif_cmd_short_burst_dch1                    ,
  //  `endif // UMCTL2_DUAL_CHANNEL

     output                                                      mux_hif_go2critical_l1_lpr                     ,
     output                                                      mux_hif_go2critical_l1_hpr                     ,
     output                                                      mux_hif_go2critical_l1_wr                      ,
     output                                                      mux_hif_go2critical_l2_lpr                     ,
     output                                                      mux_hif_go2critical_l2_hpr                     ,
     output                                                      mux_hif_go2critical_l2_wr                      ,



     output                                                      mux_hif_cmd_valid                               ,
     output [1:0]                                                mux_hif_cmd_type                                ,
     output [`MEMC_HIF_ADDR_WIDTH_MAX-1:0]                       mux_hif_cmd_addr                                ,
     output [1:0]                                                mux_hif_cmd_pri                                 ,
     output [HIF_RQOS_TW-1:0]                                    mux_hif_cmd_latency                             ,
     output [MEMC_TAGBITS-1:0]                                   mux_hif_cmd_token                               ,
     output [UMCTL2_CMD_LEN_BITS-1:0]                            mux_hif_cmd_length                              ,
     output [MEMC_WDATA_PTR_BITS-1:0]                            mux_hif_cmd_wdata_ptr                           ,
     output                                                      mux_hif_cmd_autopre                             ,
     output                                                      mux_hif_cmd_ecc_region                          ,
     output [WRDATA_CYCLES-1:0]                                  mux_hif_cmd_wdata_mask_full_ie                  ,


     output                                                      mux_hif_wdata_valid                             ,
     output                                                      mux_hif_wdata_end                               ,
     output [`MEMC_DRAM_DATA_WIDTH*`MEMC_FREQ_RATIO*2-1:0]       mux_hif_wdata                                   , 
     output [(`MEMC_DRAM_DATA_WIDTH*`MEMC_FREQ_RATIO*2)/8-1:0]   mux_hif_wdata_mask                              , 
     output [UMCTL2_WDATARAM_PAR_DW-1:0]                         mux_hif_wdata_parity                            , 
     output                                                      mux_hif_go2critical_lpr                         ,
     output                                                      mux_hif_go2critical_hpr                         ,
     output                                                      mux_hif_go2critical_wr                          ,
     //output to arb_top

     output [HIF_CREDIT_BITS-1:0]                hif_lpr_credit          ,
     output                                      hif_cmd_stall           ,
     output                                      hif_wr_credit           ,
     output [HIF_CREDIT_BITS-1:0]                hif_hpr_credit          ,
     output [1:0]                                hif_wrecc_credit        ,

     output [MEMC_WDATA_PTR_BITS-1:0]            hif_wdata_ptr           ,
     output                                      hif_wdata_ptr_valid     ,
     output                                      hif_wdata_ptr_addr_err         ,
     output                                      hif_rdata_valid         ,
     output                                      hif_rdata_end           ,
     output [MEMC_TAGBITS-1:0]                   hif_rdata_token         ,
     output [A_DW-1:0]                           hif_rdata               ,
     output [A_STRBW-1:0]                        hif_rdata_parity        ,
     output                                      hif_rdata_uncorr_ecc_err,
     output                                      hif_rdata_uncorr_linkecc_err,
     output                                      hif_rdata_addr_err      ,
     output                                      hif_wdata_stall         ,

     //input from ddrc

     input [HIF_CREDIT_BITS-1:0]                ddrc_hif_lpr_credit          ,
     input                                      ddrc_hif_cmd_stall           ,
     input                                      ddrc_hif_wr_credit           ,
     input [HIF_CREDIT_BITS-1:0]                ddrc_hif_hpr_credit          ,
     input [1:0]                                ddrc_hif_wrecc_credit        ,

     input [MEMC_WDATA_PTR_BITS-1:0]            ddrc_hif_wdata_ptr           ,
     input                                      ddrc_hif_wdata_ptr_valid     ,
     input                                      ddrc_hif_wdata_ptr_addr_err  ,
     input                                      ddrc_hif_rdata_addr_err      ,
     input                                      ddrc_hif_rdata_valid         ,
     input                                      ddrc_hif_rdata_end           ,
     input [MEMC_TAGBITS-1:0]                   ddrc_hif_rdata_token         ,
     input [A_DW-1:0]                           ddrc_hif_rdata               ,
     input [A_STRBW-1:0]                        ddrc_hif_rdata_parity        ,
     input                                      ddrc_hif_rdata_uncorr_ecc_err,
     input                                      ddrc_hif_rdata_uncorr_linkecc_err,
     input                                      ddrc_hif_wdata_stall         
    );

    /** 
    *-------------------------
    *   tb_hif signals
    *-------------------------
    */
     logic                                                       tb_hif_en                                         ;

     logic                                                       tb_hif_cmd_valid                                  ;
     logic [1:0]                                                 tb_hif_cmd_type                                   ;
     logic [1:0]                                                 tb_hif_cmd_pri                                    ;
     logic                                                       tb_hif_cmd_ecc_region                             ;
     logic [WRDATA_CYCLES-1:0]                                   tb_hif_cmd_wdata_mask_full_ie                     ;


     logic [HIF_RQOS_TW-1:0]                                     tb_hif_cmd_latency                                ;
     logic [`MEMC_HIF_ADDR_WIDTH_MAX-1:0]                        tb_hif_cmd_addr                                   ;
     logic [UMCTL2_CMD_LEN_BITS-1:0]                             tb_hif_cmd_length                                 ;
     logic [MEMC_TAGBITS-1:0]                                    tb_hif_cmd_token                                  ;
     logic [MEMC_WDATA_PTR_BITS-1:0]                             tb_hif_cmd_wdata_ptr                              ;
     logic                                                       tb_hif_cmd_autopre                                ;



     logic                                                       tb_hif_wdata_valid                                ;
     logic [`MEMC_DRAM_DATA_WIDTH*`MEMC_FREQ_RATIO*2-1:0]        tb_hif_wdata                                      ;
     logic [(`MEMC_DRAM_DATA_WIDTH*`MEMC_FREQ_RATIO*2)/8-1:0]    tb_hif_wdata_mask                                 ;
     logic                                                       tb_hif_wdata_end                                  ;
     logic [UMCTL2_WDATARAM_PAR_DW-1:0]                          tb_hif_wdata_parity                               ;
     logic                                                       tb_hif_go2critical_wr                             ;
     logic                                                       tb_hif_go2critical_lpr                            ;
     logic                                                       tb_hif_go2critical_hpr                            ;
     logic                                                       tb_hif_go2critical_l1_wr                          ;
     logic                                                       tb_hif_go2critical_l1_lpr                         ;
     logic                                                       tb_hif_go2critical_l1_hpr                         ;
     logic                                                       tb_hif_go2critical_l2_wr                          ;
     logic                                                       tb_hif_go2critical_l2_lpr                         ;
     logic                                                       tb_hif_go2critical_l2_hpr                         ;



        /**
        *--------------------------------------------------------------
        *    pass through  if define SYNTHESIS
        *--------------------------------------------------------------
        */
        `ifdef SYNTHESIS
            assign tb_hif_en      = 0;
            
            //add to fix W123 spyglass violation
            always @(tb_hif_en) begin
                tb_hif_cmd_valid                                  = 1'b0                                                 ;
                tb_hif_cmd_type                                   = 2'b00                                                ;
                tb_hif_cmd_pri                                    = 2'b00                                                ;
                tb_hif_cmd_ecc_region                             = 1'b0                                                 ;
                tb_hif_cmd_wdata_mask_full_ie                     = {WRDATA_CYCLES{1'b0}}                                ;
           
           
                tb_hif_cmd_latency                                = {HIF_RQOS_TW{1'b0}}                                  ;
                tb_hif_cmd_addr                                   = {`MEMC_HIF_ADDR_WIDTH_MAX{1'b0}}                     ;
                tb_hif_cmd_length                                 = {UMCTL2_CMD_LEN_BITS{1'b0}}                          ;
                tb_hif_cmd_token                                  = {MEMC_TAGBITS{1'b0}}                                ;
                tb_hif_cmd_wdata_ptr                              = {MEMC_WDATA_PTR_BITS{1'b0}}                          ;
                tb_hif_cmd_autopre                                = 1'b0                                                 ;
           
                tb_hif_wdata_valid                                = 1'b0                                                 ;
                tb_hif_wdata                                      = {`MEMC_DRAM_DATA_WIDTH*`MEMC_FREQ_RATIO*2{1'b0}}     ;
                tb_hif_wdata_mask                                 = {(`MEMC_DRAM_DATA_WIDTH*`MEMC_FREQ_RATIO*2)/8{1'b0}};
                tb_hif_wdata_end                                  = 1'b0                                                 ;
                tb_hif_wdata_parity                               = {UMCTL2_WDATARAM_PAR_DW{1'b0}}                       ;
                tb_hif_go2critical_wr                             = 1'b0;
                tb_hif_go2critical_lpr                            = 1'b0;
                tb_hif_go2critical_hpr                            = 1'b0;
                tb_hif_go2critical_l1_wr                          = 1'b0;
                tb_hif_go2critical_l1_lpr                         = 1'b0;
                tb_hif_go2critical_l1_hpr                         = 1'b0;
                tb_hif_go2critical_l2_wr                          = 1'b0;
                tb_hif_go2critical_l2_lpr                         = 1'b0;
                tb_hif_go2critical_l2_hpr                         = 1'b0;
           
           end
        `else   
          /**
           *--------------------------------------------------------------
           *  pass through if not using Synopsys PVE simulation envirnoment
           *--------------------------------------------------------------
           */
       
          `ifndef DWC_DDRCTL_TB_HIF_MUX_EN
            assign tb_hif_en      = 0;
          `endif

        `endif //SYNTHESIS
      
                   
        //spyglass disable_block UndrivenInTerm-ML
        //SMD: undirven but loaded input terminal
        //SJ: these signals are driven from testbench. 
            assign mux_hif_cmd_valid                   = tb_hif_en      ? tb_hif_cmd_valid                   : hif_hif_cmd_valid                     ;
            assign mux_hif_cmd_type                    = tb_hif_en      ? tb_hif_cmd_type                    : hif_hif_cmd_type                      ;
            assign mux_hif_cmd_pri                     = tb_hif_en      ? tb_hif_cmd_pri                     : hif_hif_cmd_pri                       ;
            assign mux_hif_cmd_ecc_region              = tb_hif_en      ? tb_hif_cmd_ecc_region              : hif_hif_cmd_ecc_region                ;
            assign mux_hif_cmd_wdata_mask_full_ie      = tb_hif_en      ? tb_hif_cmd_wdata_mask_full_ie      : hif_hif_cmd_wdata_mask_full_ie        ;
            assign mux_hif_cmd_latency                 = tb_hif_en      ? tb_hif_cmd_latency                 : hif_hif_cmd_latency                   ;
            assign mux_hif_cmd_addr                    = tb_hif_en      ? tb_hif_cmd_addr                    : hif_hif_cmd_addr                      ;
            assign mux_hif_cmd_length                  = tb_hif_en      ? tb_hif_cmd_length                  : hif_hif_cmd_length                    ;
            assign mux_hif_cmd_token                   = tb_hif_en      ? tb_hif_cmd_token                   : hif_hif_cmd_token                     ;
            assign mux_hif_cmd_wdata_ptr               = tb_hif_en      ? tb_hif_cmd_wdata_ptr               : hif_hif_cmd_wdata_ptr                 ;
            assign mux_hif_cmd_autopre                 = tb_hif_en      ? tb_hif_cmd_autopre                 : hif_hif_cmd_autopre                   ;
            assign mux_hif_wdata_valid                 = tb_hif_en      ? tb_hif_wdata_valid                 : hif_hif_wdata_valid                   ;
            assign mux_hif_wdata                       = tb_hif_en      ? tb_hif_wdata                       : hif_hif_wdata                         ;
            assign mux_hif_wdata_mask                  = tb_hif_en      ? tb_hif_wdata_mask                  : hif_hif_wdata_mask                    ;
            assign mux_hif_wdata_end                   = tb_hif_en      ? tb_hif_wdata_end                   : hif_hif_wdata_end                     ;
            assign mux_hif_go2critical_wr              = tb_hif_en      ? tb_hif_go2critical_wr              : pa_hif_go2critical_wr                 ;
            assign mux_hif_go2critical_lpr             = tb_hif_en      ? tb_hif_go2critical_lpr             : pa_hif_go2critical_lpr                ;
            assign mux_hif_go2critical_hpr             = tb_hif_en      ? tb_hif_go2critical_hpr             : pa_hif_go2critical_hpr                ;
            assign mux_hif_go2critical_l1_wr           = tb_hif_en      ? tb_hif_go2critical_l1_wr           : pa_hif_go2critical_l1_wr              ;
            assign mux_hif_go2critical_l1_lpr          = tb_hif_en      ? tb_hif_go2critical_l1_lpr          : pa_hif_go2critical_l1_lpr             ;
            assign mux_hif_go2critical_l1_hpr          = tb_hif_en      ? tb_hif_go2critical_l1_hpr          : pa_hif_go2critical_l1_hpr             ;
            assign mux_hif_go2critical_l2_wr           = tb_hif_en      ? tb_hif_go2critical_l2_wr           : pa_hif_go2critical_l2_wr              ;
            assign mux_hif_go2critical_l2_lpr          = tb_hif_en      ? tb_hif_go2critical_l2_lpr          : pa_hif_go2critical_l2_lpr             ;
            assign mux_hif_go2critical_l2_hpr          = tb_hif_en      ? tb_hif_go2critical_l2_hpr          : pa_hif_go2critical_l2_hpr             ;
            assign mux_hif_wdata_parity                = tb_hif_en      ? tb_hif_wdata_parity                : hif_hif_wdata_parity                  ;


     //ddrc ---> tb_hif_mux ---> arb_top

         assign hif_lpr_credit          = tb_hif_en ? {`MEMC_HIF_CREDIT_BITS{1'b0}} : ddrc_hif_lpr_credit          ;
         assign hif_cmd_stall           = tb_hif_en ? 1'b0                          : ddrc_hif_cmd_stall           ;
         assign hif_wr_credit           = tb_hif_en ? 1'b0                          : ddrc_hif_wr_credit           ;
         assign hif_hpr_credit          = tb_hif_en ? {`MEMC_HIF_CREDIT_BITS{1'b0}} : ddrc_hif_hpr_credit          ;
         assign hif_wrecc_credit        = tb_hif_en ? 2'b00                         : ddrc_hif_wrecc_credit        ;
         assign hif_wdata_ptr           = tb_hif_en ? {`MEMC_WDATA_PTR_BITS{1'b0}}  : ddrc_hif_wdata_ptr           ;
         assign hif_wdata_ptr_valid     = tb_hif_en ? 1'b0                          : ddrc_hif_wdata_ptr_valid     ;

         assign hif_wdata_ptr_addr_err  = tb_hif_en ? 1'b0                          : ddrc_hif_wdata_ptr_addr_err  ; 
         assign hif_rdata_addr_err      = tb_hif_en ? 1'b0                          : ddrc_hif_rdata_addr_err      ;

         assign hif_rdata_valid         = tb_hif_en ? 1'b0                          : ddrc_hif_rdata_valid         ;
         assign hif_rdata_end           = tb_hif_en ? 1'b0                          : ddrc_hif_rdata_end           ;
         assign hif_rdata_token         = tb_hif_en ? {`MEMC_TAGBITS{1'b0}}         : ddrc_hif_rdata_token         ;
         assign hif_rdata               = tb_hif_en ? {`UMCTL2_A_DW{1'b0}}          : ddrc_hif_rdata               ;
         assign hif_rdata_parity        = tb_hif_en ? {`UMCTL2_A_DW/8{1'b0}}        : ddrc_hif_rdata_parity        ;

         assign hif_rdata_uncorr_ecc_err= tb_hif_en ? 1'b0                          : ddrc_hif_rdata_uncorr_ecc_err;

         assign hif_rdata_uncorr_linkecc_err = tb_hif_en ? 1'b0                     : ddrc_hif_rdata_uncorr_linkecc_err;
         assign hif_wdata_stall         = tb_hif_en ? 1'b0                          : ddrc_hif_wdata_stall         ;

        //spyglass enable_block UndrivenInTerm-ML

    endmodule  // dwc_ddrctl_tb_hif_mux

