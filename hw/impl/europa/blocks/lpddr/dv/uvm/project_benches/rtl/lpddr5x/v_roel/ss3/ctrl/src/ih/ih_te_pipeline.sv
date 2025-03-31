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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_te_pipeline.sv#3 $
// -------------------------------------------------------------------------
// Description:
//     This is the top level of IH module.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module ih_te_pipeline #(
    //------------------------------ PARAMETERS ------------------------------------
     parameter IH_TAG_WIDTH      = `MEMC_TAGBITS                 // width of token/tag field from core
    ,parameter CMD_LEN_BITS      = 1                             // bits for command length, when used
    ,parameter RMW_TYPE_BITS     = 2                             // 2 bits for RMW type
    ,parameter WDATA_PTR_BITS    = `MEMC_WDATA_PTR_BITS 
    ,parameter RD_LATENCY_BITS   = `UMCTL2_XPI_RQOS_TW 
    ,parameter WR_LATENCY_BITS   = `UMCTL2_XPI_WQOS_TW 
    ,parameter BT_BITS           = 4  
    ,parameter BWT_BITS          = 4  
    ,parameter IE_RD_TYPE_BITS   = `IE_RD_TYPE_BITS
    ,parameter IE_WR_TYPE_BITS   = `IE_WR_TYPE_BITS
    ,parameter IE_BURST_NUM_BITS = 5
    ,parameter MWR_BITS = 1  // currently 1-bit info (OR of all data beats)
    ,parameter PARTIAL_WR_BITS = `UMCTL2_PARTIAL_WR_BITS 
    ,parameter PARTIAL_WR_BITS_LOG2 = 1 
    ,parameter PW_WORD_CNT_WD_MAX = 1 
    ,parameter HIF_KEYID_WIDTH    = `DDRCTL_HIF_KEYID_WIDTH
    )
    (
    //-------------------------- INPUTS AND OUTPUTS --------------------------------  
   input                         te_ih_retry
  ,input                         co_ih_clk                 // clock
  ,input                         core_ddrc_rstn            // reset
  //spyglass disable_block W240
  //SMD: Input declared but not read
  //SJ: Used only if VPR_EN/VPW_EN is set. Decided to keep current coding style
  ,input                         ddrc_cg_en                // DDRC clock gating enable
  //spyglass enable_block W240
  ,input                         wu_ih_flow_cntrl_req

   //control signal of pipeline
  ,output [WDATA_PTR_BITS-1:0]   rxcmd_wdata_ptr
  ,output                        ih_te_ppl_empty
  ,output                        ih_te_ppl_wr_empty
  ,output                        ih_te_ppl_rd_empty
  ,output                        te_ppl_ih_stall

  ,input                         reg_ddrc_ecc_type

   //data out of pipeline
  ,output                        ih_te_rd_valid
  ,output                        ih_te_wr_valid
  ,output                        ih_wu_wr_valid
  ,output                        ih_te_rd_valid_addr_err 
  ,output                        ih_te_wr_valid_addr_err
  ,output [CMD_LEN_BITS-1:0]     ih_te_rd_length 
  ,output [IH_TAG_WIDTH-1:0]     ih_te_rd_tag 
  ,output [RMW_TYPE_BITS-1:0]    ih_te_rmwtype 
  ,output [1:0]                  ih_te_hi_pri           // priority that is affected by the force_low_pri_n signal
  ,output [1:0]                  ih_te_hi_pri_int 

  ,output [RD_LATENCY_BITS-1:0]  ih_te_rd_latency 
  ,output                        ih_gs_any_vpr_timed_out 
  ,output [WR_LATENCY_BITS-1:0]  ih_te_wr_latency 
  ,output                        ih_gs_any_vpw_timed_out 

  ,output                        ih_te_autopre          // auto precharge enable flag
  ,output                        ih_te_eccap
  ,output [`UMCTL2_LRANK_BITS -1:0]  ih_te_rank_num
  ,output [`MEMC_BG_BITS-1:0]    ih_te_bankgroup_num
  ,output [`MEMC_BG_BANK_BITS -1:0]  ih_te_bg_bank_num
  ,output [`MEMC_BANK_BITS -1:0] ih_te_bank_num
  ,output [`MEMC_PAGE_BITS -1:0] ih_te_page_num
  ,output [`MEMC_BLK_BITS -1:0]  ih_te_block_num
  ,output [`MEMC_WORD_BITS-1:0]  ih_te_critical_dword      // for reads only, critical word within a block - not currently supported
  ,output [`MEMC_WORD_BITS-1:0]  ih_wu_critical_dword      // for reads only, critical word within a block - not currently supported
  ,output  [BT_BITS-1:0]         ih_te_ie_bt
  ,output  [BWT_BITS-1:0]        ih_te_ie_bwt
  ,output  [IE_RD_TYPE_BITS-1:0] ih_te_ie_rd_type
  ,output  [IE_WR_TYPE_BITS-1:0] ih_te_ie_wr_type
  ,output  [IE_BURST_NUM_BITS-1:0] ih_te_ie_blk_burst_num  //only for the Data command
  ,output  [`MEMC_BLK_BITS-1:0]  ih_te_ie_block_num
  ,output [MWR_BITS-1:0]         ih_te_mwr 
  ,output [PARTIAL_WR_BITS-1:0]  ih_te_wr_word_valid 
  ,output [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first 
  ,output [PW_WORD_CNT_WD_MAX-1:0] ih_te_wr_pw_num_beats_m1 
  ,output [PW_WORD_CNT_WD_MAX-1:0] ih_te_wr_pw_num_cols_m1 

   //data in of pipeline
  ,input  [WDATA_PTR_BITS-1:0]   ppl_rxcmd_wdata_ptr
  ,input                         ih_ppl_te_rd_valid
  ,input                         ih_ppl_te_wr_valid
  ,input                         ih_ppl_wu_wr_valid
  ,input                         ih_ppl_te_rd_valid_addr_err 
  ,input                         ih_ppl_te_wr_valid_addr_err
  ,input  [CMD_LEN_BITS-1:0]     ih_ppl_te_rd_length 
  ,input  [IH_TAG_WIDTH-1:0]     ih_ppl_te_rd_tag 
  ,input  [RMW_TYPE_BITS-1:0]    ih_ppl_te_rmwtype 
  ,input  [1:0]                  ih_ppl_te_hi_pri           // priority that is affected by the force_low_pri_n signal
  ,input  [1:0]                  ih_ppl_te_hi_pri_int 

  ,input  [RD_LATENCY_BITS-1:0]  ih_ppl_te_rd_latency 
  ,input                         ih_ppl_gs_any_vpr_timed_out
  ,input  [WR_LATENCY_BITS-1:0]  ih_ppl_te_wr_latency 
  ,input                         ih_ppl_gs_any_vpw_timed_out

  ,input                         ih_ppl_te_autopre          // auto precharge enable flag
  ,input                         ih_ppl_te_eccap
  ,input  [`UMCTL2_LRANK_BITS -1:0]  ih_ppl_te_rank_num
  ,input  [`MEMC_BG_BITS-1:0]    ih_ppl_te_bankgroup_num
  ,input  [`MEMC_BG_BANK_BITS -1:0]  ih_ppl_te_bg_bank_num
  ,input  [`MEMC_BANK_BITS -1:0] ih_ppl_te_bank_num
  ,input  [`MEMC_PAGE_BITS -1:0] ih_ppl_te_page_num
  ,input  [`MEMC_BLK_BITS -1:0]  ih_ppl_te_block_num
  ,input  [`MEMC_WORD_BITS-1:0]  ih_ppl_te_critical_dword      // for reads only, critical word within a block - not currently supported
  ,input  [`MEMC_WORD_BITS-1:0]  ih_ppl_wu_critical_dword      // for reads only, critical word within a block - not currently supported
  ,input   [BT_BITS-1:0]         ih_ppl_te_ie_bt
  ,input   [BWT_BITS-1:0]        ih_ppl_te_ie_bwt
  ,input   [IE_RD_TYPE_BITS-1:0] ih_ppl_te_ie_rd_type
  ,input   [IE_WR_TYPE_BITS-1:0] ih_ppl_te_ie_wr_type
  ,input   [IE_BURST_NUM_BITS-1:0] ih_ppl_te_ie_blk_burst_num  //only for the Data command
  ,input   [`MEMC_BLK_BITS-1:0]  ih_ppl_te_ie_block_num
  ,input  [MWR_BITS-1:0]         ih_ppl_te_mwr 
  ,input  [PARTIAL_WR_BITS-1:0]  ih_ppl_te_wr_word_valid 
  ,input  [PARTIAL_WR_BITS_LOG2-1:0] ih_ppl_te_wr_ram_raddr_lsb_first 
  ,input  [PW_WORD_CNT_WD_MAX-1:0] ih_ppl_te_wr_pw_num_beats_m1 
  ,input  [PW_WORD_CNT_WD_MAX-1:0] ih_ppl_te_wr_pw_num_cols_m1 
);

localparam FIFO_DATA_BITS = 
  WDATA_PTR_BITS  //,input  [WDATA_PTR_BITS-1:0]   ppl_rxcmd_wdata_ptr
  +1      //,input                         ih_ppl_te_rd_valid
  +1     //,input                         ih_ppl_te_wr_valid
  +1     //,input                         ih_ppl_wu_wr_valid
  +1     //,input                         ih_ppl_te_rd_valid_addr_err 
  +1     //,input                         ih_ppl_te_wr_valid_addr_err
  +CMD_LEN_BITS   //,input  [CMD_LEN_BITS-1:0]     ih_ppl_te_rd_length 
  +IH_TAG_WIDTH   //,input  [IH_TAG_WIDTH-1:0]     ih_ppl_te_rd_tag 
  +RMW_TYPE_BITS  //,input  [RMW_TYPE_BITS-1:0]    ih_ppl_te_rmwtype 
  +2              //,input  [1:0]                  ih_ppl_te_hi_pri           // priority that is affected by the force_low_pri_n signal
  +2              //,input  [1:0]                  ih_ppl_te_hi_pri_int 
  +1     //,input                         ih_ppl_te_autopre          // auto precharge enable flag
  +1     //,input                         ih_ppl_te_eccap
  +`UMCTL2_LRANK_BITS //,input  [`UMCTL2_LRANK_BITS -1:0]  ih_ppl_te_rank_num
  +`MEMC_BG_BITS  //,input  [`MEMC_BG_BITS-1:0]    ih_ppl_te_bankgroup_num
  +`MEMC_BG_BANK_BITS   //,input  [`MEMC_BG_BANK_BITS -1:0]  ih_ppl_te_bg_bank_num
  +`MEMC_BANK_BITS      //,input  [`MEMC_BANK_BITS -1:0] ih_ppl_te_bank_num
  +`MEMC_PAGE_BITS      //,input  [`MEMC_PAGE_BITS -1:0] ih_ppl_te_page_num
  +`MEMC_BLK_BITS       //,input  [`MEMC_BLK_BITS -1:0]  ih_ppl_te_block_num
  +`MEMC_WORD_BITS      //,input  [`MEMC_WORD_BITS-1:0]  ih_ppl_te_critical_dword      // for reads only, critical word within a block - not currently supported
  +`MEMC_WORD_BITS      //,input  [`MEMC_WORD_BITS-1:0]  ih_ppl_wu_critical_dword      // for reads only, critical word within a block - not currently supported
  +BT_BITS        //,input   [BT_BITS-1:0]         ih_ppl_te_ie_bt
  +BWT_BITS        //,input   [BWT_BITS-1:0]         ih_ppl_te_ie_bwt
  +IE_RD_TYPE_BITS   //,input   [IE_RD_TYPE_BITS-1:0] ih_ppl_te_ie_rd_type
  +IE_WR_TYPE_BITS   //,input   [IE_WR_TYPE_BITS-1:0] ih_ppl_te_ie_wr_type
  +IE_BURST_NUM_BITS //,input   [IE_BURST_NUM_BITS-1:0] ih_ppl_te_ie_blk_burst_num  //only for the Data command
  +`MEMC_BLK_BITS    //,input   [`MEMC_BLK_BITS-1:0]  ih_ppl_te_ie_block_num
  +MWR_BITS          //,input  [MWR_BITS-1:0]         ih_ppl_te_mwr 
  +PARTIAL_WR_BITS   //,input  [PARTIAL_WR_BITS-1:0]  ih_ppl_te_wr_word_valid 
  +PARTIAL_WR_BITS_LOG2 //,input  [PARTIAL_WR_BITS_LOG2-1:0] ih_ppl_te_wr_ram_raddr_lsb_first 
  +PW_WORD_CNT_WD_MAX   //,input  [PW_WORD_CNT_WD_MAX-1:0] ih_ppl_te_wr_pw_num_beats_m1 
  +PW_WORD_CNT_WD_MAX   //,input  [PW_WORD_CNT_WD_MAX-1:0] ih_ppl_te_wr_pw_num_cols_m1 
;
// 2-bit read priority encoding
localparam CMD_PRI_LPR       = `MEMC_CMD_PRI_LPR;
localparam CMD_PRI_VPR       = `MEMC_CMD_PRI_VPR;
localparam CMD_PRI_HPR       = `MEMC_CMD_PRI_HPR;
localparam CMD_PRI_XVPR      = `MEMC_CMD_PRI_XVPR;

// 2-bit write priority encoding
localparam CMD_PRI_NPW       = `MEMC_CMD_PRI_NPW;
localparam CMD_PRI_VPW       = `MEMC_CMD_PRI_VPW;
localparam CMD_PRI_RSVD      = `MEMC_CMD_PRI_RSVD;
localparam CMD_PRI_XVPW      = `MEMC_CMD_PRI_XVPW;

wire [FIFO_DATA_BITS-1:0] ih_te_fifo_in;
wire [FIFO_DATA_BITS-1:0] ih_te_fifo_out;
wire [FIFO_DATA_BITS-1:0] ih_te_fifo_out_ie;

wire  ih_te_rd_valid_orig;
wire  ih_te_wr_valid_orig;
wire  ih_wu_wr_valid_orig;

wire  ih_te_rd_valid_addr_err_orig;
wire  ih_te_wr_valid_addr_err_orig;

assign ih_te_fifo_in = {
   ppl_rxcmd_wdata_ptr
  ,ih_ppl_te_rd_valid
  ,ih_ppl_te_wr_valid
  ,ih_ppl_wu_wr_valid
  ,ih_ppl_te_rd_valid_addr_err 
  ,ih_ppl_te_wr_valid_addr_err
  ,ih_ppl_te_rd_length 
  ,ih_ppl_te_rd_tag 
  ,ih_ppl_te_rmwtype 
  ,ih_ppl_te_hi_pri           // priority that is affected by the force_low_pri_n signal
  ,ih_ppl_te_hi_pri_int 

  ,ih_ppl_te_autopre          // auto precharge enable flag
  ,ih_ppl_te_eccap
  ,ih_ppl_te_rank_num
  ,ih_ppl_te_bankgroup_num
  ,ih_ppl_te_bg_bank_num
  ,ih_ppl_te_bank_num
  ,ih_ppl_te_page_num
  ,ih_ppl_te_block_num
  ,ih_ppl_te_critical_dword      // for reads only, critical word within a block - not currently supported
  ,ih_ppl_wu_critical_dword      // for reads only, critical word within a block - not currently supported
  ,ih_ppl_te_ie_bt
  ,ih_ppl_te_ie_bwt
  ,ih_ppl_te_ie_rd_type
  ,ih_ppl_te_ie_wr_type
  ,ih_ppl_te_ie_blk_burst_num  //only for the Data command
  ,ih_ppl_te_ie_block_num
  ,ih_ppl_te_mwr 
  ,ih_ppl_te_wr_word_valid 
  ,ih_ppl_te_wr_ram_raddr_lsb_first 
  ,ih_ppl_te_wr_pw_num_beats_m1 
  ,ih_ppl_te_wr_pw_num_cols_m1 
   };

assign {
   rxcmd_wdata_ptr
  ,ih_te_rd_valid_orig
  ,ih_te_wr_valid_orig
  ,ih_wu_wr_valid_orig
  ,ih_te_rd_valid_addr_err_orig 
  ,ih_te_wr_valid_addr_err_orig
  ,ih_te_rd_length 
  ,ih_te_rd_tag 
  ,ih_te_rmwtype 
  ,ih_te_hi_pri           // priority that is affected by the force_low_pri_n signal
  ,ih_te_hi_pri_int 

  ,ih_te_autopre          // auto precharge enable flag
  ,ih_te_eccap
  ,ih_te_rank_num
  ,ih_te_bankgroup_num
  ,ih_te_bg_bank_num
  ,ih_te_bank_num
  ,ih_te_page_num
  ,ih_te_block_num
  ,ih_te_critical_dword      // for reads only, critical word within a block - not currently supported
  ,ih_wu_critical_dword      // for reads only, critical word within a block - not currently supported
  ,ih_te_ie_bt
  ,ih_te_ie_bwt
  ,ih_te_ie_rd_type
  ,ih_te_ie_wr_type
  ,ih_te_ie_blk_burst_num  //only for the Data command
  ,ih_te_ie_block_num
  ,ih_te_mwr 
  ,ih_te_wr_word_valid 
  ,ih_te_wr_ram_raddr_lsb_first 
  ,ih_te_wr_pw_num_beats_m1 
  ,ih_te_wr_pw_num_cols_m1 
   } = ih_te_fifo_out;

   wire ih_te_fifo_wr;
   wire ih_te_fifo_rd;
   wire par_err_unused;

   DWC_ddr_umctl2_retime
   
   #(
     .SIZE     (FIFO_DATA_BITS),
     .OCCAP_EN (0),
     .OCCAP_PIPELINE_EN (0)) // Balancing for check_occap_en_cmp_occap_pipeline_en check in preprocess script
   U_retime
   (
     .clk         (co_ih_clk),    
     .rst_n       (core_ddrc_rstn),    
     .d           (ih_te_fifo_in),
     .wr          (ih_te_fifo_wr),
     .rd          (ih_te_fifo_rd),
     .par_en      (1'b0),
     .q           (ih_te_fifo_out_ie),
     .fe          (ih_te_fifo_empty),
     .ff          (ih_te_fifo_full),
     .par_err     (par_err_unused)
   );

   wire in_vpr_expired;
   wire out_vpr_expired;
   reg  any_vpr_timed_out;
   wire ih_te_fifo_wr_vpr;
   wire ih_te_fifo_rd_vpr;
   wire [RD_LATENCY_BITS-1:0]  rd_latency_vpr;
   wire vpr_timer_counters_empty_unused;
   wire vpr_timer_counters_full_unused;
   wire occap_xpi_vpt_par_err_unused;
   wire [RD_LATENCY_BITS-1:0] ih_te_rd_latency_ie;
   wire ih_gs_any_vpr_timed_out_ie;

   assign ih_gs_any_vpr_timed_out_ie = any_vpr_timed_out;
   assign in_vpr_expired = ~|ih_ppl_te_rd_latency;

   assign ih_te_fifo_wr_vpr = ih_te_fifo_wr & ih_ppl_te_rd_valid & (ih_ppl_te_hi_pri==CMD_PRI_VPR);
   assign ih_te_fifo_rd_vpr = ih_te_fifo_rd & ih_te_rd_valid & (ih_te_hi_pri==CMD_PRI_VPR);
   assign ih_te_rd_latency_ie  = ih_te_hi_pri==CMD_PRI_VPR ? rd_latency_vpr : {RD_LATENCY_BITS{1'b1}};

   // if a command expires while in IH then indication won't
   // go to GS module, until the write collision is cleared.
   // //--------------------------
   always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
      if(~core_ddrc_rstn) begin
         any_vpr_timed_out <= 1'b0;
      end else if(ddrc_cg_en) begin
         any_vpr_timed_out <= out_vpr_expired & ~te_ih_retry;
      end
   end

   DWC_ddr_umctl2_xpi_vpt
   
   #(
     .CNT_WIDTH    (RD_LATENCY_BITS),
     .CNT_DEPTH    (2),
     .OCCAP_EN     (0),
     .OCCAP_PIPELINE_EN (0)) // Balancing for check_occap_en_cmp_occap_pipeline_en check in preprocess script
   U_vpr_timer
   (
      // inputs
      .e_clk               (co_ih_clk),
      .e_rst_n             (core_ddrc_rstn),
      .push                (ih_te_fifo_wr_vpr),
      .pop                 (ih_te_fifo_rd_vpr),
      .input_timeout       (ih_ppl_te_rd_latency),
      .input_timeout_zero  (in_vpr_expired),
      .reg_ddrc_occap_en   (1'b0),
      // outputs
      .counters_empty      (vpr_timer_counters_empty_unused),
      .counters_full       (vpr_timer_counters_full_unused),
      .output_timeout_zero (out_vpr_expired),
      .output_timeout      (rd_latency_vpr),
      .occap_xpi_vpt_par_err (occap_xpi_vpt_par_err_unused)
   );

   wire in_vpw_expired;
   wire out_vpw_expired;
   reg  any_vpw_timed_out;
   wire ih_te_fifo_wr_vpw;
   wire ih_te_fifo_rd_vpw;
   wire [WR_LATENCY_BITS-1:0]  wr_latency_vpw;
   wire vpw_timer_counters_empty_unused;
   wire vpw_timer_counters_full_unused;
   wire occap_xpi_vpw_par_err_unused;
   wire [WR_LATENCY_BITS-1:0] ih_te_wr_latency_ie;
   wire ih_gs_any_vpw_timed_out_ie;

   assign ih_gs_any_vpw_timed_out_ie = any_vpw_timed_out;
   assign in_vpw_expired = ~|ih_ppl_te_wr_latency;

   assign ih_te_fifo_wr_vpw = ih_te_fifo_wr & ih_ppl_te_wr_valid & (ih_ppl_te_hi_pri==CMD_PRI_VPW);
   assign ih_te_fifo_rd_vpw = ih_te_fifo_rd & ih_te_wr_valid & (ih_te_hi_pri==CMD_PRI_VPW);
   assign ih_te_wr_latency_ie  = ih_te_hi_pri==CMD_PRI_VPW ? wr_latency_vpw : {WR_LATENCY_BITS{1'b1}};

   // if a command expires while in IH then indication won't
   // go to GS module, until the collision is cleared.
   // //--------------------------
   always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
      if(~core_ddrc_rstn) begin
         any_vpw_timed_out <= 1'b0;
      end else if(ddrc_cg_en) begin
         any_vpw_timed_out <= out_vpw_expired & ~te_ih_retry;
      end
   end


   DWC_ddr_umctl2_xpi_vpt
   
   #(
     .CNT_WIDTH    (WR_LATENCY_BITS),
     .CNT_DEPTH    (2),
     .OCCAP_EN     (0),
     .OCCAP_PIPELINE_EN (0)) // Balancing for check_occap_en_cmp_occap_pipeline_en check in preprocess script
   U_vpw_timer
   (
      // inputs
      .e_clk               (co_ih_clk),
      .e_rst_n             (core_ddrc_rstn),
      .push                (ih_te_fifo_wr_vpw),
      .pop                 (ih_te_fifo_rd_vpw),
      .input_timeout       (ih_ppl_te_wr_latency),
      .input_timeout_zero  (in_vpw_expired),
      .reg_ddrc_occap_en   (1'b0),
      // outputs
      .counters_empty      (vpw_timer_counters_empty_unused),
      .counters_full       (vpw_timer_counters_full_unused),
      .output_timeout_zero (out_vpw_expired),
      .output_timeout      (wr_latency_vpw),
      .occap_xpi_vpt_par_err (occap_xpi_vpw_par_err_unused)
   );

   // wu_ih_flow_cntrl_req indication that wu_wdata_if fifo is full
   // all the commands in the fifo are waiting for data_valid.
   // overhead WECC command can go anyway.
   wire is_wecc_cmd;
   wire wu_ih_stall;

   assign is_wecc_cmd     = (ih_te_ie_wr_type == `IE_WR_TYPE_WE_BW) & ih_te_wr_valid_orig & ~ih_te_fifo_empty;

   assign wu_ih_stall     = wu_ih_flow_cntrl_req & ~is_wecc_cmd;

   wire   ih_te_fifo_wr_ie = (ih_ppl_te_rd_valid | ih_ppl_te_wr_valid)& ~ih_te_fifo_full;
   wire   ih_te_fifo_rd_ie = ~ih_te_fifo_empty & ~te_ih_retry & ~wu_ih_stall;
   wire   te_ppl_ih_stall_ie = ih_te_fifo_full;
   assign ih_te_ppl_empty_ie = ih_te_fifo_empty;

  //output valid only when ih_te_fifo is not empty
  wire ih_te_rd_valid_ie = ~ih_te_fifo_empty & ~wu_ih_stall & ih_te_rd_valid_orig;
  wire ih_te_wr_valid_ie = ~ih_te_fifo_empty & ~wu_ih_stall & ih_te_wr_valid_orig;
  wire ih_wu_wr_valid_ie = ~ih_te_fifo_empty & ~wu_ih_stall & ih_wu_wr_valid_orig;
  wire ih_te_rd_valid_addr_err_ie = ~ih_te_fifo_empty & ~wu_ih_stall & ih_te_rd_valid_addr_err_orig;
  wire ih_te_wr_valid_addr_err_ie = ~ih_te_fifo_empty & ~wu_ih_stall & ih_te_wr_valid_addr_err_orig;

//-----------------------------------------
// Logic for generating the separate Write and Read FIFO empty signals
//-----------------------------------------

// The width of 2-bits has an assumption that the input FIFO will always be 2-deep
reg [1:0] wr_in_fifo, rd_in_fifo;
wire      wr_put, wr_get;
wire      rd_put, rd_get;

assign    wr_put = ih_ppl_te_wr_valid & ~ih_te_fifo_full;
assign    wr_get = ih_te_fifo_rd && ih_te_wr_valid;

assign    rd_put = ih_ppl_te_rd_valid & ~ih_te_fifo_full;
assign    rd_get = ih_te_fifo_rd && ih_te_rd_valid;

// generation of signals that indicate that there is a read or write 
// command in the input FIFO
always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
       wr_in_fifo <= 2'b00;
       rd_in_fifo <= 2'b00;
   end
   else begin
      if(wr_put & (~wr_get))
             wr_in_fifo <= wr_in_fifo + 2'b01;
      else if(wr_get & (~wr_put))
             wr_in_fifo <= wr_in_fifo - 2'b01;

      if(rd_put & (~rd_get))
             rd_in_fifo <= rd_in_fifo + 2'b01;
      else if(rd_get & (~rd_put))
             rd_in_fifo <= rd_in_fifo - 2'b01;

   end
end

assign ih_te_ppl_wr_empty_ie = (wr_in_fifo == 2'b00);
assign ih_te_ppl_rd_empty_ie = (rd_in_fifo == 2'b00);

  // MUX to select based on ecc_type
  // Bypasses PIPELINE's FIFO if ecc_type=0
  assign ih_te_fifo_wr    = (reg_ddrc_ecc_type) ? ih_te_fifo_wr_ie   : 1'b0;
  assign ih_te_fifo_rd    = (reg_ddrc_ecc_type) ? ih_te_fifo_rd_ie   : 1'b0;
  assign ih_te_fifo_out   = (reg_ddrc_ecc_type) ? ih_te_fifo_out_ie  : ih_te_fifo_in;

  assign te_ppl_ih_stall  = (reg_ddrc_ecc_type) ? te_ppl_ih_stall_ie : te_ih_retry;
  assign ih_te_ppl_wr_empty = (reg_ddrc_ecc_type) ? ih_te_ppl_wr_empty_ie : 1'b1;
  assign ih_te_ppl_rd_empty = (reg_ddrc_ecc_type) ? ih_te_ppl_rd_empty_ie : 1'b1;
  assign ih_te_ppl_empty    = (reg_ddrc_ecc_type) ? ih_te_ppl_empty_ie    : 1'b1;

  assign ih_te_rd_valid   = (reg_ddrc_ecc_type) ? ih_te_rd_valid_ie  : ih_te_rd_valid_orig;
  assign ih_te_wr_valid   = (reg_ddrc_ecc_type) ? ih_te_wr_valid_ie  : ih_te_wr_valid_orig;
  assign ih_wu_wr_valid   = (reg_ddrc_ecc_type) ? ih_wu_wr_valid_ie  : ih_wu_wr_valid_orig;
  assign ih_te_rd_valid_addr_err = (reg_ddrc_ecc_type) ? ih_te_rd_valid_addr_err_ie : ih_te_rd_valid_addr_err_orig;
  assign ih_te_wr_valid_addr_err = (reg_ddrc_ecc_type) ? ih_te_wr_valid_addr_err_ie : ih_te_wr_valid_addr_err_orig;

  assign ih_te_rd_latency        = (reg_ddrc_ecc_type) ? ih_te_rd_latency_ie        : ih_ppl_te_rd_latency;
  assign ih_gs_any_vpr_timed_out = (reg_ddrc_ecc_type) ? ih_gs_any_vpr_timed_out_ie : ih_ppl_gs_any_vpr_timed_out;
  assign ih_te_wr_latency        = (reg_ddrc_ecc_type) ? ih_te_wr_latency_ie        : ih_ppl_te_wr_latency;
  assign ih_gs_any_vpw_timed_out = (reg_ddrc_ecc_type) ? ih_gs_any_vpw_timed_out_ie : ih_ppl_gs_any_vpw_timed_out;



`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON

a_ih_te_ppl_empty: //---------------------------------------------------------
    assert property ( @ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
         (ih_te_ppl_empty |-> (ih_te_ppl_wr_empty && ih_te_ppl_rd_empty))) 
    else $error("[%t][%m] ERROR: ih_te_ppl_rd_empty OR ih_te_ppl_wr_empty is showing non-empty when ih_te_ppl_empty is showing empty.", $time);

a_ih_te_ppl_non_empty: //---------------------------------------------------------
    assert property ( @ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
         (~ih_te_ppl_empty |-> (~ih_te_ppl_wr_empty || ~ih_te_ppl_rd_empty))) 
    else $error("[%t][%m] ERROR: ih_te_ppl_rd_empty AND ih_te_ppl_wr_empty are both HIGH when ih_te_ppl_empty is low.", $time);

a_ih_te_ppl_no_wr_when_full:
    assert property ( @ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
         (ih_te_fifo_wr |-> ~ih_te_fifo_full)) 
    else $error("[%t][%m] ERROR: Write into FIFO when it is FULL.", $time);

a_ih_te_ppl_no_rd_when_empty:
    assert property ( @ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
         (ih_te_fifo_rd |-> ~ih_te_fifo_empty)) 
    else $error("[%t][%m] ERROR: Read from FIFO when it is Empty.", $time);


`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
