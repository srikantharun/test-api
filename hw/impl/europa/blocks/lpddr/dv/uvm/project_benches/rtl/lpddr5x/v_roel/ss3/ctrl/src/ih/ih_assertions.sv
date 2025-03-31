//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_assertions.sv#4 $
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

// ----------------------------------------------------------------------------
//                              Description
//
// ----------------------------------------------------------------------------


`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS

`include "DWC_ddrctl_all_defs.svh"
module ih_assertions(
        co_ih_clk,
        core_ddrc_rstn,
        dh_ih_operating_mode,
  
        hif_cmd_valid,
        hif_cmd_addr,
        hif_cmd_type,
        hif_cmd_token,
        hif_cmd_pri,
        hif_cmd_length,
        hif_cmd_wdata_ptr,
        hif_cmd_ecc_region,
        hif_cmd_wdata_mask_full,
        hif_cmd_latency,
        hif_cmd_stall,
        hif_wdata_ptr,
        hif_wdata_ptr_valid,
        hif_lpr_credit,
        hif_wr_credit,
        hif_wrecc_credit,
        dh_ih_blk_channel_active_term,
        hif_hpr_credit,

        // WU Interface
        wu_ih_flow_cntrl_req,



// TE Interface
        ih_te_rd_valid,
        ih_te_wr_valid,
        ih_te_rd_latency,
        ih_te_ie_rd_type,
        ih_te_ie_wr_type,
        ih_te_ie_bt,
        ih_te_ie_blk_burst_num,
        free_bt_vld,
        free_bt,
        ih_te_ie_btt_vct,
        ih_te_rd_valid_addr_err,
        ih_te_wr_valid_addr_err,
        ih_te_rd_length,
        ih_te_rd_tag,
        ih_te_rmwtype,
        ih_te_rank_num,
        ih_te_bg_bank_num,
        ih_te_page_num,
        ih_te_block_num,
        ih_te_critical_dword,
        ih_te_rd_entry,
        ih_te_wr_entry,
        ih_te_lo_rd_prefer,
        ih_te_wr_prefer,

        ih_te_hi_pri,
        ih_te_hi_rd_prefer,

        ih_gs_rdhigh_empty,
        ih_be_hi_pri_rd_xact,
        dh_ih_lpr_num_entries,
        ih_be_rank_num,
        ih_be_bg_bank_num,
        ih_be_page_num,

        te_ih_free_rd_entry,
        te_ih_free_rd_entry_valid,
        mr_ih_free_wr_entry,
        mr_ih_free_wr_entry_valid,
        te_ih_retry,
        te_ih_retry_i,
        te_ih_core_in_stall,
        te_ih_wr_combine
        ,assert_ie_cmd
        ,assert_ie_cmd_invalid_addr
        ,assert_dis_dm
       ,ih_te_rd_eccap
       ,ih_te_wr_eccap
       ,reg_ddrc_ecc_ap_en
       ,input_fifo_empty
       ,ih_te_fifo_empty
       ,reg_ddrc_ecc_type
);

parameter   RDCMD_ENTRY_BITS  = 5;    // bits to address all entries in read CAM                   
parameter   WRCMD_ENTRY_BITS  = 5;    // bits to address all entries in write CAM                  
parameter   CORE_ADDR_WIDTH   = 35;   // any change may necessitate a change to address map in IC  
parameter   IH_TAG_WIDTH      = 8;    // width of token/tag field from core                         
parameter   CMD_LEN_BITS      = 1;    // bits for command length, when used                        
parameter   RMW_TYPE_BITS     = 2;    // 2 bits for RMW type                                       
                                      //  (partial write, atomic RMW, scrub, or none)              
parameter   WDATA_PTR_BITS    = 8;                                                                 

parameter   CMD_TYPE_BITS     = 2;    // any change will require RTL modifications in IC           
parameter   BT_BITS           = 4;
parameter   BWT_BITS          = 4;
parameter   BRT_BITS          = 4;
parameter   NO_OF_BT          = 16;
parameter   IE_BURST_NUM_BITS = 5;
localparam  WRDATA_ENTRY_BITS = WRCMD_ENTRY_BITS + 1;        // write data RAM entries
                                        // (only support 2 datas per command at the moment)

localparam  WR_CAM_DEPTH      = (1 << WRCMD_ENTRY_BITS);
localparam  RD_CAM_DEPTH      = (1 << RDCMD_ENTRY_BITS);
localparam  WRDATA_CYCLES     = `MEMC_WRDATA_CYCLES;


parameter       RD_LATENCY_BITS = `UMCTL2_XPI_RQOS_TW;
parameter       WR_LATENCY_BITS = `UMCTL2_XPI_WQOS_TW;
parameter IE_RD_TYPE_BITS   = `IE_RD_TYPE_BITS;
parameter IE_WR_TYPE_BITS   = `IE_WR_TYPE_BITS;

input                             co_ih_clk;
input                             core_ddrc_rstn;
 
    input [2:0]                   dh_ih_operating_mode;        // global schedule FSM state

  

input                             hif_cmd_valid;
input   [CMD_TYPE_BITS-1:0]       hif_cmd_type;
input   [CORE_ADDR_WIDTH-1:0]     hif_cmd_addr;
input   [IH_TAG_WIDTH-1:0]        hif_cmd_token;
input   [1:0]                     hif_cmd_pri;
input   [CMD_LEN_BITS-1:0]        hif_cmd_length;
input   [WDATA_PTR_BITS-1:0]      hif_cmd_wdata_ptr;
input                             hif_cmd_ecc_region;
input [WRDATA_CYCLES-1:0]         hif_cmd_wdata_mask_full;
input   [RD_LATENCY_BITS-1:0]     hif_cmd_latency;
input [RD_LATENCY_BITS-1:0]       ih_te_rd_latency;
input                             hif_cmd_stall;
input  [WDATA_PTR_BITS-1:0]       hif_wdata_ptr;
input                             hif_wdata_ptr_valid;
input                              hif_wr_credit;
input  [`MEMC_HIF_CREDIT_BITS-1:0] hif_wrecc_credit;
input                              dh_ih_blk_channel_active_term;
input  [`MEMC_HIF_CREDIT_BITS-1:0] hif_lpr_credit;
input  [`MEMC_HIF_CREDIT_BITS-1:0] hif_hpr_credit;

input                             wu_ih_flow_cntrl_req;


input                             ih_te_rd_valid;
input                             ih_te_wr_valid;
input                             ih_te_rd_valid_addr_err;
input                             ih_te_wr_valid_addr_err;
input  [CMD_LEN_BITS-1:0]         ih_te_rd_length;
input  [IH_TAG_WIDTH-1:0]         ih_te_rd_tag;
input  [RMW_TYPE_BITS-1:0]        ih_te_rmwtype;

input  [`UMCTL2_LRANK_BITS -1:0]  ih_te_rank_num;
input  [`MEMC_BG_BANK_BITS -1:0]  ih_te_bg_bank_num;
input  [`MEMC_PAGE_BITS -1:0]     ih_te_page_num;
input  [`MEMC_BLK_BITS  -1:0]     ih_te_block_num;
input  [`MEMC_WORD_BITS -1:0]     ih_te_critical_dword;

input  [RDCMD_ENTRY_BITS-1:0]     ih_te_rd_entry;
input  [WRCMD_ENTRY_BITS-1:0]     ih_te_wr_entry;
input  [WRCMD_ENTRY_BITS-2:0]     ih_te_wr_prefer;
input  [RDCMD_ENTRY_BITS-1:0]     ih_te_lo_rd_prefer;
input [RDCMD_ENTRY_BITS-1:0]      ih_te_hi_rd_prefer;
input [1:0]                       ih_te_hi_pri;


input  [`UMCTL2_LRANK_BITS -1:0]  ih_be_rank_num;
input  [`MEMC_BG_BANK_BITS -1:0]  ih_be_bg_bank_num;
input  [`MEMC_PAGE_BITS -1:0]     ih_be_page_num;

input   [RDCMD_ENTRY_BITS-1:0]    te_ih_free_rd_entry;
input                             te_ih_free_rd_entry_valid;
input   [WRCMD_ENTRY_BITS-1:0]    mr_ih_free_wr_entry;
input                             mr_ih_free_wr_entry_valid;
input                             te_ih_retry;
input                             te_ih_retry_i; //te_ih_retry_i will be assert when te_ih_retry or ie_cmd_active assert, indicate block the input fifo
input                             te_ih_core_in_stall;  //it will be assert when pipeline is full or overhead command is pushing to pipeline
input                             te_ih_wr_combine;

input [IE_RD_TYPE_BITS-1:0]       ih_te_ie_rd_type;
input [IE_WR_TYPE_BITS-1:0]       ih_te_ie_wr_type;
input [BT_BITS-1:0]               ih_te_ie_bt;
input [IE_BURST_NUM_BITS-1:0]     ih_te_ie_blk_burst_num;  //only for the Data command
input                             free_bt_vld;
input [BT_BITS-1:0]               free_bt;
input [NO_OF_BT-1:0]              ih_te_ie_btt_vct;
input                             assert_ie_cmd;
input                             assert_ie_cmd_invalid_addr;
input                             assert_dis_dm;
input                             ih_te_rd_eccap;
input                             ih_te_wr_eccap;
input                             reg_ddrc_ecc_ap_en;
input                             input_fifo_empty;
input                             ih_te_fifo_empty;


input                             reg_ddrc_ecc_type;

input                             ih_be_hi_pri_rd_xact;           // hi priority read transaction valid
input   [RDCMD_ENTRY_BITS-1:0]    dh_ih_lpr_num_entries;
input                             ih_gs_rdhigh_empty;             // transaction queue is empty

//--------------------------------------------------
//---------- AUXILLARY CODE    ---------------------
//--------------------------------------------------


         wire [WRCMD_ENTRY_BITS-1:0]      wr_oldest_radd = ih_te_wr_prefer;


   localparam IH_BUF_DEPTH = 4;
   localparam IH_BUF_ADDR_BITS = 2;


wire    valid_from_core_put, valid_from_core_get;
reg  [IH_BUF_ADDR_BITS-1:0]    valid_from_core_wptr, valid_from_core_rptr;
reg     valid_from_core_fifo   [IH_BUF_DEPTH-1:0];
wire    valid_from_core;

assign valid_from_core_put = hif_cmd_valid && ~hif_cmd_stall;
assign valid_from_core_get = (ih_te_rd_valid || ih_te_wr_valid) && ~te_ih_retry_i && ih_te_rmwtype!=`MEMC_RMW_TYPE_SCRUB;

always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      valid_from_core_wptr    <= {IH_BUF_ADDR_BITS{1'b0}};
   end
   else if(valid_from_core_put) begin
      valid_from_core_wptr    <= valid_from_core_wptr + 1'b1;
   end
end

always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
     for(int i=0; i<IH_BUF_DEPTH; i=i+1)
         valid_from_core_fifo[i] <= 1'b0;
  end
  else begin
    case({valid_from_core_get,valid_from_core_put})
      2'b00 : ;
      2'b01 : valid_from_core_fifo[valid_from_core_wptr] <= 1'b1;
      2'b10 : valid_from_core_fifo[valid_from_core_rptr] <= 1'b0;
      2'b11 : begin
              valid_from_core_fifo[valid_from_core_wptr] <= 1'b1;
              valid_from_core_fifo[valid_from_core_rptr] <= 1'b0;
            end
    endcase
  end
end


always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn)
      valid_from_core_rptr            <= {IH_BUF_ADDR_BITS{1'b0}};
   else if(valid_from_core_get)
      valid_from_core_rptr            <= valid_from_core_rptr + 1'b1;
end

assign  valid_from_core = valid_from_core_fifo[valid_from_core_rptr];



// `ifdef MEMC_SIDEBAND_ECC
// 
// wire scrub_operation;
// assign scrub_operation = ih_te_rd_valid && ih_te_wr_valid && (ih_te_rmwtype == 2'b10);
// 
// //-------- CORRUPT SCRUB ASSERTIONS -----------------------
// 
// `ifdef UMCTL2_NUM_LRANKS_TOTAL_GT_1
// property p_corrupt_scrub_rank;
//         @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) scrub_operation |-> (ih_te_rank_num[0] == expected_scrub_rank);
// endproperty
// 
// 
// assert_corrupt_scrub_rank: assert property (p_corrupt_scrub_rank) else $error("%m @ %t Scrub Rank coming out of IH to TE is wrong", $time);
// 
// `endif // UMCTL2_NUM_LRANKS_TOTAL_GT_1
// 
// 
// property p_corrupt_scrub_bg_bank; 
//         @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) scrub_operation |-> (ih_te_bg_bank_num[0] == expected_scrub_bg_bank);
// endproperty
// 
// assert_corrupt_scrub_bg_bank: assert property (p_corrupt_scrub_bg_bank) else $error("%m @ %t Scrub Bank Group and/or Bank coming out of IH to TE is wrong", $time);
// 
// 
// 
// property p_corrupt_scrub_page; 
//         @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) scrub_operation |-> (ih_te_page_num[0] == expected_scrub_page);
// endproperty
// 
// assert_corrupt_scrub_page: assert property (p_corrupt_scrub_page) else $error("%m @ %t Scrub Page coming out of IH to TE is wrong", $time);
// 
// 
// 
// property p_corrupt_scrub_block;
//         @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) scrub_operation |-> (ih_te_block_num[0] == expected_scrub_block);
// endproperty
// 
// assert_corrupt_scrub_block: assert property (p_corrupt_scrub_block) else $error("%m @ %t Scrub Block coming out of IH to TE is wrong", $time);
// 
// 
// 
// //-------- DROP SCRUB ASSERTIONS -----------------------
// 
// property p_drop_scrub_valid;
//         @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (expected_scrub_valid && ~valid_from_core) |-> (ih_te_rd_valid && ih_te_wr_valid);
// endproperty
// 
// // Temp disabled 23/09/13 due to issue with Scrub commands and current dual HIF implementation
// `ifndef UMCTL2_DUAL_HIF_1
// assert_drop_scrub_valid: assert property (p_drop_scrub_valid) else $error("%m @ %t Scrub request got dropped in IH", $time);
// `endif
// 
// //-------- DUPLICATE SCRUB ASSERTIONS -----------------------
// 
// property p_dup_scrub_valid;
//         @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (scrub_operation && ~te_ih_retry) |-> (expected_scrub_valid && ~valid_from_core);
// endproperty
// 
// // Temp disabled 23/09/13 dur to issue with Scrub commands and current dual HIF implementation
// `ifndef UMCTL2_DUAL_HIF_1
// assert_dup_scrub_valid: assert property (p_dup_scrub_valid) else $error("%m @ %t Duplicate Scrub request at the output of IH", $time);
// `endif
// 
// `endif //MEMC_SIDEBAND_ECC


//##############################
// CREDIT CHECKING LOGIC
//##############################


wire  [WRCMD_ENTRY_BITS-1:0]  max_wr_entries;
wire  [WRCMD_ENTRY_BITS-1:0]  max_wrecc_entries;
wire  [RDCMD_ENTRY_BITS-1:0]  max_lpr_entries;
wire  [RDCMD_ENTRY_BITS-1:0]  max_hpr_entries;

wire  [WRCMD_ENTRY_BITS-1:0]  init_wr_credits;
wire  [WRCMD_ENTRY_BITS-1:0]  init_wrecc_credits;
wire  [RDCMD_ENTRY_BITS-1:0]  init_lpr_credits;
wire  [RDCMD_ENTRY_BITS-1:0]  init_hpr_credits;


// Max value for credits

assign  init_wr_credits   = {WRCMD_ENTRY_BITS{1'b0}};
assign  init_wrecc_credits= {WRCMD_ENTRY_BITS{1'b0}};
assign  init_lpr_credits  = {RDCMD_ENTRY_BITS{1'b0}};
assign  init_hpr_credits  = {RDCMD_ENTRY_BITS{1'b0}};

assign  max_wr_entries  = {WRCMD_ENTRY_BITS{1'b1}};
assign  max_wrecc_entries = 0 + {WRCMD_ENTRY_BITS-1{1'b1}};
assign  max_lpr_entries = dh_ih_lpr_num_entries;
assign  max_hpr_entries = ({RDCMD_ENTRY_BITS{1'b1}} - dh_ih_lpr_num_entries);


//------------------------------------------
// Illegal value on the priority input for reads
// When Arbiter: pri=2'b11 is illegal (legal values: 00 - LPR, 01 - VPR, 10 - HPR)
// When HIF + non RMW: pri=2'b01 and 2'b11 is illegal (legal values: 00 - LPR, 10 - HPR)
// When HIF + RMW: no illegal priority (legal values: 00 - LPR, 01 - VPR, 10 - HPR, 11 - HPRL)
//------------------------------------------
assign illegal_rd_pri_value = hif_cmd_valid && ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_RD) 
                                || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                              ) 
                            && (hif_cmd_pri==`MEMC_CMD_PRI_XVPR)
                            && !hif_cmd_stall;


property p_illegal_rd_pri_value;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ~illegal_rd_pri_value;
endproperty


assert_illegal_rd_pri_value: assert property (p_illegal_rd_pri_value);

//------------------------------------------
// Illegal value on the priority input for writes
// When Arbiter and VPW: pri=2'b10 and 2'b11 is illegal (legal values: 00 - NPW, 01 - VPW)
// HIF-only testbench puts non-zero value on hif_cmd_pri for write commands - these are ignnored by RTL
// hence the check is limited to configs with UMCTL2_INCL_ARB defined
//------------------------------------------

  
assign illegal_wr_pri_value = hif_cmd_valid && ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_WR)
                                || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                                ) && !hif_cmd_stall
                         &&   ((hif_cmd_pri==`MEMC_CMD_PRI_XVPW) || (hif_cmd_pri==`MEMC_CMD_PRI_RSVD))
                        ;


property p_illegal_wr_pri_value;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ~illegal_wr_pri_value;
endproperty


assert_illegal_wr_pri_value: assert property (p_illegal_wr_pri_value);



reg [1:0] ih_te_cmd_pri_fifo[IH_BUF_DEPTH-1:0];
reg [1:0] ih_te_cmd_type_fifo[IH_BUF_DEPTH-1:0];
reg ih_te_cmd_ecc_region_fifo[IH_BUF_DEPTH-1:0];
reg [CMD_LEN_BITS-1:0] ih_te_cmd_len_fifo[IH_BUF_DEPTH-1:0];
reg [WRDATA_CYCLES-1:0] ih_te_cmd_wdata_mask_full_fifo[IH_BUF_DEPTH-1:0];

wire [1:0] hif_cmd_pri_i;
wire [1:0] hif_cmd_type_i;
wire hif_cmd_ecc_region_i;
wire [CMD_LEN_BITS-1:0] hif_cmd_length_i;
wire [WRDATA_CYCLES-1:0] hif_cmd_wdata_mask_full_i;
wire ie_wr_data_cmd_valid;
wire ie_rd_data_cmd_valid;

reg [RD_LATENCY_BITS-1:0] ih_te_cmd_latency_fifo[IH_BUF_DEPTH-1:0];
wire [RD_LATENCY_BITS-1:0] hif_cmd_latency_i;

reg [8-1:0] blk_wr_received_per_bt[NO_OF_BT-1:0];
reg  full_blk_wr_received_per_bt_r[NO_OF_BT-1:0]; 
reg [8-1:0] blk_rd_received_per_bt[NO_OF_BT-1:0];
reg  full_blk_rd_received_per_bt_r[NO_OF_BT-1:0]; 
wire full_blk_wr_received_per_bt[NO_OF_BT-1:0]; 
wire full_blk_rd_received_per_bt[NO_OF_BT-1:0]; 

reg ie_wr_data_cmd_valid_new;
reg ie_rd_data_cmd_valid_new;

always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
     for (int i=0; i<IH_BUF_DEPTH; i=i+1) begin
        ih_te_cmd_pri_fifo[i]       <= 2'b00;
        ih_te_cmd_type_fifo[i]      <= 2'b00;
        ih_te_cmd_ecc_region_fifo[i]<= 1'b0;
        ih_te_cmd_len_fifo[i]       <= {CMD_LEN_BITS{1'b0}};
        ih_te_cmd_latency_fifo[i]   <= {RD_LATENCY_BITS{1'b0}};
        ih_te_cmd_wdata_mask_full_fifo[i] <= {WRDATA_CYCLES{1'b0}};
     end
    ie_wr_data_cmd_valid_new    <= 1'b0;
    ie_rd_data_cmd_valid_new    <= 1'b0;
  end else begin
    if(valid_from_core_put) begin
      ih_te_cmd_pri_fifo[valid_from_core_wptr]        <= hif_cmd_pri;
      ih_te_cmd_type_fifo[valid_from_core_wptr]       <= hif_cmd_type;
      ih_te_cmd_ecc_region_fifo[valid_from_core_wptr] <= hif_cmd_ecc_region;
      ih_te_cmd_len_fifo[valid_from_core_wptr]        <= hif_cmd_length;
      ih_te_cmd_latency_fifo[valid_from_core_wptr]    <= (hif_cmd_latency=={RD_LATENCY_BITS{1'b0}}) ? {RD_LATENCY_BITS{1'b0}} : hif_cmd_latency-1;
      ih_te_cmd_wdata_mask_full_fifo[valid_from_core_wptr] <= hif_cmd_wdata_mask_full;
    end
    if(!te_ih_retry) begin
      ie_wr_data_cmd_valid_new <= ie_wr_data_cmd_valid;
      ie_rd_data_cmd_valid_new <= ie_rd_data_cmd_valid;
    end
  end
end

genvar bt_num;
generate
  for (bt_num=0;bt_num<NO_OF_BT;bt_num=bt_num+1) begin : num_bursts_GEN
    always @(posedge co_ih_clk or negedge core_ddrc_rstn) begin
      if (~core_ddrc_rstn) begin
        blk_wr_received_per_bt[bt_num]        <= {8{1'b0}};
        full_blk_wr_received_per_bt_r[bt_num] <= 1'b0;
        blk_rd_received_per_bt[bt_num]        <= {8{1'b0}};
        full_blk_rd_received_per_bt_r[bt_num] <= 1'b0;
      end else begin
        if(ih_te_wr_valid && (ih_te_ie_wr_type==`IE_WR_TYPE_WD_E) && (ih_te_ie_bt==bt_num) && (!te_ih_retry) && (&hif_cmd_wdata_mask_full_i) ) begin
          blk_wr_received_per_bt[bt_num][ih_te_ie_blk_burst_num[2:0]] <= 1'b1;
        end else if(free_bt_vld && (free_bt==bt_num)) begin // reset 
          blk_wr_received_per_bt[bt_num] <= {8{1'b0}};
        end
        if(ih_te_rd_valid && (ih_te_ie_rd_type==`IE_RD_TYPE_RD_E) && (ih_te_ie_bt==bt_num) && (!te_ih_retry) && (hif_cmd_type_i!=`MEMC_CMD_TYPE_RMW) ) begin
          blk_rd_received_per_bt[bt_num][ih_te_ie_blk_burst_num[2:0]] <= 1'b1;
        end else if(free_bt_vld && (free_bt==bt_num)) begin // reset 
          blk_rd_received_per_bt[bt_num] <= {8{1'b0}};
        end
        full_blk_rd_received_per_bt_r[bt_num] <= (free_bt_vld && (free_bt==bt_num)) ? 1'b0 : (&blk_rd_received_per_bt[bt_num][7:0]);
        if((&blk_wr_received_per_bt[bt_num][7:0]) && (!(free_bt_vld && (free_bt==bt_num))) ) begin
          full_blk_wr_received_per_bt_r[bt_num] <= (ih_te_wr_valid && (ih_te_ie_wr_type==`IE_WR_TYPE_WE_BW) && (ih_te_ie_bt==bt_num) && (!te_ih_retry)) | full_blk_wr_received_per_bt_r[bt_num];
        end else if(free_bt_vld && (free_bt==bt_num))
          full_blk_wr_received_per_bt_r[bt_num] <= 1'b0;
      end
    end
  assign full_blk_wr_received_per_bt[bt_num] = (free_bt_vld && (free_bt==bt_num)) ? 1'b0 : full_blk_wr_received_per_bt_r[bt_num];
  assign full_blk_rd_received_per_bt[bt_num] = (free_bt_vld && (free_bt==bt_num)) ? 1'b0 : full_blk_rd_received_per_bt_r[bt_num];
  end
endgenerate

assign hif_cmd_pri_i        = ih_te_cmd_pri_fifo[valid_from_core_rptr];
assign hif_cmd_type_i       = ih_te_cmd_type_fifo[valid_from_core_rptr];
assign hif_cmd_length_i     = ih_te_cmd_len_fifo[valid_from_core_rptr];
assign hif_cmd_wdata_mask_full_i = ih_te_cmd_wdata_mask_full_fifo[valid_from_core_rptr];

assign hif_cmd_ecc_region_i = ih_te_cmd_ecc_region_fifo[valid_from_core_rptr];
assign hif_cmd_latency_i    = ih_te_cmd_latency_fifo[valid_from_core_rptr];

assign wr_cmd_pri_mismatch = ih_te_wr_valid && (!te_ih_retry) && (ih_te_ie_wr_type!=`IE_WR_TYPE_WE_BW) && (ih_te_hi_pri!=hif_cmd_pri_i);
assign rd_cmd_pri_mismatch = ih_te_rd_valid && (!te_ih_retry) && ((ih_te_ie_rd_type==`IE_RD_TYPE_RD_N)||(ih_te_ie_rd_type==`IE_RD_TYPE_RD_E)) && (ih_te_hi_pri!=hif_cmd_pri_i);
assign ie_rd_ecc_cmd_pri_mismatch = ih_te_rd_valid && (!te_ih_retry) && (ih_te_ie_rd_type==`IE_RD_TYPE_RE_B) && (ih_te_hi_pri!=hif_cmd_pri_i);
assign ie_wr_ecc_cmd_pri_mismatch = ih_te_wr_valid && (!te_ih_retry) && (ih_te_ie_wr_type==`IE_WR_TYPE_WE_BW) && (ih_te_hi_pri!=2'b00);
assign ie_rd_ecc_cmd_unprotected_region = ih_te_rd_valid && (!te_ih_retry) && (ih_te_ie_rd_type==`IE_RD_TYPE_RE_B) && (hif_cmd_ecc_region_i==1'b0);
assign ie_wr_data_cmd_valid = ih_te_wr_valid && (!te_ih_retry) && (ih_te_ie_wr_type==`IE_WR_TYPE_WD_E);
assign ie_wr_ecc_cmd_valid  = ih_te_wr_valid && (!te_ih_retry) && (ih_te_ie_wr_type==`IE_WR_TYPE_WE_BW);
assign ie_rd_data_cmd_valid = ih_te_rd_valid && (!te_ih_retry) && (ih_te_ie_rd_type==`IE_RD_TYPE_RD_E);
assign ie_rd_ecc_cmd_valid  = ih_te_rd_valid && (!te_ih_retry) && (ih_te_ie_rd_type==`IE_RD_TYPE_RE_B);

property p_ie_ih_wr_cmd_pri_not_loaded_as_incoming_pri;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ~wr_cmd_pri_mismatch;
endproperty

property p_ie_ih_rd_cmd_pri_not_loaded_as_incoming_pri;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ~rd_cmd_pri_mismatch;
endproperty

property p_ie_ih_rd_ecc_cmd_pri_not_loaded_as_1st_data_cmd_pri;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ~ie_rd_ecc_cmd_pri_mismatch;
endproperty

property p_ie_ih_wr_ecc_cmd_pri_not_loaded_as_npw;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ~ie_wr_ecc_cmd_pri_mismatch;
endproperty

property p_ie_ih_wr_ecc_cmd_not_loaded_after_1st_data_cmd;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ((ie_wr_data_cmd_valid_new & !te_ih_retry) |-> ie_wr_ecc_cmd_valid) ;
endproperty

property p_ie_ih_rd_ecc_cmd_not_loaded_after_1st_data_cmd;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ((ie_rd_data_cmd_valid_new & !te_ih_retry) |-> ie_rd_ecc_cmd_valid) ;
endproperty

property p_ie_ih_rd_ecc_cmd_loaded_to_unprotected_ecc_region;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ~ie_rd_ecc_cmd_unprotected_region;
endproperty

property p_ie_ih_wr_bt_not_terminated_when_full_wr_blk_access_done(bwt);
   @(posedge co_ih_clk) disable iff (~core_ddrc_rstn | (~dh_ih_blk_channel_active_term)) 
      ( full_blk_wr_received_per_bt[bwt] ) |-> ##1 (ih_te_ie_btt_vct[bwt]);
endproperty

property p_ie_ih_rd_bt_not_terminated_when_full_rd_blk_access_done(brt);
   @(posedge co_ih_clk) disable iff (~core_ddrc_rstn | (~dh_ih_blk_channel_active_term)) 
      ( full_blk_rd_received_per_bt[brt] ) |-> ##1 (ih_te_ie_btt_vct[brt]);
endproperty

a_ie_ih_wr_cmd_pri_not_loaded_as_incoming_pri: assert property (p_ie_ih_wr_cmd_pri_not_loaded_as_incoming_pri)
else $display("[%t][%m] ERROR: Write command's priority is not loaded as expected into CAM. Expected ih_te_hi_pri=%0h", $time,hif_cmd_pri_i);

a_ie_ih_rd_cmd_pri_not_loaded_as_incoming_pri: assert property (p_ie_ih_rd_cmd_pri_not_loaded_as_incoming_pri)
else $display("[%t][%m] ERROR: Read command's priority is not loaded as expected into CAM. Expected ih_te_hi_pri=%0h", $time,hif_cmd_pri_i);

a_ie_ih_rd_ecc_cmd_pri_not_loaded_as_1st_data_cmd_pri: assert property (p_ie_ih_rd_ecc_cmd_pri_not_loaded_as_1st_data_cmd_pri)
else $display("[%t][%m] ERROR: [Inline ECC] Read ECC command's priority is not same as first Read Data command of that block, expected ih_te_hi_pri=%0h", $time,hif_cmd_pri_i);

a_ie_ih_wr_ecc_cmd_pri_not_loaded_as_npw: assert property (p_ie_ih_wr_ecc_cmd_pri_not_loaded_as_npw)
else $display("[%t][%m] ERROR: [Inline ECC] Write ECC command's priority is not same NPW", $time);

a_ie_ih_wr_ecc_cmd_not_loaded_after_1st_data_cmd: assert property (p_ie_ih_wr_ecc_cmd_not_loaded_after_1st_data_cmd)
else $display("[%t][%m] ERROR: [Inline ECC] WR ECC command is not loaded after first Write Data command of that block", $time);

//a_ie_ih_rd_ecc_cmd_not_loaded_after_1st_data_cmd: assert property (p_ie_ih_rd_ecc_cmd_not_loaded_after_1st_data_cmd)
//else $display("[%t][%m] ERROR: [Inline ECC] RD ECC command is not loaded after first Read Data command of that block", $time);
//a_ie_ih_rd_ecc_cmd_not_loaded_after_1st_data_cmd: cover property (p_ie_ih_rd_ecc_cmd_not_loaded_after_1st_data_cmd)
//$display("[%t][%m] WARNING: [Inline ECC] RD ECC command is not loaded after first Read Data command of that block", $time);

// This assertion is valid only for Arbiter Configs
a_ie_ih_rd_ecc_cmd_loaded_to_unprotected_ecc_region: assert property (p_ie_ih_rd_ecc_cmd_loaded_to_unprotected_ecc_region)
else $display("[%t][%m] ERROR: [Inline ECC] Read ECC command loaded into CAM for un-protected ECC region", $time);

assign ie_rd_ecc_cmd_latency_mismatch = ih_te_rd_valid && (!te_ih_retry) && (ih_te_ie_rd_type==`IE_RD_TYPE_RE_B) && (ih_te_hi_pri==`MEMC_CMD_PRI_VPR || ih_te_hi_pri==`MEMC_CMD_PRI_XVPR) && (ih_te_rd_latency>hif_cmd_latency_i);

property p_ie_ih_rd_ecc_cmd_latency_not_loaded_as_1st_data_cmd_latency;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) ~ie_rd_ecc_cmd_latency_mismatch;
endproperty

a_ie_ih_rd_ecc_cmd_latency_not_loaded_as_1st_data_cmd_latency: assert property (p_ie_ih_rd_ecc_cmd_latency_not_loaded_as_1st_data_cmd_latency)
else $display("[%t][%m] ERROR: [Inline ECC] Read ECC command's latency is not same as first Read Data command of that block, expected ih_te_rd_latency=%0h", $time,hif_cmd_latency_i);

genvar btnum;
generate 
for(btnum=0; btnum<NO_OF_BT; btnum=btnum+1) begin : a_full_blk_bt_gen
//  a_ie_ih_wr_bt_not_terminated_when_full_wr_blk_access_done : assert property (p_ie_ih_wr_bt_not_terminated_when_full_wr_blk_access_done(btnum))
//  else $display("[%t][%m] ERROR: [Inline ECC] Write BT is not terminated when full block access is performed to BWT =%0d ", $time,btnum);
  a_ie_ih_rd_bt_not_terminated_when_full_rd_blk_access_done : assert property (p_ie_ih_rd_bt_not_terminated_when_full_rd_blk_access_done(btnum))
  else $display("[%t][%m] ERROR: [Inline ECC] Read BT is not terminated when full block access is performed to BRT =%0d ", $time,btnum);
end
endgenerate


/////////////////////////////
// WRITE Credit mechanism for generating the cmd_valid
/////////////////////////////

reg                           r_resetb;    // reset in the previous cycle
                                           //  (used by all 3 credit logic groups)
reg   [WRCMD_ENTRY_BITS-1:0]  wrecc_credits_avail;
reg   [WRCMD_ENTRY_BITS:0]    wr_credits_avail;

wire                              incr_wr_credit;
wire                              decr_wr_credit;
wire                              incr_wrecc_credit;
wire                              decr_wrecc_credit;

assign decr_wr_credit = hif_cmd_valid && ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_WR)
                                || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                                ) && !hif_cmd_stall;
assign decr_wrecc_credit = ih_te_wr_valid && (ih_te_ie_wr_type==`IE_WR_TYPE_WE_BW) && !te_ih_retry;

assign incr_wrecc_credit = hif_wrecc_credit[0];

always @ (posedge co_ih_clk or negedge core_ddrc_rstn)  begin
  if(!core_ddrc_rstn) begin
    wrecc_credits_avail <= init_wrecc_credits;
  end
  else begin
    // assign credit_avail in the cycle after reset, in case it was modified
    //  in the same cycle that soft reset was de-asserted
    if (!r_resetb)
      wrecc_credits_avail <= init_wrecc_credits;

    case ({decr_wrecc_credit,incr_wrecc_credit})
      2'b00 : wrecc_credits_avail <= wrecc_credits_avail;
      2'b01 : wrecc_credits_avail <= wrecc_credits_avail + 1'b1;
      2'b10 : wrecc_credits_avail <= wrecc_credits_avail - 1'b1;
      2'b11 : wrecc_credits_avail <= wrecc_credits_avail;
    endcase

  end
end


        
assign incr_wr_credit = hif_wr_credit;

always @ (posedge co_ih_clk or negedge core_ddrc_rstn)  begin
  if(!core_ddrc_rstn) begin
    wr_credits_avail <= init_wr_credits;
    r_resetb         <= 1'b0;
  end
  else begin
    r_resetb         <= 1'b1;

    // assign credit_avail in the cycle after reset, in case it was modified
    //  in the same cycle that soft reset was de-asserted
    if (!r_resetb)
      wr_credits_avail <= init_wr_credits;

    case ({decr_wr_credit,incr_wr_credit})
      2'b00 : wr_credits_avail <= wr_credits_avail;
      2'b01 : wr_credits_avail <= wr_credits_avail + 1'b1;
      2'b10 : wr_credits_avail <= wr_credits_avail - 1'b1;
      2'b11 : wr_credits_avail <= wr_credits_avail;
    endcase

  end
end


/////////////////////////////
// LPR Credit mechanism for generating the cmd_valid
/////////////////////////////

reg   [RDCMD_ENTRY_BITS:0]      lpr_credits_avail;

wire  [`MEMC_HIF_CREDIT_BITS-1:0] incr_lpr_credit;
wire  [`MEMC_HIF_CREDIT_BITS-1:0] decr_lpr_credit;


assign decr_lpr_credit[0] = hif_cmd_valid && ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_RD)
                                || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                                ) &&
                                !(hif_cmd_pri==2'b10) && !hif_cmd_stall;        
assign decr_lpr_credit[1] = (decr_lpr_credit[0] & (assert_ie_cmd | assert_ie_cmd_invalid_addr)); 
        
assign incr_lpr_credit = hif_lpr_credit; 

always @ (posedge co_ih_clk or negedge core_ddrc_rstn)  begin
  if(!core_ddrc_rstn)
    lpr_credits_avail <= init_lpr_credits;
  else begin

    // assign credit_avail in the cycle after reset, in case it was modified
    //  in the same cycle that soft reset was de-asserted
    if (!r_resetb)
      lpr_credits_avail <= init_lpr_credits;

    lpr_credits_avail <= lpr_credits_avail + incr_lpr_credit[0] + incr_lpr_credit[1] - decr_lpr_credit[0] - decr_lpr_credit[1];

  end
end


/////////////////////////////
// HPR Credit mechanism for generating the cmd_valid
/////////////////////////////

reg   [RDCMD_ENTRY_BITS-1:0]    hpr_credits_avail;
wire  [`MEMC_HIF_CREDIT_BITS-1:0] incr_hpr_credit;
wire  [`MEMC_HIF_CREDIT_BITS-1:0] decr_hpr_credit;


assign decr_hpr_credit[0] = hif_cmd_valid && ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_RD)
                                || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                                ) && 
                                (hif_cmd_pri==2'b10) && !hif_cmd_stall;
      assign decr_hpr_credit[1] = decr_hpr_credit[0] & (assert_ie_cmd | assert_ie_cmd_invalid_addr);
      
assign incr_hpr_credit = hif_hpr_credit;

always @ (posedge co_ih_clk or negedge core_ddrc_rstn)  begin
  if(!core_ddrc_rstn)
    hpr_credits_avail <= init_hpr_credits;
  else begin

    // assign credit_avail in the cycle after reset, in case it was modified
    //  in the same cycle that soft reset was de-asserted
    if (!r_resetb)
      hpr_credits_avail <= init_hpr_credits;

    hpr_credits_avail <= hpr_credits_avail + incr_hpr_credit[0] + incr_hpr_credit[1] - decr_hpr_credit[0] - decr_hpr_credit[1];

  end
end




//---------------------------
// Keeping track of entries
//---------------------------
reg [WR_CAM_DEPTH-1:0] wr_entry_in_te;
reg [RD_CAM_DEPTH-1:0] rd_entry_in_te;


// WR CAM 
// 1 indicates there is an entry in the CAM 
// 0 indicates there is NO entry in the CAM 
always @(posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if (!core_ddrc_rstn) begin
       wr_entry_in_te <= {WR_CAM_DEPTH{1'b0}};
   end
   else begin
      if (~te_ih_retry && (ih_te_wr_valid 
                                && ~ih_te_wr_valid_addr_err
                          ) && ~te_ih_wr_combine )
         wr_entry_in_te[ih_te_wr_entry]   <= 1'b1;
      if (mr_ih_free_wr_entry_valid)
         wr_entry_in_te[mr_ih_free_wr_entry]   <= 1'b0;
   end
end


// RD CAM 
// 1 indicates there is an entry in the CAM 
// 0 indicates there is NO entry in the CAM 
always @(posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if (!core_ddrc_rstn) begin
       rd_entry_in_te <= {RD_CAM_DEPTH{1'b0}};
   end
   else begin
      if ((~te_ih_retry && (ih_te_rd_valid
                                && ~(ih_te_rd_valid_addr_err && ih_te_wr_valid_addr_err && ih_te_rmwtype==2'b00)
                           ) && (ih_te_rd_entry <= max_lpr_entries)) || 
          (~te_ih_retry && (ih_te_rd_valid
                                && ~(ih_te_rd_valid_addr_err && ih_te_wr_valid_addr_err && ih_te_rmwtype==2'b00)
                           ) && (ih_te_rd_entry > max_lpr_entries)))
         rd_entry_in_te[ih_te_rd_entry] <= 1'b1;
      if (te_ih_free_rd_entry_valid)
         rd_entry_in_te[te_ih_free_rd_entry] <= 1'b0;
   end
end






wire  other_retry;  // retry if for rd or wr request

assign  other_retry  = te_ih_retry && (ih_te_rd_valid ^ ih_te_wr_valid);




//--------------------------------------------------
//---------- INPUT ASSUMPTIONS ---------------------
//--------------------------------------------------

//---------------------------
//-------cmd_valid-----------
//---------------------------

property p_cmd_valid_keep_high;
  @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) hif_cmd_valid && hif_cmd_stall |-> ##1 hif_cmd_valid;
endproperty

property p_wr_cmd_valid_if_credit_avail;
  @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (hif_cmd_valid && ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_WR)
                                                        || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                                                        ) && !hif_cmd_stall)  |-> 
                (wr_credits_avail > 0);
endproperty

property p_wr_cmd_valid_ecc_region_if_wrecc_credit_avail;
  @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (hif_cmd_valid && hif_cmd_ecc_region && ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_WR)
                                                        || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                                                        ) && !hif_cmd_stall)  |-> 
                (wrecc_credits_avail>0  &&  wr_credits_avail>0);
endproperty


property p_lpr_cmd_valid_if_credit_avail;
  @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (hif_cmd_valid && ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_RD)
                                                        || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                                                        ) && 
              !(hif_cmd_pri==2'b10) && !hif_cmd_stall) |-> (lpr_credits_avail > 0);
endproperty


property p_hpr_cmd_valid_if_credit_avail;
  @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (hif_cmd_valid && ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_RD)
                                                        || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                                                        ) &&
              (hif_cmd_pri==2'b10) && !hif_cmd_stall) |-> (hpr_credits_avail > 0);
endproperty


//---------------------------
//-------cmd_type-----------
//---------------------------
property p_cmd_type_legal;
     @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (hif_cmd_valid && !hif_cmd_stall) |-> 
    ((hif_cmd_type == `MEMC_CMD_TYPE_BLK_WR) || 
     (hif_cmd_type == `MEMC_CMD_TYPE_BLK_RD) 
                    || (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                    );
endproperty


//---------------------------
//------- RETRY allowed only if there is a rd_valid or wr_valid going to the TE
//---------------------------
property p_retry_legal;
   @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) te_ih_retry |-> (ih_te_rd_valid || ih_te_wr_valid);
endproperty


//---------------------------
//------- FREE RD ENTRY only if it has been allocated
//---------------------------
property p_free_rd_entry_only_if_allocated;
  @ (posedge co_ih_clk) disable iff (!core_ddrc_rstn) te_ih_free_rd_entry_valid |->
                rd_entry_in_te[te_ih_free_rd_entry];
endproperty


//---------------------------
//------- FREE WR ENTRY only if it has been allocated
//---------------------------
property p_free_wr_entry_only_if_allocated;
  @ (posedge co_ih_clk) disable iff (!core_ddrc_rstn) mr_ih_free_wr_entry_valid |->
                wr_entry_in_te[mr_ih_free_wr_entry];
endproperty


// `ifdef MEMC_SIDEBAND_ECC_AND_MEMC_USE_RMW
// 
// //--------------------------------------
// //-------scrub free rd entry - free scrub rd entry only if scrub rd request is pending
// //--------------------------------------
// property p_scrub_free_rd_entry;
//      @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry == dh_ih_lpr_num_entries)) |-> ((scrub_pending_ff[0] == 1'b1) || reg_ddrc_ecc_type);
// endproperty
// 
// 
// //--------------------------------------
// //-------scrub free wr entry - free scrub wr entry only if scrub wr request is pending
// //--------------------------------------
// property p_scrub_free_wr_entry;
//      @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (mr_ih_free_wr_entry_valid && (mr_ih_free_wr_entry == {WRCMD_ENTRY_BITS{1'b1}})) |-> ((scrub_pending_ff[1] == 1'b1) || reg_ddrc_ecc_type);
// endproperty
// 
// 
// `endif






// Logic for generating a pulse one clock after reset de-asserts
reg     reset_ff;
wire    first_clk_after_reset;

// flop the reset
always @ (posedge co_ih_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
        reset_ff        <= 1'b0;
  else
        reset_ff        <= core_ddrc_rstn;

// pulse first clk after reset
assign first_clk_after_reset = core_ddrc_rstn & !reset_ff;

// Don't issue rxcmd_valid first clk after reset
// The max_entry_ff in the fifo_control module gets the value one clock after reset is de-asserted
// So if the request from core comes in the first clock after reset, it cannot be handled. the following is the
// constraint for preventing it
property p_no_cmd_first_clk_after_reset;
  @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) hif_cmd_valid |-> ~first_clk_after_reset;
endproperty


//-------Calling the Assume properties -----------



assert_wr_cmd_valid_if_credit_avail  : assert property (p_wr_cmd_valid_if_credit_avail)
          else $error("%m @ %t WR cmd_valid asserted when no Write credits available", $time);

// This assertion is valid only for Arbiter Configs, because hif_cmd_ecc_region is present in ARB configs
assert_wr_cmd_valid_ecc_region_if_wrecc_credit_avail  : assert property (p_wr_cmd_valid_ecc_region_if_wrecc_credit_avail)
          else $error("%m @ %t WR cmd_valid for Inline ECC protected region asserted when no Write/WR ECC credits available", $time);

assert_lpr_cmd_valid_if_credit_avail  : assert property (p_lpr_cmd_valid_if_credit_avail)
          else $error("%m @ %t LPR cmd_valid asserted when no LPR credits available", $time);

assert_cmd_type_legal      : assert property (p_cmd_type_legal) 
          else $error("%m @ %t cmd_type received by IH is not legal. It should either be 2'b00 or 2'b01", $time);

assert_retry_legal      : assert property (p_retry_legal) 
          else $error("%m @ %t Retry received by IH is not legal. Retry should come only if there is either rd_valid or wr_valid going to TE", $time);

assert_free_rd_entry_only_if_allocated   : assert property (p_free_rd_entry_only_if_allocated) 
          else $error("%m @ %t Read entry was free'ed without being allocated", $time);

assert_free_wr_entry_only_if_allocated   : assert property (p_free_wr_entry_only_if_allocated) 
          else $error("%m @ %t Write entry was free'ed without being allocated", $time);


// `ifdef MEMC_SIDEBAND_ECC_AND_MEMC_USE_RMW
// 
// assert_scrub_free_rd_entry    : assert property (p_scrub_free_rd_entry) 
//           else $error("%m %t Scrub Read Entry free'ed when scrub read request is NOT pending", $time);
// 
// assert_scrub_free_wr_entry    : assert property (p_scrub_free_wr_entry) 
//           else $error("%m %t Scrub Write Entry free'ed when scrub write request is NOT pending", $time);
// `endif



assert_hpr_cmd_valid_if_credit_avail  : assert property (p_hpr_cmd_valid_if_credit_avail)
          else $error("%m @ %t HPR cmd_valid asserted when no HPR credits available", $time);



assert_no_cmd_first_clk_after_reset  : assert property (p_no_cmd_first_clk_after_reset)
          else $error("%m @ %t hif_cmd_valid came in first clock after reset", $time);






//--------------------------------------------------
//----------     COVERGAE      ---------------------
//--------------------------------------------------

//--------------------------------------------------
// rd_cmd_valid scenario
//--------------------------------------------------
cover_rd_cmd_valid  : cover property (@(posedge co_ih_clk) disable iff (~core_ddrc_rstn)
        (hif_cmd_valid && (hif_cmd_type == `MEMC_CMD_TYPE_BLK_RD)));

//--------------------------------------------------
//---- Making sure that credits are being issued
//--------------------------------------------------
cover_wr_credit  : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn) hif_wr_credit);
cover_lpr_credit : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn) hif_lpr_credit);
cover_hpr_credit : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn) hif_hpr_credit);


//--------------------------------------------------
// check for credit being issued 2 clocks after receiving free entry (in-order)
//--------------------------------------------------

cover_in_order_wr_free_credit_2clks : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                        (mr_ih_free_wr_entry_valid && (mr_ih_free_wr_entry <= {WRCMD_ENTRY_BITS{1'b1}}) &&
                                           (mr_ih_free_wr_entry == wr_oldest_radd)) ##2 hif_wr_credit);

cover_in_order_lpr_free_credit_2clks : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                        (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry <= dh_ih_lpr_num_entries) &&
                                           (te_ih_free_rd_entry == ih_te_lo_rd_prefer) ##2 hif_lpr_credit[0]));

cover_in_order_hpr_free_credit_2clks : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                        (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry > dh_ih_lpr_num_entries) &&
                                           (te_ih_free_rd_entry == ih_te_hi_rd_prefer) ##2 hif_hpr_credit[0]));


//--------------------------------------------------
// check for out of order free - if the free entry is not for the oldest entry, then no credit should be issued
// after 2 clocks
// FIXME: Is this true? Can credits from previous free's come during this period?
//--------------------------------------------------

/*
cover_out_of_order_wr_free_no_credit_NEG : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                          (mr_ih_free_wr_entry_valid && (mr_ih_free_wr_entry < {WRCMD_ENTRY_BITS{1'b1}}) &&
                                          (mr_ih_free_wr_entry != wr_oldest_radd)) ##0 (!hif_wr_credit[*2]));

cover_out_of_order_lpr_free_no_credit_NEG : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                           (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry < dh_ih_lpr_num_entries) &&
                                           (te_ih_free_rd_entry != ih_te_lo_rd_prefer) ##0 (!hif_lpr_credit[*2])));


`ifndef MEMC_NO_PRIORITY
cover_out_of_order_hpr_free_no_credit_NEG : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                           (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry > dh_ih_lpr_num_entries) &&
                                           (te_ih_free_rd_entry != ih_te_hi_rd_prefer) ##0 (!hif_hpr_credit[*2])));
`endif

*/

//--------------------------------------------------
// checking for a case where retry is on for 10 clocks
//--------------------------------------------------
cover_rd_valid_with_retry : cover property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                           ((hif_cmd_valid && (hif_cmd_type == `MEMC_CMD_TYPE_BLK_RD) && !hif_cmd_stall) ##1
                            (ih_te_rd_valid && other_retry)[*10] ##1 (ih_te_rd_valid && !other_retry)));

//--------------------------------------------------
//----------     ASSERTIONS    ---------------------
//--------------------------------------------------

//--------------------------------------------------
// checking for a bad case of cmd_valid - if stall & cmd_valid are high, next clock cmd_valid & stall cannot be low
// valid is driven low when there is stall if PA is present
//--------------------------------------------------


//*********************************
//   IH_TE_WR_VALID
//*********************************

//------------------------------------
// wr request from core results in a write command to TE in the next clock
// Same as above, but retry is checked in the clock in which the command came in also
// This is to make sure that we are checking for case where there are no commands stored in IH input fifo
// New assertions have to written to cover cases where commands are stored in IH input fifo
//------------------------------------
    // assign ih_te_ie_wr_type = IE_WR_TYPE_WD_E if MEMC_INLINE_ECC=0 for MEMC_IH_TE_PIPELINE=1 case
     
    
    assert_wr_valid_with_no_retry_nonie : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                   ((hif_cmd_valid && (hif_cmd_type == `MEMC_CMD_TYPE_BLK_WR) && !hif_cmd_stall && !te_ih_core_in_stall && !wu_ih_flow_cntrl_req && !reg_ddrc_ecc_type) ##1 
                                   (!te_ih_core_in_stall && !wu_ih_flow_cntrl_req)) |->
                                   (ih_te_wr_valid && !ih_te_rd_valid));

     property wr_valid_nof_nof;
             @(posedge co_ih_clk) disable iff(~core_ddrc_rstn)
                     ((hif_cmd_valid && (hif_cmd_type == `MEMC_CMD_TYPE_BLK_WR) && !hif_cmd_stall && input_fifo_empty && reg_ddrc_ecc_type) ##1
                     (!te_ih_core_in_stall) [->1]
                     |-> (ih_te_fifo_empty) ##1 (!te_ih_retry && !wu_ih_flow_cntrl_req) [->1]
                     |-> (ih_te_wr_valid && !ih_te_rd_valid && (ih_te_ie_wr_type!=`IE_WR_TYPE_WE_BW)));
     endproperty
     assert_wr_valid_nof_nof: assert property(wr_valid_nof_nof);
    
     property wr_valid_f_nof;
             @(posedge co_ih_clk) disable iff(~core_ddrc_rstn)
                     ((hif_cmd_valid && (hif_cmd_type ==`MEMC_CMD_TYPE_BLK_WR) && !hif_cmd_stall && !input_fifo_empty && reg_ddrc_ecc_type) |->
                     (!te_ih_core_in_stall) [->2]
                     |-> (ih_te_fifo_empty) ##1 (!te_ih_retry && !wu_ih_flow_cntrl_req) [->1]
                     |-> (ih_te_wr_valid && !ih_te_rd_valid && (ih_te_ie_wr_type!=`IE_WR_TYPE_WE_BW)));
     endproperty                        
     assert_wr_valid_f_nof: assert property(wr_valid_f_nof); 
    
     property wr_valid_nof_f; 
             @(posedge co_ih_clk) disable iff(~core_ddrc_rstn)
                     ((hif_cmd_valid && (hif_cmd_type ==`MEMC_CMD_TYPE_BLK_WR) && !hif_cmd_stall && input_fifo_empty  && reg_ddrc_ecc_type) ##1
                     (!te_ih_core_in_stall) [->1]
                     |-> (!ih_te_fifo_empty) |-> (!te_ih_retry && ((ih_te_wr_valid && ih_te_ie_wr_type==`IE_WR_TYPE_WE_BW) || !wu_ih_flow_cntrl_req)) [->2]
                     |-> (ih_te_wr_valid && !ih_te_rd_valid && (ih_te_ie_wr_type!=`IE_WR_TYPE_WE_BW)));
     endproperty
     assert_wr_valid_nof_f: assert property(wr_valid_nof_f);
    
     property wr_valid_f_f;
             @(posedge co_ih_clk) disable iff(~core_ddrc_rstn)
                     ((hif_cmd_valid && (hif_cmd_type == `MEMC_CMD_TYPE_BLK_WR) && !hif_cmd_stall  && !input_fifo_empty && reg_ddrc_ecc_type) |->
                     (!te_ih_core_in_stall) [->2]
                     |-> (!ih_te_fifo_empty) |-> (!te_ih_retry && ((ih_te_wr_valid && ih_te_ie_wr_type==`IE_WR_TYPE_WE_BW) || !wu_ih_flow_cntrl_req)) [->2]
                     |-> (ih_te_wr_valid && !ih_te_rd_valid && (ih_te_ie_wr_type!=`IE_WR_TYPE_WE_BW)));
     endproperty
     assert_wr_valid_f_f: assert property(wr_valid_f_f);



// Auxillary code for wr_valid
reg     [3:0]   wr_req_counter;
wire            wr_req_incr;
wire            wr_req_decr;

assign  wr_req_incr = hif_cmd_valid && (hif_cmd_type == `MEMC_CMD_TYPE_BLK_WR) && !hif_cmd_stall;

assign  wr_req_decr = ih_te_wr_valid && !ih_te_rd_valid && !te_ih_retry_i;
                       
always @ (posedge co_ih_clk) begin
   if(!core_ddrc_rstn) begin
     wr_req_counter <= 0;
   end
   else begin
      case({wr_req_decr,wr_req_incr})
        2'b00 : wr_req_counter <= wr_req_counter; 
        2'b01 : wr_req_counter <= wr_req_counter + 1'b1;
        2'b10 : wr_req_counter <= wr_req_counter - 1'b1;
        2'b11 : wr_req_counter <= wr_req_counter;
      endcase
   end
end


//------------------------------------
// wr_valid to TE accounted for
//------------------------------------
assert_wr_valid_accounted : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn) 
          (ih_te_wr_valid && !ih_te_rd_valid && !te_ih_retry_i) |-> 
          (wr_req_counter> 0));


//------------------------------------
// Entry N cannot be granted unless N has been freed
//------------------------------------

property p_wr_entry_N_legal;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn)
              (ih_te_wr_valid) |-> ~wr_entry_in_te[ih_te_wr_entry];
//[RUI] Why not add te_ih_retry as pre-condition???, such as below
// Inline ECC has the assertion failure, suggest changed as belwo.
//              (ih_te_wr_valid && ~te_ih_retry) |-> ~wr_entry_in_te[ih_te_wr_entry];
endproperty

assert_wr_entry_N_legal: assert property (p_wr_entry_N_legal);




//*********************************
//   IH_TE_RD_VALID
//*********************************

/////////////
// Auxillary code for rd_valid
/////////////
reg     [3:0]   rd_req_counter;
wire            rd_req_incr;
wire            rd_req_decr;

assign  rd_req_incr = hif_cmd_valid && (hif_cmd_type == `MEMC_CMD_TYPE_BLK_RD) && !hif_cmd_stall;

assign  rd_req_decr = ih_te_rd_valid && !ih_te_wr_valid && !te_ih_retry_i;

always @ (posedge co_ih_clk) begin
   if(!core_ddrc_rstn) begin
     rd_req_counter <= 0;
   end
   else begin
      case({rd_req_decr,rd_req_incr})
        2'b00 : rd_req_counter <= rd_req_counter;
        2'b01 : rd_req_counter <= rd_req_counter + 1'b1;
        2'b10 : rd_req_counter <= rd_req_counter - 1'b1;
        2'b11 : rd_req_counter <= rd_req_counter;
      endcase
   end
end


//------------------------------------
// rd_valid to TE accounted for
//------------------------------------
assert_rd_valid_accounted : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
               (ih_te_rd_valid && !ih_te_wr_valid && !te_ih_retry_i ) 
               |-> 
                    (rd_req_counter> 0));
                        

/////////////
// Auxillary code for RMW
/////////////
reg     [3:0]   rmw_req_counter;
wire            rmw_req_incr;
wire            rmw_req_decr;


assign  rmw_req_incr = hif_cmd_valid 
                            && (hif_cmd_type == `MEMC_CMD_TYPE_RMW)
                            && !hif_cmd_stall;

assign  rmw_req_decr = ih_te_rd_valid && ih_te_wr_valid && !te_ih_retry_i && ih_te_rmwtype!=2'b11;

always @ (posedge co_ih_clk) begin
   if(!core_ddrc_rstn) begin
     rmw_req_counter <= 0;
   end
   else begin
      case({rmw_req_decr,rmw_req_incr})
        2'b00 : rmw_req_counter <= rmw_req_counter;
        2'b01 : rmw_req_counter <= rmw_req_counter + 1'b1;
        2'b10 : rmw_req_counter <= rmw_req_counter - 1'b1;
        2'b11 : rmw_req_counter <= rmw_req_counter;
      endcase
   end
end


//------------------------------------
// rmw_valid to TE accounted for
//------------------------------------
assert_rmw_valid_accounted : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
               (ih_te_rd_valid && ih_te_wr_valid && !te_ih_retry_i && (ih_te_rmwtype!=2'b11)) |-> 
                    (rmw_req_counter> 0));


//------------------------------------
// Entry N cannot be granted unless N has been freed
//------------------------------------

property p_rd_entry_N_legal;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn)
              (ih_te_rd_valid) |-> ~rd_entry_in_te[ih_te_rd_entry];
endproperty

assert_rd_entry_N_legal: assert property (p_rd_entry_N_legal);

//*********************************
//   IH_TE_RMW_TYPE
//*********************************

// `ifdef MEMC_SIDEBAND_ECC
// //------------------------------------
// // If scrub, then rmwtype should be 2'b10
// //------------------------------------
// `ifndef UMCTL2_DUAL_HIF_1
// assert_rmw_type_scrub_legal : assert property (@ (posedge co_ih_clk)  disable iff (~core_ddrc_rstn)
//                                 (ih_te_rd_valid && ih_te_wr_valid) |-> ((ih_te_rmwtype == 2'b10) || (ih_te_rmwtype == 2'b00)));
// `endif // UMCTL2_DUAL_HIF_1
// `endif //MEMC_SIDEBAND_ECC

assert_rmw_type_other : assert property (@ (posedge co_ih_clk)  disable iff (~core_ddrc_rstn)
                                (ih_te_rd_valid ^ ih_te_wr_valid)|-> (ih_te_rmwtype == 2'b11));





//*********************************
//   IH_TE_BLOCK_RD
//*********************************


//*********************************
// Check for ih_te_rank
// Check for ih_te_bankgroup
// Check for ih_te_bank
// Check for ih_te_page
// Check for ih_te_col
// Check for ih_te_dword
//*********************************


//*********************************
//   hif_CREDITS
//*********************************


//------------------------------------
// High level property
// If credits available, then all wr_entries in CAM should not be used
//------------------------------------

//don't check during retry_stage because credit avail is not correct during retry_stage.
property p_wr_cam_oversubscription;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn)
        (wr_credits_avail > 0) |-> (wr_entry_in_te != {WR_CAM_DEPTH{1'b1}});
endproperty

assert_wr_cam_oversubscription: assert property (p_wr_cam_oversubscription);


property p_rd_cam_oversubscription;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn)
        ((lpr_credits_avail > 0) || (hpr_credits_avail > 0))  |-> (rd_entry_in_te != {RD_CAM_DEPTH{1'b1}});
endproperty

assert_rd_cam_oversubscription: assert property (p_rd_cam_oversubscription);



//------------------------------------
// if free entry match prefer, then credit issued exactly in the second clock after free arrived
//------------------------------------

assert_in_order_wr_free_credit_2clks : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                        (mr_ih_free_wr_entry_valid && (mr_ih_free_wr_entry <= {WRCMD_ENTRY_BITS{1'b1}}) &&
                                           (mr_ih_free_wr_entry == wr_oldest_radd)) |-> ##2 hif_wr_credit);

assert_in_order_lpr_free_credit_2clks : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                        (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry <= dh_ih_lpr_num_entries) &&
                                           (te_ih_free_rd_entry == ih_te_lo_rd_prefer) |-> ##2 hif_lpr_credit[0]));

assert_in_order_hpr_free_credit_2clks : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                        (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry > dh_ih_lpr_num_entries) &&
                                           (te_ih_free_rd_entry == ih_te_hi_rd_prefer) |-> ##2 hif_hpr_credit[0]));



// //------------------------------------
// // if free entry is received for scrubs, no credit is issued to the core
// // TRIGGER WILL FAIL UNTIL SCRUBS ARE TURNED ON
// // FIXME: Is this true? Can the credits os previous free entry request come in the cycles given below?
// //------------------------------------
// 
// `ifdef MEMC_SIDEBAND_ECC
// 
// /*
// 
// assert_wr_free_scrub_and_no_wr_credit_NEG : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
//                                            (mr_ih_free_wr_entry_valid && (mr_ih_free_wr_entry == {WRCMD_ENTRY_BITS{1'b1}})) |->
//                                                 ##2 !hif_wr_credit);
// 
// assert_rd_free_scrub_and_no_lpr_credit_NEG : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
//                                           (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry == dh_ih_lpr_num_entries)) |->
//                                                 ##2 !hif_lpr_credit);
// 
// `ifndef MEMC_NO_PRIORITY
// assert_rd_free_scrub_and_no_hpr_credit_NEG : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
//                                           (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry == dh_ih_lpr_num_entries)) |->
//                                                 ##2 !hif_hpr_credit);
// `endif  // NO_PRIORITY
// 
// */
// 
// `endif //MEMC_SIDEBAND_ECC

//------------------------------------
// if free entry doesn't match prefer, then no credits issued during the next 2 clocks
// FIXME: This is put as NEG because, I'm not sure if credits due to previous free's can interfere
// YES, CREDITS DUE TO PREVIOUS REQUESTS CAN INTERFERE - looks at the failed example waveform
//------------------------------------

/*

assert_out_of_order_wr_free_no_credit_NEG : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                                (mr_ih_free_wr_entry_valid && (mr_ih_free_wr_entry < {WRCMD_ENTRY_BITS{1'b1}}) &&
                                                    (mr_ih_free_wr_entry != wr_oldest_radd)) |-> (!hif_wr_credit[*2]));

assert_out_of_order_lpr_free_no_credit_NEG : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                                (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry < dh_ih_lpr_num_entries) &&
                                                   (te_ih_free_rd_entry != ih_te_lo_rd_prefer) |-> (!hif_lpr_credit[*2])));


`ifndef MEMC_NO_PRIORITY
assert_out_of_order_hpr_free_no_credit_NEG : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                                (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry > dh_ih_lpr_num_entries) &&
                                                  (te_ih_free_rd_entry != ih_te_hi_rd_prefer) |-> (!hif_hpr_credit[*2])));
`endif  // NO_PRIORITY

*/

//------------------------------------
// If N out of order free, followed by 1 in-order free, expect N+1 credits
// This is an example for 2 out of order, followed by an in-order, causing 3 credits to be issued (LPR)
//------------------------------------

/*

assert_out_of_order_lpr_free_credit_expect : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
                                                ((te_ih_free_rd_entry_valid && (te_ih_free_rd_entry < dh_ih_lpr_num_entries) &&
                                                   (te_ih_free_rd_entry != ih_te_lo_rd_prefer)) ##1 !te_ih_free_rd_entry_valid[*0:$]) [*2] ##1
                                                        (te_ih_free_rd_entry_valid && (te_ih_free_rd_entry < dh_ih_lpr_num_entries) &&
                                                            (te_ih_free_rd_entry == ih_te_lo_rd_prefer)) |-> ##2 hif_lpr_credit[*3]);
*/


//*********************************
//   hif_wdata_PTR_VALID
//*********************************

//------------------------------------
// FIXME: give a decription for the assertion
//------------------------------------

// note use of hif_cmd_stall_orig, not hif_cmd_stall
// This was original hif_cmd_stall before ability to stall core interface
// for Self Refresh was introduced
// safe to change it as hif_wdata_ptr_valid is not actually related to
// hif_cmd_stall, but was using info in hif_cmd_stall to know if ok
//assert_corrupt_wdata_ptr_valid  : assert property (@ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
//            hif_wdata_ptr_valid |-> (~hif_cmd_stall_orig && ~($past(te_ih_retry)) && $past(ih_te_wr_valid)))
//           else $error ("%m @ %t wdata_ptr_valid from IH to Core is corrupt.", $time);

/// any ECCAP signal must be 0 with feature disabled 
property p_eccap_zero_with_disable_eccap;
        @(posedge co_ih_clk) disable iff (~core_ddrc_rstn)
        (reg_ddrc_ecc_ap_en==0) |-> (ih_te_rd_eccap==0 && ih_te_wr_eccap==0);
endproperty

a_eccap_zero_with_disable_eccap: assert property (p_eccap_zero_with_disable_eccap) else $error("%m @ %t ih_te_rd_eccap or ih_te_wr_eccap is non zero value with reg_ddrc_ecc_ap_en==0",$time);




endmodule
`endif // `ifndef SYNTHESIS
`endif // SNPS_ASSERT_ON
