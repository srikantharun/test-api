//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_ie_blk_chn_table.sv#3 $
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
//                              DDR Controller
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//                              Description
//
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module ih_ie_blk_chn_table
import DWC_ddrctl_reg_pkg::*;
#(
    parameter NO_OF_BLK_CHN         = 16
   ,parameter BLK_CHN_BITS          = 4
   ,parameter IE_BURST_NUM_BITS     = 5
   ,parameter BT_BITS               = 4
   ,parameter BWT_BITS              = 4
   ,parameter BRT_BITS              = 4
   ,parameter IE_RD_TYPE_BITS       = 2
   ,parameter IE_WR_TYPE_BITS       = 2
   ,parameter CMD_TYPE_BITS         = 2
   ,parameter CMD_LEN_BITS          = 2
   ,parameter IH_TAG_WIDTH          = 2
   ,parameter RMW_TYPE_BITS         = 2
   ,parameter WRDATA_CYCLES         = `MEMC_WRDATA_CYCLES 
   ,parameter MWR_BITS              = `DDRCTL_MWR_BITS
   ,parameter UMCTL2_LRANK_BITS     = `UMCTL2_LRANK_BITS
   ,parameter MEMC_BG_BANK_BITS     = `MEMC_BG_BANK_BITS
   ,parameter MEMC_BLK_BITS         = `MEMC_BLK_BITS
   ,parameter MEMC_PAGE_BITS        = `MEMC_PAGE_BITS
   ,parameter MEMC_WORD_BITS        = `MEMC_WORD_BITS
   ,parameter ECC_ADDR_WIDTH        = 
                                       UMCTL2_LRANK_BITS +
                                       2 +    //MSB of critical_dword
                                       MEMC_BG_BANK_BITS + MEMC_BLK_BITS + MEMC_WORD_BITS

)
(  
    input                              core_ddrc_core_clk
   ,input                              core_ddrc_rstn
   ,input                              ddrc_cg_en
   ,input  [BLK_CHANNEL_IDLE_TIME_X32_WIDTH-1:0]                       reg_ddrc_blk_channel_idle_time_x32
   ,input  [4:0]                       reg_ddrc_active_blk_channel
   ,input                              reg_ddrc_blk_channel_active_term
   ,input  [BURST_RDWR_WIDTH-1:0]      reg_ddrc_burst_rdwr
   ,input                              dh_ih_dis_hif             // disable (stall) hif
   ,input                              gsfsm_sr_co_if_stall
   ,input [SELFREF_SW_WIDTH-1:0]       reg_ddrc_selfref_sw
   ,input                              mpsm_en_int
   ,input                              input_fifo_empty
   //te_ih 
   ,input                              te_ih_retry
   //incomming command
   ,input [ECC_ADDR_WIDTH-1:0]         rxcmd_ecc_addr
   ,input [1:0]                        rxcmd_pri     //1: HPR; 0: LPR/VPR
   ,input [CMD_TYPE_BITS-1:0]          rxcmd_type
   ,input                              rxcmd_ptc_vld //protected region to this channel

   //for accumulate wrdata in one block.
   ,input   [WRDATA_CYCLES-1:0]        wdata_mask_full
   ,input   [IE_BURST_NUM_BITS-1:0]    ie_burst_num

   //channel information
   ,input                              ecc_hole_access

   ,input   [ BT_BITS-1:0]             alloc_bt
   ,input   [BWT_BITS-1:0]             alloc_bwt
   ,input   [BRT_BITS-1:0]             alloc_brt

   ,input                              re_done_i
   ,input   [BT_BITS-1:0]              re_done_bt
   ,input                              ie_wr_vld
   //output
   ,output                             chn_vld
   ,output                             hif_lpr_credit_ie
   ,output                             hif_hpr_credit_ie
   ,output                             te_ih_retry_ie_cmd
   ,output                             ie_cmd_active
   ,output                             ie_rd_vld
   ,output  [IE_RD_TYPE_BITS-1:0]      ie_rd_type
   ,output  [IE_WR_TYPE_BITS-1:0]      ie_wr_type

   ,output  [CMD_LEN_BITS-1:0]         ie_rd_length // <- full
   ,output  [IH_TAG_WIDTH-1:0]         ie_rd_tag    // <- 0;
   ,output  [RMW_TYPE_BITS-1:0]        ie_rmwtype 
   ,output  [1:0]                      ie_hi_pri
   ,output  [BT_BITS-1:0]              ie_bt
   ,output  [BWT_BITS-1:0]             ie_cmd_bwt
   ,output  [UMCTL2_LRANK_BITS-1:0]    ie_rank_num
   ,output  [MEMC_BG_BANK_BITS-1:0]    ie_bg_bank_num
   ,output  [MEMC_BLK_BITS-1:0]        ie_block_num
   ,output  [MEMC_PAGE_BITS-1:0]       ie_page_num
   ,output  [MEMC_WORD_BITS-1:0]       ie_critical_dword
   ,output  [MWR_BITS-1:0]             is_mwr

   ,output                             alloc_bt_vld
   ,output                             alloc_bwt_vld
   ,output                             alloc_brt_vld
   ,output                             ie_wr_cnt_inc
   ,output                             ie_rd_cnt_inc
   ,output  [BWT_BITS-1:0]             ie_bwt
   ,output  [BRT_BITS-1:0]             ie_brt
   ,output                             ie_bwt_vld
   ,output                             ie_brt_vld
   ,output  [BT_BITS-1:0]              ie_blk_end_bt
   ,output                             ie_blk_end
   ,output                             ie_blk_rd_end
   ,output                             ie_blk_wr_end
   ,output                             flush_req      //flush_req will assert ddrc_cg_en
);

//------------------------------ LOCAL PARAMETERS ------------------------------------
//   to fix a VCS compile issue
localparam  UMCTL2_LRANK_BITS_EXT  = UMCTL2_LRANK_BITS==0 ? 1 : UMCTL2_LRANK_BITS;

reg [BLK_CHN_BITS-1:0]        next_chn_num;
reg [NO_OF_BLK_CHN-1:0]       next_chn_bit;

wire [NO_OF_BLK_CHN-1:0]      chn_vld_vct;
wire [NO_OF_BLK_CHN-1:0]      matched_vct;
wire                          override;
wire [NO_OF_BLK_CHN-1:0]      flush_req_vct;
wire [NO_OF_BLK_CHN-1:0]      flush_done_vct;

wire [NO_OF_BLK_CHN-1:0]      te_ih_retry_ie_cmd_vct_unused;
wire [NO_OF_BLK_CHN-1:0]      ie_cmd_active_vct;
wire [NO_OF_BLK_CHN-1:0]      ie_rd_vld_vct;
wire [NO_OF_BLK_CHN*IE_RD_TYPE_BITS-1:0]  ie_rd_type_vct;
wire [NO_OF_BLK_CHN*IE_WR_TYPE_BITS-1:0]  ie_wr_type_vct;

wire [NO_OF_BLK_CHN*CMD_LEN_BITS-1:0]     ie_rd_length_vct;
wire [NO_OF_BLK_CHN*RMW_TYPE_BITS-1:0]    ie_rmwtype_vct;
wire [NO_OF_BLK_CHN*2-1:0]                ie_hi_pri_vct;

wire [NO_OF_BLK_CHN*UMCTL2_LRANK_BITS_EXT-1:0] ie_rank_num_vct;
wire [NO_OF_BLK_CHN*MEMC_BG_BANK_BITS-1:0] ie_bg_bank_num_vct;
wire [NO_OF_BLK_CHN*MEMC_BLK_BITS-1:0]     ie_block_num_vct;
wire [NO_OF_BLK_CHN*MEMC_PAGE_BITS-1:0]    ie_page_num_vct;
wire [NO_OF_BLK_CHN*MEMC_WORD_BITS-1:0]    ie_critical_dword_vct;
wire [NO_OF_BLK_CHN*MWR_BITS-1:0]          is_mwr_vct;
wire [NO_OF_BLK_CHN*BT_BITS-1:0]           ie_bt_vct;
wire [NO_OF_BLK_CHN*BWT_BITS-1:0]          ie_cmd_bwt_vct;

wire [NO_OF_BLK_CHN-1:0]            alloc_bt_vld_vct;
wire [NO_OF_BLK_CHN-1:0]            alloc_bwt_vld_vct;
wire [NO_OF_BLK_CHN-1:0]            alloc_brt_vld_vct;
wire [NO_OF_BLK_CHN-1:0]            ie_wr_cnt_inc_vct;
wire [NO_OF_BLK_CHN-1:0]            ie_rd_cnt_inc_vct;
wire [NO_OF_BLK_CHN*BWT_BITS-1:0]   ie_bwt_vct;
wire [NO_OF_BLK_CHN*BRT_BITS-1:0]   ie_brt_vct;
wire [NO_OF_BLK_CHN-1:0]            ie_bwt_vld_vct;
wire [NO_OF_BLK_CHN-1:0]            ie_brt_vld_vct;
wire [NO_OF_BLK_CHN-1:0]            ie_blk_end_vct;
wire [NO_OF_BLK_CHN-1:0]            ie_blk_rd_end_vct;
wire [NO_OF_BLK_CHN-1:0]            ie_blk_wr_end_vct;
wire [NO_OF_BLK_CHN-1:0]            hif_lpr_credit_ie_vct;
wire [NO_OF_BLK_CHN-1:0]            hif_hpr_credit_ie_vct;

wire [NO_OF_BLK_CHN*BT_BITS-1:0]   ie_blk_end_bt_vct;

reg  [NO_OF_BLK_CHN-1:0]           rxcmd_ptc_vld_vct;
reg  [BLK_CHN_BITS-1:0]            flush_cnt;
wire                               flush_trigger;
wire                               flush_done;
reg  [4:0] cnt_for_32;
reg  [$bits(reg_ddrc_blk_channel_idle_time_x32)-1:0] cnt_blk_idle_x32;
reg        flush_by_timeout;
wire       flush_timeout;
wire       flush_by_req;
wire       flush_by_ecc_hole;

wire [NO_OF_BLK_CHN-1:0]              sel_chn;
wire [NO_OF_BLK_CHN*IH_TAG_WIDTH-1:0] ie_rd_tag_unused;

integer i;
genvar  idx;
//------------------------------------------------------------------
//  next channel point (next_chn)
//------------------------------------------------------------------

reg  [NO_OF_BLK_CHN-1:0]  chn_idle_vct;
always @ (*) begin
   for(i=0; i<NO_OF_BLK_CHN; i=i+1)
      if(i<=reg_ddrc_active_blk_channel)
         chn_idle_vct[i] = ~chn_vld_vct[i];
      else
         chn_idle_vct[i] = 1'b0;
end

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      next_chn_num <= {(BLK_CHN_BITS-1){1'b0}};
      next_chn_bit <= {{(NO_OF_BLK_CHN-2){1'b0}}, 1'b1};
   end else if(ddrc_cg_en) begin
      if( (~|matched_vct & ~|chn_idle_vct & rxcmd_ptc_vld & ~te_ih_retry) | (flush_req & flush_done)) begin   //move pointer to next chn if incoming command override a valid channel or is flushing, 
         if(next_chn_num == reg_ddrc_active_blk_channel[BLK_CHN_BITS-1:0] ) begin
            next_chn_num <= {(BLK_CHN_BITS-1){1'b0}};
            next_chn_bit <= {{(NO_OF_BLK_CHN-2){1'b0}}, 1'b1};
         end else begin
            next_chn_num <= next_chn_num + 1'b1;
            next_chn_bit <= {next_chn_bit[NO_OF_BLK_CHN-2:0], next_chn_bit[NO_OF_BLK_CHN-1]};
         end
      end
   end
end

assign override   = ~|matched_vct;  //no any matched will cause overrite

//assign sel_chn    = |matched_vct ? matched_vct : next_chn_bit;

//----------------------------------------------------------
// Flush logic
// 1) dis_hif and no command to trigger flush all the channels
//   step1: waiting NO command in Input FIFO
//   step2: flush channels one by one (start from next_chn, untill all the channel is flushed - use a counter)
//   step3: assert flush done when all the channel is flushed.
//----------------------------------------------------------
// use register version to trigger flush to break the combo logic loop
// dont use ddrc_cg_en since gsfsm_sr_co_if_stall could be changed regardless ddrc_cg_en.
reg gsfsm_sr_co_if_stall_r;
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      gsfsm_sr_co_if_stall_r <= 1'b0;
   end else begin
      gsfsm_sr_co_if_stall_r <= gsfsm_sr_co_if_stall;
   end
end


assign flush_by_req     = mpsm_en_int | 
                          dh_ih_dis_hif | 
                          gsfsm_sr_co_if_stall_r | 
                          reg_ddrc_selfref_sw;

assign flush_by_ecc_hole = ecc_hole_access;

assign flush_trigger    = flush_by_req | flush_by_timeout | flush_by_ecc_hole;

// flush_req is a lower priority than rxcmd.
// but if flush_req is by ecc_hole access, all the channels must be flushed before send the ECC hole command
assign flush_req        = flush_trigger & chn_vld & ~ie_wr_vld & (flush_by_ecc_hole | input_fifo_empty);

assign chn_vld        = |chn_vld_vct;

assign flush_req_vct = flush_req ? next_chn_bit : {NO_OF_BLK_CHN{1'b0}};

//-------------------------------------------------------
// flush condition by block idle timeout
// the timer is counting when no access to protected region
// if incoming command is to protected region, stop flush regardless if all the channel are flushed
// if incoming command is to unprotected region, pause flush, make unprotected region has a high priority, and then continue flush after input fifo empty


always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      cnt_for_32 <= {5{1'b0}};
   end else begin //Note: this counter don't need ddrc_cg_en because it is counting the idle time.
      //three condition will cause counter stop
      //command to protected region
      //timeout
      //blk_channel_idle_time_x32==0, indicate flush by timeout
      if(rxcmd_ptc_vld | flush_timeout | ~chn_vld | (~|reg_ddrc_blk_channel_idle_time_x32)) begin   
         cnt_for_32 <= {5{1'b0}};
      end else begin //no command to  protected region
         cnt_for_32 <= cnt_for_32 + 1'b1;
      end
   end
end

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      cnt_blk_idle_x32 <= {6{1'b0}};
   end else begin //Note: this counter don't need ddrc_cg_en because it is counting the idle time.
      if(rxcmd_ptc_vld | flush_timeout) begin   
         cnt_blk_idle_x32 <= {6{1'b0}};
      end else if(&cnt_for_32) begin //no protected region
         cnt_blk_idle_x32 <= cnt_blk_idle_x32 + 1'b1;
      end
   end
end

assign flush_timeout = (cnt_blk_idle_x32 == reg_ddrc_blk_channel_idle_time_x32) & (&cnt_for_32);

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      flush_by_timeout <= 1'b0;
   end else begin //Note this logic for flush_by_timeout don't need ddrc_cg_en because it could be happen when DDRC is IDLE
      if(~chn_vld | rxcmd_ptc_vld) begin
         flush_by_timeout <= 1'b0;
      end else if(flush_timeout) begin   
         flush_by_timeout <= 1'b1;
      end
   end
end
//--------------------------------------------------------------
// instantiate number of blkd_chn_item
//-------------------------------------------------------------
generate
   for(idx=0; idx<NO_OF_BLK_CHN; idx=idx+1) begin: blk_chn_item_gen
      ih_ie_blk_chn_item
      
      #(
          .CHN_ID                (idx                 )
         ,.ECC_ADDR_WIDTH        (ECC_ADDR_WIDTH      )
         ,.IE_BURST_NUM_BITS     (IE_BURST_NUM_BITS   )
         ,.BT_BITS               (BT_BITS             )
         ,.BWT_BITS              (BWT_BITS            )
         ,.BRT_BITS              (BRT_BITS            )
         ,.IE_RD_TYPE_BITS       (IE_RD_TYPE_BITS     )
         ,.IE_WR_TYPE_BITS       (IE_WR_TYPE_BITS     )
         ,.CMD_LEN_BITS          (CMD_LEN_BITS        )
         ,.IH_TAG_WIDTH          (IH_TAG_WIDTH        )
         ,.RMW_TYPE_BITS         (RMW_TYPE_BITS       )
         ,.WRDATA_CYCLES         (WRDATA_CYCLES       )
         ,.MWR_BITS              (MWR_BITS            )
         ,.UMCTL2_LRANK_BITS     (UMCTL2_LRANK_BITS_EXT)
         ,.MEMC_BG_BANK_BITS     (MEMC_BG_BANK_BITS)
         ,.MEMC_BLK_BITS         (MEMC_BLK_BITS)
         ,.MEMC_PAGE_BITS        (MEMC_PAGE_BITS)
         ,.MEMC_WORD_BITS        (MEMC_WORD_BITS)
      ) blk_chn_item
      (  
          .core_ddrc_core_clk    (core_ddrc_core_clk)
         ,.core_ddrc_rstn        (core_ddrc_rstn)
         ,.ddrc_cg_en            (ddrc_cg_en)
         ,.reg_ddrc_blk_channel_active_term (reg_ddrc_blk_channel_active_term)
         ,.reg_ddrc_burst_rdwr   (reg_ddrc_burst_rdwr)
         //te_ih 
         ,.te_ih_retry           (te_ih_retry)
         //incomming command
         ,.rxcmd_ecc_addr        (rxcmd_ecc_addr)
         ,.rxcmd_pri             (rxcmd_pri)
         ,.rxcmd_type            (rxcmd_type)
         ,.rxcmd_ptc_vld         (rxcmd_ptc_vld_vct[idx])
      
         //for accumulate wrdata in one block.
         ,.wdata_mask_full       (wdata_mask_full)
         ,.ie_burst_num          (ie_burst_num)
      
         //channel information
         ,.override              (override)
         ,.flush_req             (flush_req_vct[idx])
         ,.flush_done            (flush_done_vct[idx])
      
         ,.alloc_bt              (alloc_bt)
         ,.alloc_bwt             (alloc_bwt)
         ,.alloc_brt             (alloc_brt)

         ,.re_done_i             (re_done_i)
         ,.re_done_bt            (re_done_bt)
         ,.ie_wr_vld             (ie_wr_vld)

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(idx * IE_RD_TYPE_BITS)' found in module 'ih_ie_blk_chn_table'
//SJ: This coding style is acceptable and there is no plan to change it.

         //output
         ,.chn_vld               (chn_vld_vct[idx])
         ,.matched               (matched_vct[idx])
         ,.te_ih_retry_ie_cmd    (te_ih_retry_ie_cmd_vct_unused[idx])
         ,.ie_cmd_active         (ie_cmd_active_vct[idx])
         ,.ie_rd_vld             (ie_rd_vld_vct[idx])
         ,.ie_rd_type            (ie_rd_type_vct[idx*IE_RD_TYPE_BITS+:IE_RD_TYPE_BITS])
         ,.ie_wr_type            (ie_wr_type_vct[idx*IE_WR_TYPE_BITS+:IE_WR_TYPE_BITS])
      
         ,.ie_rd_length          (ie_rd_length_vct[idx*CMD_LEN_BITS+:CMD_LEN_BITS])
         ,.ie_rd_tag             (ie_rd_tag_unused[idx*IH_TAG_WIDTH+:IH_TAG_WIDTH])//it always is 0, don't need mux. (ie_rd_tag_vct[idx]) 
         ,.ie_rmwtype            (ie_rmwtype_vct[idx*RMW_TYPE_BITS+:RMW_TYPE_BITS])
         ,.ie_hi_pri             (ie_hi_pri_vct[idx*2+:2])
         ,.ie_bt                 (ie_bt_vct[idx*BT_BITS+:BT_BITS])
         ,.ie_cmd_bwt            (ie_cmd_bwt_vct[idx*BWT_BITS+:BWT_BITS])
         ,.ie_rank_num           (ie_rank_num_vct[idx*UMCTL2_LRANK_BITS_EXT+:UMCTL2_LRANK_BITS_EXT])
         ,.ie_bg_bank_num        (ie_bg_bank_num_vct[idx*MEMC_BG_BANK_BITS+:MEMC_BG_BANK_BITS])
         ,.ie_block_num          (ie_block_num_vct[idx*MEMC_BLK_BITS+:MEMC_BLK_BITS])
         ,.ie_page_num           (ie_page_num_vct[idx*MEMC_PAGE_BITS+:MEMC_PAGE_BITS])
         ,.ie_critical_dword     (ie_critical_dword_vct[idx*MEMC_WORD_BITS+:MEMC_WORD_BITS])
         ,.is_mwr                (is_mwr_vct[idx*MWR_BITS+:MWR_BITS])
      
         ,.alloc_bt_vld          (alloc_bt_vld_vct[idx])
         ,.alloc_bwt_vld         (alloc_bwt_vld_vct[idx])
         ,.alloc_brt_vld         (alloc_brt_vld_vct[idx])
         ,.ie_wr_cnt_inc         (ie_wr_cnt_inc_vct[idx])
         ,.ie_rd_cnt_inc         (ie_rd_cnt_inc_vct[idx])
         ,.ie_bwt                (ie_bwt_vct[idx*BWT_BITS+:BWT_BITS])
         ,.ie_brt                (ie_brt_vct[idx*BRT_BITS+:BRT_BITS])
         ,.ie_blk_end_bt         (ie_blk_end_bt_vct[idx*BT_BITS+:BT_BITS])
         ,.ie_bwt_vld            (ie_bwt_vld_vct[idx])
         ,.ie_brt_vld            (ie_brt_vld_vct[idx])
         ,.ie_blk_end            (ie_blk_end_vct[idx])
         ,.ie_blk_rd_end         (ie_blk_rd_end_vct[idx])
         ,.ie_blk_wr_end         (ie_blk_wr_end_vct[idx])
         ,.hif_lpr_credit_ie     (hif_lpr_credit_ie_vct[idx])
         ,.hif_hpr_credit_ie     (hif_hpr_credit_ie_vct[idx])
//spyglass enable_block SelfDeterminedExpr-ML
      );
   end
endgenerate

wire [BLK_CHN_BITS-1:0] matched_chn_num;
wire                    matched_chn_num_vld;
wire [BLK_CHN_BITS-1:0] sel_chn_num;
wire                    idle_chn_num_vld;
wire [BLK_CHN_BITS-1:0] idle_chn_num;
wire                    matched_vct_tag_selected_unused;
wire                    idle_vct_tag_selected_unused;
reg  [BLK_CHN_BITS-1:0] sel_chn_num_r;

select_net_lite

#(
   .TAG_BITS(0),
   .NUM_INPUTS (NO_OF_BLK_CHN))
U_matched_vct_selnet 
(
   .clk                   (core_ddrc_core_clk),
   .resetb                (core_ddrc_rstn),
   .tags                  ({NO_OF_BLK_CHN{1'b0}}),
   .vlds                  (matched_vct),
   .wall_next             ({BLK_CHN_BITS{1'b0}}),  //set to 0, becuase it is onehot.
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion
   .selected_vld          (matched_chn_num_vld),  //matched_chn_num_vld is same as |matched_vct;
//spyglass enable_block W528
   .tag_selected          (matched_vct_tag_selected_unused), //not used
   .selected              (matched_chn_num)
);

select_net_lite

#(
   .TAG_BITS(0),
   .NUM_INPUTS (NO_OF_BLK_CHN))
U_idle_vct_selnet 
(
   .clk                   (core_ddrc_core_clk),
   .resetb                (core_ddrc_rstn),
   .tags                  ({NO_OF_BLK_CHN{1'b0}}),
   .vlds                  (chn_idle_vct),
   .wall_next             ({BLK_CHN_BITS{1'b0}}),  //set to 0 to select a idle channel from 0 to No.BLK_CHN, becuase it select any idle channel is fine, and that don't change next_chn_num.
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion
   .selected_vld          (idle_chn_num_vld),      //idle_chn_num_vld is same as |chn_idle_vct;
//spyglass enable_block W528
   .tag_selected          (idle_vct_tag_selected_unused), //not used
   .selected              (idle_chn_num)
);

// it is not possible that matched_vct==0 when ie_wr_vld=1
assign sel_chn_num = ( (rxcmd_ptc_vld | ie_wr_vld) & |matched_vct) ? matched_chn_num : 
                     ( rxcmd_ptc_vld & |chn_idle_vct) ? idle_chn_num : 
                                                        next_chn_num;

//below signals is registered in blk_chn_item, so the select signals is registered accordingly.
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      sel_chn_num_r <= {(BLK_CHN_BITS-1){1'b0}};
   end else if(ddrc_cg_en) begin
      sel_chn_num_r <= sel_chn_num;
   end
end
//--------------------------------------------------------
// generate rxcmd_ptc_vld for each channel
//
always @ (*)
begin
   for (i=0; i<NO_OF_BLK_CHN; i=i+1)
      if(i==sel_chn_num)
         rxcmd_ptc_vld_vct[i] = rxcmd_ptc_vld;
      else
         rxcmd_ptc_vld_vct[i] = 1'b0;
end

localparam NO_OF_BLK_CHN_POW2 = 2**(BLK_CHN_BITS);
wire [NO_OF_BLK_CHN_POW2*BWT_BITS-1:0]   ie_bwt_vct_tmp;
wire [NO_OF_BLK_CHN_POW2*BRT_BITS-1:0]   ie_brt_vct_tmp;
wire [NO_OF_BLK_CHN_POW2*BT_BITS-1:0]    ie_bt_vct_tmp;
wire [NO_OF_BLK_CHN_POW2*BT_BITS-1:0]    ie_blk_end_bt_vct_tmp;
wire [NO_OF_BLK_CHN_POW2*BWT_BITS-1:0]   ie_cmd_bwt_vct_tmp;

generate
  if(NO_OF_BLK_CHN_POW2 == NO_OF_BLK_CHN) begin:NO_OF_BLK_CHN_pow2
assign ie_bwt_vct_tmp        = ie_bwt_vct;
assign ie_brt_vct_tmp        = ie_brt_vct;
assign ie_bt_vct_tmp         = ie_bt_vct;
assign ie_blk_end_bt_vct_tmp = ie_blk_end_bt_vct;
assign ie_cmd_bwt_vct_tmp    = ie_cmd_bwt_vct;
  end else begin:NO_OF_BLK_CHN_pow2
assign ie_bwt_vct_tmp        = {{(NO_OF_BLK_CHN_POW2-NO_OF_BLK_CHN)*BWT_BITS{1'b0}},ie_bwt_vct};
assign ie_brt_vct_tmp        = {{(NO_OF_BLK_CHN_POW2-NO_OF_BLK_CHN)*BRT_BITS{1'b0}},ie_brt_vct};
assign ie_bt_vct_tmp         = {{(NO_OF_BLK_CHN_POW2-NO_OF_BLK_CHN)*BT_BITS{1'b0}},ie_bt_vct};
assign ie_blk_end_bt_vct_tmp = {{(NO_OF_BLK_CHN_POW2-NO_OF_BLK_CHN)*BT_BITS{1'b0}},ie_blk_end_bt_vct};
assign ie_cmd_bwt_vct_tmp    = {{(NO_OF_BLK_CHN_POW2-NO_OF_BLK_CHN)*BT_BITS{1'b0}},ie_cmd_bwt_vct};
  end
endgenerate

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(sel_chn_num * IE_RD_TYPE_BITS)' found in module 'ih_ie_blk_chn_table'
//SJ: This coding style is acceptable and there is no plan to change it.

assign  te_ih_retry_ie_cmd =  te_ih_retry | ie_cmd_active;   //the two methods for te_ih_retry_ie_cmd are same, to see which one has a beter time closure.
assign  ie_cmd_active    =    |ie_cmd_active_vct;
assign  ie_rd_vld        =    |ie_rd_vld_vct;
assign  ie_rd_type       =    ie_rd_type_vct[sel_chn_num*IE_RD_TYPE_BITS+:IE_RD_TYPE_BITS];
assign  ie_wr_type       =    ie_wr_type_vct[sel_chn_num*IE_WR_TYPE_BITS+:IE_WR_TYPE_BITS];
                           
assign  ie_rd_length     =    ie_rd_length_vct[sel_chn_num*CMD_LEN_BITS+:CMD_LEN_BITS];
assign  ie_rd_tag        =    'h0; //it always is 0, don't need mux. (ie_rd_tag_vct[idx]) 
assign  ie_rmwtype       =    ie_rmwtype_vct[sel_chn_num*RMW_TYPE_BITS+:RMW_TYPE_BITS];
assign  ie_hi_pri        =    ie_hi_pri_vct[sel_chn_num*2+:2];
assign  ie_rank_num      =    ie_rank_num_vct[sel_chn_num*UMCTL2_LRANK_BITS_EXT+:UMCTL2_LRANK_BITS_EXT];
assign  ie_bg_bank_num   =    ie_bg_bank_num_vct[sel_chn_num*MEMC_BG_BANK_BITS+:MEMC_BG_BANK_BITS];
assign  ie_block_num     =    ie_block_num_vct[sel_chn_num*MEMC_BLK_BITS+:MEMC_BLK_BITS];
assign  ie_page_num      =    ie_page_num_vct[sel_chn_num*MEMC_PAGE_BITS+:MEMC_PAGE_BITS];
assign  ie_critical_dword =   ie_critical_dword_vct[sel_chn_num*MEMC_WORD_BITS+:MEMC_WORD_BITS];
assign  is_mwr           =    is_mwr_vct[sel_chn_num*MWR_BITS+:MWR_BITS];
assign  ie_bt            =    ie_bt_vct_tmp[sel_chn_num*BT_BITS+:BT_BITS];
assign  ie_cmd_bwt       =    ie_cmd_bwt_vct_tmp[sel_chn_num*BWT_BITS+:BWT_BITS];

assign  hif_lpr_credit_ie =   |hif_lpr_credit_ie_vct;
assign  hif_hpr_credit_ie =   |hif_hpr_credit_ie_vct;

assign flush_done       =     flush_done_vct[sel_chn_num];

assign  alloc_bt_vld     =    |alloc_bt_vld_vct;
assign  alloc_bwt_vld    =    |alloc_bwt_vld_vct;
assign  alloc_brt_vld    =    |alloc_brt_vld_vct;

assign  ie_wr_cnt_inc    =    |ie_wr_cnt_inc_vct;
assign  ie_rd_cnt_inc    =    |ie_rd_cnt_inc_vct;
assign  ie_blk_end       =    |ie_blk_end_vct;
assign  ie_blk_rd_end    =    |ie_blk_rd_end_vct;
assign  ie_blk_wr_end    =    |ie_blk_wr_end_vct;
assign  ie_bwt           =    ie_bwt_vct_tmp[sel_chn_num_r*BWT_BITS+:BWT_BITS];
assign  ie_brt           =    ie_brt_vct_tmp[sel_chn_num_r*BRT_BITS+:BRT_BITS];
assign  ie_blk_end_bt    =    ie_blk_end_bt_vct_tmp[sel_chn_num_r*BT_BITS+:BT_BITS];
assign  ie_bwt_vld       =    ie_bwt_vld_vct[sel_chn_num_r];
assign  ie_brt_vld       =    ie_brt_vld_vct[sel_chn_num_r];
//spyglass enable_block SelfDeterminedExpr-ML

`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON

// coverpoints for channel flush
  covergroup cg_chn_flush @(posedge core_ddrc_core_clk);
     cp_flush_type : coverpoint ({flush_by_req, flush_by_timeout, flush_by_ecc_hole}) iff(core_ddrc_rstn & flush_req & flush_done) {
                 bins          flush_by_req = {3'b100};    
                 bins      flush_by_timeout = {3'b010};    
                 bins     flush_by_ecc_hole = {3'b001};    
     }
     cp_flush_req_type : coverpoint ({mpsm_en_int, dh_ih_dis_hif, gsfsm_sr_co_if_stall_r, reg_ddrc_selfref_sw}) iff(core_ddrc_rstn & flush_req & flush_done) {
               // MPSM is only supported in DDR4 
                 bins      req_by_dis_hif = {4'b0100};    
                 bins  req_by_co_if_stall = {4'b0010};    
                 bins   req_by_selfref_sw = {4'b0001};    
     }
  endgroup
  cg_chn_flush cg_chn_flush_inst = new;

//check below vector are one hot and same to sel_chn_num
property p_check_vct_sel_match;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
     ((ie_cmd_active_vct[sel_chn_num]) == (|ie_cmd_active_vct)) and
     ((ie_rd_vld_vct[sel_chn_num]) == (|ie_rd_vld_vct)) and
     ((hif_lpr_credit_ie_vct[sel_chn_num]) == (|hif_lpr_credit_ie_vct)) and
     ((hif_hpr_credit_ie_vct[sel_chn_num]) == (|hif_hpr_credit_ie_vct)) and
     ((alloc_bt_vld_vct[sel_chn_num]) == (|alloc_bt_vld_vct)) and
     ((alloc_bwt_vld_vct[sel_chn_num]) == (|alloc_bwt_vld_vct)) and
     ((alloc_brt_vld_vct[sel_chn_num]) == (|alloc_brt_vld_vct)) and
     ((|matched_vct) == matched_chn_num_vld) and
     ((|chn_idle_vct) == idle_chn_num_vld);

endproperty

a_check_vct_sel_match: assert property (p_check_vct_sel_match);

property p_check_vct_onehot;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
//  $onehot0(ie_cmd_active_vct) and 
  $onehot0(ie_rd_vld_vct) and 
  $onehot0(hif_lpr_credit_ie_vct) and 
  $onehot0(hif_hpr_credit_ie_vct) and 
  $onehot0(alloc_bt_vld_vct) and
  $onehot0(alloc_bwt_vld_vct) and
  $onehot0(alloc_brt_vld_vct) and
  $onehot0(ie_rd_cnt_inc_vct) and
  $onehot0(ie_blk_end_vct);

endproperty

a_check_vct_onehot: assert property (p_check_vct_onehot);

//if no override, the command should go to matched channel
property p_match_chn;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
   (rxcmd_ptc_vld & ~override) |-> (rxcmd_ptc_vld_vct == matched_vct);
endproperty

a_match_chn : assert property (p_match_chn);

//if any channel is idle, should not override valid channel
property p_override_idle_chn;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
   (rxcmd_ptc_vld & override & |chn_idle_vct) |-> ~|(rxcmd_ptc_vld_vct & chn_vld_vct);
endproperty

a_override_idle_chn : assert property (p_override_idle_chn);

//if no channel is idle, override valid channel
property p_override_vld_chn;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
   (rxcmd_ptc_vld & override & ~|chn_idle_vct) |-> |(rxcmd_ptc_vld_vct & chn_vld_vct);
endproperty

a_override_vld_chn : assert property (p_override_vld_chn);

//when ie_wr_vld is 1, must have one channel are matched. i.e.|matched_vct=1.
property p_check_matched_ie_wr_vld;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
   ie_wr_vld |-> |matched_vct;
endproperty

a_check_matched_ie_wr_vld : assert property (p_check_matched_ie_wr_vld);

property p_check_matched_vct_onehot;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  |matched_vct |-> $onehot(matched_vct);
endproperty

a_check_matched_vct_onehot: assert property (p_check_matched_vct_onehot);

// flush and rxcmd_ptc_vld cannot be assert at same time
property p_check_flush_rxcmd_vld;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  flush_req |-> ~rxcmd_ptc_vld;
endproperty

a_check_flush_rxcmd_vld : assert property (p_check_flush_rxcmd_vld);

// flush mode, sel_chn_num should equal to next_chn_num;
property p_check_flush_sel_chn_num_eq_next_chn_num;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  flush_req |-> (sel_chn_num == next_chn_num);
endproperty

a_check_flush_sel_chn_num_eq_next_chn_num : assert property (p_check_flush_sel_chn_num_eq_next_chn_num);
`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
