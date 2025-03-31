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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_misc.sv#4 $
// -------------------------------------------------------------------------
// Description:
//
`include "DWC_ddrctl_all_defs.svh"
module te_misc #(
    //------------------------------ PARAMETERS ------------------------------------
     parameter  RD_CAM_ADDR_BITS  = `MEMC_RDCMD_ENTRY_BITS  // bits required to address RD CAM
    ,parameter  WR_CAM_ADDR_BITS  = `MEMC_WRCMD_ENTRY_BITS  // bits required to address WR CAM
    ,parameter  MAX_CAM_ADDR_BITS = 0                       // bits required to address WR CAM
    ,parameter  RD_CAM_ENTRIES    = 1 << RD_CAM_ADDR_BITS
    ,parameter  WR_CAM_ENTRIES    = 1 << WR_CAM_ADDR_BITS
    ,parameter  WR_ECC_CAM_ENTRIES = 0
    ,parameter  WR_ECC_CAM_ADDR_BITS = 0
    ,parameter  RANK_BITS         = `MEMC_RANK_BITS
    ,parameter  LRANK_BITS        = `UMCTL2_LRANK_BITS      // max supported of ranks in the system
    ,parameter  BG_BITS           = `MEMC_BG_BITS           // max supported bankgroups per rank
    ,parameter  BANK_BITS         = `MEMC_BANK_BITS         // max supported banks per rank
    ,parameter  BG_BANK_BITS      = `MEMC_BG_BANK_BITS      // max supported banks groups per rank
    ,parameter  PAGE_BITS         = `MEMC_PAGE_BITS     
    ,parameter  RANKBANK_BITS     = LRANK_BITS + BG_BANK_BITS 
    ,parameter  BSM_BITS          = `UMCTL2_BSM_BITS
    ,parameter  TOTAL_LRANKS      = 1 << LRANK_BITS
    ,parameter  TOTAL_BANKS       = 1 << (LRANK_BITS + BG_BANK_BITS)
    ,parameter  TOTAL_BSMS        = `UMCTL2_NUM_BSM
    ,parameter  IE_WR_TYPE_BITS   = 3
    ,parameter  CID_WIDTH         = `UMCTL2_CID_WIDTH
    )
    (
    //-------------------------- INPUTS AND OUTPUTS --------------------------------
     input                           core_ddrc_rstn                  // reset
    ,input                           co_te_clk                       // main clock
    ,input                           ddrc_cg_en                      // clock gate enable
//     ,input                           dh_te_dis_autopre_collide_opt   // by default, auto-precharge will
//                                                                      //  not be used when issuing a colliding
//                                                                      //  read/write, to allow the subsequent
//                                                                      //  write/read to take advantage of the
//                                                                      //  open page.
//                                                                      // set this bit to '1' to disable this
//                                                                      //  performance optimization
    ,input                           dh_te_dis_wc                    // write combine is disabled
    ,input  [MAX_CAM_ADDR_BITS-1:0]  te_rdwr_entry                   // read/write entry number
//     ,input                           te_wr_autopre                   // enable auto-precharge from wrCam
//     ,input                           te_pi_rd_autopre                // enable auto-precharge from rdCam
//    `ifdef UMCTL2_DUAL_HIF_1_OR_DDRCTL_RD_CRC_RETRY
    ,input                           te_wr_ie_blk_collision          // Block address collision 
//     ,input [BSM_BITS-1:0]            ts_bsm_num4rdwr                 // BSM # to use for reads and writes
    ,input                           ts_op_is_rd                     // DRAM op is read
    ,input                           ts_op_is_wr                     // DRAM op is write
//     ,input                           ts_wr_mode                      // DRAM in write mode
    ,output                          te_ts_rd_flush                  // need to do a read flush
    ,output                          te_ts_wr_flush                  // need to do a write flush
    ,input                           te_rd_flush                     // collision in the read cam
    ,input                           te_rd_flush_due_rd              // collision in the read cam
    ,input                           te_rd_flush_due_wr              // collision in the read cam
    ,input                           te_wr_flush                     // collision in the write cam
    ,input                           te_wr_flush_due_rd              // collision in the write cam
    ,input                           te_wr_flush_due_wr              // collision in the write cam
//     ,input                           te_rd_flush_started             // collision in the read cam has caused flush to start
//                                                                      // (same as te_rd_flush, but not accounting for
//                                                                      // currently issued command  better timing)
//     ,input                           te_wr_flush_started             // collision in the write cam has caused flush to start
//                                                                      //   (same as te_wr_flush, but not accounting for
//                                                                      //    currently issued command  better timing)
    ,output                          te_ih_retry 
    ,output                          te_wu_wr_retry                  // detected, retry the command
    ,output                          te_rdwr_autopre                 // read or write issues by GS w/ auto-precharge
                                                                     //  (does not comprehend read bypass)
    ,input                           ts_te_autopre                   // auto-precharge indicator 
    ,output reg                      te_ih_free_rd_entry_valid       // IH to free this read CAM entry number
    ,output reg [RD_CAM_ADDR_BITS-1:0] te_ih_free_rd_entry           // IH to free this read CAM entry number
    ,input  [TOTAL_BSMS-1:0]         te_dh_rd_bsm_valid
    ,input  [TOTAL_BSMS-1:0]         te_dh_rd_bsm_page_hit
    ,input  [TOTAL_BSMS-1:0]         te_dh_wr_bsm_valid
    ,input  [TOTAL_BSMS-1:0]         te_dh_wr_bsm_page_hit
    ,output reg [TOTAL_BANKS-1:0]    te_dh_rd_valid
    ,output reg [TOTAL_BANKS-1:0]    te_dh_rd_page_hit
    ,output reg [TOTAL_BANKS-1:0]    te_dh_wr_valid
    ,output reg [TOTAL_BANKS-1:0]    te_dh_wr_page_hit
    ,input  [TOTAL_BSMS-1:0]         te_bs_rd_hi
    ,output reg [TOTAL_BANKS-1:0]    te_dh_rd_hi
    ,output reg [TOTAL_LRANKS-1:0]   te_gs_rank_rd_valid
    ,output reg [TOTAL_LRANKS-1:0]   te_gs_rank_wr_valid
    ,input  [WR_CAM_ENTRIES-1:0]                te_wr_entry_valid           // WR CAM entry valid
    ,input  [RD_CAM_ENTRIES-1:0]                te_rd_entry_valid           // RD CAM entry valid
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block
    ,input  [WR_CAM_ENTRIES*RANKBANK_BITS-1:0]  te_wr_entry_rankbank        // WR CAM rank/bank entry
    ,input  [RD_CAM_ENTRIES*RANKBANK_BITS-1:0]  te_rd_entry_rankbank        // RD CAM rank/bank entry
//spyglass enable_block W240
    ,output                                     te_gs_any_wr_pending        // WR command pending
    ,output                                     te_gs_any_rd_pending        // RD command pending
    ,output reg [TOTAL_LRANKS-1:0]              te_gs_rank_wr_pending       // WR command pending per rank
    ,output reg [TOTAL_LRANKS-1:0]              te_gs_rank_rd_pending       // RD command pending per rank
    ,output reg [TOTAL_BANKS-1:0]               te_gs_bank_wr_pending       // WR command pending per rank/bank
    ,output reg [TOTAL_BANKS-1:0]               te_gs_bank_rd_pending       // RD command pending per rank/bank
   ,input  [LRANK_BITS-1:0]                      ih_te_wr_rank_num          // rank number
   ,input  [BG_BANK_BITS-1:0]                   ih_te_wr_bg_bank_num       // bank number
   ,input  [LRANK_BITS-1:0]                      ih_te_rd_rank_num          // rank number
   ,input  [BG_BANK_BITS-1:0]                   ih_te_rd_bg_bank_num       // bank number
   ,input                                       te_wr_collision_vld_due_rd
   ,input                                       te_wr_collision_vld_due_wr
   ,output  reg [TOTAL_BSMS-1:0]                te_rws_wr_col_bank         // entry of colliding bank (1bit for 1bank)
   ,output  reg [TOTAL_BSMS-1:0]                te_rws_rd_col_bank         // entry of colliding bank (1bit for 1bank)
   ,input  [RD_CAM_ENTRIES-1:0]                 te_rd_page_hit
   ,input  [WR_CAM_ENTRIES-1:0]                 te_wr_page_hit_entries
   ,output reg [WR_CAM_ADDR_BITS:0]             te_num_wr_pghit_entries
   ,output reg [RD_CAM_ADDR_BITS:0]             te_num_rd_pghit_entries
   ,input  [RD_CAM_ENTRIES-1:0]                 hmx_rd_vpr_abso_oldest_oh  // Oldest exVPR(One Hot)            
   ,output reg [RD_CAM_ADDR_BITS-1:0]           te_vpr_prefer              // Oldest exVPR(binary)  
   ,input  [WR_CAM_ENTRIES-WR_ECC_CAM_ENTRIES-1:0]          hmx_wr_vpw_abso_oldest_oh  // Oldest exVPW(One Hot). Use WR_ECC_CAM_ENTRIES to exclude WR ECC CAM
   ,output reg [WR_CAM_ADDR_BITS-`MEMC_INLINE_ECC_EN-1:0]   te_vpw_prefer               // Oldest exVPW(binary). Use MEMC_INLINE_ECC_EN to exclude WR ECC CAM BITS
   ,input  [WR_ECC_CAM_ENTRIES-1:0]             hmx_wrecc_btt_abso_oldest_oh  // Oldest exVPW(One Hot). Use RD_CAM_ENTRIES to exclude WR ECC CAM
   ,output reg [WR_ECC_CAM_ADDR_BITS-1:0]       te_wrecc_btt_prefer              // Oldest exVPW(binary). Use RD_CAM_ADDR_BITS to exclude WR ECC CAM
   ,input                                       reg_ddrc_lpddr4

   ,input  [RANKBANK_BITS-1:0]                  te_rd_rankbank_prefer      // cid and rank number of oldest entry in te_rd_cam
   ,input  [RANKBANK_BITS-1:0]                  te_wr_rankbank_prefer      // cid and rank number of oldest entry in te_wr_cam
   ,output [RANK_BITS-1:0]                      te_gs_rank_rd_prefer       // rank number of oldest entry in te_rd_cam
   ,output [RANK_BITS-1:0]                      te_gs_rank_wr_prefer       // rank number of oldest entry in te_wr_cam
);
 reg  [TOTAL_LRANKS-1:0]   te_gs_rank_rd_valid_w;
 reg  [TOTAL_LRANKS-1:0]   te_gs_rank_wr_valid_w;

 wire [BSM_BITS-1:0] ih_te_rd_rank_bg_bank_num;
 wire [BSM_BITS-1:0] ih_te_wr_rank_bg_bank_num;
 wire                ih_te_wr_bsm_alloc_int;
 assign ih_te_rd_rank_bg_bank_num = {ih_te_rd_rank_num,ih_te_rd_bg_bank_num};
 assign ih_te_wr_rank_bg_bank_num = {ih_te_wr_rank_num,ih_te_wr_bg_bank_num};

// save the collided bank number for WAR
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
     te_rws_rd_col_bank    <= {TOTAL_BSMS{1'b0}}; 
  end  
  else if(ddrc_cg_en)
  begin
     if (te_rd_flush_due_wr | te_rd_flush_due_rd) begin
        if (te_rd_flush_due_wr)
           te_rws_rd_col_bank[ih_te_wr_rank_bg_bank_num] <= 1'b1;
        else if (te_rd_flush_due_rd)
           te_rws_rd_col_bank[ih_te_rd_rank_bg_bank_num] <= 1'b1;
     end else begin
        te_rws_rd_col_bank <= {TOTAL_BSMS{1'b0}};
     end
  end  
end

// save the collided bank number for RAW or WAW
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
     te_rws_wr_col_bank    <= {TOTAL_BSMS{1'b0}}; 
  end  
  else if(ddrc_cg_en)
  begin
     if (te_wr_collision_vld_due_wr | te_wr_collision_vld_due_rd) begin
        if (te_wr_collision_vld_due_rd)
           te_rws_wr_col_bank[ih_te_rd_rank_bg_bank_num] <= 1'b1;
        else if (te_wr_collision_vld_due_wr)
           te_rws_wr_col_bank[ih_te_wr_rank_bg_bank_num] <= 1'b1;
     end else begin
        te_rws_wr_col_bank <= {TOTAL_BSMS{1'b0}};
     end
  end  
end


wire [WR_CAM_ENTRIES-1:0]      wr_pghit_entries;
wire [RD_CAM_ENTRIES-1:0]      rd_pghit_entries;

wire [WR_CAM_ADDR_BITS:0]      num_wr_pghit_entries;
wire [RD_CAM_ADDR_BITS:0]      num_rd_pghit_entries;
reg [4*(WR_CAM_ENTRIES/8)-1:0] num_wr_pghit_l1;
reg [4*(RD_CAM_ENTRIES/8)-1:0] num_rd_pghit_l1;

integer i;
assign wr_pghit_entries = te_wr_entry_valid & te_wr_page_hit_entries;
assign rd_pghit_entries = te_rd_entry_valid & te_rd_page_hit;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * 8)' found in module 'te_misc'
//SJ: This coding style is acceptable and there is no plan to change it.
    
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
       for(i=0; i<WR_CAM_ENTRIES/8; i=i+1)
         num_wr_pghit_l1[i*4+:4] <= 4'b0;
   end
   else begin
      for(i=0; i<WR_CAM_ENTRIES/8; i=i+1)
         if (num_wr_pghit_l1[i*4+:4] != f_add8bits(wr_pghit_entries[i*8+:8])) begin
            num_wr_pghit_l1[i*4+:4] <= f_add8bits(wr_pghit_entries[i*8+:8]);
         end
   end
end

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
       for(i=0; i<RD_CAM_ENTRIES/8; i=i+1)
         num_rd_pghit_l1[i*4+:4] <= 4'b0;
   end
   else begin
      for(i=0; i<RD_CAM_ENTRIES/8; i=i+1)
         if (num_rd_pghit_l1[i*4+:4] != f_add8bits(rd_pghit_entries[i*8+:8])) begin
            num_rd_pghit_l1[i*4+:4] <= f_add8bits(rd_pghit_entries[i*8+:8]);
         end
   end
end
//spyglass enable_block SelfDeterminedExpr-ML

generate
   if (WR_CAM_ENTRIES/8==64) begin: WR_64_l1
      assign num_wr_pghit_entries = f_add64_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==48) begin: WR_48_l1
      assign num_wr_pghit_entries = f_add48_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==32) begin: WR_32_l1
      assign num_wr_pghit_entries = f_add32_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==28) begin: WR_28_l1
      assign num_wr_pghit_entries = f_add28_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==24) begin: WR_24_l1
      assign num_wr_pghit_entries = f_add24_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==20) begin: WR_20_l1
      assign num_wr_pghit_entries = f_add20_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==16) begin: WR_16_l1
      assign num_wr_pghit_entries = f_add16_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==12) begin: WR_12_l1
      assign num_wr_pghit_entries = f_add12_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==8)begin: WR_8_l1
      assign num_wr_pghit_entries = f_add8_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==6)begin: WR_6_l1
      assign num_wr_pghit_entries = f_add6_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==4)begin: WR_4_l1
      assign num_wr_pghit_entries = f_add4_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==3)begin: WR_3_l1
      assign num_wr_pghit_entries = f_add3_4bits(num_wr_pghit_l1);
   end else if (WR_CAM_ENTRIES/8==2)begin: WR_2_l1
      assign num_wr_pghit_entries = f_add2_4bits(num_wr_pghit_l1);
   end
   
   if (RD_CAM_ENTRIES/8==32)begin: RD_32_l1
      assign num_rd_pghit_entries = f_add32_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==28) begin: RD_28_l1
      assign num_rd_pghit_entries = f_add28_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==24) begin: RD_24_l1
      assign num_rd_pghit_entries = f_add24_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==20) begin: RD_20_l1
      assign num_rd_pghit_entries = f_add20_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==16)begin: RD_16_l1
      assign num_rd_pghit_entries = f_add16_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==12) begin: RD_12_l1
      assign num_rd_pghit_entries = f_add12_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==8)begin: RD_8_l1
      assign num_rd_pghit_entries = f_add8_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==6)begin: RD_6_l1
      assign num_rd_pghit_entries = f_add6_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==4)begin: RD_4_l1
      assign num_rd_pghit_entries = f_add4_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==3)begin: RD_3_l1
      assign num_rd_pghit_entries = f_add3_4bits(num_rd_pghit_l1);
   end else if (RD_CAM_ENTRIES/8==2)begin: RD_2_l1
      assign num_rd_pghit_entries = f_add2_4bits(num_rd_pghit_l1);
   end

endgenerate

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
     te_num_wr_pghit_entries <= {1'b0,{WR_CAM_ADDR_BITS{1'b0}}};
     te_num_rd_pghit_entries <= {1'b0,{RD_CAM_ADDR_BITS{1'b0}}};
   end
   else begin
      if (|(te_num_wr_pghit_entries ^ num_wr_pghit_entries)) begin
         te_num_wr_pghit_entries <= num_wr_pghit_entries;
      end
      if (|(te_num_rd_pghit_entries ^ num_rd_pghit_entries)) begin
         te_num_rd_pghit_entries <= num_rd_pghit_entries;
      end
   end
end

//---------------------------------------------------------------
// Functions
//--------------------------------------------------------------
// add 8bits
function automatic [3:0] f_add8bits;
   input [7:0] data_in;
   begin
      f_add8bits = {3'b0,data_in[0]}+data_in[1]+data_in[2]+data_in[3]+data_in[4]+data_in[5]+data_in[6]+data_in[7];
   end
endfunction

// add 2 4bits
function automatic [4:0] f_add2_4bits;
   input [4*2-1:0] data_in;
   begin
      f_add2_4bits = {1'b0,data_in[0*4+:4]}+data_in[1*4+:4];
   end
endfunction

// add 3 4bits
function automatic [5:0] f_add3_4bits;
   input [4*3-1:0] data_in ;
   begin
      f_add3_4bits = f_add2_4bits(data_in[7:0]) + {2'b0,data_in[11:8]};
   end
endfunction

// add 4 4bits
function automatic [5:0] f_add4_4bits;
   input [4*4-1:0] data_in ;
   begin
      f_add4_4bits = f_add2_4bits(data_in[7:0]) + {1'b0,f_add2_4bits(data_in[15:8])};
   end
endfunction

// add 6 4bits
function automatic [6:0] f_add6_4bits;
   input [4*6-1:0] data_in;
   begin
      f_add6_4bits = f_add4_4bits(data_in[15:0]) + {2'b0,f_add2_4bits(data_in[23:16])};
   end
endfunction

// add 8 4bits
function automatic [6:0] f_add8_4bits;
   input [4*8-1:0] data_in;
   begin
      f_add8_4bits = f_add4_4bits(data_in[15:0]) + {1'b0,f_add4_4bits(data_in[31:16])};
   end
endfunction

// add 12 4bits
function automatic [7:0] f_add12_4bits;
   input [4*12-1:0] data_in;
   begin
      f_add12_4bits = f_add8_4bits(data_in[31:0]) + {2'b0,f_add4_4bits(data_in[47:32])};
   end
endfunction

// add 16 4bits
function automatic [7:0] f_add16_4bits;
   input [4*16-1:0] data_in;
   begin
      f_add16_4bits = f_add8_4bits(data_in[31:0]) + {1'b0,f_add8_4bits(data_in[63:32])};
   end
endfunction

// add 20 4bits
function automatic [8:0] f_add20_4bits;
   input [4*20-1:0] data_in;
   begin
      f_add20_4bits = f_add16_4bits(data_in[63:0]) + {3'b0,f_add4_4bits(data_in[79:64])};
   end
endfunction

// add 24 4bits
function automatic [8:0] f_add24_4bits;
   input [4*24-1:0] data_in;
   begin
      f_add24_4bits = f_add16_4bits(data_in[63:0]) + {2'b0,f_add8_4bits(data_in[95:64])};
   end
endfunction

// add 28 4bits
function automatic [8:0] f_add28_4bits;
   input [4*28-1:0] data_in;
   begin
      f_add28_4bits = f_add16_4bits(data_in[63:0]) + {1'b0,f_add12_4bits(data_in[111:64])};
   end
endfunction

// add 32 4bits
function automatic [8:0] f_add32_4bits;
   input [4*32-1:0] data_in;
   begin
      f_add32_4bits = f_add16_4bits(data_in[63:0]) + {1'b0,f_add16_4bits(data_in[127:64])};
   end
endfunction

// add 48 4bits
function automatic [9:0] f_add48_4bits;
   input [4*48-1:0] data_in;
   begin
      f_add48_4bits = f_add32_4bits(data_in[127:0]) + {2'b0,f_add16_4bits(data_in[191:128])};
   end
endfunction

// add 64 4bits
function automatic [9:0] f_add64_4bits;
   input [4*64-1:0] data_in;
   begin
      f_add64_4bits = f_add32_4bits(data_in[127:0]) + {1'b0,f_add32_4bits(data_in[255:128])};
   end
endfunction

//----------------------------- MISC LOGIC -------------------------------------

localparam  BANKS_PER_RANK      = 1 << BG_BANK_BITS;

// wire                         te_autopre_l;          // sel auto precharge betn rdCAM and wrCAM
// wire [BSM_BITS-1:0]          r_ih_bsm_num;          // flopped rank/bank from IH
// wire                         r_ih_bsm_alloc;        // flopped rank/bank from IH
// reg  [BSM_BITS-1:0]          r_ih_rd_bsm_num;       // flopped rank/bank from IH RD
// reg                          r_ih_rd_bsm_alloc;     // flopped rank/bank from IH RD
// `ifdef UMCTL2_DUAL_HIF_1
// reg  [BSM_BITS-1:0]          r_ih_wr_bsm_num;       // flopped rank/bank from IH WR
// reg                          r_ih_wr_bsm_alloc;     // flopped rank/bank from IH WR
// `endif // UMCTL2_DUAL_HIF_1
wire                         te_wr_rme_pas_viol = 1'b0;

// a collision has detected
// (a write combine is not considered a collision: data will be merged, even if there
//  is a read pending for the existing write)
// One exception not dealt with here: an explicit RMW command cannot be combined

wire   te_ih_wr_retry_int = te_rd_flush_due_wr | te_wr_flush_due_wr 
                            ;
//wire   te_ih_rd_retry_int = te_rd_flush_due_rd | (te_wr_flush_due_rd `ifdef DDRCTL_RD_CRC_RETRY `ifdef MEMC_USE_RMW & ~(ih_te_retry_rd & ih_te_rd_rmw) `endif `endif) 
wire   te_ih_rd_retry_int = te_rd_flush_due_rd | te_wr_flush_due_rd
                            ;

// single retry so OR the RD/WR retry together
assign te_ih_retry = te_ih_wr_retry_int | te_ih_rd_retry_int;
  
assign te_wu_wr_retry = te_ih_retry;



// determine the flush policy
assign te_ts_rd_flush = te_rd_flush;

// issue write flush to GS only if
// - no read flush
// - write flush enabled
// - no write valid from ih Or write combine is disabled (this condition was added
//   to prevent the global_fsm in GS from switching to WRITE when waiting for write data for
//   the write combine commands)
// For Inline ECC, write combine cannot be done for block address collision
// in this case, write is not flushed immediately. 
assign te_ts_wr_flush = ~te_rd_flush & te_wr_flush &
(
 (te_wr_flush_due_wr & (dh_te_dis_wc | te_wr_ie_blk_collision | te_wr_rme_pas_viol) // WAW & (dis_wc | block address collisoin | PAS violation)
) | (
 (te_wr_flush_due_rd) // WAR collision (Including RMW) 
)
);

// issue auto-precharge if auto-precharge is enabled, UNLESS:
//   - auto-precharge collision optimization is enabled AND
//   - there is a collision occurring AND
//   - collision is to the same bank as current read/write
// (if there is no current rd/wr, then te_autopre should be ignored)
// (note: this is based on flush in previous cycle, so it's not perfect
//        if IH withdraws a retried command and issues a new one.)

// always @(posedge co_te_clk or negedge core_ddrc_rstn)
//   if (~core_ddrc_rstn) begin
//      r_ih_rd_bsm_num    <= {BSM_BITS{1'b0}};
//      r_ih_rd_bsm_alloc  <= 1'b0;
//   end else `ifdef UMCTL2_CG_EN_1 if(ddrc_cg_en) `endif begin
//      r_ih_rd_bsm_num    <= ih_te_rd_bsm_num;
//      r_ih_rd_bsm_alloc  <= ih_te_rd_bsm_alloc;
//   end
// 
// `ifdef UMCTL2_DUAL_HIF_1
// always @(posedge co_te_clk or negedge core_ddrc_rstn)
//   if (~core_ddrc_rstn) begin
//      r_ih_wr_bsm_num    <= {BSM_BITS{1'b0}};
//      r_ih_wr_bsm_alloc  <= 1'b0;
//   end else `ifdef UMCTL2_CG_EN_1 if(ddrc_cg_en) `endif begin
//      r_ih_wr_bsm_num    <= ih_te_wr_bsm_num;
//      r_ih_wr_bsm_alloc  <= ih_te_wr_bsm_alloc;
//   end
// `endif // UMCTL2_DUAL_HIF_1


// note: following codes are commented out for bug 7584
// mux betn rd and wr autopre from respective CAMs
// in wr_mode choose wr_autopre and in rd_mode choose rd_autopre
// `ifndef UPCTL2_EN_1 //------------------------------------------------- Start uMCTL2 unique block --------------//
// Similarly, mux between r_ih_wr_bsm_num and r_ih_rd_bsm_num
// assign te_autopre_l = ts_wr_mode ? te_wr_autopre : te_pi_rd_autopre;
// `ifdef UMCTL2_DUAL_HIF_1    
// assign r_ih_bsm_num     = ts_wr_mode ? r_ih_wr_bsm_num : r_ih_rd_bsm_num;
// assign r_ih_bsm_alloc   = ts_wr_mode ? r_ih_wr_bsm_alloc : r_ih_rd_bsm_alloc;
// `else
// assign r_ih_bsm_num     = r_ih_rd_bsm_num;
// assign r_ih_bsm_alloc   = r_ih_rd_bsm_alloc;
// `endif // UMCTL2_DUAL_HIF_1
// 
// assign te_autopre = te_autopre_l                                      &
//                    (~(~dh_te_dis_autopre_collide_opt                   &
//                      (te_rd_flush_started | te_wr_flush_started) &
//          (r_ih_bsm_num == ts_bsm_num4rdwr) & (r_ih_bsm_alloc)));
// `endif // UPCTL2_EN_1 //----------------------------------------------- End uMCTL2 unique block ----------------//
// `ifdef UPCTL2_EN_1    //----------------------------------------------- Start uPCTL2 unique block --------------//
// assign te_autopre = ts_wr_mode ? te_wr_autopre : te_pi_rd_autopre;
// `endif // UPCTL2_EN_1 //----------------------------------------------- End uPCTL2 unique block ----------------//

assign te_rdwr_autopre = ts_te_autopre & (ts_op_is_rd | ts_op_is_wr);
// note for uMCTL2: bypass reads will never be issued with auto-precharge,
//       even if auto-precharge is enabled.

//-------------------------- FREE CAM ENTRIES ----------------------------------

// free read CAM pointers
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn) begin
    te_ih_free_rd_entry_valid <= 1'b0;
    te_ih_free_rd_entry [RD_CAM_ADDR_BITS-1:0] <= {RD_CAM_ADDR_BITS{1'b0}};
  end
  else if(ddrc_cg_en) begin
    te_ih_free_rd_entry_valid <= ts_op_is_rd;
    te_ih_free_rd_entry [RD_CAM_ADDR_BITS-1:0] <= te_rdwr_entry [RD_CAM_ADDR_BITS-1:0];
  end


//------------------------------------------------------------------------------

//-------------------------- BSM to RANKBANK num -------------------------------
        wire [TOTAL_BSMS-1:0]               rd_vld_w_pghit;
        wire [TOTAL_BSMS-1:0]               wr_vld_w_pghit;

        assign rd_vld_w_pghit = te_dh_rd_bsm_valid & te_dh_rd_bsm_page_hit;
        assign wr_vld_w_pghit = te_dh_wr_bsm_valid & te_dh_wr_bsm_page_hit;
        integer                             rank_idx;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(RANKBANK_BITS * bsm_idx)' found in module 'te_misc'
//SJ: This coding style is acceptable and there is no plan to change it.

    always @(*) begin
        te_dh_rd_valid    = te_dh_rd_bsm_valid;
        te_dh_rd_page_hit = te_dh_rd_bsm_page_hit;
        te_dh_wr_valid    = te_dh_wr_bsm_valid;
        te_dh_wr_page_hit = te_dh_wr_bsm_page_hit;
        te_dh_rd_hi       = te_bs_rd_hi;
    end

    always @(*) begin
        for (rank_idx=0; rank_idx<TOTAL_LRANKS; rank_idx=rank_idx+1) begin
            te_gs_rank_rd_valid_w[rank_idx] = |rd_vld_w_pghit[rank_idx*BANKS_PER_RANK+:BANKS_PER_RANK];
        end
    end

    always @(*) begin
        for (rank_idx=0; rank_idx<TOTAL_LRANKS; rank_idx=rank_idx+1) begin
            te_gs_rank_wr_valid_w[rank_idx] = |wr_vld_w_pghit[rank_idx*BANKS_PER_RANK+:BANKS_PER_RANK];
        end
    end



  // Flop te_gs_rank_rd_valid/te_gs_rank_wr_valid here
     logic te_gs_rank_rw_vld_update ;

     assign te_gs_rank_rw_vld_update = (|(te_gs_rank_rd_valid ^ te_gs_rank_rd_valid_w)) | (|(te_gs_rank_wr_valid ^ te_gs_rank_wr_valid_w));

  always @(posedge co_te_clk or negedge core_ddrc_rstn)
    if (~core_ddrc_rstn) begin
      te_gs_rank_rd_valid <= {TOTAL_LRANKS{1'b0}};
      te_gs_rank_wr_valid <= {TOTAL_LRANKS{1'b0}};
    end
    else begin
      if (te_gs_rank_rw_vld_update) begin
         te_gs_rank_rd_valid <= te_gs_rank_rd_valid_w;
         te_gs_rank_wr_valid <= te_gs_rank_wr_valid_w;
      end
    end

//spyglass enable_block SelfDeterminedExpr-ML

//---------------------- CAM ENTRY VALID PER RANK/BANK -------------------------

    // RD/WR command pending in the CAM
    assign te_gs_any_wr_pending = |te_wr_entry_valid;
    assign te_gs_any_rd_pending = |te_rd_entry_valid;

//spyglass disable_block W415a
//SMD: Signal te_gs_rank_wr_pending/te_gs_rank_rd_pending is being assigned multiple times in same always block. 
//SJ: Using initialization in process to minimize code - sets the default for any hanging branches, avoids latches
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((i * RANKBANK_BITS) + BG_BANK_BITS)' found in module 'te_misc'
//SJ: This coding style is acceptable and there is no plan to change it.

    // RD/WR command per rank pending in the CAM
    generate
        if (TOTAL_LRANKS > 1) begin : TOTAL_LRANKS_GT1
            always @(*) begin : rank_rdwr_pending_PROC
                integer i;

                te_gs_rank_wr_pending = {TOTAL_LRANKS{1'b0}};
                te_gs_rank_rd_pending = {TOTAL_LRANKS{1'b0}};

                for (i=0; i<WR_CAM_ENTRIES; i=i+1) begin
                    if (te_wr_entry_valid[i]) begin
                        te_gs_rank_wr_pending   = te_gs_rank_wr_pending
                                                | ({{(TOTAL_LRANKS-1){1'b0}}, 1'b1} << te_wr_entry_rankbank[((i*RANKBANK_BITS)+BG_BANK_BITS)+:LRANK_BITS]);
                    end
                end
                for (i=0; i<RD_CAM_ENTRIES; i=i+1) begin
                    if (te_rd_entry_valid[i]) begin
                        te_gs_rank_rd_pending   = te_gs_rank_rd_pending
                                                | ({{(TOTAL_LRANKS-1){1'b0}}, 1'b1} << te_rd_entry_rankbank[((i*RANKBANK_BITS)+BG_BANK_BITS)+:LRANK_BITS]);
                    end
                end
            end
        end else begin : TOTAL_LRANKS_EQ1
            always @(*) begin : rank_rdwr_pending_PROC
                te_gs_rank_wr_pending = te_gs_any_wr_pending;
                te_gs_rank_rd_pending = te_gs_any_rd_pending;
            end
        end
    endgenerate

    // RD/WR command per rank/bank pending in the CAM
    reg [LRANK_BITS-1:0]   wr_entry_rank;
    reg [LRANK_BITS-1:0]   rd_entry_rank;
    reg [BG_BANK_BITS-1:0] wr_entry_bank;
    reg [BG_BANK_BITS-1:0] rd_entry_bank;

    always @(*) begin : bank_rdwr_pending_lp54_PROC
        integer i;

        //wr_entry_rank = {LRANK_BITS{1'b0}};
        //wr_entry_bank = {BG_BANK_BITS{1'b0}};
        //rd_entry_rank = {LRANK_BITS{1'b0}};
        //rd_entry_bank = {BG_BANK_BITS{1'b0}};

        te_gs_bank_wr_pending = {TOTAL_BANKS{1'b0}};
        te_gs_bank_rd_pending = {TOTAL_BANKS{1'b0}};

        for (i=0; i<WR_CAM_ENTRIES; i=i+1) begin
            if (te_wr_entry_valid[i]) begin
                wr_entry_rank = te_wr_entry_rankbank[((i*RANKBANK_BITS)+BG_BANK_BITS)+:LRANK_BITS];
                wr_entry_bank = te_wr_entry_rankbank[(i*RANKBANK_BITS)+:BG_BANK_BITS];
                te_gs_bank_wr_pending   = te_gs_bank_wr_pending
                                        | {{(TOTAL_BANKS-1){1'b0}}, 1'b1} << ((reg_ddrc_lpddr4) ? {wr_entry_rank,wr_entry_bank[2:0]} : 
                                                                                                  {wr_entry_rank,wr_entry_bank[0],wr_entry_bank[3:2]});
            end
        end
        for (i=0; i<RD_CAM_ENTRIES; i=i+1) begin
            if (te_rd_entry_valid[i]) begin
                rd_entry_rank = te_rd_entry_rankbank[((i*RANKBANK_BITS)+BG_BANK_BITS)+:LRANK_BITS];
                rd_entry_bank = te_rd_entry_rankbank[(i*RANKBANK_BITS)+:BG_BANK_BITS];
                te_gs_bank_rd_pending   = te_gs_bank_rd_pending
                                        | {{(TOTAL_BANKS-1){1'b0}}, 1'b1} << ((reg_ddrc_lpddr4) ? {rd_entry_rank,rd_entry_bank[2:0]} : 
                                                                                                  {rd_entry_rank,rd_entry_bank[0],rd_entry_bank[3:2]});
            end
        end
    end
//spyglass enable_block SelfDeterminedExpr-ML
//spyglass enable_block W415a


//--------------------------//
// Generate te_vpr/w_prefer // 
//--------------------------//

// one hot to binary
function automatic [RD_CAM_ADDR_BITS-1:0] oh2bin (input [RD_CAM_ENTRIES-1:0] oh);
    integer k,l;
    begin
        oh2bin = 0;
        for (k=0;k<RD_CAM_ADDR_BITS;k=k+1) begin
            for (l=0;l<RD_CAM_ENTRIES;l=l+1) begin
                if (|(l & (1 << k))) begin
                    oh2bin[k] = oh2bin[k] | oh[l];
                    // An example of RD_CAM_ADDR_BITS=4, RD_CAM_ENTRIES=16
                    // oh2bin [0] = oh[ 1]  | oh[ 3] | oh[ 5] | oh[ 7] | oh[ 9] | oh[11] | oh[13] | oh[15]
                    // oh2bin [1] = oh[ 2]  | oh[ 3] | oh[ 6] | oh[ 7] | oh[10] | oh[11] | oh[14] | oh[15]
                    // oh2bin [2] = oh[ 4]  | oh[ 5] | oh[ 6] | oh[ 7] | oh[12] | oh[13] | oh[14] | oh[15]
                    // oh2bin [3] = oh[ 8]  | oh[ 9] | oh[10] | oh[11] | oh[12] | oh[13] | oh[14] | oh[15]
                end
            end 
        end
    end
endfunction

// one hot to binary
function automatic [WR_CAM_ADDR_BITS-`MEMC_INLINE_ECC_EN-1:0] oh2bin_wr (input [WR_CAM_ENTRIES-WR_ECC_CAM_ENTRIES-1:0] oh);
    integer k,l;
    begin
        oh2bin_wr = 0;
        for (k=0;k<WR_CAM_ADDR_BITS-`MEMC_INLINE_ECC_EN;k=k+1) begin
            for (l=0;l<WR_CAM_ENTRIES-WR_ECC_CAM_ENTRIES;l=l+1) begin
                if (|(l & (1 << k))) begin
                    oh2bin_wr[k] = oh2bin_wr[k] | oh[l];
                    // An example of RD_CAM_ADDR_BITS=4, RD_CAM_ENTRIES=16
                    // oh2bin [0] = oh[ 1]  | oh[ 3] | oh[ 5] | oh[ 7] | oh[ 9] | oh[11] | oh[13] | oh[15]
                    // oh2bin [1] = oh[ 2]  | oh[ 3] | oh[ 6] | oh[ 7] | oh[10] | oh[11] | oh[14] | oh[15]
                    // oh2bin [2] = oh[ 4]  | oh[ 5] | oh[ 6] | oh[ 7] | oh[12] | oh[13] | oh[14] | oh[15]
                    // oh2bin [3] = oh[ 8]  | oh[ 9] | oh[10] | oh[11] | oh[12] | oh[13] | oh[14] | oh[15]
                end
            end 
        end
    end
endfunction

// one hot to binary
function automatic [WR_ECC_CAM_ADDR_BITS-1:0] oh2bin_wrecc (input [WR_ECC_CAM_ENTRIES-1:0] oh);
    integer k,l;
    begin
        oh2bin_wrecc = 0;
        for (k=0;k<WR_ECC_CAM_ADDR_BITS;k=k+1) begin
            for (l=0;l<WR_ECC_CAM_ENTRIES;l=l+1) begin
                if (|(l & (1 << k))) begin
                    oh2bin_wrecc[k] = oh2bin_wrecc[k] | oh[l];
                    // An example of RD_CAM_ADDR_BITS=4, RD_CAM_ENTRIES=16
                    // oh2bin [0] = oh[ 1]  | oh[ 3] | oh[ 5] | oh[ 7] | oh[ 9] | oh[11] | oh[13] | oh[15]
                    // oh2bin [1] = oh[ 2]  | oh[ 3] | oh[ 6] | oh[ 7] | oh[10] | oh[11] | oh[14] | oh[15]
                    // oh2bin [2] = oh[ 4]  | oh[ 5] | oh[ 6] | oh[ 7] | oh[12] | oh[13] | oh[14] | oh[15]
                    // oh2bin [3] = oh[ 8]  | oh[ 9] | oh[10] | oh[11] | oh[12] | oh[13] | oh[14] | oh[15]
                end
            end 
        end
    end
endfunction

wire [RD_CAM_ADDR_BITS-1:0] te_vpr_prefer_w;
assign te_vpr_prefer_w = oh2bin(hmx_rd_vpr_abso_oldest_oh);


wire [WR_CAM_ADDR_BITS-`MEMC_INLINE_ECC_EN-1:0] te_vpw_prefer_w;
assign te_vpw_prefer_w = { 1'b0, oh2bin(hmx_wr_vpw_abso_oldest_oh) };

wire [WR_ECC_CAM_ADDR_BITS-1:0] te_wrecc_btt_prefer_w;
assign te_wrecc_btt_prefer_w = oh2bin_wrecc(hmx_wrecc_btt_abso_oldest_oh);

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_vpr_prefer <= {RD_CAM_ADDR_BITS{1'b0}};
    te_vpw_prefer <= {WR_CAM_ADDR_BITS-`MEMC_INLINE_ECC_EN{1'b0}};
    te_wrecc_btt_prefer <= {WR_ECC_CAM_ADDR_BITS{1'b0}};
  end
  else begin
    if (|(te_vpr_prefer ^ te_vpr_prefer_w)) begin
       te_vpr_prefer <= te_vpr_prefer_w;
    end
//spyglass disable_block W164a
//SMD: LHS: 'te_vpw_prefer' width 4 is less than RHS: 'te_vpw_prefer_w' width 5 in assignment
//SJ: Using RD_CAM_ADDR_BITS width to exclude WR ECC CAM.
    te_vpw_prefer <= te_vpw_prefer_w;
//spyglass enable_block W164a
    te_wrecc_btt_prefer <= te_wrecc_btt_prefer_w;
  end
end



wire [LRANK_BITS-1:0] te_mapped_rank_rd_prefer = te_rd_rankbank_prefer[(RANKBANK_BITS-1):BG_BANK_BITS];
wire [LRANK_BITS-1:0] te_mapped_rank_wr_prefer = te_wr_rankbank_prefer[(RANKBANK_BITS-1):BG_BANK_BITS];
assign te_gs_rank_rd_prefer = te_mapped_rank_rd_prefer;
assign te_gs_rank_wr_prefer = te_mapped_rank_wr_prefer;

endmodule
