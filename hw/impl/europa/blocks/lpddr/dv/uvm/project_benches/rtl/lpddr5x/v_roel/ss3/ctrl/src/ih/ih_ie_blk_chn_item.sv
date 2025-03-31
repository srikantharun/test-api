//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_ie_blk_chn_item.sv#4 $
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
//  compare ecc address and generate ecc command in one cycle
//  below cases to terminate a block
//  - override
//  - rd priority change
//  - rd->wr to same address
//  - full access
//  - flush
//  Flush can be trigger by below ways
//  - ecc hole access
//  - self refresh with power down
//  - dis_hif=1
//  - timeout 
//  - etc... (_replace_P80001562-505275_)
//
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module ih_ie_blk_chn_item
import DWC_ddrctl_reg_pkg::*;
#(
    parameter CHN_ID                = 0
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
   ,parameter ECC_ADDR_WIDTH        = 32
)
(  
    input                              core_ddrc_core_clk
   ,input                              core_ddrc_rstn
   ,input                              ddrc_cg_en
   ,input                              reg_ddrc_blk_channel_active_term
   ,input  [BURST_RDWR_WIDTH-1:0]      reg_ddrc_burst_rdwr
   //te_ih 
   ,input                              te_ih_retry
   //incomming command
   ,input   [ECC_ADDR_WIDTH-1:0]       rxcmd_ecc_addr
   ,input   [1:0]                      rxcmd_pri   //1: HPR; 0: LPR/VPR
   ,input   [CMD_TYPE_BITS-1:0]        rxcmd_type
   ,input                              rxcmd_ptc_vld //protected region

   //for accumulate wrdata in one block.
   ,input   [WRDATA_CYCLES-1:0]        wdata_mask_full
   ,input   [IE_BURST_NUM_BITS-1:0]    ie_burst_num

   //channel information
   ,input                              override
   ,input                              ie_wr_vld
   ,input                              flush_req
   ,output                             flush_done

   ,input   [ BT_BITS-1:0]             alloc_bt
   ,input   [BWT_BITS-1:0]             alloc_bwt
   ,input   [BRT_BITS-1:0]             alloc_brt
   ,input                              re_done_i
   ,input   [BT_BITS-1:0]              re_done_bt
   //output
   ,output  reg                        chn_vld
   ,output                             matched
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
   ,output  [BT_BITS-1:0]              ie_blk_end_bt
   ,output                             ie_bwt_vld
   ,output                             ie_brt_vld
   ,output                             ie_blk_end
   ,output                             ie_blk_rd_end
   ,output                             ie_blk_wr_end

   ,output                             hif_lpr_credit_ie
   ,output                             hif_hpr_credit_ie
);

//------------------------------ LOCAL PARAMETERS ------------------------------------
localparam CMD_TYPE_BLK_WR   = `MEMC_CMD_TYPE_BLK_WR;
localparam CMD_TYPE_BLK_RD   = `MEMC_CMD_TYPE_BLK_RD;
localparam CMD_TYPE_RMW      = `MEMC_CMD_TYPE_RMW;
localparam CMD_TYPE_RESERVED = `MEMC_CMD_TYPE_RESERVED;
localparam MASK_VEC_BITS     = WRDATA_CYCLES*8;  //8 access per block, each access support Full or Half write.
localparam ACCESS_VEC_BITS   =  8; 

//channel fileds
reg  [ECC_ADDR_WIDTH-1:0]  r_ecc_addr;
reg                        r_blk_pri;
reg  [ BT_BITS-1:0]        r_ie_bt;
reg  [BWT_BITS-1:0]        r_ie_bwt;
reg  [BRT_BITS-1:0]        r_ie_brt;

wire [ BT_BITS-1:0]        ie_chn_bt;
reg                        re_done;
reg                        any_wr;
reg                        any_rd;

wire                       rd_cmd;
wire                       wr_cmd;
wire                       rmw_cmd;

wire                       rd_pri_chg;
wire                       next_is_hpr;

wire                       rd_wr_collision;
wire                       wr_addr_match;

wire                       override_or_rpc;
wire  [1:0]                ie_critical_dword_msb;

wire                       override_or_rwc;
wire                       override_or_rpc_rwc;

reg [MASK_VEC_BITS-1:0]    wdata_mask_full_vec;

reg [MASK_VEC_BITS-1:0]    ie_mask_full_vec;
reg [ACCESS_VEC_BITS-1:0]  ie_access_vec;

wire                       is_full_blk_wr;
wire                       is_full_blk_rd;

wire                       chn_act_idle;

//for register output signals
reg                 alloc_bt_vld_r ;
reg                 alloc_bwt_vld_r;
reg                 alloc_brt_vld_r;

wire                ie_wr_cnt_inc_i;
wire                ie_rd_cnt_inc_i;
wire [BWT_BITS-1:0] ie_bwt_i;
wire [BRT_BITS-1:0] ie_brt_i;
wire                ie_bwt_vld_i;
wire                ie_brt_vld_i;
wire [BT_BITS-1:0]  ie_blk_end_bt_i;
wire                ie_blk_end_i;
wire                ie_blk_rd_end_i;
wire                ie_blk_wr_end_i;

reg                ie_wr_cnt_inc_r;
reg                ie_rd_cnt_inc_r;
reg [BWT_BITS-1:0] ie_bwt_r;
reg [BRT_BITS-1:0] ie_brt_r;
reg                ie_bwt_vld_r;
reg                ie_brt_vld_r;
reg [BT_BITS-1:0]  ie_blk_end_bt_r;
reg                ie_blk_end_r;
reg                ie_blk_rd_end_r;
reg                ie_blk_wr_end_r;
//spyglass disable_block W528
//SMD: set but not read.
//SJ: This signal will be removed in future in UMCTL5. For temporary.
wire [1:0] reg_ddrc_data_bus_width;
assign reg_ddrc_data_bus_width = 2'b00;
//spyglass enable_block W528
integer                    i;

assign te_ih_retry_ie_cmd = te_ih_retry | ie_cmd_active;

assign override_or_rpc        = override | rd_pri_chg;
assign override_or_rwc        = override | rd_wr_collision;
assign override_or_rpc_rwc    = override | rd_pri_chg | rd_wr_collision;

//------------------------------------------------------------------
// comparator
//------------------------------------------------------------------
assign matched = chn_vld && (r_ecc_addr == rxcmd_ecc_addr);

//Flush logic
//assign flush_done = flush_req & (any_wr ? wr_ecc_done : 1'b1);
assign flush_done = flush_req;  //should no incoming command during flush.

//a pulse signasl, active block terminated will make the channel IDLE
assign chn_act_idle = reg_ddrc_blk_channel_active_term & ((is_full_blk_wr & ie_wr_vld & ~te_ih_retry) |
                                                          (is_full_blk_rd & rd_cmd & ~te_ih_retry_ie_cmd)); 
//------------------------------------------------------------------
// Latch channel's ecc_address, blk_pri, ie_bt;
//------------------------------------------------------------------
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      r_ecc_addr     <= {(ECC_ADDR_WIDTH){1'b0}}; 
      chn_vld        <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(override & rxcmd_ptc_vld & ~te_ih_retry) begin // override will cause chn_vld become 1, and store ecc address. chn_vld could be 0 or 1 when override happen.
         r_ecc_addr     <= rxcmd_ecc_addr;
         chn_vld        <= 1'b1;
      end else if(chn_act_idle | flush_done)begin  //flush done or active block terminated will make the channel IDLE, at this time should no incoming command (rxcmd_ptc_vld=0), see assertion
         r_ecc_addr     <= {(ECC_ADDR_WIDTH){1'b0}}; 
         chn_vld        <= 1'b0;
      end
   end
end

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      r_ie_bt        <= {BT_BITS{1'b0}};
      r_ie_bwt       <= {BT_BITS{1'b0}};
      r_ie_brt       <= {BT_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      if(alloc_bt_vld) begin
         r_ie_bt     <= alloc_bt;
      end
      if(alloc_bwt_vld) begin
         r_ie_bwt     <= alloc_bwt;
      end
      if(alloc_brt_vld) begin
         r_ie_brt     <= alloc_brt;
      end
   end
end
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      r_blk_pri      <= 1'b0;
   end else if(ddrc_cg_en) begin
      if ((ie_rd_vld & ie_rd_type==`IE_RD_TYPE_RE_B) & ~te_ih_retry) begin //store blk priority when RE_B is accepted
         r_blk_pri   <= next_is_hpr;
      end
   end
end

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      re_done  <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(override_or_rpc_rwc & rxcmd_ptc_vld) begin
         re_done  <= 1'b0;
      end else if(chn_act_idle | flush_done) begin
         re_done  <= 1'b0;
      end else if(re_done_i & (re_done_bt == ie_chn_bt)) begin
         re_done  <= 1'b1;
      end
   end
end
//------------------------------------------------------------------
// generate input command
//------------------------------------------------------------------
assign rd_cmd       = (rxcmd_type == CMD_TYPE_BLK_RD) & rxcmd_ptc_vld ;
assign wr_cmd       = (rxcmd_type == CMD_TYPE_BLK_WR) & rxcmd_ptc_vld ;
assign rmw_cmd      = (rxcmd_type == CMD_TYPE_RMW)    & rxcmd_ptc_vld ;

//------------------------------------------------------------------
// generate any_rd/any_wr
//------------------------------------------------------------------
// any_rd became 1 aftre RD_ECC(RE_B) is send
// any_rd became 0 after a channel is override or channel go to idle
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      any_rd <= 1'b0;
   end else if(ddrc_cg_en) begin
      if ((ie_rd_vld & ie_rd_type==`IE_RD_TYPE_RE_B) & ~te_ih_retry) begin
         any_rd <= 1'b1;
      end else if((override_or_rwc & rxcmd_ptc_vld & ~te_ih_retry) | chn_act_idle | flush_done) begin  //any override will clear any_rd. the command could be RE_B or WD_E
         any_rd <= 1'b0;
      end
   end
end


// any_wr became 0 after override with read or chn become idle
// any_wr became 1 aftre any wr/rmw command is accepted.
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      any_wr <= 1'b0;
   end else if(ddrc_cg_en) begin
      if ((wr_cmd | rmw_cmd) & ~te_ih_retry_ie_cmd) begin
         any_wr <= 1'b1;
      end else if((override_or_rpc & ie_rd_vld & ~te_ih_retry) | chn_act_idle | flush_done) begin  //override with read will clear any_wr. override by WR don't clear any_wr because the new write block should set any_wr right now.
         any_wr <= 1'b0;
      end
   end
end

//generate the first read command
// 
reg first_rd_flag;
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      first_rd_flag <= 1'b0;
   end else if(ddrc_cg_en) begin
      if((override_or_rpc_rwc & rxcmd_ptc_vld) | chn_act_idle | flush_done) begin 
         first_rd_flag <= 1'b0;
      end else if ((rd_cmd | rmw_cmd) & ~te_ih_retry_ie_cmd) begin
         first_rd_flag <= 1'b1;
      end
   end
end

wire first_cmd;
wire first_cmd_acpt;
wire first_wr_cmd;
wire first_wr_cmd_acpt;


assign first_cmd         = override_or_rpc_rwc & rxcmd_ptc_vld ; //the first command is assert on the interface.  first command could be RD_ECC or WR_DAT
assign first_cmd_acpt    = first_cmd & ~te_ih_retry; //the first command is accepted by TE.

assign first_wr_cmd      = (override_or_rwc | ~any_wr) & (wr_cmd | rmw_cmd); //the first write command is accepted that will located a BWT. the first wr command is first WR_DAT.
assign first_wr_cmd_acpt = first_wr_cmd & ~te_ih_retry_ie_cmd; //the first write command is accepted that will located a BWT.


assign alloc_bt_vld      = alloc_bt_vld_r; 
assign alloc_bwt_vld     = alloc_bwt_vld_r;
assign alloc_brt_vld     = alloc_brt_vld_r;

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      alloc_bt_vld_r      <= 1'b0;
      alloc_bwt_vld_r     <= 1'b0;
      alloc_brt_vld_r     <= 1'b0;
   end else if(ddrc_cg_en) begin
      alloc_bt_vld_r      <= first_cmd_acpt; //the first command is accepted that will allocated a BT.
      alloc_bwt_vld_r     <= first_wr_cmd_acpt; //the first write command is accepted that will allocated a BWT.
      alloc_brt_vld_r     <= ie_rd_vld & ~ie_wr_vld & ~te_ih_retry; //"ie_rd_vld & ~ie_wr_vld" indicate RE_B.
   end
end

//assign ie_bt             = first_cmd ? alloc_bt :  r_ie_bt;
assign ie_bt             = (first_cmd | alloc_bt_vld) ? alloc_bt :  r_ie_bt; //BT for all the command, that qualify with ih_te_rd/wr_vld
assign ie_chn_bt         = alloc_bt_vld ? alloc_bt : r_ie_bt; //BT for one channel untill first comand is accpted. that qualify with chn status/blk_end_i/cnt_inc

assign ie_cmd_bwt        = (first_wr_cmd | alloc_bwt_vld) ? alloc_bwt :  r_ie_bwt; //BWT for all the command, that qualify with ih_te_rd/wr_vld
//-------------------------------------------------------------------------------
//ie_bwt is used when ie_blk_wr_end or ie_wr_cnt_inc
// ie_blk_wr_end is assert when WE_BW command or override by incoming command.
// ie_wr_cnt_inc is aligned with WE_BW command
// so use register version.
//assign ie_bwt          = r_ie_bwt;
assign ie_bwt_i          = alloc_bwt_vld ? alloc_bwt : r_ie_bwt;
//
//ie_brt is used when ie_blk_rd_end or ie_rd_cnt_inc.
// ie_blk_rd_end is assert when WE_BW command if a write command cuase block active terminate
// ie_blk_rd_end is assert when RD_E (not the first read) command if a read  command cuase block active terminate
// ie_blk_rd_end is assert when RE_B  command if override command is RD
// ie_blk_rd_end is assert when WD_E  command if override command is WR 
// ie_rd_cnt_inc is aligned with RD_E command, the BRT was registerd when RD ECC.
//assign ie_brt          = r_ie_brt; 
assign ie_brt_i          = alloc_brt_vld ? alloc_brt : r_ie_brt; 

// blk_end could assert in below cases
// active block terminated by write, it is assert when WE_BW command accepted (is_full_blk_wr)
// active block terminated by read, it is assert when RD_E command accepted (is_full_blk_rd)
// overide by incoming write, it is assert when WD_E command accepted (override==1)
// overide by incoming read, it is assert when RE_B command accepted (override==1)
// flush, it is assert when at flush cycle.
//
assign ie_blk_end_i    = chn_vld & ((override_or_rpc_rwc & rxcmd_ptc_vld & ~te_ih_retry) | chn_act_idle | flush_done);

assign ie_blk_end_bt_i = ie_chn_bt;

assign ie_blk_rd_end_i = ie_blk_end_i & any_rd;
assign ie_blk_wr_end_i = ie_blk_end_i & any_wr;

assign ie_rd_cnt_inc_i = (rd_cmd | rmw_cmd) & ~te_ih_retry_ie_cmd;
assign ie_wr_cnt_inc_i = ie_wr_vld & ~te_ih_retry;

assign ie_brt_vld_i    = any_rd;
assign ie_bwt_vld_i    = any_wr;

//register blk_*_end blk_*_inc and brt/bwt to making timing better
// (those signal used te_ih_retry that could generate critical path)
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ie_blk_end_r        <= 1'b0;
      ie_blk_rd_end_r     <= 1'b0;
      ie_blk_wr_end_r     <= 1'b0;
      ie_rd_cnt_inc_r     <= 1'b0;
      ie_wr_cnt_inc_r     <= 1'b0;
      ie_brt_vld_r        <= 1'b0;
      ie_bwt_vld_r        <= 1'b0;
      ie_brt_r            <= {BRT_BITS{1'b0}};
      ie_bwt_r            <= {BWT_BITS{1'b0}};
      ie_blk_end_bt_r     <= {BT_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      ie_blk_end_r        <= ie_blk_end_i   ;
      ie_blk_rd_end_r     <= ie_blk_rd_end_i;
      ie_blk_wr_end_r     <= ie_blk_wr_end_i;
      ie_rd_cnt_inc_r     <= ie_rd_cnt_inc_i;
      ie_wr_cnt_inc_r     <= ie_wr_cnt_inc_i;
      ie_brt_vld_r        <= ie_brt_vld_i   ;
      ie_bwt_vld_r        <= ie_bwt_vld_i   ;
      ie_brt_r            <= ie_brt_i       ;
      ie_bwt_r            <= ie_bwt_i       ;
      ie_blk_end_bt_r     <= ie_blk_end_bt_i;
   end
end

assign    ie_blk_end    =  ie_blk_end_r   ;
assign    ie_blk_rd_end =  ie_blk_rd_end_r;
assign    ie_blk_wr_end =  ie_blk_wr_end_r;
assign    ie_rd_cnt_inc =  ie_rd_cnt_inc_r;
assign    ie_wr_cnt_inc =  ie_wr_cnt_inc_r;
assign    ie_brt_vld    =  ie_brt_vld_r   ;
assign    ie_bwt_vld    =  ie_bwt_vld_r   ;
assign    ie_brt        =  ie_brt_r       ;
assign    ie_bwt        =  ie_bwt_r       ;
assign    ie_blk_end_bt =  ie_blk_end_bt_r;
//-----------------------------------------------------------------
// Read block priority
// if the block is high priorty, it could be terminated by incoming LPR/VPR
//    if rd_done =1, don't terminate; else terminate.
// if the block is not high priorty, it could be terminate by incoming HPR
//    if rd_done =1, don't terminate; else terminate.
// if any_wr=1 in the block, don't terminate even if read priority change, because that will cuase block collision between WR ECC and RD ECC
//-----------------------------------------------------------------
assign next_is_hpr  = (rxcmd_pri == 2'b10) ? 1'b1 : 1'b0;

assign rd_pri_chg   = ~any_wr & any_rd & ~re_done & rd_cmd & (r_blk_pri ^ next_is_hpr);

//-----------------------------------------------------------------
// For ECC Cache coherence issue (Address collision in Data path), 
// i.e. Encoding Write ECC before previous read data command is returned and decoded.
//
// Here to implement the proposal 1, which have a big performance impact
// HIF command: READ  ->   WRITE
// IH to CAM:   RE_B -> RD_E -> FLUSH CHN -> WD_E -> WE_B.
//              |------BT0-----------------|---BT1-------|
// FLUSH CHN means flush RD ECC and WR ECC cache, i.e.
//  if there are write before read/write collision, inject WE_B and set any_wr=0 to flush write, and set any_rd=0 to flush read
//  if therea are no write, only set any_rd=0 to flush read
// the performance impact:
//   1) more overhead command is inject
//   2) cuase TE block collision, becuase same ECC address with different BT.
//-----------------------------------------------------------------
wire [2:0]  offset_addr;
reg  [ACCESS_VEC_BITS-1:0] rd_access_vec;
wire [ACCESS_VEC_BITS-1:0] rd_access_vec_nxt;

assign offset_addr = ie_burst_num[2:0];

// if there are read in this block, and the incoming command is wr, and the wr address is matching any previous read address.
assign rd_wr_collision =  wr_cmd & wr_addr_match;

assign rd_access_vec_nxt = rd_access_vec | ie_access_vec;
// accumulator hif read address,
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      rd_access_vec    <= {ACCESS_VEC_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      if((override_or_rpc & rxcmd_ptc_vld) | chn_act_idle | flush_done | (rd_wr_collision & ~te_ih_retry_ie_cmd)) begin // clear vector after the collision write is acctpted; if block terminated by override or flush, clear the vector as well.
         rd_access_vec    <= {ACCESS_VEC_BITS{1'b0}};
      end else if(rd_cmd && ~ie_cmd_active) begin
         rd_access_vec    <= rd_access_vec_nxt;
      end
   end
end

assign wr_addr_match = rd_access_vec[offset_addr];
//-----------------------------------------------------------------
// Acculumate wdata mask full
//-----------------------------------------------------------------
// accumulator hif_cmd_wdata_mask_full
// Sample wdata_mask_full at the wr ecc slot, that is same as pervious wr/rmw command because it is latched.
// clean up at the end of block - i.e when incoming command override current block.
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      wdata_mask_full_vec <= {MASK_VEC_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      if((wr_cmd|rmw_cmd) && chn_vld && override_or_rpc_rwc) begin  //if a wr or rmw is overriding a channel, clean up wdata_mask_full_vec and recored the incoming's
         wdata_mask_full_vec <= ie_mask_full_vec;
      end else if(chn_act_idle | flush_done | (rd_cmd & override_or_rpc)) begin // clear vector if block active idle
         wdata_mask_full_vec <= {MASK_VEC_BITS{1'b0}};
//      end else if((wr_cmd|rmw_cmd) && ~te_ih_retry_ie_cmd) begin
      end else if((wr_cmd|rmw_cmd) && ~ie_cmd_active) begin
         wdata_mask_full_vec <= wdata_mask_full_vec | ie_mask_full_vec;
      end
   end
end

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * WRDATA_CYCLES)' found in module 'ih_ie_blk_chn_item'
//SJ: This coding style is acceptable and there is no plan to change it.
always @ (*) begin
   for (i=0; i<8; i=i+1 )
      if(i==offset_addr)
         ie_mask_full_vec[i*WRDATA_CYCLES +: WRDATA_CYCLES] = wdata_mask_full;
      else
         ie_mask_full_vec[i*WRDATA_CYCLES +: WRDATA_CYCLES] = {WRDATA_CYCLES{1'b0}};
end
//spyglass enable_block SelfDeterminedExpr-ML

always @ (*) begin
   for (i=0; i<ACCESS_VEC_BITS; i=i+1 )
      if(i==offset_addr) begin
         ie_access_vec[i] = 1'b1;
      end else begin
         ie_access_vec[i] = 1'b0;
      end
end


////wire [ACCESS_VEC_BITS/2-1:0] rd_access_half [0:1];
////assign rd_access_half[0] = rd_access_vec_nxt[ACCESS_VEC_BITS/2-1:0];
////assign rd_access_half[1] = rd_access_vec_nxt[ACCESS_VEC_BITS-1:ACCESS_VEC_BITS/2];

// below section to generate WR ECC command is BL16 or BL8 or BL4 or RMW.
// use hif_cmd_wdata_mask_full(wdata_mask_full_vec) to generate which ECC are full valid
// use hif_cmd access(wdata_access_vec) to generate which ECC are accessed (could be full valid, partial valid or no valid)

reg [MASK_VEC_BITS/2-1:0] mask_full_lower_half;
reg [MASK_VEC_BITS/2-1:0] mask_full_upper_half;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD:Self determined expression '(i * WRDATA_CYCLES)' found in module 'ih_ie_blk_chn_item'
//SJ: This coding style is acceptable and there is no plan to change it.
always @ (*)
begin
   for (i=0; i<8; i=i+1) begin
      {mask_full_lower_half[i*WRDATA_CYCLES/2 +: WRDATA_CYCLES/2], mask_full_upper_half[i*WRDATA_CYCLES/2 +: WRDATA_CYCLES/2]} = wdata_mask_full_vec[i*WRDATA_CYCLES +: WRDATA_CYCLES];
   end
end
//spyglass enable_block SelfDeterminedExpr-ML

// full block write indicate all the data are written within one block
// when bl16 & FBW, all the vector is valid that means full block access
// when bl8, half of vector is valid means full block access
assign is_full_blk_wr = 
                        (reg_ddrc_burst_rdwr==5'b00100)? (&mask_full_lower_half | &mask_full_upper_half) :  // half read in case of DRAM burst lenght=BL8
                                                         &wdata_mask_full_vec;


// full block read indicate all the offset address are read within one block
assign is_full_blk_rd = &rd_access_vec_nxt;

///assign rmw_ecc= 1'b0;
assign is_mwr = ~is_full_blk_wr;

//------------------------------------------------------------------
// generate ie_rd_vld, ie_wr_vld, ie_cmd_active
//------------------------------------------------------------------
assign ie_rd_vld = ((rd_cmd | rmw_cmd) & override_or_rpc_rwc ) || 
                   ((rd_cmd | rmw_cmd) & ~override_or_rpc_rwc & ~any_rd);

//ie_wr_vld is a input signal in V3.
assign ie_cmd_active = ie_rd_vld | ie_wr_vld | flush_req;

assign ie_rd_type =  ie_rd_vld     ? `IE_RD_TYPE_RE_B :
                     rxcmd_ptc_vld ? `IE_RD_TYPE_RD_E :
                                     `IE_RD_TYPE_RD_N ;

assign ie_wr_type =  ie_wr_vld     ? `IE_WR_TYPE_WE_BW: 
                     rxcmd_ptc_vld ? `IE_WR_TYPE_WD_E :
                                     `IE_WR_TYPE_WD_N ;
//------------------------------------------------------------------
// generate ECC address, and command option
//------------------------------------------------------------------

assign ie_rmwtype  = `MEMC_RMW_TYPE_NO_RMW;

assign ie_rd_length = (reg_ddrc_burst_rdwr==5'b00100) ? 2'b10 :  // half read in case of HBW or DRAM burst lenght=BL8
                                                        2'b00;
assign ie_rd_tag    = 'h0;

//critical_word MSB (COL3:2) is decided by AddressMap
// if burst_rdwr=BL16 & FBW, COL3:2 must be 0, since col[3:2] is mapping to HIF[3:2], and HIF[3:2] is set to 0
// if burst_rdwr=BL8 & FBW, COL3 could be 0 or 1, decided by HIF[3]. and even for RMW command, Inline ECC support partil read of RMW. COL2 is 0
// if burst_rdwr=BL8 & HBW, COL2 could be 0 or 1, decided by HIF[2]. COL3 is set to 1.
assign ie_critical_dword[`MEMC_WORD_BITS-1]   = ie_critical_dword_msb[1]; 
assign ie_critical_dword[`MEMC_WORD_BITS-2]   = ie_critical_dword_msb[0]; 
assign ie_critical_dword[`MEMC_WORD_BITS-3:0] = 2'b00; 

assign {
            ie_rank_num,
            ie_bg_bank_num,ie_page_num, ie_block_num
           ,ie_critical_dword_msb
       } =  rxcmd_ecc_addr;

assign ie_hi_pri = ie_wr_vld ? 2'b00 : rxcmd_pri;  // when ie_wr_vld is high, it could be a RMW command, set to LPR.


assign hif_lpr_credit_ie  = (((rd_cmd & ~next_is_hpr) | rmw_cmd) & first_rd_flag & ~te_ih_retry_ie_cmd) ; //reserve a LPR when the first read or RMW command, the LPR credit will be released by CAM.

assign hif_hpr_credit_ie  = ((rd_cmd & next_is_hpr) & first_rd_flag & ~te_ih_retry_ie_cmd);

`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON

// channel infor should be clean when chn_vld=0;
  property p_clr_chn_info_when_chn_idle;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
//       (chn_vld==0) |-> (~any_rd & ~any_wr & ~|wdata_mask_full_vec & ~|rd_access_vec & ~|r_ecc_addr );
       (chn_vld==0) |-> (~any_rd & ~any_wr & ~|r_ecc_addr );
  endproperty
  
  a_clr_chn_info_when_chn_idle: assert property (p_clr_chn_info_when_chn_idle)
      else $error("%m @ %t Error : when channel is IDLE state, all the channel information should be clean", $time);

  property p_clr_chn_info_when_chn_bcm_idle;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       $fell(chn_vld) |-> (~any_rd & ~any_wr & ~|wdata_mask_full_vec & ~|rd_access_vec & ~|r_ecc_addr );
  endproperty
  
  a_clr_chn_info_when_chn_bcm_idle: assert property (p_clr_chn_info_when_chn_bcm_idle)
      else $error("%m @ %t Error : when channel become IDLE state, all the channel information should be clean", $time);

// check rxcmd_ptc_vld should be 0 when slot of WR ECC (ie_wr_vld)
  property p_rxcmd_ptc_vld_not_in_we_slot;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (ie_wr_vld) |-> (~rxcmd_ptc_vld);
  endproperty
  
  a_rxcmd_ptc_vld_not_in_we_slot: assert property (p_rxcmd_ptc_vld_not_in_we_slot)
      else $error("%m @ %t Error : in write ecc slot rxcmd_ptc_vld cannot be assert", $time);

// check rxcmd_ptc_vld should be 0 when slot of flush
  property p_rxcmd_ptc_vld_not_in_flush;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (flush_req) |-> (~rxcmd_ptc_vld);
  endproperty
  
  a_rxcmd_ptc_vld_not_in_flush: assert property (p_rxcmd_ptc_vld_not_in_flush)
      else $error("%m @ %t Error : in flush slot rxcmd_ptc_vld cannot be assert", $time);

// check ECC address is same as block channel's ecc address if override is 0
  property p_incoming_ecc_eq_chn_ecc;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (rxcmd_ptc_vld & ~override) |-> (rxcmd_ecc_addr==r_ecc_addr);
  endproperty
  
  a_incoming_ecc_eq_chn_ecc: assert property (p_incoming_ecc_eq_chn_ecc)
      else $error("%m @ %t Error : incoming ecc address is not equal to channel's ecc address", $time);

// invalid case, incoming command without override, but any_rd=0 and any_wr=0.
  property p_any_rd_wr_wo_override;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (rxcmd_ptc_vld & ~override_or_rwc) |-> (any_rd|any_wr);
  endproperty
  
  a_any_rd_wr_wo_override: assert property (p_any_rd_wr_wo_override)
      else $error("%m @ %t Error : incoming command without override, but both any_rd and any_wr is 0", $time);

// check first_cmd and first_cmd_acpt
  property p_first_cmd_acpt;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (first_cmd & ~first_cmd_acpt) |=> (first_cmd & ~first_cmd_acpt) or (first_cmd & first_cmd_acpt);
  endproperty
  
  a_first_cmd_acpt : assert property (p_first_cmd_acpt)
      else $error("%m @ %t Error : first_cmd sequence is not correct", $time);

// check any_rd became to 0 when when a command with override_or_rwc assert
  property p_any_rd_0_rwc;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (rxcmd_ptc_vld & ~override & rd_wr_collision & ~te_ih_retry_ie_cmd) |=> ~any_rd;
  endproperty
  
  a_any_rd_0_rwc : assert property (p_any_rd_0_rwc)
      else $error("%m @ %t Error : any_rd should be 0 after rd write collision ", $time);


//don't need this assertion in V3, because WE_BW was injected after WD
////// check any_wr equal to 0 when when a command with override_or_rwc assert
////  property p_any_wr_0_rwc;
////    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
////       (rxcmd_ptc_vld & ~override & rd_wr_collision & ~te_ih_retry_ie_cmd) |-> ~any_wr;
////  endproperty
////  
////  a_any_wr_0_rwc : assert property (p_any_wr_0_rwc)
////      else $error("%m @ %t Error : any_wr should be 0 when rd write collision", $time);
`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
