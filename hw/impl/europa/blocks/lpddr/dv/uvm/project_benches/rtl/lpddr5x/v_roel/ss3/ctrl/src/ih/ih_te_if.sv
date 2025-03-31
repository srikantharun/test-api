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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_te_if.sv#4 $
// -------------------------------------------------------------------------
// Description:
//
// -------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module ih_te_if
import DWC_ddrctl_reg_pkg::*;
(
        bg_b16_addr_mode,
        reg_ddrc_ecc_type,

        // from core_if
        rxcmd_valid,
        rxcmd_type,
        rxcmd_token,
        rxcmd_autopre,
        rxcmd_pri,
        rxcmd_length,
        rxcmd_rd_latency,
        rxcmd_wr_latency,
        rxcmd_invalid_addr,

        // Address from address_map module
        am_rank,
        am_bg_bank,
        am_row,
        am_block,
        am_critical_dword,
        rxcmd_rmw_src,


        ie_cmd_active   ,
        rxcmd_ptc_vld   ,
        ecc_region_invalid,
        ie_rd_vld       , 
        ie_wr_vld       , 
        ie_rd_length    , 
        ie_rd_tag       , 
        ie_rmwtype      , 
        ie_hi_pri       , 
        ie_autopre      , 
        ie_rank_num,
        ie_bg_bank_num,
        ie_block_num,
        ie_page_num,
        ie_critical_dword,
        ih_te_eccap,
        am_eccap,
        // outputs for TE
        ih_te_rd_valid,
        ih_te_wr_valid,
        ih_wu_wr_valid,
        ih_te_rd_valid_addr_err,
        ih_te_wr_valid_addr_err,
        ih_te_rd_length,
        ih_te_rd_tag,
        ih_te_rmwtype,
        ih_te_rd_latency,
        ih_te_wr_latency,

        ih_te_hi_pri,
        ih_te_hi_pri_int,
        ih_te_autopre,
        ih_te_rank_num,
        ih_te_bankgroup_num,
        ih_te_bg_bank_num,
        ih_te_bank_num,
        ih_te_page_num,
        ih_te_block_num,
        ih_te_critical_dword,
        ih_wu_critical_dword
);

//------------------------------ PARAMETERS ------------------------------------

parameter       IH_TAG_WIDTH    = `MEMC_TAGBITS;                // width of token/tag field from core
parameter       CMD_LEN_BITS    = 1;                            // bits for command length, when used
parameter       RMW_TYPE_BITS   = 2;                            // 2 bits for RMW type
                                                                //  (partial write, scrub, or none)
parameter       CMD_TYPE_BITS   = 2;                            // any change will require RTL modifications in IC
parameter       RD_LATENCY_BITS = `UMCTL2_XPI_RQOS_TW;
parameter       WR_LATENCY_BITS = `UMCTL2_XPI_WQOS_TW;
parameter  RXCMD_SRC_WIDTH  = 1;

// 2-bit command type encodings
localparam CMD_TYPE_BLK_WR   = `MEMC_CMD_TYPE_BLK_WR;
localparam CMD_TYPE_BLK_RD   = `MEMC_CMD_TYPE_BLK_RD;
localparam CMD_TYPE_RMW      = `MEMC_CMD_TYPE_RMW;
localparam CMD_TYPE_RESERVED = `MEMC_CMD_TYPE_RESERVED;

// 2-bit RMW type encodings
localparam RMW_TYPE_PARTIAL_NBW = `MEMC_RMW_TYPE_PARTIAL_NBW;
localparam RMW_TYPE_RMW_CMD     = `MEMC_RMW_TYPE_RMW_CMD;
localparam RMW_TYPE_SCRUB       = `MEMC_RMW_TYPE_SCRUB;
localparam RMW_TYPE_NO_RMW      = `MEMC_RMW_TYPE_NO_RMW;

// 2-bit read priority encoding
localparam CMD_PRI_LPR    = `MEMC_CMD_PRI_LPR;
localparam CMD_PRI_VPR    = `MEMC_CMD_PRI_VPR;
localparam CMD_PRI_HPR    = `MEMC_CMD_PRI_HPR;
localparam CMD_PRI_XVPR   = `MEMC_CMD_PRI_XVPR;




input                                   bg_b16_addr_mode;
input                                   reg_ddrc_ecc_type;

input                                   rxcmd_valid;
input  [CMD_TYPE_BITS-1:0]              rxcmd_type;
input  [IH_TAG_WIDTH-1:0]               rxcmd_token;
input                                   rxcmd_autopre;
input  [1:0]                            rxcmd_pri;
input  [CMD_LEN_BITS-1:0]               rxcmd_length;
input  [RD_LATENCY_BITS-1:0]            rxcmd_rd_latency;
input  [WR_LATENCY_BITS-1:0]            rxcmd_wr_latency;
input                                   rxcmd_invalid_addr;

input [`MEMC_WORD_BITS-1:0]             am_critical_dword;
input [`MEMC_BLK_BITS-1:0]              am_block;
input [`MEMC_PAGE_BITS-1:0]             am_row;
input [`MEMC_BG_BANK_BITS-1:0]          am_bg_bank;
input [`UMCTL2_LRANK_BITS-1:0]          am_rank;
input [RXCMD_SRC_WIDTH-1:0]             rxcmd_rmw_src;


input                         ie_cmd_active ;
input                         rxcmd_ptc_vld ;
input                         ecc_region_invalid;
input                         ie_rd_vld     ;
input                         ie_wr_vld     ;
input  [CMD_LEN_BITS-1:0]     ie_rd_length  ;// <- full
input  [IH_TAG_WIDTH-1:0]     ie_rd_tag     ;// <- 0;
input  [RMW_TYPE_BITS-1:0]    ie_rmwtype    ;
input  [1:0]                  ie_hi_pri     ;
input                         ie_autopre    ;
input  [`UMCTL2_LRANK_BITS-1:0]   ie_rank_num;
input  [`MEMC_BG_BANK_BITS-1:0]   ie_bg_bank_num;
input  [`MEMC_BLK_BITS-1:0]       ie_block_num;
input  [`MEMC_PAGE_BITS-1:0]      ie_page_num;
input  [`MEMC_WORD_BITS-1:0]      ie_critical_dword;
output                                  ih_te_eccap;
input                                   am_eccap;
output                                  ih_te_rd_valid;
output                                  ih_te_wr_valid;
output                                  ih_wu_wr_valid;
output                                  ih_te_rd_valid_addr_err;    // High when detected RD/RMW with invalid address
output                                  ih_te_wr_valid_addr_err;    // High when detected WR/RMW with invalid address
output  [CMD_LEN_BITS-1:0]              ih_te_rd_length;
output  [IH_TAG_WIDTH-1:0]              ih_te_rd_tag;
output  [RMW_TYPE_BITS-1:0]             ih_te_rmwtype;
output  [1:0]                           ih_te_hi_pri;
output  [1:0]                           ih_te_hi_pri_int;
output                                  ih_te_autopre;

output  [RD_LATENCY_BITS-1:0]           ih_te_rd_latency;
output  [WR_LATENCY_BITS-1:0]           ih_te_wr_latency;

output  [`UMCTL2_LRANK_BITS -1:0]       ih_te_rank_num;
output  [`MEMC_BG_BITS-1:0]             ih_te_bankgroup_num;
output  [`MEMC_BG_BANK_BITS -1:0]       ih_te_bg_bank_num;
output  [`MEMC_BANK_BITS -1:0]          ih_te_bank_num;
output  [`MEMC_PAGE_BITS -1:0]          ih_te_page_num;
output  [`MEMC_BLK_BITS -1:0]           ih_te_block_num;
output  [`MEMC_WORD_BITS-1:0]           ih_te_critical_dword; 
output  [`MEMC_WORD_BITS-1:0]           ih_wu_critical_dword; 

wire                                    ih_te_rd_valid;
wire                                    ih_te_wr_valid;
wire                                    ih_wu_wr_valid;
wire                                    ih_te_rd_valid_addr_err;
wire                                    ih_te_wr_valid_addr_err;
wire    [CMD_LEN_BITS-1:0]              ih_te_rd_length;
wire    [IH_TAG_WIDTH-1:0]              ih_te_rd_tag;
wire    [RMW_TYPE_BITS-1:0]             ih_te_rmwtype;
wire    [RD_LATENCY_BITS-1:0]           ih_te_rd_latency;
wire    [WR_LATENCY_BITS-1:0]           ih_te_wr_latency;
wire    [1:0]                           ih_te_hi_pri;
wire    [1:0]                           ih_te_hi_pri_int;

wire                                    ih_te_autopre;

wire    [`UMCTL2_LRANK_BITS -1:0]       ih_te_rank_num;
wire    [`MEMC_BG_BITS-1:0]             ih_te_bankgroup_num;
wire  [`MEMC_BG_BANK_BITS -1:0]         ih_te_bg_bank_num;
wire  [`MEMC_BANK_BITS -1:0]            ih_te_bank_num;
wire  [`MEMC_PAGE_BITS -1:0]            ih_te_page_num;
wire  [`MEMC_BLK_BITS -1:0]             ih_te_block_num;
wire  [`MEMC_WORD_BITS-1:0]             ih_te_critical_dword; 
wire  [`MEMC_WORD_BITS-1:0]             ih_wu_critical_dword; 





wire    [CMD_LEN_BITS-1:0]              rd_length_core;

wire  [`MEMC_WORD_BITS-1:0]             am_critical_dword_rmw;
wire  [CMD_LEN_BITS-1:0]                rxcmd_length_rmw;


// rd_length value
// if cmd_type is READ, then rd_length = 0, when length=0 and rd_length != 0, when length !=0
// if cmd_type is RMW, then rd_length = 0 irrespective of the length field
assign  rxcmd_length_rmw  = {CMD_LEN_BITS{1'b0}};


assign  rd_length_core   = (rxcmd_valid && (((rxcmd_type == CMD_TYPE_BLK_RD) && (rxcmd_length == {CMD_LEN_BITS{1'b0}}))
                                                || (rxcmd_type == CMD_TYPE_RMW)
                        )) ? rxcmd_length_rmw : rxcmd_length;


wire ie_cmd_active_i = (reg_ddrc_ecc_type) ? ie_cmd_active : 1'b0;

// Assert ih_te_rd_valid_addr_err for every ih_te_rd_valid with invalid address
// For INLINE ECC configration, ie_cmd_active has higher priority than rxcmd_valid,
// if ie_cmd_active=1, don't generate valid_addr_err.(for example, the current rxcmd_valid is invalid address, but at this monment IE is inject ECC command for previous valid address)
// addl, No overhead ECC command for invalid address.
// In inline ECC mode, access ecc_region_* with ecc_region_*_lock=1 that will cuase invalid address error
wire invalid_addr;
assign invalid_addr             = 
                                   rxcmd_invalid_addr ||
                                   ecc_region_invalid ||
                                1'b0;
assign ih_te_rd_valid_addr_err  = 
                                  ie_cmd_active_i  ? 1'b0:
                                  (rxcmd_valid && invalid_addr &&
                                  ((rxcmd_type == CMD_TYPE_BLK_RD)
                                  || (rxcmd_type == CMD_TYPE_RMW)
                                  ));

// Assert ih_te_wr_valid_addr_err for every ih_te_wr_valid with invalid address
assign ih_te_wr_valid_addr_err  = 
                                  ie_cmd_active_i  ? 1'b0:
                                  (rxcmd_valid && invalid_addr &&
                                  ((rxcmd_type == CMD_TYPE_BLK_WR)
                                  || (rxcmd_type == CMD_TYPE_RMW)
                                  ));


wire wr_valid_rxcmd;
wire rd_valid_rxcmd;

// Assert rd_valid to TE when
// cmd_type is READ or RMW and there is no flow control from WU
// OR When SCRUB is on
assign  rd_valid_rxcmd          = (rxcmd_valid && 
                                  ((rxcmd_type == CMD_TYPE_BLK_RD)
                                  || (rxcmd_type == CMD_TYPE_RMW)
                                  ))
                                  ;

assign  ih_te_rd_valid  = 
                           ie_cmd_active_i  ? ie_rd_vld :
                           rd_valid_rxcmd;



// Assert wr_valid to TE when
// cmd_type is WRITE or RMW and there is no flow control from WU
// OR When SCRUB is on
assign  wr_valid_rxcmd          = (rxcmd_valid &&
                                  ((rxcmd_type == CMD_TYPE_BLK_WR)
                                  || (rxcmd_type == CMD_TYPE_RMW)
                                  ))
                                  ;

assign  ih_te_wr_valid  = 
                           ie_cmd_active_i  ? ie_wr_vld :
                           wr_valid_rxcmd;


// Don't tell Inline ECC overhead command to WU.
// MR will give wr_valid when a block end.
assign  ih_wu_wr_valid  = 
                           ie_cmd_active_i  ? 1'b0 :
                           wr_valid_rxcmd;


assign  ih_te_rd_length         = 
                                  ie_cmd_active_i ? ie_rd_length :
                                  rxcmd_valid   ? rd_length_core  : {CMD_LEN_BITS{1'b0}};

assign  ih_te_rd_tag         = 
                                  ie_cmd_active_i ? ie_rd_tag :
                                  rxcmd_valid   ?
                                  (rxcmd_type == CMD_TYPE_RMW)? {rxcmd_token[IH_TAG_WIDTH-1: RXCMD_SRC_WIDTH],rxcmd_rmw_src} :
                                  rxcmd_token : {IH_TAG_WIDTH{1'b0}};
                                  
// If the incoming cmd_type is RMW, then set to PARTIAL_NBW,
// if no cmd, set to scrub
// else keep it at NO_RMW
// MEMC_RMW_TYPE_RMW_CMD is not supported for now
assign  ih_te_rmwtype   =                                    ie_cmd_active_i  ? ie_rmwtype:
                                    (rxcmd_valid && (rxcmd_type == CMD_TYPE_RMW)) ? RMW_TYPE_PARTIAL_NBW :
                                RMW_TYPE_NO_RMW;

assign  ih_te_rank_num   = 
                          ie_cmd_active_i  ? ie_rank_num:
                           am_rank;

assign  ih_te_bg_bank_num =
                          ie_cmd_active_i  ? ie_bg_bank_num:
                          am_bg_bank;

assign  ih_te_page_num =
                          ie_cmd_active_i  ? ie_page_num:
                          am_row;                          

assign  ih_te_block_num =
                          ie_cmd_active_i  ? ie_block_num:
                          am_block;  
  


assign  ih_te_bankgroup_num = bg_b16_addr_mode ? ih_te_bg_bank_num[`MEMC_BG_BITS-1:0] : {`MEMC_BG_BITS{1'b0}};

assign  ih_te_bank_num      =                                     bg_b16_addr_mode ? (`MEMC_BANK_BITS)'(ih_te_bg_bank_num[`MEMC_BG_BANK_BITS-1:`MEMC_BG_BITS]) : 
                                     ih_te_bg_bank_num[`MEMC_BANK_BITS-1:0];



// send the critical word from the address mapper to TE when rxcmd_valid is present, else keep it 0
// the exception is RMW commands. when cmd_type is RMW, critical_word is forced to 0
// critical_word going to TE is used only during reads in the controller.
// during writes, the critical_word sent to WU will make the data to be correctly aligned.
//
// Inline ECC enabled in MEMC_BURST_LENGTH_16, 
//   if burst_rdwr=4'b0100 and HBW, read of RMW is quarter read, the critical_word could be 0,4,8,c to indicate which quater.
//   if burst_rdwr=4'b0100 or HBW, read of RMW is half read, the critical_word could be 0 or 8 to indicate which half.
//   otherwise, it is full read. (assume it is BL16 and FBW, don't support QBW)
assign  am_critical_dword_rmw  = {`MEMC_WORD_BITS{1'b0}};

assign  ih_te_critical_dword    = 
                                    ie_cmd_active_i  ? ie_critical_dword :
                                    (rxcmd_valid 
                                    && (rxcmd_type != CMD_TYPE_RMW)
                                    ) ? am_critical_dword : 
                                      am_critical_dword_rmw;



// send the critical word from the address mapper to TE when rxcmd_valid is present, else keep it 0
// this is needed even during RMW
assign  ih_wu_critical_dword    = 
                                 ie_cmd_active_i  ? ie_critical_dword :
                                 rxcmd_valid ? am_critical_dword : {`MEMC_WORD_BITS{1'b0}};



// this is the priority going out to TE. this is used by the global scheduler.
// the value of this priority is based on the incoming priroity as well as the register value
// CMD_PRI_LPR is used in the logic below, but it applies for Write priority as well.
// Since both LP Read and Write use the same encoding, it is ok to use it this way
assign  ih_te_hi_pri            = 
                                  ie_cmd_active_i ? ie_hi_pri:
                                  rxcmd_valid ? rxcmd_pri : CMD_PRI_LPR;

// this is the priority used for credit mechanism. this is the real priority that came in.
assign  ih_te_hi_pri_int        = 
                                  ie_cmd_active_i ? ie_hi_pri :
                                  rxcmd_valid ? rxcmd_pri : CMD_PRI_LPR;

assign ih_te_autopre            = 
                                  ie_cmd_active_i ? ie_autopre : 
                                  (rxcmd_ptc_vld & wr_valid_rxcmd) ? 1'b0 :  //don't assert autopre for a write to protect region, autopre will be asserted in it's WR ECC command
                                  rxcmd_valid && rxcmd_autopre;

assign ih_te_rd_latency         = rxcmd_rd_latency;

assign ih_te_wr_latency         = rxcmd_wr_latency;



assign ih_te_eccap =  ie_cmd_active_i  ? 1'b0 : // 0 for autogenerated command
                      am_eccap ;

`ifdef SNPS_ASSERT_ON

// `ifdef MEMC_SIDEBAND_ECC_AND_MEMC_USE_RMW
// 
// //--------------------------------------------------
// // scrub request is sent to TE
// // it gets retried
// // command comes in from core
// // scrub is withdrawn - core command serviced
// // scrub requested again and is served
// //--------------------------------------------------
// 
// cover_scrub_with_retry : cover property (@ (posedge co_ih_clk) disable iff (!core_ddrc_rstn)
//                                           (ih_te_wr_valid && ih_te_rd_valid && te_ih_retry) ##1 
//                                           (rxcmd_valid && (rxcmd_type == CMD_TYPE_BLK_RD) && ih_te_rd_valid && !ih_te_wr_valid && !te_ih_retry) ##1
//                                           (ih_te_wr_valid && ih_te_rd_valid && !te_ih_retry));
// 
// cover_scrub_with_retry_complex : cover property (@ (posedge co_ih_clk) disable iff (!core_ddrc_rstn)
//                                           (ih_te_wr_valid && ih_te_rd_valid && te_ih_retry) ##1 
//                                           (rxcmd_valid && (rxcmd_type == CMD_TYPE_BLK_RD) && ih_te_rd_valid && !ih_te_wr_valid && te_ih_retry)[*3] ##1
//                                           (rxcmd_valid && (rxcmd_type == CMD_TYPE_BLK_RD) && ih_te_rd_valid && !ih_te_wr_valid && !te_ih_retry) ##1
//                                           (ih_te_wr_valid && ih_te_rd_valid && te_ih_retry)[*2] ##1
//                                           (ih_te_wr_valid && ih_te_rd_valid && !te_ih_retry));
// 
// `endif //MEMC_SIDEBAND_ECC_AND_MEMC_USE_RMW

`endif // SNPS_ASSERT_ON



endmodule

