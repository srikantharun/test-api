//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/rd/rd_linkecc_decoder.sv#4 $
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
// ---    $Revision:
// -------------------------------------------------------------------------
// Description:
//    Read Link-ECC top module
// -------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module rd_linkecc_decoder
import DWC_ddrctl_reg_pkg::*;
#(
    parameter CMD_LEN_BITS        = 1
   ,parameter PHY_DATA_WIDTH      = 288
   ,parameter PHY_DBI_WIDTH       = 18
   ,parameter RMW_TYPE_BITS       = 2
   ,parameter RA_INFO_WIDTH       = 47
   ,parameter ECC_INFO_WIDTH      = 35
   ,parameter WU_INFO_WIDTH       = 47
   ,parameter IE_RD_TYPE_BITS     = `IE_RD_TYPE_BITS
   ,parameter IE_BURST_NUM_BITS   = 3
   ,parameter BT_BITS             = 4
   ,parameter WORD_BITS           = `MEMC_WORD_BITS
   ,parameter BLK_BITS            = `MEMC_BLK_BITS
   ,parameter CORE_MASK_WIDTH     = `MEMC_DFI_DATA_WIDTH/8
   ,parameter DRAM_BYTE_NUM       = `MEMC_DRAM_TOTAL_BYTE_NUM
   ,parameter LRANK_BITS          = `UMCTL2_LRANK_BITS
)
(
    input                          co_yy_clk
   ,input                          core_ddrc_rstn
   ,input                          ddrc_cg_en
   ,input                          reg_ddrc_rd_link_ecc_enable
   ,input                          reg_ddrc_rd_link_ecc_uncorr_cnt_clr
   ,input                          reg_ddrc_rd_link_ecc_uncorr_intr_clr
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Interrupt mask function is moved to APB module. This signal is not used.
   ,input                          reg_ddrc_rd_link_ecc_uncorr_intr_en
   ,input                          reg_ddrc_rd_link_ecc_corr_intr_en
//spyglass enable_block W240
   ,input                          reg_ddrc_rd_link_ecc_corr_cnt_clr
   ,input                          reg_ddrc_rd_link_ecc_corr_intr_clr
   ,input  [DRAM_BYTE_NUM-1:0]     reg_ddrc_linkecc_poison_byte_sel
   ,input                          reg_ddrc_linkecc_poison_rw
   ,input                          reg_ddrc_linkecc_poison_type
   ,input                          reg_ddrc_linkecc_poison_inject_en
   ,input  [ECC_INFO_WIDTH-1:0]    rt_rd_link_ecc_info
   ,input  [RD_LINK_ECC_ERR_RANK_SEL_WIDTH-1:0] reg_ddrc_rd_link_ecc_err_rank_sel
   ,input  [RD_LINK_ECC_ERR_BYTE_SEL_WIDTH-1:0] reg_ddrc_rd_link_ecc_err_byte_sel

   ,input  [PHY_DBI_WIDTH-1:0]     ph_rd_rdbi_n
   ,input  [PHY_DATA_WIDTH-1:0]    ph_rd_rdata
   ,input                          rt_rd_rd_valid
   ,input                          rt_rd_eod
   ,input  [CMD_LEN_BITS-1:0]      rt_rd_partial
   ,input  [RA_INFO_WIDTH-1:0]     rt_rd_ra_info
   ,input                          rt_rd_rd_mrr
   ,input                          rt_rd_rd_mrr_ext
   ,input                          rt_rd_rd_mrr_snoop
   ,input                          rt_rd_rd_mrr_sod
   ,input   [RMW_TYPE_BITS-1:0]    rt_rd_rmwtype
   ,input   [WU_INFO_WIDTH-1:0]    rt_rd_wu_info
   ,input                          rt_rd_rmw_word_sel
   ,input  [BT_BITS-1:0]           rt_rd_ie_bt
   ,input  [IE_RD_TYPE_BITS-1:0]   rt_rd_ie_rd_type
   ,input  [IE_BURST_NUM_BITS-1:0] rt_rd_ie_blk_burst_num
   ,input   [ECC_INFO_WIDTH-1:0]   rt_rd_ecc_info
   ,input   [WORD_BITS-1:0]        rt_rd_ecc_word
   ,input                          rt_rd_eccap
   ,input                          rt_rd_rd_addr_err

   ,output [PHY_DBI_WIDTH-1:0]     sel_ph_rd_rdbi_n
   ,output [PHY_DATA_WIDTH-1:0]    sel_ph_rd_rdata
   ,output                         sel_rt_rd_rd_valid
   ,output                         sel_rt_rd_eod
   ,output [CMD_LEN_BITS-1:0]      sel_rt_rd_partial
   ,output [RA_INFO_WIDTH-1:0]     sel_rt_rd_ra_info
   ,output                         sel_rt_rd_rd_mrr
   ,output                         sel_rt_rd_rd_mrr_ext
   ,output                         sel_rt_rd_rd_mrr_snoop
   ,output                         sel_rt_rd_rd_mrr_sod
   ,output  [RMW_TYPE_BITS-1:0]    sel_rt_rd_rmwtype
   ,output  [WU_INFO_WIDTH-1:0]    sel_rt_rd_wu_info
   ,output                         sel_rt_rd_rmw_word_sel
   ,output [BT_BITS-1:0]           sel_rt_rd_ie_bt
   ,output [IE_RD_TYPE_BITS-1:0]   sel_rt_rd_ie_rd_type
   ,output [IE_BURST_NUM_BITS-1:0] sel_rt_rd_ie_blk_burst_num
   ,output  [ECC_INFO_WIDTH-1:0]   sel_rt_rd_ecc_info
   ,output  [WORD_BITS-1:0]        sel_rt_rd_ecc_word
   ,output                         sel_rt_rd_eccap
   ,output                         sel_rt_rd_rd_addr_err
   ,output                                        ddrc_reg_rd_linkecc_poison_complete
   ,output [RD_LINK_ECC_UNCORR_CNT_WIDTH    -1:0] ddrc_reg_rd_link_ecc_uncorr_cnt
   ,output [RD_LINK_ECC_CORR_CNT_WIDTH      -1:0] ddrc_reg_rd_link_ecc_corr_cnt
   ,output [RD_LINK_ECC_ERR_SYNDROME_WIDTH  -1:0] ddrc_reg_rd_link_ecc_err_syndrome
   ,output [RD_LINK_ECC_UNCORR_ERR_INT_WIDTH-1:0] ddrc_reg_rd_link_ecc_uncorr_err_int
   ,output [RD_LINK_ECC_CORR_ERR_INT_WIDTH  -1:0] ddrc_reg_rd_link_ecc_corr_err_int
   ,output                                        rd_link_ecc_uncorr_err

   ,output [LINK_ECC_CORR_RANK_WIDTH-1:0]          ddrc_reg_link_ecc_corr_rank
   ,output [LINK_ECC_CORR_BG_WIDTH-1:0]            ddrc_reg_link_ecc_corr_bg
   ,output [LINK_ECC_CORR_BANK_WIDTH-1:0]          ddrc_reg_link_ecc_corr_bank
   ,output [LINK_ECC_CORR_ROW_WIDTH-1:0]           ddrc_reg_link_ecc_corr_row
   ,output [LINK_ECC_CORR_COL_WIDTH-1:0]           ddrc_reg_link_ecc_corr_col
   ,output [LINK_ECC_UNCORR_RANK_WIDTH-1:0]        ddrc_reg_link_ecc_uncorr_rank
   ,output [LINK_ECC_UNCORR_BG_WIDTH-1:0]          ddrc_reg_link_ecc_uncorr_bg
   ,output [LINK_ECC_UNCORR_BANK_WIDTH-1:0]        ddrc_reg_link_ecc_uncorr_bank
   ,output [LINK_ECC_UNCORR_ROW_WIDTH-1:0]         ddrc_reg_link_ecc_uncorr_row
   ,output [LINK_ECC_UNCORR_COL_WIDTH-1:0]         ddrc_reg_link_ecc_uncorr_col
);

//---------------------------- PARAMETERS --------------------------------------
parameter  PHY_MASK_WIDTH = PHY_DATA_WIDTH/8;

localparam MAX_NUM_BYTE = 8;
localparam DQ_WIDTH  = `MEMC_DRAM_DATA_WIDTH;
localparam DMI_WIDTH = `MEMC_DRAM_DATA_WIDTH/8;
localparam NUM_BYTE  = `MEMC_DRAM_DATA_WIDTH/8;


//--------------------------------- WIRES --------------------------------------
reg  [PHY_DBI_WIDTH-1:0]     ph_rd_rdbi_n_1d;
reg  [PHY_DATA_WIDTH-1:0]    ph_rd_rdata_1d;
reg                          rt_rd_rd_valid_1d;
reg                          rt_rd_eod_1d;
reg  [CMD_LEN_BITS-1:0]      rt_rd_partial_1d;
reg  [RA_INFO_WIDTH-1:0]     rt_rd_ra_info_1d;
reg                          rt_rd_rd_mrr_1d;
reg                          rt_rd_rd_mrr_ext_1d;
reg                          rt_rd_rd_mrr_snoop_1d;
reg                          rt_rd_rd_mrr_sod_1d;
reg   [RMW_TYPE_BITS-1:0]    rt_rd_rmwtype_1d;
reg   [WU_INFO_WIDTH-1:0]    rt_rd_wu_info_1d;
reg                          rt_rd_rmw_word_sel_1d;
reg  [BT_BITS-1:0]           rt_rd_ie_bt_1d;
reg  [IE_RD_TYPE_BITS-1:0]   rt_rd_ie_rd_type_1d;
reg  [IE_BURST_NUM_BITS-1:0] rt_rd_ie_blk_burst_num_1d;
reg   [ECC_INFO_WIDTH-1:0]   rt_rd_ecc_info_1d;
reg   [WORD_BITS-1:0]        rt_rd_ecc_word_1d;
reg                          rt_rd_eccap_1d;
reg                          rt_rd_rd_addr_err_1d;


reg  [PHY_DBI_WIDTH-1:0]     ph_rd_rdbi_n_2d;
reg  [PHY_DATA_WIDTH-1:0]    ph_rd_rdata_2d;
reg                          rt_rd_rd_valid_2d;
reg                          rt_rd_eod_2d;
reg  [CMD_LEN_BITS-1:0]      rt_rd_partial_2d;
reg  [RA_INFO_WIDTH-1:0]     rt_rd_ra_info_2d;
reg                          rt_rd_rd_mrr_2d;
reg                          rt_rd_rd_mrr_ext_2d;
reg                          rt_rd_rd_mrr_snoop_2d;
reg                          rt_rd_rd_mrr_sod_2d;
reg   [RMW_TYPE_BITS-1:0]    rt_rd_rmwtype_2d;
reg   [WU_INFO_WIDTH-1:0]    rt_rd_wu_info_2d;
reg                          rt_rd_rmw_word_sel_2d;
reg  [BT_BITS-1:0]           rt_rd_ie_bt_2d;
reg  [IE_RD_TYPE_BITS-1:0]   rt_rd_ie_rd_type_2d;
reg  [IE_BURST_NUM_BITS-1:0] rt_rd_ie_blk_burst_num_2d;
reg   [ECC_INFO_WIDTH-1:0]   rt_rd_ecc_info_2d;
reg   [WORD_BITS-1:0]        rt_rd_ecc_word_2d;
reg                          rt_rd_eccap_2d;
reg                          rt_rd_rd_addr_err_2d;

wire [1:0]                   rt_rd_rank;

wire                         linkecc_chk_en;

wire [PHY_DATA_WIDTH*2-1:0]  ph_rd_rdata_w;
wire [PHY_DBI_WIDTH*2 -1:0]  ph_rd_rdbi_n_w;
wire [PHY_DATA_WIDTH-1:0]    ph_rd_rdata_1d_w;
reg  [PHY_DATA_WIDTH-1:0]    corr_rdata_1d;

wire [PHY_DATA_WIDTH*2-1:0]  corr_rdata;
wire [MAX_NUM_BYTE    -1:0]  corr_err_byte;
wire [MAX_NUM_BYTE    -1:0]  uncorr_err_byte;
reg                          uncorr_err_byte_any_d[1:2];

wire [RD_LINK_ECC_ERR_SYNDROME_WIDTH-1:0]  syndrome_byte              [MAX_NUM_BYTE-1:0];

wire [RD_LINK_ECC_ERR_SYNDROME_WIDTH-1:0]  syndrome_byte_rank0        [MAX_NUM_BYTE-1:0];
wire [RD_LINK_ECC_CORR_CNT_WIDTH    -1:0]  corr_err_cnt_byte_rank0    [MAX_NUM_BYTE-1:0];
wire [RD_LINK_ECC_UNCORR_CNT_WIDTH  -1:0]  uncorr_err_cnt_byte_rank0  [MAX_NUM_BYTE-1:0];
wire [MAX_NUM_BYTE                  -1:0]  corr_err_intr_byte_rank0;
wire [MAX_NUM_BYTE                  -1:0]  uncorr_err_intr_byte_rank0;
wire                                       uncorr_err_intr_rank0;
wire                                       corr_err_intr_rank0;

wire [RD_LINK_ECC_ERR_SYNDROME_WIDTH-1:0]  syndrome_byte_rank1        [MAX_NUM_BYTE-1:0];
wire [RD_LINK_ECC_CORR_CNT_WIDTH    -1:0]  corr_err_cnt_byte_rank1    [MAX_NUM_BYTE-1:0];
wire [RD_LINK_ECC_UNCORR_CNT_WIDTH  -1:0]  uncorr_err_cnt_byte_rank1  [MAX_NUM_BYTE-1:0];
wire [MAX_NUM_BYTE                  -1:0]  corr_err_intr_byte_rank1;
wire [MAX_NUM_BYTE                  -1:0]  uncorr_err_intr_byte_rank1;
wire                                       uncorr_err_intr_rank1;
wire                                       corr_err_intr_rank1;

reg  [ECC_INFO_WIDTH-1:0]                  link_ecc_corr_info;
reg  [ECC_INFO_WIDTH-1:0]                  link_ecc_uncorr_info;


//----------------------- COMBINATORIAL ASSIGNMENTS ----------------------------

// Select all output signals. If link-ECC is disabled, all signals should be bypassed.
assign sel_ph_rd_rdbi_n           = (reg_ddrc_rd_link_ecc_enable)? ph_rd_rdbi_n_2d            : ph_rd_rdbi_n           ;
assign sel_ph_rd_rdata            = (reg_ddrc_rd_link_ecc_enable)? ph_rd_rdata_2d             : ph_rd_rdata            ;
assign sel_rt_rd_rd_valid         = (reg_ddrc_rd_link_ecc_enable)? rt_rd_rd_valid_2d          : rt_rd_rd_valid         ;
assign sel_rt_rd_eod              = (reg_ddrc_rd_link_ecc_enable)? rt_rd_eod_2d               : rt_rd_eod              ;
assign sel_rt_rd_partial          = (reg_ddrc_rd_link_ecc_enable)? rt_rd_partial_2d           : rt_rd_partial          ;
assign sel_rt_rd_ra_info          = (reg_ddrc_rd_link_ecc_enable)? rt_rd_ra_info_2d           : rt_rd_ra_info          ;
assign sel_rt_rd_rd_mrr           = (reg_ddrc_rd_link_ecc_enable)? rt_rd_rd_mrr_2d            : rt_rd_rd_mrr           ;
assign sel_rt_rd_rd_mrr_ext       = (reg_ddrc_rd_link_ecc_enable)? rt_rd_rd_mrr_ext_2d        : rt_rd_rd_mrr_ext       ;
assign sel_rt_rd_rd_mrr_snoop     = (reg_ddrc_rd_link_ecc_enable)? rt_rd_rd_mrr_snoop_2d      : rt_rd_rd_mrr_snoop     ;
assign sel_rt_rd_rd_mrr_sod       = (reg_ddrc_rd_link_ecc_enable)? rt_rd_rd_mrr_sod_2d        : rt_rd_rd_mrr_sod       ;
assign sel_rt_rd_rmwtype          = (reg_ddrc_rd_link_ecc_enable)? rt_rd_rmwtype_2d           : rt_rd_rmwtype          ;
assign sel_rt_rd_wu_info          = (reg_ddrc_rd_link_ecc_enable)? rt_rd_wu_info_2d           : rt_rd_wu_info          ;
assign sel_rt_rd_rmw_word_sel     = (reg_ddrc_rd_link_ecc_enable)? rt_rd_rmw_word_sel_2d      : rt_rd_rmw_word_sel     ;
assign sel_rt_rd_ie_bt            = (reg_ddrc_rd_link_ecc_enable)? rt_rd_ie_bt_2d             : rt_rd_ie_bt            ;
assign sel_rt_rd_ie_rd_type       = (reg_ddrc_rd_link_ecc_enable)? rt_rd_ie_rd_type_2d        : rt_rd_ie_rd_type       ;
assign sel_rt_rd_ie_blk_burst_num = (reg_ddrc_rd_link_ecc_enable)? rt_rd_ie_blk_burst_num_2d  : rt_rd_ie_blk_burst_num ;
assign sel_rt_rd_ecc_info         = (reg_ddrc_rd_link_ecc_enable)? rt_rd_ecc_info_2d          : rt_rd_ecc_info         ;
assign sel_rt_rd_ecc_word         = (reg_ddrc_rd_link_ecc_enable)? rt_rd_ecc_word_2d          : rt_rd_ecc_word         ;
assign sel_rt_rd_eccap            = (reg_ddrc_rd_link_ecc_enable)? rt_rd_eccap_2d             : rt_rd_eccap            ;
assign sel_rt_rd_rd_addr_err      = (reg_ddrc_rd_link_ecc_enable)? rt_rd_rd_addr_err_2d       : rt_rd_rd_addr_err      ;



// Retiming all input signals.
always@(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
      {ph_rd_rdbi_n_2d          ,ph_rd_rdbi_n_1d          } <= {PHY_DBI_WIDTH*2{1'b0}}; 
      {ph_rd_rdata_2d           ,ph_rd_rdata_1d           } <= {PHY_DATA_WIDTH*2{1'b0}}; 
      {rt_rd_rd_valid_2d        ,rt_rd_rd_valid_1d        } <= {1*2{1'b0}}; 
      {rt_rd_eod_2d             ,rt_rd_eod_1d             } <= {1*2{1'b0}}; 
      {rt_rd_partial_2d         ,rt_rd_partial_1d         } <= {CMD_LEN_BITS*2{1'b0}}; 
      {rt_rd_ra_info_2d         ,rt_rd_ra_info_1d         } <= {RA_INFO_WIDTH*2{1'b0}}; 
      {rt_rd_rd_mrr_2d          ,rt_rd_rd_mrr_1d          } <= {1*2{1'b0}}; 
      {rt_rd_rd_mrr_ext_2d      ,rt_rd_rd_mrr_ext_1d      } <= {1*2{1'b0}}; 
      {rt_rd_rd_mrr_snoop_2d    ,rt_rd_rd_mrr_snoop_1d    } <= {1*2{1'b0}}; 
      {rt_rd_rd_mrr_sod_2d      ,rt_rd_rd_mrr_sod_1d      } <= {1*2{1'b0}}; 
      {rt_rd_rmwtype_2d         ,rt_rd_rmwtype_1d         } <= {RMW_TYPE_BITS*2{1'b0}}; 
      {rt_rd_wu_info_2d         ,rt_rd_wu_info_1d         } <= {WU_INFO_WIDTH*2{1'b0}}; 
      {rt_rd_rmw_word_sel_2d    ,rt_rd_rmw_word_sel_1d    } <= {1*2{1'b0}}; 
      {rt_rd_ie_bt_2d           ,rt_rd_ie_bt_1d           } <= {BT_BITS*2{1'b0}}; 
      {rt_rd_ie_rd_type_2d      ,rt_rd_ie_rd_type_1d      } <= {IE_RD_TYPE_BITS*2{1'b0}}; 
      {rt_rd_ie_blk_burst_num_2d,rt_rd_ie_blk_burst_num_1d} <= {IE_BURST_NUM_BITS*2{1'b0}}; 
      {rt_rd_ecc_info_2d        ,rt_rd_ecc_info_1d        } <= {ECC_INFO_WIDTH*2{1'b0}}; 
      {rt_rd_ecc_word_2d        ,rt_rd_ecc_word_1d        } <= {WORD_BITS*2{1'b0}}; 
      {rt_rd_eccap_2d           ,rt_rd_eccap_1d           } <= {1*2{1'b0}}; 
      {rt_rd_rd_addr_err_2d     ,rt_rd_rd_addr_err_1d     } <= {1*2{1'b0}}; 
  end
  else if(ddrc_cg_en) begin
      {ph_rd_rdbi_n_2d          ,ph_rd_rdbi_n_1d          } <= {ph_rd_rdbi_n_1d          ,ph_rd_rdbi_n          };
      {ph_rd_rdata_2d           ,ph_rd_rdata_1d           } <= {ph_rd_rdata_1d_w         ,ph_rd_rdata           };
      {rt_rd_rd_valid_2d        ,rt_rd_rd_valid_1d        } <= {rt_rd_rd_valid_1d        ,rt_rd_rd_valid        };
      {rt_rd_eod_2d             ,rt_rd_eod_1d             } <= {rt_rd_eod_1d             ,rt_rd_eod             };
      {rt_rd_partial_2d         ,rt_rd_partial_1d         } <= {rt_rd_partial_1d         ,rt_rd_partial         };
      {rt_rd_ra_info_2d         ,rt_rd_ra_info_1d         } <= {rt_rd_ra_info_1d         ,rt_rd_ra_info         };
      {rt_rd_rd_mrr_2d          ,rt_rd_rd_mrr_1d          } <= {rt_rd_rd_mrr_1d          ,rt_rd_rd_mrr          };
      {rt_rd_rd_mrr_ext_2d      ,rt_rd_rd_mrr_ext_1d      } <= {rt_rd_rd_mrr_ext_1d      ,rt_rd_rd_mrr_ext      };
      {rt_rd_rd_mrr_snoop_2d    ,rt_rd_rd_mrr_snoop_1d    } <= {rt_rd_rd_mrr_snoop_1d    ,rt_rd_rd_mrr_snoop    };
      {rt_rd_rd_mrr_sod_2d      ,rt_rd_rd_mrr_sod_1d      } <= {rt_rd_rd_mrr_sod_1d      ,rt_rd_rd_mrr_sod      };
      {rt_rd_rmwtype_2d         ,rt_rd_rmwtype_1d         } <= {rt_rd_rmwtype_1d         ,rt_rd_rmwtype         };
      {rt_rd_wu_info_2d         ,rt_rd_wu_info_1d         } <= {rt_rd_wu_info_1d         ,rt_rd_wu_info         };
      {rt_rd_rmw_word_sel_2d    ,rt_rd_rmw_word_sel_1d    } <= {rt_rd_rmw_word_sel_1d    ,rt_rd_rmw_word_sel    };
      {rt_rd_ie_bt_2d           ,rt_rd_ie_bt_1d           } <= {rt_rd_ie_bt_1d           ,rt_rd_ie_bt           };
      {rt_rd_ie_rd_type_2d      ,rt_rd_ie_rd_type_1d      } <= {rt_rd_ie_rd_type_1d      ,rt_rd_ie_rd_type      };
      {rt_rd_ie_blk_burst_num_2d,rt_rd_ie_blk_burst_num_1d} <= {rt_rd_ie_blk_burst_num_1d,rt_rd_ie_blk_burst_num};
      {rt_rd_ecc_info_2d        ,rt_rd_ecc_info_1d        } <= {rt_rd_ecc_info_1d        ,rt_rd_ecc_info        };
      {rt_rd_ecc_word_2d        ,rt_rd_ecc_word_1d        } <= {rt_rd_ecc_word_1d        ,rt_rd_ecc_word        };
      {rt_rd_eccap_2d           ,rt_rd_eccap_1d           } <= {rt_rd_eccap_1d           ,rt_rd_eccap           };
      {rt_rd_rd_addr_err_2d     ,rt_rd_rd_addr_err_1d     } <= {rt_rd_rd_addr_err_1d     ,rt_rd_rd_addr_err     };
  end
end


always@(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
      corr_rdata_1d <= {PHY_DATA_WIDTH{1'b0}};
  end
  else if(ddrc_cg_en) begin
      corr_rdata_1d <= corr_rdata[PHY_DATA_WIDTH +:PHY_DATA_WIDTH];
  end
end

wire    mrr;
assign mrr = rt_rd_rd_mrr | rt_rd_rd_mrr_ext | rt_rd_rd_mrr_snoop;

reg     mrr_1d;
always@(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
     mrr_1d <= 1'b0;
  end
  else if(ddrc_cg_en) begin
     mrr_1d <= mrr;
  end
end

assign linkecc_chk_en   = reg_ddrc_rd_link_ecc_enable & (
                           rt_rd_eod
                        );
assign ph_rd_rdata_w    = (linkecc_chk_en)? {ph_rd_rdata ,ph_rd_rdata_1d } : {PHY_DATA_WIDTH*2{1'b0}};
assign ph_rd_rdbi_n_w   = (linkecc_chk_en)? {ph_rd_rdbi_n,ph_rd_rdbi_n_1d} : {PHY_DBI_WIDTH *2{1'b0}};

assign ph_rd_rdata_1d_w = (~reg_ddrc_rd_link_ecc_enable || mrr_1d)? ph_rd_rdata_1d :
                          (linkecc_chk_en)? corr_rdata[0 +:PHY_DATA_WIDTH] : corr_rdata_1d;


// Poison complete
reg                        linkecc_poison_inject_complete;
wire                       linkecc_poison_tmg;
reg                        linkecc_poison_inject_en;
wire [DRAM_BYTE_NUM-1:0]   linkecc_poison_byte_sel;



assign linkecc_poison_tmg        = linkecc_poison_inject_en & (reg_ddrc_linkecc_poison_rw) & (
                                    rt_rd_eod
                                 );
assign linkecc_poison_byte_sel   = (linkecc_poison_tmg)? reg_ddrc_linkecc_poison_byte_sel : {DRAM_BYTE_NUM{1'b0}};

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
    if (~core_ddrc_rstn) begin
        linkecc_poison_inject_complete <= 1'b0;
    end else if(!reg_ddrc_linkecc_poison_inject_en) begin
        linkecc_poison_inject_complete <= 1'b0;
    end else if(reg_ddrc_linkecc_poison_inject_en && linkecc_poison_tmg) begin
        linkecc_poison_inject_complete <= 1'b1;
    end
end
assign ddrc_reg_rd_linkecc_poison_complete = linkecc_poison_inject_complete;

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
    if (~core_ddrc_rstn) begin
        linkecc_poison_inject_en <= 1'b0;
    end else if(!reg_ddrc_linkecc_poison_inject_en || linkecc_poison_inject_complete || linkecc_poison_tmg) begin
        linkecc_poison_inject_en <= 1'b0;
    end else if(!linkecc_poison_inject_complete && reg_ddrc_linkecc_poison_inject_en) begin
        linkecc_poison_inject_en <= 1'b1;
    end
end


assign rt_rd_rank = {1'b0,rt_rd_link_ecc_info[ECC_INFO_WIDTH-LRANK_BITS+:LRANK_BITS]};


// Indicate uncorrectable Link-ECC Error to HIF/AXI interface
// Assuming that uncorr_err_byte is always deasserted while data is not read.
// Since its driver 'rd_linkecc_secded' takes ph_rd_rdata_w and ph_rd_rdbi_n_w as input which are masked out while idle, just OK.
always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
  // Extend uncorr flag;{for BL 15-8 output      , for BL 7-0 output       }  All of BL 15-0 (or 31-16) should assert slverr when uncorr err is detected
  if (~core_ddrc_rstn) begin
    {uncorr_err_byte_any_d[2], uncorr_err_byte_any_d[1]} <= 2'b0;
  end else begin
    {uncorr_err_byte_any_d[2], uncorr_err_byte_any_d[1]} <= {uncorr_err_byte_any_d[1], |uncorr_err_byte};
  end
end
assign rd_link_ecc_uncorr_err              = uncorr_err_byte_any_d[2] || uncorr_err_byte_any_d[1];

assign ddrc_reg_rd_link_ecc_uncorr_err_int = {2'b00,uncorr_err_intr_rank1,uncorr_err_intr_rank0};
assign ddrc_reg_rd_link_ecc_corr_err_int   = {2'b00,corr_err_intr_rank1  ,corr_err_intr_rank0};

assign uncorr_err_intr_rank0 = |uncorr_err_intr_byte_rank0;
assign uncorr_err_intr_rank1 = |uncorr_err_intr_byte_rank1;

assign corr_err_intr_rank0 = |corr_err_intr_byte_rank0;
assign corr_err_intr_rank1 = |corr_err_intr_byte_rank1;

// Select Error status
assign ddrc_reg_rd_link_ecc_uncorr_cnt =
    (reg_ddrc_rd_link_ecc_err_rank_sel==2'b01)? uncorr_err_cnt_byte_rank1[reg_ddrc_rd_link_ecc_err_byte_sel] :
                                               uncorr_err_cnt_byte_rank0[reg_ddrc_rd_link_ecc_err_byte_sel];

assign ddrc_reg_rd_link_ecc_corr_cnt =
    (reg_ddrc_rd_link_ecc_err_rank_sel==2'b01)? corr_err_cnt_byte_rank1[reg_ddrc_rd_link_ecc_err_byte_sel] :
                                               corr_err_cnt_byte_rank0[reg_ddrc_rd_link_ecc_err_byte_sel];

assign ddrc_reg_rd_link_ecc_err_syndrome =
    (reg_ddrc_rd_link_ecc_err_rank_sel==2'b01)? syndrome_byte_rank1[reg_ddrc_rd_link_ecc_err_byte_sel] :
                                               syndrome_byte_rank0[reg_ddrc_rd_link_ecc_err_byte_sel];



// Status Link-ECC
genvar STAT_BYTES_LECC;
generate
  for (STAT_BYTES_LECC=0; STAT_BYTES_LECC<MAX_NUM_BYTE; STAT_BYTES_LECC=STAT_BYTES_LECC+1) begin : stat_lecc
    if(STAT_BYTES_LECC<NUM_BYTE) begin: RD_LNKECC_STAT_en
       reg  [RD_LINK_ECC_CORR_CNT_WIDTH    -1:0]    corr_err_cnt_rank0;
       reg  [RD_LINK_ECC_UNCORR_CNT_WIDTH  -1:0]    uncorr_err_cnt_rank0;
       reg  [RD_LINK_ECC_ERR_SYNDROME_WIDTH-1:0]    syndrome_rank0;
       reg                                          corr_err_intr_rank0;
       reg                                          uncorr_err_intr_rank0;

       // Link-ECC  1-bit error count
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           corr_err_cnt_rank0 <= {RD_LINK_ECC_CORR_CNT_WIDTH{1'b0}};
         end else if(reg_ddrc_rd_link_ecc_corr_cnt_clr) begin
           corr_err_cnt_rank0 <= {RD_LINK_ECC_CORR_CNT_WIDTH{1'b0}};
         end else if(rt_rd_rank==2'b00 && corr_err_byte[STAT_BYTES_LECC] && corr_err_cnt_rank0!={RD_LINK_ECC_CORR_CNT_WIDTH{1'b1}}) begin
           corr_err_cnt_rank0 <= corr_err_cnt_rank0 + 8'd1;
         end
       end

       // Link-ECC 1-bit error interrupt
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           corr_err_intr_rank0 <= 1'b0;
         end else if(reg_ddrc_rd_link_ecc_corr_intr_clr) begin
           corr_err_intr_rank0 <= 1'b0;
         end else if(rt_rd_rank==2'b00 && corr_err_byte[STAT_BYTES_LECC]) begin
           corr_err_intr_rank0 <= 1'b1;
         end
       end

       // Stored 1-bit error syndrome
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           syndrome_rank0 <= {RD_LINK_ECC_ERR_SYNDROME_WIDTH{1'b0}};
         end else if(rt_rd_rank==2'b00 && corr_err_byte[STAT_BYTES_LECC]) begin
           syndrome_rank0 <= syndrome_byte[STAT_BYTES_LECC];
         end
       end

       // Link-ECC  2-bit error count
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           uncorr_err_cnt_rank0 <= {RD_LINK_ECC_UNCORR_CNT_WIDTH{1'b0}};
         end else if(reg_ddrc_rd_link_ecc_uncorr_cnt_clr) begin
           uncorr_err_cnt_rank0 <= {RD_LINK_ECC_UNCORR_CNT_WIDTH{1'b0}};
         end else if(rt_rd_rank==2'b00 && uncorr_err_byte[STAT_BYTES_LECC] && uncorr_err_cnt_rank0!={RD_LINK_ECC_UNCORR_CNT_WIDTH{1'b1}}) begin
           uncorr_err_cnt_rank0 <= uncorr_err_cnt_rank0 + 8'd1;
         end
       end

       // Link-ECC 2-bit error interrupt
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           uncorr_err_intr_rank0 <= 1'b0;
         end else if(reg_ddrc_rd_link_ecc_uncorr_intr_clr) begin
           uncorr_err_intr_rank0 <= 1'b0;
         end else if(rt_rd_rank==2'b00 && uncorr_err_byte[STAT_BYTES_LECC]) begin
           uncorr_err_intr_rank0 <= 1'b1;
         end
       end

       assign uncorr_err_cnt_byte_rank0[STAT_BYTES_LECC]  = uncorr_err_cnt_rank0;
       assign corr_err_cnt_byte_rank0[STAT_BYTES_LECC]    = corr_err_cnt_rank0;
       assign syndrome_byte_rank0[STAT_BYTES_LECC]        = syndrome_rank0;
       assign uncorr_err_intr_byte_rank0[STAT_BYTES_LECC] = uncorr_err_intr_rank0;
       assign corr_err_intr_byte_rank0[STAT_BYTES_LECC]   = corr_err_intr_rank0;

       reg  [RD_LINK_ECC_CORR_CNT_WIDTH    -1:0]    corr_err_cnt_rank1;
       reg  [RD_LINK_ECC_UNCORR_CNT_WIDTH  -1:0]    uncorr_err_cnt_rank1;
       reg  [RD_LINK_ECC_ERR_SYNDROME_WIDTH-1:0]    syndrome_rank1;
       reg                                          corr_err_intr_rank1;
       reg                                          uncorr_err_intr_rank1;

       // Link-ECC  1-bit error count
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           corr_err_cnt_rank1 <= {RD_LINK_ECC_CORR_CNT_WIDTH{1'b0}};
         end else if(reg_ddrc_rd_link_ecc_corr_cnt_clr) begin
           corr_err_cnt_rank1 <= {RD_LINK_ECC_CORR_CNT_WIDTH{1'b0}};
         end else if(rt_rd_rank==2'b01 && corr_err_byte[STAT_BYTES_LECC] && corr_err_cnt_rank1!={RD_LINK_ECC_CORR_CNT_WIDTH{1'b1}}) begin
           corr_err_cnt_rank1 <= corr_err_cnt_rank1 + 8'd1;
         end
       end

       // Link-ECC 1-bit error interrupt
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           corr_err_intr_rank1 <= 1'b0;
         end else if(reg_ddrc_rd_link_ecc_corr_intr_clr) begin
           corr_err_intr_rank1 <= 1'b0;
         end else if(rt_rd_rank==2'b01 && corr_err_byte[STAT_BYTES_LECC]) begin
           corr_err_intr_rank1 <= 1'b1;
         end
       end

       // Stored 1-bit error syndrome
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           syndrome_rank1 <= {RD_LINK_ECC_ERR_SYNDROME_WIDTH{1'b0}};
         end else if(rt_rd_rank==2'b01 && corr_err_byte[STAT_BYTES_LECC]) begin
           syndrome_rank1 <= syndrome_byte[STAT_BYTES_LECC];
         end
       end

       // Link-ECC  2-bit error count
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           uncorr_err_cnt_rank1 <= {RD_LINK_ECC_UNCORR_CNT_WIDTH{1'b0}};
         end else if(reg_ddrc_rd_link_ecc_uncorr_cnt_clr) begin
           uncorr_err_cnt_rank1 <= {RD_LINK_ECC_UNCORR_CNT_WIDTH{1'b0}};
         end else if(rt_rd_rank==2'b01 && uncorr_err_byte[STAT_BYTES_LECC] && uncorr_err_cnt_rank1!={RD_LINK_ECC_UNCORR_CNT_WIDTH{1'b1}}) begin
           uncorr_err_cnt_rank1 <= uncorr_err_cnt_rank1 + 8'd1;
         end
       end

       // Link-ECC 2-bit error interrupt
       always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
         if (~core_ddrc_rstn) begin
           uncorr_err_intr_rank1 <= 1'b0;
         end else if(reg_ddrc_rd_link_ecc_uncorr_intr_clr) begin
           uncorr_err_intr_rank1 <= 1'b0;
         end else if(rt_rd_rank==2'b01 && uncorr_err_byte[STAT_BYTES_LECC]) begin
           uncorr_err_intr_rank1 <= 1'b1;
         end
       end

       assign uncorr_err_cnt_byte_rank1[STAT_BYTES_LECC]  = uncorr_err_cnt_rank1;
       assign corr_err_cnt_byte_rank1[STAT_BYTES_LECC]    = corr_err_cnt_rank1;
       assign syndrome_byte_rank1[STAT_BYTES_LECC]        = syndrome_rank1;
       assign uncorr_err_intr_byte_rank1[STAT_BYTES_LECC] = uncorr_err_intr_rank1;
       assign corr_err_intr_byte_rank1[STAT_BYTES_LECC]   = corr_err_intr_rank1;


    end else begin: RD_LNKECC_STAT_dis

       assign uncorr_err_cnt_byte_rank0[STAT_BYTES_LECC]  = {RD_LINK_ECC_UNCORR_CNT_WIDTH{1'b0}};
       assign corr_err_cnt_byte_rank0[STAT_BYTES_LECC]    = {RD_LINK_ECC_CORR_CNT_WIDTH{1'b0}};
       assign syndrome_byte_rank0[STAT_BYTES_LECC]        = {RD_LINK_ECC_ERR_SYNDROME_WIDTH{1'b0}};
       assign uncorr_err_intr_byte_rank0[STAT_BYTES_LECC] = 1'b0;
       assign corr_err_intr_byte_rank0[STAT_BYTES_LECC]   = 1'b0;

       assign uncorr_err_cnt_byte_rank1[STAT_BYTES_LECC]  = {RD_LINK_ECC_UNCORR_CNT_WIDTH{1'b0}};
       assign corr_err_cnt_byte_rank1[STAT_BYTES_LECC]    = {RD_LINK_ECC_CORR_CNT_WIDTH{1'b0}};
       assign syndrome_byte_rank1[STAT_BYTES_LECC]        = {RD_LINK_ECC_ERR_SYNDROME_WIDTH{1'b0}};
       assign uncorr_err_intr_byte_rank1[STAT_BYTES_LECC] = 1'b0;
       assign corr_err_intr_byte_rank1[STAT_BYTES_LECC]   = 1'b0;

    end
  end // stat_lecc
endgenerate


// Check ECC-code
genvar CHK_BYTES_LECC;
generate
  for (CHK_BYTES_LECC=0; CHK_BYTES_LECC<MAX_NUM_BYTE; CHK_BYTES_LECC=CHK_BYTES_LECC+1) begin : chk_lecc
    if(CHK_BYTES_LECC<NUM_BYTE) begin: RD_LNKECC_CHK_en
       wire          corr_err;
       wire          uncorr_err;
       wire [8:0]    syndrome;

       assign uncorr_err_byte[CHK_BYTES_LECC] = uncorr_err;
       assign corr_err_byte[CHK_BYTES_LECC]   = corr_err;
       assign syndrome_byte[CHK_BYTES_LECC]   = syndrome;

       // Link-ECC Check per Byte
       rd_linkecc_secded
       

        rd_linkecc_secded (
           .data_in ({
                          ph_rd_rdata_w[DQ_WIDTH*15 +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*14 +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*13 +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*12 +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*11 +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*10 +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*9  +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*8  +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*7  +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*6  +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*5  +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*4  +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*3  +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*2  +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*1  +CHK_BYTES_LECC*8 +: 8],
                          ph_rd_rdata_w[DQ_WIDTH*0  +CHK_BYTES_LECC*8 +: 8]
                    }),
           .dmi_in  ({
                          ph_rd_rdbi_n_w[DMI_WIDTH*15 + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*14 + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*13 + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*12 + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*11 + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*10 + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*9  + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*8  + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*7  + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*6  + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*5  + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*4  + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*3  + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*2  + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*1  + CHK_BYTES_LECC],
                          ph_rd_rdbi_n_w[DMI_WIDTH*0  + CHK_BYTES_LECC]
                    }),
           .poison_type    (reg_ddrc_linkecc_poison_type),
           .poison_data    (linkecc_poison_byte_sel[CHK_BYTES_LECC]),
           .mrr            (mrr       ),
           .corr_err       (corr_err  ),
           .uncorr_err     (uncorr_err),
           .syndrome       (syndrome  ),
           .corrected_data ({
                          corr_rdata[DQ_WIDTH*15 +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*14 +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*13 +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*12 +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*11 +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*10 +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*9  +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*8  +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*7  +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*6  +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*5  +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*4  +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*3  +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*2  +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*1  +CHK_BYTES_LECC*8 +: 8],
                          corr_rdata[DQ_WIDTH*0  +CHK_BYTES_LECC*8 +: 8]
                   })
       );
    end else begin: RD_LNKECC_CHK_dis
       assign uncorr_err_byte[CHK_BYTES_LECC] = 1'b0;
       assign corr_err_byte[CHK_BYTES_LECC]   = 1'b0;
       assign syndrome_byte[CHK_BYTES_LECC]   = {RD_LINK_ECC_ERR_SYNDROME_WIDTH{1'b0}};
    end

  end // chk_lecc
endgenerate

// Address logging for corrected Read Link ECC error
always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
      link_ecc_corr_info <= {ECC_INFO_WIDTH{1'b0}};
   end else if (reg_ddrc_rd_link_ecc_corr_cnt_clr) begin
      link_ecc_corr_info <= {ECC_INFO_WIDTH{1'b0}};
   end else if ((|corr_err_byte)) begin
      link_ecc_corr_info <= rt_rd_link_ecc_info;
   end
end

assign ddrc_reg_link_ecc_corr_rank     = link_ecc_corr_info[ECC_INFO_WIDTH-LINK_ECC_CORR_RANK_WIDTH+:LINK_ECC_CORR_RANK_WIDTH];
assign ddrc_reg_link_ecc_corr_bank     = link_ecc_corr_info[(BLK_BITS+LINK_ECC_CORR_ROW_WIDTH+LINK_ECC_CORR_BG_WIDTH)+:LINK_ECC_CORR_BANK_WIDTH];
assign ddrc_reg_link_ecc_corr_bg       = link_ecc_corr_info[(BLK_BITS+LINK_ECC_CORR_ROW_WIDTH)+:LINK_ECC_CORR_BG_WIDTH];
assign ddrc_reg_link_ecc_corr_row      = link_ecc_corr_info[BLK_BITS+:LINK_ECC_CORR_ROW_WIDTH];
assign ddrc_reg_link_ecc_corr_col      = {link_ecc_corr_info[BLK_BITS-1:0],
                                          {(LINK_ECC_CORR_COL_WIDTH-BLK_BITS){1'b0}}
                                       };

// Address logging for uncorrected Read Link ECC error
always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
      link_ecc_uncorr_info <= {ECC_INFO_WIDTH{1'b0}};
   end else if (reg_ddrc_rd_link_ecc_uncorr_cnt_clr) begin
      link_ecc_uncorr_info <= {ECC_INFO_WIDTH{1'b0}};
   end else if ((|uncorr_err_byte)) begin
      link_ecc_uncorr_info <= rt_rd_link_ecc_info;
   end
end

assign ddrc_reg_link_ecc_uncorr_rank   = link_ecc_uncorr_info[ECC_INFO_WIDTH-LINK_ECC_UNCORR_RANK_WIDTH+:LINK_ECC_UNCORR_RANK_WIDTH];
assign ddrc_reg_link_ecc_uncorr_bank   = link_ecc_uncorr_info[(BLK_BITS+LINK_ECC_UNCORR_ROW_WIDTH+LINK_ECC_UNCORR_BG_WIDTH)+:LINK_ECC_UNCORR_BANK_WIDTH];
assign ddrc_reg_link_ecc_uncorr_bg     = link_ecc_uncorr_info[(BLK_BITS+LINK_ECC_UNCORR_ROW_WIDTH)+:LINK_ECC_UNCORR_BG_WIDTH];
assign ddrc_reg_link_ecc_uncorr_row    = link_ecc_uncorr_info[BLK_BITS+:LINK_ECC_UNCORR_ROW_WIDTH];
assign ddrc_reg_link_ecc_uncorr_col    = {link_ecc_uncorr_info[BLK_BITS-1:0],
                                          {(LINK_ECC_UNCORR_COL_WIDTH-BLK_BITS){1'b0}}
                                       };

endmodule
