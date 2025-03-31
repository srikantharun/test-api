//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_ie_cmd_ctl.sv#5 $
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
//  1) SEP
//  2) FSM
//  3) ECC ADDR GEN
//  4)
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module ih_ie_cmd_ctl
import DWC_ddrctl_reg_pkg::*;
#(
    parameter HIF_ADDR_WIDTH = `MEMC_HIF_ADDR_WIDTH
   ,parameter CORE_ADDR_WIDTH= (`UMCTL2_LRANK_BITS+`MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS) 
   ,parameter IH_TAG_WIDTH   = `MEMC_TAGBITS            // width of token/tag field from core
   ,parameter CMD_LEN_BITS   = 1                        // bits for command length, when used
   ,parameter RMW_TYPE_BITS  = 2
   ,parameter WDATA_PTR_BITS = `MEMC_WDATA_PTR_BITS
   ,parameter CMD_TYPE_BITS  = 2    
   ,parameter WRDATA_CYCLES = `MEMC_WRDATA_CYCLES 

   ,parameter BT_BITS           = 4   
   ,parameter BWT_BITS          = 4   
   ,parameter BRT_BITS          = 4   
   ,parameter NO_OF_BT          = 16 
   ,parameter NO_OF_BWT         = 16 
   ,parameter NO_OF_BRT         = 16 
   ,parameter NO_OF_BLK_CHN     = 16
   ,parameter BLK_CHN_BITS      = 4 

   ,parameter MWR_BITS = `DDRCTL_MWR_BITS
   ,parameter PARTIAL_WR_BITS = `UMCTL2_PARTIAL_WR_BITS 
   ,parameter PARTIAL_WR_BITS_LOG2 = 1 
   ,parameter PW_WORD_CNT_WD_MAX = 1 

   ,parameter IE_RD_TYPE_BITS   = `IE_RD_TYPE_BITS
   ,parameter IE_WR_TYPE_BITS   = `IE_WR_TYPE_BITS

   ,parameter IE_CMD_IVLD_ADDR_BITS = 1
   ,parameter IE_CMD_BITS       = 1
   ,parameter ECC_HOLE_BITS     = 2
   ,parameter IE_MASK_FULL_BITS = WRDATA_CYCLES 
   ,parameter IE_BURST_NUM_BITS = 5
   ,parameter IE_FIFO_DATA_BITS = IE_CMD_BITS +
                               IE_CMD_IVLD_ADDR_BITS +
                               ECC_HOLE_BITS +
                               IE_MASK_FULL_BITS +
                               IE_BURST_NUM_BITS +
                               `MEMC_BLK_BITS

)
(  
    input                      core_ddrc_core_clk
   ,input                      core_ddrc_rstn
   ,input                      ddrc_cg_en

   // address map registers

   // register 
   ,input [2:0]                    reg_ddrc_nonbinary_device_density

   ,input                           reg_ddrc_ecc_type
   ,input   [2:0]                   reg_ddrc_ecc_mode
   ,input   [6:0]                   reg_ddrc_ecc_region_map
   ,input   [1:0]                   reg_ddrc_ecc_region_map_granu
   ,input                           reg_ddrc_ecc_region_map_other
   ,input                           reg_ddrc_ecc_region_parity_lock
   ,input                           reg_ddrc_ecc_region_waste_lock
   ,input   [BLK_CHANNEL_IDLE_TIME_X32_WIDTH-1:0]                   reg_ddrc_blk_channel_idle_time_x32
   ,input   [4:0]                   reg_ddrc_active_blk_channel
   ,input                           reg_ddrc_blk_channel_active_term
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: Used under different `ifdefs. Decided to keep current implementation.
   ,input   [BURST_RDWR_WIDTH-1:0]  reg_ddrc_burst_rdwr 
//spyglass enable_block W240
   ,input                           dh_ih_dis_hif             // disable (stall) hif
   ,input                           gsfsm_sr_co_if_stall
   ,input [SELFREF_SW_WIDTH-1:0]    reg_ddrc_selfref_sw
   ,input [5:0]                     highest_col_bit  // the bit in hif address for the highest column address.
   ,input [3:0]                     highest_col_num  // the number of highest valid column address

//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: hif_cmd_valid/hif_cmd_length/hif_cmd_type - Used in RTL assertion/coverpoint \
//    hif_cmd_ecc_region - Used in TB (sva_ih.sv) \
//    mapped_critical_dword_b4_inpff/mapped_page_num_b4_inpff/mapped_critical_dword - Used under different `ifdefs. Decided to keep current coding style.
   // HIF Interface
   ,input                           hif_cmd_valid             // valid command
   ,input [CMD_LEN_BITS-1:0]        hif_cmd_length            // hif command length
   ,input [CMD_TYPE_BITS-1:0]       hif_cmd_type              // command type:
                                                              //  00 - block write
                                                              //  01 - read
                                                              //  10 - rmw
                                                              //  11 - reserved
   ,input [CORE_ADDR_WIDTH-1:0]     hif_cmd_addr              // address
   ,input                           hif_cmd_ecc_region        // HIF BLK sideband signal, 1: command belong to ECC region, 0: command don't belong to ECC region
   ,input  [WRDATA_CYCLES-1:0]      hif_cmd_wdata_mask_full 
   ,output                          hif_lpr_credit_ie
   ,output                          hif_hpr_credit_ie
   ,output                          hif_wrecc_credit_ie

   // mapped dram address before input FIFO
   ,input [`MEMC_BLK_BITS-1:0]      mapped_block_num_b4_inpff
   ,input [`MEMC_WORD_BITS-1:0]     mapped_critical_dword_b4_inpff
   ,input [`MEMC_PAGE_BITS-1:0]     mapped_page_num_b4_inpff 
   ,input [`MEMC_WORD_BITS-1:0]     mapped_critical_dword   
//spyglass enable_block W240
   // Received command after input FIFO
   ,input                           rxcmd_valid
   ,input [CMD_TYPE_BITS-1:0]       rxcmd_type
   ,input [1:0]                     rxcmd_pri
   ,input                           rxcmd_autopre
   ,input [`MEMC_PAGE_BITS-1:0]     mapped_page_num   // to generate row address of Write ECC command
   ,input [`UMCTL2_LRANK_BITS-1:0]  mapped_rank_num
   ,input [`MEMC_BG_BANK_BITS-1:0]  mapped_bg_bank_num
   ,input [`MEMC_BLK_BITS-1:0]      mapped_block_num
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: Used in RTL assertion
   ,input                           lpr_cam_empty
   ,input                           lpr_cam_full
   ,input                           hpr_cam_empty
   ,input                           hpr_cam_full
   ,input                           wr_cam_empty
   ,input                           wr_cam_full
   ,input                           wrecc_cam_empty
   ,input                           wrecc_cam_full
//spyglass enable_block W240
   ,input                           input_fifo_empty

   // from TE
   ,input                           te_ih_re_done_i
   ,input   [BT_BITS-1:0]           te_ih_re_done_bt
   ,input                           te_ih_retry
   ,output                          te_ih_retry_ie_cmd
   // Mapped address from address_map module
   //
   // INPUT FIFO EXTRA DATA
   ,input  [IE_FIFO_DATA_BITS-1:0]  input_fifo_dout_ie
   ,output [IE_FIFO_DATA_BITS-1:0]  input_fifo_din_ie
   ,output                          ie_cmd_active
   ,output                          ecc_region_invalid
   ,output                          rxcmd_ptc_vld 
   // output of IE cmd
   ,output                          ie_rd_vld
   ,output  reg                     ie_wr_vld
   ,output  [CMD_LEN_BITS-1:0]      ie_rd_length // <- full
   ,output  [IH_TAG_WIDTH-1:0]      ie_rd_tag    // <- 0;
   ,output  [RMW_TYPE_BITS-1:0]     ie_rmwtype 
   ,output  [1:0]                   ie_hi_pri
   ,output                          ie_autopre
   ,output  [`UMCTL2_LRANK_BITS-1:0] ie_rank_num
   ,output  [`MEMC_BG_BANK_BITS-1:0] ie_bg_bank_num
   ,output  [`MEMC_BLK_BITS-1:0]    ie_block_num
   ,output  [`MEMC_PAGE_BITS-1:0]   ie_page_num
   ,output  [`MEMC_WORD_BITS-1:0]   ie_critical_dword
   // output signal for both ECC and DATA command
   ,output  [BT_BITS-1:0]           ih_te_ie_bt
   ,output  [BWT_BITS-1:0]          ih_te_ie_bwt
   ,output  [IE_RD_TYPE_BITS-1:0]   ih_te_ie_rd_type
   ,output  [IE_WR_TYPE_BITS-1:0]   ih_te_ie_wr_type
   ,output  [IE_BURST_NUM_BITS-1:0] ih_te_ie_blk_burst_num  //only for the Data command
   ,output [MWR_BITS-1:0]                ih_te_mwr 
   ,input                                reg_ddrc_frequency_ratio
   ,output [PARTIAL_WR_BITS-1:0]         ih_te_wr_word_valid 
   ,output [PARTIAL_WR_BITS_LOG2-1:0]   ih_te_wr_ram_raddr_lsb_first 
   ,output [PW_WORD_CNT_WD_MAX-1:0]     ih_te_wr_pw_num_beats_m1 
   ,output [PW_WORD_CNT_WD_MAX-1:0]     ih_te_wr_pw_num_cols_m1 
   //Token manager
   ,input                          mr_ih_free_bwt_vld
   ,input   [BWT_BITS-1:0]         mr_ih_free_bwt
   ,input                          rd_ih_free_brt_vld
   ,input   [BRT_BITS-1:0]         rd_ih_free_brt

   ,output  [BRT_BITS-1:0]         ih_rd_ie_brt
   ,output                         ih_rd_ie_rd_cnt_inc
   ,output                         ih_rd_ie_blk_rd_end
   ,output  [BWT_BITS-1:0]         ih_mr_ie_bwt
   ,output  [BRT_BITS-1:0]         ih_mr_ie_brt
   ,output                         ih_mr_ie_brt_vld
   ,output                         ih_mr_ie_wr_cnt_inc
   ,output                         ih_mr_ie_blk_wr_end

   ,output                         ih_ie_empty
   ,output                         ih_ie_busy        // ih_ie_busy will assert ddrc_cg_en

   ,output                         assert_ie_cmd
   ,output                         assert_ie_cmd_invalid_addr
   ,output                         assert_dis_dm
   //signals for BTT and RDECC_RDY
   ,input                    rd_ih_ie_re_rdy
   ,output [NO_OF_BT-1:0]    ie_re_vct
   ,output [NO_OF_BT-1:0]    ie_btt_vct
   //signals for look up BT table
   ,input  [BT_BITS-1:0]     mr_ih_lkp_bwt_by_bt
   ,input  [BT_BITS-1:0]     mr_ih_lkp_brt_by_bt
   ,input  [BT_BITS-1:0]     rd_ih_lkp_brt_by_bt
   ,input  [BT_BITS-1:0]     rd_ih_lkp_bwt_by_bt
   ,output [BWT_BITS-1:0]    ih_mr_lkp_bwt
   ,output                   ih_mr_lkp_bwt_vld
   ,output [BRT_BITS-1:0]    ih_mr_lkp_brt
   ,output                   ih_mr_lkp_brt_vld
   ,output [BRT_BITS-1:0]    ih_rd_lkp_brt
   ,output                   ih_rd_lkp_brt_vld
   ,output [BWT_BITS-1:0]    ih_rd_lkp_bwt
   ,output                   ih_rd_lkp_bwt_vld

);

//------------------------------ LOCAL PARAMETERS ------------------------------------

// 2-bit command type encodings
localparam CMD_TYPE_BLK_WR   = `MEMC_CMD_TYPE_BLK_WR;
localparam CMD_TYPE_BLK_RD   = `MEMC_CMD_TYPE_BLK_RD;
localparam CMD_TYPE_RMW      = `MEMC_CMD_TYPE_RMW;
localparam CMD_TYPE_RESERVED = `MEMC_CMD_TYPE_RESERVED;

localparam MASK_VEC_BITS = WRDATA_CYCLES*8;  //8 access per block, each access support Full or Half write.
                                             //8 access per block, each access support Full write.
localparam ACCESS_VEC_BITS = `MEMC_BURST_LENGTH==16 ? 16 : 8;  //8 access per block, each access support Full or Half write.

localparam ECC_ADDR_BITS = (`UMCTL2_LRANK_BITS+`MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+ (`MEMC_BURST_LENGTH==16 ? 2 : 0)); 

localparam WRDATA_CYCLES_BITS = WRDATA_CYCLES==8 ? 3 : WRDATA_CYCLES==4 ? 2 : 1;

wire [2:0]                    hif_addr_h3;

wire [IE_BURST_NUM_BITS-1:0]  ie_burst_num;
wire [IE_BURST_NUM_BITS-1:0]  ie_burst_num_i;

reg  [`MEMC_BLK_BITS-1:0]     mapped_block_num_ecc_b4_inpff;
wire [`MEMC_BLK_BITS-1:0]     mapped_block_num_ecc_i;
wire [`MEMC_BLK_BITS-1:0]     mapped_block_num_ecc_mux;

wire [ECC_ADDR_BITS-1:0]      rxcmd_ecc_addr;
wire [ECC_ADDR_BITS-1:0]      rxcmd_ecc_addr_i;
reg  [ECC_ADDR_BITS-1:0]      rxcmd_ecc_addr_r;

wire [CMD_TYPE_BITS-1:0]      rxcmd_type_i;
wire [1:0]                    rxcmd_pri_i;
reg  [CMD_TYPE_BITS-1:0]      rxcmd_type_r;
reg  [1:0]                    rxcmd_pri_r;
reg                           rxcmd_autopre_r;

wire                          ie_ecc_mode;
wire                          ie_cmd_int;
wire                          ie_cmd;
wire                          ie_cmd_i;
wire [WRDATA_CYCLES-1:0]      ie_mask_full;
wire [WRDATA_CYCLES-1:0]      ie_mask_full_i;
wire [WRDATA_CYCLES-1:0]      ie_mask_full_int;
reg  [WRDATA_CYCLES-1:0]      ie_mask_full_r;

wire [7:0]                    ecc_region_map_ext;
wire                          ecc_region_map_bit7;

wire [BT_BITS-1:0]            ie_bt;
wire [BWT_BITS-1:0]           ie_cmd_bwt;
wire [BT_BITS-1:0]            allocated_bt;
wire [BWT_BITS-1:0]           allocated_bwt;
wire [BRT_BITS-1:0]           allocated_brt;
wire                          allocate_bt_vld;
wire                          allocate_bwt_vld;
wire                          allocate_brt_vld;

wire [BWT_BITS-1:0]  free_bwt_i;
wire [BRT_BITS-1:0]  free_brt_i;
wire                 free_bwt_vld;
wire                 free_brt_vld;

wire [BT_BITS-1:0]   ie_blk_end_bt;
wire                 ie_blk_end;
wire                 ie_blk_rd_end;
wire                 ie_blk_wr_end;
wire                 free_bt_vld_o;
wire                 free_bwt_vld_o;
wire                 free_brt_vld_o;
wire                 free_bt_vld   ;
wire [BT_BITS-1:0]   free_bt; 
wire [BWT_BITS-1:0]  free_bwt;
wire [BRT_BITS-1:0]  free_brt;

wire                 chn_vld;
wire                 bt_fifo_empty;

wire [MWR_BITS-1:0]  is_mwr;

wire                 ie_flush_req;      //ie_flush_req will assert ddrc_cg_en
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: This signal will be removed in future in UMCTL5. For temporary.
//spyglass enable_block W240
integer i; // for loop index


assign ih_ie_empty         = ~chn_vld & bt_fifo_empty;
assign ih_ie_busy          = ie_flush_req | free_bt_vld;


//---------------------------------------------------------------------
// 6G/12G invalid address checker
// cannot re-use existing rxcmd_invalid_addr in IH because combination logic loop.
//  - rxcmd_invalid_addr is generated by page_num of ih_te_if;
//  - page_num of ih_te_if is generated by ie_cmd_ctl;
//  - ie_cmd_ctl cannot use rxcmd_invalid_addr to generate page_num
// So, re-generate rxcmd_invalid_addr inside ie_cmd_ctl. 
// use ECC command's page_num that is same as data's
//--------------------------------------------------------------------
  wire invalid_addr_row13_12;
  wire invalid_addr_row14_13;
  wire invalid_addr_row15_14;
  wire invalid_addr_row16_15;
  wire invalid_addr_row17_16;
  wire invalid_addr;
  
  wire ie_cmd_invalid_addr;
  wire ie_cmd_invalid_addr_i;

  assign invalid_addr_row13_12 = ((reg_ddrc_nonbinary_device_density == 3'b001) && (mapped_page_num_b4_inpff[13:12] == 2'b11)) ? 1'b1 : 1'b0; 
  assign invalid_addr_row14_13 = ((reg_ddrc_nonbinary_device_density == 3'b010) && (mapped_page_num_b4_inpff[14:13] == 2'b11)) ? 1'b1 : 1'b0; 
  assign invalid_addr_row15_14 = ((reg_ddrc_nonbinary_device_density == 3'b011) && (mapped_page_num_b4_inpff[15:14] == 2'b11)) ? 1'b1 : 1'b0; 
  assign invalid_addr_row16_15 = ((reg_ddrc_nonbinary_device_density == 3'b100) && (mapped_page_num_b4_inpff[16:15] == 2'b11)) ? 1'b1 : 1'b0; 
  assign invalid_addr_row17_16 = ((reg_ddrc_nonbinary_device_density == 3'b101) && (mapped_page_num_b4_inpff[17:16] == 2'b11)) ? 1'b1 : 1'b0; 

  assign invalid_addr = invalid_addr_row13_12 || invalid_addr_row14_13 || invalid_addr_row15_14 || invalid_addr_row16_15 || invalid_addr_row17_16; 


//---------------------------------------------------------------------
// SEP Logic
//---------------------------------------------------------------------
// HIF sideband signal "hif_cmd_ie_ecc" indicate the command belong to ECC region or not
// In ARB config, XPI drive it according to ecc_region_map registers DDDRC use it directly.
// In HIF config, DDRC decode the command belong to ECC region or not according to ecc_region_map register
// "hif_cmd_ie_ecc" is not used in HIF configration.

localparam ADDR_IDX = `UMCTL_LOG2(CORE_ADDR_WIDTH);
localparam CORE_ADDR_WIDTH_EXTEND = 2**(ADDR_IDX);

wire [CORE_ADDR_WIDTH_EXTEND-1:0]  hif_cmd_addr_tmp;
wire [ADDR_IDX-1:0]  highest_col_index;
wire [ADDR_IDX-1:0]  highest_col_index_granu;
wire [ADDR_IDX-1:0]  highest_col_index_m3;
generate
  if(CORE_ADDR_WIDTH_EXTEND == CORE_ADDR_WIDTH) begin:CORE_ADDR_WIDTH_pow2 
assign hif_cmd_addr_tmp =  hif_cmd_addr;
  end else begin:CORE_ADDR_WIDTH_pow2
assign hif_cmd_addr_tmp =  {{(CORE_ADDR_WIDTH_EXTEND-CORE_ADDR_WIDTH){1'b0}},hif_cmd_addr};
  end
endgenerate

assign highest_col_index        = ADDR_IDX < 6 ?   highest_col_bit[ADDR_IDX-1:0]                                   : (highest_col_bit+{ADDR_IDX{1'b0}});
assign highest_col_index_granu  = ADDR_IDX < 6 ?  (highest_col_bit[ADDR_IDX-1:0]-reg_ddrc_ecc_region_map_granu)    : (highest_col_bit-reg_ddrc_ecc_region_map_granu+{ADDR_IDX{1'b0}});
assign highest_col_index_m3     = ADDR_IDX < 6 ?  (highest_col_bit[ADDR_IDX-1:0]-3)                                : (highest_col_bit-3+{ADDR_IDX{1'b0}});

assign hif_addr_h3        = hif_cmd_addr_tmp[highest_col_index-: 3];

assign ecc_region_map_bit7 = ~|reg_ddrc_ecc_region_map_granu ? 1'b0 : reg_ddrc_ecc_region_map_other;
assign ecc_region_map_ext = {ecc_region_map_bit7, reg_ddrc_ecc_region_map};
assign ie_cmd_int         = hif_cmd_ecc_region;

assign ie_ecc_mode        = (reg_ddrc_ecc_mode!=3'b000) ? reg_ddrc_ecc_type : 1'b0;

assign ie_cmd             = (!ie_ecc_mode)       ? 1'b0 : 
                                                    ~invalid_addr &
                                                   ie_cmd_int;

  assign ie_cmd_invalid_addr = (!ie_ecc_mode) ? 1'b0 : invalid_addr & ie_cmd_int;


//
// use below logic to generate how many location are accessed in one block, then to decide send WR ECC or RMW ECC, BL8 or BL4, DM or not.
//
wire [WRDATA_CYCLES-1:0] hif_cmd_wdata_mask_full_bitmap;


wire [WRDATA_CYCLES_BITS-1:0] addr_shift;
      assign addr_shift   = hif_cmd_addr[3];

assign hif_cmd_wdata_mask_full_bitmap = hif_cmd_wdata_mask_full << addr_shift;

assign ie_mask_full = hif_cmd_wdata_mask_full_bitmap;                                                                            


//---------------------------------------------------------------------
// ECC Hole access
//---------------------------------------------------------------------
wire [1:0] ecc_hole;
wire [1:0] ecc_hole_i;
wire       ecc_region_parity;
wire       ecc_region_waste;
wire [2:0] offset_addr;
wire [5:0] hif_ecc_addr_sep;

//if MEMC_BURST_LENGTH==16, offset_addr is Col6..4 
//if MEMC_BURST_LENGTH==8,  offset_addr is Col5..3 
assign offset_addr       = mapped_block_num_b4_inpff[2:0];

//spyglass disable_block TA_09
//SMD: Net 'DWC_ddrctl.U_ddrc.ddrc_ctrl_wrapper.\ddrc_ctrl_inst[0].ddrc_ctrl .ih.ih_ie_cmd_ctl.highest_col_bit[5]' [in 'ih_ie_cmd_ctl'] is not observable[affected by other input(s)].
//SJ: Functionally correct. In some configs, highest_col_bit[5] might never have value 1'b1.
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(3 - reg_ddrc_ecc_region_map_granu)' found in module 'ih_ie_cmd_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.
assign hif_ecc_addr_sep  = {offset_addr,hif_cmd_addr_tmp[highest_col_index_m3 -: 3]} >> (3-reg_ddrc_ecc_region_map_granu);
//spyglass enable_block SelfDeterminedExpr-ML
//spyglass enable_block TA_09

assign ecc_region_used_sep   =  ~|hif_ecc_addr_sep[5:3] & ecc_region_map_ext[hif_ecc_addr_sep[2:0]];
assign ecc_region_used_other =  |hif_ecc_addr_sep[5:3] & (~&offset_addr) & reg_ddrc_ecc_region_map_other;

assign ecc_region_parity = (!ie_ecc_mode) ? 1'b0 : (&hif_addr_h3) & (ecc_region_used_sep | ecc_region_used_other);
assign ecc_region_waste  = (!ie_ecc_mode) ? 1'b0 : (&hif_addr_h3) & ~(ecc_region_used_sep | ecc_region_used_other);


assign ecc_hole = {ecc_region_waste, ecc_region_parity};

//------------------------------------------------------------------
// Inline ECC address Gen
// only need generate column address, the other are same as data's address
// put it before fifo to optimize the timing
//------------------------------------------------------------------
// Generate ECC address based on each DARM address that is derived from HIF command address
// Replace blk_offset address with highest 3bits HIF address(that equal to the highest 3bit column address)
//    blk_offset address is COL[5:3] when MEMC_BURST_LENGTH is 8
//    blk_offset address is COL[6:4] when MEMC_BURST_LENGTH is 16
// then, set the highest 3 bits of HIF address to 3'b111.
//
//ie_burst_num definition
//in MEMC_BURST_LENGTH_8,  ie_burst_num is 3 bits, COL[5:3], same as blk_offset
//in MEMC_BURST_LENGTH_16, ie_burst_num is 5 bits, the lowest 3bits, COL[6:4], is blk_offset, the upper 2 bits are COL[3:2] or 1'b0,COL[3] or 2'b00 according to below 3 condition
//   it is COL[3:2] in case of : HBW & BL8
//   it is {1'b0, COL[3]} in case of HBW or BL8. # in case of HBW, COL[3] is set to 1.
//   it is 2'b00 in case of FBW & BL16.
//   So: a limitaiton: in MEMC_BURST_LENGTH=16, burst_rdwr=BL8, col3 must not map to HIF[5:0].
//   in HBW mode, Col3 is mapping to Higest, and is set to 1 for ECC address, so set ie_burst_num[3]=1 to indicate always use upper half of each data unit
//
assign ie_burst_num       = reg_ddrc_burst_rdwr == 5'b00100 ? {1'b0, mapped_critical_dword_b4_inpff[3], offset_addr} :
                                                              {2'b00, offset_addr};

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(highest_col_num - 4)' found in module 'ih_ie_cmd_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.



//generate column address of ECC
always @ (*)
begin
   mapped_block_num_ecc_b4_inpff = mapped_block_num_b4_inpff;
   begin //FBW
      //Col[Highest -:3] <= 3'b111
      for(int i=2;i<`MEMC_BLK_BITS;i=i+1) begin
        if($unsigned(i) == (highest_col_num-`MEMC_WORD_BITS)) begin           
          mapped_block_num_ecc_b4_inpff[i-:3] = 3'b111;
      //Col[5:3] <= Col[Highest -:3]
          mapped_block_num_ecc_b4_inpff[2:0] = mapped_block_num_b4_inpff[i-:3];
        end
      end

   end
end
//spyglass enable_block SelfDeterminedExpr-ML

//-------------------------------------------------------------------
// IH sync FIFO
// reuse sync FIFO in ih_core_in_if, just extend FIFO data width
// FIFO content includes: 
//    mapped_block_num), ie_burst_num(3 or 5), ecc_hole(2), ie_mask_full(1), ie_cmd(1)
//-------------------------------------------------------------------

assign input_fifo_din_ie = {mapped_block_num_ecc_b4_inpff, 
                            ie_burst_num, 
                            ie_mask_full, 
                            ecc_hole,
                              ie_cmd_invalid_addr,
                            ie_cmd};

assign {mapped_block_num_ecc_i, 
        ie_burst_num_i, 
        ie_mask_full_i, 
        ecc_hole_i,
        ie_cmd_invalid_addr_i,
        ie_cmd_i} = input_fifo_dout_ie;

//----------------------------------------------------------------------
// After input FIFO
//----------------------------------------------------------------------


// if ecc_cmd is 1, use generated ECC address
// if ecc_cmd is 0, ECC address equal to full address (original address), in order that TE can always use ECC address to check block collision
// Especially in unlock mode, RD/WR ECC is tread as RD_N/WR_N, we expect there have block collison with block read/write via compare ECC address.
assign mapped_block_num_ecc_mux =  ie_cmd_i ? mapped_block_num_ecc_i : mapped_block_num;

wire mpsm_en_int;


assign mpsm_en_int = 1'b0;

//-----------------------------------------------------------------------------
// IE BLK Channel table
//----------------------------------------------------------------------------

wire  hif_lpr_credit_ie_t;
wire  hif_hpr_credit_ie_t;
wire  bwt_fifo_full;
wire  brt_fifo_full;
wire  bt_fifo_full;
wire  bwt_fifo_empty;
wire  brt_fifo_empty;

wire  te_ih_retry_ie_cmd_t;
wire  ie_cmd_active_t;

wire  rxcmd_valid_i;
wire  ecc_hole_access;

wire  any_token_fifo_full;

assign any_token_fifo_full = bwt_fifo_full | brt_fifo_full | bt_fifo_full;

assign rxcmd_valid_i = ~any_token_fifo_full & rxcmd_valid ;   //when any token fifo is full stop accept inmocming command // ?? maybe it is reduandency.

wire [1:0] mapped_msb_critical_ecc;  //COL[3:2]
assign mapped_msb_critical_ecc[1] = reg_ddrc_burst_rdwr==5'b01000 ? 1'b0 :      //set to 0 for a full read ECC
                                    mapped_critical_dword[`MEMC_WORD_BITS-1];  //set to value that same as HIF command.

assign mapped_msb_critical_ecc[0] = 1'b0 ;      //set to 0 
//only block number is changed, the others are same as command's address
assign rxcmd_ecc_addr = {
                               mapped_rank_num,
                               mapped_bg_bank_num,mapped_page_num,
                               mapped_block_num_ecc_mux
                              ,mapped_msb_critical_ecc
                          };

assign rxcmd_ptc_vld  = rxcmd_valid_i & ie_cmd_i & ~ie_wr_vld;

assign ecc_hole_access= rxcmd_valid_i & (|ecc_hole_i);

//invalid access to ecc_region, i.e. access ecc_region_* when ecc_region_*_lock=1
assign ecc_region_invalid = (reg_ddrc_ecc_region_parity_lock & ecc_hole_i[0]) |
                            (reg_ddrc_ecc_region_waste_lock  & ecc_hole_i[1]) ;

assign te_ih_retry_ie_cmd = te_ih_retry_ie_cmd_t | any_token_fifo_full;   //when any token fifo is full, stall input fifo via setting te_ih_rety_ie_cmd.
assign ie_cmd_active      = ie_cmd_active_t | any_token_fifo_full;   //when any token fifo is full, stop send command to TE via setting ie_cmd_active=1 (ie_rd/wr_vld=0).

  wire   rd_cmd_invalid_addr;
  wire   wr_cmd_invalid_addr;
  wire   rmw_cmd_invalid_addr;
  
  assign rd_cmd_invalid_addr       = (rxcmd_type == CMD_TYPE_BLK_RD) & rxcmd_valid_i & ie_cmd_invalid_addr_i & ~te_ih_retry_ie_cmd;
  assign wr_cmd_invalid_addr       = (rxcmd_type == CMD_TYPE_BLK_WR) & rxcmd_valid_i & ie_cmd_invalid_addr_i & ~te_ih_retry_ie_cmd;
  assign rmw_cmd_invalid_addr      = (rxcmd_type == CMD_TYPE_RMW)    & rxcmd_valid_i & ie_cmd_invalid_addr_i & ~te_ih_retry_ie_cmd;

// generate WR ECC slot, i.e. ie_wr_vld
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ie_wr_vld      <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(rxcmd_ptc_vld & (rxcmd_type == CMD_TYPE_RMW || rxcmd_type == CMD_TYPE_BLK_WR) & ~te_ih_retry_ie_cmd_t)begin //set 1 when a WR/RMW to protected region
         ie_wr_vld   <= 1'b1;
      end else if(ie_wr_vld & ~te_ih_retry) begin // set 0 when WR ECC is sent to TE
         ie_wr_vld   <= 1'b0;
      end
   end
end
// latch rxcmd info for WR ECC slot
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      rxcmd_ecc_addr_r      <= {ECC_ADDR_BITS{1'b0}};
      rxcmd_type_r          <= {CMD_TYPE_BITS{1'b0}};
      rxcmd_pri_r           <= {2{1'b0}};
      rxcmd_autopre_r       <= 1'b0;
      ie_mask_full_r        <= {WRDATA_CYCLES{1'b0}};
   end else if(ddrc_cg_en) begin
      if(rxcmd_ptc_vld & (rxcmd_type == CMD_TYPE_RMW || rxcmd_type == CMD_TYPE_BLK_WR) & ~te_ih_retry)begin //set 1 when a WR/RMW to protected region
         rxcmd_ecc_addr_r   <= rxcmd_ecc_addr;
         rxcmd_type_r       <= rxcmd_type;
         rxcmd_pri_r        <= rxcmd_pri;
         rxcmd_autopre_r    <= rxcmd_autopre;
         ie_mask_full_r     <= ie_mask_full_i;
      end
   end
end

assign rxcmd_ecc_addr_i  = ie_wr_vld ? rxcmd_ecc_addr_r  : rxcmd_ecc_addr;
assign rxcmd_type_i      = ie_wr_vld ? rxcmd_type_r      : rxcmd_type;
assign rxcmd_pri_i       = ie_wr_vld ? rxcmd_pri_r       : rxcmd_pri;
assign ie_mask_full_int  = ie_wr_vld ? ie_mask_full_r    : ie_mask_full_i;
assign ie_autopre        = ie_wr_vld ? rxcmd_autopre_r   : 1'b0;   //don't assert autopre for RD ECC command and keep same autopre of WR DATA for WR ECC

reg hif_lpr_credit_ie_r;
reg hif_hpr_credit_ie_r;
//reg hif_wr_credit_ie_r ;
reg hif_lpr_credit_ie_invalid;
reg hif_hpr_credit_ie_invalid;
reg hif_wrecc_credit_ie_invalid ;

assign hif_lpr_credit_ie = hif_lpr_credit_ie_r 
                                                | hif_lpr_credit_ie_invalid
                                                                             ;
assign hif_hpr_credit_ie = hif_hpr_credit_ie_r 
                                                | hif_hpr_credit_ie_invalid
                                                                             ;
assign hif_wrecc_credit_ie = 1'b0
                                                | hif_wrecc_credit_ie_invalid
                                                                               ;
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      hif_lpr_credit_ie_r <= 1'b0;
      hif_hpr_credit_ie_r <= 1'b0;
      hif_lpr_credit_ie_invalid   <= 1'b0 ;                             
      hif_hpr_credit_ie_invalid   <= 1'b0 ;         // if it is ecc_region but it invalid address, don't consume overhead credit
      hif_wrecc_credit_ie_invalid    <= 1'b0 ;    // if it is ecc_region but it invalid address, don't consume overhead credit
   end else begin
      hif_lpr_credit_ie_r <= hif_lpr_credit_ie_t;
      hif_hpr_credit_ie_r <= hif_hpr_credit_ie_t;
      hif_lpr_credit_ie_invalid   <= (rd_cmd_invalid_addr & (rxcmd_pri!=2'b10)) |         // if it is ecc_region but it invalid address, don't consume overhead credit
                                    (rmw_cmd_invalid_addr) ;                             

      hif_hpr_credit_ie_invalid   <= (rd_cmd_invalid_addr & (rxcmd_pri==2'b10)) ;         // if it is ecc_region but it invalid address, don't consume overhead credit
      hif_wrecc_credit_ie_invalid    <= (wr_cmd_invalid_addr ) | (rmw_cmd_invalid_addr) ;    // if it is ecc_region but it invalid address, don't consume overhead credit
   end
end

wire  [`UMCTL2_LRANK_BITS-1:0] ie_rank_num_dummy;
wire  [`MEMC_BG_BANK_BITS-1:0] ie_bg_bank_num_dummy;
wire  [`MEMC_BLK_BITS-1:0]    ie_block_num_dummy;
wire  [`MEMC_PAGE_BITS-1:0]   ie_page_num_dummy;
wire                          ie_bwt_vld_unused;
ih_ie_blk_chn_table

#(
    .NO_OF_BLK_CHN      (NO_OF_BLK_CHN     )
   ,.BLK_CHN_BITS       (BLK_CHN_BITS)
   ,.IE_BURST_NUM_BITS  (IE_BURST_NUM_BITS )
   ,.BT_BITS            (BT_BITS           )
   ,.BWT_BITS           (BWT_BITS          )
   ,.BRT_BITS           (BRT_BITS          )
   ,.IE_RD_TYPE_BITS    (IE_RD_TYPE_BITS   )
   ,.IE_WR_TYPE_BITS    (IE_WR_TYPE_BITS   )
   ,.CMD_LEN_BITS       (CMD_LEN_BITS      )
   ,.IH_TAG_WIDTH       (IH_TAG_WIDTH      )
   ,.RMW_TYPE_BITS      (RMW_TYPE_BITS     )
   ,.WRDATA_CYCLES      (WRDATA_CYCLES     )
   ,.MWR_BITS           (MWR_BITS          )
   ,.UMCTL2_LRANK_BITS  (`UMCTL2_LRANK_BITS )
   ,.MEMC_BG_BANK_BITS  (`MEMC_BG_BANK_BITS)
   ,.MEMC_BLK_BITS      (`MEMC_BLK_BITS)
   ,.MEMC_PAGE_BITS     (`MEMC_PAGE_BITS)
   ,.MEMC_WORD_BITS     (`MEMC_WORD_BITS)
   ,.ECC_ADDR_WIDTH     (ECC_ADDR_BITS)
) blk_chn_table
(  
    .core_ddrc_core_clk    (core_ddrc_core_clk)
   ,.core_ddrc_rstn        (core_ddrc_rstn)
   ,.ddrc_cg_en            (ddrc_cg_en)
   ,.reg_ddrc_blk_channel_idle_time_x32 (reg_ddrc_blk_channel_idle_time_x32)
   ,.reg_ddrc_active_blk_channel        (reg_ddrc_active_blk_channel)
   ,.reg_ddrc_blk_channel_active_term   (reg_ddrc_blk_channel_active_term)
   ,.reg_ddrc_burst_rdwr   (reg_ddrc_burst_rdwr)
   ,.dh_ih_dis_hif         (dh_ih_dis_hif)    // disable (stall) hif
   ,.gsfsm_sr_co_if_stall  (gsfsm_sr_co_if_stall)
   ,.reg_ddrc_selfref_sw   (reg_ddrc_selfref_sw)
   ,.mpsm_en_int           (mpsm_en_int)

   //input
   ,.te_ih_retry           (te_ih_retry)
   ,.input_fifo_empty      (input_fifo_empty)
   ,.rxcmd_ecc_addr        (rxcmd_ecc_addr_i) //don't include page and critical_dword
   ,.rxcmd_pri             (rxcmd_pri_i)
   ,.rxcmd_type            (rxcmd_type_i)
   ,.rxcmd_ptc_vld         (rxcmd_ptc_vld)
   ,.wdata_mask_full       (ie_mask_full_int)
   ,.ie_burst_num          (ie_burst_num_i)
   ,.ecc_hole_access       (ecc_hole_access)
   ,.alloc_bt              (allocated_bt)
   ,.alloc_bwt             (allocated_bwt)
   ,.alloc_brt             (allocated_brt)
   ,.re_done_i             (te_ih_re_done_i)
   ,.re_done_bt            (te_ih_re_done_bt)
   //output
   ,.chn_vld               (chn_vld)
   ,.hif_lpr_credit_ie     (hif_lpr_credit_ie_t)
   ,.hif_hpr_credit_ie     (hif_hpr_credit_ie_t)
   ,.te_ih_retry_ie_cmd    (te_ih_retry_ie_cmd_t)
   ,.ie_cmd_active         (ie_cmd_active_t)
   ,.ie_rd_vld             (ie_rd_vld)
   ,.ie_wr_vld             (ie_wr_vld)
   ,.ie_rd_type            (ih_te_ie_rd_type)
   ,.ie_wr_type            (ih_te_ie_wr_type)
   ,.ie_bt                 (ie_bt)
   ,.ie_cmd_bwt            (ie_cmd_bwt)
   ,.ie_rd_length          (ie_rd_length)
   ,.ie_rd_tag             (ie_rd_tag)
   ,.ie_rmwtype            (ie_rmwtype)
   ,.ie_hi_pri             (ie_hi_pri)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion
   ,.ie_rank_num           (ie_rank_num_dummy)
   ,.ie_bg_bank_num        (ie_bg_bank_num_dummy)
   ,.ie_block_num          (ie_block_num_dummy)
   ,.ie_page_num           (ie_page_num_dummy)
//spyglass enable_block W528
   ,.ie_critical_dword     (ie_critical_dword)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current implementation.
   ,.is_mwr                (is_mwr)
//spyglass enable_block W528
   ,.alloc_bt_vld          (allocate_bt_vld) 
   ,.alloc_bwt_vld         (allocate_bwt_vld)
   ,.alloc_brt_vld         (allocate_brt_vld)
   ,.ie_wr_cnt_inc         (ih_mr_ie_wr_cnt_inc)
   ,.ie_rd_cnt_inc         (ih_rd_ie_rd_cnt_inc)
   ,.ie_bwt                (ih_mr_ie_bwt)
   ,.ie_brt                (ih_rd_ie_brt)
   ,.ie_bwt_vld            (ie_bwt_vld_unused) //not used
   ,.ie_brt_vld            (ih_mr_ie_brt_vld)
   ,.ie_blk_end_bt         (ie_blk_end_bt)       
   ,.ie_blk_end            (ie_blk_end)
   ,.ie_blk_rd_end         (ie_blk_rd_end)
   ,.ie_blk_wr_end         (ie_blk_wr_end)
   ,.flush_req             (ie_flush_req) 
);

assign  ih_mr_ie_brt      = ih_rd_ie_brt;

wire [1:0] ie_critical_unused;  //COL[3:2]

assign  {
              ie_rank_num,
              ie_bg_bank_num, ie_page_num,
              ie_block_num 
             ,ie_critical_unused
         } = rxcmd_ecc_addr_i;

// generate WR CAM fields for WR ECC command
// ih_te_mwr is derived by block channel.
// the others are derived by ih_pw module
assign ih_te_mwr = is_mwr; 

// ie_wr_len=2'b00 - Full : 1) MEMC_BURST_LENGTH_16 && DRAM_L16 && FBW; 2) MEMC_BURST_LENGTH_8 && DRAM_BL8 && FBW.
// ie_wr_len=2'b10 - Half : 1) MEMC_BURST_LENGTH_16 && DRAM_L16 && HBW; 2) MEMC_BURST_LENGTH_16 && DRAM_BL8 && FBW; 3) MEMC_BURST_LENGTH_8 && DRAM_BL8 && HBW.
// ie_wr_len=2'b11 - Quarter : 1) MEMC_BURST_LENGTH_16 && DRAM_BL8 && HBW.
// For Half/Quarter, use critical_dword to determine which half/quarter is valid
wire [CMD_LEN_BITS-1:0] ie_wr_length;
   assign ie_wr_length[1] = (reg_ddrc_burst_rdwr!=5'b01000);
   assign ie_wr_length[0] = 1'b0;


ih_pw
 #(
//------------------------------ PARAMETERS ------------------------------------
  .CMD_LEN_BITS         (CMD_LEN_BITS)                             // bits for command length, when used
 ,.WRDATA_CYCLES        (WRDATA_CYCLES) 
 ,.MWR_BITS             (MWR_BITS)
 ,.PARTIAL_WR_BITS      (PARTIAL_WR_BITS) 
 ,.PARTIAL_WR_BITS_LOG2 (PARTIAL_WR_BITS_LOG2)
 ,.PW_WORD_CNT_WD_MAX   (PW_WORD_CNT_WD_MAX) 
)
 ih_pw (
//-------------------------- INPUTS AND OUTPUTS --------------------------------    
  .ih_te_rd_length                    (ie_wr_length)
 ,.ih_te_critical_dword               (ie_critical_dword)
 `ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
 ,.core_ddrc_core_clk                 (core_ddrc_core_clk)
 ,.core_ddrc_rstn                     (core_ddrc_rstn)  
  `endif //SYNTHESIS
 `endif //SNPS_ASSERT_ON
 ,.reg_ddrc_burst_rdwr                (reg_ddrc_burst_rdwr)
 ,.reg_ddrc_frequency_ratio           (reg_ddrc_frequency_ratio)
 ,.ih_te_wr_word_valid                (ih_te_wr_word_valid)
 ,.ih_te_wr_ram_raddr_lsb_first       (ih_te_wr_ram_raddr_lsb_first)
 ,.ih_te_wr_pw_num_beats_m1           (ih_te_wr_pw_num_beats_m1)
 ,.ih_te_wr_pw_num_cols_m1            (ih_te_wr_pw_num_cols_m1)
);

//----------------------------------------------------------------------------
// output signal generate
// ---------------------------------------------------------------------------
wire free_bwt_vld_i;
wire free_brt_vld_i;

assign ih_te_ie_blk_burst_num = ie_burst_num_i;

assign ih_rd_ie_blk_rd_end = ie_blk_rd_end;
assign ih_mr_ie_blk_wr_end = ie_blk_wr_end;
assign ih_te_ie_bt         = ie_bt;
assign ih_te_ie_bwt        = ie_cmd_bwt;
// input signals to internal signals
assign free_bwt_vld_i      = mr_ih_free_bwt_vld;
assign free_bwt_i          = mr_ih_free_bwt;
assign free_brt_vld_i      = rd_ih_free_brt_vld;
assign free_brt_i          = rd_ih_free_brt;

//three token are released at the same time
assign free_bt_vld         = free_bt_vld_o;
assign free_bwt_vld        = free_bwt_vld_o;
assign free_brt_vld        = free_brt_vld_o;
//-----------------------------------------------------------------------------
// Token manager 
// ie_bwt_fifo
// ie_brt_fifo
//-----------------------------------------------------------------------------
ih_ie_bt_table

#(
    .NO_OF_BT       (NO_OF_BT)
   ,.BT_BITS        (BT_BITS )
   ,.BWT_BITS       (BWT_BITS)
   ,.BRT_BITS       (BRT_BITS)
) bt_table
(  
    .core_ddrc_core_clk (core_ddrc_core_clk)
   ,.core_ddrc_rstn     (core_ddrc_rstn    )
   ,.ddrc_cg_en         (ddrc_cg_en        )

   //signals to generate BT table
   ,.alloc_bwt_vld      (allocate_bwt_vld)
   ,.alloc_brt_vld      (allocate_brt_vld)
   ,.ie_bt              (ie_bt)
   ,.allocated_bwt      (allocated_bwt)
   ,.allocated_brt      (allocated_brt)

   //signals to free BT table
   ,.free_bwt_vld_i     (free_bwt_vld_i)
   ,.free_brt_vld_i     (free_brt_vld_i)
   ,.free_bwt_i         (free_bwt_i) 
   ,.free_brt_i         (free_brt_i) 
   
   ,.free_bt_vld_o      (free_bt_vld_o)
   ,.free_bwt_vld_o     (free_bwt_vld_o)
   ,.free_brt_vld_o     (free_brt_vld_o)
   ,.free_bt_o          (free_bt) 
   ,.free_bwt_o         (free_bwt)
   ,.free_brt_o         (free_brt)
   //signals for BTT and RDECC RDY
   ,.ie_blk_end         (ie_blk_end)
   ,.ie_blk_end_bt      (ie_blk_end_bt)       
   ,.ie_btt_vct         (ie_btt_vct)
   ,.rd_ih_ie_re_rdy    (rd_ih_ie_re_rdy)
   ,.ie_re_vct          (ie_re_vct)
   //signals for look up BT table
   ,.mr_ih_lkp_bwt_by_bt(mr_ih_lkp_bwt_by_bt)
   ,.mr_ih_lkp_brt_by_bt(mr_ih_lkp_brt_by_bt)
   ,.rd_ih_lkp_brt_by_bt(rd_ih_lkp_brt_by_bt)
   ,.rd_ih_lkp_bwt_by_bt(rd_ih_lkp_bwt_by_bt)
   ,.ih_mr_lkp_bwt      (ih_mr_lkp_bwt      )   
   ,.ih_mr_lkp_bwt_vld  (ih_mr_lkp_bwt_vld  )
   ,.ih_mr_lkp_brt      (ih_mr_lkp_brt      )   
   ,.ih_mr_lkp_brt_vld  (ih_mr_lkp_brt_vld  )
   ,.ih_rd_lkp_brt      (ih_rd_lkp_brt      )   
   ,.ih_rd_lkp_brt_vld  (ih_rd_lkp_brt_vld  )
   ,.ih_rd_lkp_bwt      (ih_rd_lkp_bwt      )   
   ,.ih_rd_lkp_bwt_vld  (ih_rd_lkp_bwt_vld  )
);

// instantiate block write token fifo
ih_ie_token_fifo
 #(
  .DEPTH  (NO_OF_BWT)
  )
  bwt_fifo (
  .clk                   (core_ddrc_core_clk),
  .rstn                  (core_ddrc_rstn),
  .allocate_token        (allocate_bwt_vld),    // allocate signal
  .release_token         (free_bwt_vld),        // free signal
  .release_token_num     (free_bwt),            // free token#
  .allocate_token_num    (allocated_bwt),       // allocated token#
  .token_empty           (bwt_fifo_full),       // full (no token is available)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion/coverpoint
  .token_full            (bwt_fifo_empty)       // Empty (all token are ready)
//spyglass enable_block W528
);

// instantiate block read token fifo
ih_ie_token_fifo
 #(
  .DEPTH  (NO_OF_BRT)
  )
  brt_fifo (
  .clk                   (core_ddrc_core_clk),
  .rstn                  (core_ddrc_rstn),
  .allocate_token        (allocate_brt_vld),    // allocate signal
  .release_token         (free_brt_vld),        // free signal
  .release_token_num     (free_brt),            // free token#
  .allocate_token_num    (allocated_brt),       // allocated token#
  .token_empty           (brt_fifo_full),       // full (no token is available)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion/coverpoint
  .token_full            (brt_fifo_empty)       // Empty (all token are ready)
//spyglass enable_block W528
);

// instantiate block token fifo
ih_ie_token_fifo
 #(
  .DEPTH  (NO_OF_BT)
  )
  bt_fifo (
  .clk                   (core_ddrc_core_clk),
  .rstn                  (core_ddrc_rstn),
  .allocate_token        (allocate_bt_vld),     // allocate signal
  .release_token         (free_bt_vld),         // free signal
  .release_token_num     (free_bt),             // free token#
  .allocate_token_num    (allocated_bt),        // allocated token#
  .token_empty           (bt_fifo_full),        // full (no token is available)
  .token_full            (bt_fifo_empty)        // Empty (all token are ready)
);

// to ih_assertion
assign assert_ie_cmd               = ie_cmd;
  assign assert_ie_cmd_invalid_addr  = ie_cmd_invalid_addr;
assign assert_dis_dm               = 1'b0;

`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON

//-----------------------------------------------------------------------------
//  Coverpoint for CAM/TOKEN FIFO STATUS
wire brt_fifo_nofull_noempty;
wire bwt_fifo_nofull_noempty;
wire lpr_cam_nofull_noempty;
wire hpr_cam_nofull_noempty;
wire wr_cam_nofull_noempty;
wire wrecc_cam_nofull_noempty;

assign brt_fifo_nofull_noempty  = ~brt_fifo_full & ~brt_fifo_empty;
assign bwt_fifo_nofull_noempty  = ~bwt_fifo_full & ~bwt_fifo_empty;
assign lpr_cam_nofull_noempty   = ~lpr_cam_full & ~lpr_cam_empty;
assign hpr_cam_nofull_noempty   = ~hpr_cam_full & ~hpr_cam_empty;
assign wr_cam_nofull_noempty    = ~wr_cam_full & ~wr_cam_empty;
assign wrecc_cam_nofull_noempty = ~wrecc_cam_full & ~wrecc_cam_empty;

  covergroup cg_cam_token_fifo @(posedge core_ddrc_core_clk);
     cp_lpr_cam : coverpoint ({lpr_cam_full, lpr_cam_nofull_noempty, lpr_cam_empty}) iff(core_ddrc_rstn) {
                 bins             empty = {3'b001};    
                 bins  no_full_no_empty = {3'b010};    
                 bins              full = {3'b100};    
     }
     cp_hpr_cam : coverpoint ({hpr_cam_full, hpr_cam_nofull_noempty, hpr_cam_empty}) iff(core_ddrc_rstn) {
                 bins             empty = {3'b001};    
                 bins  no_full_no_empty = {3'b010};    
                 bins              full = {3'b100};    
     }
     cp_wrcam : coverpoint ({wr_cam_full, wr_cam_nofull_noempty, wr_cam_empty}) iff(core_ddrc_rstn) {
                 bins             empty = {3'b001};    
                 bins  no_full_no_empty = {3'b010};    
                 bins              full = {3'b100};    
     }
     cp_wrecccam : coverpoint ({wrecc_cam_full, wrecc_cam_nofull_noempty, wrecc_cam_empty}) iff(core_ddrc_rstn) {
                 bins             empty = {3'b001};    
                 bins  no_full_no_empty = {3'b010};    
                 bins              full = {3'b100};    
     }
     cp_brt_fifo : coverpoint ({brt_fifo_full, brt_fifo_nofull_noempty, brt_fifo_empty}) iff(core_ddrc_rstn) {
                 bins             empty = {3'b001};    
                 bins  no_full_no_empty = {3'b010};    
                 bins              full = {3'b100};    
     }
     cp_bwt_fifo : coverpoint ({bwt_fifo_full, bwt_fifo_nofull_noempty, bwt_fifo_empty}) iff(core_ddrc_rstn) {
                 bins             empty = {3'b001};    
                 bins  no_full_no_empty = {3'b010};    
                 bins              full = {3'b100};    
     }

     cp_hif_cmd : coverpoint ({hif_cmd_type, hif_cmd_valid}) iff(core_ddrc_rstn) {
                 bins             WR = {3'b001};    
                 bins             RD = {3'b011};    
                 bins            RMW = {3'b101};    
       wildcard  bins            NOP = {3'b??0};    
     }
     // Cross rdcam and brt_fifo, all the combination.
     cp_cross_lpr_cam_brt_fifo : cross cp_lpr_cam, cp_brt_fifo{
     }

     // Cross rdcam and brt_fifo, all the combination.
     cp_cross_hpr_cam_brt_fifo : cross cp_hpr_cam, cp_brt_fifo{
     }

     // Cross rdcam and brt_fifo, all the combination.
     cp_cross_wrcam_bwt_fifo : cross cp_wrcam, cp_bwt_fifo{
     }

     // Cross rdcam and brt_fifo with hif commands, all the combination.
     cp_cross_lpr_cam_brt_fifo_hif_cmd : cross cp_cross_lpr_cam_brt_fifo, cp_hif_cmd{
     }

     // Cross rdcam and brt_fifo with hif commands, all the combination.
     cp_cross_hpr_cam_brt_fifo_hif_cmd : cross cp_cross_hpr_cam_brt_fifo, cp_hif_cmd{
     }

     // Cross wrcam and bwt_fifo with hif commands, all the combination.
     cp_cross_wrcam_bwt_fifo_hif_cmd : cross cp_cross_wrcam_bwt_fifo, cp_hif_cmd{
     }
  endgroup
  // Coverage group instantiation
  cg_cam_token_fifo cg_cam_token_fifo_inst = new;
//assertions for BWT/BRT fifo, it is not allow Write with FULL or Read with empty.

  property p_wr_when_bwt_fifo_full;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      (bwt_fifo_full) |-> (~allocate_bwt_vld);
  endproperty
  
  a_wr_when_bwt_fifo_full: assert property (p_wr_when_bwt_fifo_full)
      else $error("%m @ %t Error : allocate BWT when BWT_FIFO is full", $time);

  property p_wr_when_brt_fifo_full;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      (brt_fifo_full) |-> (~allocate_brt_vld);
  endproperty

  a_wr_when_brt_fifo_full: assert property (p_wr_when_brt_fifo_full)
      else $error("%m @ %t Error : allocate BRT when BWT_FIFO is full", $time);
  
//if MEMC_BURST_LENGTH=16, burst_rdwr=4'b0100(BL8), hif_cmd_length cannot be full.
property p_hif_cmd_lengh_is_full_bl8;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      (reg_ddrc_burst_rdwr==5'b00100 && ie_ecc_mode && hif_cmd_valid==1'b1) |-> hif_cmd_length!=2'b00;

endproperty

a_hif_cmd_lengh_is_full_bl8 : assert property (p_hif_cmd_lengh_is_full_bl8);

  property p_check_ecc_address_with_chn_sel;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      (rxcmd_valid | ie_rd_vld | ie_wr_vld) |-> 
         (ie_rank_num            == ie_rank_num_dummy)and
         (ie_bg_bank_num         == ie_bg_bank_num_dummy)and
         (ie_block_num           == ie_block_num_dummy)and
         (ie_page_num            == ie_page_num_dummy);
  endproperty
  
  a_check_ecc_address_with_chn_sel: assert property (p_check_ecc_address_with_chn_sel)
      else $error("%m @ %t Error : ecc_address is not same as address from channel selnet", $time);

`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
