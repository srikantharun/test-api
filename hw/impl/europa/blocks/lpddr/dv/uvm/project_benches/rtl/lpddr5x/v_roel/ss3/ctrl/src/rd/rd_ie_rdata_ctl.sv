//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/rd/rd_ie_rdata_ctl.sv#4 $
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
//
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module rd_ie_rdata_ctl
import DWC_ddrctl_reg_pkg::*;
#(
    parameter CORE_DATA_WIDTH       = `MEMC_DFI_DATA_WIDTH   // internal data width
   ,parameter CORE_MASK_WIDTH       = `MEMC_DFI_DATA_WIDTH/8 // data mask width
   ,parameter RDCAM_ADDR_WIDTH      = `MEMC_RDCMD_ENTRY_BITS // bits to address into CAM
//   ,parameter WRDATA_RAM_ADDR_WIDTH = `UMCTL2_WDATARAM_AW    // data width to RAM
   ,parameter NO_OF_BRT             = 16
   ,parameter BT_BITS               = 4
   ,parameter BWT_BITS              = 4
   ,parameter BRT_BITS              = 4
   ,parameter IE_RD_TYPE_BITS       = 3
   ,parameter IE_BURST_NUM_BITS     = 5
   ,parameter WORD_BITS             = 3 //  // bits for critical dword
   ,parameter CMD_INFO_WIDTH        = 8 //need overwrite
   ,parameter ECC_RAM_DEPTH         = `MEMC_ECC_RAM_DEPTH
   ,parameter ECC_RAM_ADDR_BITS     = `log2(ECC_RAM_DEPTH)
   ,parameter ECC_ERR_RAM_DEPTH     = 16
   ,parameter ECC_ERR_RAM_ADDR_BITS = `log2(ECC_ERR_RAM_DEPTH)
   ,parameter ECC_ERR_RAM_WIDTH      = 16 //MEMC_WRDATA_CYCLES*SECDED_LANES;

   ,parameter ECC_INFO_WIDTH        = 35   // width of read info from RT to be passed
   ,parameter ECCAP_TH_WIDTH        = 4
   ,parameter RMW_TYPE_BITS         = 2
   ,parameter OCECC_EN              = 0
   ,parameter OCECC_XPI_RD_GRANU    = 64
   ,parameter OCECC_MR_RD_GRANU     = 8
   ,parameter OCECC_MR_BNUM_WIDTH   = 5
   ,parameter OCECC_MR_RD_ECCW      = 40

   ,parameter RD_IE_PAR_ERR_PIPELINE    = 0

)
(  
    input                      core_ddrc_core_clk
   ,input                      core_ddrc_rstn
   ,input                      ddrc_cg_en
   ,input [2:0]                reg_ddrc_ecc_mode 
   ,input                      reg_ddrc_med_ecc_en 
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: This signal will be used programmable MEMC_BURST_LENGTH
   ,input [BURST_RDWR_WIDTH-1:0] reg_ddrc_burst_rdwr    
//spyglass enable_block W240
   ,input [1:0]                reg_ddrc_data_bus_width
// data in after asm
   ,input [CORE_DATA_WIDTH-1:0]  data_in
   ,input [CORE_MASK_WIDTH-1:0]  data_par
// data valid
   ,input                        rt_rd_rd_valid
   ,input                        rt_rd_eod

//CMD info input
   ,input [WORD_BITS-1:0]       rt_rd_ecc_word
   ,input [CMD_INFO_WIDTH-1:0]  rt_rd_cmd_info
   ,input                       mrr_operation_on

//Inline ECC information
   ,input  [BT_BITS-1:0]            rt_rd_ie_bt
   ,input  [IE_RD_TYPE_BITS-1:0]    rt_rd_ie_rd_type
   ,input  [IE_BURST_NUM_BITS-1:0]  rt_rd_ie_blk_burst_num  //only for the Data command
   ,output                          rt_rd_ie_ecc_vld // only used by ocpar

// IH to RD for IE
   ,input  [BRT_BITS-1:0]           ih_rd_ie_brt
   ,input                           ih_rd_ie_rd_cnt_inc
   ,input                           ih_rd_ie_blk_rd_end

// CMD info output (delay 1 or 2 cycles)
   ,output [CMD_INFO_WIDTH-1:0]     ie_rt_rd_cmd_info
   ,output                          ie_mrr_operation_on

// RD to IH for free BRT
//
   ,output                          rd_ih_free_brt_vld
   ,output [BRT_BITS-1:0]           rd_ih_free_brt
// ocpar error
   ,output                          par_rdata_err_pulse
// Data out
   ,output [CORE_DATA_WIDTH-1:0]    data_out
   ,output                          data_out_vld
   ,output                          data_out_eod
   ,output                          ecc_corrected_err
   ,output                          ecc_uncorrected_err
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block
// OCECC
   ,input                           ocecc_en
   ,input                           ocecc_poison_egen_mr_rd_1
   ,input [OCECC_MR_BNUM_WIDTH-1:0] ocecc_poison_egen_mr_rd_1_bnum
   ,input                           ocecc_poison_egen_xpi_rd_0
   ,input                           ocecc_poison_single
//spyglass enable_block W240
   ,output [OCECC_MR_RD_ECCW-1:0]   ecc_out_rw
   ,output [CORE_MASK_WIDTH-1:0]    ecc_out_ra

//Connect ecc ram to outside
   ,output                          rd_ecc_ram_wr
   ,output [ECC_RAM_ADDR_BITS-1:0]  rd_ecc_ram_waddr
   ,output [CORE_DATA_WIDTH-1:0]    rd_ecc_ram_wdata
   ,output [CORE_MASK_WIDTH-1:0]    rd_ecc_ram_wdata_mask_n //should be all 1, no mask. 
   ,output [CORE_MASK_WIDTH-1:0]    rd_ecc_ram_wdata_par
   
   ,output [ECC_RAM_ADDR_BITS-1:0]  rd_ecc_ram_raddr
   ,input  [CORE_DATA_WIDTH-1:0]    ecc_ram_rd_rdata
   ,output [ECC_RAM_ADDR_BITS-1:0]  rd_ecc_acc_raddr_2
   ,input  [CORE_DATA_WIDTH-1:0]    ecc_acc_rd_rdata_2
   ,input  [CORE_MASK_WIDTH-1:0]    ecc_acc_rd_rdata_mask_n_2

// ECC ERR RAM interface
   ,input                               mr_ecc_err_rd
   ,input  [ECC_ERR_RAM_ADDR_BITS-1:0]  mr_ecc_err_raddr
   ,output [ECC_ERR_RAM_WIDTH-1:0]      ecc_err_mr_rdata

   ,output [BT_BITS-1:0]            rd_ih_lkp_bwt_by_bt
   ,output [BT_BITS-1:0]            rd_ih_lkp_brt_by_bt
   ,input  [BRT_BITS-1:0]           ih_rd_lkp_brt
   ,input  [BWT_BITS-1:0]           ih_rd_lkp_bwt
   ,input                           ih_rd_lkp_bwt_vld


// REGISTERS INTERFACE
   ,input  [ECC_INFO_WIDTH-1:0]     ie_rt_rd_ecc_info
   ,input  [RMW_TYPE_BITS-1:0]      ie_rt_rd_rmwtype
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in conditional assignment based on HW parameter value
   ,input                                  reg_ddrc_oc_parity_en // enables on-chip parity
   ,input                                  reg_ddrc_oc_parity_type // selects parity type. 0 even, 1 odd
//spyglass enable_block W240
   ,input                                  reg_ddrc_ecc_clr_corr_err      // Clear corrected error interrupt
   ,input                                  reg_ddrc_ecc_clr_uncorr_err    // Clear uncorrected error interrupt
   ,input                                  reg_ddrc_ecc_clr_corr_err_cnt  // Clear correctable ECC error count
   ,input                                  reg_ddrc_ecc_clr_uncorr_err_cnt // Clear uncorrectable ECC error count
   ,output                                 ddrc_reg_ecc_corrected_err   // single-bit error that will be corrected, per lane
   ,output                                 ddrc_reg_ecc_uncorrected_err // double-bit error detected in read data, per lane
   ,output  [6:0]                          ddrc_reg_ecc_corrected_bit_num// bit number corrected by single-bit error
   ,output  [15:0]                         ddrc_reg_ecc_corr_err_cnt       // Count of correctable ECC errors
   ,output  [15:0]                         ddrc_reg_ecc_uncorr_err_cnt     // Count of uncorrectable ECC errors
   ,output  [(`MEMC_ECC_SYNDROME_WIDTH)-1:0] rd_dh_ecc_corr_syndromes        // data pattern that resulted in an error;
   ,output  [(`MEMC_ECC_SYNDROME_WIDTH)-1:0] rd_dh_ecc_uncorr_syndromes      // data pattern that resulted in an error;
   ,output  [(`MEMC_ECC_SYNDROME_WIDTH)-1:0] rd_dh_ecc_corr_bit_mask         // mask for the bit that is corrected
   ,output  [ECC_INFO_WIDTH-1:0]           rd_dh_ecc_corr_info
   ,output  [ECC_INFO_WIDTH-1:0]           rd_dh_ecc_uncorr_info
   ,output  [5:0]                          rd_dh_ecc_corr_word_num
   ,output  [5:0]                          rd_dh_ecc_uncorr_word_num 
   ,input                                  rt_rd_eccap
   ,output                                 ddrc_reg_ecc_ap_err
   ,input                                  reg_ddrc_ecc_ap_en
   ,input                                  reg_ddrc_ecc_ap_err_intr_clr
   ,input   [ECCAP_TH_WIDTH-1:0]           reg_ddrc_ecc_ap_err_threshold

);

//------------------------------ LOCAL PARAMETERS ------------------------------------
localparam  DATA_BITS_PER_LANE      = 64;     // data bits per ECC engine
localparam  ECC_BITS_PER_LANE       = 8 ;     // ecc bits per ECC engine
localparam  DATA_ECC_BITS_PER_LANE  = DATA_BITS_PER_LANE + ECC_BITS_PER_LANE;      // data+ecc bits per ECC engine

localparam  CORE_DATA_WIDTH_EXT     = (CORE_DATA_WIDTH<DATA_BITS_PER_LANE) ? DATA_BITS_PER_LANE : CORE_DATA_WIDTH;
localparam  ECC_DATA_WIDTH_EXT      = (CORE_DATA_WIDTH<DATA_BITS_PER_LANE) ? ECC_BITS_PER_LANE  : CORE_DATA_WIDTH/8;
localparam  CORE_ECC_DATA_WIDTH_EXT = CORE_DATA_WIDTH_EXT + ECC_DATA_WIDTH_EXT;
localparam  SECDED_LANES            = CORE_DATA_WIDTH_EXT / DATA_BITS_PER_LANE; // number of data lanes for SEC/DED

localparam  MEMC_WRDATA_CYCLES      = `MEMC_WRDATA_CYCLES;
// WRDATA_CYCLES_BITS: 1 - when MEMC_WRDATA_CYCLES=2.
// WRDATA_CYCLES_BITS: 2 - when MEMC_WRDATA_CYCLES=4.
// WRDATA_CYCLES_BITS: 3 - when MEMC_WRDATA_CYCLES=8.
localparam WRDATA_CYCLES_BITS   = MEMC_WRDATA_CYCLES==8 ? 3 : MEMC_WRDATA_CYCLES==4 ? 2 : 1; // that is equal to WRDATA_RAM_AW - WRCAM_AW. 

wire                                   rd_data_vld;
wire                                   ecc_region_vld;
wire                                   ecc_vld;

wire [WRDATA_CYCLES_BITS-1:0]          word_num;
reg  [WRDATA_CYCLES_BITS-1:0]          word_num_r;
wire [WRDATA_CYCLES_BITS-1:0]          dfi_word_num;
wire [WRDATA_CYCLES_BITS-1:0]          dfi_word_num_log;
reg  [WRDATA_CYCLES_BITS-1:0]          dfi_word_num_r;
reg  [WRDATA_CYCLES_BITS-1:0]          dfi_word_num_2r;

wire [2:0]                             burst_num;    //burst address in one block
wire [3+WRDATA_CYCLES_BITS-1:0]        burst_num_word_num;    //word address in one block (8 burst)

reg                                    ecc_ram_wr;
reg  [ECC_RAM_ADDR_BITS-1:0]           ecc_ram_waddr;
reg  [CORE_DATA_WIDTH-1:0]             ecc_ram_wdata;
reg  [CORE_DATA_WIDTH/8-1:0]           ecc_ram_wdata_mask_n; //should be all 1, no mask. 
reg  [CORE_MASK_WIDTH-1:0]             ecc_ram_wdata_par;

wire                                   data_in_lanes_vld;
wire [CORE_DATA_WIDTH_EXT-1:0]         data_in_lanes;
wire [ECC_DATA_WIDTH_EXT-1:0]          ecc_lanes;
wire [ECC_DATA_WIDTH_EXT-1:0]          ecc_lanes_with_eccap; // After considering ECCAP
reg  [CORE_ECC_DATA_WIDTH_EXT-1:0]     data_ecc_lanes;
reg  [CORE_ECC_DATA_WIDTH_EXT-1:0]     data_ecc_lanes_r;
wire [SECDED_LANES*7-1:0]              err_bit_num_lanes;


wire [SECDED_LANES-1:0]                corrected_err_i;
wire [SECDED_LANES-1:0]                uncorrected_err_i;
wire [SECDED_LANES-1:0]                corrected_err;
wire [SECDED_LANES-1:0]                uncorrected_err;
wire [CORE_DATA_WIDTH_EXT-1:0]         corrected_data;
wire [CORE_DATA_WIDTH_EXT-1:0]         corrected_data_w;

wire [SECDED_LANES-1:0]                corrected_err_log;
wire [SECDED_LANES-1:0]                uncorrected_err_log;

wire [NO_OF_BRT-1:0]                   re_bw_vld_vct;

wire [NO_OF_BRT-1:0]                   free_req_vct;
reg  [NO_OF_BRT-1:0]                   free_ack_vct;


reg                                    data_out_vld_r;
reg                                    data_out_eod_r;
reg                                    ecc_region_vld_r;
reg  [CORE_DATA_WIDTH-1:0]             data_in_r;
reg  [CMD_INFO_WIDTH-1:0]              rt_rd_cmd_info_r;
reg                                    mrr_operation_on_r;

reg                                    ecc_err_ram_wr;
reg  [ECC_ERR_RAM_ADDR_BITS-1:0]       ecc_err_ram_waddr;
reg  [ECC_ERR_RAM_WIDTH-1:0]           ecc_err_ram_wdata;
wire                                   ptc_region_vld;
reg  [ECC_ERR_RAM_WIDTH-1:0]           ecc_err_int;
reg  [ECC_ERR_RAM_WIDTH-1:0]           ecc_err_ram_wdata_acc;
reg  [ECC_ERR_RAM_ADDR_BITS-1:0]       ecc_err_ram_waddr_r;
wire [ECC_ERR_RAM_ADDR_BITS-1:0]       ecc_err_ram_waddr_t;

reg                                    burst_ongoing;
wire                                   new_cmd;


wire [2:0]                             ecc_bytes;
integer i;

wire [CORE_DATA_WIDTH-1:0]         data_in_i;
wire                               ecc_region_vld_i;
wire                               ecc_vld_i;
wire [3+WRDATA_CYCLES_BITS-1:0]    burst_num_word_num_i;    //word address in one block (8 burst)
wire [WRDATA_CYCLES_BITS-1:0]      word_num_i;
wire [2:0]                         burst_num_i;

wire [CMD_INFO_WIDTH-1:0]          rt_rd_cmd_info_i;
wire                               rt_rd_rd_valid_i;
wire                               rt_rd_eod_i;
wire                               mrr_operation_on_i;
wire [BRT_BITS-1:0]                ih_rd_lkp_brt_i;
wire                               ih_rd_lkp_bwt_vld_i;
wire                               rt_rd_eccap_i;

genvar bit_idx;
generate
   for (bit_idx=0; bit_idx<ECC_DATA_WIDTH_EXT; bit_idx=bit_idx+1) begin : ECCAP
      if (bit_idx%8<=1) begin : ECCAP_INVERT // Invert lowest two bit for every byte if rt_rd_eccap==1
         assign ecc_lanes_with_eccap[bit_idx] = ecc_lanes[bit_idx] ^ rt_rd_eccap_i; // Invert
      end
      else begin : ECCAP_NON_INVERT
         assign ecc_lanes_with_eccap[bit_idx] = ecc_lanes[bit_idx];
      end
   end
endgenerate


//connect ECC RAM to outside
assign   rd_ecc_ram_wr              =  ecc_ram_wr;
assign   rd_ecc_ram_waddr           =  ecc_ram_waddr; 
assign   rd_ecc_ram_wdata           =  ecc_ram_wdata;
assign   rd_ecc_ram_wdata_mask_n    =  ecc_ram_wdata_mask_n; //should be all 1, no mask. 
assign   rd_ecc_ram_wdata_par       =  ecc_ram_wdata_par;

//---------------------------------------------------------------------
// Seperate incoming data_in accoridng to ie_rd_type
// If ie_rd_type == RD_N, do nothing, just bypass
// If ie_rd_type == RD_BW/RD_BR, decode the data with it's ECC
// If ie_rd_type == RE_BW/RE_BR, store the "data" to ECC ram
// If ie_rd_type == RD_RMW, do nothing, just bypass
//--------------------------------------------------------------------
assign ecc_region_vld     =  (rt_rd_ie_rd_type == `IE_RD_TYPE_RD_E) & rt_rd_rd_valid & ~mrr_operation_on;
assign ecc_vld            =  (rt_rd_ie_rd_type == `IE_RD_TYPE_RE_B) & rt_rd_rd_valid & ~mrr_operation_on;

assign rd_data_vld        =  rt_rd_rd_valid & ~mrr_operation_on;

assign rt_rd_ie_ecc_vld   = ecc_vld;

//JIRA___ID: need consider Retry
//JIRA___ID: need consider the start address is not aligned
//JIRA___ID: need consiser the LPDDR and DDR protocol
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      word_num_r <= {WRDATA_CYCLES_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      if(rd_data_vld) begin
         if(new_cmd) begin
            word_num_r <= word_num + 1'b1;
         end else begin
            word_num_r <= word_num_r + 1'b1;
         end
      end
   end
end
//Note: WORD_BITS = WRDATA_CYCLES_BITS + MEMC_FREQ_RATIO
wire [WORD_BITS-1:0] rt_rd_ecc_word_shift;
assign rt_rd_ecc_word_shift = rt_rd_ecc_word >> (`UMCTL_LOG2(`MEMC_FREQ_RATIO)+1);
assign word_num = new_cmd ? rt_rd_ecc_word_shift[WRDATA_CYCLES_BITS-1:0] : word_num_r;

//generate new command flag
assign new_cmd = ~burst_ongoing & rd_data_vld;
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      burst_ongoing <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(rd_data_vld & ~rt_rd_eod) begin
         burst_ongoing <= 1'b1;
      end else if(rd_data_vld && rt_rd_eod) begin
         burst_ongoing <= 1'b0;
      end
   end
end
//---------------------------------------------------------------------
// ECC RAM
//---------------------------------------------------------------------
assign rd_ih_lkp_brt_by_bt = rt_rd_ie_bt;
assign rd_ih_lkp_bwt_by_bt = rt_rd_ie_bt;

// register ECC RAM write interface to optimize timing
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_ram_wr           <= 1'b0;
      ecc_ram_waddr        <= {ECC_RAM_ADDR_BITS{1'b0}};
      ecc_ram_wdata        <= {CORE_DATA_WIDTH{1'b0}};   
      ecc_ram_wdata_par    <= {CORE_MASK_WIDTH{1'b0}};
      ecc_ram_wdata_mask_n <= {(CORE_DATA_WIDTH/8){1'b1}};
   end else if(ddrc_cg_en) begin
      ecc_ram_wr           <= ecc_vld;
//      ecc_ram_waddr        <= {rt_rd_ie_brt, word_num};
      ecc_ram_waddr        <= {ih_rd_lkp_brt, word_num};
      ecc_ram_wdata        <= data_in;  
      ecc_ram_wdata_par    <= data_par;
      ecc_ram_wdata_mask_n <= {(CORE_DATA_WIDTH/8){1'b1}};
   end
end

assign burst_num          = rt_rd_ie_blk_burst_num[2:0] ;
// Read ECC from ECC RAM when ecc_region_vld
assign burst_num_word_num = reg_ddrc_burst_rdwr ==5'b00100 ? rt_rd_ie_blk_burst_num[3:0] :
                                                           {rt_rd_ie_blk_burst_num[2:0], word_num} ;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((3 + WRDATA_CYCLES_BITS) - 1)' found in module 'rd_ie_rdata_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.

reg [ECC_RAM_ADDR_BITS-1:0] ecc_ram_raddr;
// register ECC RAM read interface to optimize timing
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_ram_raddr        <= {ECC_RAM_ADDR_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      ecc_ram_raddr[ECC_RAM_ADDR_BITS-1:WRDATA_CYCLES_BITS] <= ih_rd_lkp_brt;
      ecc_ram_raddr[WRDATA_CYCLES_BITS-1:0] <= burst_num_word_num[(3+WRDATA_CYCLES_BITS-1)-:WRDATA_CYCLES_BITS];
   end
end

//------------------------------------------------------------------
// copy ECC from RD to MR if it is READ ECC during block write 
//------------------------------------------------------------------
// MR to RD for IE to update ECC during block write
reg [ECC_RAM_ADDR_BITS-1:0] ecc_acc_raddr;
// register ECC RAM read interface to optimize timing
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_acc_raddr        <= {ECC_RAM_ADDR_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      ecc_acc_raddr[ECC_RAM_ADDR_BITS-1:WRDATA_CYCLES_BITS] <= ih_rd_lkp_bwt;
      ecc_acc_raddr[WRDATA_CYCLES_BITS-1:0] <= burst_num_word_num[(3+WRDATA_CYCLES_BITS-1)-:WRDATA_CYCLES_BITS];
   end
end
//spyglass enable_block SelfDeterminedExpr-ML

assign rd_ecc_acc_raddr_2 = ecc_acc_raddr;
assign rd_ecc_ram_raddr = ecc_ram_raddr;

//---------------------------------------------------------------------
// Data input register to optimize timing
//---------------------------------------------------------------------

///////
reg  [CORE_DATA_WIDTH-1:0]         data_in_prereg;
reg                                ecc_region_vld_prereg;
reg                                ecc_vld_prereg;
reg  [3+WRDATA_CYCLES_BITS-1:0]    burst_num_word_num_prereg;    //word address in one block (8 burst)
reg  [WRDATA_CYCLES_BITS-1:0]      word_num_prereg;
reg  [2:0]                         burst_num_prereg;

reg  [CMD_INFO_WIDTH-1:0]          rt_rd_cmd_info_prereg;
reg                                rt_rd_rd_valid_prereg;
reg                                rt_rd_eod_prereg;
reg                                mrr_operation_on_prereg;
reg [BRT_BITS-1:0]                 ih_rd_lkp_brt_prereg;
reg                                ih_rd_lkp_bwt_vld_prereg;
reg                                rt_rd_eccap_prereg;
// register data_in to align with read data of ECC RAM, to optimize timing
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      data_in_prereg            <= {CORE_DATA_WIDTH{1'b0}};
      ecc_region_vld_prereg     <= 1'b0;
      ecc_vld_prereg            <= 1'b0;
      burst_num_word_num_prereg <= {(3+WRDATA_CYCLES_BITS){1'b0}};
      word_num_prereg           <= {WRDATA_CYCLES_BITS{1'b0}};
      burst_num_prereg          <= 3'b000;
      rt_rd_cmd_info_prereg     <= {CMD_INFO_WIDTH{1'b0}};
      rt_rd_rd_valid_prereg     <= 1'b0;
      rt_rd_eod_prereg          <= 1'b0;
      mrr_operation_on_prereg   <= 1'b0;
      ih_rd_lkp_brt_prereg      <= {BRT_BITS{1'b0}};
      ih_rd_lkp_bwt_vld_prereg  <= 1'b0;
      rt_rd_eccap_prereg        <= 1'b0;
   end else if(ddrc_cg_en) begin
      data_in_prereg            <= data_in;
      ecc_region_vld_prereg     <= ecc_region_vld;
      ecc_vld_prereg            <= ecc_vld;
      burst_num_word_num_prereg <= burst_num_word_num;
      word_num_prereg           <= word_num;
      burst_num_prereg          <= burst_num;
      rt_rd_cmd_info_prereg     <= rt_rd_cmd_info;
      rt_rd_rd_valid_prereg     <= rt_rd_rd_valid;
      rt_rd_eod_prereg          <= rt_rd_eod;
      mrr_operation_on_prereg   <= mrr_operation_on;
      ih_rd_lkp_brt_prereg      <= ih_rd_lkp_brt;
      ih_rd_lkp_bwt_vld_prereg  <= ih_rd_lkp_bwt_vld;
      rt_rd_eccap_prereg        <= rt_rd_eccap;
   end
end

assign   data_in_i             =  data_in_prereg           ;
assign   ecc_region_vld_i      =  ecc_region_vld_prereg    ;
assign   ecc_vld_i             =  ecc_vld_prereg           ;
assign   burst_num_word_num_i  =  burst_num_word_num_prereg;
assign   word_num_i            =  word_num_prereg          ;
assign   burst_num_i           =  burst_num_prereg         ;
assign   rt_rd_cmd_info_i      =  rt_rd_cmd_info_prereg    ;
assign   rt_rd_rd_valid_i      =  rt_rd_rd_valid_prereg    ;
assign   rt_rd_eod_i           =  rt_rd_eod_prereg         ;
assign   mrr_operation_on_i    =  mrr_operation_on_prereg  ;
assign   ih_rd_lkp_brt_i       =  ih_rd_lkp_brt_prereg     ;
assign   ih_rd_lkp_bwt_vld_i   = ih_rd_lkp_bwt_vld_prereg  ;
assign   rt_rd_eccap_i         =  rt_rd_eccap_prereg       ;

assign data_in_lanes_vld = ecc_region_vld_i; // decoder is valid when data_acc_vld is 1.
assign ecc_bytes         = burst_num_word_num_i[2:0];

rd_ie_rdata_merge
 rd_ie_rdata_merge (
   .data_bus_width  (reg_ddrc_data_bus_width),
   .data            (data_in_i),
   .merged_rdata    (data_in_lanes)
);

reg  [CORE_DATA_WIDTH-1:0]    ecc_ram_rdata_updated;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * 8)' found in module 'rd_ie_rdata_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.

//update ECC RAM when a RE_BW occurs for one brt, becuase that means the ECC could be changing in Write path.
always @ (*) begin
   for (i=0; i<CORE_DATA_WIDTH/8; i=i+1) begin
      ecc_ram_rdata_updated[i*8+:8] = (ih_rd_lkp_bwt_vld_i && ecc_acc_rd_rdata_mask_n_2[i]) ? ecc_acc_rd_rdata_2[i*8+:8] : ecc_ram_rd_rdata[i*8+:8];
   end
end

assign ecc_lanes = ecc_ram_rdata_updated[ecc_bytes*ECC_DATA_WIDTH_EXT+: ECC_DATA_WIDTH_EXT];

localparam NO_OF_BRT_POW2 = 2**BRT_BITS; 


//compose the data and ecc per lane
always @ (*)
begin
   for (i=0; i<SECDED_LANES; i=i+1)
      if(reg_ddrc_data_bus_width==2'b01 && i>=SECDED_LANES/2)
         // Note: QBW is not considered here, because it is not supported now.
         data_ecc_lanes[i*DATA_ECC_BITS_PER_LANE+:DATA_ECC_BITS_PER_LANE] = {{ECC_BITS_PER_LANE{1'b1}}, {DATA_BITS_PER_LANE{1'b0}}};
      else
         data_ecc_lanes[i*DATA_ECC_BITS_PER_LANE+:DATA_ECC_BITS_PER_LANE] = {ecc_lanes_with_eccap[i*ECC_BITS_PER_LANE+:ECC_BITS_PER_LANE], data_in_lanes[i*DATA_BITS_PER_LANE+:DATA_BITS_PER_LANE]};
end
//spyglass enable_block SelfDeterminedExpr-ML

//--------------------------------------------------------------------
// add flip-flop to the data to optimize timing
//
// Flip-flop the data and cmd info


always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      data_ecc_lanes_r   <= {CORE_ECC_DATA_WIDTH_EXT{1'b0}};
      data_in_r          <= {CORE_DATA_WIDTH{1'b0}}; // register data_in for un-ECC protected region
      rt_rd_cmd_info_r   <= {CMD_INFO_WIDTH{1'b0}};
      mrr_operation_on_r <= 1'b0;
      dfi_word_num_r     <= {WRDATA_CYCLES_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      if(data_in_lanes_vld) begin
         data_ecc_lanes_r<= data_ecc_lanes;
      end
      data_in_r          <= data_in_i;
      rt_rd_cmd_info_r   <= rt_rd_cmd_info_i;
      mrr_operation_on_r <= mrr_operation_on_i;
      dfi_word_num_r     <= word_num_i;
   end
end

// add flip-flop to data valid signals
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      data_out_vld_r     <= 1'b0;
      data_out_eod_r     <= 1'b0;
      ecc_region_vld_r   <= 1'b0;
   end else if(ddrc_cg_en) begin
      data_out_vld_r     <= (!ecc_vld_i) & rt_rd_rd_valid_i;  //filter out "ECC" data
      data_out_eod_r     <= rt_rd_eod_i;
      ecc_region_vld_r   <= ecc_region_vld_i;
   end
end

//generate ecc_err address and latch it aligned with input valid
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_err_ram_waddr_r   <= {ECC_ERR_RAM_ADDR_BITS{1'b0}};
   end else begin
      if(rt_rd_rd_valid) begin
         ecc_err_ram_waddr_r   <= {ih_rd_lkp_brt_i, burst_num_i}; 
      end
   end
end

// add one extra pipeline to align with CRC path when Inline ECC is selected and ecc_mode diaabled.
// the extra one pipeline in needed only when DDRCTL_RD_CRC_RETRY is enabled.
wire                            rt_rd_rd_valid_mux;
wire                            rt_rd_eod_mux;
wire   [CORE_DATA_WIDTH-1:0]    data_in_mux;
wire   [CMD_INFO_WIDTH-1:0]     rt_rd_cmd_info_mux;
wire                            mrr_operation_on_mux;
assign rt_rd_rd_valid_mux  = rt_rd_rd_valid;
assign rt_rd_eod_mux       = rt_rd_eod;
assign data_in_mux         = data_in;
assign rt_rd_cmd_info_mux  = rt_rd_cmd_info;
assign mrr_operation_on_mux = mrr_operation_on;

assign data_out_vld        = (reg_ddrc_ecc_mode==0) ? rt_rd_rd_valid_mux   : data_out_vld_r;
assign data_out_eod        = (reg_ddrc_ecc_mode==0) ? rt_rd_eod_mux        : data_out_eod_r;
assign data_out            = (reg_ddrc_ecc_mode==0) ? data_in_mux          : ecc_region_vld_r ? corrected_data : data_in_r; // select the corrected data or origianls data.
assign ie_rt_rd_cmd_info   = (reg_ddrc_ecc_mode==0) ? rt_rd_cmd_info_mux   : rt_rd_cmd_info_r;
assign ie_mrr_operation_on = (reg_ddrc_ecc_mode==0) ? mrr_operation_on_mux : mrr_operation_on_r;
assign corrected_err       = (reg_ddrc_ecc_mode==0) ? {SECDED_LANES{1'b0}} : ecc_region_vld_r ? corrected_err_i : {SECDED_LANES{1'b0}};
assign uncorrected_err     = (reg_ddrc_ecc_mode==0) ? {SECDED_LANES{1'b0}} : ecc_region_vld_r ? uncorrected_err_i : {SECDED_LANES{1'b0}};
assign corrected_err_log   = corrected_err;
assign uncorrected_err_log = uncorrected_err;
assign dfi_word_num_log    = dfi_word_num_r;
assign dfi_word_num        = dfi_word_num_r;
assign ptc_region_vld      = ecc_region_vld_r;
assign ecc_err_ram_waddr_t = ecc_err_ram_waddr_r;

generate
  if (OCECC_EN == 1) begin: OCECC_en
    
    ocecc_enc
     
         #(
            .DW      (CORE_DATA_WIDTH),
            .GRANU   (OCECC_MR_RD_GRANU),
            .EW      (OCECC_MR_RD_ECCW)
         )
         egen_mr_rd_1
         (
            .clk           (core_ddrc_core_clk),
            .rstn          (core_ddrc_rstn),
            .data_in       (data_out),
            .data_valid    (data_out_vld & ocecc_en),
            .poison_en     (ocecc_poison_egen_mr_rd_1),
            .poison_single (ocecc_poison_single),
            .poison_bnum   (ocecc_poison_egen_mr_rd_1_bnum),
            .ecc_out       (ecc_out_rw)
         );
         
    ocecc_enc
     
         #(
            .DW      (CORE_DATA_WIDTH),
            .GRANU   (OCECC_XPI_RD_GRANU),
            .EW      (CORE_MASK_WIDTH)
         )
         egen_xpi_rd_0
         (
            .clk           (core_ddrc_core_clk),
            .rstn          (core_ddrc_rstn),
            .data_in       (data_out),
            .data_valid    (data_out_vld & ocecc_en),
            .poison_en     (ocecc_poison_egen_xpi_rd_0),
            .poison_single (ocecc_poison_single),
            .poison_bnum   (5'd0),
            .ecc_out       (ecc_out_ra)
         );
         
  end
  else begin: OCECC_dis
  
    assign ecc_out_rw = {OCECC_MR_RD_ECCW{1'b0}};
    assign ecc_out_ra = {CORE_MASK_WIDTH{1'b0}};
  
  end
endgenerate

assign ecc_corrected_err   = |corrected_err;
assign ecc_uncorrected_err = |uncorrected_err;

//---------------------------------------------------------------------
// decoder
// the number of encoder depend on the HIF data width(CORE_DATA_WIDTH) 
// CORE_DATA_WIDTH could be: 64, 128, 256.
// The number of encoder is:  1,   2,   4.
//---------------------------------------------------------------------


//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(idx * DATA_ECC_BITS_PER_LANE)' found in module 'rd_ie_rdata_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.

// generate the appropriate number of error-correcting lanes for this ECC implementation
genvar idx;
generate
   for (idx=0; idx<SECDED_LANES; idx=idx+1) begin : secded_lanes
         rd_secded_lane
          rd_secded_lane (
            .rdata                  (data_ecc_lanes_r[idx*DATA_ECC_BITS_PER_LANE +: DATA_ECC_BITS_PER_LANE]),
            .reg_ddrc_med_ecc_en    (reg_ddrc_med_ecc_en),
            .corrected_err          (corrected_err_i[idx]),
            .uncorrected_err        (uncorrected_err_i[idx]),
            .corrected_data         (corrected_data_w[idx*DATA_BITS_PER_LANE +: DATA_BITS_PER_LANE]),
            .err_bit_num            (err_bit_num_lanes[idx*7 +: 7])
        );
    end // secded_lanes
endgenerate
//spyglass enable_block SelfDeterminedExpr-ML

rd_ie_rdata_unmerge
 rd_ie_rdata_unmerge(
   .data_bus_width    (reg_ddrc_data_bus_width),
   .data              (corrected_data_w),
   .unmerged_rdata    (corrected_data)
);

//-------------------------------------------------------------------
// counter for each IE_BWT
//------------------------------------------------------------------
wire new_ecc_cmd_done;
assign new_ecc_cmd_done = ecc_region_vld_i && rt_rd_eod_i;

generate
   for (idx=0; idx<NO_OF_BRT; idx=idx+1) begin : IE_BRT_MNGR
      ie_brt_mngr
       #(
         .TOKEN_ID         (idx)
        ,.TOKEN_BITS       (BRT_BITS) 
      )
      ie_brt_mngr(
         .core_ddrc_core_clk  (core_ddrc_core_clk)
        ,.core_ddrc_rstn      (core_ddrc_rstn)
        ,.ddrc_cg_en          (ddrc_cg_en) 
        //RT to RD 
        ,.new_cmd             (new_ecc_cmd_done) 
        ,.cmd_token_id        (ih_rd_lkp_brt_i)     
        //IH to RD 
        ,.ie_token_id         (ih_rd_ie_brt)
        ,.ie_cnt_inc          (ih_rd_ie_rd_cnt_inc)
        ,.ie_blk_end          (ih_rd_ie_blk_rd_end)

        ,.free_ack            (free_ack_vct[idx])
        //output
        ,.free_req            (free_req_vct[idx])
      );
    end 
endgenerate

//-----------------------------------------------------------------
// SCH ECC ARRAY
//-----------------------------------------------------------------

//localparam NO_OF_BRT_POW2 = 2**BRT_BITS; 
wire [NO_OF_BRT_POW2-1:0] free_req_vct_pow2;
generate 
   if(NO_OF_BRT_POW2>NO_OF_BRT) begin: NOTPOW2
      assign free_req_vct_pow2 = {{(NO_OF_BRT_POW2-NO_OF_BRT){1'b0}}, free_req_vct};
   end else begin: ISPOW2
      assign free_req_vct_pow2 = free_req_vct;
   end
endgenerate

wire req_vct_selected_vld_unused;
wire req_vct_tag_selected_unused;

wire  [BRT_BITS-1:0]    selected_token;
select_net_lite

#(
   .TAG_BITS(0),
   .NUM_INPUTS (NO_OF_BRT_POW2))
U_req_vct_selnet 
(
   .clk                   (core_ddrc_core_clk),
   .resetb                (core_ddrc_rstn),
   .tags                  ({NO_OF_BRT_POW2{1'b0}}),
   .vlds                  (free_req_vct_pow2),
   .wall_next             ({BRT_BITS{1'b0}}),  //set to 0
   .selected_vld          (req_vct_selected_vld_unused),  //selected_vld is same as |vlds;
   .tag_selected          (req_vct_tag_selected_unused), //not used
   .selected              (selected_token)
);
//----------------------------------------------------------
// Free block write token
//----------------------------------------------------------
//spyglass disable_block W415a
//SMD: Signal is being assigned multiple times in same always block. 
//SJ: Using initialization in process to minimize code - sets the default for any hanging branches, avoids latches
always @ (*) begin
   free_ack_vct = {NO_OF_BRT{1'b0}};
   for (i=0; i<NO_OF_BRT; i=i+1) begin
      if(i==selected_token)begin
         free_ack_vct[i] = 1'b1;
      end
   end
end
//spyglass enable_block W415a
assign rd_ih_free_brt_vld  = |free_req_vct;
assign rd_ih_free_brt      = selected_token;


//------------------------------------------------------------------
// Store ecc_err (uncorrected error in read of RMW)
//------------------------------------------------------------------

//only write when read part of RMW.
//only wirte at the end of the burst
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_err_ram_wr        <= 1'b0;
      ecc_err_ram_waddr     <= {ECC_ERR_RAM_ADDR_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      ecc_err_ram_wr      <= (ie_rt_rd_rmwtype==(`MEMC_RMW_TYPE_PARTIAL_NBW)) & ptc_region_vld & data_out_eod & ~ie_mrr_operation_on ;
      ecc_err_ram_waddr   <= ecc_err_ram_waddr_t;
   end
end

//accumulate uncorrected error in one burst
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_err_ram_wdata      <= {ECC_ERR_RAM_WIDTH{1'b0}};
   end else if(ddrc_cg_en) begin
      if(data_out_vld & data_out_eod) begin
         ecc_err_ram_wdata   <= ecc_err_ram_wdata_acc | ecc_err_int;
      end
   end
end

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_err_ram_wdata_acc      <= {ECC_ERR_RAM_WIDTH{1'b0}};
   end else if(ddrc_cg_en) begin
      if(data_out_vld) begin
         if(data_out_eod) begin
            ecc_err_ram_wdata_acc   <= {ECC_ERR_RAM_WIDTH{1'b0}};
         end else begin
            ecc_err_ram_wdata_acc   <= ecc_err_ram_wdata_acc | ecc_err_int;
         end
      end
   end
end

always @ (*) begin
   for (i=0; i<MEMC_WRDATA_CYCLES; i=i+1 )
      if(i==dfi_word_num)
         ecc_err_int[i*SECDED_LANES+: SECDED_LANES] = uncorrected_err;
      else
         ecc_err_int[i*SECDED_LANES+: SECDED_LANES] = {SECDED_LANES{1'b0}};
end

ie_err_ram

#(
    .WIDTH         (ECC_ERR_RAM_WIDTH)
   ,.DEPTH         (ECC_ERR_RAM_DEPTH)
   ,.ADDR_BITS     (ECC_ERR_RAM_ADDR_BITS)
   ,.RD_CLR        (1'b1)   //1: the mask will be clear after read. 0: no clear after read.
   ,.REGOUT        (1'b0)   //1: rdata valid in the next cycle of raddr, like RAM;
                            //0: rdata valid in the same cycle with raddr, like ROM;

) ie_err_ram
(  
    .clk             (core_ddrc_core_clk)
   ,.rstn            (core_ddrc_rstn)
   ,.wr              (ecc_err_ram_wr)
   ,.wdata           (ecc_err_ram_wdata)
   ,.waddr           (ecc_err_ram_waddr)
   ,.rd              (mr_ecc_err_rd)
   ,.raddr           (mr_ecc_err_raddr)
   ,.rdata           (ecc_err_mr_rdata)
);

//-----------------------------------------------------------------
//Log registers
//
//-----------------------------------------------------------------
wire [5:0] ie_word_num;
assign ie_word_num = {{(6-`MEMC_FREQ_RATIO-WRDATA_CYCLES_BITS){1'b0}}, dfi_word_num_log, {(`MEMC_FREQ_RATIO){1'b0}}};

reg [SECDED_LANES*(`MEMC_ECC_SYNDROME_WIDTH)-1:0]   ecc_corr_bit_mask_lanes;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * 7)' found in module 'rd_ie_rdata_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.
always @ (*)
begin
   for(i=0;i<SECDED_LANES;i=i+1)
      ecc_corr_bit_mask_lanes[i*(`MEMC_ECC_SYNDROME_WIDTH)+:(`MEMC_ECC_SYNDROME_WIDTH)] = f_bitnum_to_bitmask(err_bit_num_lanes[i*7+:7]);
end
//spyglass enable_block SelfDeterminedExpr-ML

rd_ie_log_reg

#(
     .ECC_INFO_WIDTH           (ECC_INFO_WIDTH         ) 
    ,.CORE_DATA_WIDTH          (CORE_DATA_WIDTH        )
    ,.MEMC_ECC_SYNDROME_WIDTH  (`MEMC_ECC_SYNDROME_WIDTH)
    ,.ECC_LANES                (SECDED_LANES           )
    ,.DATA_ECC_BITS_PER_LANE   (DATA_ECC_BITS_PER_LANE )
    ,.REG_IN_EN                (0)
    ,.ECCAP_TH_WIDTH           (ECCAP_TH_WIDTH)

) rd_ie_log_reg (
     .core_ddrc_core_clk            (core_ddrc_core_clk) 
    ,.core_ddrc_rstn                (core_ddrc_rstn)
// Internal register/signals
    ,.rt_rd_ecc_info                (ie_rt_rd_ecc_info) // address, etc. from RT and provided to ECC wire
    ,.rd_dh_word_num                (ie_word_num) 

    ,.corrected_err                 (corrected_err_log)
    ,.uncorrected_err               (uncorrected_err_log)
    ,.data_ecc_lanes                (data_ecc_lanes_r)
    ,.ecc_corr_bit_num_lanes        (err_bit_num_lanes)
    ,.ecc_corr_bit_mask_lanes       (ecc_corr_bit_mask_lanes)


// REGISTERS INTERFACE
    ,.reg_ddrc_ecc_clr_corr_err       (reg_ddrc_ecc_clr_corr_err      ) // Clear corrected error interrupt
    ,.reg_ddrc_ecc_clr_uncorr_err     (reg_ddrc_ecc_clr_uncorr_err    ) // Clear uncorrected error interrupt
    ,.reg_ddrc_ecc_clr_corr_err_cnt   (reg_ddrc_ecc_clr_corr_err_cnt  ) // Clear correctable ECC error count
    ,.reg_ddrc_ecc_clr_uncorr_err_cnt (reg_ddrc_ecc_clr_uncorr_err_cnt) // Clear uncorrectable ECC error count
    ,.ddrc_reg_ecc_corrected_err      (ddrc_reg_ecc_corrected_err     ) // single-bit error that will be corrected, per lane
    ,.ddrc_reg_ecc_uncorrected_err    (ddrc_reg_ecc_uncorrected_err   ) // double-bit error detected in read data, per lane
    ,.ddrc_reg_ecc_corrected_bit_num  (ddrc_reg_ecc_corrected_bit_num ) // bit number corrected by single-bit error
    ,.ddrc_reg_ecc_corr_err_cnt       (ddrc_reg_ecc_corr_err_cnt      ) // Count of correctable ECC errors
    ,.ddrc_reg_ecc_uncorr_err_cnt     (ddrc_reg_ecc_uncorr_err_cnt    ) // Count of uncorrectable ECC errors
    ,.ddrc_reg_ecc_corr_syndromes     (rd_dh_ecc_corr_syndromes    ) // data pattern that resulted in an error;
    ,.ddrc_reg_ecc_uncorr_syndromes   (rd_dh_ecc_uncorr_syndromes  ) // data pattern that resulted in an error;
    ,.ddrc_reg_ecc_corr_bit_mask      (rd_dh_ecc_corr_bit_mask     ) // mask for the bit that is corrected
    ,.ddrc_reg_ecc_corr_info          (rd_dh_ecc_corr_info         ) //
    ,.ddrc_reg_ecc_uncorr_info        (rd_dh_ecc_uncorr_info       ) //
    ,.ddrc_reg_ecc_corr_word_num      (rd_dh_ecc_corr_word_num     ) //
    ,.ddrc_reg_ecc_uncorr_word_num    (rd_dh_ecc_uncorr_word_num   ) //
    ,.data_out_eod                    (data_out_eod)
    ,.ddrc_reg_ecc_ap_err             (ddrc_reg_ecc_ap_err)
    ,.reg_ddrc_ecc_ap_en              (reg_ddrc_ecc_ap_en)
    ,.reg_ddrc_ecc_ap_err_intr_clr    (reg_ddrc_ecc_ap_err_intr_clr)
    ,.reg_ddrc_ecc_ap_err_threshold   (reg_ddrc_ecc_ap_err_threshold)
    ,.reg_ddrc_ecc_mode               (reg_ddrc_ecc_mode)

);


   assign par_rdata_err_pulse = 1'b0;


function automatic [71:0] f_bitnum_to_bitmask;
    input   [6:0]  bitnum;
    reg     [71:0] bitmask_enc;
    begin
// corrected bit number mask generation
// put a 1 into the location where bit was corrected
// this is an encoded value with check bits in middle of data bits
   bitmask_enc = ({{71{1'b0}}, 1'b1} << bitnum);

// encoded value is decoded here - this logic is the same as the one taken from rd_secded_lane.v
   f_bitnum_to_bitmask     = {bitmask_enc[64],
                                  bitmask_enc[32],
                                  bitmask_enc[16],
                                  bitmask_enc[8],
                                  bitmask_enc[4],
                                  bitmask_enc[2:0],
                                  bitmask_enc[71:65], //64
                                  bitmask_enc[63:33], //32
                                  bitmask_enc[31:17], //16
                                  bitmask_enc[15: 9], //8
                                  bitmask_enc[ 7: 5], //4
                                  bitmask_enc[    3] };


    end
endfunction


`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------

`ifdef SNPS_ASSERT_ON

      property p_rd_eccap_zero_with_overhead_command;
        @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
          (rt_rd_ie_rd_type==`IE_RD_TYPE_RE_B) -> rt_rd_eccap == 0 ;
      endproperty

      a_rd_eccap_zero_with_overhead_command : assert property (p_rd_eccap_zero_with_overhead_command)
      else $error("%m @ %t Error : rt_rd_eccap must be 0 with RE_*", $time);


`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
