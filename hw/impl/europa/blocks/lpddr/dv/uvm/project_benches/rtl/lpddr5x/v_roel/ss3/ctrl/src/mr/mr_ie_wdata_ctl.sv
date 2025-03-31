//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/mr/mr_ie_wdata_ctl.sv#5 $
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
module mr_ie_wdata_ctl
import DWC_ddrctl_reg_pkg::*;
#(
    parameter CORE_DATA_WIDTH       = `MEMC_DFI_DATA_WIDTH   // internal data width
   ,parameter CORE_MASK_WIDTH       = `MEMC_DFI_DATA_WIDTH/8 // data mask width
   ,parameter WRCAM_ADDR_WIDTH      = `MEMC_WRCMD_ENTRY_BITS // bits to address into CAM
   ,parameter WRDATA_RAM_ADDR_WIDTH = `UMCTL2_WDATARAM_AW    // data width to RAM
   ,parameter ECC_INFO_WIDTH        = 35
   ,parameter NO_OF_BWT             = 16
   ,parameter BT_BITS               = 4
   ,parameter BWT_BITS              = 4
   ,parameter BRT_BITS              = 4
   ,parameter IE_WR_TYPE_BITS       = 2
   ,parameter IE_BURST_NUM_BITS     = `MEMC_BURST_LENGTH==16 ? 4 : 3
   ,parameter ECC_RAM_DEPTH         = `MEMC_ECC_RAM_DEPTH
   ,parameter ECC_RAM_ADDR_BITS     = `log2(`MEMC_ECC_RAM_DEPTH)
   ,parameter ECC_ERR_RAM_ADDR_BITS = 4
   ,parameter ECC_ERR_RAM_WIDTH      = 16 //MEMC_WRDATA_CYCLES*SECDED_LANES;

)
(  
    input                              core_ddrc_core_clk
   ,input                              core_ddrc_rstn
   ,input                              ddrc_cg_en 
   ,input                              reg_ddrc_lpddr4        // select LPDDR4 SDRAM
   ,input                              reg_ddrc_lpddr5        // select LPDDR5 SDRAM
   ,input [BURST_RDWR_WIDTH-1:0]       reg_ddrc_burst_rdwr
   ,input                              dh_mr_frequency_ratio
   ,input [1:0]                        dh_mr_data_bus_width


   // signals from mr_ram_rd_pipeline
   ,input                              new_ram_rd_cmd // a new command
   ,input                              ie_mwr_flag
   ,input                              free_wr_entry_valid // a new command is done
   ,input  [WRDATA_RAM_ADDR_WIDTH -1:0]mr_me_raddr  // read address to write data RAM
   ,input                              mr_me_re       // read enable to write data RAM
   ,input                              ram_data_vld            // data from write data RAM is valid
   ,input                              ram_data_vld_early
   ,input [CORE_DATA_WIDTH-1:0]        me_mr_rdata     // write data read from write data RAM
   ,input [CORE_DATA_WIDTH/8-1:0]      me_mr_rdatamask // write data read from write data RAM
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: Used in generate block and/or in TB (sva_ddrc.sv))
   ,input [CORE_MASK_WIDTH-1:0]        me_mr_rdatapar

   // TE to MR for receive data
   ,input  [BT_BITS-1:0]               te_mr_ie_bt
//spyglass enable_block W240
   ,input  [BWT_BITS-1:0]              te_mr_ie_bwt
   ,input  [BRT_BITS-1:0]              te_mr_ie_brt
   ,input                              te_mr_ie_brt_vld
   ,input  [IE_WR_TYPE_BITS-1:0]       te_mr_ie_wr_type
   ,input  [IE_BURST_NUM_BITS-1:0]     te_mr_ie_blk_burst_num  //only for the Data command
   ,input                              te_mr_eccap
   // IH to MR for load BWT
   ,input  [BWT_BITS-1:0]              ih_mr_ie_bwt       
   ,input  [BRT_BITS-1:0]              ih_mr_ie_brt       
   ,input                              ih_mr_ie_brt_vld       
   ,input  [NO_OF_BWT-1:0]             ih_mr_ie_wr_cnt_dec_vct
   ,input                              ih_mr_ie_wr_cnt_inc
   ,input                              ih_mr_ie_blk_wr_end
   ,output                             wr_ecc_vld
   ,output reg [CORE_DATA_WIDTH-1:0]   ecc_wdata
   ,output reg [CORE_MASK_WIDTH-1:0]   ecc_wdata_par
   ,output reg [CORE_DATA_WIDTH/8-1:0] ecc_wdata_mask_n
   // ocpar interrupt
   ,output                             wdata_par_err
   // MR to IH for free BWT
   ,output                             mr_ih_free_bwt_vld
   ,output [BWT_BITS-1:0]              mr_ih_free_bwt

   ,input                              rd_mr_free_brt_vld
   ,input  [BRT_BITS-1:0]              rd_mr_free_brt

// ECC ACC and ECC RAM interface
   ,output                             mr_ecc_acc_wr
   ,output [ECC_RAM_ADDR_BITS-1:0]     mr_ecc_acc_waddr
   ,output [CORE_DATA_WIDTH-1:0]       mr_ecc_acc_wdata
   ,output [CORE_MASK_WIDTH-1:0]       mr_ecc_acc_wdata_par
   ,output [CORE_MASK_WIDTH-1:0]       mr_ecc_acc_wdata_mask_n
   ,output                             mr_ecc_acc_rd
   ,output [ECC_RAM_ADDR_BITS-1:0]     mr_ecc_acc_raddr
   ,input  [CORE_DATA_WIDTH-1:0]       ecc_acc_mr_rdata
   ,input  [CORE_MASK_WIDTH-1:0]       ecc_acc_mr_rdata_par
   ,input  [CORE_MASK_WIDTH-1:0]       ecc_acc_mr_rdata_mask_n
   ,output [ECC_RAM_ADDR_BITS-1:0]     mr_ecc_ram_raddr_2
   ,input  [CORE_DATA_WIDTH-1:0]       ecc_ram_mr_rdata_2
   ,input  [CORE_MASK_WIDTH-1:0]       ecc_ram_mr_rdata_par_2
   // Flush ECC ACC
   ,output                             mr_ecc_acc_flush_en
   ,output [BWT_BITS-1:0]              mr_ecc_acc_flush_addr
// ECC ERR RAM interface
   ,output                             mr_ecc_err_rd
   ,output [ECC_ERR_RAM_ADDR_BITS-1:0] mr_ecc_err_raddr
   ,input  [ECC_ERR_RAM_WIDTH-1:0]     ecc_err_mr_rdata
);

//------------------------------ LOCAL PARAMETERS ------------------------------------
localparam  DATA_BITS_PER_LANE  = 64;     // data bits per ECC engine
localparam  ECC_BITS_PER_LANE   = 8;      // ecc bits per ECC engine
localparam  CORE_DATA_WIDTH_EXT = (CORE_DATA_WIDTH<DATA_BITS_PER_LANE) ? DATA_BITS_PER_LANE : CORE_DATA_WIDTH;
localparam  ECC_DATA_WIDTH_EXT  = (CORE_DATA_WIDTH<DATA_BITS_PER_LANE) ? ECC_BITS_PER_LANE  : CORE_DATA_WIDTH/8;

localparam  SECDED_LANES        = CORE_DATA_WIDTH_EXT / DATA_BITS_PER_LANE; // number of data lanes for SEC/DED

localparam  MEMC_WRDATA_CYCLES  = `MEMC_WRDATA_CYCLES;
// WRDATA_CYCLES_BITS: 1 - when MEMC_WRDATA_CYCLES=2.
// WRDATA_CYCLES_BITS: 2 - when MEMC_WRDATA_CYCLES=4.
// WRDATA_CYCLES_BITS: 3 - when MEMC_WRDATA_CYCLES=8.
localparam WRDATA_CYCLES_BITS   = MEMC_WRDATA_CYCLES==8 ? 3 : MEMC_WRDATA_CYCLES==4 ? 2 : 1; // that is equal to WRDATA_RAM_AW - WRCAM_AW. 

wire                                   ecc_region_vld;

wire                                   data_in_ecc_lanes_vld;
wire [SECDED_LANES-1:0]                data_in_ecc_lanes_mask;
wire [CORE_DATA_WIDTH_EXT/8-1:0]       merged_rdatamask;
wire [CORE_DATA_WIDTH_EXT-1:0]         data_in_ecc_lanes;
wire [ECC_DATA_WIDTH_EXT-1:0]          ecc_lanes;
reg  [ECC_DATA_WIDTH_EXT-1:0]          ecc_lanes_werr;

wire [DATA_BITS_PER_LANE/8-1:0]        me_mr_rdatamask_per_lane[0:SECDED_LANES-1]; //used for assertion

wire [WRDATA_CYCLES_BITS-1:0]          word_num;              // word address in one burst.
reg  [WRDATA_CYCLES_BITS-1:0]          word_num_r;              // word address in one burst.
reg  [WRDATA_CYCLES_BITS-1:0]          word_num_2r;              // word address in one burst.
wire [2:0]                             burst_num;    //word address in one block (8 burst)
reg  [3+WRDATA_CYCLES_BITS-1:0]        burst_num_word_num_r;  //word address in one block (8 burst)
reg  [3+WRDATA_CYCLES_BITS-1:0]        burst_num_word_num_2r; //word address in one block (8 burst)
wire [3+WRDATA_CYCLES_BITS-1:0]        burst_num_word_num;    //word address in one block (8 burst)
reg  [ECC_RAM_ADDR_BITS-1:0]           ecc_acc_waddr_r;
reg  [ECC_RAM_ADDR_BITS-1:0]           ecc_acc_waddr_2r;
wire [ECC_RAM_ADDR_BITS-1:0]           ecc_acc_waddr;
wire                                   ecc_acc_wr;
wire [CORE_DATA_WIDTH-1:0]             ecc_acc_wdata;
wire [CORE_DATA_WIDTH-1:0]             ecc_acc_wdata_eccap; // After ECC Address protection
wire [CORE_MASK_WIDTH-1:0]             ecc_acc_wdata_par;
reg  [CORE_DATA_WIDTH/8-1:0]           ecc_acc_wdata_mask_n;


reg                                    ecc_err_ram_rd_r;
reg  [ECC_ERR_RAM_ADDR_BITS-1:0]       ecc_err_ram_raddr_r;
reg  [ECC_ERR_RAM_WIDTH-1:0]           ecc_err_r;

wire                                   ecc_acc_rd;
wire [ECC_RAM_ADDR_BITS-1:0]           ecc_acc_raddr;
wire [CORE_DATA_WIDTH-1:0]             ecc_acc_rdata;
wire [CORE_MASK_WIDTH-1:0]             ecc_acc_rdata_par;
wire [CORE_DATA_WIDTH/8-1:0]           ecc_acc_rdata_mask_n;

///reg  new_ram_rd_cmd_r;
///wire new_ecc_cmd;

reg  [NO_OF_BWT-1:0]                   free_ack_vct;
wire [NO_OF_BWT-1:0]                   free_req_vct;

wire [NO_OF_BWT-1:0]                   re_bw_vld_vct;
wire [BRT_BITS*NO_OF_BWT-1:0]          re_bw_brt_vct;
wire [BWT_BITS-1:0]                    selected_token;
wire [WRCAM_ADDR_WIDTH-1:0]            wr_ecc_entry;
wire [1:0]                             rmw_type;
wire [BRT_BITS-1:0]                    we_ie_brt;
wire                                   we_ie_brt_vld;

reg  [WRDATA_CYCLES_BITS:0]            ecc_word_cnt;
wire [WRDATA_CYCLES_BITS-1:0]          ecc_word_cnt_pw;
wire                                   wr_ecc_done;
reg                                    ecc_region_cmd_r;
reg                                    ecc_region_cmd_2r;
reg                                    wr_ecc_cmd_r;
reg                                    wr_ecc_cmd_2r;
reg [BWT_BITS-1:0]                     bwt_r;
reg [BRT_BITS-1:0]                     brt_r;

wire                                   new_ecc_cmd_done;
reg                                    new_ecc_cmd_done_r;

wire [71:0]                            secded_lane_out_unused[0:SECDED_LANES-1]; //unused

wire [CORE_DATA_WIDTH-1:0]             me_mr_rdata_swp;     // data after swap for ddr4 bc
wire [CORE_MASK_WIDTH-1:0]             me_mr_rdatamask_swp; // 

//-------------------------------------------------
// connnect ECC ACC interface to outside
//-------------------------------------------------
assign   mr_ecc_acc_wr           =     ecc_acc_wr;
assign   mr_ecc_acc_waddr        =     ecc_acc_waddr;
assign   mr_ecc_acc_wdata        =     ecc_acc_wdata_eccap;
assign   mr_ecc_acc_wdata_par    =     ecc_acc_wdata_par;
assign   mr_ecc_acc_wdata_mask_n =     ecc_acc_wdata_mask_n;
assign   mr_ecc_acc_rd           =     ecc_acc_rd;

assign   mr_ecc_acc_raddr        =     ecc_acc_raddr;
assign   ecc_acc_rdata           =     ecc_acc_mr_rdata;
assign   ecc_acc_rdata_par       =     ecc_acc_mr_rdata_par;
assign   ecc_acc_rdata_mask_n    =     ecc_acc_mr_rdata_mask_n;

assign   mr_ecc_err_rd           =     ecc_err_ram_rd_r;
assign   mr_ecc_err_raddr        =     ecc_err_ram_raddr_r;

// as mr is wired to reg_ddrc_burst_rdwr_int at toplevel of ddrc.v
// adjust for shift >>1 if FREQ_RATIO=2, but only if SW selected 1:2 mode
// if FREQ_RATIO-2 and SW selected 1:1 mode, do not re-adjust as reg_ddrc_burst_rdwr=reg_ddrc_burst_rdwr_int
// 
//  `ifdef MEMC_FREQ_RATIO_2
wire [3:0] reg_ddrc_burst_rdwr_adj;
  assign reg_ddrc_burst_rdwr_adj = (dh_mr_frequency_ratio) ? reg_ddrc_burst_rdwr[3:0] : {reg_ddrc_burst_rdwr[2:0], 1'b0};
//  `endif //MEMC_FREQ_RATIO_2

// ECC Address Protection
// If command parity is 1, invert lowest two bit of ECC for every byte
// The same is done also in Read
reg        te_mr_eccap_1r; // One cycle delay of te_mr_eccap
reg        te_mr_eccap_2r; // Two cycle delay of te_mr_eccap (align to ecc_acc_wr)

// Generate delay signals
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      te_mr_eccap_1r <= 1'b0;
      te_mr_eccap_2r <= 1'b0;
   end
   else begin
      te_mr_eccap_1r <= te_mr_eccap;
      te_mr_eccap_2r <= te_mr_eccap_1r;
   end
end

genvar bit_idx;
generate
   for (bit_idx=0; bit_idx<CORE_DATA_WIDTH; bit_idx=bit_idx+1) begin : ECCAP
      if (bit_idx%8<=1) begin : ECCAP_INVERT // Invert lowest two bit for every byte if te_mr_eccap_2r==1 
         //reduce one pipeline temp, will re-enable 2 pipeline stage after LPDDR4X
         assign ecc_acc_wdata_eccap[bit_idx] = ecc_acc_wdata[bit_idx] ^ te_mr_eccap_2r; // Invert
         //assign ecc_acc_wdata_eccap[bit_idx] = ecc_acc_wdata[bit_idx] ^ te_mr_eccap_1r; // Invert
      end
      else begin : ECCAP_NON_INVERT
         assign ecc_acc_wdata_eccap[bit_idx] = ecc_acc_wdata[bit_idx];
      end
   end
endgenerate



integer i; // for loop index
genvar idx;
//---------------------------------------------------------------------
// Distigush the data is ECC protected or not
// by checking ie_wr_type == WD_E(1)
//
// Distigush the data is ECC command or not
// by checking ie_wr_type == WD_E(1)
//---------------------------------------------------------------------

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_region_cmd_r  <= 1'b0;
      ecc_region_cmd_2r <= 1'b0;
      wr_ecc_cmd_r      <= 1'b0;
      wr_ecc_cmd_2r     <= 1'b0;

      bwt_r          <= {BWT_BITS{1'b0}};
      brt_r          <= {BRT_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      ecc_region_cmd_r  <= (te_mr_ie_wr_type == `IE_WR_TYPE_WD_E) ? 1'b1 : 1'b0;
      ecc_region_cmd_2r <= ecc_region_cmd_r;
      wr_ecc_cmd_r      <= (te_mr_ie_wr_type == `IE_WR_TYPE_WE_BW) ? 1'b1 : 1'b0;
      wr_ecc_cmd_2r     <= wr_ecc_cmd_r;

      bwt_r          <= te_mr_ie_bwt;
      brt_r          <= te_mr_ie_brt;
   end
end
assign ecc_region_vld = ecc_region_cmd_2r && ram_data_vld;
assign wr_ecc_vld     = wr_ecc_cmd_2r && ram_data_vld;

//---------------------------------------------------------------------
// Encoder
// The number of encoder depend on the HIF data width(CORE_DATA_WIDTH) 
// CORE_DATA_WIDTH could be: 64, 128, 256.
// The number of encoder is:  1,   2,   4.
//---------------------------------------------------------------------


    assign data_in_ecc_lanes_vld  = ecc_region_vld;

   assign me_mr_rdata_swp      =
                                  me_mr_rdata;
   assign me_mr_rdatamask_swp  =
                                  me_mr_rdatamask;
   mr_ie_wdata_merge
    mr_ie_wdata_merge(
      // Input 
      .data_bus_width   (dh_mr_data_bus_width),
      .data             (me_mr_rdata_swp),
      .datamask         (me_mr_rdatamask_swp),
      // Output
      .merged_rdata     (data_in_ecc_lanes)
     ,.merged_rdatamask (merged_rdatamask)
   );

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(idx * DATA_BITS_PER_LANE)' found in module 'mr_ie_wdata_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.
generate
  for (idx=0; idx<SECDED_LANES; idx=idx+1) begin : data_lane_mask
     assign data_in_ecc_lanes_mask[idx] = |merged_rdatamask[idx*(DATA_BITS_PER_LANE/8) +: DATA_BITS_PER_LANE/8];
  //spyglass disable_block W528
  //SMD: A signal or variable is set but never read
  //SJ: Used in RTL assertion
     assign me_mr_rdatamask_per_lane[idx] = merged_rdatamask[idx*(DATA_BITS_PER_LANE/8) +: DATA_BITS_PER_LANE/8]; //used for assertion.
  //spyglass enable_block W528
  end
      
endgenerate


//spyglass disable_block W287b
//SMD: Instance output port secded_lane_out is not connected
//SJ: Intentionally left unconnected

// Generate the appropriate number of error-correcting lanes for this ECC implementation
generate
   for (idx=0; idx<SECDED_LANES; idx=idx+1) begin : secded_lanes
         mr_secded_lane
          mr_secded_lane (
            .lane_in     (data_in_ecc_lanes[(idx*DATA_BITS_PER_LANE) +: DATA_BITS_PER_LANE]),
            .ecc_parity  (ecc_lanes[idx*ECC_BITS_PER_LANE +: ECC_BITS_PER_LANE]),
            .secded_lane_out(secded_lane_out_unused[idx])
        );
    end // secded_lanes
endgenerate
//spyglass enable_block W287b
//spyglass enable_block SelfDeterminedExpr-ML

//-------------------------------------------------------------------
// ECC ACC array interface
// ------------------------------------------------------------------
assign word_num           = mr_me_raddr[WRDATA_CYCLES_BITS-1:0];    //offset address in one burst i.e. BL8/BL16

assign burst_num          = te_mr_ie_blk_burst_num[2:0] ;

assign burst_num_word_num = reg_ddrc_burst_rdwr_adj==4'b0100 ? te_mr_ie_blk_burst_num[3:0] :
                                                               {te_mr_ie_blk_burst_num[2:0], word_num} ;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((3 + WRDATA_CYCLES_BITS) - 1)' found in module 'mr_ie_wdata_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.

// register address inorder to align address with data.
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_acc_waddr_r       <= {ECC_RAM_ADDR_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      ecc_acc_waddr_r[ECC_RAM_ADDR_BITS-1:WRDATA_CYCLES_BITS] <= te_mr_ie_bwt;
      ecc_acc_waddr_r[WRDATA_CYCLES_BITS-1:0] <= burst_num_word_num[(3+WRDATA_CYCLES_BITS-1)-:WRDATA_CYCLES_BITS];
   end
end
//spyglass enable_block SelfDeterminedExpr-ML

// register address to align ECC because  Encoder has one FF.
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_acc_waddr_2r       <= {ECC_RAM_ADDR_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      ecc_acc_waddr_2r       <= ecc_acc_waddr_r;
   end
end

// register address 2 cycles to align with ECC
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      burst_num_word_num_r  <= {(3+WRDATA_CYCLES_BITS){1'b0}};
      burst_num_word_num_2r <= {(3+WRDATA_CYCLES_BITS){1'b0}};
   end else if(ddrc_cg_en) begin
      burst_num_word_num_r  <= burst_num_word_num;
      burst_num_word_num_2r <= burst_num_word_num_r;
   end
end

// register 2 cycle for word_num to align with ecc_err_r
// register 2 cycle for ecc_err_vld to align with ecc_err_r
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      word_num_r       <= {WRDATA_CYCLES_BITS{1'b0}};
      word_num_2r      <= {WRDATA_CYCLES_BITS{1'b0}};
      new_ecc_cmd_done_r <= 1'b0;
   end else if(ddrc_cg_en) begin
      word_num_r       <= word_num;
      word_num_2r      <= word_num_r;
      new_ecc_cmd_done_r <= new_ecc_cmd_done;
   end
end

// ecc_acc_waddr is delayed 2 cycle from te_mr_ie_xxx
assign ecc_acc_waddr = ecc_acc_waddr_2r;
assign ecc_acc_wr    = data_in_ecc_lanes_vld;


wire [2:0] ecc_bytes;
// ecc_byte is vaild in same cycle as ecc_acc_wr and ecc_acc_waddr
assign ecc_bytes = burst_num_word_num_2r[2:0];

//--------------------------------------------------------
//inject error when uncorrected error in read part of RMW
//
// ECC ERR RAM interface
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_err_ram_raddr_r       <= {ECC_ERR_RAM_ADDR_BITS{1'b0}};
      ecc_err_ram_rd_r          <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(new_ram_rd_cmd & mr_me_re & (te_mr_ie_wr_type == `IE_WR_TYPE_WD_E) & te_mr_ie_brt_vld) begin
         ecc_err_ram_rd_r       <= 1'b1; 
         ecc_err_ram_raddr_r    <= {te_mr_ie_brt,burst_num};
      end else begin
         ecc_err_ram_rd_r       <= 1'b0; 
      end
   end
end

// register ecc error for one burst
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_err_r       <= {ECC_ERR_RAM_WIDTH{1'b0}};
   end else if(ddrc_cg_en) begin
      if(ecc_err_ram_rd_r) begin //set error when read ecc_err at the begining of burst
         ecc_err_r    <= ecc_err_mr_rdata;
      end else if(new_ecc_cmd_done_r) begin
         ecc_err_r    <= {ECC_ERR_RAM_WIDTH{1'b0}};
      end
   end
end


//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((word_num_2r * SECDED_LANES) + i)' found in module 'mr_ie_wdata_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.

always @ (*) begin
   for(i=0; i<SECDED_LANES; i=i+1)
      if((ecc_err_r[word_num_2r*SECDED_LANES+i]) )
         ecc_lanes_werr[i*ECC_BITS_PER_LANE+:ECC_BITS_PER_LANE] = ecc_lanes[i*ECC_BITS_PER_LANE+:ECC_BITS_PER_LANE] ^ 8'h3;
      else
         ecc_lanes_werr[i*ECC_BITS_PER_LANE+:ECC_BITS_PER_LANE] = ecc_lanes[i*ECC_BITS_PER_LANE+:ECC_BITS_PER_LANE] ;
end

assign ecc_acc_wdata   = {(CORE_DATA_WIDTH/ECC_DATA_WIDTH_EXT){ecc_lanes_werr}};  //data and ecc is 8:1, only 1/8 are valid.

always @ (*)
begin
   for(i=0; i<CORE_MASK_WIDTH; i=i+SECDED_LANES)
      if((i/SECDED_LANES)== ecc_bytes)
         ecc_acc_wdata_mask_n[i+:SECDED_LANES] = data_in_ecc_lanes_mask;
      else
         ecc_acc_wdata_mask_n[i+:SECDED_LANES] = {SECDED_LANES{1'b0}};
end
//spyglass enable_block SelfDeterminedExpr-ML

//-------------------------------------------------------------------
// Token manager for each IE_BWT
//------------------------------------------------------------------

assign new_ecc_cmd_done = free_wr_entry_valid && ecc_region_cmd_r && ram_data_vld_early;

generate
   for (idx=0; idx<NO_OF_BWT; idx=idx+1) begin : IE_BWT_MNGR
      ie_bwt_mngr
       #(
         .TOKEN_ID         (idx)
        ,.TOKEN_BITS       (BWT_BITS) 
      )
      ie_bwt_mngr(
         .core_ddrc_core_clk  (core_ddrc_core_clk)
        ,.core_ddrc_rstn      (core_ddrc_rstn)
        ,.ddrc_cg_en          (ddrc_cg_en)
        //TE to MR
        ,.new_cmd             (new_ecc_cmd_done)      // new ecc region command from TE
        ,.wr_ecc_cmd          (wr_ecc_done)       
        ,.cmd_token_id        (bwt_r)    
        //IH to MR
        ,.ie_token_id         (ih_mr_ie_bwt)
        ,.ie_ass_token_id     (ih_mr_ie_brt)
        ,.ie_ass_token_id_vld (ih_mr_ie_brt_vld)
        ,.ie_cnt_inc          (ih_mr_ie_wr_cnt_inc)
        ,.ie_blk_end          (ih_mr_ie_blk_wr_end)
        ,.ie_cnt_dec          (ih_mr_ie_wr_cnt_dec_vct[idx])

        ,.free_ass_token_vld  (rd_mr_free_brt_vld)
        ,.free_ass_token      (rd_mr_free_brt)

        ,.free_ack            (free_ack_vct[idx])
        //output
        ,.free_req            (free_req_vct[idx])
      );
    end // secded_lanes
endgenerate

//rd_acc_addr generate in V3
wire [WRDATA_CYCLES_BITS:0] num_wrdata_cycles;
assign num_wrdata_cycles = (dh_mr_frequency_ratio | (reg_ddrc_burst_rdwr_adj==4'b0100)) ? MEMC_WRDATA_CYCLES-1 : MEMC_WRDATA_CYCLES*2-1;    // full write

assign wr_ecc_done = (ecc_word_cnt == num_wrdata_cycles) ? 1'b1 : 1'b0;

//rd_acc_addr generate in V3
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_word_cnt <= {(WRDATA_CYCLES_BITS+1){1'b0}};
   end else if(ddrc_cg_en) begin
      if(wr_ecc_done) begin
         ecc_word_cnt <= {(WRDATA_CYCLES_BITS+1){1'b0}};
      end else if(ecc_acc_rd)  begin
         ecc_word_cnt <= ecc_word_cnt + 1'b1;
      end
   end
end

assign ecc_word_cnt_pw = word_num_r;

// ecc_acc_rd/raddr is assert 1 cycle later after wr_ecc command
// ecc_acc_rdata will be delay 1 cycle
// so totally 2 cycles from wr_ecc command to data valid.
assign ecc_acc_rd        = wr_ecc_cmd_r && ram_data_vld_early;
assign ecc_acc_raddr     = {bwt_r, ecc_word_cnt_pw};

// read ECC RAM on read path in order to merge with ECC ACC.
assign mr_ecc_ram_raddr_2 = {brt_r, ecc_word_cnt_pw};

//---------------------------------------------------------
// Free block write token
// and Flush ECC ACC for this token
//----------------------------------------------------------

localparam NO_OF_BWT_POW2 = 2**BWT_BITS; 
wire [NO_OF_BWT_POW2-1:0] free_req_vct_pow2;
generate 
   if(NO_OF_BWT_POW2>NO_OF_BWT) begin: NOTPOW2
      assign free_req_vct_pow2 = {{(NO_OF_BWT_POW2-NO_OF_BWT){1'b0}}, free_req_vct};
   end else begin: ISPOW2
      assign free_req_vct_pow2 = free_req_vct;
   end
endgenerate

wire req_vct_selected_vld_unused;
wire req_vct_tag_selected_unused;

select_net_lite

#(
   .TAG_BITS(0),
   .NUM_INPUTS (NO_OF_BWT_POW2))
U_req_vct_selnet 
(
   .clk                   (core_ddrc_core_clk),
   .resetb                (core_ddrc_rstn),
   .tags                  ({NO_OF_BWT_POW2{1'b0}}),
   .vlds                  (free_req_vct_pow2),
   .wall_next             ({BWT_BITS{1'b0}}),  //set to 0
   .selected_vld          (req_vct_selected_vld_unused),  //selected_vld is same as |vlds;
   .tag_selected          (req_vct_tag_selected_unused), //not used
   .selected              (selected_token)
);

always @ (*) begin
   free_ack_vct = {NO_OF_BWT{1'b0}};
   for(int i=0;i<NO_OF_BWT;i=i+1) begin
     if($unsigned(i) == selected_token[BWT_BITS-1:0]) begin
       free_ack_vct[i] = 1'b1;
     end
   end
end

assign  mr_ih_free_bwt_vld     = |free_req_vct;
assign  mr_ih_free_bwt         = selected_token;
assign  mr_ecc_acc_flush_en    = |free_req_vct;
assign  mr_ecc_acc_flush_addr  = selected_token;
//----------------------------------------------------
// RMW (merge Read ECC and Write ECC)
//---------------------------------------------------

//JIRA___ID: When ECC ARRAY is ready, Mask Write will become a full write.
//So: 
// if it is Mask write, only use ECC ACC's data
// if it is full write, merge ECC ARRAY with ECC ACC.
// if it is not lpddr4, set is_mwr=1 means always use ECC ACC (DM=1). 
   
// add a assertion: if it is not mask write, the ECC_ACC must full or ECC ARRAY must ready. 
wire is_mwr;

reg  mwr_flag_r;
//register ie_mwr_flag to align with data phase
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      mwr_flag_r <= 1'b0;
   end else if(ddrc_cg_en) begin
      mwr_flag_r <= ie_mwr_flag;
   end
end
assign is_mwr = (reg_ddrc_lpddr4 || reg_ddrc_lpddr5) ?  mwr_flag_r : 1'b1;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * 8)' found in module 'mr_ie_wdata_ctl'
//SJ: This coding style is acceptable and there is no plan to change it.
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ecc_wdata        <=  {CORE_DATA_WIDTH{1'b0}};
      ecc_wdata_par    <=  {CORE_MASK_WIDTH{1'b0}};
      ecc_wdata_mask_n <=  {CORE_MASK_WIDTH{1'b0}};
   end else if(ddrc_cg_en) begin
      for (i=0; i<CORE_DATA_WIDTH/8; i=i+1) begin
         ecc_wdata[i*8+:8]   <=  (~is_mwr & ~ecc_acc_rdata_mask_n[i]) ? ecc_ram_mr_rdata_2[i*8+:8] : ecc_acc_rdata[i*8+:8];
         ecc_wdata_par[i]    <=  (~is_mwr & ~ecc_acc_rdata_mask_n[i]) ? ecc_ram_mr_rdata_par_2[i]  : ecc_acc_rdata_par[i];
         ecc_wdata_mask_n[i] <=  ~is_mwr ? 1'b1 :  ecc_acc_rdata_mask_n[i];
      end
   end
end
//spyglass enable_block SelfDeterminedExpr-ML

   
   assign wdata_par_err       = 1'b0;
   assign ecc_acc_wdata_par   = 'h0;


`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON

//Check selected_token should less than NO_OF_BWT(who could not power of 2).
property p_selected_token_less_than_num_token;
  @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
    (|free_req_vct) |-> (selected_token < NO_OF_BWT);
endproperty
a_selected_token_less_than_num_token: assert property (p_selected_token_less_than_num_token)
else $error("%m @ %t Error : selected_token should less than number of token", $time);

//assertion for new_ram_rd_cmd and ram_data_vld;
property p_new_ram_rd_cmd;
  @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
    (new_ram_rd_cmd & mr_me_re) |-> ##2 (ram_data_vld);
endproperty
a_new_ram_rd_cmd: assert property (p_new_ram_rd_cmd)
else $error("%m @ %t Error : ram_data_vld is not assert after new_ram_rd_cmd", $time);


generate
   for (idx=0; idx<SECDED_LANES; idx=idx+1) begin : assert_gen
      property p_ecc_code_all1_or_all0;
        @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
          (data_in_ecc_lanes_vld) |-> (&me_mr_rdatamask_per_lane[idx] || ~|me_mr_rdatamask_per_lane[idx]);
      endproperty
      
      a_ecc_code_all1_or_all0 : assert property (p_ecc_code_all1_or_all0)
      else $error("%m @ %t Error : Each ecc lane should all 1 or all0", $time);
   end
endgenerate

      property p_wr_eccap_zero_with_overhead_command;
        @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
          ($past(te_mr_ie_wr_type,2)==`IE_WR_TYPE_WE_BW) -> te_mr_eccap_2r == 0 ;
      endproperty

      a_wr_eccap_zero_with_overhead_command : assert property (p_wr_eccap_zero_with_overhead_command)
      else $error("%m @ %t Error : te_mr_eccap must be 0 with WE_BW", $time);


`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
