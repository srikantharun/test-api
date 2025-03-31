//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/rd/rd_ie_log_reg.sv#3 $
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
// ----------------------------------------------------------------------------
//                              Description
//
//===========================================================================

`include "DWC_ddrctl_all_defs.svh"
module rd_ie_log_reg
#(
     parameter       ECC_INFO_WIDTH              = 35   // width of read info from RT to be passed
    ,parameter       CORE_DATA_WIDTH             = `MEMC_DFI_DATA_WIDTH
    ,parameter       MEMC_ECC_SYNDROME_WIDTH     = `MEMC_ECC_SYNDROME_WIDTH  //it equal to DATA + 8bit 
    ,parameter       ECC_LANES                   = 2 //need overwrite
    ,parameter       DATA_ECC_BITS_PER_LANE      = 64
    ,parameter       REG_IN_EN                   = 1 
    ,parameter       ECCAP_TH_WIDTH              = 4
)(
     input            core_ddrc_core_clk 
    ,input            core_ddrc_rstn

// Internal register/signals
    ,input   [ECC_INFO_WIDTH-1:0]  rt_rd_ecc_info  // address, etc. from RT and provided to ECC wire
    ,input   [5:0]                 rd_dh_word_num  

    ,input   [ECC_LANES-1:0]       corrected_err
    ,input   [ECC_LANES-1:0]       uncorrected_err
    ,input   [ECC_LANES*DATA_ECC_BITS_PER_LANE-1:0]  data_ecc_lanes
    ,input   [ECC_LANES*7-1:0]                       ecc_corr_bit_num_lanes
    ,input   [ECC_LANES*DATA_ECC_BITS_PER_LANE-1:0]  ecc_corr_bit_mask_lanes

// REGISTERS INTERFACE
    ,input                                      reg_ddrc_ecc_clr_corr_err       // Clear corrected error interrupt
    ,input                                      reg_ddrc_ecc_clr_uncorr_err     // Clear uncorrected error interrupt
    ,input                                      reg_ddrc_ecc_clr_corr_err_cnt   // Clear correctable ECC error count
    ,input                                      reg_ddrc_ecc_clr_uncorr_err_cnt // Clear uncorrectable ECC error count
    ,output reg                                 ddrc_reg_ecc_corrected_err      // single-bit error that will be corrected, per lane
    ,output reg                                 ddrc_reg_ecc_uncorrected_err    // double-bit error detected in read data, per lane
    ,output reg  [6:0]                          ddrc_reg_ecc_corrected_bit_num  // bit number corrected by single-bit error
    ,output reg  [15:0]                         ddrc_reg_ecc_corr_err_cnt       // Count of correctable ECC errors
    ,output reg  [15:0]                         ddrc_reg_ecc_uncorr_err_cnt     // Count of uncorrectable ECC errors
    ,output reg  [MEMC_ECC_SYNDROME_WIDTH-1:0]  ddrc_reg_ecc_corr_syndromes        // data pattern that resulted in an error;
    ,output reg  [MEMC_ECC_SYNDROME_WIDTH-1:0]  ddrc_reg_ecc_uncorr_syndromes      // data pattern that resulted in an error;
    ,output reg  [MEMC_ECC_SYNDROME_WIDTH-1:0]  ddrc_reg_ecc_corr_bit_mask         // mask for the bit that is corrected
    ,output reg  [ECC_INFO_WIDTH-1:0]           ddrc_reg_ecc_corr_info
    ,output reg  [ECC_INFO_WIDTH-1:0]           ddrc_reg_ecc_uncorr_info
    ,output reg  [5:0]                          ddrc_reg_ecc_corr_word_num
    ,output reg  [5:0]                          ddrc_reg_ecc_uncorr_word_num
    ,input                                      data_out_eod
    ,output reg                                 ddrc_reg_ecc_ap_err
    ,input                                      reg_ddrc_ecc_ap_en
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in RTL coverpoint
    ,input  [2:0]                               reg_ddrc_ecc_mode    
//spyglass enable_block W240
    ,input                                      reg_ddrc_ecc_ap_err_intr_clr
    ,input  [ECCAP_TH_WIDTH-1:0]                reg_ddrc_ecc_ap_err_threshold  


);

//-----------------------------------------------------------------------------
// parameter 
//-----------------------------------------------------------------------------
parameter COL_WIDTH = $clog2(`MEMC_FREQ_RATIO);
//-----------------------------------------------------------------------------
// registers and wires
//-----------------------------------------------------------------------------


//-----------------------------------------------------------------------------
// Logic Start
//-----------------------------------------------------------------------------
//

wire   [ECC_INFO_WIDTH-1:0]  i_rt_rd_ecc_info;  // address, etc. from RT and provided to ECC wire
wire   [5:0]                 i_rd_dh_word_num;  
wire   [ECC_LANES-1:0]       i_corrected_err;
wire   [ECC_LANES-1:0]       i_uncorrected_err;
wire   [ECC_LANES*DATA_ECC_BITS_PER_LANE-1:0]  i_data_ecc_lanes;
wire   [ECC_LANES*7-1:0]                       i_ecc_corr_bit_num_lanes;
wire   [ECC_LANES*DATA_ECC_BITS_PER_LANE-1:0]  i_ecc_corr_bit_mask_lanes;
wire                         i_data_out_eod;
// Input Register to refine the timing
generate 
   if (REG_IN_EN==1) begin: REG_IN
      reg   [ECC_INFO_WIDTH-1:0]  r_rt_rd_ecc_info;  // address, etc. from RT and provided to ECC wire
      reg   [5:0]                 r_rd_dh_word_num;  
      reg   [ECC_LANES-1:0]       r_corrected_err;
      reg   [ECC_LANES-1:0]       r_uncorrected_err;
      reg   [ECC_LANES*DATA_ECC_BITS_PER_LANE-1:0]  r_data_ecc_lanes;
      reg   [ECC_LANES*7-1:0]                       r_ecc_corr_bit_num_lanes;
      reg   [ECC_LANES*DATA_ECC_BITS_PER_LANE-1:0]  r_ecc_corr_bit_mask_lanes;
      reg                         r_data_out_eod;                
       
      always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn)
      begin
         if (~core_ddrc_rstn) begin
            r_rt_rd_ecc_info             <= {ECC_INFO_WIDTH{1'b0}} ;  
            r_rd_dh_word_num             <= {6{1'b0}};  
            r_corrected_err              <= {ECC_LANES{1'b0}};
            r_uncorrected_err            <= {ECC_LANES{1'b0}};
            r_data_ecc_lanes             <= {ECC_LANES*DATA_ECC_BITS_PER_LANE{1'b0}};
            r_ecc_corr_bit_num_lanes     <= {ECC_LANES*7{1'b0}};
            r_ecc_corr_bit_mask_lanes    <= {ECC_LANES*DATA_ECC_BITS_PER_LANE{1'b0}};
            r_data_out_eod               <= 1'b0;              
         end
         else begin
            r_rt_rd_ecc_info             <= rt_rd_ecc_info;  
            r_rd_dh_word_num             <= rd_dh_word_num;  
            r_corrected_err              <= corrected_err    ; 
            r_uncorrected_err            <= uncorrected_err  ; 
            r_data_ecc_lanes             <= data_ecc_lanes   ; 
            r_ecc_corr_bit_num_lanes     <= ecc_corr_bit_num_lanes; 
            r_ecc_corr_bit_mask_lanes    <= ecc_corr_bit_mask_lanes; 
            r_data_out_eod               <= data_out_eod; 
         end
      end

      assign     i_rt_rd_ecc_info             = r_rt_rd_ecc_info;  
      assign     i_rd_dh_word_num             = r_rd_dh_word_num;  
      
      assign     i_corrected_err              = r_corrected_err    ; 
      assign     i_uncorrected_err            = r_uncorrected_err  ; 
      assign     i_data_ecc_lanes             = r_data_ecc_lanes   ; 
      assign     i_ecc_corr_bit_num_lanes     = r_ecc_corr_bit_num_lanes; 
      assign     i_ecc_corr_bit_mask_lanes    = r_ecc_corr_bit_mask_lanes; 
      assign     i_data_out_eod               = r_data_out_eod;

   end else begin : NOT_REG_IN
       
      assign     i_rt_rd_ecc_info             = rt_rd_ecc_info;  
      assign     i_rd_dh_word_num             = rd_dh_word_num;  

      assign     i_corrected_err              = corrected_err    ; 
      assign     i_uncorrected_err            = uncorrected_err  ; 
      assign     i_data_ecc_lanes             = data_ecc_lanes   ; 
      assign     i_ecc_corr_bit_num_lanes     = ecc_corr_bit_num_lanes; 
      assign     i_ecc_corr_bit_mask_lanes    = ecc_corr_bit_mask_lanes; 
      assign     i_data_out_eod               = data_out_eod;
   end
endgenerate

//----------------------------------------------------------------
// Log registers
// --------------------------------------------------------------
integer i;
wire [3:0] num_corrected_err;
reg  [4:0] num_corrected_err_wider;
wire [3:0] num_uncorrected_err;
reg  [4:0] num_uncorrected_err_wider;
reg  [6:0] sel_corr_bit_num;
reg  [MEMC_ECC_SYNDROME_WIDTH-1:0] sel_corr_bit_mask;
reg  [MEMC_ECC_SYNDROME_WIDTH-1:0] sel_corr_syndromes;
reg  [MEMC_ECC_SYNDROME_WIDTH-1:0] sel_uncorr_syndromes;

//spyglass disable_block W415a
//SMD: Signal is being assigned multiple times in same always block. 
//SJ: Using initialization in process to minimize code - sets the default for any hanging branches, avoids latches
always @ (*)begin
   num_uncorrected_err_wider = 4'b0000;
   for(i=0; i<ECC_LANES; i=i+1)
      num_uncorrected_err_wider = num_uncorrected_err_wider[3:0]+i_uncorrected_err[i];
end
assign num_uncorrected_err = num_uncorrected_err_wider[3:0];

always @ (*)begin
   num_corrected_err_wider = 4'b0000;
   for(i=0; i<ECC_LANES; i=i+1)
      num_corrected_err_wider = num_corrected_err_wider[3:0]+i_corrected_err[i];
end
assign num_corrected_err = num_corrected_err_wider[3:0];

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * 7)' found in module 'rd_ie_log_reg'
//SJ: This coding style is acceptable and there is no plan to change it.

always @ (*)begin
   sel_corr_syndromes = {MEMC_ECC_SYNDROME_WIDTH{1'b0}};
   sel_corr_bit_num   = {7{1'b0}};
   sel_corr_bit_mask  = {MEMC_ECC_SYNDROME_WIDTH{1'b0}};
   for(i=ECC_LANES-1; i>=0; i=i-1)
      if(i_corrected_err[i])begin
         sel_corr_syndromes = i_data_ecc_lanes[i*MEMC_ECC_SYNDROME_WIDTH+:MEMC_ECC_SYNDROME_WIDTH];
         sel_corr_bit_num   = i_ecc_corr_bit_num_lanes[i*7+:7];
         sel_corr_bit_mask  = sel_corr_bit_mask | i_ecc_corr_bit_mask_lanes[i*MEMC_ECC_SYNDROME_WIDTH+:MEMC_ECC_SYNDROME_WIDTH];
      end
end

always @ (*)begin
   sel_uncorr_syndromes = {MEMC_ECC_SYNDROME_WIDTH{1'b0}};
   for(i=ECC_LANES-1; i>=0; i=i-1)
      if(i_uncorrected_err[i])
         sel_uncorr_syndromes = i_data_ecc_lanes[i*MEMC_ECC_SYNDROME_WIDTH+:MEMC_ECC_SYNDROME_WIDTH];
end
//spyglass enable_block SelfDeterminedExpr-ML
//spyglass enable_block W415a

// ECCSTAT.ecc_corrected_err
// ECCSTAT.ecc_uncorrected_err
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn)
begin
   if (~core_ddrc_rstn) begin
      ddrc_reg_ecc_corrected_err          <= 1'b0;
      ddrc_reg_ecc_uncorrected_err        <= 1'b0;
   end
   else begin
      if (reg_ddrc_ecc_clr_corr_err) begin
         ddrc_reg_ecc_corrected_err       <= 1'b0;
      end else if ( ~ddrc_reg_ecc_corrected_err & |i_corrected_err) begin
         ddrc_reg_ecc_corrected_err       <= 1'b1;
      end

      if (reg_ddrc_ecc_clr_uncorr_err) begin
         ddrc_reg_ecc_uncorrected_err     <= 1'b0;
      end else if ( ~ddrc_reg_ecc_uncorrected_err & |i_uncorrected_err) begin
         ddrc_reg_ecc_uncorrected_err     <= 1'b1;
      end
   end
end


//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((16'hFFFF - ddrc_reg_ecc_corr_err_cnt)>={{ 13{ 1'b0} }  ,num_corrected_err})' found in module 'rd_ie_log_reg'
//SJ: No suitable (better) re-coding found
//spyglass disable_block W164a
//SMD: LHS: 'ddrc_reg_ecc_corr_err_cnt' width 16 is less than RHS: '(ddrc_reg_ecc_corr_err_cnt + {{ 13{ 1'b0} }  ,num_corrected_err})' width 17 in assignment
//SMD: LHS: 'ddrc_reg_ecc_uncorr_err_cnt' width 16 is less than RHS: '(ddrc_reg_ecc_uncorr_err_cnt + {{ 13{ 1'b0} }  ,num_uncorrected_err})' width 17 in assignment
//SJ: Overflow cannot occur in these conditions. Protected by 'if' conditions.

// ECCCCNT
// ECCUCCNT
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn)
begin
   if (~core_ddrc_rstn) begin
      ddrc_reg_ecc_corr_err_cnt              <= 16'h0000;
      ddrc_reg_ecc_uncorr_err_cnt            <= 16'h0000;
   end
   else begin
      if (reg_ddrc_ecc_clr_corr_err_cnt) begin
         ddrc_reg_ecc_corr_err_cnt           <= 16'h0000;
      end else if (|i_corrected_err)begin
         if( (16'hFFFF - ddrc_reg_ecc_corr_err_cnt) >= { {13{1'b0}}, num_corrected_err} )begin
            ddrc_reg_ecc_corr_err_cnt        <= ddrc_reg_ecc_corr_err_cnt + { {13{1'b0}}, num_corrected_err};
         end else begin
            ddrc_reg_ecc_corr_err_cnt        <= 16'hFFFF;
         end
      end
      
      if (reg_ddrc_ecc_clr_uncorr_err_cnt) begin
         ddrc_reg_ecc_uncorr_err_cnt         <= 16'h0000;
      end else if (|i_uncorrected_err) begin
         if(16'hFFFF - ddrc_reg_ecc_uncorr_err_cnt >= { {13{1'b0}}, num_uncorrected_err} )begin
            ddrc_reg_ecc_uncorr_err_cnt      <= ddrc_reg_ecc_uncorr_err_cnt + { {13{1'b0}}, num_uncorrected_err};
         end else begin
            ddrc_reg_ecc_uncorr_err_cnt      <= 16'hFFFF;
         end
      end
   end
end
//spyglass enable_block W164a
//spyglass enable_block SelfDeterminedExpr-ML

// ECCCBITMASK
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn)
begin
   if (~core_ddrc_rstn) begin
      ddrc_reg_ecc_corr_bit_mask                <= {MEMC_ECC_SYNDROME_WIDTH{1'b0}};
   end
   else begin
      if (reg_ddrc_ecc_clr_corr_err) begin
         ddrc_reg_ecc_corr_bit_mask             <= {MEMC_ECC_SYNDROME_WIDTH{1'b0}};
      end else begin
         ddrc_reg_ecc_corr_bit_mask             <= ddrc_reg_ecc_corr_bit_mask | sel_corr_bit_mask;
      end
   end
end


// generate column address according to word_num(dfi beats number)
// Note: for inline ECC read command always are aligned
wire [COL_WIDTH:0] lsb_col_corr;
wire [COL_WIDTH:0] lsb_col_uncorr;
// if  8bits: 1 Dec; lsb_col= 3'b000
// if 16bits: 2 dec; 
//       dec0 error -> lsb_col= 3'b000
//       dec1 error -> lsb_col= 3'b100
// if 32bits: 4 dec;
//       dec0 error -> lsb_col= 3'b000
//       dec1 error -> lsb_col= 3'b010
//       dec2 error -> lsb_col= 3'b100
//       dec3 error -> lsb_col= 3'b110
// if 64bits: 4 dec;8
//       dec0 error -> lsb_col= 3'b000
//       dec1 error -> lsb_col= 3'b001
//       dec2 error -> lsb_col= 3'b010
//       dec3 error -> lsb_col= 3'b011
//       dec4 error -> lsb_col= 3'b100
//       dec5 error -> lsb_col= 3'b101
//       dec6 error -> lsb_col= 3'b110
//       dec7 error -> lsb_col= 3'b111
generate
   if(ECC_LANES==1) begin: ECC_LANES_1_FR4
      assign lsb_col_corr   = {{$bits(lsb_col_corr)}{1'b0}};
      assign lsb_col_uncorr = {{$bits(lsb_col_uncorr)}{1'b0}};
   end else if(ECC_LANES==2) begin: ECC_LANES_2_FR4
      assign lsb_col_corr   = {~i_corrected_err[0],2'b00};
      assign lsb_col_uncorr = {~i_uncorrected_err[0],2'b00};
   end else if(ECC_LANES==4) begin: ECC_LANES_4_FR4
      assign lsb_col_corr   = i_corrected_err[0]   ? 3'b000 : i_corrected_err[1]   ? 3'b010 : i_corrected_err[2]   ? 3'b100 : 3'b110;
      assign lsb_col_uncorr = i_uncorrected_err[0] ? 3'b000 : i_uncorrected_err[1] ? 3'b010 : i_uncorrected_err[2] ? 3'b100 : 3'b110;
   end else begin : ECC_LANES_8_FR4
      assign lsb_col_corr   = i_corrected_err[0] ? 3'b000 : i_corrected_err[1] ? 3'b001 : i_corrected_err[2] ? 3'b010 : 
                              i_corrected_err[3] ? 3'b011 : i_corrected_err[4] ? 3'b100 : i_corrected_err[5] ? 3'b101 :
                              i_corrected_err[6] ? 3'b110 : 3'b111;
      assign lsb_col_uncorr = i_uncorrected_err[0] ? 3'b000 : i_uncorrected_err[1] ? 3'b001 : i_uncorrected_err[2] ? 3'b010 : 
                              i_uncorrected_err[3] ? 3'b011 : i_uncorrected_err[4] ? 3'b100 : i_uncorrected_err[5] ? 3'b101 :
                              i_uncorrected_err[6] ? 3'b110 : 3'b111;
   end
endgenerate

// register (un)corrected_error info and word_num for generate error address
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn) begin
     ddrc_reg_ecc_corr_info            <= {ECC_INFO_WIDTH{1'b0}};
     ddrc_reg_ecc_uncorr_info          <= {ECC_INFO_WIDTH{1'b0}};
     ddrc_reg_ecc_corr_word_num        <= 6'b0;
     ddrc_reg_ecc_uncorr_word_num      <= 6'b0;
     ddrc_reg_ecc_corr_syndromes       <= {MEMC_ECC_SYNDROME_WIDTH{1'b0}};
     ddrc_reg_ecc_uncorr_syndromes     <= {MEMC_ECC_SYNDROME_WIDTH{1'b0}};
     ddrc_reg_ecc_corrected_bit_num    <= {7{1'b0}};
  end
  else begin
     if (reg_ddrc_ecc_clr_corr_err) begin
        ddrc_reg_ecc_corr_info         <= {ECC_INFO_WIDTH{1'b0}};
        ddrc_reg_ecc_corr_word_num     <= 6'b0;
        ddrc_reg_ecc_corr_syndromes    <= {MEMC_ECC_SYNDROME_WIDTH{1'b0}};
        ddrc_reg_ecc_corrected_bit_num <= {7{1'b0}};
     end else if ( ~ddrc_reg_ecc_corrected_err & |i_corrected_err) begin
        ddrc_reg_ecc_corr_info         <= i_rt_rd_ecc_info;
//spyglass disable_block W164b
//SMD: LHS: 'ddrc_reg_ecc_corr_word_num' width 6 is greater than RHS: '{i_rd_dh_word_num[5:4]  ,lsb_col_corr}' width 5 in assignment
//SJ: Waived for Backword compatibility
        ddrc_reg_ecc_corr_word_num     <= {i_rd_dh_word_num[5:`MEMC_FREQ_RATIO], lsb_col_corr};
//spyglass enable_block W164b
        ddrc_reg_ecc_corr_syndromes    <= sel_corr_syndromes;
        ddrc_reg_ecc_corrected_bit_num <= sel_corr_bit_num;
     end

     if (reg_ddrc_ecc_clr_uncorr_err) begin
        ddrc_reg_ecc_uncorr_info       <= {ECC_INFO_WIDTH{1'b0}};
        ddrc_reg_ecc_uncorr_word_num   <= 6'b0;
        ddrc_reg_ecc_uncorr_syndromes  <= {MEMC_ECC_SYNDROME_WIDTH{1'b0}};
     end else if ( ~ddrc_reg_ecc_uncorrected_err& |i_uncorrected_err) begin
        ddrc_reg_ecc_uncorr_info       <= i_rt_rd_ecc_info;
//spyglass disable_block W164b
//SMD: LHS: 'ddrc_reg_ecc_uncorr_word_num' width 6 is greater than RHS: '{i_rd_dh_word_num[5:4]  ,lsb_col_uncorr}' width 5 in assignment
//SJ: Waived for Backword compatibility
        ddrc_reg_ecc_uncorr_word_num   <= {i_rd_dh_word_num[5:`MEMC_FREQ_RATIO], lsb_col_uncorr};
//spyglass enable_block W164b
        ddrc_reg_ecc_uncorr_syndromes  <= sel_uncorr_syndromes;
     end
  end

//-----------------------
// ECCAP register
//-----------------------
reg [ECCAP_TH_WIDTH+1-1:0] ecc_ap_err_counter;
reg                        i_data_out_eod_1d;  

// Total number of error on this cycle
wire [4:0] num_any_err;
assign num_any_err = {1'b0,num_corrected_err} + {1'b0,num_uncorrected_err};

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
     ecc_ap_err_counter  <= {ECCAP_TH_WIDTH+1{1'b0}};
     ddrc_reg_ecc_ap_err <= 1'b0;
     i_data_out_eod_1d   <= 1'b0;
  end
  else begin
     i_data_out_eod_1d     <= i_data_out_eod;

     if (ddrc_reg_ecc_ap_err || (~reg_ddrc_ecc_ap_en)) begin // Interrupt asserted or feature disabled
         ecc_ap_err_counter <= {ECCAP_TH_WIDTH+1{1'b0}};
     end
     else if (i_data_out_eod_1d) begin // Burst ended
         ecc_ap_err_counter <= num_any_err[ECCAP_TH_WIDTH:0];
     end
     else begin
         //spyglass disable_block W164a
         //SMD: LHS: 'ecc_ap_err_counter' width 4 is less than RHS: '(ecc_ap_err_counter + num_any_err[ECCAP_TH_WIDTH:0] )' width 5 in assignment
         //SJ: Overflow should not occur (there is an existing RTL assertion at the bottom of this file checking this assumption)
         ecc_ap_err_counter <=  ecc_ap_err_counter + num_any_err[ECCAP_TH_WIDTH:0]; // This must not be overflow
         //spyglass enable_block W164a
     end

     if (reg_ddrc_ecc_ap_err_intr_clr) begin
         ddrc_reg_ecc_ap_err <= 1'b0;
     end
     else if (ecc_ap_err_counter > {1'b0,reg_ddrc_ecc_ap_err_threshold}) begin
         ddrc_reg_ecc_ap_err <= 1'b1;
     end
   
  end

end

`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------

`ifdef SNPS_ASSERT_ON


      // Counters for coverpoint
      
      reg [ECCAP_TH_WIDTH+1-1:0] corr_cnt4cp;
      reg [ECCAP_TH_WIDTH+1-1:0] uncorr_cnt4cp;

      always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
        if (~core_ddrc_rstn) begin
           corr_cnt4cp   <= {ECCAP_TH_WIDTH+1{1'b0}};
           uncorr_cnt4cp <= {ECCAP_TH_WIDTH+1{1'b0}};
        end
        else begin
           if (ddrc_reg_ecc_ap_err) begin // Interrupt asserted
               corr_cnt4cp   <= {ECCAP_TH_WIDTH+1{1'b0}};
               uncorr_cnt4cp <= {ECCAP_TH_WIDTH+1{1'b0}};
           end
           else if (i_data_out_eod_1d) begin // Burst ended
               corr_cnt4cp   <= num_corrected_err;
               uncorr_cnt4cp <= num_uncorrected_err[3:0];
           end
           else begin
               corr_cnt4cp   <=  corr_cnt4cp   + num_corrected_err;
               uncorr_cnt4cp <=  uncorr_cnt4cp + num_uncorrected_err[3:0];
           end
         
        end
      
      end

      // Assertions

      property p_eccap_corr_uncorr_uniq;
        @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
          (num_corrected_err+num_uncorrected_err<=ECC_LANES) ;
      endproperty

      a_eccap_corr_uncorr_uniq : assert property (p_eccap_corr_uncorr_uniq)
      else $error("%m @ %t Error : num_corrected_err + num_uncorrected_err must be less than or equal to ECC_LANES", $time);

      property p_ecc_ap_err_counter_no_overflow;
        @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
          (ddrc_reg_ecc_ap_err==0 && i_data_out_eod_1d==0) |-> (({32'd0,ecc_ap_err_counter} + {32'd0,num_any_err[ECCAP_TH_WIDTH:0]}) <= {32'd0,{ECCAP_TH_WIDTH+1{1'b1}}});
      endproperty

      a_ecc_ap_err_counter_no_overflow : assert property (p_ecc_ap_err_counter_no_overflow)
      else $error("%m @ %t Error : a_ecc_ap_err_counter_no_overflow failed", $time);

      property p_ecc_ap_err_never_assert_when_disabled;
        @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
          (reg_ddrc_ecc_ap_en==0) |-> (ddrc_reg_ecc_ap_err==0);
      endproperty

      a_ecc_ap_err_never_assert_when_disabled : assert property (p_ecc_ap_err_never_assert_when_disabled)
      else $error("%m @ %t Error : ddrc_reg_ecc_ap_err is asserted with reg_ddrc_ecc_ap_en==0", $time);

      generate
        if (ECCAP_TH_WIDTH<4) begin : ECCAP_TH_WIDTH_LT4
          property p_eccap_num_any_err_no_overflow;
            @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
            (num_any_err[4:ECCAP_TH_WIDTH+1] == 0) ;
          endproperty

          a_eccap_num_any_err_no_overflow : assert property (p_eccap_num_any_err_no_overflow)
          else $error("%m @ %t Error : a_eccap_num_any_err_no_overflow is failed", $time);
        end

      endgenerate

      // Coverpoints

      covergroup cg_eccap @(posedge core_ddrc_core_clk);
          // observe all value of ecc_ap_err_counter
          cp_ecc_ap_err_counter : coverpoint (ecc_ap_err_counter)
             iff (core_ddrc_rstn & reg_ddrc_ecc_mode>0 & reg_ddrc_ecc_ap_en) {
                 bins values[]   = {[0:(1<<ECCAP_TH_WIDTH)-2]};
                 bins max_value  = {(1<<ECCAP_TH_WIDTH)-1};
          }

          // observe all value of uncorr_cnt4cp     
          cp_uncorr_cnt4cp : coverpoint (uncorr_cnt4cp)
             iff (core_ddrc_rstn & reg_ddrc_ecc_mode>0 & reg_ddrc_ecc_ap_en) {
                 bins values[]   = {[0:(1<<ECCAP_TH_WIDTH)-2]};
                 bins max_value  = {(1<<ECCAP_TH_WIDTH)-1};
          }

          // observe all value of uncorr_cnt4cp
          cp_corr_cnt4cp : coverpoint (corr_cnt4cp)
             iff (core_ddrc_rstn & reg_ddrc_ecc_mode>0 & reg_ddrc_ecc_ap_en) {
                 bins values[]   = {[0:(1<<ECCAP_TH_WIDTH)-2]};
                 bins max_value  = {(1<<ECCAP_TH_WIDTH)-1};
          }

          // observe all value of ecc_ap_err_threshold
          cp_ecc_ap_err_threshold : coverpoint (reg_ddrc_ecc_ap_err_threshold)
             iff (core_ddrc_rstn & reg_ddrc_ecc_mode>0 & reg_ddrc_ecc_ap_en) {
                 bins values[]   = {[0:(1<<ECCAP_TH_WIDTH)-2]};
                 bins max_value  = {(1<<ECCAP_TH_WIDTH)-1};
          }
      endgroup
      
      cg_eccap cg_eccap_inst = new;



`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS


endmodule
