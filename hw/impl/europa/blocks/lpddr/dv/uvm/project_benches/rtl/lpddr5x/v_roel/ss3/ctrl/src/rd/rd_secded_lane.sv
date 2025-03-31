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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/rd/rd_secded_lane.sv#2 $
// -------------------------------------------------------------------------
// Description:
//
// Data Phase 2 (D2) unit.  This block is responsible for handling SEC/DED
// (single-error correction/double-error detection) error checking and
// correcting on read response data for 1 64-bit lane.
// Date:   January 28, 2004
//
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
module rd_secded_lane 
(
   rdata, 
   reg_ddrc_med_ecc_en,
   corrected_err, uncorrected_err,
   corrected_data, err_bit_num
);

input [71:0] rdata;      // [71:64] check bits
                         // [63: 0] data bits

input reg_ddrc_med_ecc_en;  // MED support control

output corrected_err;    // An error was detected in read
                         //  data and will be corrected
output uncorrected_err;  // An uncorrectable error was
                         //  detected in read data
output [63:0] corrected_data; // read data in from D1, corrected for
                              //  ECC errors, with check bits removed
output [6:0]  err_bit_num;    // bit number that an ECC error was
                              //  detected on.  valid when corrected_err=1

wire  [71:0]   d; 

wire odd1_parity;    // parity over every other bit,
                     //  should be '0'
wire odd2_parity;    // parity over every other pair of bits,
                     //  should be '0'
wire odd4_parity;    // parity over every other quartet of
                     //  bits, should be '0'
wire odd8_parity;    // parity over every other octet of
                     //  bits, should be '0'
wire odd16_parity;   // parity over every other set of 16
                     //  bits, should be '0'
wire odd32_parity;   // parity over every other set of 32
                     //  bits, should be '0'
wire odd64_parity;   // parity over every other set of 64
                     //  bits (=last 8 bits), should be '0'
wire final_parity;   // parity over all bits.  if other
                     //  checks fail and this passes, at
                     //  least 2 errors have occurred
wire    parity_err;        // 1 or more parity errors detected 
wire [6:0] err_bit_num;    // bit number that is in error

reg [71:0] corrected_rdata;  // corrected data, with check bits still
                             //  in place
integer  i;                  // bit index


// insert the check bits at every power-of-2 bit position and bit 0
// note: all ecc bits [71:64] are inverted to match the inversion that happens in the ECC encoder module (mr_secded_lane.v)
// the encoder does this to enable the writing of same pattern of 'hAA on data and ECC bytes going to the DRAM through PHY BIST operation
// this is needed to load the entire DRAM with the same pattern after DRAM initialization, before issuing any traffic
assign d= { 
    rdata[63:57],  ~rdata[71],
    rdata[56:26],  ~rdata[70],
    rdata[25:11],  ~rdata[69],
    rdata[10: 4],  ~rdata[68],
    rdata[ 3: 1],  ~rdata[67],
    rdata[    0],  ~rdata[66],
    ~rdata[65],    ~rdata[64] };

assign odd1_parity = d[ 1] ^ d[ 3] ^ d[ 5] ^ d[ 7] ^
        d[ 9] ^ d[11] ^ d[13] ^ d[15] ^
        d[17] ^ d[19] ^ d[21] ^ d[23] ^
        d[25] ^ d[27] ^ d[29] ^ d[31] ^
        d[33] ^ d[35] ^ d[37] ^ d[39] ^
        d[41] ^ d[43] ^ d[45] ^ d[47] ^
        d[49] ^ d[51] ^ d[53] ^ d[55] ^
        d[57] ^ d[59] ^ d[61] ^ d[63] ^
        d[65] ^ d[67] ^ d[69] ^ d[71] 
        ;

assign odd2_parity = d[ 2] ^ d[ 3] ^ d[ 6] ^ d[ 7] ^
        d[10] ^ d[11] ^ d[14] ^ d[15] ^
        d[18] ^ d[19] ^ d[22] ^ d[23] ^
        d[26] ^ d[27] ^ d[30] ^ d[31] ^
        d[34] ^ d[35] ^ d[38] ^ d[39] ^
        d[42] ^ d[43] ^ d[46] ^ d[47] ^
        d[50] ^ d[51] ^ d[54] ^ d[55] ^
        d[58] ^ d[59] ^ d[62] ^ d[63] ^
        d[66] ^ d[67] ^ d[70] ^ d[71] 
        ;

assign odd4_parity = d[ 4] ^ d[ 5] ^ d[ 6] ^ d[ 7] ^
        d[12] ^ d[13] ^ d[14] ^ d[15] ^
        d[20] ^ d[21] ^ d[22] ^ d[23] ^
        d[28] ^ d[29] ^ d[30] ^ d[31] ^
        d[36] ^ d[37] ^ d[38] ^ d[39] ^
        d[44] ^ d[45] ^ d[46] ^ d[47] ^
        d[52] ^ d[53] ^ d[54] ^ d[55] ^
        d[60] ^ d[61] ^ d[62] ^ d[63] ^
        d[68] ^ d[69] ^ d[70] ^ d[71] 
        ;

assign odd8_parity = d[ 8] ^ d[ 9] ^ d[10] ^ d[11] ^
        d[12] ^ d[13] ^ d[14] ^ d[15] ^
        d[24] ^ d[25] ^ d[26] ^ d[27] ^
        d[28] ^ d[29] ^ d[30] ^ d[31] ^
        d[40] ^ d[41] ^ d[42] ^ d[43] ^
        d[44] ^ d[45] ^ d[46] ^ d[47] ^
        d[56] ^ d[57] ^ d[58] ^ d[59] ^
        d[60] ^ d[61] ^ d[62] ^ d[63] 
        ;

assign odd16_parity = d[16] ^ d[17] ^ d[18] ^ d[19] ^
        d[20] ^ d[21] ^ d[22] ^ d[23] ^
        d[24] ^ d[25] ^ d[26] ^ d[27] ^
        d[28] ^ d[29] ^ d[30] ^ d[31] ^
        d[48] ^ d[49] ^ d[50] ^ d[51] ^
        d[52] ^ d[53] ^ d[54] ^ d[55] ^
        d[56] ^ d[57] ^ d[58] ^ d[59] ^
        d[60] ^ d[61] ^ d[62] ^ d[63] 
        ;

assign odd32_parity = d[32] ^ d[33] ^ d[34] ^ d[35] ^
        d[36] ^ d[37] ^ d[38] ^ d[39] ^
        d[40] ^ d[41] ^ d[42] ^ d[43] ^
        d[44] ^ d[45] ^ d[46] ^ d[47] ^
        d[48] ^ d[49] ^ d[50] ^ d[51] ^
        d[52] ^ d[53] ^ d[54] ^ d[55] ^
        d[56] ^ d[57] ^ d[58] ^ d[59] ^
        d[60] ^ d[61] ^ d[62] ^ d[63] 
        ;

assign odd64_parity = d[64] ^ d[65] ^ d[66] ^ d[67] ^
        d[68] ^ d[69] ^ d[70] ^ d[71] 
        ;

assign final_parity = d[ 0] ^ d[ 1] ^ d[ 2] ^ d[ 3] ^
        d[ 4] ^ d[ 5] ^ d[ 6] ^ d[ 7] ^
        d[ 8] ^ d[ 9] ^ d[10] ^ d[11] ^
        d[12] ^ d[13] ^ d[14] ^ d[15] ^
        d[16] ^ d[17] ^ d[18] ^ d[19] ^
        d[20] ^ d[21] ^ d[22] ^ d[23] ^
        d[24] ^ d[25] ^ d[26] ^ d[27] ^
        d[28] ^ d[29] ^ d[30] ^ d[31] ^
        d[32] ^ d[33] ^ d[34] ^ d[35] ^
        d[36] ^ d[37] ^ d[38] ^ d[39] ^
        d[40] ^ d[41] ^ d[42] ^ d[43] ^
        d[44] ^ d[45] ^ d[46] ^ d[47] ^
        d[48] ^ d[49] ^ d[50] ^ d[51] ^
        d[52] ^ d[53] ^ d[54] ^ d[55] ^
        d[56] ^ d[57] ^ d[58] ^ d[59] ^
        d[60] ^ d[61] ^ d[62] ^ d[63] ^
        d[64] ^ d[65] ^ d[66] ^ d[67] ^
        d[68] ^ d[69] ^ d[70] ^ d[71] 
        ;

// OR all parity checks together to get the parity error result
assign parity_err = odd1_parity  | odd2_parity  |
        odd4_parity  | odd8_parity  |
        odd16_parity | odd32_parity |
        odd64_parity | final_parity  ;

// if there is a parity error and final_parity is wrong, that indicates
//  that a single-bit error has occurred.  if there is a parity error and
//  final_parity is not set, then that indicates that there must be a
//  double-bit error.
assign corrected_err   = parity_err &  final_parity & ~reg_ddrc_med_ecc_en;
assign uncorrected_err = parity_err & (~final_parity | reg_ddrc_med_ecc_en );
/*
// the parity error indicators will tell us which bit is in error.
//  just add the weighted power-of-2 indicators together, as shown below,
//  to get the number of the bit that is error.
assign err_bit_num  = {6'b000000,odd1_parity}         |
        {5'b00000,(odd2_parity  << 1)} |
        {4'b0000,(odd4_parity  << 2)} |
        {3'b000,(odd8_parity  << 3)} |
        {2'b00,(odd16_parity << 4)} |
        {1'b0,(odd32_parity << 5)} |
        (odd64_parity << 6)  ;
*/

// Fixing LINT issue with the above logic. bit-width-mismatch

// the parity error indicators will tell us which bit is in error.
//  just add the weighted power-of-2 indicators together, as shown below,
//  to get the number of the bit that is error.

//spyglass disable_block W164a
//SMD: LHS: 'odd64_parity_tmp' width 7 is less than RHS: '({6'h00 ,odd64_parity} << 6)' width 13 in assignment
//SJ: Overflow not possible
wire [1:0] odd2_parity_tmp;
assign odd2_parity_tmp  = {1'h0, odd2_parity}       << 1;
wire [2:0] odd4_parity_tmp;
assign odd4_parity_tmp  = {2'h0, odd4_parity}       << 2;
wire [3:0] odd8_parity_tmp;
assign odd8_parity_tmp  = {3'h0, odd8_parity}       << 3;
wire [4:0] odd16_parity_tmp;
assign odd16_parity_tmp = {4'h0, odd16_parity}      << 4;
wire [5:0] odd32_parity_tmp;
assign odd32_parity_tmp = {5'h00, odd32_parity}     << 5;
wire [6:0] odd64_parity_tmp;
assign odd64_parity_tmp = {6'h00, odd64_parity}     << 6;
//spyglass enable_block W164a

assign err_bit_num = {6'b000000,odd1_parity}    |
        {5'b00000,odd2_parity_tmp} |
        {4'b0000,odd4_parity_tmp}  |
        {3'b000,odd8_parity_tmp}   |
        {2'b00,odd16_parity_tmp}   |
        {1'b0,odd32_parity_tmp}    |
        (odd64_parity_tmp);

//spyglass disable_block W216
//SMD: Inappropriate range select for int_part_sel variable: "i[6:0] "
//SJ: All occurences of W216 errors have been previously waived in Leda, as they were considered safe and because no suitable re-coding was found (see bug2455)
// correct errors, if necessary
always @ (*) begin
  for (i=0; i<72; i=i+1) begin
    if ((err_bit_num == i[6:0]) && (final_parity == 1'b1) && ~reg_ddrc_med_ecc_en)
      corrected_rdata[i] = ~d[i];
    else
      corrected_rdata[i] =  d[i];
  end // for: looping thru data bits
end // always
//spyglass enable_block W216

// every power-of-2 bit is a check bit; remove these
assign corrected_data = {corrected_rdata[71:65], //64
                corrected_rdata[63:33], //32
                corrected_rdata[31:17], //16
                corrected_rdata[15: 9], //8
                corrected_rdata[ 7: 5], //4
                corrected_rdata[    3] };


endmodule  // rd_secded_lane: data phase 2 sub-unit, SEC/DED ECC for 1 64-bit lane
