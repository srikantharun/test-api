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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/mr/mr_secded_lane.sv#2 $
// -------------------------------------------------------------------------
// Description:
//
// Memory Read Engine sub-unit for providing single-error corrections and
//  double-error detection error-correcting codes.  The input a 64-bit data
//  vector; the output is a 72-bit vector of the data with the check bits
//  interspersed at every power-of-2 bit position.

`include "DWC_ddrctl_all_defs.svh"
module mr_secded_lane (  
    input  [63:0]  lane_in          // data into this SEC/DED ECC encoding
   ,output [7:0]   ecc_parity       // parity 
   ,output [71:0]  secded_lane_out  // data with SEC/DED encoding check
                                    //  bits in upper 8 bits
    );

//--------------------------------- WIRES --------------------------------------

wire    bit0, bit1, bit2, bit4, bit8, bit16, bit32, bit64;
wire  [71:0]   d;
//----------------------- COMBINATORIAL ASSIGNMENTS ----------------------------

// put a place-holding 0 at every power-of-2 bit position
assign d= { 
    lane_in[63:57], 1'b0,
    lane_in[56:26], 1'b0,
    lane_in[25:11], 1'b0,
    lane_in[10: 4], 1'b0,
    lane_in[ 3: 1], 1'b0,
    lane_in[    0], 1'b0,
    1'b0,    1'b0 };

// XOR all of the odd bits
assign bit1  = d[3]   ^ d[5]   ^ d[7]   ^ d[9]   ^ d[11]  ^ d[13]  ^ d[15]  ^
               d[17]  ^ d[19]  ^ d[21]  ^ d[23]  ^ d[25]  ^ d[27]  ^ d[29]  ^
               d[31]  ^ d[33]  ^ d[35]  ^ d[37]  ^ d[39]  ^ d[41]  ^ d[43]  ^
               d[45]  ^ d[47]  ^ d[49]  ^ d[51]  ^ d[53]  ^ d[55]  ^ d[57]  ^
               d[59]  ^ d[61]  ^ d[63]  ^ d[65]  ^ d[67]  ^ d[69]  ^ d[71]   
               ;

// XOR every odd pair of bits
assign bit2=   d[3]   ^ d[6]   ^ d[7]   ^ d[10]  ^ d[11]  ^ d[14]  ^ d[15]  ^
      d[18]  ^ d[19]  ^ d[22]  ^ d[23]  ^ d[26]  ^ d[27]  ^ d[30]  ^ d[31]  ^
      d[34]  ^ d[35]  ^ d[38]  ^ d[39]  ^ d[42]  ^ d[43]  ^ d[46]  ^ d[47]  ^
      d[50]  ^ d[51]  ^ d[54]  ^ d[55]  ^ d[58]  ^ d[59]  ^ d[62]  ^ d[63]  ^
      d[66]  ^ d[67]  ^ d[70]  ^ d[71]  
      ;

// XOR every odd quartet of bits
assign bit4=    d[5]  ^ d[6]  ^ d[7]  ^ d[12]  ^ d[13]  ^ d[14]  ^ d[15]  ^
    d[20]  ^ d[21]  ^ d[22]  ^ d[23]  ^ d[28]  ^ d[29]  ^ d[30]  ^ d[31]  ^
    d[36]  ^ d[37]  ^ d[38]  ^ d[39]  ^ d[44]  ^ d[45]  ^ d[46]  ^ d[47]  ^
    d[52]  ^ d[53]  ^ d[54]  ^ d[55]  ^ d[60]  ^ d[61]  ^ d[62]  ^ d[63]  ^
    d[68]  ^ d[69]  ^ d[70]  ^ d[71]  
    ;

// XOR every odd octet of bits
assign bit8=    d[9]  ^ d[10]  ^ d[11]  ^ d[12]  ^ d[13]  ^ d[14]  ^ d[15]  ^
      d[24]  ^ d[25]  ^ d[26]  ^ d[27]  ^ d[28]  ^ d[29]  ^ d[30]  ^ d[31]  ^
      d[40]  ^ d[41]  ^ d[42]  ^ d[43]  ^ d[44]  ^ d[45]  ^ d[46]  ^ d[47]  ^
      d[56]  ^ d[57]  ^ d[58]  ^ d[59]  ^ d[60]  ^ d[61]  ^ d[62]  ^ d[63]  
      ;

// XOR the odd sets of 16 bits
assign bit16=    d[17]  ^ d[18]  ^ d[19]  ^ d[20]  ^ d[21]  ^ d[22]  ^ d[23]  ^
        d[24]  ^ d[25]  ^ d[26]  ^ d[27]  ^ d[28]  ^ d[29]  ^ d[30]  ^ d[31]  ^
        d[48]  ^ d[49]  ^ d[50]  ^ d[51]  ^ d[52]  ^ d[53]  ^ d[54]  ^ d[55]  ^
        d[56]  ^ d[57]  ^ d[58]  ^ d[59]  ^ d[60]  ^ d[61]  ^ d[62]  ^ d[63]  
        ;

// XOR the odd sets of 32 bits
assign bit32=    d[33]  ^ d[34]  ^ d[35]  ^ d[36]  ^ d[37]  ^ d[38]  ^ d[39]  ^
        d[40]  ^ d[41]  ^ d[42]  ^ d[43]  ^ d[44]  ^ d[45]  ^ d[46]  ^ d[47]  ^
        d[48]  ^ d[49]  ^ d[50]  ^ d[51]  ^ d[52]  ^ d[53]  ^ d[54]  ^ d[55]  ^
        d[56]  ^ d[57]  ^ d[58]  ^ d[59]  ^ d[60]  ^ d[61]  ^ d[62]  ^ d[63]  
        ;

// XOR the odd sets of 64 bits
assign bit64=    d[65]  ^ d[66]  ^ d[67]  ^ d[68]  ^ d[69]  ^ d[70]  ^ d[71]  
        ;
    
// XOR everything except bit 0
assign bit0=     bit1  ^ bit2  ^ d[3]  ^ bit4  ^ d[5]  ^ d[6]  ^ d[7]  ^
     bit8  ^  d[9]  ^ d[10]  ^ d[11]  ^ d[12]  ^ d[13]  ^ d[14]  ^ d[15]  ^
    bit16  ^ d[17]  ^ d[18]  ^ d[19]  ^ d[20]  ^ d[21]  ^ d[22]  ^ d[23]  ^
    d[24]  ^ d[25]  ^ d[26]  ^ d[27]  ^ d[28]  ^ d[29]  ^ d[30]  ^ d[31]  ^
    bit32  ^ d[33]  ^ d[34]  ^ d[35]  ^ d[36]  ^ d[37]  ^ d[38]  ^ d[39]  ^
    d[40]  ^ d[41]  ^ d[42]  ^ d[43]  ^ d[44]  ^ d[45]  ^ d[46]  ^ d[47]  ^
    d[48]  ^ d[49]  ^ d[50]  ^ d[51]  ^ d[52]  ^ d[53]  ^ d[54]  ^ d[55]  ^
    d[56]  ^ d[57]  ^ d[58]  ^ d[59]  ^ d[60]  ^ d[61]  ^ d[62]  ^ d[63]  ^
    bit64  ^ d[65]  ^ d[66]  ^ d[67]  ^ d[68]  ^ d[69]  ^ d[70]  ^ d[71]   
    ;

// Output is 8 check bits and 64 data bits
//
//-----------------------------------------------------
// Note: All the ECC bits are inverted for 2 reasons:
//-----------------------------------------------------
// 1. To ensure that all 0's will decode to an ECC error (for eg: a disconnected DRAM will show as ECC error)
//
// 2. To enable the writing of same pattern of 'hAA on data and ECC bytes going to the DRAM through PHY BIST operation
//    This is needed to load the entire DRAM with the same pattern after DRAM initialization, before issuing any traffic
//    The ECC for 64'hAAAA_AAAA_AAAA_AAAA is 'h55
//    To get AA on the ECC byte, all bits from the ECC encoder ('h55) have to be inverted

assign secded_lane_out  = {  ~bit64,  ~bit32,  ~bit16, ~bit8,
                             ~bit4,   ~bit2,   ~bit1,  ~bit0,
                             lane_in[63: 0]         };

assign ecc_parity       = {  ~bit64,  ~bit32,  ~bit16, ~bit8,
                             ~bit4,   ~bit2,   ~bit1,  ~bit0
                          };

endmodule  // mr_secded_lane: single-error correction / double-error detection
