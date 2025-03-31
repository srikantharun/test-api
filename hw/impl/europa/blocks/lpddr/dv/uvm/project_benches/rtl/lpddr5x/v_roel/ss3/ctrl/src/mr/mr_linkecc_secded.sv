//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/mr/mr_linkecc_secded.sv#1 $
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
//    Write Link-ECC SECDED module
// -------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module mr_linkecc_secded (
    input  [127:0] data_in
   ,input  [15:0]  mask_in
   ,input          poison_type
   ,input          poison_data
   ,input          poison_dmi
   ,output [15:0]  ecc_parity
);

//--------------------------------- WIRES --------------------------------------
wire  [7:0]    b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15;
wire  [8:0]    dc;
wire           ds0,ds1,ds2,ds3,ds4,ds5,ds6,ds7,ds8;

wire  [15:0]   m;
wire  [5:0]    mc;
wire           ms0,ms1,ms2,ms3,ms4,ms5;

wire  [15:0]   poison;

//----------------------- COMBINATORIAL ASSIGNMENTS ----------------------------

// Generate ECC check bit (Data)
assign {b15,b14,b13,b12,b11,b10,b9,b8,b7,b6,b5,b4,b3,b2,b1,b0} = data_in;
assign dc=9'd0;

assign ds0 = b0[1] ^ b1[1] ^ b2[1] ^ b3[1] ^ b4[1] ^ b5[1] ^ b6[1] ^ b7[1] ^ b8[1] ^ b9[1] ^ b10[1] ^ b11[1] ^ b12[1] ^ b13[1] ^ b14[1] ^ b15[1] ^
             b0[3] ^ b1[3] ^ b2[3] ^ b3[3] ^ b4[3] ^ b5[3] ^ b6[3] ^ b7[3] ^ b8[3] ^ b9[3] ^ b10[3] ^ b11[3] ^ b12[3] ^ b13[3] ^ b14[3] ^ b15[3] ^
             b0[5] ^ b1[5] ^ b2[5] ^ b3[5] ^ b4[5] ^ b5[5] ^ b6[5] ^ b7[5] ^ b8[5] ^ b9[5] ^ b10[5] ^ b11[5] ^ b12[5] ^ b13[5] ^ b14[5] ^ b15[5] ^
             b0[7] ^ b1[7] ^ b2[7] ^ b3[7] ^ b4[7] ^ b5[7] ^ b6[7] ^ b7[7] ^ b8[7] ^ b9[7] ^ b10[7] ^ b11[7] ^ b12[7] ^ b13[7] ^ b14[7] ^ b15[7] ^ dc[0];

assign ds1 = (^b0[3:2]) ^ (^b1[3:2]) ^ (^b2[3:2] ) ^ (^b3[3:2] ) ^ (^b4[3:2] ) ^ (^b5[3:2] ) ^ (^b6[3:2] ) ^ (^b7[3:2] ) ^
             (^b0[7:6]) ^ (^b1[7:6]) ^ (^b2[7:6] ) ^ (^b3[7:6] ) ^ (^b4[7:6] ) ^ (^b5[7:6] ) ^ (^b6[7:6] ) ^ (^b7[7:6] ) ^
             (^b8[3:2]) ^ (^b9[3:2]) ^ (^b10[3:2]) ^ (^b11[3:2]) ^ (^b12[3:2]) ^ (^b13[3:2]) ^ (^b14[3:2]) ^ (^b15[3:2]) ^ 
             (^b8[7:6]) ^ (^b9[7:6]) ^ (^b10[7:6]) ^ (^b11[7:6]) ^ (^b12[7:6]) ^ (^b13[7:6]) ^ (^b14[7:6]) ^ (^b15[7:6]) ^ dc[1];

assign ds2 = (^b0[7:4]) ^ (^b1[7:4]) ^ (^b2[7:4] ) ^ (^b3[7:4] ) ^ (^b4[7:4] ) ^ (^b5[7:4] ) ^ (^b6[7:4] ) ^ (^b7[7:4] ) ^
             (^b8[7:4]) ^ (^b9[7:4]) ^ (^b10[7:4]) ^ (^b11[7:4]) ^ (^b12[7:4]) ^ (^b13[7:4]) ^ (^b14[7:4]) ^ (^b15[7:4]) ^ dc[2];

assign ds3 = (^b0) ^ (^b2) ^ (^b5) ^ (^b6) ^ (^b8) ^ (^b11) ^ (^b12) ^ (^b15) ^ dc[3];
assign ds4 = (^b0) ^ (^b3) ^ (^b4) ^ (^b6) ^ (^b9) ^ (^b10) ^ (^b12) ^ (^b15) ^ dc[4];
assign ds5 = (^b1) ^ (^b2) ^ (^b4) ^ (^b6) ^ (^b9) ^ (^b11) ^ (^b13) ^ (^b14) ^ dc[5];
assign ds6 = (^b1) ^ (^b3) ^ (^b5) ^ (^b7) ^ (^b8) ^ (^b10) ^ (^b12) ^ (^b14) ^ dc[6];
assign ds7 = (^b1) ^ (^b3) ^ (^b5) ^ (^b7) ^ (^b9) ^ (^b11) ^ (^b13) ^ (^b15) ^ dc[7];
assign ds8 = (^data_in) ^ ds0 ^ ds1 ^ ds2 ^ ds3 ^ ds4 ^ ds5 ^ ds6 ^ ds7 ^ dc[8];

// Generate ECC check bit (DMI)
assign m = mask_in;
assign mc = 6'd0;

assign ms0 = m[1] ^ m[3] ^ m[5] ^ m[7] ^ m[9] ^ m[11] ^ m[13] ^ m[15] ^ mc[0];
assign ms1 = (^m[3:2]) ^ (^m[7:6]) ^ (^m[11:10]) ^ (^m[15:14]) ^ mc[1];
assign ms2 = (^m[ 3:0]) ^ (^m[15: 8]) ^ mc[2];
assign ms3 = (^m[ 7:0]) ^ (^m[15:12]) ^ mc[3];
assign ms4 = (^m[15:4])               ^ mc[4];
assign ms5 = (^m) ^ ms0 ^ ms1 ^ ms2 ^ ms3 ^ ms4 ^ mc[5];


// MUX Data ECC bit and DMI ECC bit
assign ecc_parity = {ds8,ds7,ds6,ds5,ds4,ds3,ds2,ds1,ds0, ms5,ms4,ms3,ms2,ms1,ms0, 1'b0} ^ poison;

// Generate poison
assign poison = {7'b0000000,(poison_data&poison_type),poison_data, 4'b0000, (poison_dmi&poison_type),poison_dmi, 1'b0};

endmodule
