//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/rd/rd_linkecc_secded.sv#1 $
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
//    Read Link-ECC SECDED module
// -------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module rd_linkecc_secded (
    input  [127:0] data_in
   ,input  [15:0]  dmi_in
   ,input          mrr
   ,input          poison_type
   ,input          poison_data
   ,output         corr_err
   ,output         uncorr_err
   ,output [8:0]   syndrome
   ,output [127:0] corrected_data
);

//--------------------------------- WIRES --------------------------------------
wire  [127:0]  data;
wire  [7:0]    b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15;
wire  [8:0]    dc;
wire           ds0,ds1,ds2,ds3,ds4,ds5,ds6,ds7,ds8;

wire           no_err;
wire  [2:0]    corr_err_bit;
wire  [3:0]    corr_err_beat;
wire  [2:0]    sum_s7_s3;
wire           corr_err_cb;

wire  [1:0]    poison;
//----------------------- COMBINATORIAL ASSIGNMENTS ----------------------------

// Poison
assign poison = {(poison_data&poison_type), poison_data};
assign data = {data_in[127:2], (data_in[1:0]^poison)};


// Generate ECC check bit (Data)
assign {b15,b14,b13,b12,b11,b10,b9,b8,b7,b6,b5,b4,b3,b2,b1,b0} = data;
assign dc=dmi_in[15:7];

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
assign ds8 = (^data) ^ (^dc);


// Max Data ECC bit and DMI ECC bit
assign syndrome = {ds8,ds7,ds6,ds5,ds4,ds3,ds2,ds1,ds0};


// No-err/1bit-err/2bit-err
assign no_err     = ({ds8,ds7,ds6,ds5,ds4,ds3,ds2,ds1,ds0}==9'b0_0000_0000) | mrr;
assign uncorr_err = (~no_err) & (~ds8) & (~mrr);
assign corr_err   = (~no_err) & ( ds8) & (~mrr);

assign corr_err_bit  = (corr_err)? {ds2,ds1,ds0} : 3'd0;
assign corr_err_beat = (~corr_err)? 4'd0 :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b00011)? 4'd0  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b11100)? 4'd1  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b00101)? 4'd2  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b11010)? 4'd3  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b00110)? 4'd4  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b11001)? 4'd5  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b00111)? 4'd6  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b11000)? 4'd7  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b01001)? 4'd8  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b10110)? 4'd9  :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b01010)? 4'd10 :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b10101)? 4'd11 :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b01011)? 4'd12 :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b10100)? 4'd13 :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b01100)? 4'd14 :
                          ({ds7,ds6,ds5,ds4,ds3}==5'b10011)? 4'd15 : 4'd0;

assign sum_s7_s3 = ds7+ds6+ds5+ds4+ds3;
assign corr_err_cb = (corr_err)? (sum_s7_s3 < 3'd2) : 1'b0;

// The following condition is all true, input data will be corrected.
// - 1-bit error
// - Error happened within data (Not ECC-code)
wire [127:0]   corr_err_mask;
assign corr_err_mask = ({{127{1'b0}}, (corr_err & (~corr_err_cb))} << {corr_err_beat,corr_err_bit});
assign corrected_data = data ^ corr_err_mask;


endmodule
