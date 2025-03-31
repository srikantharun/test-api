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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/xpi/field_packer10.sv#1 $
// -------------------------------------------------------------------------
// Description:
//  Note: other sizes of field_packer are available in the following location: *
//     src/unused_modules/DWC_ddr_umctl2_field_packer.v                        *
`include "DWC_ddrctl_all_defs.svh"
module field_packer10
  (
   // Outputs
   out0,out1,out2,out3,out4,out5,out6,out7,out8,out9,pack_out,
   // Inputs
   in0,in1,in2,in3,in4,in5,in6,in7,in8,in9,pack_in
   );
  
  //--------------------------------------------------------------------------
  // Parameters
  //---------------------------------------------------------------------------
  
  parameter W0            = 0;
  parameter W1            = 0;
  parameter W2            = 0;
  parameter W3            = 0;
  parameter W4            = 0;
  parameter W5            = 0; 
  parameter W6            = 0;
  parameter W7            = 0;
  parameter W8            = 0;
  parameter W9            = 0; 

  localparam WALL = W0+W1+W2+W3+W4+W5+W6+W7+W8+W9;
  localparam WALL_L = (WALL==0) ? 1 : WALL;
  localparam W0_L = (W0==0) ? 1 : W0;
  localparam W1_L = (W1==0) ? 1 : W1;
  localparam W2_L = (W2==0) ? 1 : W2;
  localparam W3_L = (W3==0) ? 1 : W3;
  localparam W4_L = (W4==0) ? 1 : W4;
  localparam W5_L = (W5==0) ? 1 : W5;
  localparam W6_L = (W6==0) ? 1 : W6;
  localparam W7_L = (W7==0) ? 1 : W7;
  localparam W8_L = (W8==0) ? 1 : W8;
  localparam W9_L = (W9==0) ? 1 : W9;

  //---------------------------------------------------------------------------
  // Interface Pins
  //---------------------------------------------------------------------------
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: Used in generate block.
  input [W0_L-1:0] in0;
  input [W1_L-1:0] in1;
  input [W2_L-1:0] in2;
  input [W3_L-1:0] in3;
  input [W4_L-1:0] in4;
  input [W5_L-1:0] in5;
  input [W6_L-1:0] in6;
  input [W7_L-1:0] in7;
  input [W8_L-1:0] in8;
  input [W9_L-1:0] in9;
//spyglass enable_block W240
  input [WALL_L-1:0] pack_in;

  output [W0_L-1:0] out0;
  output [W1_L-1:0] out1;
  output [W2_L-1:0] out2;
  output [W3_L-1:0] out3;
  output [W4_L-1:0] out4;
  output [W5_L-1:0] out5;
  output [W6_L-1:0] out6;
  output [W7_L-1:0] out7;
  output [W8_L-1:0] out8;
  output [W9_L-1:0] out9;
  output [WALL_L-1:0] pack_out;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(W1 + W0)' found in module 'field_packer10'
//SJ: This coding style is acceptable and there is no plan to change it.
  generate
    if (W0>0) begin : pack_0
      assign pack_out [W0-1:0] = in0;
      assign out0 = pack_in [W0-1:0];
    end
    else begin : npack_0
      assign out0 = 1'b0;
    end
    if (W1>0) begin : pack_1
      assign pack_out       [W1+W0-1:W0] = in1;
      assign out1 = pack_in [W1+W0-1:W0] ;
    end
    else begin : npack_1
      assign out1 = 1'b0;
    end
    if (W2>0) begin : pack_2
      assign pack_out       [W2+W1+W0-1:W1+W0] = in2;
      assign out2= pack_in  [W2+W1+W0-1:W1+W0] ;
    end
    else begin : npack_2
      assign out2 = 1'b0;
    end
    if (W3>0) begin : pack_3
      assign pack_out       [W3+W2+W1+W0-1:W2+W1+W0] = in3;
      assign out3 = pack_in [W3+W2+W1+W0-1:W2+W1+W0] ;
    end
    else begin : npack_3
      assign out3 = 1'b0;
    end
    if (W4>0) begin : pack_4
      assign pack_out       [W4+W3+W2+W1+W0-1:W3+W2+W1+W0] = in4;
      assign out4 = pack_in [W4+W3+W2+W1+W0-1:W3+W2+W1+W0] ;
    end
    else begin : npack_4
      assign out4 = 1'b0;
    end
    if (W5>0) begin : pack_5
      assign pack_out       [W5+W4+W3+W2+W1+W0-1:W4+W3+W2+W1+W0] = in5;
      assign out5 = pack_in [W5+W4+W3+W2+W1+W0-1:W4+W3+W2+W1+W0] ;
    end
    else begin : npack_5
      assign out5 = 1'b0;
    end
    if (W6>0) begin : pack_6
      assign pack_out       [W6+W5+W4+W3+W2+W1+W0-1:W5+W4+W3+W2+W1+W0] = in6;
      assign out6 = pack_in [W6+W5+W4+W3+W2+W1+W0-1:W5+W4+W3+W2+W1+W0] ;
    end
    else begin : npack_6
      assign out6 = 1'b0;
    end
    if (W7>0) begin : pack_7
      assign pack_out       [W7+W6+W5+W4+W3+W2+W1+W0-1:W6+W5+W4+W3+W2+W1+W0] = in7;
      assign out7 = pack_in [W7+W6+W5+W4+W3+W2+W1+W0-1:W6+W5+W4+W3+W2+W1+W0] ;
    end
    else begin : npack_7
      assign out7 = 1'b0;
    end
    if (W8>0) begin : pack_8
      assign pack_out       [W8+W7+W6+W5+W4+W3+W2+W1+W0-1:W7+W6+W5+W4+W3+W2+W1+W0] = in8;
      assign out8 = pack_in [W8+W7+W6+W5+W4+W3+W2+W1+W0-1:W7+W6+W5+W4+W3+W2+W1+W0] ;
    end
    else begin : npack_8
      assign out8 = 1'b0;
    end
    if (W9>0) begin : pack_9
      assign pack_out       [W9+W8+W7+W6+W5+W4+W3+W2+W1+W0-1:W8+W7+W6+W5+W4+W3+W2+W1+W0] = in9;
      assign out9 = pack_in [W9+W8+W7+W6+W5+W4+W3+W2+W1+W0-1:W8+W7+W6+W5+W4+W3+W2+W1+W0] ;
    end
    else begin : npack_9
      assign out9 = 1'b0;
    end
  endgenerate
//spyglass enable_block SelfDeterminedExpr-ML

endmodule // field_packer10

