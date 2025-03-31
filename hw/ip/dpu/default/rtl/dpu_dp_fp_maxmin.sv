// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenminger <wolfgang.roenninger@axelera.ai>

/// Floating-Point Maxmin2
///
/// Performs fp_max or fp_min on two floating-point numbers.
///
/// fp_max2: out_o = (in1 < in2) ? in2 : in1;
/// fp_min2: out_o = (in1 < in2) ? in1 : in2;
module dpu_dp_fp_maxmin
  import dpu_pkg::*;
(
  // doc async
  // First input number.
  input  dpu_fp_t in1_i,
  // Second input number.
  input  dpu_fp_t in2_i,
  // Mode select: '0'- max, '1'- min
  input  logic    sel_i,
  // Winning result number.
  output dpu_fp_t out_o
);

  logic lt;

  dpu_dp_fp_lt u_dpu_dp_fp_lt (
    .i_operand_a    (in1_i),
    .i_operand_b    (in2_i),
    .o_a_less_than_b(lt)
  );

  assign out_o = ((sel_i && lt) || (!sel_i && !lt)) ? in1_i : in2_i;

endmodule
