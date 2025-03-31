// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//        Stefan Mach <stefan.mach@axelera.ai>

/// FP A lower than B comparator
///
/// - Treats -0 and +0 as equal (returns 0)
/// - Does not handle `NaN` values.
module dpu_dp_fp_lt
  import dpu_pkg::*;
(
  /// Operand A
  input  dpu_fp_t i_operand_a,
  /// Operand B
  input  dpu_fp_t i_operand_b,
  /// Result: `(i_operand_a < i_operand_b) ? 1 : 0`
  output logic    o_a_less_than_b
);
  logic both_are_zero;
  logic a_is_smaller;

  // Detect zeroes
  always_comb both_are_zero = ~(|{i_operand_a.exp, i_operand_a.mant}) & (~(|{i_operand_b.exp, i_operand_b.mant}));
  // Invert result if non-zero signs are involved (unsigned comparison)
  always_comb a_is_smaller = (i_operand_a < i_operand_b) ^ (i_operand_a.sign || i_operand_b.sign);
  // FP-rules LT comparison here:
  always_comb o_a_less_than_b = a_is_smaller & ~both_are_zero;

endmodule
