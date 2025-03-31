// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

/// Bind SVA in dpu
///

module dpu_dp_fp_to_fp_sva
#(
  parameter type inp_t = logic,
  parameter type oup_t = logic
) (
  input inp_t in_i,
  input oup_t out_o,
  input logic overflow_o,
  input logic underflow_o,
  input logic inexact_o
);

  wire clk; // VCF needs a clock net even if it's not relevant for the SVAs

  parameter int signed INPUT_EXPONENT_BIAS = -(2**($bits(in_i.exp)-1));
  parameter int signed OUTPUT_EXPONENT_BIAS = -(2**($bits(out_o.exp)-1));
  parameter int signed INPUT_EXPONENT_MAX = INPUT_EXPONENT_BIAS + 2**$bits(in_i.exp)-1;
  parameter int signed OUTPUT_EXPONENT_MAX = OUTPUT_EXPONENT_BIAS + 2**$bits(out_o.exp)-1;
  parameter int signed MANTISA_WIDTH_DECREASE = $bits(in_i.mant) - $bits(out_o.mant);

  logic signed [$bits(in_i.exp):0] in_i_exp_signed;
  logic signed [$bits(out_o.exp):0] out_o_exp_signed;

  assign in_i_exp_signed = $signed({1'b0, in_i.exp});
  assign out_o_exp_signed = $signed({1'b0, out_o.exp});

  logic signed [$bits(in_i.exp):0] in_i_exp_biased;
  logic signed [$bits(out_o.exp):0] out_o_exp_biased;

  assign in_i_exp_biased = signed'(INPUT_EXPONENT_BIAS + in_i_exp_signed);
  assign out_o_exp_biased = signed'(OUTPUT_EXPONENT_BIAS + out_o_exp_signed);

  logic normal_range_conversion;
  assign normal_range_conversion =              // normal range conversion if we have
       (in_i.exp != '0                        ) // non-zero and non-subnormal
    && (in_i.exp != '1                        ) // non-infinity and non-NaN
    && (in_i_exp_biased > OUTPUT_EXPONENT_BIAS) // exponent higher than destination range minimum
    && (in_i_exp_biased < OUTPUT_EXPONENT_MAX); // exponent lower than destination range maximum

  // 0. It's assumed that NaN does not occur at input
  as_nan_input: assume property(
    @(posedge clk)
    in_i.exp == '1
    |->
    in_i.mant == '0
  );

  // 1. If the input is +- infinity, the output is same sign +- infinity and no flag is raised
  ap_infinity_conversion: assert property(
    @(posedge clk)
    (in_i.exp == '1 && in_i.mant == '0)
    |->
    (out_o.sign == in_i.sign && out_o.exp == '1 && out_o.mant == '0)
    && !overflow_o && !underflow_o && !inexact_o
  ) else $error("Improper infinity conversion");

  // 2. If the input is +- zero, the output is same sign +- zero and no flag is raised
  ap_zero_conversion: assert property(
    @(posedge clk)
    (in_i.exp == '0 && in_i.mant == '0)
    |->
    (out_o.sign == in_i.sign && out_o.exp == '0 && out_o.mant == '0)
    && !overflow_o && !underflow_o && !inexact_o
  ) else $error("Improper zero conversion");

  // 3. If the input is subnormal at input, the output is set to zero and underflow and inexact flags are raised
  ap_subnormal_at_input: assert property(
    @(posedge clk)
    (in_i.exp == '0 && in_i.mant != '0)
    |->
    (out_o.sign == in_i.sign && out_o.exp == '0 && out_o.mant == '0)
    && !overflow_o && underflow_o && inexact_o
  ) else $error("Subnormal at input not rounded to zero");

  // 4. If the input is too small to be represented at output (including boundary subnormal at output), the output is set to zero and underflow and inexact flags are raised
  if($bits(in_i.exp) > $bits(out_o.exp)) begin : g_exponent_decrease_4
    ap_underflow_conversion: assert property(
      @(posedge clk)
      (in_i_exp_biased <= OUTPUT_EXPONENT_BIAS)
      && !(in_i.exp == '0 && in_i.mant == '0) // zero is special case
      |->
      (out_o.sign == in_i.sign && out_o.exp == '0 && out_o.mant == '0)
      && !overflow_o && underflow_o && inexact_o
    ) else $error("Improper underflow conversion");
  end

  // 5. If the input is too large to be represented at output (including boundary Inf/NaN at output), the output is set to same sign +- infinity and overflow flag is raised
  if($bits(in_i.exp) > $bits(out_o.exp)) begin : g_exponent_decrease_5
    ap_overflow_conversion: assert property(
      @(posedge clk)
      (in_i_exp_biased >= OUTPUT_EXPONENT_MAX)
      && !(in_i.exp == '1 && in_i.mant == '0) // infinity is special case
      |->
      (out_o.sign == in_i.sign && out_o.exp == '1 && out_o.mant == '0)
      && overflow_o && !underflow_o && !inexact_o
    ) else $error("Improper overflow conversion");
  end

  // 6. If mantisa precision decreases and the exact mantisa value cannot be represented at the output, the inexact flag is raised
  if($bits(in_i.mant) > $bits(out_o.mant)) begin : g_mantisa_decrease_6
    ap_inexact_mantisa_detection: assert property(
      @(posedge clk)
      normal_range_conversion &&
      ((in_i.mant % (2**MANTISA_WIDTH_DECREASE)) != 0)
      |->
      !overflow_o && !underflow_o && inexact_o
    ) else $error("Inexact condition not detected");
  end

  // 7. If exponent range increases, overflow cannot be raised, underflow and inexact can only be raised in the case of subnormal at input
  if($bits(in_i.exp) < $bits(out_o.exp)) begin : g_exponent_increase_7
    ap_increasing_exponent_flags: assert property(
      @(posedge clk)
      (!overflow_o)
      &&
      ((in_i.exp == '0 && in_i.mant != '0) == (underflow_o && inexact_o))
      &&
      (underflow_o == inexact_o)
    ) else $error("Inconsistent flags in increasing exponent range");
  end

  // 8. If no flags are raised, the biased exponent must be equal between input and output
  ap_normal_conversion_exponent: assert property(
    @(posedge clk)
    normal_range_conversion
    |->
    in_i_exp_biased == out_o_exp_biased
    && !underflow_o && !overflow_o
  ) else $error("Improper exponent conversion in normal range");

  // 9. If no flags are raised, fp.mant/2**$bits(fp.mant) must be equal between input and output
  if($bits(in_i.mant) < $bits(out_o.mant)) begin : g_mantisa_increase_9
    ap_normal_conversion_increase_exact_mantisa: assert property(
      @(posedge clk)
      normal_range_conversion && !inexact_o
      |->
      out_o.mant/(2**($bits(out_o.mant)-$bits(in_i.mant))) == in_i.mant
      && !underflow_o && !overflow_o
    ) else $error("Improper exact mantisa conversion");
  end

  if($bits(in_i.mant) >= $bits(out_o.mant)) begin : g_mantisa_decrease_9
    ap_normal_conversion_decrease_exact_mantisa: assert property(
      @(posedge clk)
      normal_range_conversion && !inexact_o
      |->
      in_i.mant/(2**($bits(in_i.mant)-$bits(out_o.mant))) == out_o.mant
      && !underflow_o && !overflow_o
    ) else $error("Improper exact mantisa conversion");
  end

  // 10. If only the inexact flag is raised, the mantisa output is roundedTiesToEven
  if($bits(in_i.mant) > $bits(out_o.mant)) begin : g_mantisa_decrease_10
    ap_normal_conversion_inexact_mantisa_rounds_up: assert property(
      @(posedge clk)
      normal_range_conversion && inexact_o
      && in_i.mant[MANTISA_WIDTH_DECREASE-1:0] > 2**(MANTISA_WIDTH_DECREASE-1)
      && in_i.mant[$bits(in_i.mant)-1:MANTISA_WIDTH_DECREASE] != '1
      |->
      out_o.mant > in_i.mant/2**MANTISA_WIDTH_DECREASE
    ) else $error("Inexact mantisa didn't round up when it was expected to");

    ap_normal_conversion_inexact_mantisa_rounds_down: assert property(
      @(posedge clk)
      normal_range_conversion && inexact_o
      && in_i.mant[MANTISA_WIDTH_DECREASE-1:0] < 2**(MANTISA_WIDTH_DECREASE-1)
      |->
      out_o.mant == in_i.mant/2**MANTISA_WIDTH_DECREASE // integer division already rounds down
    ) else $error("Inexact mantisa didn't round down when it was expected to");

    ap_normal_conversion_inexact_mantisa_rounds_even: assert property(
      @(posedge clk)
      normal_range_conversion && inexact_o
      && in_i.mant[MANTISA_WIDTH_DECREASE-1:0] == 2**(MANTISA_WIDTH_DECREASE-1)
      && in_i.mant[$bits(in_i.mant)-1:MANTISA_WIDTH_DECREASE] != '1
      |->
      !out_o.mant[0]
    ) else $error("Inexact mantisa didn't round to even it was expected to");
  end

endmodule : dpu_dp_fp_to_fp_sva
