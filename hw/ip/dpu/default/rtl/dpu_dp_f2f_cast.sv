// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: FP to FP cast. Copied from FPnew and cut down beyond recognition to ignore NaNs and
// subnormals. Adheres to europa#108.
//
// Owner: Stefan Mach <stefan.mach@axelera.ai>
//
// [Original header below]
//------------------------------------------------>8------------------------------------------------
// Copyright 2019 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Stefan Mach <smach@iis.ee.ethz.ch>
//------------------------------------------------>8------------------------------------------------

module dpu_dp_f2f_cast
  import dpu_pkg::*;
#(
  parameter type src_fp_t = dpu_fp_t,
  parameter type dst_fp_t = dpu_fp_t
) (
  input  src_fp_t src_i,
  output dst_fp_t dst_o,
  output logic    overflow_o,
  output logic    underflow_o,
  output logic    inexact_o
);

  // Constants
  // ==========
  localparam src_fp_t _SRC = '0;  // INFO: Questa fails to resolve $bits(src_i.exp) as constexpr,
  localparam dst_fp_t _DST = '0;  //       treating it as a hierarchical reference.
  localparam int unsigned SRC_EXPW = $bits(_SRC.exp);  // questa fails to detect constexpr
  localparam int unsigned SRC_SIGW = $bits(_SRC.mant);
  localparam int unsigned SRC_BIAS = 2 ** (SRC_EXPW - 1) - 1;  // symmetric bias
  localparam int unsigned DST_EXPW = $bits(_DST.exp);
  localparam int unsigned DST_SIGW = $bits(_DST.mant);
  localparam int unsigned DST_BIAS = 2 ** (DST_EXPW - 1) - 1;  // symmetric bias
  // The internal exponent must be able to represent the larger one as a signed value
  localparam int unsigned MAX_EXPW = max(SRC_EXPW, DST_EXPW) + 1;  // +1 for signed
  // The wider of both mantissa widhts
  localparam int unsigned MAX_SIGW = max(SRC_SIGW, DST_SIGW);
                                     // DST_SIGW +1 +MAX_SIGW-DST_SIGW+1 -SRC_SIGW =
  localparam int          SIG_PADW = 2+MAX_SIGW-SRC_SIGW;

  // Classification
  // ===============
  logic src_zero, src_inf, dst_special;
  assign src_zero   = src_i.exp == '0; // subnormals are considered zero
  assign src_inf    = src_i.exp == '1; // NaNs are considrered infinity
  assign dst_special = src_inf | src_zero; // special values that don't take the regular path

  // Casting
  // ========
  logic signed [       MAX_EXPW-1:0] target_exp;  // re-biased exponent for destination
  logic        [       DST_EXPW-1:0] dst_exp;  // target exp in dest exponent width
  logic        [       DST_SIGW-1:0] dst_mant;  // mantissa pre-round
  logic        [MAX_SIGW-DST_SIGW:0] spill_bits;  // at least 1 bit for sticky
  logic round_bit, sticky_bit;
  logic of_before_round, uf_before_round;

  // Rebias the exponent
  assign target_exp = signed'(src_i.exp - SRC_BIAS + DST_BIAS);
  assign dst_exp = unsigned'(target_exp);  // take exponent as is, of/uf separate
  // Place source mantissa to the left of the destination mantissa, fill up with zeroes if narrower
  assign {dst_mant, round_bit, spill_bits} = {src_i.mant, {SIG_PADW{1'b0}}};
  assign sticky_bit = (|spill_bits);  // unused bits are sticky
  // Detect over/underflow
  assign of_before_round = !dst_special & target_exp >= 2 ** DST_EXPW - 1;
  assign uf_before_round = !dst_special & target_exp < 1;  // only possible on down-casts

  // Rounding
  // =========
  logic [DST_EXPW+DST_SIGW-1:0] pre_round_abs;  // absolute value of result before rounding
  logic rnd_add;

  dst_fp_t regular_result;
  logic    of_after_round;  // overflow due to rounding

  assign pre_round_abs = {dst_exp, dst_mant};
  assign rnd_add = round_bit & (sticky_bit | dst_mant[0]);  // RNE, always 0 if SRC_SIGW < DST_SIGW
  assign {regular_result.exp, regular_result.mant} = pre_round_abs + rnd_add;
  assign regular_result.sign = src_i.sign;

  // Classification after rounding
  assign of_after_round = !dst_special & !uf_before_round & regular_result.exp == '1;  // rounded up

  // Result selection
  // =================
  // Select output depending on special case detection
  assign dst_o = (src_zero | uf_before_round) ?
      '{sign: src_i.sign, exp: '0, mant: '0}
      : (src_inf | of_before_round) ?
      '{sign: src_i.sign, exp: '1, mant: '0}
      : regular_result;
  assign overflow_o = of_before_round | of_after_round;  // infinity is excluded by dst_special
  assign underflow_o = uf_before_round;
  assign inexact_o = ~dst_special & (round_bit | sticky_bit | overflow_o | underflow_o);

endmodule
