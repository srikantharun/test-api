// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

/// Testbench to check only FP to FP converters in FV
///

`ifndef DPU_DP_FP_TO_FP_TB_SV
`define DPU_DP_FP_TO_FP_TB_SV

module dpu_dp_fp_to_fp_tb
  import dpu_pkg::*;
(
  input wire i_clk,
  input wire i_rst_n
);

  fp16_t   fp16_fp18_inp;
  dpu_fp_t fp16_fp18_oup;
  logic    fp16_fp18_ovf;
  logic    fp16_fp18_udf;
  logic    fp16_fp18_ine;

  dpu_dp_fp16_to_fp18 u_fp16_fp18 (
    .in_i       (fp16_fp18_inp),
    .out_o      (fp16_fp18_oup),
    .overflow_o (fp16_fp18_ovf),
    .underflow_o(fp16_fp18_udf),
    .inexact_o  (fp16_fp18_ine)
  );
  
  dpu_fp_t fp18_fp16_inp;
  fp16_t   fp18_fp16_oup;
  logic    fp18_fp16_ovf;
  logic    fp18_fp16_udf;
  logic    fp18_fp16_ine;

  dpu_dp_fp18_to_fp16 u_fp18_fp16 (
    .in_i       (fp18_fp16_inp),
    .out_o      (fp18_fp16_oup),
    .overflow_o (fp18_fp16_ovf),
    .underflow_o(fp18_fp16_udf),
    .inexact_o  (fp18_fp16_ine)
  );

  dpu_fp_t fp18_fp32_inp;
  fp32_t   fp18_fp32_oup;
  logic    fp18_fp32_ovf;
  logic    fp18_fp32_udf;
  logic    fp18_fp32_ine;

  dpu_dp_fp18_to_fp32 u_fp18_fp32 (
    .in_i       (fp18_fp32_inp),
    .out_o      (fp18_fp32_oup),
    .overflow_o (fp18_fp32_ovf),
    .underflow_o(fp18_fp32_udf),
    .inexact_o  (fp18_fp32_ine)
  );

  fp32_t   fp32_fp18_inp;
  dpu_fp_t fp32_fp18_oup;
  logic    fp32_fp18_ovf;
  logic    fp32_fp18_udf;
  logic    fp32_fp18_ine;

  dpu_dp_fp32_to_fp18 u_fp32_fp18 (
    .in_i       (fp32_fp18_inp),
    .out_o      (fp32_fp18_oup),
    .overflow_o (fp32_fp18_ovf),
    .underflow_o(fp32_fp18_udf),
    .inexact_o  (fp32_fp18_ine)
  );

endmodule

`endif // DPU_DP_FP_TO_FP_TB_SV
