// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Built-in Repair Analysis
//   Built-in Self Repair
//   Implements a controller runs IMC BIST iteratively to search for feasible repair settings
//   Implements self repair datapath to shift repair settings onto the IMC banks
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module imc_bira_bisr
  import imc_bank_pkg::IMC_BANK_COL_PW;
  import mvm_pkg::MVM_IMC_BANK_PW;
#(
  /// BIST command and config interface
  parameter type aic_csr_hw2reg_t = imc_bist_pkg::aic_csr_hw2reg_t,
  /// BIST status inferface
  parameter type aic_csr_reg2hw_t = imc_bist_pkg::aic_csr_reg2hw_t
) (
  input  wire             i_clk,
  input  wire             i_rst_n,

  /// Command and config inputs interface from mux
  input  aic_csr_reg2hw_t i_mux_reg,
  /// Status outputs interface to mux
  output aic_csr_hw2reg_t o_mux_reg,
  /// Command and config outputs to bist_ctl
  output aic_csr_reg2hw_t o_ctl_reg,
  /// Status inputs from bist_ctl
  input  aic_csr_hw2reg_t i_ctl_reg,

  /// Serial repair mux bira-mode enable to repair hooks
  output logic            o_imc_bisr_mux_mode,
  /// Serial repair shift enable to repair hooks
  output logic            o_imc_bisr_shift_en,
  /// Serial repair update enable to repair hooks
  output logic            o_imc_bisr_ue,
  /// Serial repair data output to repair hooks
  output logic            o_imc_bisr_si,
  /// Serial repair data input from repair hooks
  input  logic            i_imc_bisr_so
);

  logic                             clear;
  logic [1:0]                       imc_repair_req;
  logic [1:0] [MVM_IMC_BANK_PW-1:0] imc_repair_bank;
  logic [1:0] [IMC_BANK_COL_PW-1:0] imc_repair_col;
  logic [1:0]                       imc_repair_ack;
  logic [1:0]                       imc_repair_nack;

  imc_bira #(
    .aic_csr_hw2reg_t(aic_csr_hw2reg_t),
    .aic_csr_reg2hw_t(aic_csr_reg2hw_t)
  ) u_imc_bira (
    .i_clk,
    .i_rst_n,
    .i_mux_reg,
    .o_mux_reg,
    .o_ctl_reg,
    .i_ctl_reg,
    .o_clear          (clear),
    .o_imc_bisr_mux_mode,
    .o_imc_repair_req (imc_repair_req),
    .o_imc_repair_bank(imc_repair_bank),
    .o_imc_repair_col (imc_repair_col),
    .i_imc_repair_ack (imc_repair_ack),
    .i_imc_repair_nack(imc_repair_nack)
  );

  imc_bisr u_imc_bisr (
    .i_clk,
    .i_rst_n,
    .i_clear              (clear),
    .i_max_repair_attempts(i_mux_reg.imc_bist_cfg.max_repair_attempts.q),
    .i_imc_repair_req     (imc_repair_req),
    .i_imc_repair_bank    (imc_repair_bank),
    .i_imc_repair_col     (imc_repair_col),
    .o_imc_repair_ack     (imc_repair_ack),
    .o_imc_repair_nack    (imc_repair_nack),
    .o_imc_bisr_shift_en,
    .o_imc_bisr_ue,
    .o_imc_bisr_si,
    .i_imc_bisr_so
  );

endmodule : imc_bira_bisr
