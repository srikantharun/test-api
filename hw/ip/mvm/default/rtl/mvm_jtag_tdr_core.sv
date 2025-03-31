// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DFT insertable TDR core
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef MVM_JTAG_TDR_CORE_SV
`define MVM_JTAG_TDR_CORE_SV

module mvm_jtag_tdr_core
  import imc_bank_pkg::IMC_BANK_COL_PW;
  import mvm_pkg::MVM_IMC_BANK_PW;
  import imc_bist_pkg::IMC_BIST_REPAIR_ATTEMPT_PW;
  import imc_bist_pkg::IMC_BIST_CYCLE_PW;
#(
  parameter type aic_csr_hw2reg_t = imc_bist_pkg::aic_csr_hw2reg_t,
  parameter type aic_csr_reg2hw_t = imc_bist_pkg::aic_csr_reg2hw_t
) (
  // JTAG
  input  logic tcki,
  input  logic trsti,
  // JTAG TAP
  input  logic seli,
  input  logic sei,
  input  logic cei,
  input  logic uei,
  input  logic tdi,
  output logic tdo,

  input  logic                         i_busy,
  input  logic                         i_done,
  input  logic                         i_pass,
  input  logic                         i_repair_needed,
  input  logic   [MVM_IMC_BANK_PW-1:0] i_error_bank,
  input  logic   [IMC_BANK_COL_PW-1:0] i_error_col,
  input  logic [IMC_BIST_CYCLE_PW-1:0] i_error_cycle,

  output logic                                  o_mbist_start,
  output logic                                  o_cbist_start,
  output logic                                  o_resume,
  output logic                                  o_stop,
  output logic [IMC_BIST_REPAIR_ATTEMPT_PW-1:0] o_max_repair_attempts,
  output logic                          [2-1:0] o_bira_mode,
  output logic                                  o_burn_in,
  output logic                                  o_fail_analysis
);

`ifndef TARGET_DFT
`ifndef TESSENT
  assign tdo = 1'b0;

  assign o_mbist_start = '0;
  assign o_cbist_start = '0;
  assign o_resume = '0;
  assign o_stop = '0;
  assign o_max_repair_attempts = '0;
  assign o_bira_mode = '0;
  assign o_burn_in = '0;
  assign o_fail_analysis = '0;
`endif // ! TESSENT
`endif // ! TARGET_DFT

endmodule
`endif  // MVM_JTAG_TDR_CORE_SV
