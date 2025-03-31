// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Muxes the IMC BIST interface between CSR and JTAG
//   TODO: Implement register slice
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module imc_bist_intf_mux #(
  /// BIST command and config interface
  parameter type aic_csr_hw2reg_t = imc_bist_pkg::aic_csr_hw2reg_t,
  /// BIST status inferface
  parameter type aic_csr_reg2hw_t = imc_bist_pkg::aic_csr_reg2hw_t
) (
  input  wire             i_clk,
  input  wire             i_rst_n,

  /// Command and config inputs interface from CSR
  input  aic_csr_reg2hw_t i_regcsr,
  /// Status outputs interface to CSR
  output aic_csr_hw2reg_t o_regcsr,
  /// Command and config inputs interface from JTAG
  input  aic_csr_reg2hw_t i_regjtag,
  /// Status outputs interface to JTAG
  output aic_csr_hw2reg_t o_regjtag,
  /// Command and config outputs to bira_ctl
  output aic_csr_reg2hw_t o_regmuxed,
  ///  Status inputs from bira_ctl
  input  aic_csr_hw2reg_t i_regmuxed
);

  assign o_regmuxed = i_regcsr.imc_bist_cfg.csr_sel.q ? i_regcsr : i_regjtag;
  assign o_regcsr  = i_regcsr.imc_bist_cfg.csr_sel.q ? i_regmuxed : '0;
  assign o_regjtag = (~i_regcsr.imc_bist_cfg.csr_sel.q) ? i_regmuxed : '0;

endmodule : imc_bist_intf_mux
