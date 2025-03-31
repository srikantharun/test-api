// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: imc_bank package, defining parameters for the imc_bank.
//
// Authors: Roel Uytterhoeven, Bram Rooseleer
// Owner: Bram Rooseleer <bram.rooseleer@axelera.ai>

`ifndef IMC_BANK_PKG_SV
`define IMC_BANK_PKG_SV

package imc_bank_pkg;

  // IMC related parameters
  parameter IMC_DATA_W = 4;
  parameter IMC_OUT_DATA_W = 15;
  parameter IMC_NB_COLS_PER_BANK = 32;
  parameter IMC_NB_REDUNDANT_COLS_PER_BANK = 1;
  parameter IMC_NB_TOTAL_COLS_PER_BANK = IMC_NB_COLS_PER_BANK + IMC_NB_REDUNDANT_COLS_PER_BANK;
  parameter IMC_BANK_COL_PW = $clog2(IMC_NB_COLS_PER_BANK);
  parameter IMC_NB_ROWS = 576;
  parameter IMC_ROW_PW = $clog2(IMC_NB_ROWS);
  parameter IMC_COLUMNS_W = $clog2(IMC_NB_TOTAL_COLS_PER_BANK);
  parameter IMC_NB_WEIGHT_SETS = 4;
  parameter IMC_WEIGHT_SET_PW = $clog2(IMC_NB_WEIGHT_SETS);
  parameter IMC_NB_DELAY_CYCLES = 4;
  parameter IMC_BLOCK_GATING_GRANULARITY = 32;
  parameter IMC_BLOCK_ENABLE_W = IMC_NB_ROWS / IMC_BLOCK_GATING_GRANULARITY;

endpackage

`endif  // IMC_BANK_PKG_SV
