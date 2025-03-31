// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: imc bist package
// Defines parameters and structs
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef IMC_BIST_PKG_SV
`define IMC_BIST_PKG_SV

package imc_bist_pkg;
  // =======================================
  // Parameter definition
  // =======================================
  // ! IMC_BIST_CYCLE_PW must match CSR reg width MVM_EXE_CSR_IMC_BIST_STATUS.ERROR_CYCLE
  parameter int unsigned IMC_BIST_CYCLE_PW = 24;
  // ! IMC_BIST_REPAIR_ATTEMPT_PW must match CSR reg width MVM_EXE_CSR_IMC_BIST_CFG.MAX_REPAIR_ATTEMPTS
  parameter int unsigned IMC_BIST_REPAIR_ATTEMPT_PW = 5;
  parameter int unsigned NUM_COMPARATORS = 8;
  parameter int unsigned NUM_REPAIR_HOOKS = 32;
  parameter int unsigned NUM_REPAIR_HOOKS_PW = $clog2(NUM_REPAIR_HOOKS);

  // =======================================
  // Enum definition
  // =======================================
  typedef enum logic {
    E_IMC_MBIST = 1'b0,
    E_IMC_CBIST = 1'b1
  } bist_type_e;

  typedef enum logic [2:0] {
    E_NEIGHBOR = 3'b000,
    E_GOLDEN_ZEROES = 3'b001,
    E_GOLDEN_ONES = 3'b010,
    E_GOLDEN_55 = 3'b011,
    E_GOLDEN_AA = 3'b100
  } expect_type_e;

  // =======================================
  // Struct definition
  // =======================================
  typedef struct packed {
    struct packed {
      logic        q;
    } mbist_start;
    struct packed {
      logic        q;
    } cbist_start;
    struct packed {
      logic        q;
    } resume;
    struct packed {
      logic        q;
    } stop;
  } reg2hw_imc_bist_cmd_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
    } csr_sel;
    struct packed {
      logic [4:0]  q;
    } max_repair_attempts;
    struct packed {
      logic [1:0]  q;
    } bira_mode;
    struct packed {
      logic        q;
    } burn_in;
    struct packed {
      logic        q;
    } fail_analysis;
  } reg2hw_imc_bist_cfg_reg_t;

  typedef struct packed {
    struct packed {
      logic [23:0] q;
    } error_cycle;
    struct packed {
      logic [4:0]  q;
    } error_col;
    struct packed {
      logic [3:0]  q;
    } error_bank;
    struct packed {
      logic        q;
    } repair_needed;
    struct packed {
      logic        q;
    } pass;
    struct packed {
      logic        q;
    } done;
    struct packed {
      logic        q;
    } busy;
  } reg2hw_imc_bist_status_reg_t;

  typedef struct packed {
    struct packed {
      logic        d;
      logic        de;
    } mbist_start;
    struct packed {
      logic        d;
      logic        de;
    } cbist_start;
    struct packed {
      logic        d;
      logic        de;
    } resume;
    struct packed {
      logic        d;
      logic        de;
    } stop;
  } hw2reg_imc_bist_cmd_reg_t;

  typedef struct packed {
    struct packed {
      logic [23:0] d;
      logic        de;
    } error_cycle;
    struct packed {
      logic [4:0]  d;
      logic        de;
    } error_col;
    struct packed {
      logic [3:0]  d;
      logic        de;
    } error_bank;
    struct packed {
      logic        d;
      logic        de;
    } repair_needed;
    struct packed {
      logic        d;
      logic        de;
    } pass;
    struct packed {
      logic        d;
      logic        de;
    } done;
    struct packed {
      logic        d;
      logic        de;
    } busy;
  } hw2reg_imc_bist_status_reg_t;

  // one version with extended field names as used in AIC CSR that is placed in mid
  typedef struct packed {
    hw2reg_imc_bist_cmd_reg_t imc_bist_cmd;
    hw2reg_imc_bist_status_reg_t imc_bist_status;
  } aic_csr_hw2reg_t;

  typedef struct packed {
    reg2hw_imc_bist_cmd_reg_t imc_bist_cmd;
    reg2hw_imc_bist_cfg_reg_t imc_bist_cfg;
    reg2hw_imc_bist_status_reg_t imc_bist_status;
  } aic_csr_reg2hw_t;

  typedef struct packed {
    logic lbank_ok;
    logic rbank_ok;
    logic [imc_bank_pkg::IMC_BANK_COL_PW-1:0] fail_column;
  } compare_bus_t;

  ////////////////////////////////
  // Compressed repair settings //
  ////////////////////////////////
  ///  A 7-bit representation of the repair settings.
  ///  This is useful to minimize the required wiring.
  ///
  typedef struct packed {
    /// Repair required active high
    ///
    logic repair_en;
    /// Repair column index in 63,...,0
    ///
    /// Columns 63,...,32 mapped to columns 31,...,0 of u_mvm_imc_bank_wrapper[1]
    ///
    /// Columns 31,...,0 mapped directly to u_mvm_imc_bank_wrapper[0]
    ///
    logic [5:0] repair_col;
  } compressed_repair_t;

  //////////////////////////////////
  // Uncompressed repair settings //
  //////////////////////////////////
  ///  A 32-bit representation of the repair settings. There are two distinct representations:
  ///
  ///  1. Thermometer encoding as required by the IMC bank macro: `repair_setting = ~((32)'({repair_col{repair_en}}))`
  ///
  ///  2. One-hot encoding encoding as strongly recommended for the fusebox interface: `repair_setting = (32)'(repair_en<<repair_col)`
  ///
  typedef logic [31:0] uncompressed_repair_t;

  typedef struct packed {
    logic mux_mode;
    logic shift_en;
    logic ue;
    logic s;
  } imc_repair_struct_t;

endpackage

`endif  // IMC_BIST_PKG
