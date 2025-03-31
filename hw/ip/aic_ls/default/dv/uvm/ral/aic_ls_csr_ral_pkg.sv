// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI CORE LS RAL package.
//             (But strictly the regmodel package)
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

// Manually created RAL model package for AI Core LS Sub-system
package aic_ls_csr_ral_pkg;
  // Packages import
  import uvm_pkg::*;
  import dv_base_reg_pkg::*;
  import v_utils_pkg::*;
  import ifd_csr_ral_pkg::*;
  import odr_csr_ral_pkg::*;

  parameter int unsigned AIC_DMC_NUM_REGBLOCKS = 9;

  // Macro includes
  `include "uvm_macros.svh"
  `include "aic_ls_subsys_reg_block.svh"
  `include "aic_ls_ral.svh"

endpackage:aic_ls_csr_ral_pkg

