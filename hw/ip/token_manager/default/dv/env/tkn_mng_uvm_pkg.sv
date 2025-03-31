// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>

package tkn_mng_uvm_pkg;

    timeunit      1ns;
    timeprecision 1ns;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    import tkn_mng_aic_agent_pkg::*;
    import token_agent_uvm_pkg::*;

   // Environment and environment Configurations
  `include "tkn_mng_env.svh"

endpackage
