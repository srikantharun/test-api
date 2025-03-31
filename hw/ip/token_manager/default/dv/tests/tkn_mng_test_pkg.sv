// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>

package tkn_mng_test_pkg;

    timeunit      1ns;
    timeprecision 1ns;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    import tkn_mng_aic_sequences_pkg::*;
    import tkn_mng_uvm_pkg::*;
    import token_agent_uvm_pkg::*;

    // Tests
    `include "tkn_mng_base_test.svh"
    `include "tkn_mng_hello_world_test.svh"
    `include "tkn_mng_loc_dev_test.svh"

endpackage
