// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token Manager Reference Model Package
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>
// Author: Raymond Garcia <raymond.garcia@axelera.ai>
package tkn_mng_aic_ref_model_pkg;

    `include "uvm_macros.svh"
    import uvm_pkg::*;
    import token_agent_uvm_pkg::*;


    parameter int unsigned TOKEN_MGR_COUNTER_SATURATION_VALUE         = 8'hFF;


    typedef enum bit {
        PROD_NONE,
        PRODUCE
    } token_mgr_prod_action_t;


    typedef enum bit {
        CONS_NONE,
        CONSUME
    } token_mgr_cons_action_t;


    `include "tkn_mng_aic_ref_model_cfg.sv"
    `include "tkn_mng_aic_ref_model_item.sv"
    `include "tkn_mng_aic_ref_model.sv"

endpackage //tkn_mng_aic
