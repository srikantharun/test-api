// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DWPU reference model Package
// Owner: Jorge Carvalho <jorge.carvalho@axelera.ai>
package ai_core_dwpu_ref_model_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import aic_common_pkg::*;
  import dwpu_pkg::*;
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  import ai_core_dwpu_common_pkg::*;
  import token_agent_uvm_pkg::*;
  import ai_core_dwpu_agent_pkg::*;

  `include "ai_core_dwpu_ref_model.svh"
endpackage : ai_core_dwpu_ref_model_pkg
