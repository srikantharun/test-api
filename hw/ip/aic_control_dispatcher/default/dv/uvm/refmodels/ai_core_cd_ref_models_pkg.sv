

package ai_core_cd_ref_models_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  //`ifdef AXI_VIP
  //  import svt_uvm_pkg::*;
  //  import svt_axi_uvm_pkg::*;
  //`endif
  import aic_cd_csr_ral_pkg::*;
  import ai_core_cd_command_pkg::*;
  import token_agent_uvm_pkg::*;

  `include "ai_core_cd_ref_model_cfg.sv"
  `include "ai_core_cd_ref_model.svh"
endpackage : ai_core_cd_ref_models_pkg

