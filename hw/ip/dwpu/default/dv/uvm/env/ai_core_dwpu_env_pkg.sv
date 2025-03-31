

package ai_core_dwpu_env_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import dwpu_pkg::*;
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif
  import dwpu_csr_ral_pkg::*;
  import token_agent_uvm_pkg::*;
  import ai_core_dwpu_agent_pkg::*;
  import ai_core_dwpu_ref_model_pkg::*;
  import ai_core_dwpu_scoreboard_pkg::*;
  import ai_core_dwpu_coverage_pkg::*;
  import ai_core_dwpu_common_pkg::*;

  `include "warning_catcher.sv"
  // Environment and environment Configurations
  `include "dwpu_cust_svt_axi_system_configuration.sv"
  `include "dwpu_cust_svt_axi_system_cc_configuration.sv"
  `include "dwpu_axi_virtual_sequencer.sv"
  `include "ai_core_dwpu_axi_slverr_adapter.sv"

  // Environment configuration and environment
  `include "ai_core_dwpu_env_cfg.sv"
`ifdef TARGET_GLS
  `include "ai_core_dwpu_gls_demoter.sv"
`endif // TARGET_GLS
  `include "ai_core_dwpu_env.sv"

endpackage : ai_core_dwpu_env_pkg
