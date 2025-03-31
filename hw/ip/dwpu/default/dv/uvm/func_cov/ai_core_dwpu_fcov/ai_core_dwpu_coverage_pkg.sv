

package ai_core_dwpu_coverage_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import dwpu_pkg::*;
  import aic_common_pkg::*;
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif
  import token_agent_uvm_pkg::*;
  import ai_core_dwpu_agent_pkg::*;
  import ai_core_dwpu_common_pkg::*;

  `include "ai_core_dwpu_coverage.svh"

endpackage : ai_core_dwpu_coverage_pkg
