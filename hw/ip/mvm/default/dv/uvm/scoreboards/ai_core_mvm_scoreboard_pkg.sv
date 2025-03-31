package ai_core_mvm_scoreboard_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mvm_pkg::*;
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif
  import token_agent_uvm_pkg::*;
  import ai_core_mvm_common_pkg::*;

  `include "ai_core_mvm_scoreboard.sv"

endpackage : ai_core_mvm_scoreboard_pkg
