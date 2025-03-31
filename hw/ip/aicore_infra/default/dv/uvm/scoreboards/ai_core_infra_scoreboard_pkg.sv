package ai_core_infra_scoreboard_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  //import triton_pkg::*;
  `ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  `endif

  `include "ai_core_infra_uvm_scoreboard.sv"

endpackage : ai_core_infra_scoreboard_pkg
