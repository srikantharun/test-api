package dpu_scoreboard_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  import dpu_common_pkg::*;
  import token_agent_uvm_pkg::*;
  import dpu_agent_pkg::*;

  `include "dpu_scoreboard.svh"
endpackage : dpu_scoreboard_pkg

