`define AXI_VIP

// AI_CORE_INFRA UVM package
package ai_core_infra_uvm_pkg;

  timeunit      1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

`ifdef AXI_VIP

  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  `include "ai_core_infra_tb_define.svh"
   // Environment and environment Configurations
  `include "cust_svt_axi_system_configuration.svh"
  `include "axi_virtual_sequencer.svh"
  // Scoreboard
  `include "../scoreboards/ai_core_infra_uvm_scoreboard.sv"
  `include "ai_core_infra_env.svh"

 
`endif
endpackage:ai_core_infra_uvm_pkg
