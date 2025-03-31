`ifndef CC_CLK_DIV_AGENT_UVM_PKG_SV
`define CC_CLK_DIV_AGENT_UVM_PKG_SV


package cc_clk_div_agent_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  //include necessary files for token manager package
  `include "cc_clk_div_agent_enums.svi"
  `include "cc_clk_div_agent_parameters.svi"
  `include "cc_clk_div_agent_config.sv"
  `include "cc_clk_div_agent_seq_item.sv"
  `include "cc_clk_div_agent_sequence_library.sv"
  `include "cc_clk_div_agent_monitor.sv"
  `include "cc_clk_div_agent_sequencer.sv"
  `include "cc_clk_div_agent_driver.sv"
  `include "cc_clk_div_agent.sv"

endpackage : cc_clk_div_agent_uvm_pkg

`endif // CC_CLK_DIV_AGENT_UVM_PKG_SV

