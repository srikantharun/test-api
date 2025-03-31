`ifndef TOKEN_AGENT_UVM_PKG_SV
`define TOKEN_AGENT_UVM_PKG_SV


package token_agent_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  //include necessary files for token manager package
  `include "token_agent_enums.svi"
  `include "token_agent_parameters.svi"
  `include "token_agent_config.sv"
  `include "token_agent_seq_item.sv"
  `include "token_agent_sequence_library.sv"
  `include "token_agent_monitor.sv"
  `include "token_agent_sequencer.sv"
  `include "token_agent_driver.sv"
  `include "token_agent.sv"

endpackage : token_agent_uvm_pkg

`endif // TOKEN_AGENT_UVM_PKG_SV

