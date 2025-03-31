`ifndef TOKEN_AGENT_SEQUENCER_SV
`define TOKEN_AGENT_SEQUENCER_SV

class token_agent_sequencer extends uvm_sequencer#(token_agent_seq_item);
  `uvm_component_utils(token_agent_sequencer)

  virtual token_agent_if m_vif;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

endclass : token_agent_sequencer

`endif // TOKEN_AGENT_SEQUENCER_SV


