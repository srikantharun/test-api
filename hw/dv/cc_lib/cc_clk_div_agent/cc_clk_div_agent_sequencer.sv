`ifndef CC_CLK_DIV_AGENT_SEQUENCER_SV
`define CC_CLK_DIV_AGENT_SEQUENCER_SV

class cc_clk_div_agent_sequencer extends uvm_sequencer#(cc_clk_div_agent_seq_item);
  `uvm_component_utils(cc_clk_div_agent_sequencer)

  virtual cc_clk_div_agent_if m_vif;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

endclass : cc_clk_div_agent_sequencer

`endif // CC_CLK_DIV_AGENT_SEQUENCER_SV


