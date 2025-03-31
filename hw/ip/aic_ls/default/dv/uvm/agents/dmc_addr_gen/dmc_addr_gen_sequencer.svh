`ifndef DMC_ADDR_GEN_SEQUENCER_SV
`define DMC_ADDR_GEN_SEQUENCER_SV

class dmc_addr_gen_sequencer extends uvm_sequencer#(dmc_addr_gen_seq_item);
  `uvm_component_utils(dmc_addr_gen_sequencer)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual dmc_addr_gen_if vif;

  task wait_cycles(int x=1);
    repeat(x) @(vif.mon);
  endtask

endclass

`endif


