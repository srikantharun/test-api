
/**
 * Abstract:
 * class ai_core_top_axi_null_virtual_sequence defines a virtual sequence ai_core_top_axi_null_virtual_sequence.
 * ai_core_top_axi_null_virtual_sequence is a no-operation sequence since the body() method
 * has empty implementation.
 *
 * ai_core_top_axi_null_virtual_sequence is used by directed_test and random_wr_rd_test.
 * These tests load this null sequence into the virtual sequencer in testbench
 * ENV, as these tests use the sequencer in the master agent.
 *
 * Execution phase: main_phase 
 * Sequencer: Can be used with any sequencer in
 * which default sequence needs to be overridden with a null sequence. In this
 * example, this sequence has been used with virtual sequencer in the testbench
 * environment.
 */

`ifndef GUARD_AXI_NULL_VIRTUAL_SEQUENCE_SV
`define GUARD_AXI_NULL_VIRTUAL_SEQUENCE_SV

class ai_core_top_axi_null_virtual_sequence extends uvm_sequence;

  /** UVM Object Utility macro */
  `uvm_object_utils(ai_core_top_axi_null_virtual_sequence)

  /** Class Constructor */
  function new (string name = "ai_core_top_axi_null_virtual_sequence");
     super.new(name);
  endfunction : new

  /** Need an empty body function to override the warning from the UVM base class */
  virtual task body();
  endtask

endclass : ai_core_top_axi_null_virtual_sequence 

`endif // GUARD_AXI_NULL_VIRTUAL_SEQUENCE_UVM_SV

