/**
* The aim of this test is to test the concurrency of the command write with program execution
*/
class ai_core_dwpu_concurrency_cmd_prog_test extends ai_core_dwpu_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_concurrency_cmd_prog_test)

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.main_phase", "default_sequence", ai_core_dwpu_concurrency_cmd_prog_sequence::type_id::get());
    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction : build_phase

endclass : ai_core_dwpu_concurrency_cmd_prog_test

