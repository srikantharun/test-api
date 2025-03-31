//
// This test runs the built-in UVM reset test
// That test checks the reset value for every register
class iau_ral_hw_rst_test extends iau_ral_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (iau_ral_hw_rst_test);

  uvm_status_e         status;
  uvm_reg_hw_reset_seq seq;

  function new (string name="iau_ral_hw_rst_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("iau_ral_hw_rst_test", "is entered", UVM_LOW)
    seq = uvm_reg_hw_reset_seq::type_id::create("seq",,get_full_name());

    `uvm_info("iau_ral_hw_rst_test", "build - is exited", UVM_LOW)
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    `uvm_info("iau_ral_hw_rst_test", "Run phase entered", UVM_LOW)
    phase.get_objection().set_drain_time(this, 100ns);

    // Token Manager RAL model
    seq.model = env.regmodel;
    // Call start method to start built-in sequences.
    `uvm_info("iau_ral_hw_rst_test", "Before sequence start", UVM_LOW)
    seq.start(null);
    `uvm_info("iau_ral_hw_rst_test", "After sequence start", UVM_LOW)
    env.regmodel.print();
    `uvm_info("iau_ral_hw_rst_test", "Run phase exited", UVM_LOW)

  endtask : run_phase

endclass:iau_ral_hw_rst_test
