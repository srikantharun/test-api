// This test runs the built-in UVM reset test
// That test checks the reset value for every register
class ai_core_mvm_ral_hw_rst_test extends ai_core_mvm_ral_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_mvm_ral_hw_rst_test);

  uvm_status_e         status;
  uvm_reg_hw_reset_seq seq;

  function new (string name="ai_core_mvm_ral_hw_rst_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("ai_core_mvm_ral_hw_rst_test", "is entered", UVM_HIGH)
    seq = uvm_reg_hw_reset_seq::type_id::create("seq",,get_full_name());

    `uvm_info("ai_core_mvm_ral_hw_rst_test", "build - is exited", UVM_HIGH)
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this); //rasing objection
    `uvm_info("ai_core_mvm_ral_hw_rst_test", "Run phase entered", UVM_HIGH)
    phase.get_objection().set_drain_time(this, 100ns);
    uvm_report_info(get_type_name(), $psprintf("env.mvm_regmodel= \n %s", env.mvm_regmodel.sprint()), UVM_HIGH);
    // Disable the assertion for ral test because we expect the x value from few registers
    //currently wrapper for mvm subsytem is not in repo
    //mvm_if.disable_axi4_errs_rdata_x_assert;
    // Token Manager RAL model
    seq.model = env.mvm_regmodel;
    // Call start method to start built-in sequences.
    `uvm_info("ai_core_mvm_ral_hw_rst_test", "Before sequence start", UVM_HIGH)
     seq.start(null);
    `uvm_info("ai_core_mvm_ral_hw_rst_test", "After sequence start", UVM_HIGH)
    `uvm_info("ai_core_mvm_ral_hw_rst_test", "Run phase exited", UVM_HIGH)
    phase.drop_objection(this);  //droping objection
  endtask : run_phase

endclass:ai_core_mvm_ral_hw_rst_test
