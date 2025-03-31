class ai_core_mvm_ral_bit_bash_test extends ai_core_mvm_ral_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_mvm_ral_bit_bash_test);
  uvm_status_e         status;
  ai_core_mvm_uvm_reg_bit_bash_seq seq;

  function new (string name="ai_core_mvm_ral_bit_bash_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("ai_core_mvm_ral_bit_bash_test", "is entered", UVM_LOW)
    seq = ai_core_mvm_uvm_reg_bit_bash_seq::type_id::create("seq",,get_full_name());

    `uvm_info("ai_core_mvm_ral_bit_bash_test", "build - is exited", UVM_LOW)
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this); //rasing objection
    phase.get_objection().set_drain_time(this, 150);
    uvm_report_info(get_type_name(), $psprintf("env.mvm_regmodel= \n %s", env.mvm_regmodel.sprint()), UVM_LOW);
    // Disable the assertion for ral test because we expect the x value from few registers
    //currently wrapper for mvm subsytem is not in repo
    //mvm_if.disable_axi4_errs_rdata_x_assert;
    seq.model = env.mvm_regmodel;
    // Call start method to start built-in sequences.
    `uvm_info("ai_core_mvm_ral_bit_bash_test", "Before sequence start", UVM_LOW)
    seq.start(null);
    `uvm_info("ai_core_mvm_ral_bit_bash_test", "After sequence start", UVM_LOW)
    uvm_report_info(get_type_name(), $psprintf("env.mvm_regmodel= \n %s", env.mvm_regmodel.sprint()), UVM_LOW);
    `uvm_info("ai_core_mvm_ral_bit_bash_test", "Run phase exited", UVM_LOW)
    phase.drop_objection(this);  //droping objection
  endtask : run_phase

endclass:ai_core_mvm_ral_bit_bash_test
