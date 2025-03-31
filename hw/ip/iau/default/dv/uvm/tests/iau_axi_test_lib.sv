
// ---------------------------------------------------------------------------- IAU_AXI_M_ALIGNED_ADDR_TEST ----------------------------------------------
// IAU AXI aligned address test-case
class iau_axi_m_aligned_addr_test extends iau_base_test;
  // Registration with the factory
  `uvm_component_utils (iau_axi_m_aligned_addr_test)
  // Class Constructor
  function new (string name="iau_axi_m_aligned_addr_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);

    m_env_cfg.axi_test = 1;
    // Apply the directed master sequence to the master sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[0].sequencer.main_phase", "default_sequence", svt_axi_master_aligned_addr_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[0].sequencer.svt_axi_master_aligned_addr_sequence", "sequence_length", 100);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase

  // Run phase with timeout
  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1); // Add this line to set the timeout

    super.run_phase(phase); // Call the parent run_phase

    `uvm_info ("run_phase", "Exiting...", UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:iau_axi_m_aligned_addr_test



// ---------------------------------------------------------------------------- IAU_AXI_M_BLKING_WRRD_TEST ----------------------------------------------
// IAU AXI blocking write/read test
class iau_axi_m_blking_wrrd_test extends iau_base_test;

  // Factory registration
  `uvm_component_utils (iau_axi_m_blking_wrrd_test)

  // Class Constructor
  function new (string name="iau_axi_m_blking_wrrd_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("Build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);
    m_env_cfg.axi_test = 1;

    // Apply sequence to the master sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[0].sequencer.main_phase", "default_sequence", svt_axi_master_blocking_write_read_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[0].sequencer.svt_axi_master_blocking_write_read_sequence", "sequence_length", 200);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info ("Build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase

  // Run phase with timeout
  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1); // Add this line to set the timeout

    super.run_phase(phase); // Call the parent run_phase

    `uvm_info ("run_phase", "Exiting...", UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:iau_axi_m_blking_wrrd_test


// ---------------------------------------------------------------------------- IAU_AXI_M_WRITE_DATA_BFR_ADDR_TEST ----------------------------------------------
// IAU AXI write data before address test
class iau_axi_m_write_data_bfr_addr_test extends iau_base_test;

  // Factory registration
  `uvm_component_utils (iau_axi_m_write_data_bfr_addr_test)

  // Class Constructor
  function new (string name="iau_axi_m_write_data_bfr_addr_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("Build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);
    m_env_cfg.axi_test = 1;

    // Apply sequence to the master sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[0].sequencer.main_phase", "default_sequence", svt_axi_master_write_data_before_addr_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[0].sequencer.svt_axi_master_write_data_before_addr_sequence", "sequence_length", 200);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info ("Build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase

  // Run phase with timeout
  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1); // Add this line to set the timeout

    super.run_phase(phase); // Call the parent run_phase

    `uvm_info ("run_phase", "Exiting...", UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:iau_axi_m_write_data_bfr_addr_test


// ---------------------------------------------------------------------------- IAU_AXI_RND_TEST ---------------------------------------------------------------
// IAU AXI rnd test-case class
class iau_axi_rnd_test extends iau_base_test;

  // Registration with the factory
  `uvm_component_utils (iau_axi_rnd_test)

  // Class Constructor
  function new (string name="iau_axi_rnd_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);
    m_env_cfg.axi_test = 1;

    // Apply the svt_axi_random_sequence
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[0].sequencer.main_phase", "default_sequence", svt_axi_master_random_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[0].sequencer.svt_axi_master_random_sequence", "sequence_length", 200);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase

  // Run phase with timeout
  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1); // Add this line to set the timeout

    super.run_phase(phase); // Call the parent run_phase

    `uvm_info ("run_phase", "Exiting...", UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:iau_axi_rnd_test

