`ifndef GUARD_AI_CORE_MVM_SANITY_TEST_SV
`define GUARD_AI_CORE_MVM_SANITY_TEST_SV

// AI CORE LS sanity test class
class ai_core_mvm_sanity_test extends ai_core_mvm_base_test;

  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_sanity_test)

  string path;

  // Class Constructor
  function new(string name = "ai_core_mvm_sanity_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    //  /** Define the test DIR */
    uvm_config_db #(string)::get(null, "*", "path", path);

   `uvm_info("Shahid Rizwan Khokher", $sformatf("Path = %s", path), UVM_LOW)
   `uvm_info("Shahid Rizwan Khokher", $sformatf("Path = %s", path), UVM_LOW)
   `uvm_info("Shahid Rizwan Khokher", $sformatf("Path = %s", path), UVM_LOW)
   `uvm_info("Shahid Rizwan Khokher", $sformatf("Path = %s", path), UVM_LOW)
   `uvm_info("Shahid Rizwan Khokher", $sformatf("Path = %s", path), UVM_LOW)

    // Apply the directed master sequence to the master sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[0].sequencer.main_phase", "default_sequence", axi_master_directed_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[1].sequencer.main_phase", "default_sequence", axi_master_stream_base_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[2].sequencer.main_phase", "default_sequence", axi_master_stream_base_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[3].sequencer.main_phase", "default_sequence", axi_master_stream_base_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[4].sequencer.main_phase", "default_sequence", axi_master_stream_base_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[5].sequencer.main_phase", "default_sequence", axi_master_stream_base_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[6].sequencer.main_phase", "default_sequence", axi_master_directed_sequence::type_id::get());

    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[0].sequencer.axi_master_directed_sequence",   "sequence_length", 5);
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[1].sequencer.axi_master_stream_base_sequence","sequence_length", 5);
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[2].sequencer.axi_master_stream_base_sequence","sequence_length", 5);
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[3].sequencer.axi_master_stream_base_sequence","sequence_length", 5);
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[4].sequencer.axi_master_stream_base_sequence","sequence_length", 5);
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[5].sequencer.axi_master_stream_base_sequence","sequence_length", 5);
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[6].sequencer.axi_master_directed_sequence",   "sequence_length", 5);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase","default_sequence",axi_slave_mem_response_sequence::type_id::get());

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

endclass : ai_core_mvm_sanity_test

`endif  // GUARD_AI_CORE_MVM_SANITY_TEST_SV
