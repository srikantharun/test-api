// AI Core MVM AXI discrete test
class ai_core_mvm_axi_rnd_discr_test extends ai_core_mvm_base_test;

  // Factory registration
  `uvm_component_utils(ai_core_mvm_axi_rnd_discr_test)

  axi_master_random_discrete_sequence seq ;

  // Class Constructor
  function new(string name = "ai_core_mvm_axi_rnd_discr_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    seq = axi_master_random_discrete_sequence::type_id::create("seq");

     // Set the address range
     seq.set_address_range(32'h0009_0000, 32'h000A_1FFF);
     

    // Apply sequence to the master sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[0].sequencer.main_phase",
                                            "default_sequence",
                                            axi_master_random_discrete_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(
        this, "env.axi_system_env.master[0].sequencer.seq",
        "sequence_length", 1000);
   // // Apply the slave default response sequence to every slave sequencer
   // uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase",
   //                                         "default_sequence",
   //                                         axi_slave_mem_response_sequence::type_id::get());

    `uvm_info("Build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

endclass
