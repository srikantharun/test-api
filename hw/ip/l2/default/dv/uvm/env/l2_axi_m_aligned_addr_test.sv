// L2 AXI aligned address test-case
class l2_axi_m_aligned_addr_test extends l2_base_test;
  // Registration with the factory
  `uvm_component_utils (l2_axi_m_aligned_addr_test)

  // Class Constructor
  function new (string name="l2_axi_m_aligned_addr_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);

    // Apply the directed master sequence to the master sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[0].sequencer.main_phase", "default_sequence", svt_axi_master_aligned_addr_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[0].sequencer.svt_axi_master_aligned_addr_sequence", "sequence_length", 1000);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave[0].sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase
  
endclass:l2_axi_m_aligned_addr_test

