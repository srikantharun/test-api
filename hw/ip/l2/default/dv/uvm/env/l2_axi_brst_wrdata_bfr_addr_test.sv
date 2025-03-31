// L2 AXI burst write data before address transfers test
class l2_axi_brst_wrdata_bfr_addr_test extends l2_base_test;

  // Factory registration
  `uvm_component_utils (l2_axi_brst_wrdata_bfr_addr_test)

  // Class Constructor
  function new (string name="l2_axi_brst_wrdata_bfr_addr_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("Build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);

    // Apply sequence to the system sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.sequencer.main_phase", "default_sequence", svt_axi_burst_write_data_before_address_ictest_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.sequencer.svt_axi_burst_write_data_before_address_ictest_sequence", "sequence_length", 200);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.svt_axi_system_env.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info ("Build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase
  
endclass:l2_axi_brst_wrdata_bfr_addr_test
