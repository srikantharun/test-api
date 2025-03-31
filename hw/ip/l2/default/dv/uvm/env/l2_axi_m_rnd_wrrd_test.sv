//`define SEQ_LIB_CFG
// Test class
class l2_axi_m_rnd_wrrd_test extends l2_base_test;
  // Registration with the factory
  `uvm_component_utils (l2_axi_m_rnd_wrrd_test)

  // Class Constructor
  function new (string name="l2_axi_m_rnd_wrrd_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("Build phase", "Entered",UVM_HIGH)
    super.build_phase(phase);
`ifdef SEQ_LIB_CFG
    // Sequence library object
    uvm_sequence_library_cfg seq_lib_cfg;
    // Sequence library creation
    //seq_lib = new("seq_lib"); 
    
    // Transaction override
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());
 
    // uvm_sequence_lib_mode could be set to UVM_SEQ_LIB_RAND, UVM_SEQ_LIB_RANDC, UVM_SEQ_LIB_ITEM or UVM_SEQ_LIB_USER 
    //                          uvm_sequence_lib_mode, Min, Max  
    seq_lib_cfg = new("seq_cfg",UVM_SEQ_LIB_RAND,      1,   1);
`endif

  /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     * 
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave[0].sequencer.main_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info ("Build phase", "Exited",UVM_HIGH)
  endfunction: build_phase
  
endclass:l2_axi_m_rnd_wrrd_test
