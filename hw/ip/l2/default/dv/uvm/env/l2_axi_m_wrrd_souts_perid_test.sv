// L2 AI write/read single outstanding per id test-case class
class l2_axi_m_wrrd_souts_perid_test extends l2_base_test;
  // Registration with the factory
  `uvm_component_utils (l2_axi_m_wrrd_souts_perid_test)

  // Class Constructor
  function new (string name="l2_axi_m_wrrd_souts_perid_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);

    cfg.master_cfg[0].single_outstanding_per_id_enable = 1;
    cfg.master_cfg[0].single_outstanding_per_id_kind = svt_axi_port_configuration::MODIFY_SAME_ID;
    cfg.master_cfg[0].num_outstanding_xact = -1;
    cfg.master_cfg[0].num_read_outstanding_xact = 127;
    cfg.master_cfg[0].num_write_outstanding_xact = 127;
    cfg.master_cfg[0].id_width = 4;

    cfg.slave_cfg[0].single_outstanding_per_id_enable = 1;
    cfg.slave_cfg[0].single_outstanding_per_id_kind = svt_axi_port_configuration::MODIFY_SAME_ID;
    cfg.slave_cfg[0].num_outstanding_xact = -1;
    cfg.slave_cfg[0].num_read_outstanding_xact = 127;
    cfg.slave_cfg[0].num_write_outstanding_xact = 127;
    cfg.slave_cfg[0].id_width = 4;

    // Apply the directed master sequence to the master sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[0].sequencer.main_phase", "default_sequence", axi_master_wr_rd_single_outstanding_per_id_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[0].sequencer.axi_master_wr_rd_single_outstanding_per_id_sequence", "sequence_length", 1000);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave[0].sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase
  
endclass
