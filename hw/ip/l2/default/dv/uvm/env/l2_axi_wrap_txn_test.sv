class l2_axi_wrap_txn_test extends l2_base_test;

  //Registration with the factory
  `uvm_component_utils(l2_axi_wrap_txn_test)

  axi_master_wr_rd_wrap_sequence axi_wr_rd_wrap_seq;

  //class constructor
  function new (string name = "l2_axi_wrap_txn_test", uvm_component parent);
    super.new(name,parent);
  endfunction

  //Build phase
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    axi_wr_rd_wrap_seq = axi_master_wr_rd_wrap_sequence::type_id::create("axi_wr_rd_wrap_seq");
  endfunction

  //Run phase
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);


// Apply sequence to the master sequencer
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.master[0].sequencer.main_phase", "default_sequence", axi_master_wr_rd_wrap_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.master[0].sequencer.axi_master_wr_rd_wrap_sequence", "sequence_length", 1000);


     phase.drop_objection(this);
   endtask

endclass




