// AI Core MVM AXI b2b_test-case class
class ai_core_mvm_b2b_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_b2b_test)
      bit [AXI_LT_ADDR_WIDTH-1:0]    axi_addr[$];
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_write_data;
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_read_data;

      axi_master_write_sequence axi_wr_seq;
      axi_master_read_sequence axi_rd_seq;
  // Class constructor
  function new (string name="ai_core_mvm_b2b_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_b2b_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
  // Address and data
       `uvm_info("MVM_REG",$sformatf("MVM axi reg starting"), UVM_LOW)

      axi_addr.push_back(28'h009_8000);
      axi_addr.push_back(28'h009_1000);
      axi_write_data = {$urandom, $urandom};
       // Randomize the sequence

      for (int i =0;i<axi_addr.size();i++) begin
      axi_wr_seq.randomize() with {
        cfg_addr        == axi_addr[i];
        sequence_length == 'd3;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == axi_write_data;
      };
      // Start the sequence on the respective sequencer
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
      if(axi_wr_seq.write_transaction.bresp == AXI_OKAY_RESPONSE)
       `uvm_info("MVM_WRITE_REG_COMPARE: PASSED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp), UVM_LOW)
      else
       `uvm_error("MVM_WRITE_REG_COMPARE: FAILED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp))
      end  

    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_b2b_test

