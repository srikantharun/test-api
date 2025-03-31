// MVM reg_burst with_crossing_boundary test-case class
`ifndef __AI_CORE_MVM_REG_BURST_WITH_CROSSING_BOUNDARY_TEST__
`define __AI_CORE_MVM_REG_BURST_WITH_CROSSING_BOUNDARY_TEST__

class ai_core_mvm_reg_burst_with_crossing_boundary_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_reg_burst_with_crossing_boundary_test)
      bit [AXI_LT_ADDR_WIDTH-1:0]    axi_write_addr;
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_write_data;
      bit [AXI_LT_ADDR_WIDTH-1:0]    axi_read_addr;
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_read_data;

      axi_master_write_sequence axi_wr_seq;
      axi_master_read_sequence axi_rd_seq;
  // Class constructor
  function new (string name="ai_core_mvm_reg_burst_with_crossing_boundary_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_reg_burst_with_crossing_boundary_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    // Address and dat

      `uvm_info("MVM_REG",$sformatf("MVM axi reg starting"), UVM_LOW)
      axi_write_addr = 28'h009_FFE0;
      axi_write_data = {$urandom, $urandom};
      // Randomize the sequence
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == axi_write_addr;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_4;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      // Start the sequence on the respective sequencer
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
      if(axi_wr_seq.write_transaction.bresp == AXI_SLVERR_RESPONSE)
       `uvm_info("MVM_WRITE_REG_COMPARE: PASSED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp), UVM_LOW)
      else
       `uvm_error("MVM_WRITE_REG_COMPARE: FAILED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp))
      if(!axi_rd_seq.randomize() with {
        cfg_addr        == axi_write_addr;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_4;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
      foreach(axi_rd_seq.read_transaction.rresp[i]) begin
        if(axi_rd_seq.read_transaction.rresp[i] == AXI_SLVERR_RESPONSE)
         `uvm_info("MVM_READ_REG_COMPARE: PASSED", $sformatf("RRESP[%0d] = %s", i, axi_rd_seq.read_transaction.rresp[i]), UVM_LOW)
        else
         `uvm_error("MVM_READ_REG_COMPARE: FAILED", $sformatf("RRESP[%0d] = %s",i, axi_rd_seq.read_transaction.rresp[i]))
      end
    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_reg_burst_with_crossing_boundary_test

`endif	// __AI_CORE_MVM_REG_BURST_WITH_CROSSING_BOUNDARY_TEST__
