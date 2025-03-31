// MVM reg_narrow_access test-case class
`ifndef __AI_CORE_MVM_REG_NARROW_ACCESS_TEST__
`define __AI_CORE_MVM_REG_NARROW_ACCESS_TEST__

class ai_core_mvm_reg_narrow_access_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_reg_narrow_access_test)
      bit [AXI_LT_ADDR_WIDTH-1:0]    axi_write_addr;
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_write_data;
      bit [AXI_LT_ADDR_WIDTH-1:0]    axi_read_addr;
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_read_data;

      axi_master_write_sequence axi_wr_seq;
      axi_master_read_sequence axi_rd_seq;
  // Class constructor
  function new (string name="ai_core_mvm_reg_narrow_access_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_reg_narrow_access_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
  // Address and data
       `uvm_info("MVM_REG",$sformatf("MVM axi reg starting"), UVM_HIGH)
      axi_write_addr = 28'h009_8000;
      axi_write_data = {$urandom, $urandom};
       // Randomize the sequence
      if(!axi_wr_seq.randomize() with {
        cfg_addr        == axi_write_addr;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == axi_write_data;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      // Start the sequence on the respective sequencer
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
      if(axi_wr_seq.write_transaction.bresp == AXI_OKAY_RESPONSE)
       `uvm_info("MVM_WRITE_REG_COMPARE: PASSED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp), UVM_HIGH)
      else
       `uvm_error("MVM_WRITE_REG_COMPARE: FAILED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp))
      if(!axi_rd_seq.randomize() with {
        cfg_addr        == axi_write_addr;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
      if(axi_rd_seq.read_transaction.rresp[0] == AXI_OKAY_RESPONSE)
       `uvm_info("MVM_READ_REG_COMPARE: PASSED", $sformatf("RRESP = %s", axi_rd_seq.read_transaction.rresp[0]), UVM_HIGH)
      else
       `uvm_error("MVM_READ_REG_COMPARE: FAILED", $sformatf("RRESP = %s",axi_rd_seq.read_transaction.rresp[0]))

     // Commented code becuse of Document bug https://git.axelera.ai/ai-hw-team/triton/-/issues/576
     // // Randomize the sequence
     // axi_wr_seq.randomize() with {
     //   cfg_addr        == axi_write_addr;
     //   sequence_length == 'd1;
     //   burst_size_enum_t == BURST_SIZE_32BIT;
     //   burst_type_enum_t == FIXED;
     //   burst_lenght_enum_t == BURST_LENGTH_1;
     //   cfg_data[0] == axi_write_data;
     // };
     // // Start the sequence on the respective sequencer
     // axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
     // if(axi_wr_seq.write_transaction.bresp == AXI_OKAY_RESPONSE)
     //  `uvm_info("MVM_WRITE_REG_COMPARE: PASSED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp), UVM_HIGH)
     // else
     //  `uvm_error("MVM_WRITE_REG_COMPARE: FAILED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp))
     // axi_rd_seq.randomize() with {
     //   cfg_addr        == axi_write_addr;
     //   sequence_length == 'd1;
     //   burst_size_enum_t == BURST_SIZE_32BIT;
     //   burst_type_enum_t == FIXED;
     //   burst_lenght_enum_t == BURST_LENGTH_1;
     // };
     // axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
     // if(axi_rd_seq.read_transaction.rresp[0] == AXI_OKAY_RESPONSE)
     //  `uvm_info("MVM_READ_REG_COMPARE: PASSED", $sformatf("RRESP = %s", axi_rd_seq.read_transaction.rresp[0]), UVM_HIGH)
     // else
     //  `uvm_error("MVM_READ_REG_COMPARE: FAILED", $sformatf("RRESP = %s",axi_rd_seq.read_transaction.rresp[0]))
     // // Randomize the sequence
     // axi_wr_seq.randomize() with {
     //   cfg_addr        == axi_write_addr;
     //   sequence_length == 'd1;
     //   burst_size_enum_t == BURST_SIZE_16BIT;
     //   burst_type_enum_t == FIXED;
     //   burst_lenght_enum_t == BURST_LENGTH_1;
     //   cfg_data[0] == axi_write_data;
     // };
     // // Start the sequence on the respective sequencer
     // axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
     // if(axi_wr_seq.write_transaction.bresp == AXI_OKAY_RESPONSE)
     //  `uvm_info("MVM_WRITE_REG_COMPARE: PASSED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp), UVM_HIGH)
     // else
     //  `uvm_error("MVM_WRITE_REG_COMPARE: FAILED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp))
     // axi_rd_seq.randomize() with {
     //   cfg_addr        == axi_write_addr;
     //   sequence_length == 'd1;
     //   burst_size_enum_t == BURST_SIZE_16BIT;
     //   burst_type_enum_t == FIXED;
     //   burst_lenght_enum_t == BURST_LENGTH_1;
     // };
     // axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
     // if(axi_rd_seq.read_transaction.rresp[0] == AXI_OKAY_RESPONSE)
     //  `uvm_info("MVM_READ_REG_COMPARE: PASSED", $sformatf("RRESP = %s", axi_rd_seq.read_transaction.rresp[0]), UVM_HIGH)
     // else
     //  `uvm_error("MVM_READ_REG_COMPARE: FAILED", $sformatf("RRESP = %s",axi_rd_seq.read_transaction.rresp[0]))
     // // Randomize the sequence
     // axi_wr_seq.randomize() with {
     //   cfg_addr        == axi_write_addr;
     //   sequence_length == 'd1;
     //   burst_size_enum_t == BURST_SIZE_8BIT;
     //   burst_type_enum_t == FIXED;
     //   burst_lenght_enum_t == BURST_LENGTH_1;
     //   cfg_data[0] == axi_write_data;
     // };
     // // Start the sequence on the respective sequencer
     // axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
     // if(axi_wr_seq.write_transaction.bresp == AXI_OKAY_RESPONSE)
     //  `uvm_info("MVM_WRITE_REG_COMPARE: PASSED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp), UVM_HIGH)
     // else
     //  `uvm_error("MVM_WRITE_REG_COMPARE: FAILED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp))
     // axi_rd_seq.randomize() with {
     //   cfg_addr        == axi_write_addr;
     //   sequence_length == 'd1;
     //   burst_size_enum_t == BURST_SIZE_8BIT;
     //   burst_type_enum_t == FIXED;
     //   burst_lenght_enum_t == BURST_LENGTH_1;
     // };
     // axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
     // if(axi_rd_seq.read_transaction.rresp[0] == AXI_OKAY_RESPONSE)
     //  `uvm_info("MVM_READ_REG_COMPARE: PASSED", $sformatf("RRESP = %s", axi_rd_seq.read_transaction.rresp[0]), UVM_HIGH)
     // else
     //  `uvm_error("MVM_READ_REG_COMPARE: FAILED", $sformatf("RRESP = %s",axi_rd_seq.read_transaction.rresp[0]))


     // for(int i=0;i<6;i++) begin

     //   if(i==0) axi_write_addr = 28'h009_0000;
     //   if(i==1) axi_write_addr = 28'h009_1000;
     //   if(i==2) axi_write_addr = 28'h009_2000;
     //   if(i==3) axi_write_addr = 28'h009_8000;
     //   if(i==4) axi_write_addr = 28'h00A_1000;
     //   if(i==5) axi_write_addr = 28'h00A_2000;
     //     // Randomize the sequence
     //     axi_wr_seq.randomize() with {
     //       cfg_addr        == axi_write_addr;
     //       sequence_length == 'd1;
     //       burst_size_enum_t == BURST_SIZE_8BIT;
     //       burst_type_enum_t == FIXED;
     //       burst_lenght_enum_t == BURST_LENGTH_1;
     //       cfg_data[0] == axi_write_data;
     //     };
     //     // Start the sequence on the respective sequencer
     //     axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
     //     if(axi_wr_seq.write_transaction.bresp == AXI_OKAY_RESPONSE)
     //      `uvm_info("MVM_WRITE_REG_COMPARE: PASSED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp), UVM_HIGH)
     //     else
     //      `uvm_error("MVM_WRITE_REG_COMPARE: FAILED", $sformatf("BRESP = %s", axi_wr_seq.write_transaction.bresp))
     //     axi_rd_seq.randomize() with {
     //       cfg_addr        == axi_write_addr;
     //       sequence_length == 'd1;
     //       burst_size_enum_t == BURST_SIZE_8BIT;
     //       burst_type_enum_t == FIXED;
     //       burst_lenght_enum_t == BURST_LENGTH_1;
     //     };
     //     axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
     //     if(axi_rd_seq.read_transaction.rresp[0] == AXI_OKAY_RESPONSE)
     //      `uvm_info("MVM_READ_REG_COMPARE: PASSED", $sformatf("RRESP = %s", axi_rd_seq.read_transaction.rresp[0]), UVM_HIGH)
     //     else
     //      `uvm_error("MVM_READ_REG_COMPARE: FAILED", $sformatf("RRESP = %s",axi_rd_seq.read_transaction.rresp[0]))

     // end
    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_reg_narrow_access_test

`endif	// __AI_CORE_MVM_REG_NARROW_ACCESS_TEST__
