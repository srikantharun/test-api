// MVM basic test-case class
`ifndef __AI_CORE_MVM_BASIC_TEST__
`define __AI_CORE_MVM_BASIC_TEST__

class ai_core_mvm_basic_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_basic_test)
      bit [AXI_LT_DATA_WIDTH-1:0]    ral_write_data;
      bit [AXI_LT_DATA_WIDTH-1:0]    ral_read_data;
      bit [AXI_LT_ADDR_WIDTH-1:0]    axi_write_addr;
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_write_data;
      bit [AXI_LT_ADDR_WIDTH-1:0]    axi_read_addr;
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_read_data;
   
      axi_master_write_sequence axi_wr_seq;
      axi_master_read_sequence axi_rd_seq;
      axi_master_stream_base_sequence #(AXI_STREAM_IFDW_DATA_WIDTH)	axi_master_stream_ifdw_base_seq;
      axi_master_stream_base_sequence #(AXI_STREAM_IFD0_DATA_WIDTH)	axi_master_stream_ifd0_base_seq;
      axi_slave_mem_response_sequence  axi_slave_stream_iau_base_seq;
  // Class constructor
  function new (string name="ai_core_mvm_basic_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_basic_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
    axi_master_stream_ifdw_base_seq	= axi_master_stream_base_sequence#(AXI_STREAM_IFDW_DATA_WIDTH)::type_id::create("axi_master_stream_ifdw_base_seq");
    axi_master_stream_ifd0_base_seq	= axi_master_stream_base_sequence#(AXI_STREAM_IFD0_DATA_WIDTH)::type_id::create("axi_master_stream_ifd0_base_seq");
    axi_slave_stream_iau_base_seq	= axi_slave_mem_response_sequence::type_id::create("axi_slave_stream_iau_base_seq");
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
      `uvm_info("MVM_CSR",$sformatf("MVM ral test starting"), UVM_LOW)
      ral_write_data = 64'h000_0003;
      ral_read_data   = 64'h000_0003;
      `uvm_info("MVM_CSR", $sformatf("Write Data = 64'h%0h, Read Data = 64'h%0h", ral_write_data, ral_read_data), UVM_LOW)
      // Perform writes and reads
      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.get();
      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.write(status, ral_write_data);
      mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.read(status, ral_read_data);
      // Comparison between the expected and the actual value
      if(ral_read_data != ral_write_data)
        `uvm_error("MVM_CSR:SINGLE_WRRD: FAILED", $sformatf("Write Data = 64'h%0h, Read Data = 64'h%0h", ral_write_data, ral_read_data))
      else
       `uvm_info("MVM_CSR:SINGLE_WRRD: PASSED", $sformatf("Write Data = 64'h%0h, Read Data = 64'h%0h", ral_write_data, ral_read_data), UVM_LOW)

  // Address and data
      `uvm_info("MVM_AXI_LP",$sformatf("MVM axi lp starting"), UVM_LOW)
      axi_write_addr = 28'h009_0008;
      axi_write_data = {$urandom, $urandom};
      // Randomize the sequence
      if (!axi_wr_seq.randomize() with {
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
      if (!axi_rd_seq.randomize() with {
        cfg_addr        == axi_write_addr;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
      })
        `uvm_fatal("run_phase", "Failed to randomize");
      axi_rd_seq.start(env.axi_system_env.master[0].sequencer);


      `uvm_info("MVM_STREAM",$sformatf("MVM stream starting"), UVM_LOW)
      //axi_master_stream_ifdw_base_seq.randomize() with {
      //  burst_length == 1; 
      //};
      //axi_master_stream_ifd0_base_seq.randomize() with {
      //  burst_length == 1; 
      //};
      //axi_slave_stream_iau_base_seq.randomize();
      //fork
      //axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);
      //axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
      //axi_slave_stream_iau_base_seq.start(env.axi_system_env.slave[0].sequencer);
      //join
    phase.drop_objection(this);
  endtask

endclass:ai_core_mvm_basic_test

`endif	// __AI_CORE_MVM_BASIC_TEST__
