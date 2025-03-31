// DMA IP basic test-case class
`ifndef __DMA_IP_BASIC_REG_TEST__
`define __DMA_IP_BASIC_REG_TEST__

class dma_ip_basic_reg_test extends dma_ip_base_test;
  // Registration with the factory
  `uvm_component_utils(dma_ip_basic_reg_test)
  // Class constructor
  function new (string name="dma_ip_basic_reg_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("dma_ip_basic_reg_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      `uvm_info("DMA_IP_TEST",$sformatf("DMA IP Basic Test starting"), UVM_LOW)
 
      // 2 WRITES
       if (!axi_wr_seq.randomize() with {
        cfg_addr        == 32'h000_0000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == 64'h0000_0101_0000_0000;
      })
	     `uvm_fatal(get_name, "axi_wr_seq : Randomization Failed!")
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      if (!axi_wr_seq.randomize() with {
        cfg_addr        == 32'h000_0004;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == 64'h2200;
      })
	     `uvm_fatal(get_name, "axi_wr_seq : Randomization Failed!")
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      // 2 READS
       if (!axi_rd_seq.randomize() with {
        cfg_addr        == 32'h000_0000;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
      })
	     `uvm_fatal(get_name, "axi_rd_seq : Randomization Failed!")
      axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

      if (!axi_rd_seq.randomize() with {
        cfg_addr        == 32'h000_0004;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
      })
	     `uvm_fatal(get_name, "axi_rd_seq : Randomization Failed!")
      axi_rd_seq.start(env.axi_system_env.master[0].sequencer);




      `uvm_info("DMA_IP_TEST",$sformatf("DMA IP Basic Test starting"), UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass:dma_ip_basic_reg_test

`endif	// __DMA_IP_BASIC_REG_TEST__
