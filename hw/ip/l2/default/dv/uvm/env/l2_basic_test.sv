class l2_basic_test extends l2_base_test;

  //Registration with the factory
  `uvm_component_utils(l2_basic_test)
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;

  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  //class constructor
  function new (string name = "l2_basic_test", uvm_component parent);
    super.new(name,parent);
  endfunction

  //Build phase
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    axi_wr_seq = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq = axi_master_read_sequence::type_id::create("axi_rd_seq");
  endfunction

  //Run phase
  virtual task main_phase(uvm_phase phase);
    phase.raise_objection(this);
    // size = 8bit
    axi_write_addr = 40'h10000;
    axi_write_data = $urandom;
    axi_wr_seq.randomize() with {
      cfg_addr == axi_write_addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_32BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
      cfg_data[0] == axi_write_data;
      cfg_data[1] == cfg_data[0] + 'h4;
      cfg_data[2] == cfg_data[1] + 'h4;
      cfg_data[3] == cfg_data[2] + 'h4;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == axi_write_addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_32BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

     phase.drop_objection(this);
  endtask

endclass
