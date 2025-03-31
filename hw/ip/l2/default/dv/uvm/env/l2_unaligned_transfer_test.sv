class l2_unaligned_transfer_test extends l2_base_test;

  //Registration with the factory
  `uvm_component_utils(l2_unaligned_transfer_test)
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;
  rand bit [31:0] addr ;

  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  //class constructor
  function new (string name = "l2_unaligned_transfer_test", uvm_component parent);
    super.new(name,parent);
  endfunction

  //Build phase
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    axi_wr_seq = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq = axi_master_read_sequence::type_id::create("axi_rd_seq");
  endfunction

  //Run phase
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);


repeat (100) begin 
addr = $urandom_range(0,63);

// size = 8bit
    axi_wr_seq.randomize() with {
      cfg_addr == addr ;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_8BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
      cfg_data[0] == 1;
      cfg_data[1] == 2;
      cfg_data[2] == 3;
      cfg_data[3] == 4;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_8BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
        };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
     foreach (axi_wr_seq.cfg_data[i]) begin
      if((axi_rd_seq.cfg_read_data[i] == axi_wr_seq.cfg_data[i]) && (addr == axi_rd_seq.readaddr)) begin
        `uvm_info(get_name(), $psprintf("MATCHING EXPECTED_DATA= 0x%0h OBSERVED_DATA_DATA= 0x%0h",axi_wr_seq.cfg_data[i],axi_rd_seq.cfg_read_data[i]), UVM_LOW);end
      else begin
        `uvm_error(get_name(), $psprintf("Data check failure index = %d READ_ADDR = 0x%0h WRITE_ADDR = 0x%0h EXPECTED_DATA = 0x%0h OBSERVED_DATA = 0x%0h",i,axi_rd_seq.readaddr,addr,axi_wr_seq.cfg_data[i],axi_rd_seq.cfg_read_data[i])); end
      end





addr = $urandom_range(0, 63);

    //size = 16bit
    axi_wr_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_16BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_2;
      cfg_data[0] == 1;
      cfg_data[1] == 2;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_16BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_2;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
     foreach (axi_wr_seq.cfg_data[i]) begin
      if((axi_rd_seq.cfg_read_data[i] == axi_wr_seq.cfg_data[i]) && (addr == axi_rd_seq.readaddr)) begin
        `uvm_info(get_name(), $psprintf("MATCHING EXPECTED_DATA= 0x%0h OBSERVED_DATA_DATA= 0x%0h",axi_wr_seq.cfg_data[i],axi_rd_seq.cfg_read_data[i]), UVM_LOW);end
      else begin
        `uvm_error(get_name(), $psprintf("Data check failure index = %d READ_ADDR = 0x%0h WRITE_ADDR = 0x%0h EXPECTED_DATA = 0x%0h OBSERVED_DATA = 0x%0h",i,axi_rd_seq.readaddr,addr,axi_wr_seq.cfg_data[i],axi_rd_seq.cfg_read_data[i])); end
      end


  


addr = $urandom_range(0, (2**32 - 1) / 512) * 512 + $urandom_range(0, 32 - 1);

    //size = 32bit
    axi_wr_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_32BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
      cfg_data[0] == 1;
      cfg_data[1] == 2;
      cfg_data[2] == 3;
      cfg_data[3] == 4;

    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_32BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

 foreach (axi_wr_seq.cfg_data[i]) begin
      if((axi_rd_seq.cfg_read_data[i] == axi_wr_seq.cfg_data[i]) && (addr == axi_rd_seq.readaddr)) begin
        `uvm_info(get_name(), $psprintf("MATCHING EXPECTED_DATA= 0x%0h OBSERVED_DATA_DATA= 0x%0h",axi_wr_seq.cfg_data[i],axi_rd_seq.cfg_read_data[i]), UVM_LOW);end
      else begin
        `uvm_error(get_name(), $psprintf("Data check failure index = %d READ_ADDR = 0x%0h WRITE_ADDR = 0x%0h EXPECTED_DATA = 0x%0h OBSERVED_DATA = 0x%0h",i,axi_rd_seq.readaddr,addr,axi_wr_seq.cfg_data[i],axi_rd_seq.cfg_read_data[i])); end
      end

 
end
  phase.drop_objection(this);
  endtask

endclass
