class l2_addr_out_of_range_check_test extends l2_base_test;

  //Registration with the factory
  `uvm_component_utils(l2_addr_out_of_range_check_test)
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;

  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  //class constructor
  function new (string name = "l2_addr_out_of_range_check_test", uvm_component parent);
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
  axi_write_addr = 36'h800000;
  axi_wr_seq.randomize() with {
  cfg_addr == axi_write_addr;
  sequence_length == 1;
  burst_size_enum_t == BURST_SIZE_64BIT;
  burst_type_enum_t == INCR;
  burst_lenght_enum_t == BURST_LENGTH_8;
  cfg_data[0] == axi_write_addr;
  cfg_data[1] == cfg_data[0] + 36'h8;
  cfg_data[2] == cfg_data[1] + 36'h8;
  cfg_data[3] == cfg_data[2] + 36'h8;
  cfg_data[4] == cfg_data[3] + 36'h8;
  cfg_data[5] == cfg_data[4] + 36'h8;
  cfg_data[6] == cfg_data[5] + 36'h8;
  cfg_data[7] == cfg_data[6] + 36'h8;
  };
  axi_wr_seq.start(env.axi_system_env.master[0].sequencer);


  axi_rd_seq.randomize() with {
  cfg_addr == axi_write_addr;
  sequence_length == 1;
  burst_size_enum_t == BURST_SIZE_64BIT;
  burst_type_enum_t == INCR;
  burst_lenght_enum_t == BURST_LENGTH_8;
  };
  axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

  foreach (axi_wr_seq.cfg_data[i]) begin
    if((axi_rd_seq.cfg_read_data[i] == axi_wr_seq.cfg_data[i]) && (axi_write_addr == axi_rd_seq.readaddr)) begin
      `uvm_info(get_name(), $psprintf("index=%d READ ADDRESS AND WRITE ADDRESS MATCHING READ_ADDRESS= 0x%0h WRITE_ADDR= 0x%0h",i,axi_rd_seq.readaddr,axi_write_addr), UVM_LOW);
      `uvm_info(get_name(), $psprintf("READ DATA AND WRITE DATA MATCHING READ_DATA= 0x%0h WRITE_DATA= 0x%0h",axi_rd_seq.cfg_read_data[i],axi_wr_seq.cfg_data[i]), UVM_LOW);end
    else begin
      `uvm_error(get_name(), $psprintf("middle address and data check failure index = %d READ_ADDR = 0x%0h WRITE_ADDR = 0x%0h READ_DATA = 0x%0h WRITE_DATA = 0x%0h",i,axi_rd_seq.readaddr,axi_write_addr,axi_rd_seq.cfg_read_data[i],axi_wr_seq.cfg_data[i])); end
    end
  
  phase.drop_objection(this);
  endtask

 endclass

