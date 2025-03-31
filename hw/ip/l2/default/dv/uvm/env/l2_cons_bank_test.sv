class l2_cons_bank_test extends l2_base_test;

  //Registration with the factory
  `uvm_component_utils(l2_cons_bank_test)
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;

  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  //class constructor
  function new (string name = "l2_cons_bank_test", uvm_component parent);
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
   
 
     //bank 0 last boundary
     write(32'hFFFF0);
     read(32'hFFFF0);
     checker_print();
     //bank 1 first boundary 
     write(32'h100000);
     read(32'h100000);
     checker_print();
     //bank 1 last boundary
     write(32'h1FFFF0);
     read(32'h1FFFF0);
     checker_print();
     //bank 2 first boundary 
     write(32'h200000);
     read(32'h200000);
     checker_print();
     //bank 2 last boundary
     write(32'h2FFFF0);
     read(32'h2FFFF0);
     checker_print();
     //bank 3 first boundary 
     write(32'h300000);
     read(32'h300000);
     checker_print();
     //bank 3 last boundary
     write(32'h3FFFF0);
     read(32'h3FFFF0);
     checker_print();
     //bank 4 first boundary 
     write(32'h400000);
     read(32'h400000);
     checker_print();
     //bank 4 last boundary
     write(32'h4FFFF0);
     read(32'h4FFFF0);
     checker_print();
     //bank 5 first boundary 
     write(32'h500000);
     read(32'h500000);
     checker_print();
     //bank 5 last boundary
     write(32'h5FFFF0);
     read(32'h5FFFF0);
     checker_print();
     //bank 6 first boundary 
     write(32'h600000);
     read(32'h600000);
     checker_print();
     //bank 6 last boundary
     write(32'h6FFFF0);
     read(32'h6FFFF0);
     checker_print();
     //bank 7 first boundary 
     write(32'h700000);
     read(32'h700000);
     checker_print();
    

     phase.drop_objection(this);

  endtask

task write(bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr);
    axi_wr_seq.randomize() with {
      cfg_addr == axi_write_addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_32BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
      cfg_data[0] == axi_write_addr;
      cfg_data[1] == cfg_data[0] + 36'h4;
      cfg_data[2] == cfg_data[1] + 36'h4;
      cfg_data[3] == cfg_data[2] + 36'h4;
      };
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
  endtask

  task read (bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr);
      axi_rd_seq.randomize() with {
      cfg_addr == axi_write_addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_32BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
      };
      axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
  endtask
  

  task checker_print();
     foreach (axi_wr_seq.cfg_data[i]) begin
          if((axi_rd_seq.cfg_read_data[i] == axi_wr_seq.cfg_data[i]) && (axi_wr_seq.cfg_addr == axi_rd_seq.readaddr)) begin
            `uvm_info(get_name(), $psprintf("index= %d READ ADDRESS AND WRITE ADDRESS MATCHING READ_ADDRESS= 0x%0h WRITE_ADDR= 0x%0h",i,axi_rd_seq.readaddr,axi_wr_seq.cfg_addr), UVM_LOW);
            `uvm_info(get_name(), $psprintf("READ DATA AND WRITE DATA MATCHING READ_DATA= 0x%0h WRITE_DATA= 0x%0h",axi_rd_seq.cfg_read_data[i],axi_wr_seq.cfg_data[i]), UVM_LOW);end
          else begin
            `uvm_error(get_name(), $psprintf("Address and data check failure index = %d READ_ADDR = 0x%0h WRITE_ADDR = 0x%0h READ_DATA = 0x%0h WRITE_DATA = 0x%0h",i,axi_rd_seq.readaddr,axi_wr_seq.cfg_addr,axi_rd_seq.cfg_read_data[i],axi_wr_seq.cfg_data[i])); end
          end
    endtask

    endclass 


