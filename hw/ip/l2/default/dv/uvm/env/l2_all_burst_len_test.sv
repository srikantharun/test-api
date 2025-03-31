class l2_all_burst_len_test extends l2_base_test;

  //Registration with the factory
  `uvm_component_utils(l2_all_burst_len_test)
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;
   rand bit [31:0] addr ;


  axi_write_sequence axi_wr_seq;
  axi_read_sequence axi_rd_seq;

  //class constructor
  function new (string name = "l2_all_burst_len_test", uvm_component parent);
    super.new(name,parent);
  endfunction

  //Build phase
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    axi_wr_seq = axi_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq = axi_read_sequence::type_id::create("axi_rd_seq");
  endfunction

  //Run phase
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
 
 repeat(1) begin
  
  for(int burst_length = 1; burst_length< 256 ;burst_length++)
  begin
  
    
  addr = $urandom_range(0,63);

    axi_wr_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_8BIT;
      burst_type_enum_t == INCR;
      burst_length_t  == burst_length;
      
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 
    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_length_t == axi_wr_seq.burst_length_t;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

    axi_wr_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_16BIT;
      burst_type_enum_t == INCR;
      burst_length_t  == burst_length;
      
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 
    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_length_t == axi_wr_seq.burst_length_t;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

    axi_wr_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_32BIT;
      burst_type_enum_t == INCR;
      burst_length_t  == burst_length;
      
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 
    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_length_t == axi_wr_seq.burst_length_t;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

    axi_wr_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_64BIT;
      burst_type_enum_t == INCR;
      burst_length_t  == burst_length;
      
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 
    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_length_t == axi_wr_seq.burst_length_t;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

    
    axi_wr_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_128BIT;
      burst_type_enum_t == INCR;
      burst_length_t  == burst_length;
      
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 
    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_length_t == axi_wr_seq.burst_length_t;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

   axi_wr_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_256BIT;
      burst_type_enum_t == INCR;
      burst_length_t  == burst_length;
      
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 
    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_length_t == axi_wr_seq.burst_length_t;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);


    axi_wr_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_512BIT;
      burst_type_enum_t == INCR;
      burst_length_t  == burst_length;
      
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 
    axi_rd_seq.randomize() with {
      cfg_addr == addr;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_length_t == axi_wr_seq.burst_length_t;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);


   end 
   end 
    
   

    phase.drop_objection(this);
  endtask

endclass
