class l2_axi_max_len_txn_test extends l2_base_test;

  //Registration with the factory
  `uvm_component_utils(l2_axi_max_len_txn_test)
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;

  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  //class constructor
  function new (string name = "l2_axi_max_len_txn_test", uvm_component parent);
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

  repeat (10) begin
  //burst length 128
        axi_wr_seq.randomize() with {
      cfg_addr == 32'h0;
      sequence_length == 1;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_1;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 
    axi_rd_seq.randomize() with {
      cfg_addr == 32'h0;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_1;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);


    

  //burst length 4 
     axi_wr_seq.randomize() with {
      cfg_addr == 32'h100000;
      sequence_length == 1;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 
    axi_rd_seq.randomize() with {
      cfg_addr == 32'h100000;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t ;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_4;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

  //burst length 256

      axi_wr_seq.randomize() with {
      cfg_addr == 32'h0;
      sequence_length == 1;
      burst_type_enum_t == INCR;
      burst_size_enum_t == BURST_SIZE_256BIT;
      burst_lenght_enum_t == BURST_LENGTH_256;
      write_strobe == 32'h55555555;
      
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 

    axi_rd_seq.randomize() with {
      cfg_addr == 32'h0;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_256;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

      //burst length 256

      axi_wr_seq.randomize() with {
      cfg_addr == 32'h0;
      sequence_length == 1;
      burst_type_enum_t == INCR;
      burst_size_enum_t == BURST_SIZE_256BIT;
      burst_lenght_enum_t == BURST_LENGTH_256;
      write_strobe == 32'haaaaaaaa;
      
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
 

    axi_rd_seq.randomize() with {
      cfg_addr == 32'h0;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_256;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);




  //burst length 1
     axi_wr_seq.randomize() with {
      cfg_addr == 32'h200000;
      sequence_length == 1;
      burst_type_enum_t == INCR;
      burst_size_enum_t == BURST_SIZE_256BIT ;
      burst_lenght_enum_t == BURST_LENGTH_1;
      write_strobe == 64'haaaaaaaaaaaaaaaa;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == 32'h200000;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_1;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);


  //fixed
     axi_wr_seq.randomize() with {
      cfg_addr == 32'h200000;
      sequence_length == 1;
      burst_type_enum_t == FIXED;
      burst_size_enum_t == BURST_SIZE_256BIT ;
      burst_lenght_enum_t == BURST_LENGTH_1;
      write_strobe == 64'haaaaaaaaaaaaaaaa;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == 32'h200000;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_1;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);


    //burst length 1
     axi_wr_seq.randomize() with {
      cfg_addr == 32'h200000;
      sequence_length == 1;
      burst_type_enum_t == INCR;
      burst_size_enum_t == BURST_SIZE_256BIT ;
      burst_lenght_enum_t == BURST_LENGTH_1;
      write_strobe == 64'h5555555555555555;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == 32'h200000;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_1;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);


    //fixed
     axi_wr_seq.randomize() with {
      cfg_addr == 32'h200000;
      sequence_length == 1;
      burst_type_enum_t == FIXED;
      burst_size_enum_t == BURST_SIZE_256BIT ;
      burst_lenght_enum_t == BURST_LENGTH_1;
      write_strobe == 64'h5555555555555555;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == 32'h200000;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_1;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);


     //burst length 1
     axi_wr_seq.randomize() with {
      cfg_addr == 32'h600000;
      sequence_length == 1;
      burst_type_enum_t == FIXED;
      burst_size_enum_t == BURST_SIZE_256BIT ;
      burst_lenght_enum_t == BURST_LENGTH_1;
      write_strobe == 64'h5555555555555555;
    };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == 32'h200000;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == FIXED;
      burst_lenght_enum_t == BURST_LENGTH_1;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

 end 
   
  phase.drop_objection(this);
  endtask

endclass
