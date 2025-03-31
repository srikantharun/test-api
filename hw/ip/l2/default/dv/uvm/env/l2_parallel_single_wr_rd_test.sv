
//====================================================================================================================================
/*This test is to make the bvalid and rvalid high at same time in parallel write and read transaction such that it will
 toggle that handshake counters in the backpressure module*/
//====================================================================================================================================
 class l2_parallel_single_wr_rd_test extends l2_base_test;

  //=====================================================================================================================================
  //Registration with the factory
  //=====================================================================================================================================

  `uvm_component_utils(l2_parallel_single_wr_rd_test)

  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;

  axi_master_write_sequence axi_wr_seq; //write_sequence handle
  axi_master_read_sequence axi_rd_seq;  //read sequemce handle

  //=====================================================================================================================================
  //class constructor
  //=====================================================================================================================================

  function new (string name = "l2_parallel_single_wr_rd_test", uvm_component parent);
    super.new(name,parent);
  endfunction

  //=====================================================================================================================================
  //Build phase
  //=====================================================================================================================================

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    axi_wr_seq = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq = axi_master_read_sequence::type_id::create("axi_rd_seq");
  endfunction

  //======================================================================================================================================
  //Run phase
  //======================================================================================================================================

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    //Single write and read transaction

    axi_write_addr = 'h100000;
    axi_wr_seq.randomize() with {
      cfg_addr == axi_write_addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_32BIT;
      burst_type_enum_t == FIXED;
      burst_lenght_enum_t == BURST_LENGTH_1;
      cfg_data[0] == axi_write_data;
    };

    axi_rd_seq.randomize() with {
      cfg_addr == axi_write_addr;
      sequence_length == 1;
      burst_size_enum_t == BURST_SIZE_32BIT;
      burst_type_enum_t == FIXED;
      burst_lenght_enum_t == BURST_LENGTH_1;
    };

    //Running the write and read sequence in parallel

    fork
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
      axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
    join

     phase.drop_objection(this);
    endtask

   endclass
