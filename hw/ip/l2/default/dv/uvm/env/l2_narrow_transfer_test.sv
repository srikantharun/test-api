class l2_narrow_transfer_test extends l2_base_test;

  //Registration with the factory
  `uvm_component_utils(l2_narrow_transfer_test)
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;

  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  
  rand int burst_size;


  //class constructor
  function new (string name = "l2_narrow_transfer_test", uvm_component parent);
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
    for (int iteration=0 ; iteration <100; iteration ++) begin
    std::randomize (burst_size) with { burst_size inside {0, 1, 2, 3} ;} ;  // Constrainted to run the narrow burst size with 8,16,32,64
    for(int i=0; i<10; i++) begin  //To send the multiple transaction with same size
    axi_wr_seq.randomize() with {
      cfg_addr == axi_write_addr;
      sequence_length == 1;
      burst_size_enum_t == burst_size;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_1;
          };
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

    axi_rd_seq.randomize() with {
      cfg_addr == axi_write_addr;
      sequence_length == 1;
      burst_size_enum_t == axi_wr_seq.burst_size_enum_t;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == axi_wr_seq.burst_lenght_enum_t;
    };
    axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
    end 
    end

     phase.drop_objection(this);
  endtask

endclass
