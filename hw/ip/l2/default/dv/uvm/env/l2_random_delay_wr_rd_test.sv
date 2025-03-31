//=======================================================================================================================================
//This test to check the behaviour of the memory with random delay for write and read sequence running in parallel
//=======================================================================================================================================

class l2_random_delay_wr_rd_test extends l2_base_test;

  //=====================================================================================================================================
  //Registration with the factory
  //=====================================================================================================================================
  `uvm_component_utils(l2_random_delay_wr_rd_test)

  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] cal_addr;
  bit [6:0] wr_delay;    //write delay
  bit [6:0] rd_delay;    //read delay

  axi_master_write_sequence axi_wr_seq;   //write sequence
  axi_master_read_sequence axi_rd_seq;    //read sequence

  //=====================================================================================================================================
  //class constructor
  //=====================================================================================================================================

  function new (string name = "l2_random_delay_wr_rd_test", uvm_component parent);
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

  //====================================================================================================================================
  //Run phase
  //====================================================================================================================================
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

  //======================================================================================================================================
  /* 1.Used two for loop. First for loop is to loop the banks ( 0 to 7 ) and second to loop the ram ( 0 to 15 ) inside each bank.
     2.Randomized the wr_delay and rd_delay.
     3. Made to run the write and read sequence inside fork join_none with random delay. */
  //======================================================================================================================================

    for(int j=0;j<8;j++)
    begin
    axi_write_addr[15:0] = 0;
    axi_write_addr[19:16] = 'h0;
    if(j==0) begin
    axi_write_addr[22:20] = 0;end
    else begin
    axi_write_addr[22:20] = axi_write_addr[22:20] + 1;end
    axi_write_addr[35:23] = 0;
    //axi_write_addr = 36'h0;
    for (int i=0;i<16;i=i+1)
    begin
        std::randomize(wr_delay) with { wr_delay dist { 0:= 50 , [1:127]:= 50};};
        std::randomize(rd_delay) with { rd_delay dist { 0:= 50 , [1:127]:= 50};};
        if(i==0) begin
        axi_write_addr[19:16] = 0; end
        else begin
        axi_write_addr [19:16] = axi_write_addr[19:16] + 'h1; end
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


        axi_rd_seq.randomize() with {
        cfg_addr == axi_write_addr;
        sequence_length == 1;
        burst_size_enum_t == BURST_SIZE_32BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_4;
        };

        fork
        #wr_delay axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        #rd_delay axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
        join_none

        `uvm_info("Wr_delay",$sformatf("%d", wr_delay), UVM_LOW);
        `uvm_info("rd_delay",$sformatf("%d", rd_delay), UVM_LOW);

        wait fork;

    end
   end
   phase.drop_objection(this);
  endtask

 endclass
