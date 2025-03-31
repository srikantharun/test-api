class l2_axi_back_2_back_txn extends l2_base_test;

  //Registration with the factory
  `uvm_component_utils(l2_axi_back_2_back_txn)
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_write_data;
  bit [`AXI_LP_DATA_WIDTH-1:0] axi_read_data;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_read_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0] cal_addr [15:0];
  int index;
  
  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  //class constructor
  function new (string name = "l2_axi_back_2_back_txn", uvm_component parent);
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

    index = 0;
    for(int j=0;j<1;j++)
    begin
    axi_write_addr[15:0] = 0;
    axi_write_addr[19:16] = 'h0;
    if(j==0) begin
    axi_write_addr[22:20] = 0;end
    else begin
    axi_write_addr[22:20] = axi_write_addr[22:20] + 1;end
    axi_write_addr[35:23] = 0;
    for (int i=0;i<16;i=i+1)
    begin
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
        cfg_data[0] == 0;
        cfg_data[1] == cfg_data[0] + 1;
        cfg_data[2] == cfg_data[1] + 1;
        cfg_data[3] == cfg_data[2] + 1;
          };
         axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        cal_addr[index++] = axi_write_addr;
       end
   end
        
      for(int i=0;i<16;i++)
	   begin
        axi_rd_seq.randomize() with {
        cfg_addr == cal_addr[i];
        sequence_length == 1;
        burst_size_enum_t == BURST_SIZE_32BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_4;
        };
         axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
        
   end
  phase.drop_objection(this);
  endtask

 endclass
