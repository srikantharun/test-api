/**
 * Sequence that does small random transactions to the program memory from DWPU
 */
class  ai_core_dwpu_small_random_prog_sequence extends ai_core_dwpu_base_sequence;
  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;
  
  rand int sequence_length;
  
  constraint c_reasonable_sequence_length {soft sequence_length == 100;}

  `uvm_object_utils(ai_core_dwpu_small_random_prog_sequence)
  // Class Constructor
  function new (string name = "ai_core_dwpu_small_random_prog_sequence");
    super.new(name);
  endfunction

  extern virtual task body();

endclass

task ai_core_dwpu_small_random_prog_sequence::body();
  axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
  axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");

  `uvm_info("body", $sformatf("Start small_random_prog sequence body"), UVM_LOW)
    
  `uvm_info("body", $sformatf("Start sending writes"), UVM_LOW)
  //Randomize writes the memory that use small lengths
  for(int i= 0; i<sequence_length; i++) begin
    if(!axi_wr_seq.randomize() with {
      cfg_addr inside {[DWPU_IMEM_ST_ADDR: DWPU_IMEM_ST_ADDR+ ((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8)-(8*100)]}; //address from the beginning of program memory until the max memory -100 positions
      (cfg_addr%8) == 0;
      sequence_length == 'd1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == INCR;
      cfg_data.size inside {[1:3]}; //maximum 3 words to be able to cover the overflow of the request fifos
      foreach (cfg_data[i]) cfg_data[i] == 0;
      back_to_back_en == 1;
    }) `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
    // Start the sequence on the respective sequencer
    axi_wr_seq.start(p_sequencer.cfg_seqr);
  end
  #(1000*`CLK_PERIOD_PS*1ps);

  `uvm_info("body", $sformatf("Start sending reads"), UVM_LOW)
  //Randomize reads to the memory that use small lengths
  for(int i= 0; i<sequence_length; i++) begin
    if(!axi_rd_seq.randomize() with {
      cfg_addr inside {[DWPU_IMEM_ST_ADDR: DWPU_IMEM_ST_ADDR+ ((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8)-(8*100)]}; //address from the beginning of program memory until the max memory -100 positions
      (cfg_addr%8) == 0;
      sequence_length == 'd1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == INCR;
      burst_length inside {[1:3]}; //maximum 3 words to be able to cover the overflow of the request fifos
      back_to_back_en == 1;
    }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
    // Start the sequence on the respective sequencer
    axi_rd_seq.start(p_sequencer.cfg_seqr);
  end
  #(1000*`CLK_PERIOD_PS*1ps);
  

  //Randomize writes the memory that use length equal to 1 to stress as much as possible
  for(int i= 0; i<sequence_length; i++) begin
    if(!axi_wr_seq.randomize() with {
      cfg_addr inside {[DWPU_IMEM_ST_ADDR: DWPU_IMEM_ST_ADDR+ ((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8)-(8*100)]}; //address from the beginning of program memory until the max memory -100 positions
      (cfg_addr%8) == 0;
      sequence_length == 'd1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == INCR;
      cfg_data.size == 1;
      foreach (cfg_data[i]) cfg_data[i] == 0;
      back_to_back_en == 1;
    }) `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
    // Start the sequence on the respective sequencer
    axi_wr_seq.start(p_sequencer.cfg_seqr);
  end
  #(1000*`CLK_PERIOD_PS*1ps);
  
  `uvm_info("body", $sformatf("Start sending reads"), UVM_LOW)
  //Randomize reads to the memory that use length equal to 1 to stress as much as possible
  for(int i= 0; i<sequence_length; i++) begin
    if(!axi_rd_seq.randomize() with {
      cfg_addr inside {[DWPU_IMEM_ST_ADDR: DWPU_IMEM_ST_ADDR+ ((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8)-(8*100)]}; //address from the beginning of program memory until the max memory -100 positions
      (cfg_addr%8) == 0;
      sequence_length == 'd1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == INCR;
      burst_length == 1;
      back_to_back_en == 1;
    }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
    // Start the sequence on the respective sequencer
    axi_rd_seq.start(p_sequencer.cfg_seqr);
  end
  #(1000*`CLK_PERIOD_PS*1ps);

  `uvm_info("body", $sformatf("Finished  small_random_prog sequence body..."), UVM_HIGH)
endtask : body
