/**
 * Sequence that initializes the program memory from DWPU
 */
class  ai_core_dwpu_initialize_prog_sequence extends ai_core_dwpu_base_sequence;
  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;

  `uvm_object_utils(ai_core_dwpu_initialize_prog_sequence)

  // Class Constructor
  function new (string name = "ai_core_dwpu_initialize_prog_sequence");
    super.new(name);
  endfunction

  extern virtual task body();

endclass

task ai_core_dwpu_initialize_prog_sequence::body();
  `uvm_info("body", $sformatf("Start not addressable csr sequence body..."), UVM_HIGH)
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");

    `uvm_info("body", $sformatf("Initialize via frontdoor instruction memory size = %0d", INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS), UVM_LOW)

    //write the memory
    // Randomize the sequence
    if(!axi_wr_seq.randomize() with {
      cfg_addr        == DWPU_IMEM_ST_ADDR;
      sequence_length == 'd1;
      split_burst == 1;
      incr_addr_between_bursts ==1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == INCR;
      cfg_data.size == (INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS);
      foreach (cfg_data[i]) cfg_data[i] == 0;
      back_to_back_en == 1;
    }) `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
    // Start the sequence on the respective sequencer
    axi_wr_seq.start(p_sequencer.cfg_seqr);
    #(3000*`CLK_PERIOD_PS*1ps);
    
    //read the memory
    // Randomize the sequence
    if(!axi_rd_seq.randomize() with {
      cfg_addr        == DWPU_IMEM_ST_ADDR;
      sequence_length == 'd1;
      split_burst == 1;
      incr_addr_between_bursts ==1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == INCR;
      burst_length == (INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS);
      back_to_back_en == 1;
    }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
    // Start the sequence on the respective sequencer
    axi_rd_seq.start(p_sequencer.cfg_seqr);
    #(3000*`CLK_PERIOD_PS*1ps);

  `uvm_info("body", $sformatf("Finished not addressable csr sequence body..."), UVM_HIGH)
endtask : body
