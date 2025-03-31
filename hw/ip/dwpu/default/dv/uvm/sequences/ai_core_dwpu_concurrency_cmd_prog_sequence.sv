/**
 * Sequence that initializes the program memory from DWPU
 */
class  ai_core_dwpu_concurrency_cmd_prog_sequence extends ai_core_dwpu_base_sequence;
  ai_core_dwpu_csr_config_sequence                      csr_cfg_seq;
  ai_core_dwpu_cmd_sequence                             cmd_seq[];
  ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb   cmd_info_seq[];
  ai_core_dwpu_stream_sequence                          data_seq[];
  ai_core_dwpu_prg_sequence                             prg_seq[];
  axi_master_write_split_sequence                       cmds_in_single_seq;

  int m_max_num_iter = 10;

  int m_in_use_mem_start[int];
  int m_in_use_mem_end[int];
  int m_in_use_mem_index;

  `uvm_object_utils(ai_core_dwpu_concurrency_cmd_prog_sequence)

  // Class Constructor
  function new (string name = "ai_core_dwpu_concurrency_cmd_prog_sequence");
    super.new(name);
  endfunction

  extern virtual task body();
  extern function void add_to_in_use_mem(ai_core_dwpu_cmd_sequence cmd);
  extern function void remove_from_in_use_mem(ai_core_dwpu_cmd_sequence cmd);

endclass

task ai_core_dwpu_concurrency_cmd_prog_sequence::body();
  bit [AXI_LT_DATA_WIDTH-1:0] l_cmd_data_da[];
  `uvm_info("body", $sformatf("Start concurrency command with program sequence..."), UVM_HIGH)

  /** Randomize and call the start of CSR sequence */
  `uvm_do_on(csr_cfg_seq, p_sequencer)

  /** Loop for several commands */
  for(int iter=0; iter < m_max_num_iter; iter++) begin
    /** - create the command, program sequences */
    cmd_seq       = new[cmd_seq.size+1](cmd_seq);
    cmd_info_seq  = new[cmd_info_seq.size+1](cmd_seq);
    prg_seq       = new[prg_seq.size+1](prg_seq);
    data_seq      = new[data_seq.size+1](data_seq);

    cmd_seq[iter]       = ai_core_dwpu_cmd_sequence::type_id::create($sformatf("cmd_seq[%0d]", iter));
    cmd_info_seq[iter]  = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb::type_id::create($sformatf("cmd_info_seq[%0d]", iter));
    prg_seq[iter]       = ai_core_dwpu_prg_sequence::type_id::create($sformatf("prg_seq[%0d]", iter));
    data_seq[iter]      = ai_core_dwpu_stream_sequence::type_id::create($sformatf("data_seq[%0d]", iter));

    /** - randomize command */
    if(!cmd_seq[iter].randomize() with {
      header.format inside {[aic_dp_cmd_gen_pkg::LoopsM1N1:aic_dp_cmd_gen_pkg::LoopsM1N2]}; //at least nested 0 will exist
    }) `uvm_error(get_name, $sformatf("cmd_seq[%0d] randomization error!", iter));
    
    //set the base and top addresses for cmd_info_seq randomization
    cmd_info_seq[iter].base=0;
    cmd_info_seq[iter].top=INSTR_MEM_DEPTH-1;
    //randomize command
    if(!cmd_info_seq[iter].randomize() with {
      //set the command to be valid
      valid == 1;
      format == cmd_seq[iter].header.format;
      
      main_0.iteration inside {[10:20]}; //make sure the main 0 loop takes time, thiVs will help on the concurrency behaviour
      nested_0.iteration inside {[10:20]}; //make sure the nested 0 loop takes time, this will help on the concurrency behaviour
      if(format == aic_dp_cmd_gen_pkg::LoopsM1N2) {
        nested_1.iteration inside {[10:20]}; //make sure the inner1 loop takes time, this will help on the concurrency behaviour
      }
      
      foreach(m_in_use_mem_start[index]) {
        (!(main_0.start inside {[m_in_use_mem_start[index] : m_in_use_mem_end[index]]}));
        (!((main_0.start+main_0.length-1) inside {[m_in_use_mem_start[index] : m_in_use_mem_end[index]]}));

        (!(m_in_use_mem_start[index] inside {[main_0.start : (main_0.start+main_0.length-1)]}));
        (!(m_in_use_mem_end[index] inside {[main_0.start : (main_0.start+main_0.length-1)]}));
      }
    }) `uvm_error(get_name, "cmd_info_seq randomization error!");

    //set the pointer to command info
    cmd_seq[iter].cmd_info = cmd_info_seq[iter];
      
    /** - randomize program command */
    prg_seq[iter].cmd_info = cmd_info_seq[iter];
    if(!prg_seq[iter].randomize()) `uvm_error(get_name, $sformatf("prg_seq[%0d] randomization error!", iter));

    /** - randomize data */
    if(!data_seq[iter].randomize()) `uvm_error(get_name, $sformatf("data_seq[%0d] randomization error!", iter));
    //get necessary number of data based on instructions requests to input data (source param == pop)
    data_seq[iter].set_data_stream_length(prg_seq[iter].get_input_stream_info(cmd_info_seq[iter]));

    //update positions in use on memory
    add_to_in_use_mem(cmd_seq[iter]);
  end
  foreach(cmd_seq[i]) begin
    `uvm_info("body", $sformatf("Packing command %0d", i), UVM_HIGH)
    //get cmd_data into an array
    cmd_seq[i].get_packed_data_from_cmd(l_cmd_data_da);
  end

  /** write the first program in memory to make sure that when command starts, the program in memory is diferent from 0 */
  prg_seq[0].start(p_sequencer.cfg_seqr);
  `uvm_info("body", $sformatf("Finished prg_seq[0] sequence..."), UVM_HIGH)

  /** launch the sequences concurrently but sequential inside of each context (for example, data_seq[0] followed by data_seq[1] and so forward) */
  fork
    begin
      int rnd_clks2wait;
      for(int iter = 1; iter < m_max_num_iter; iter++) begin //this starts at 1 because the prg_seq[0] is already stored in memory
        prg_seq[iter].start(p_sequencer.cfg_seqr);
        std::randomize(rnd_clks2wait) with {rnd_clks2wait inside {[10 : 100]};};
        repeat (rnd_clks2wait) @(posedge p_sequencer.reset_mp.clk);
      end
    end
    begin
      int rnd_clks2wait;
      for(int iter = 0; iter < m_max_num_iter; iter++) begin
        cmd_seq[iter].start(p_sequencer.cfg_seqr);
        std::randomize(rnd_clks2wait) with {rnd_clks2wait inside {[10 : 100]};};
        repeat (rnd_clks2wait) @(posedge p_sequencer.reset_mp.clk);
      end
    end
    begin
      int rnd_clks2wait;
      for(int iter = 0; iter < m_max_num_iter; iter++) begin
        data_seq[iter].start(p_sequencer.in_stream_seqr);
        remove_from_in_use_mem(cmd_seq[iter]);
        std::randomize(rnd_clks2wait) with {rnd_clks2wait inside {[10 : 100]};};
        repeat (rnd_clks2wait) @(posedge p_sequencer.reset_mp.clk);
      end
    end
  join_none
  wait fork;

  //wait a drain time to make sure that all the data comes out from the AXIS output stream
  repeat (5000) @(posedge p_sequencer.reset_mp.clk);

  `uvm_info("body", $sformatf("Finished concurrency command with program sequence..."), UVM_HIGH)
endtask : body


function void ai_core_dwpu_concurrency_cmd_prog_sequence::add_to_in_use_mem(ai_core_dwpu_cmd_sequence cmd);
  m_in_use_mem_start[m_in_use_mem_index] = cmd.cmd_info.get_start(1,0);
  m_in_use_mem_end[m_in_use_mem_index] = cmd.cmd_info.get_end(1,0);
  m_in_use_mem_index++;
endfunction : add_to_in_use_mem


function void ai_core_dwpu_concurrency_cmd_prog_sequence::remove_from_in_use_mem(ai_core_dwpu_cmd_sequence cmd);
  foreach(m_in_use_mem_start[i]) begin
    if(cmd.cmd_info.get_start(1,0) == m_in_use_mem_start[i]) begin
      m_in_use_mem_start.delete(i);
      m_in_use_mem_end.delete(i);
    end
  end
endfunction : remove_from_in_use_mem
