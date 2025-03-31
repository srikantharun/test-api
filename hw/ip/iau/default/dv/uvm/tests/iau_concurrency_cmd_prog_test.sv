// The aim of this test is to test the concurrency of the command write with program execution
class iau_concurrency_cmd_prog_test extends iau_base_test;
  iau_csr_config_sequence csr_cfg_seq;
  /** UVM Component Utility macro */
  `uvm_component_utils(iau_concurrency_cmd_prog_test)
  axi_simple_reset_sequence   rst_seq;
  iau_cmd_descriptor_sequence cmd_seq                 [];
  iau_stream_sequence         data_seq                [];
  iau_prg_sequence            prg_seq                 [];
  int                         m_max_num_iter              = 10;
  int                         m_in_use_mem_start[int];
  int                         m_in_use_mem_end[int];
  int                         m_in_use_mem_index;
  /** Class Constructor */
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void add_to_in_use_mem(iau_cmd_desc_t cmd_info);
    m_in_use_mem_start[m_in_use_mem_index] = cmd_info.loop_start;
    m_in_use_mem_end[m_in_use_mem_index]   = cmd_info.loop_len;
    m_in_use_mem_index++;
  endfunction : add_to_in_use_mem

  function void remove_from_in_use_mem(iau_cmd_desc_t cmd_info);
    foreach (m_in_use_mem_start[i]) begin
      if (cmd_info.loop_start == m_in_use_mem_start[i]) begin
        m_in_use_mem_start.delete(i);
        m_in_use_mem_end.delete(i);
      end
    end
  endfunction : remove_from_in_use_mem

  virtual task run_phase(uvm_phase phase);
    `uvm_info("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms,
                        1); // set the timeoutcsr_cfg_seq = iau_csr_config_sequence::type_id::create("csr_cfg_seq", this);
    csr_cfg_seq = iau_csr_config_sequence::type_id::create("csr_cfg_seq", this);

    if (!csr_cfg_seq.randomize() with {irq_en == 33'h1_FFFF_FFFF;})
      `uvm_fatal("run_phase", "Failed to randomize");
    `uvm_info("run_phase", $sformatf("Writing in CSR.EXEC_EN = 1"), UVM_HIGH)
    `uvm_info("run_phase",
              $sformatf("Writing in CSR.DP_CTRL saturation: %b, signed: %b, ignore_segfault: %b",
                        csr_cfg_seq.sat_op, csr_cfg_seq.signed_op, csr_cfg_seq.ignore_segfault),
              UVM_HIGH)
    csr_cfg_seq.start(env.sequencer);

    for (int iter = 0; iter < m_max_num_iter; iter++) begin
      /** - create the command, program sequences */
      cmd_seq = new[cmd_seq.size + 1] (cmd_seq);
      prg_seq = new[prg_seq.size + 1] (prg_seq);
      data_seq = new[data_seq.size + 1] (data_seq);

      cmd_seq[iter] = iau_cmd_descriptor_sequence::type_id::create($sformatf("cmd_seq[%0d]", iter));
      prg_seq[iter] = iau_prg_sequence::type_id::create($sformatf("prg_seq[%0d]", iter));
      data_seq[iter] = iau_stream_sequence::type_id::create($sformatf("data_seq[%0d]", iter));

      /** - randomize command */
      if (!cmd_seq[iter].randomize() with {
            cmd_seq[iter].cmd.main_0.start == 0;  //to simplify the test
            cmd_seq[iter].cmd.main_0.length == 255;
            cmd_seq[iter].cmd.main_0.iteration == 10;
            cmd_seq[iter].header.format == aic_dp_cmd_gen_pkg::LoopsM1N0; 
          })
        `uvm_error(get_name, $sformatf("cmd_seq[%0d] randomization error!", iter));

      /** - randomize program command */
      //prg_seq[iter].cmd = cmd_seq[iter].cmd;
      if (!prg_seq[iter].randomize() with {
            prg_seq[iter].prog_start_addr == 0;  //to simplify the test
            prg_seq[iter].prog_size == 255;
            prg_seq[iter].prog_iteration == 10;
            prg_seq[iter].set_rfs == 0;
          })
        `uvm_error(get_name, $sformatf("prg_seq[%0d] randomization error!", iter));

      /** - randomize data */
      if (!data_seq[iter].randomize())
        `uvm_error(get_name, $sformatf("data_seq[%0d] randomization error!", iter));
      //get necessary number of data based on instructions requests to input data (source param == pop)
      data_seq[iter].set_data_stream_length(prg_seq[iter].get_input_stream_info());

      //update positions in use on memory
      add_to_in_use_mem(cmd_seq[iter].cmd);
    end
    //foreach(cmd_seq[i]) begin
    //  `uvm_info("body", $sformatf("Packing command %0d", i), UVM_HIGH)
    //  //get cmd_data into an array
    //  cmd_seq[i].get_packed_data_from_cmd(l_cmd_data_da);
    //end

    /** write the first program in memory to make sure that when command starts, the program in memory is diferent from 0 */
    prg_seq[0].start(env.axi_system_env.master[0].sequencer);
    `uvm_info("body", $sformatf("Finished prg_seq[0] sequence..."), UVM_HIGH)

    /** launch the sequences concurrently but sequential inside of each context (for example, data_seq[0] followed by data_seq[1] and so forward) */
    fork
      begin
        int rnd_clks2wait;
        for (
            int iter = 1; iter < m_max_num_iter; iter++
        ) begin  //this starts at 1 because the prg_seq[0] is already stored in memory
          prg_seq[iter].start(env.axi_system_env.master[0].sequencer);
          if(!std::randomize(
              rnd_clks2wait
          ) with {
            rnd_clks2wait inside {[10 : 100]};
          }) `uvm_fatal(get_name, "Randomization Failed!")
          repeat (rnd_clks2wait) @(posedge env.sequencer.reset_mp.clk);
        end
      end
      begin
        int rnd_clks2wait;
        for (int iter = 0; iter < m_max_num_iter; iter++) begin
          cmd_seq[iter].start(env.axi_system_env.master[0].sequencer);
          if(!std::randomize(
              rnd_clks2wait
          ) with {
            rnd_clks2wait inside {[10 : 100]};
          }) `uvm_fatal(get_name, "Randomization Failed!")
          repeat (rnd_clks2wait) @(posedge env.sequencer.reset_mp.clk);
        end
      end
      begin
        int rnd_clks2wait;
        for (int iter = 0; iter < m_max_num_iter; iter++) begin
          data_seq[iter].start(env.axi_system_env.master[1].sequencer);
          remove_from_in_use_mem(cmd_seq[iter].cmd);
          if(!std::randomize(
              rnd_clks2wait
          ) with {
            rnd_clks2wait inside {[10 : 100]};
          }) `uvm_fatal(get_name, "Randomization Failed!")
          repeat (rnd_clks2wait) @(posedge env.sequencer.reset_mp.clk);
        end
      end
    join_none
    wait fork;

    //wait a drain time to make sure that all the data comes out from the AXIS output stream
    repeat (5000) @(posedge env.sequencer.reset_mp.clk);

    `uvm_info("run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : iau_concurrency_cmd_prog_test

