/**
 Take generated input, output and command files from ICDF
 model implemented in python.
*/
class ai_core_mvm_icdf_test extends ai_core_mvm_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(ai_core_mvm_icdf_test)

  // Take ICDF's tests path whichs is used in ai_core_mvm_icdf_test
  string ICDF_TEST_PATH = $test$plusargs("ICDF_EXTENSIVE_TEST") ? "/hw/dv/icdf/stimuli/mvm/extensive_tests/" : "/hw/dv/icdf/stimuli/mvm/quick_tests/";
  string icdf_cmd       = $sformatf("ls -d -1 \"$REPO_ROOT%s\"**\/ > icdf_test.txt", ICDF_TEST_PATH );

  string_queue_t                  path;
  axi_stream_master_file_sequence data_seq,data1_seq,data2_seq;
  axi_master_file_sequence        cfg_seq;
  axi_simple_reset_sequence       rst_seq;
  int fd;
  bit st;
  int file;


  /** Class Constructor */
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase);

    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);
   
    //axi_icdf scorebaord is enabled
    m_env_cfg.has_scoreboard=0;

    file = $fopen("icdf_test.txt", "r");
    if (file != 0) begin
      // File exists, so close it and remove
      $fclose(file);
      // Use $system to remove the file
      $system("rm icdf_test.txt");
    end 
    $system(icdf_cmd);

    /** Define the test DIR */
    fd = $fopen("icdf_test.txt", "r");
    if (!fd)
      `uvm_fatal("body", "icdf_text.txt not found");

    while (!$feof(fd)) begin
      string p_str;
      st = $fscanf(fd, "%s", p_str);
      path.push_back(p_str);
    end
    $fclose(fd);

    //fscanf reads a empty last line, tried better approaches but didn't worked
    //solution is remove last line
    path.delete(path.size-1);
 
    data_seq  = axi_stream_master_file_sequence::type_id::create("data_seq", this);
    data1_seq = axi_stream_master_file_sequence::type_id::create("data1_seq", this);
    data2_seq = axi_stream_master_file_sequence::type_id::create("data2_seq", this);
    cfg_seq   = axi_master_file_sequence::type_id::create("cfg_seq", this);
    rst_seq   = axi_simple_reset_sequence::type_id::create("rst_seq", this);

    /** Set ICDF input data and command files to the sequences */
    uvm_config_db#(string)::set(this, "env.axi_system_env.master[0].sequencer.cfg_seq", "filename", "mvm_cmd");
    uvm_config_db#(string)::set(this, "env.axi_system_env.master[1].sequencer.data_seq", "filename", "mvm_stream_m_ifd_w_to_m_mvmprg");
    uvm_config_db#(string)::set(this, "env.axi_system_env.master[2].sequencer.data1_seq", "filename", "mvm_stream_m_ifd_0_to_m_mvmexe");
    /** Set ICDF expected output data to axi_scoreboard */
    uvm_config_db#(string)::set(null, "*", "output_filename", "mvm_stream_m_mvmexe_to_m_iau");

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1);  // set the timeout

    foreach (path[i]) begin
      `uvm_info(get_name, $sformatf("Executing test %0d of %0d : %s", i+1, path.size(), path[i]), UVM_LOW)
      uvm_config_db#(string)::set(this, "uvm_test_top.data_seq", "path", path[i]);
      uvm_config_db#(string)::set(this, "uvm_test_top.data2_seq", "path", path[i]);
      uvm_config_db#(string)::set(this, "uvm_test_top.cfg_seq", "path", path[i]);
      /** Pass info for the output checker scoreboard */
      uvm_config_db#(string)::set(null, "*", "path", path[i]);

      fork
        cfg_seq.start(env.axi_system_env.master[0].sequencer);
        data_seq.start(env.axi_system_env.master[1].sequencer);
        data1_seq.start(env.axi_system_env.master[2].sequencer);
        //currently stimulus for IFD2 is not available 
        //data2_seq.start(env.axi_system_env.master[3].sequencer);
      join
      
      check_exec_done();

      repeat (100) @(posedge mvm_if.clk);
    end
    phase.drop_objection(this);
  endtask


  //wait for idle = 1 : program is done
  task check_exec_done();
    bit [63:0]   data;
    uvm_status_e status;
    data = ~0;

    while (|data[1:0]) begin // IDLE state == 0
      repeat (20) @(posedge mvm_if.clk);
      env.mvm_regmodel.m_mvmprg_regmod.cmdblk_status.read(status, data);
    end
  endtask

endclass

