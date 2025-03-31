// AI CORE DWPU environment configuration class for icdf testcase
class ai_core_dwpu_env_cfg_icdf extends ai_core_dwpu_env_cfg;

  `uvm_object_utils(ai_core_dwpu_env_cfg_icdf)

  /** Class Constructor */
  function new(string name = "ai_core_dwpu_env_cfg_icdf");
    super.new(name);
    has_scoreboard = 0;
    has_scoreboard_token = 0;
    has_coverage = 0;
  endfunction : new

endclass : ai_core_dwpu_env_cfg_icdf


// AI CORE DWPU environment class for icdf testcase
class ai_core_dwpu_env_icdf extends ai_core_dwpu_env;

  /** ICDF Test Scoreboard */
  axi_icdf_scoreboard     axi_icdf_scb;
  
  `uvm_component_utils(ai_core_dwpu_env_icdf)
  /** Class Constructor */
  function new(string name = "ai_core_dwpu_env_icdf", uvm_component parent = null);
    super.new(name, parent);
    //set icdf test enable variable to disable normal scoreboard
    icdf_test_en=1;
  endfunction : new
  
  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    
    super.build_phase(phase);
    
    //create axi_icdf scoreboard
    axi_icdf_scb = axi_icdf_scoreboard::type_id::create("axi_icdf_scb", this);
  endfunction : build_phase
  
  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)

    super.connect_phase(phase);
    
    //connect output stream AXI slave monitor to axi icdf scoreboard port
    m_axi_system_env.slave[0].monitor.item_observed_port.connect(axi_icdf_scb.item_observed_out_stream_export);
  endfunction : connect_phase
  
  virtual function bit is_output_data_consumed();
    return axi_icdf_scb.is_output_data_consumed();
  endfunction : is_output_data_consumed
endclass : ai_core_dwpu_env_icdf

/**
 Take generated input, output and command files from ICDF
 model implemented in python.
*/
class ai_core_dwpu_icdf_test extends ai_core_dwpu_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(ai_core_dwpu_icdf_test)

  // Take ICDF's tests path whichs is used in ai_core_dwpu_icdf_test
  string ICDF_TEST_PATH = $test$plusargs("ICDF_EXTENSIVE_TEST") ? "/hw/dv/icdf/stimuli/dwpu/extensive_tests/" : "/hw/dv/icdf/stimuli/dwpu/quick_tests/";
  string icdf_cmd       = $sformatf("ls -d -1 \"$REPO_ROOT%s\"**\/ > icdf_test.txt", ICDF_TEST_PATH );
  string_queue_t                  path;
  axi_stream_master_file_sequence data_seq;
  axi_master_file_sequence	  cfg_seq;
  axi_simple_reset_sequence       rst_seq;
  int fd;
  bit st;
  string cmd_filename = "dwpu_cmd";
  string input_filename = "dwpu_stream_d_ifd_0_to_d_dwpu";
  string output_filename = "dwpu_stream_d_dwpu_to_d_iau";


  /** Class Constructor */
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase);

    `uvm_info("build_phase", "Entered...", UVM_LOW)
    
    /** Factory override of the environment with icdf scoreboard instanciated */
    set_type_override_by_type(ai_core_dwpu_env::get_type(), ai_core_dwpu_env_icdf::get_type());
    set_type_override_by_type(ai_core_dwpu_env_cfg::get_type(), ai_core_dwpu_env_cfg_icdf::get_type());

    super.build_phase(phase);

    $system("rm icdf_test.txt");
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

    data_seq = axi_stream_master_file_sequence::type_id::create("data_seq", this);
    cfg_seq  = axi_master_file_sequence::type_id::create("cfg_seq", this);
    rst_seq  = axi_simple_reset_sequence::type_id::create("rst_seq", this);

    /** Set ICDF input data and command files to the sequences */
    uvm_config_db#(string)::set(this, "env.m_axi_system_env.master[1].sequencer.data_seq", "filename", input_filename);
    uvm_config_db#(string)::set(this, "env.m_axi_system_env.master[0].sequencer.cfg_seq", "filename", cmd_filename);
    /** Set ICDF expected output data to axi_scoreboard */
    uvm_config_db#(string)::set(null, "*", "output_filename", output_filename);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase
  
  task wait_output_data_is_consumed(int num_cycles=50);
    bit data_is_consumed;
    //while icdf scoreboard does not inform that data was consumed on the output stream, wait.
    data_is_consumed = env.is_output_data_consumed();
    while (!data_is_consumed) begin
      repeat(num_cycles) @(posedge env.m_axi_system_env.vif.common_aclk);
      data_is_consumed = env.is_output_data_consumed();
      `uvm_info ("wait_output_data_is_consumed", $sformatf("Checking is_output_data_consumed. Value: %0d", data_is_consumed), UVM_LOW)
    end
    `uvm_info ("wait_output_data_is_consumed", $sformatf("Data was fully consumed"), UVM_LOW)
  endtask


  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    uvm_top.set_timeout(3ms, 1);  // set the timeout

    if(path.size == 0)
      `uvm_fatal("body", $sformatf("No tests were found into ICDF folder. ICDF path = %s", ICDF_TEST_PATH));

    foreach (path[i]) begin
      `uvm_info(get_name, $sformatf("Executing test %0d of %0d : %s", i+1, path.size(), path[i]), UVM_LOW)
      uvm_config_db#(string)::set(this, "uvm_test_top.data_seq", "path", path[i]);
      uvm_config_db#(string)::set(this, "uvm_test_top.cfg_seq", "path", path[i]);
      /** Pass info for the output checker scoreboard */
      uvm_config_db#(string)::set(null, "*", "path", path[i]);

      fork
        cfg_seq.start(env.m_axi_system_env.master[0].sequencer);
        data_seq.start(env.m_axi_system_env.master[1].sequencer);
      join
      
      check_exec_done(0); //call check_exex_done with number of cycles to wait equal to 0

      //if the output file exists, then wait until all data is compared
      if($fopen({path[i],output_filename,".txt"}, "r")) begin
        //wait until output data was fully consumed by the scoreboard
        wait_output_data_is_consumed(50);
      end
    end
    phase.drop_objection(this);
  endtask

endclass

