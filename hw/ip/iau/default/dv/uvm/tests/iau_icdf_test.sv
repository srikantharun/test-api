/** Master file sequence using only 16 bits of address */
class axi_master_file_sequence_16b_addr extends svt_axi_master_base_sequence;

  /** UVM Object Utility macro */
  `uvm_object_utils(axi_master_file_sequence_16b_addr)

  /** Class Constructor */
  function new(string name="axi_master_file_sequence_16b_addr");
    super.new(name);
  endfunction

  virtual function void trunc_addr(ref logic [31:0] address);
    address = address[15:0];
  endfunction : trunc_addr

endclass : axi_master_file_sequence_16b_addr

/**
 Take generated input, output and command files from ICDF
 model implemented in python.
*/
class iau_icdf_test extends iau_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(iau_icdf_test)

  // Take ICDF's tests path whichs is used in iau_icdf_test
  string ICDF_TEST_PATH = $test$plusargs("ICDF_EXTENSIVE_TEST") ? "/hw/dv/icdf/stimuli/iau/extensive_tests/" : "/hw/dv/icdf/stimuli/iau/quick_tests/";
  string icdf_cmd       = $sformatf("ls -d -1 \"$REPO_ROOT%s\"**\/ > icdf_test.txt", ICDF_TEST_PATH );

  string_queue_t                    path;
  axi_stream_master_file_sequence   data_seq;
  axi_master_file_sequence_16b_addr cfg_seq;
  axi_simple_reset_sequence         rst_seq;
  int fd;
  bit st;


  /** Class Constructor */
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase);

    `uvm_info("build_phase", "Entered...", UVM_LOW)

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
    cfg_seq  = axi_master_file_sequence_16b_addr::type_id::create("cfg_seq", this);
    rst_seq  = axi_simple_reset_sequence::type_id::create("rst_seq", this);

    /** Set ICDF input data and command files to the sequences */
    uvm_config_db#(string)::set(this, "env.axi_system_env.master[1].sequencer.data_seq", "filename", "iau_in0");
    uvm_config_db#(string)::set(this, "env.axi_system_env.master[0].sequencer.cfg_seq", "filename", "iau_cmd");
    /** Set ICDF expected output data to axi_scoreboard */
    uvm_config_db#(string)::set(null, "*", "output_filename", "iau_out0");

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1);  // set the timeout

    foreach (path[i]) begin
      `uvm_info(get_name, $sformatf("Executing test %0d of %0d : %s", i+1, path.size(), path[i]), UVM_LOW)
      uvm_config_db#(string)::set(this, "uvm_test_top.data_seq", "path", path[i]);
      uvm_config_db#(string)::set(this, "uvm_test_top.cfg_seq", "path", path[i]);
      /** Pass info for the output checker scoreboard */
      uvm_config_db#(string)::set(null, "*", "path", path[i]);

      fork
        cfg_seq.start(env.axi_system_env.master[0].sequencer);
        data_seq.start(env.axi_system_env.master[1].sequencer);
      join
      
      check_exec_done();

      repeat (100) @(posedge env.axi_system_env.vif.common_aclk);
    end
    phase.drop_objection(this);
  endtask


  //wait for idle = 1 : program is done
  task check_exec_done();
    bit [63:0]   data;
    uvm_status_e status;

    while (|data[1:0]) begin // IDLE state == 0
      repeat (20) @(posedge env.axi_system_env.vif.common_aclk);
      env.regmodel.cmdblk_status.read(status, data);
    end
  endtask




endclass

