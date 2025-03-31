/**
 Take generated input, output and command files from ICDF
 model implemented in python.
*/
class aic_ls_icdf_stimuli_test extends aic_ls_dmc_cmdb_tc_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(aic_ls_icdf_stimuli_test)

  typedef bit[AIC_LS_ENV_AXI_CFG_ADDR_W-1:0] cfg_addr_t;
  typedef bit[AIC_LS_ENV_AXI_HP_ADDR_W-1:0] hp_addr_t;
  typedef bit[AIC_LS_ENV_AXI_CFG_DATA_W-1:0] cfg_data_t;
  typedef bit[L1_BANK_DATA_WIDTH-1:0] l1_data_t;
  typedef bit[AIC_HT_AXI_DATA_WIDTH/4-1:0] l1_data_quarter_t;
  typedef l1_data_t l1_data_array_t[hp_addr_t];
  
  // Take ICDF's tests path whichs is used in aic_icdf_test
  string ICDF_TEST_PATH = "/hw/dv/icdf/stimuli/ls/extensive_tests/";
  string icdf_cmd       = {"find $REPO_ROOT", ICDF_TEST_PATH, "  -mindepth 1 -maxdepth 1 -type d -exec basename {} \\; > icdf_test.txt"};  // just creates a list of all the paths that should be tested
  //string icdf_cmd       = $sformatf("find $REPO_ROOT%s  -mindepth 1 -maxdepth 1 -type d -exec basename {} \; > icdf_test.txt", ICDF_TEST_PATH );
  string parse_icdf_script = "$REPO_ROOT/hw/ip/aic_ls/default/dv/sim/process_icdf_stimuli.sh";
  string output_folder = "/icdf_stimuli_parsed/";
  string final_parse_cmd;
  hp_addr_t                  m_ag_mem_baseaddr = 'h1800_0000;
  protected string                          m_mem_path_list[L1_SUB_BANKS_PER_BANK];
  string                          m_l1_mem_root_path   = "hdl_top.dut.u_aic_ls.u_l1.u_l1_mem";

  string_queue_t                  path;
  axi_stream_master_file_sequence m_odr_seq, d_odr_seq;
  axi_master_file_sequence        cfg_seq;
  int fd;
  bit st;
  int txn_len = DEFAULT_L1_NUM_BANKS*L1_BANK_DATA_DEPTH; // 4MB of data total, 16 banks * 4096 entries each


  /** Class Constructor */
  function new(string name="aic_ls_icdf_stimuli_test", uvm_component parent);
    super.new(name, parent);
    uvm_top.set_timeout(2ms,1);
  endfunction : new


  function void get_mem_paths(hp_addr_t addr, int index);  // TODO: replace with sf5a write function
    int offset, bank_num;
    int memory_block_size = aic_common_pkg::AIC_PWORD_SIZE/L1_SUB_BANKS_PER_BANK;
    if (addr % memory_block_size != 0) begin
      `uvm_error(get_name(), $sformatf("Address 0x%0x not aligned to PWORD (i.e. %0d bytes)!", addr, memory_block_size))
    end else begin
      bank_num = index%DEFAULT_L1_NUM_BANKS;
      offset = index/DEFAULT_L1_NUM_BANKS;
      // DEBUG
      // `uvm_info(get_name(), $sformatf("DBG: addr: 0x%0x m_l1_full_start_addr: 0x%0x m_pword_size: %0d m_l1_num_banks: %0d", addr, m_env_cfg_h.m_l1_full_start_addr, m_env_cfg_h.m_pword_size, m_env_cfg_h.m_l1_num_banks), UVM_LOW)
      // `uvm_info(get_name(), $sformatf("DBG: L1 Offset: 0x%0x Bank: %0d Index: %0d", (addr - m_env_cfg_h.m_l1_full_start_addr), bank_num, offset), UVM_LOW)
    end
  
  `ifndef TARGET_DFT
      foreach (m_mem_path_list[i]) begin
        m_mem_path_list[i] = $sformatf("%s.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", m_l1_mem_root_path, i, bank_num, offset);
      end
  `else
      foreach (m_mem_path_list[i]) begin
        m_mem_path_list[i] = $sformatf("%s.\\g_sbank[%0d].u_sub_bank .\\g_mini_bank[%0d].u_mini_bank .\\g_macro[0].u_macro .u_macro.memory_q[%0d]", m_l1_mem_root_path, i, bank_num, offset);
      end
  `endif
  endfunction: get_mem_paths

  function l1_data_array_t read_l1_data_file(string output_folder, string output_filename);
    string file_path;
    hp_addr_t addr;
    l1_data_t data;
    l1_data_array_t data_q;
    bit write_type;
    int file;

    file_path = $sformatf("%s/%s.txt", output_folder, output_filename);
    file = $fopen(file_path, "r");
    if (!file) begin
      `uvm_fatal(get_name(), $sformatf("l1 load instructions not found: %s", file_path));
    end
      /** Until the end of the file read the data */
    while (!$feof(file)) begin
      $fscanf(file, "%b %h %h", write_type, addr, data);
      data_q[addr] = data;
      `uvm_info(get_name(), $sformatf("READ from %s: write_data_q[0x%0x] = 0x%0x", file_path, addr, data), UVM_MEDIUM);
    end
    $fclose(file);
    return data_q;
  endfunction : read_l1_data_file

  virtual task write_to_l1(string output_folder);
    hp_addr_t current_addr;
    l1_data_t current_data;
    l1_data_array_t write_data_q;
    
    `uvm_info(get_name(), $sformatf("write_to_l1() started! Start Address: 0x%0x txn_len: %0d", m_ag_mem_baseaddr,txn_len), UVM_LOW)
    write_data_q = read_l1_data_file(output_folder, "l1_mem_in");
    for (int i = 0; i < txn_len; i++) begin
      // Address and data
      current_addr = m_ag_mem_baseaddr + i*'d64;
      get_mem_paths(current_addr, i);
      if (write_data_q.exists(current_addr)) begin
        current_data = write_data_q[current_addr];
        `uvm_info(get_name(), $sformatf("Backdoor WR to L1 from file. %0d/%0d Address = 0x%0x Data = 0x%0x", i,txn_len, current_addr, current_data), UVM_LOW)
        
        foreach (m_mem_path_list[indx]) begin
          if (!uvm_hdl_deposit(m_mem_path_list[indx], write_data_q[current_addr][L1_SUB_BANK_WIDTH-1:0])) begin
            `uvm_fatal(get_name(), $sformatf("Failed to deposit HDL path! %s", m_mem_path_list[indx]))
          end
          write_data_q[current_addr] = write_data_q[current_addr] >> L1_SUB_BANK_WIDTH;
        end
        write_data_q.delete(current_addr); // remove entry
      end else begin
        if (i%1000 == 0) begin
          `uvm_info(get_name(), $sformatf("Backdoor WR to L1 Loop %0d/%0d Address = 0x%0x Data = 0x%0x", i,txn_len, current_addr, 0), UVM_MEDIUM)
        end
        foreach (m_mem_path_list[indx]) begin
          if (!uvm_hdl_deposit(m_mem_path_list[indx], 0)) begin
            `uvm_fatal(get_name(), $sformatf("Failed to deposit HDL path! %s", m_mem_path_list[indx]))
          end
        end
      end
    end // end for
    if (write_data_q.num() > 0) begin
      `uvm_fatal(get_name(), $sformatf("Expected write_data_q to empty, but it still has %d entries!",write_data_q.num()))
      return;
    end
    `uvm_info(get_name(), $sformatf("write_to_l1() done! End Address: 0x%0x", current_addr), UVM_LOW)
  endtask: write_to_l1

  /* simple function to check memory values at the end of the test. */
  virtual task check_l1_memory(string output_folder);
    //hp_addr_t current_addr;
    int index;
    l1_data_t expected_data;
    l1_data_t actual_data;
    l1_data_quarter_t hdl_read_part[L1_SUB_BANKS_PER_BANK];
    l1_data_array_t read_data_q;
    
    `uvm_info(get_name(), $sformatf("check_l1_memory() started! Start Address: 0x%0x txn_len: %0d", m_ag_mem_baseaddr,txn_len), UVM_LOW)
    read_data_q = read_l1_data_file(output_folder, "l1_mem_out");

    foreach(read_data_q[current_addr]) begin
      index = (current_addr - m_ag_mem_baseaddr)/'d64;
      get_mem_paths(current_addr, index);
      foreach (m_mem_path_list[i]) begin
        if (!uvm_hdl_read(m_mem_path_list[i], hdl_read_part[i])) begin
          `uvm_fatal(get_name(), $sformatf("Failed to read HDL path! %s", m_mem_path_list[i]))
        end
      end
      for (int i = L1_SUB_BANKS_PER_BANK-1; i >= 0; i--) begin
        actual_data = {actual_data << AIC_HT_AXI_DATA_WIDTH/4 | hdl_read_part[i]};
      end
      expected_data = read_data_q[current_addr];
      if (actual_data != expected_data) begin
        `uvm_fatal(get_name(), $sformatf("L1 data at end of test doesn't match for index %d: address 0x%x.\n Expected data: 0x%0x \n Actual data  : 0x%0x", index, current_addr, expected_data,actual_data) )
      end
    end
    `uvm_info(get_name(), $sformatf("check_l1_memory() done!"), UVM_LOW)
  endtask : check_l1_memory

  virtual function void build_phase(uvm_phase phase);

    `uvm_info(get_name(), "Entered...", UVM_LOW)

    super.build_phase(phase);

    //$system("rm icdf_test.txt"); writing to a file in linux will overwrite the old contents anyways
    `uvm_info(get_name(), $sformatf("running %s", icdf_cmd), UVM_LOW)
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

    m_odr_seq  = axi_stream_master_file_sequence::type_id::create("m_odr_seq", this);
    d_odr_seq = axi_stream_master_file_sequence::type_id::create("d_odr_seq", this);
    cfg_seq   = axi_master_file_sequence::type_id::create("cfg_seq", this);

    /** Set ICDF input data and command files to the sequences */
    uvm_config_db#(string)::set(this, "m_env.m_axi_system_env.master[0].sequencer.cfg_seq", "filename", "ls_cmd");
    uvm_config_db#(string)::set(this, "m_env.m_axi_system_env.master[2].sequencer.m_odr_seq", "filename", "m_odr_in");
    uvm_config_db#(string)::set(this, "m_env.m_axi_system_env.master[3].sequencer.d_odr_seq", "filename", "d_odr_in");

    /** Set ICDF expected output data to axi_scoreboard */
    uvm_config_db#(string)::set(this, "m_env.m_m_ifd0_scb", "output_filename", "m_ifd0_out");
    uvm_config_db#(string)::set(this, "m_env.m_m_ifd1_scb", "output_filename", "m_ifd1_out");
    uvm_config_db#(string)::set(this, "m_env.m_m_ifd2_scb", "output_filename", "m_ifd2_out");
    uvm_config_db#(string)::set(this, "m_env.m_m_ifdw_scb", "output_filename", "m_ifdw_out");
    uvm_config_db#(string)::set(this, "m_env.m_d_ifd0_scb", "output_filename", "d_ifd0_out");
    uvm_config_db#(string)::set(this, "m_env.m_d_ifd1_scb", "output_filename", "d_ifd1_out");

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

  virtual task test_seq();
    string full_path;
    string delete_dir;
    `uvm_info(get_name(), "Start of test", UVM_LOW)

    foreach (path[i]) begin  // iterate through all of the tests
      full_path = $sformatf("$REPO_ROOT%s%s", ICDF_TEST_PATH, path[i]);
      output_folder = $sformatf("%s_output", path[i]);
      uvm_config_db#(string)::set(null, "*", "path", {output_folder, "/"});
      `uvm_info(get_name, $sformatf("\nExecuting test %0d of %0d : %s", i+1, path.size(), path[i]), UVM_LOW)
      final_parse_cmd = $sformatf("%s %s %s",parse_icdf_script, full_path, output_folder);
      `uvm_info(get_name, $sformatf("Parsing test: %s", final_parse_cmd), UVM_MEDIUM)
      $system(final_parse_cmd);

      // fill l1 with data
      write_to_l1(output_folder);  // every new test, we rewrite l1 with data
      
      fork  // run all master sequences. if m_odr/d_odr aren't present, the will just close and not continue
        cfg_seq.start(m_env.m_axi_system_env.master[0].sequencer);
        m_odr_seq.start(m_env.m_axi_system_env.master[2].sequencer);
        d_odr_seq.start(m_env.m_axi_system_env.master[3].sequencer);
      join

      // at the end of the test, compare l1 memory to expected
      check_l1_memory(output_folder); // at the end of the test, make sure l1 mem is same as ICDF stimuli expects

      delete_dir = $sformatf("rm -rf %s", output_folder); // delete leftovers
      $system(delete_dir);

    end
    
    repeat (20) @(posedge m_env.m_axi_system_env.vif.common_aclk);
    `uvm_info(get_name(), "End of test", UVM_LOW)
  endtask

endclass

