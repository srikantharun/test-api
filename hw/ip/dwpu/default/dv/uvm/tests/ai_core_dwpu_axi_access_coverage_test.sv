/**
* The aim of this testcase is to increase the coverage regarding the AXI accesses to DWPU
*/
class ai_core_dwpu_axi_access_coverage_test extends ai_core_dwpu_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_axi_access_coverage_test)

  ai_core_dwpu_cmd_sequence                             cmd_seq;
  ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb   cmd_info_seq;
  uvm_reg_addr_t init_addr;

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
    cmd_seq     = ai_core_dwpu_cmd_sequence::type_id::create("cmd_seq", this);
    cmd_info_seq  = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb::type_id::create("cmd_info_seq", this);

    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);

    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);

    init_addr = env.sequencer.regmodel.cmdblk_ctrl.get_address();
    `uvm_info(get_name(), $sformatf("address = 0x%0x", init_addr), UVM_LOW)
    
    /**Cover csr accesses */
    stimuli_burst_access_cfg_reg();
    stimuli_back2back_addr(init_addr, 0); //without resp delay
    stimuli_back2back_addr(init_addr, 1); //with resp delay
    clear_cmdblk_ctrl();
    /** Cover instruction memory access */
    stimuli_back2back_addr(DWPU_IMEM_ST_ADDR, 0); //without resp delay
    stimuli_back2back_addr(DWPU_IMEM_ST_ADDR, 1); //with resp delay
    stimuli_back2back_addr(DWPU_IMEM_ST_ADDR+((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8), 0); //without resp delay
    stimuli_back2back_addr(DWPU_IMEM_ST_ADDR+((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8), 1); //with resp delay
    stimuli_back2back_addr(DWPU_IMEM_ST_ADDR, 0); //without resp delay
    stimuli_back2back_addr(DWPU_IMEM_ST_ADDR, 1); //with resp delay
    /** Cover cmd fifo accesses */
    stimuli_cmd_fifo(INCR);
    stimuli_cmd_fifo(FIXED);
    stimuli_cmd_fifo_last_position();
    stimuli_cmd_fifo(INCR); //added here for code coverage purpose

    `uvm_info ("run_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask

  task stimuli_burst_access_cfg_reg();
    /** read transaction to csr to verify the burst access to this region */
    if(!axi_rd_seq.randomize() with {
      cfg_addr        == init_addr;
      sequence_length == 'd1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == INCR;
      burst_length == BURST_LENGTH_4;
    }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
    axi_rd_seq.start(env.m_axi_system_env.master[0].sequencer);
    foreach (axi_rd_seq.read_transaction.rresp[i]) begin
      check_resp(resp_type_t'(axi_rd_seq.read_transaction.rresp[i]), OKAY, 0, $sformatf("CMD FIFO (0x%0x) ", axi_rd_seq.cfg_addr+(i*8)));
    end
  endtask : stimuli_burst_access_cfg_reg


  task stimuli_back2back_addr(uvm_reg_addr_t a_addr, bit a_resp_delay_en=0);
    int max_csr_access = 20;
    /** Do back-to-back write and read to csr to toogle the ready signal */
    `uvm_info(get_name(), $sformatf("Start sending back-to-back writes to address 0x%0x", a_addr), UVM_LOW)
    fork //protection to make sure the wait fork works
      begin
        for(int i= 0; i<max_csr_access; i++) begin
          axi_master_write_sequence axi_wr_seq = axi_master_write_sequence::type_id::create($sformatf("axi_wr_seq[%0d]", i));
          if(!axi_wr_seq.randomize() with {
            cfg_addr == a_addr;
            sequence_length == 'd1;
            burst_size == BURST_SIZE_64BIT;
            //make the burst type vary between FIXED and INCR to allow the coverage toggling of burst signal
            if(i%2) {
              burst_type == FIXED;
              cfg_data.size inside {[1:3]}; //maximum 3 words to be able to cover the overflow of the request fifos
            }
            else {
              burst_type == INCR;
              cfg_data.size == 1;
            }
            if(i<max_csr_access-1) {
              back_to_back_en == 1;
              if(a_resp_delay_en) bready_delay_on_back_to_back_en == 1;
            }
          }) `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
          // Start the sequence on the respective sequencer
          if(axi_wr_seq.back_to_back_en) begin
            fork
              axi_wr_seq.start(env.m_axi_system_env.master[0].sequencer);
            join_none
          end
          else begin
            axi_wr_seq.start(env.m_axi_system_env.master[0].sequencer);
          end
        end
        //wait for all write transactions to finish
        wait fork;
      end
    join

    `uvm_info(get_name(), $sformatf("Start sending back-to-back reads to address 0x%0x", a_addr), UVM_LOW)
    fork //protection to make sure the wait fork works
      begin
        for(int i= 0; i<max_csr_access; i++) begin
          axi_master_read_sequence axi_rd_seq = axi_master_read_sequence::type_id::create($sformatf("axi_rd_seq[%0d]", i));
          if(!axi_rd_seq.randomize() with {
            cfg_addr == a_addr;
            sequence_length == 'd1;
            burst_size == BURST_SIZE_64BIT;
            //make the burst type vary between FIXED and INCR to allow the coverage toggling of burst signal
            if(i%2) {
              burst_type == FIXED;
              burst_length inside {[1:3]}; //maximum 3 words to be able to cover the overflow of the request fifos
            }
            else {
              burst_type == INCR;
              burst_length == 1;
            }
            if(i<max_csr_access-1) {
              back_to_back_en == 1;
              if(a_resp_delay_en) rready_delay_on_back_to_back_en == 1;
            }
          }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
          // Start the sequence on the respective sequencer
          if(axi_rd_seq.back_to_back_en) begin
            fork
              axi_rd_seq.start(env.m_axi_system_env.master[0].sequencer);
            join_none
          end
          else begin
            axi_rd_seq.start(env.m_axi_system_env.master[0].sequencer);
          end
        end
        //wait for all read transactions to finish
        wait fork;
      end
    join
  endtask : stimuli_back2back_addr

  task stimuli_cmd_fifo(burst_type_t a_burst_type = INCR);
    bit [AXI_LT_DATA_WIDTH-1:0] cmd_data_da[];

    /** write to command fifo */
    if(!cmd_seq.randomize() with {
      header.format == aic_dp_cmd_gen_pkg::LoopsM3N2;
    }) `uvm_error(get_name, $sformatf("cmd_seq randomization error!"));
    
    //set the base and top addresses for cmd_info_seq randomization
    cmd_info_seq.base=0;
    cmd_info_seq.top=INSTR_MEM_DEPTH-1;
    //randomize command
    if(!cmd_info_seq.randomize() with {
      //set the command to be valid
      valid == 1;
      format == cmd_seq.header.format;
    }) `uvm_error(get_name, "cmd_info_seq randomization error!");

    //set the pointer to command info
    cmd_seq.cmd_info = cmd_info_seq;

    //get the data from the command
    cmd_seq.get_packed_data_from_cmd(cmd_data_da);
    // Randomize the sequence
    `uvm_info(get_name(), $sformatf("Writing and reading to/from cmd fifo (address 0x%0x)", DWPU_CMD_ST_ADDR), UVM_LOW)
    if(!axi_wr_seq.randomize() with {
      cfg_addr        == DWPU_CMD_ST_ADDR;
      sequence_length == 'd1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == a_burst_type;
      cfg_data.size == cmd_data_da.size;
      foreach(cfg_data[i]) {
        cfg_data[i] == cmd_data_da[i];
      }
    }) `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
    // Start the sequence on the respective sequencer
    axi_wr_seq.start(env.m_axi_system_env.master[0].sequencer);
    check_resp(resp_type_t'(axi_wr_seq.write_tran.bresp), OKAY, 1, $sformatf("CMD FIFO position (0x%0x) until (0x%0x) ", axi_wr_seq.cfg_addr, axi_wr_seq.cfg_addr+(axi_wr_seq.cfg_data.size*8)));
    
    /** Read from command fifo */
    if(!axi_rd_seq.randomize() with {
      cfg_addr        == axi_wr_seq.cfg_addr;
      sequence_length == 'd1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == a_burst_type;
      burst_length == BURST_LENGTH_4;
    }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
    axi_rd_seq.start(env.m_axi_system_env.master[0].sequencer);
    foreach (axi_rd_seq.read_transaction.rresp[i]) begin
      check_resp(resp_type_t'(axi_rd_seq.read_transaction.rresp[i]), OKAY, 0, $sformatf("CMD FIFO position (0x%0x) ", axi_rd_seq.cfg_addr+(i*8)));
    end
  endtask : stimuli_cmd_fifo


  task stimuli_cmd_fifo_last_position();
    uvm_status_e status;

    /** set the reset value for CMDBLK_CTRL to make sure that exe_en is equal to 0 */
    env.sequencer.regmodel.cmdblk_ctrl.write(status, 0);
    if(status != UVM_IS_OK) begin
      `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
    end
    /** write to command fifo */
    // Randomize the sequence
    `uvm_info(get_name(), $sformatf("Writing and reading to/from cmd fifo last position (address 0x%0x)", (DWPU_CMD_END_ADDR-7)), UVM_LOW)
    if(!axi_wr_seq.randomize() with {
      cfg_addr        == (DWPU_CMD_END_ADDR-7); //CMD position on the array is 1
      sequence_length == 'd1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == INCR;
      cfg_data.size == 1;
    }) `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
    // Start the sequence on the respective sequencer
    axi_wr_seq.start(env.m_axi_system_env.master[0].sequencer);
    check_resp(resp_type_t'(axi_wr_seq.write_tran.bresp), OKAY, 1, $sformatf("CMD FIFO last position (0x%0x) ", (DWPU_CMD_END_ADDR-7)));
    
    /** Read from command fifo */
    if(!axi_rd_seq.randomize() with {
      cfg_addr        == axi_wr_seq.cfg_addr;
      sequence_length == 'd1;
      burst_size == BURST_SIZE_64BIT;
      burst_type == INCR;
      burst_length == BURST_LENGTH_1;
    }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
    axi_rd_seq.start(env.m_axi_system_env.master[0].sequencer);
    foreach (axi_rd_seq.read_transaction.rresp[i]) begin
      check_resp(resp_type_t'(axi_rd_seq.read_transaction.rresp[i]), SLVERR, 0, $sformatf("CMD FIFO last position (0x%0x) ", (DWPU_CMD_END_ADDR-7)));
    end
  endtask : stimuli_cmd_fifo_last_position

  task clear_cmdblk_ctrl();
    uvm_status_e status;

    /** set the reset value for CMDBLK_CTRL to make sure that exe_en is equal to 0 */
    env.sequencer.regmodel.cmdblk_ctrl.write(status, 0);
    if(status != UVM_IS_OK) begin
      `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
    end
  endtask : clear_cmdblk_ctrl

  virtual function bit check_resp(resp_type_t read_resp, resp_type_t expected_resp, bit wr_n_rd, string info);
    string tag = (wr_n_rd == 1) ? "WRITE" : "READ";
    string resp_var = (wr_n_rd == 1) ? "BRESP" : "RRESP";
    if(read_resp == expected_resp)
      `uvm_info($sformatf("DWPU_%s_REG_COMPARE: PASSED", tag), $sformatf("%s %s = %s", info, resp_var, read_resp.name()), UVM_LOW)
    else
    `uvm_error($sformatf("DWPU_%s_REG_COMPARE: FAILED", tag), $sformatf("%s %s = %s and expected value = %s", info, resp_var, read_resp.name(), expected_resp.name()))
  endfunction : check_resp
endclass : ai_core_dwpu_axi_access_coverage_test

