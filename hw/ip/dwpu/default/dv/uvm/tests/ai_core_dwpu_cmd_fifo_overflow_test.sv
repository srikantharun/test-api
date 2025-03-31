/** Token sequence that make sure that delay of token interface is huge enough
* to create the scenario of having tvalid = 1 and tready = 0 on dwpu command fifo.
*/
class token_agent_huge_delay_seq_item extends token_agent_seq_item;

  constraint c_huge_delay {
    m_bv_delay inside {[100:1000]};
  }
  constraint c_huge_delay_dist {
    m_bv_delay dist {
      [100:700] :/ 10,
      [700:1000] :/ 90
    };
  }

  `uvm_object_utils(token_agent_huge_delay_seq_item)

  function new(string name = "token_agent_huge_delay_seq_item");
    super.new(name);
    `uvm_info ("run_phase", $sformatf("New from token_agent_huge_delay_seq_item"), UVM_HIGH)

  endfunction

endclass : token_agent_huge_delay_seq_item

/**
* The aim of this test is to reach the cmd fifo full situation where the commands after the full are dropped (not used)
* Are created data and program sequence arrays with length of AIC_GEN_CMDB_CMD_FIFO_DEPTH
* Is created a command sequence array with length of AIC_GEN_CMDB_CMD_FIFO_DEPTH+1
* Randomize all the sequences. It was necessary to constraint the size and initial address for each program to make sure
*it was possible to load all of them at the same time to memory without having overlapping.
* Write all the commands to the cmd fifo
* Write all the programs to the memory
* Write the registers (CSR) with EXEC_EN equal to 1 to start executing the commands
* Send the data for each command/program.
* Wait for DWPU to be on idle state
* Reset DWPU
* Restart from point "Randomize all the sequences. ..." till the number of iterations "max_iter" to be reached
*/
class ai_core_dwpu_cmd_fifo_overflow_test extends ai_core_dwpu_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_cmd_fifo_overflow_test)

  axi_simple_reset_sequence                             rst_seq;
  ai_core_dwpu_csr_config_sequence                      csr_cfg_seq;
  ai_core_dwpu_cmd_sequence                             cmd_seq[];
  ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb   cmd_info_seq[];
  ai_core_dwpu_stream_sequence                          data_seq[];
  ai_core_dwpu_prg_sequence                             prg_seq[];
  token_agent_cons_sequence                             tok_cons_seq[];
  token_agent_prod_sequence                             tok_prod_seq[];
  axi_master_write_split_sequence                       write_split_seq;

  int max_iter = 6;

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void set_type_override_callback();
    /** Factory override of the master transaction object */
    set_type_override_by_type (token_agent_seq_item::get_type(), token_agent_huge_delay_seq_item::get_type());
  endfunction : set_type_override_callback

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)

    /** function to overide any class if we need */
    set_type_override_callback();

    super.build_phase(phase);

    rst_seq       = axi_simple_reset_sequence::type_id::create("rst_seq", this);
    data_seq      = new[aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH];
    prg_seq       = new[aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH];
    tok_cons_seq  = new[aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH];
    tok_prod_seq  = new[aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH];
    cmd_seq       = new[aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH+1];
    cmd_info_seq  = new[aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH+1];

    for (int i=0; i<aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH; i++) begin
      data_seq[i]     = ai_core_dwpu_stream_sequence::type_id::create($sformatf("data_seq[%0d]", i), this);
      prg_seq[i]      = ai_core_dwpu_prg_sequence::type_id::create($sformatf("prg_seq[%0d]", i), this);
      tok_cons_seq[i] = token_agent_cons_sequence::type_id::create($sformatf("tok_cons_seq[%0d]", i), this);
      tok_prod_seq[i] = token_agent_prod_sequence::type_id::create($sformatf("tok_prod_seq[%0d]", i), this);
    end
    for (int i=0; i<aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH+2; i++) begin
      cmd_seq[i]      = ai_core_dwpu_cmd_sequence::type_id::create($sformatf("cmd_seq[%0d]", i), this);
      cmd_info_seq[i] = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb::type_id::create($sformatf("cmd_info_seq[%0d]", i), this);
    end
    `uvm_info ("build_phase", $sformatf("Size of cmd_seq.size = %0d", cmd_seq.size()), UVM_HIGH)
    csr_cfg_seq = ai_core_dwpu_csr_config_sequence::type_id::create("csr_cfg_seq", this);

    /** create sequence from type axi_master_write_split_sequence */
    write_split_seq = axi_master_write_split_sequence::type_id::create($sformatf("write_split_seq"));

    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction : build_phase


  virtual function void randomize_cmd_seq(ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb  cmd_info_seq[], ai_core_dwpu_cmd_sequence cmd_seq[], int iter);
    /** randomize the commands
     * It was necessary to constraint the start and the length of the programs to make sure that all the programs could be loaded for
     * memory at the same time without overrides between them.
     */
    foreach (cmd_seq[i]) begin
      //randomize the commands (one more than the maximum number of FIFO depth)
      if(!cmd_seq[i].randomize() with {
        enable_tokens == 1;
        
        //constraint the format to be only inside M1N0, M1N1, M2N0 and Bypass to make sure that each program fits into the command fifo width which is 3 words including header
        //see https://git.axelera.ai/prod/europa/-/issues/1890
        header.format inside {aic_dp_cmd_gen_pkg::LoopsM1N0, aic_dp_cmd_gen_pkg::LoopsM1N1, aic_dp_cmd_gen_pkg::LoopsM2N0, aic_dp_cmd_gen_pkg::Bypass};
        
        //make sure that tokens is active for all commands and the full of token fifos is achieved (only on half of the iterations)
        if(iter%2) {
          header.token_cons == 1;
          header.token_prod == 3;
        }
      }) `uvm_error(get_name, $sformatf("cmd_seq[%0d] randomization error!", i));
    end
        
    foreach (cmd_info_seq[i]) begin
      //set the base and top addresses for cmd_info_seq randomization
      cmd_info_seq[i].base=0;
      cmd_info_seq[i].top=INSTR_MEM_DEPTH-1;
      if(!cmd_info_seq[i].randomize() with {
        //set the command to be valid
        valid == 1;
        format == cmd_seq[i].header.format;
       
        //at least it has a main_0
        main_0.length       inside {[1:2]};
        main_0.iteration    inside {[1:2]};
       
        main_1.length       inside {[0:2]};
        main_1.iteration    inside {[0:2]};
        
        nested_0.iteration  inside {[0:2]};
        nested_1.iteration  inside {[0:2]};

        //Make sure that the start of the current program is located after the previous program with a maximum of 10 address positions of difference.
        //This is necessary to help the randomization to complete successfully and do not overwrite programs
        //
        //If it the first command does not need to take into account the previous command on the randomization
        if (i==0) {
          main_0.start inside {[0:20]};
          if(format >= aic_dp_cmd_gen_pkg::LoopsM2N0) {
            main_1.start inside {[main_0.start : main_0.start+50]};
          }
        }
        //if it not the first command
        else {
          if(cmd_info_seq[i-1].format >= aic_dp_cmd_gen_pkg::LoopsM2N0) {
            main_0.start inside {[ (cmd_info_seq[i-1].main_1.start + cmd_info_seq[i-1].main_1.length +1) : (cmd_info_seq[i-1].main_1.start + cmd_info_seq[i-1].main_1.length +10)]};
            if(format >= aic_dp_cmd_gen_pkg::LoopsM2N0){
              main_1.start inside {[ main_0.start : main_0.start+10]};
            }
          }
          else {
            main_0.start inside {[ (cmd_info_seq[i-1].main_0.start + cmd_info_seq[i-1].main_0.length +1) : cmd_info_seq[i-1].main_0.start + cmd_info_seq[i-1].main_0.length + 10]};
            if(format >= aic_dp_cmd_gen_pkg::LoopsM2N0) {
              main_1.start inside {[ main_0.start : main_0.start+10]};
            }
          }
        }
      }) `uvm_error(get_name, $sformatf("cmd_info_seq[%0d] randomization error!", i));
    
      //set the pointer to command info
      cmd_seq[i].cmd_info = cmd_info_seq[i];
    end
  endfunction : randomize_cmd_seq

  virtual task run_phase(uvm_phase phase);
    ai_core_dp_cmd_gen_uvm_pkg::data_stream_cfg_t data_stream_len;

    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    for (int iter = 1; iter <= max_iter; iter++) begin
      bit [AXI_LT_DATA_WIDTH-1:0] l_cmd_data_da[];
      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_LOW)

      //randomize the command sequences array
      randomize_cmd_seq(cmd_info_seq, cmd_seq, iter);

      foreach (prg_seq[i]) begin
        //set command info to program sequence
        prg_seq[i].cmd_info      = cmd_info_seq[i];
        //randomize the program for each command
        if(!prg_seq[i].randomize()) `uvm_error(get_name, $sformatf("prg_seq[%0d] randomization error!", i));
        `uvm_info("run_phase", $sformatf("Finish randomization of prg_seq[%0d]", i), UVM_HIGH)

        //randomize data for each program
        if(!data_seq[i].randomize()) `uvm_error(get_name, "data_seq randomization error!");
        data_seq[i].bypass_data = (cmd_seq[i].header.format == aic_dp_cmd_gen_pkg::Bypass) ? 1 : 0;
        if (cmd_seq[i].header.format != aic_dp_cmd_gen_pkg::Bypass) begin
          //get necessary number of data based on instructions requests to input data (source param == pop)
          data_stream_len = prg_seq[i].get_input_stream_info(cmd_info_seq[i]);
          data_seq[i].set_data_stream_length(data_stream_len);
        end
        `uvm_info("run_phase", $sformatf("Finish set of data stream length of prg_seq[%0d]", i), UVM_HIGH)
      end
      //randomize the csr
      if(!csr_cfg_seq.randomize() with {
        irq_en == 1;
      }) `uvm_error(get_name, "csr_cfg_seq randomization error!");

      //write all commands. It is expected the last command (aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH+1) to be dropped by the cmd fifo
      foreach(cmd_seq[i]) begin
        `uvm_info("run_phase", $sformatf("Packing command %0d", i), UVM_HIGH)
        //get cmd_data into an array
        cmd_seq[i].get_packed_data_from_cmd(l_cmd_data_da);
        foreach(l_cmd_data_da[i]) `uvm_info("debug cmd", $sformatf("writing data[%0d]: 0x%0x", i, l_cmd_data_da[i]), UVM_HIGH)
      end
      //Start sequence that sends all commands in a single sequence that will split randomly the whole size (16 commands) into several transactions
      //randomize transaction
      if(!write_split_seq.randomize() with {
        if(iter==max_iter) split_burst == 0; //make sure that we have the scenario of sending all commands on a single burst transaction
        incr_addr_between_bursts == 0; //into the command fifo we don't want to increment the address between bursts. Always write to the base address of CMD fifo
        cfg_addr        == DWPU_CMD_ST_ADDR;
        cfg_data.size == l_cmd_data_da.size;
        foreach(cfg_data[i]) {
          cfg_data[i] == l_cmd_data_da[i];
        }
        if(iter%2) back_to_back_en == 1; //allow the back to back writes
        if(iter%4) bready_delay_on_back_to_back_en == 1; //allow the back to back writes with delay on bready
      }) `uvm_fatal(get_name, "write_tran randomization error!");
        //start sequence
      if(write_split_seq.back_to_back_en) begin
        fork
          write_split_seq.start(env.m_axi_system_env.master[0].sequencer);
        join_none
      end
      else begin
        write_split_seq.start(env.m_axi_system_env.master[0].sequencer);
      end

      //write all programs
      foreach(prg_seq[i]) begin
        `uvm_info("run_phase", $sformatf("Writing program %0d", i), UVM_HIGH)
        prg_seq[i].start(env.m_axi_system_env.master[0].sequencer);
      end

      `uvm_info ("run_phase", $sformatf("Writing in CSR.EXEC_EN 1 = 1"), UVM_HIGH)
      `uvm_info ("run_phase", $sformatf("Writing in CSR.DP_CTRL 1 weight_sgn: %b image_sgn: %0b skip_illegal_prog: %b ",
          csr_cfg_seq.weight_sign, csr_cfg_seq.image_sign, csr_cfg_seq.skip_illegal_prog), UVM_HIGH)
      csr_cfg_seq.start(env.sequencer);

      fork
        begin
          //start all the token sequences (sequences is not blocking so they can be launch and only used one at a time)
          foreach (tok_prod_seq[i]) begin
            if(cmd_seq[i].header.token_prod) begin
              `uvm_info("TOK_DBG", $sformatf("Starting producer token sequence"), UVM_HIGH)
              tok_prod_seq[i].start(env.tok_agt.m_tok_seqr);
            end
            if(cmd_seq[i].header.token_cons) begin
              `uvm_info("TOK_DBG", $sformatf("Starting consumer token sequence"), UVM_HIGH)
              tok_cons_seq[i].start(env.tok_agt.m_tok_seqr);
            end
          end
        end

        foreach (data_seq[i]) begin
          `uvm_info ("run_phase", $sformatf("Writing data %0d", i), UVM_HIGH)
          data_seq[i].start(env.m_axi_system_env.master[1].sequencer);
          #100ns;
        end
      join

      check_exec_done();

      //drain time to allow the token interface to finish its requests if they are still pending
      #10us;
      //reset
      `uvm_info ("run_phase", "Reset" , UVM_HIGH)
      if(!rst_seq.randomize()) `uvm_error(get_name, "axi_reset_seq randomization error!");
      rst_seq.start(env.sequencer);
      reset_dwpu_env();
    end
    `uvm_info ("run_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : ai_core_dwpu_cmd_fifo_overflow_test
