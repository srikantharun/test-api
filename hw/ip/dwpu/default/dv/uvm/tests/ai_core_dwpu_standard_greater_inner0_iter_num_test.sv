/**
* Generate a program to test the inner0 number of iterations greater than the sanity values.
* Random Configure dwpu_dp's  signed of weight and image regs
* Send data stream accordingly generated program requests
*/
class ai_core_dwpu_standard_greater_inner0_iter_num_test extends ai_core_dwpu_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_standard_greater_inner0_iter_num_test)

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
    //changing max_iter to 3 to make sure the testcase is no take too long
    //first iteration and third do the minimum, second do the maximum
    max_iter = 3;
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
  
  endfunction : build_phase
  
  /** Override randomize_cmd_seq to make sure the cmd has a init portion and the maximum of iterations is achieved for init portion */
  virtual function void randomize_cmd_seq(ai_core_dwpu_cmd_sequence cmd_seq, int iter, cmd_cfg_st cmd_cfg);
    /** randomize command to have init section and outer sections with shorter lengths and higher iterations */
    if(!cmd_seq.randomize() with {
      cmd_loop_info.init_len inside {[cmd_cfg.instr_min:cmd_cfg.instr_max]};
      cmd_loop_info.outer_len inside {[cmd_cfg.instr_min:cmd_cfg.instr_max]};
      cmd_loop_info.inner0_len inside {[cmd_cfg.instr_min:cmd_cfg.instr_max]};
      cmd_loop_info.inner1_len inside {[cmd_cfg.instr_min:cmd_cfg.instr_max]};
      
      if(iter inside {1,3}) cmd_loop_info.inner0_iter == 1;
      else                  cmd_loop_info.inner0_iter == ((1<<DWPU_DW_INNER0_ITER)-1);
      loop_cfg.has_loop0  == 1;
      
      //only allow full commands because we want to test all the possible values of the iteration field.
      //VERIF_DWPU_CMD_INITLOOP and VERIF_DWPU_CMD_NESTLOOP use short length (8 bits) for outer_iter
      header.cmd_format inside { VERIF_DWPU_CMD_FULL, VERIF_DWPU_CMD_FULL_ALLCHAN};
      enable_tokens == cmd_cfg.tokens_en;
    }) `uvm_error(get_name, $sformatf("cmd_seq randomization error!"));
  endfunction : randomize_cmd_seq
  
  virtual function void randomize_data_seq(ai_core_dwpu_stream_sequence data_seq);
    if(!data_seq.randomize() with {enable_tvalid_delay == 0;}) `uvm_error(get_name, "data_seq randomization error!");
  endfunction : randomize_data_seq

  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    
    for (int iter = 1; iter <= max_iter; iter++) begin
      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_LOW)
      /** Call common configurations with tokens enabled and number of instructions to be inside [0:2] */
      common_rand_cmd_prg_csr(
        .curr_iter(iter),
        .tokens_en(1),
        .instr_min(0),
        .instr_max(2));

      if (iter == max_iter-1)
        common_run(.reset_en(0), .watchdog_time_us(10000), .num_cycles_on_check(1000));
      else
        common_run(.watchdog_time_us(10000), .num_cycles_on_check(1000));
    end

    `uvm_info ("run_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : ai_core_dwpu_standard_greater_inner0_iter_num_test
