/**
* Generate a program with only one instruction. With no usage of input stream, nor the output stream.
* The aim of the testcase is to verify the issue https://git.axelera.ai/ai-hw-team/triton/-/issues/2666
* We can call this testcase with two plus_args: OP_EXE and/or LAST_PUSH. By default the values of op_exe
*   and last_push are equal to 0. If the respective plus_arg is defined, the value is set to 1.
*/
class ai_core_dwpu_single_instr_no_input_no_output_test extends ai_core_dwpu_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_single_instr_no_input_no_output_test)

  ai_core_dp_cmd_gen_uvm_pkg::data_stream_cfg_t data_stream_len;
  int max_iter = 1;

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
    //set maximum iteration to 1
    max_iter=1;
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

  endfunction : build_phase

  virtual function void randomize_cmd_seq(ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb  cmd_info_seq , ai_core_dwpu_cmd_sequence cmd_seq, int iter, cmd_cfg_st cmd_cfg);
    if(!cmd_seq.randomize() with {
      enable_tokens == cmd_cfg.tokens_en;
      //set format to only have main 0
      header.format == aic_dp_cmd_gen_pkg::LoopsM1N0;
    }) `uvm_error(get_name, "cmd_seq randomization error!");

    //set the base and top addresses for cmd_info_seq randomization
    cmd_info_seq.base=0;
    cmd_info_seq.top=INSTR_MEM_DEPTH-1;
    //randomize command
    if(!cmd_info_seq.randomize() with {
      //set the command to be valid
      valid == 1;
      format == cmd_seq.header.format;

      //have only one instruction in the program
      main_0.length == 1;
      main_0.iteration == 1;
      
    }) `uvm_error(get_name, "cmd_info_seq randomization error!");
    
    //set the pointer to command info
    cmd_seq.cmd_info = cmd_info_seq;
     
  endfunction : randomize_cmd_seq

  virtual function void randomize_prg_seq(ai_core_dwpu_prg_sequence prg_seq);
    bit my_op_exe;
    bit my_last_push;

    if ($test$plusargs("OP_EXE")) my_op_exe = 1;
    else my_op_exe = 0;
    if ($test$plusargs("LAST_PUSH")) my_last_push = 1;
    else my_last_push = 0;

    if(!prg_seq.randomize() with {
      rnd_prog_mem_q.size==1;
      foreach(rnd_prog_mem_q[i]) {
        rnd_prog_mem_q[i].op_desc.rsvd==0;
        rnd_prog_mem_q[i].op_desc.opcode==0;
        rnd_prog_mem_q[i].op_desc.op_exe==0;
        rnd_prog_mem_q[i].op_desc.shift_wb==0;
        rnd_prog_mem_q[i].op_desc.shift_sp==0;
        rnd_prog_mem_q[i].op_desc.last_push==0;
        rnd_prog_mem_q[i].rsvd_i_sel == 0;
        rnd_prog_mem_q[i].rsvd_w_sel == 0;
        foreach(rnd_prog_mem_q[i].w_sel[j]) {
          rnd_prog_mem_q[i].w_sel[j] == 0;
        }
        foreach(rnd_prog_mem_q[i].i_sel[j]) {
          rnd_prog_mem_q[i].i_sel[j] == 0;
        }
      }
    }) `uvm_error(get_name, "cmd_seq randomization error!");
    prg_seq.prog_mem[0].op_desc.last_push=my_last_push;
    prg_seq.prog_mem[0].op_desc.op_exe = my_op_exe;
  endfunction : randomize_prg_seq


  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    for (int iter = 1; iter <= max_iter; iter++) begin
      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_LOW)
      common_rand_cmd_prg_csr(.curr_iter(iter));

      if (iter == max_iter-1)
        common_run(.reset_en(0));
      else
        common_run();
    end
    `uvm_info ("run_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : ai_core_dwpu_single_instr_no_input_no_output_test
