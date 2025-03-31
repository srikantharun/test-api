/**
* Generate a program with random length and start addr, loop interation = 1.
* Random Configure dwpu_dp's  signed of weight and image regs
* Send data stream accordingly generated program requests
* These steps are iterated 4 times, a reset is done after the end of execution of each iteration
* Except from the 3 to 4 iteration transition, there is no reset between them
*/
class ai_core_dwpu_standard_test extends ai_core_dwpu_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_standard_test)

  axi_simple_reset_sequence                             rst_seq;
  ai_core_dwpu_csr_config_sequence                      csr_cfg_seq;
  ai_core_dwpu_cmd_sequence                             cmd_seq;
  ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb   cmd_info_seq;
  ai_core_dwpu_stream_sequence                          data_seq;
  ai_core_dwpu_prg_sequence                             prg_seq;
  token_agent_cons_sequence                             tok_cons_seq;
  token_agent_prod_sequence                             tok_prod_seq;

  ai_core_dp_cmd_gen_uvm_pkg::data_stream_cfg_t data_stream_len;
  bit [63:0] data;
  int max_iter = 10;
  uvm_status_e status;
  bit has_reset = 1;
  int wait_clk_cycles;

  typedef struct {
    int iter            ;
    int instr_min       ;
    int instr_max       ;
    bit iter_en         ;
    int iter_min        ;
    int iter_max        ;
    bit bypass_data_en  ;
    bit bypass_data     ;
    bit all_loops_en    ;
    int innerloop_type  ;
    bit tokens_en       ;
  } cmd_cfg_st;

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    rst_seq       = axi_simple_reset_sequence::type_id::create("rst_seq", this);
    data_seq      = ai_core_dwpu_stream_sequence::type_id::create("data_seq", this);
    prg_seq       = ai_core_dwpu_prg_sequence::type_id::create("prg_seq", this);
    cmd_seq       = ai_core_dwpu_cmd_sequence::type_id::create("cmd_seq", this);
    cmd_info_seq  = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb::type_id::create("cmd_info_seq", this);
    csr_cfg_seq   = ai_core_dwpu_csr_config_sequence::type_id::create("csr_cfg_seq", this);
    tok_cons_seq  = token_agent_cons_sequence::type_id::create("tok_cons_seq", this);
    tok_prod_seq  = token_agent_prod_sequence::type_id::create("tok_prod_seq", this);

    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction : build_phase
  
  virtual function void randomize_cmd_seq(ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb  cmd_info_seq , ai_core_dwpu_cmd_sequence cmd_seq, int iter, cmd_cfg_st cmd_cfg);
    if(!cmd_seq.randomize() with {
      enable_tokens == cmd_cfg.tokens_en;

      //if all loops are enabled then set the format to the full command (3 main and 2 nested)
      if (cmd_cfg.all_loops_en) {
        header.format == aic_dp_cmd_gen_pkg::LoopsM3N2;
      }
      //if bypass_data_en is set then it means that it can randomize Bypass command, otherwise always randomize command excepting Bypass format
      if(cmd_cfg.bypass_data_en) {
        //if bypass is enabled and we strickly specify bypass_data it means that all commands will be in Bypass mode
        if(cmd_cfg.bypass_data) {
          header.format == aic_dp_cmd_gen_pkg::Bypass;
        }
      }
      else {
        header.format != aic_dp_cmd_gen_pkg::Bypass;
      }
    }) `uvm_error(get_name, "cmd_seq randomization error!");

    //set the base and top addresses for cmd_info_seq randomization
    cmd_info_seq.base=0;
    cmd_info_seq.top=INSTR_MEM_DEPTH-1;
    //randomize command
    if(!cmd_info_seq.randomize() with {
      //set the command to be valid
      valid == 1;
      format == cmd_seq.header.format;
      
      if (cmd_cfg.iter_en) {
        main_0.iteration    inside {[cmd_cfg.iter_min:cmd_cfg.iter_max]};
        main_1.iteration    inside {[cmd_cfg.iter_min:cmd_cfg.iter_max]};
        main_2.iteration    inside {[cmd_cfg.iter_min:cmd_cfg.iter_max]};
        nested_0.iteration  inside {[cmd_cfg.iter_min:cmd_cfg.iter_max]};
        nested_1.iteration  inside {[cmd_cfg.iter_min:cmd_cfg.iter_max]};
      }

      //co-nested and nested loops (not parallel)
      if(cmd_cfg.innerloop_type == 1) {
        (`_co_nested_ && (`_start_(nested_1) <= `_end_(nested_0))) == 1;
      }
      if(cmd_cfg.innerloop_type == 2) {
        (`_co_nested_ && (`_start_(nested_1) > `_end_(nested_0))) == 1;
      }

      if(`_main_0_valid_)   main_0.length   inside {[cmd_cfg.instr_min:cmd_cfg.instr_max]};
      if(`_main_1_valid_)   main_1.length   inside {[cmd_cfg.instr_min:cmd_cfg.instr_max]};
      if(`_main_2_valid_)   main_2.length   inside {[cmd_cfg.instr_min:cmd_cfg.instr_max]};
      if(`_nested_0_valid_) nested_0.length inside {[cmd_cfg.instr_min:cmd_cfg.instr_max]};
      if(`_nested_1_valid_) nested_1.length inside {[cmd_cfg.instr_min:cmd_cfg.instr_max]};

    }) `uvm_error(get_name, "cmd_info_seq randomization error!");

    //set the pointer to command info
    cmd_seq.cmd_info = cmd_info_seq;
  endfunction : randomize_cmd_seq

  virtual function void randomize_prg_seq(ai_core_dwpu_prg_sequence prg_seq);
    if(!prg_seq.randomize()) `uvm_error(get_name, "prg_seq randomization error!");
  endfunction : randomize_prg_seq
  
  virtual function void randomize_data_seq(ai_core_dwpu_stream_sequence data_seq);
    if(!data_seq.randomize()) `uvm_error(get_name, "data_seq randomization error!");
  endfunction : randomize_data_seq

  virtual function void randomize_csr_seq(ai_core_dwpu_csr_config_sequence csr_cfg_seq);
    if(!csr_cfg_seq.randomize() with {
      irq_en == 1;
    }) `uvm_error(get_name, "csr_cfg_seq randomization error!");
    `uvm_info ("randomize_csr_seq", $sformatf("Writing in CSR.EXEC_EN = 1"), UVM_HIGH)
    `uvm_info ("randomize_csr_seq", $sformatf("Writing in CSR.DP_CTRL weight_sgn: %b image_sgn: %0b skip_illegal_prog: %b ",
        csr_cfg_seq.weight_sign, csr_cfg_seq.image_sign, csr_cfg_seq.skip_illegal_prog), UVM_HIGH)
  endfunction : randomize_csr_seq


  task common_rand_cmd_prg_csr( int curr_iter             ,   //current iteration
                                int instr_min        = 5  ,   //min number of instructions generated
                                int instr_max        = 20 ,  //max number of instructions generated
                                bit iter_en          = 0  ,   //if 1, cmd with loop_iter inside [1:10];
                                int iter_min         = 0  ,   //min number of program iterations
                                int iter_max         = 10 ,
                                bit bypass_data_en   = 1  ,   //enable bypass command to be randomized
                                bit bypass_data      = 0  ,   //command that will be randomized is equal to bypass
                                bit all_loops_en     = 0  ,
                                int innerloop_type   = 0  ,   //0 means random, 1 means nested, 2 means parallel
                                bit csr_cfg_en       = 1  ,
                                bit tokens_en        = 0      //generate all the 3 loops
                              );
    /********************************
    * CMD & Program generation
    *********************************/
    cmd_cfg_st cmd_cfg;
    cmd_cfg.instr_min       = instr_min;
    cmd_cfg.instr_max       = instr_max;
    cmd_cfg.iter_en         = iter_en;
    cmd_cfg.iter_min        = iter_min;
    cmd_cfg.iter_max        = iter_max;
    cmd_cfg.bypass_data_en  = bypass_data_en;
    cmd_cfg.bypass_data     = bypass_data;
    cmd_cfg.all_loops_en    = all_loops_en;
    cmd_cfg.innerloop_type  = innerloop_type;
    cmd_cfg.tokens_en       = tokens_en;
    /** Randomize command depending on the iteration*/
    randomize_cmd_seq(cmd_info_seq, cmd_seq, curr_iter, cmd_cfg);
    //set command info to program sequence
    prg_seq.cmd_info      = cmd_info_seq;
    //program generation
    randomize_prg_seq(prg_seq);

    /********************************
    * Stream data configuration
    *********************************/
    randomize_data_seq(data_seq);
    data_seq.bypass_data = (cmd_seq.header.format == aic_dp_cmd_gen_pkg::Bypass) ? 1 : 0;
    if (cmd_seq.header.format != aic_dp_cmd_gen_pkg::Bypass) begin
      //get necessary number of data based on instructions requests to input data (source param == pop)
      data_stream_len = prg_seq.get_input_stream_info(cmd_info_seq);
      data_seq.set_data_stream_length(data_stream_len);
    end

    /********************************
    * CSR configuration
    *********************************/
    //enables dwpu blocks to process cmds
    //and configure dwpu_dp op settings
    if (csr_cfg_en) begin
      randomize_csr_seq(csr_cfg_seq);
    end
  endtask


  task common_run(bit reset_en = 1, int watchdog_time_us=10000, int num_cycles_on_check=50);
    /** Start writing the csr */
    csr_cfg_seq.start(env.sequencer);
    /** Start write of the program to memory */
    prg_seq.start(env.m_axi_system_env.master[0].sequencer);
    
    fork : fork_common
      //input data strem
      data_seq.start(env.m_axi_system_env.master[1].sequencer);

      begin
        //send command
        cmd_seq.start(env.m_axi_system_env.master[0].sequencer);
        `uvm_info("common_run", $sformatf("Finish cmd_seq"), UVM_HIGH)
        //reset between iterations, send command again
        if (has_reset) begin
          has_reset = 0;
        end
        check_exec_done(num_cycles_on_check);
        disable fork_common;
        `uvm_info("common_run", $sformatf("cmd_seq done"), UVM_HIGH)
      end
      begin : token_prod_thd
        if(cmd_seq.header.token_prod) begin
          `uvm_info("TOK_DBG", $sformatf("Starting producer token sequence"), UVM_HIGH)
          tok_prod_seq.start(env.tok_agt.m_tok_seqr);
        end
        `uvm_info("TOK_DBG", $sformatf("token_prod_thd done"), UVM_HIGH)
      end
      begin : token_cons_thd
        if(cmd_seq.header.token_cons) begin
          `uvm_info("TOK_DBG", $sformatf("Starting consumer token sequence"), UVM_HIGH)
          tok_cons_seq.start(env.tok_agt.m_tok_seqr);
        end
        `uvm_info("TOK_DBG", $sformatf("token_cons_thd done"), UVM_HIGH)
      end
      begin : watchdog_thd
        #(watchdog_time_us*1us);
        `uvm_error("check_exec_done", $sformatf("Watchdog of 50us was reached and the DUT didn't change its state to IDLE"))
        disable fork_common;
      end
    join
    `uvm_info("common_run", $sformatf("Finish data and cmd_seq"), UVM_HIGH)
    repeat(5000) @(posedge env.m_axi_system_env.vif.common_aclk);
    if (reset_en) begin
      `uvm_info ("common_run", "Reset" , UVM_HIGH)
      if(!rst_seq.randomize()) `uvm_error(get_name, "axi_reset_seq randomization error!");
      rst_seq.start(env.sequencer);
      has_reset = 1;
      reset_dwpu_env();
    end
    `uvm_info("common_run", $sformatf("Finish common_run"), UVM_HIGH)
  endtask

  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    for (int iter = 1; iter <= max_iter; iter++) begin
      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_LOW)
      common_rand_cmd_prg_csr(.curr_iter(iter), .tokens_en(1'b1), .iter_en(1));

      if (iter == max_iter-1)
        common_run(.reset_en(0));
      else
        common_run();
    end
    `uvm_info ("run_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : ai_core_dwpu_standard_test
