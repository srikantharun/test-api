/**
* Generate a program with random length and start add, RFS = 0 and loop interation = 1.
* Random Configure iau_dp's  signed_op and saturation_op
* Send data stream accordingly generated program requests
* These steps are iterated 4 times, a reset is done after the end of execution of each iteration
* Exept from the 3 to 4 iteration transition, there is no reset between them
*/
class iau_standard_test extends iau_base_test;
  /** UVM Component Utility macro */
  `uvm_component_utils(iau_standard_test)

  iau_stream_sequence                                       data_seq;
  iau_prg_sequence                                          prg_seq;
  iau_cmd_descriptor_sequence                               iau_cmd_seq;
  iau_csr_config_sequence                                   csr_cfg_seq;
  token_agent_cons_sequence                                 tok_cons_seq;
  token_agent_prod_sequence                                 tok_prod_seq;

  int_index_arr_t                                           data_stream_len;
  iau_cmd_header_t                                          header;
  int                                                       max_iter            = 4;
  iau_cmd_desc_t                                            cmd;
  uvm_status_e                                              status;
  rand int                                                  stall_input_stream;
  /** Class Constructor */
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    data_seq     = iau_stream_sequence::type_id::create("data_seq", this);
    prg_seq      = iau_prg_sequence::type_id::create("prg_seq", this);
    iau_cmd_seq  = iau_cmd_descriptor_sequence::type_id::create("iau_cmd_seq", this);
    csr_cfg_seq  = iau_csr_config_sequence::type_id::create("csr_cfg_seq", this);
    tok_cons_seq = token_agent_cons_sequence::type_id::create("tok_cons_seq", this);
    tok_prod_seq = token_agent_prod_sequence::type_id::create("tok_prod_seq", this);
  endfunction : build_phase



  task common_prog_cfg(input int p_smin             = 10,   //min number of instructions generated
                       input int p_smax             = 40,  //max number of instructions generated
                       input bit p_iter_en          = 0,   //if 1, cmd with loop_iter inside [1:10];
                       input bit set_rfs            = 0,   //if 1, randomly generate instrucions with rfs = 1
                       input bit gen_out_irq        = 0,   //if 1, generates condition that asserts output interruption
                       input bit gen_segfault_irq   = 0,   //if 1, generate a command w/ length > program memory depth
                       input bit gen_early_out_irq  = 0,   //if 1, generates more cmds with push-tlast for the same output stream
                       input bit gen_early_in_irq   = 0,   //if 1, generate more cmds with pop after the input stream has finished
                       input bit gen_rfs_irq        = 0,   //if 1, generate a rfs cmd with no pop in source
                       input bit invalid_reg_sweep  = 0,   //if 1, generate invalid reg addr 
                       input bit invld_prgmem_sweep = 0,   //if 1, generate invalid prog mem addr 
                       input int p_imin             = 1,   //min number of program iterations
                       input int p_imax             = 20,  //max number of program iterations
                       input bit bypass_cmd         = 0,   //if bypass cmd, generate a single data stream per cmd
                       input bit ignore_segfault    = 0,   //if 1, ignore segfault interruptions and execute cmd
                       input bit burst_transaction  = 0,   //if 1, generate different burst transactions for program memory
                       input bit single_stream      = 0);  //generates a single stream for whole program
    /********************************
    * Program generation
    *********************************/
    prg_seq.gen_output_irq = gen_out_irq;
    prg_seq.set_rfs        = set_rfs;
    //program generation
    if (!prg_seq.randomize() with {
      burst_transaction == local::burst_transaction;
      if (p_iter_en) {
        prog_iteration inside {[p_imin:p_imax]};
      }
      else if (gen_early_in_irq) {
        prog_iteration == 2;
      }
      else {
        prog_iteration == 1;
      }
      if (gen_segfault_irq) {
        prog_start_addr inside {[(PROG_MEM_DEPTH)-5:(PROG_MEM_DEPTH)-1]};
        prog_size       == PROG_MEM_DEPTH-prog_start_addr;
      }
      else if (gen_early_out_irq) {
        prog_size       inside {[1:PROG_MEM_DEPTH-prog_start_addr-2]};
      }
      else if (invld_prgmem_sweep) {
        prg_mem_invalid_range == invld_prgmem_sweep;
      }
      else if (invalid_reg_sweep) {
        invalid_reg_space == invalid_reg_sweep;
      }
      else {
        prog_size inside {[p_smin:p_smax]};
      }
    })`uvm_fatal("run_phase", "Failed to randomize");

    if (gen_early_out_irq) begin
      iau_common_pkg::iau_dp_cmd_t instr;
      instr.opcode = OP_ADD;
      instr.dst    = PUSH_TLAST;
      `uvm_info(get_name, $sformatf("gen_early_out_irq: prg_mem[%0d]: %p", prg_seq.prog_size - 2,
                                    prg_seq.prog_mem[prg_seq.prog_size-2]), UVM_HIGH)
      repeat (2) prg_seq.prog_mem.push_back(instr);
    end
    /********************************
    * Stream data configuration
    *********************************/
    //get necessary number of data based on instructions requests to input data (source param == pop)
    data_seq.high_value = $urandom_range(0, 1);
    if (!bypass_cmd) begin
      data_stream_len = prg_seq.get_input_stream_info();
      //instead of send loop_iter data streams, send a single stream of loop_iter * loop_len data
      if (single_stream) begin
        data_seq.prog_iteration = 1;
        data_stream_len[0] *= prg_seq.prog_iteration;
      end
      else
        data_seq.prog_iteration = prg_seq.prog_iteration;
    end else begin
      //bypass cmd now has fixed program iteration and length to 1
      data_seq.prog_iteration = 1;
      data_stream_len.delete();
      data_stream_len[0] = $urandom_range(1, 20);
    end


    if (gen_rfs_irq) begin
      prg_seq.prog_mem[prg_seq.prog_size-1].rfs  = 1;
      prg_seq.prog_mem[prg_seq.prog_size-1].src0 = $urandom_range(0, 7);
      prg_seq.prog_mem[prg_seq.prog_size-1].src1 = $urandom_range(0, 7);
    end

    /********************************
    * CSR configuration
    *********************************/
    //enables iau and dpu blocks to process cmds
    //and configure iau_dp op settings
    if (!csr_cfg_seq.randomize() with {
          irq_en == 32'hFFFF_FFFF;
          ignore_segfault == local::ignore_segfault;
        })
      `uvm_fatal("run_phase", "Failed to randomize");
    `uvm_info("run_phase", $sformatf("Writing in CSR.EXEC_EN = 1"), UVM_HIGH)
    `uvm_info("run_phase",
              $sformatf("Writing in CSR.DP_CTRL saturation: %b, signed: %b, ignore_segfault: %b",
                        csr_cfg_seq.sat_op, csr_cfg_seq.signed_op, csr_cfg_seq.ignore_segfault),
              UVM_HIGH)
    csr_cfg_seq.start(env.sequencer);
  endtask

  task check_exec_done();
    bit [63:0] data;
    data = ~0;
    //wait program done by checking IDLE state
    repeat (50) @(posedge env.axi_system_env.vif.common_aclk);
    //wait for state = idle = 0 : program is done
    while (|data[1:0]) begin // IDLE state == 0
      env.regmodel.cmdblk_status.read(status, data);
      repeat (100) @(posedge env.axi_system_env.vif.common_aclk);
    end

    `uvm_info ("run_phase", $sformatf("Program finished, iau in IDLE"), UVM_HIGH)
  endtask

  task check_irq();
    irq_en_t data;
    repeat (50) @(posedge env.axi_system_env.vif.common_aclk);
    while (data == 0) begin
      env.regmodel.irq_status.read(status, data);
      `uvm_info(get_name, $sformatf("Got interruption: %p", data), UVM_LOW)
      repeat (80) @(posedge env.axi_system_env.vif.common_aclk);
    end

    //leave some time to finish normally (check_exec_done) before killing
    repeat (200) @(posedge env.axi_system_env.vif.common_aclk);
    `uvm_info("run_phase", "irq = 1, exiting test", UVM_LOW)

  endtask


  task common_run(bit reset_en = 1, bit stream_rfs = 0, bit stream_bypass = 0,
                  input bit [7:0] loop_len = 1, input bit [7:0] loop_start = 0,
                  input bit [31:0] loop_iter = 1, input bit gen_segfault_irq = 0,
                  input bit tokens_en = 0, input int multiple_cmds_cnt = 1);
    fork : fork_common
      //input data stream
      begin
        repeat (multiple_cmds_cnt) begin
          //generate input data stream based on program (instr with pop, iteration)
          if(!this.randomize(stall_input_stream) with {
              stall_input_stream dist {
                0 := 10,
                [200 : 300] :/ 10
              };
          }) `uvm_fatal(get_name, "Randomization Failed!")
          repeat (stall_input_stream) @(posedge env.axi_system_env.vif.common_aclk);
          data_seq.set_data_stream_length(data_stream_len);
          data_seq.start(env.axi_system_env.master[1].sequencer);
        end
      end

      begin
        int iter_len = (stream_bypass || stream_rfs) ? 1 : data_stream_len.size();
        for (int i = 0; i < iter_len; i++) begin

          header.format = stream_bypass ? aic_dp_cmd_gen_pkg::Bypass : aic_dp_cmd_gen_pkg::LoopsM1N0;
          //invalid command: generate a cmd that will try to access
          //an address outside prog memory depth
          if (gen_segfault_irq) loop_len += $urandom_range(1, 10);
          iau_cmd_seq.cmd.main_0.length    = loop_len;
          iau_cmd_seq.cmd.main_0.start     = loop_start;
          iau_cmd_seq.cmd.main_0.iteration = loop_iter;
          iau_cmd_seq.header.format = header.format;
          iau_cmd_seq.enable_tokens = tokens_en;
          iau_cmd_seq.top = PROG_MEM_DEPTH; 
          fork
            begin : token_prod_thd
              if (iau_cmd_seq.header.token_prod) begin
                `uvm_info("TOK_DBG", $sformatf("Starting producer token sequence"), UVM_HIGH)
                tok_prod_seq.start(env.tok_agt.m_tok_seqr);
              end
            end
            begin : token_cons_thd
              if (iau_cmd_seq.header.token_cons) begin
                `uvm_info("TOK_DBG", $sformatf("Starting consumer token sequence"), UVM_HIGH)
                tok_cons_seq.start(env.tok_agt.m_tok_seqr);
              end
            end
            begin
              repeat (multiple_cmds_cnt) begin
                iau_cmd_seq.start(env.axi_system_env.master[0].sequencer);
              end
            end
          join
        end
        fork
          check_exec_done();
          check_irq();
        join_any
        disable fork_common;
      end
    join

    data_seq.kill();
    iau_cmd_seq.kill();

    repeat (100) @(posedge env.axi_system_env.vif.common_aclk);
    if (reset_en) begin
      `uvm_info("run_phase", "Reset", UVM_HIGH)
      rst_seq.start(env.sequencer);
    end
  endtask

  virtual task run_phase(uvm_phase phase);
    `uvm_info("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1);  // set the timeout

    for (int iter = 1; iter <= max_iter; iter++) begin
      `uvm_info("run_phase", $sformatf("Executing iteration %0d of %0d", iter, max_iter), UVM_HIGH)
      common_prog_cfg(.burst_transaction($urandom_range(0,1)));
      prg_seq.start(env.axi_system_env.master[0].sequencer);
      this.cmd = prg_seq.get_cmd();

      if (iter == max_iter - 1)
        common_run(.reset_en(0), .loop_len(this.cmd.loop_len), .loop_start(this.cmd.loop_start),
                   .loop_iter(this.cmd.loop_iter));
      else
        common_run(.loop_len(this.cmd.loop_len), .loop_start(this.cmd.loop_start),
                   .loop_iter(this.cmd.loop_iter), .tokens_en(1));
    end
    `uvm_info("run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : iau_standard_test

