/** Stream sequence that does not split the size of the data into several.
* This is necessary to make sure that the input stream interrupt is triggered correctly.
*/
class ai_core_dwpu_stream_no_split_sequence extends ai_core_dwpu_stream_sequence;

  constraint c_no_split_len {
    allow_split_len == 0;
  }

  `uvm_object_utils(ai_core_dwpu_stream_no_split_sequence)

  function new(string name = "ai_core_dwpu_stream_no_split_sequence");
    super.new(name);
    `uvm_info ("run_phase", $sformatf("New from ai_core_dwpu_stream_no_split_sequence"), UVM_HIGH)

  endfunction

endclass : ai_core_dwpu_stream_no_split_sequence

/** Define ai_core_dp_cmd_gen_cmdb with constraints to make sure the number of iterations is short to speed up the test */
class ai_core_dp_cmd_gen_cmdb_few_iterations extends ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb;

  constraint c_few_iterations {
    main_0.iteration inside {[0:2]};
    main_1.iteration inside {[0:2]};
    main_2.iteration inside {[0:2]};
    nested_0.iteration inside {[0:2]};
    nested_1.iteration inside {[0:2]};
  }

  `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_few_iterations)

  function new(string name = "ai_core_dp_cmd_gen_cmdb_few_iterations");
    super.new(name);
    `uvm_info ("run_phase", $sformatf("New from ai_core_dp_cmd_gen_cmdb_few_iterations"), UVM_LOW)

  endfunction

endclass : ai_core_dp_cmd_gen_cmdb_few_iterations

/**
* Same steps as iau_standard_test , 2 iterations
* Generates invalid programs to generate input and output irq
* 1st iteration: gen input irq by adding more data in the input stream than needed by program
* 2nd iteration: gen output irq by sending last instruction with dst = PUSH instead of PUSH-LAST
*/
class ai_core_dwpu_irq_test extends ai_core_dwpu_standard_test;
  int n_irq = 16;

  `uvm_component_utils (ai_core_dwpu_irq_test)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)
    /** Factory override of the master transaction object */
    set_type_override_by_type (ai_core_dwpu_stream_sequence::get_type(), ai_core_dwpu_stream_no_split_sequence::get_type());
    set_type_override_by_type (ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb::get_type(), ai_core_dp_cmd_gen_cmdb_few_iterations::get_type());

    super.build_phase(phase);
    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    bit [63:0] irq_data;
    int rand_idx;
    int l_innerloop_type;
    bit l_main_iter_en[3];
    bit l_main_len_en[3];
    bit l_nested_iter_en[2];
    bit l_nested_len_en[2];
    dwpu_irq_t irq_tested;
    bit irq_happened=0;

    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);

    if(!csr_cfg_seq.randomize() with {
      irq_en == 1;
      skip_illegal_prog == 1;
    }) `uvm_error(get_name, "csr_cfg_seq randomization error!");
    `uvm_info ("run_phase", $sformatf("Writing in CSR.EXEC_EN = 1"), UVM_HIGH)
    `uvm_info ("run_phase", $sformatf("Writing in CSR.DP_CTRL weight_sgn: %b image_sgn: %0b skip_illegal_prog: %b ",
        csr_cfg_seq.weight_sign, csr_cfg_seq.image_sign, csr_cfg_seq.skip_illegal_prog), UVM_HIGH)

    for (int iter = 0; iter < n_irq; iter++) begin
      `uvm_info ("run_phase", $sformatf("executing iter %0d of %0d",iter, n_irq-1), UVM_LOW)

      // set the local variable innerloop_type depending on the iteration that is being done
      if(iter inside {14}) begin
        l_innerloop_type = 1; //nested loops
      end
      else begin
        l_innerloop_type = 0; //random
      end

      common_rand_cmd_prg_csr(
        .curr_iter(iter),
        .instr_min(10),
        .instr_max(20),
        .all_loops_en(1),
        .innerloop_type(l_innerloop_type),
        .bypass_data_en(0), //make sure the commands that are randomized are different from bypass
        .csr_cfg_en(0)
      );

      //irq["ERR_ACT_STREAM_IN"]
      //input stream has more data than instructions w/ read_input = 1
      if (iter == 0) begin
        `uvm_info ("run_phase", $sformatf("Verifying ERR_ACT_STREAM_IN interrupt and Input stream is longer than it should"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_ACT_STREAM_IN;
        data_stream_len.main_dt_cnt[0]+=$urandom_range(1,5);
        data_stream_len.main_dt_cnt[1]+=$urandom_range(1,5);
        data_stream_len.main_dt_cnt[2]+=$urandom_range(1,5);
        data_stream_len.nested_dt_cnt[0]+=$urandom_range(1,5);
        data_stream_len.nested_dt_cnt[1]+=$urandom_range(1,5);
        data_seq.set_data_stream_length(data_stream_len);

      //irq["ERR_ACT_STREAM_OUT"]
      //deassert tlast flags of instructions
      end else if (iter == 1) begin
        `uvm_info ("run_phase", $sformatf("Verifying ERR_ACT_STREAM_OUT interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_ACT_STREAM_OUT;
        foreach (prg_seq.prog_mem[i])
        begin
          `uvm_info ("run_phase", $sformatf("Setting position %0d to be equal to last_push=0", i), UVM_HIGH)
          prg_seq.prog_mem[i].op_desc.last_push = 0;
        end

      //irq["ERR_ILLEGAL_FORMAT"]
      //invalid command format
      end else if (iter == 2) begin
        //create a command that will have an illegal format
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_format cmd_info_illegal_format_seq;
        cmd_info_illegal_format_seq  = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_format::type_id::create("cmd_info_illegal_format_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_ILLEGAL_FORMAT interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_ILLEGAL_FORMAT;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_format_seq.base=0;
        cmd_info_illegal_format_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_format_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_format_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_format_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_format_seq;
        `uvm_info ("run_phase", $sformatf("Value of cmd_format = %0d", cmd_seq.header.format), UVM_LOW)
        `uvm_info("run_phase", $sformatf("final command for ERR_ILLEGAL_FORMAT: %s", cmd_seq.convert2string()), UVM_LOW)


      //irq["ERR_EMPTY_PROGRAM"]
      //all loops len and or iter = 0
      end else if (iter == 3) begin //status of DP is on busy when it should be in IDLE
        //create a command that will have an empty program
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_empty_program cmd_info_empty_prg_seq;
        cmd_info_empty_prg_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_empty_program::type_id::create("cmd_info_empty_prg_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_EMPTY_PROGRAM interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_EMPTY_PROGRAM;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_empty_prg_seq.base=0;
        cmd_info_empty_prg_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_empty_prg_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_empty_prg_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_empty_prg_seq.format;
        cmd_seq.cmd_info = cmd_info_empty_prg_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_EMPTY_PROGRAM: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_MAIN_0_LEN"]
      //main 0 section greater than program memory
      end else if (iter == 4) begin
        //create a command that will have a program with main 0 length invalid
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_main_0_length cmd_info_illegal_main_0_length_seq;
        cmd_info_illegal_main_0_length_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_main_0_length::type_id::create("cmd_info_illegal_main_0_length_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_MAIN_0_LEN interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_MAIN_0_LEN;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_main_0_length_seq.base=0;
        cmd_info_illegal_main_0_length_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_main_0_length_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_main_0_length_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_main_0_length_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_main_0_length_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_MAIN_0_LEN: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_MAIN_1_LEN"]
      //main 1 section greater than program memory
      end else if (iter == 5) begin
        //create a command that will have a program with main 1 length invalid
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_main_1_length cmd_info_illegal_main_1_length_seq;
        cmd_info_illegal_main_1_length_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_main_1_length::type_id::create("cmd_info_illegal_main_1_length_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_MAIN_1_LEN interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_MAIN_1_LEN;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_main_1_length_seq.base=0;
        cmd_info_illegal_main_1_length_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_main_1_length_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_main_1_length_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_main_1_length_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_main_1_length_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_MAIN_1_LEN: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_MAIN_2_LEN"]
      //main 2 section greater than program memory
      end else if (iter == 6) begin
        //create a command that will have a program with main 2 length invalid
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_main_2_length cmd_info_illegal_main_2_length_seq;
        cmd_info_illegal_main_2_length_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_main_2_length::type_id::create("cmd_info_illegal_main_2_length_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_MAIN_2_LEN interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_MAIN_2_LEN;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_main_2_length_seq.base=0;
        cmd_info_illegal_main_2_length_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_main_2_length_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_main_2_length_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_main_2_length_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_main_2_length_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_MAIN_2_LEN: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_NESTED_0_LEN"]
      //NESTED 0 section greater than program memory
      end else if (iter == 7) begin
        //create a command that will have a program with nested 0 length invalid
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_0_length cmd_info_illegal_nested_0_length_seq;
        cmd_info_illegal_nested_0_length_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_0_length::type_id::create("cmd_info_illegal_nested_0_length_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_NESTED_0_LEN interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_NESTED_0_LEN;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_nested_0_length_seq.base=0;
        cmd_info_illegal_nested_0_length_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_nested_0_length_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_nested_0_length_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_nested_0_length_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_nested_0_length_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_NESTED_0_LEN: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_NESTED_1_LEN"]
      //NESTED 1 section greater than program memory
      end else if (iter == 8) begin
        //create a command that will have a program with nested 1 length invalid
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_1_length cmd_info_illegal_nested_1_length_seq;
        cmd_info_illegal_nested_1_length_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_1_length::type_id::create("cmd_info_illegal_nested_1_length_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_NESTED_1_LEN interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_NESTED_1_LEN;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_nested_1_length_seq.base=0;
        cmd_info_illegal_nested_1_length_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_nested_1_length_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_nested_1_length_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_nested_1_length_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_nested_1_length_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_NESTED_1_LEN: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_NESTED_0_MAP"]
      //NESTED 0 section not mapped correctly
      end else if (iter == 9) begin
        //create a command that will have a program with nested 0 map main incorrectly defined
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_0_mapping cmd_info_illegal_nested_0_map_seq;
        cmd_info_illegal_nested_0_map_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_0_mapping::type_id::create("cmd_info_illegal_nested_0_map_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_NESTED_0_MAP interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_NESTED_0_MAP;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_nested_0_map_seq.base=0;
        cmd_info_illegal_nested_0_map_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_nested_0_map_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_nested_0_map_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_nested_0_map_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_nested_0_map_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_NESTED_0_MAP: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_NESTED_1_MAP"]
      //NESTED 1 section not mapped correctly
      end else if (iter == 10) begin
        //create a command that will have a program with nested 1 map main incorrectly defined
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_1_mapping cmd_info_illegal_nested_1_map_seq;
        cmd_info_illegal_nested_1_map_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_1_mapping::type_id::create("cmd_info_illegal_nested_1_map_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_NESTED_1_MAP interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_NESTED_1_MAP;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_nested_1_map_seq.base=0;
        cmd_info_illegal_nested_1_map_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_nested_1_map_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_nested_1_map_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_nested_1_map_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_nested_1_map_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_NESTED_1_MAP: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_NESTED_0_SEGFAULT"]
      //nested 0 exceeds boundaries of main
      end else if (iter == 11) begin
        //create a command that will have a program with nested 0 end greater than main
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_0_segfault cmd_info_illegal_nested_0_segfault_seq;
        cmd_info_illegal_nested_0_segfault_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_0_segfault::type_id::create("cmd_info_illegal_nested_0_segfault_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_NESTED_0_SEGFAULT interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_NESTED_0_SEGFAULT;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_nested_0_segfault_seq.base=0;
        cmd_info_illegal_nested_0_segfault_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_nested_0_segfault_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_nested_0_segfault_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_nested_0_segfault_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_nested_0_segfault_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_NESTED_0_SEGFAULT: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_NESTED_1_SEGFAULT"]
      //nested 1 exceeds boundaries of main
      end else if (iter == 12) begin
        //create a command that will have a program with nested 1 end greater than instruction memory
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_1_segfault cmd_info_illegal_nested_1_segfault_seq;
        cmd_info_illegal_nested_1_segfault_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_1_segfault::type_id::create("cmd_info_illegal_nested_1_segfault_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_NESTED_1_SEGFAULT interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_NESTED_1_SEGFAULT;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_nested_1_segfault_seq.base=0;
        cmd_info_illegal_nested_1_segfault_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_nested_1_segfault_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_nested_1_segfault_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_nested_1_segfault_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_nested_1_segfault_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_NESTED_1_SEGFAULT: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_NESTED_ORDER"]
      //nested 1 starts before nested 0 on the same main
      end else if (iter == 13) begin
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_order cmd_info_illegal_nested_order_seq;
        cmd_info_illegal_nested_order_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_order::type_id::create("cmd_info_illegal_nested_order_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_NESTED_ORDER interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_NESTED_ORDER;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_nested_order_seq.base=0;
        cmd_info_illegal_nested_order_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_nested_order_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_nested_order_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_nested_order_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_nested_order_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_NESTED_ORDER: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_NESTED_NESTING"]
      //nested 0 is inside nested 1
      end else if (iter == 14) begin
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_nesting cmd_info_illegal_nested_nesting_seq;
        cmd_info_illegal_nested_nesting_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_nesting::type_id::create("cmd_info_illegal_nested_nesting_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_NESTED_NESTING interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_NESTED_NESTING;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_nested_nesting_seq.base=0;
        cmd_info_illegal_nested_nesting_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_nested_nesting_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_nested_nesting_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_nested_nesting_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_nested_nesting_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_NESTED_NESTING: %s", cmd_seq.convert2string()), UVM_LOW)

      //irq["ERR_NESTED_OVERLAP"]
      //nested 1 starts inside nested 0 and ends after nested 0
      end else if (iter == 15) begin
        ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_overlap cmd_info_illegal_nested_overlap_seq;
        cmd_info_illegal_nested_overlap_seq = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb_illegal_nested_overlap::type_id::create("cmd_info_illegal_nested_overlap_seq", this);
        `uvm_info ("run_phase", $sformatf("Verifying ERR_NESTED_OVERLAP interrupt"), UVM_LOW)
        irq_tested = DWPU_IRQ_ERR_NESTED_OVERLAP;
        //set the base and top addresses for cmd_info_seq randomization
        cmd_info_illegal_nested_overlap_seq.base=0;
        cmd_info_illegal_nested_overlap_seq.top=INSTR_MEM_DEPTH-1;
        //randomize command
        if(!cmd_info_illegal_nested_overlap_seq.randomize()) begin
          `uvm_error(get_name, "cmd_info_illegal_nested_overlap_seq randomization error!");
        end
        cmd_seq.header.format = cmd_info_illegal_nested_overlap_seq.format;
        cmd_seq.cmd_info = cmd_info_illegal_nested_overlap_seq;
        `uvm_info("run_phase", $sformatf("final command for ERR_NESTED_OVERLAP: %s", cmd_seq.convert2string()), UVM_LOW)
      end

      //clear irq_happened
      irq_happened=0;
      fork
        common_run(.reset_en(0));
        begin
          //disable test when irq is asserted
          irq_data = 0;
          repeat(20) @(posedge env.m_axi_system_env.vif.common_aclk);
          while (irq_data[irq_tested] == 0) begin
            regmodel.irq_status.read(status, irq_data);
            repeat(80) @(posedge env.m_axi_system_env.vif.common_aclk);
          end
          irq_happened=1;
          `uvm_info ("run_phase", "irq = 1, exiting test", UVM_LOW)
          //drain time of 10us because the tready delay is 1000 cycles maximum
          #10us;
        end
      join_any
      disable fork;

      if(irq_happened==0)begin
        `uvm_error(get_name, $sformatf("IRQ %s was not signalized in irq_status", irq_tested.name()));
      end

      data_seq.kill();
      cmd_seq.kill();
      `uvm_info ("run_phase", "Reset" , UVM_HIGH)
      if(!rst_seq.randomize()) `uvm_fatal(get_name, "axi_reset_seq randomization error!")
      rst_seq.start(env.sequencer);
      reset_dwpu_env();
      repeat(20) @(posedge env.m_axi_system_env.vif.common_aclk);
    end

    /** test DBG_SW_IRQ */
    //write enable to DBG_SW_INTERRUPT on IRQ_EN
    irq_data[DWPU_IRQ_DBG_SW_INTERRUPT] = 1'b1;
    regmodel.irq_en.write(status, irq_data);
    repeat(80) @(posedge env.m_axi_system_env.vif.common_aclk);
    //check that DBG_SW_IRQ is low
    regmodel.irq_status.read(status, irq_data);
    if(irq_data[DWPU_IRQ_DBG_SW_INTERRUPT]) begin
      `uvm_error("dwpu_scb",  $sformatf("Value of DWPU_IRQ_DBG_SW_INTERRUPT shall be 0 before being manually triggered. Monitored value = %0d and expected value = %0d",
        irq_data[DWPU_IRQ_DBG_SW_INTERRUPT], 1'b0) );
    end
    else begin
      `uvm_info("run_phase", $sformatf("Value of DWPU_IRQ_DBG_SW_INTERRUPT before manually triggered is equal to 1'b0 as it should"), UVM_MEDIUM)
    end
    //set DBG_SW_IRQ field into register DP_CTRL to trigger respective interrrupt
    irq_data[DWPU_IRQ_DBG_SW_INTERRUPT] = 1'b1;
    regmodel.dp_ctrl.write(status, irq_data);
    //check that DBG_SW_IRQ is high
    repeat(80) @(posedge env.m_axi_system_env.vif.common_aclk);
    regmodel.irq_status.read(status, irq_data);
    if(irq_data[DWPU_IRQ_DBG_SW_INTERRUPT]==0) begin
      `uvm_error("dwpu_scb",  $sformatf("Value of DWPU_IRQ_DBG_SW_INTERRUPT shall be 1 after being manually triggered. Monitored value = %0d and expected value = %0d",
        irq_data[DWPU_IRQ_DBG_SW_INTERRUPT], 1'b1) );
    end
    else begin
      `uvm_info("run_phase", $sformatf("Value of DWPU_IRQ_DBG_SW_INTERRUPT after being manually triggered is equal to 1'b1 as it should"), UVM_MEDIUM)
    end

    `uvm_info ("run_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : ai_core_dwpu_irq_test

