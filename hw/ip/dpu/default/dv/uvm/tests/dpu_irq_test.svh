`ifndef DPU_IRQ_TEST_SVH 
`define DPU_IRQ_TEST_SVH


class dpu_irq_test extends dpu_base_test;
  `uvm_component_utils(dpu_irq_test)

  dpu_random_stream_sequence dpu_rnd_stream_seq;
  dpu_instruction_sequence    instr_seq;
  
  randc dpu_irq_bit_pos_t irq_scenario;
 

  //specific interruption scenarios that will be generated in this test
  //the others interruptions are generated randomly
  constraint c_irq_scenario {
    irq_scenario inside {
      err_act_stream_in0,
      err_act_stream_in1,
      err_act_stream_out,
      err_illegal_format,
      err_empty_program,
      err_init_segfault,
      err_loop_segfault,
      err_i0_termination,
      err_i1_termination,
      err_id_illegal_instr,
      dbg_sw_interrupt,
      cmdblk_cmd_dropped
    
    };
  }

  function new(string name = "dpu_irq_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    dpu_rnd_stream_seq = dpu_random_stream_sequence::type_id::create("dpu_rnd_stream_seq");
    instr_seq           = dpu_instruction_sequence::type_id::create("instr_seq");
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);

    axi_reset_seq.start(env.sequencer);
    init_regs();

    repeat (1) begin

      fork 
       begin

        wait_cycles(5000);
        $finish;
       end
      join_none

      dpu_csr_config_seq.randomize();
      dpu_csr_config_seq.start(env.sequencer);
    
      //this.randomize(irq_scenario);
      irq_scenario =err_illegal_format; //err_act_stream_out;//err_act_stream_in0;
      `uvm_info(get_name, $sformatf("executing %p irq scenario", irq_scenario), UVM_HIGH)
      case (irq_scenario)
        err_act_stream_in0   : gen_act_stream_in_irq_scenario(1);
        err_act_stream_in1   : gen_act_stream_in_irq_scenario(0);
        err_act_stream_out   : gen_act_stream_out_irq_scenario();
        err_illegal_format   : gen_act_illegal_format_irq_scenario();
        err_empty_program    : gen_empty_program_irq_scenario();
        err_init_segfault    : gen_segfault_irq_scenario(0);
        err_loop_segfault    : gen_segfault_irq_scenario(1);
        err_i0_termination   : gen_in_termination_irq_scenario(1);
        err_i1_termination   : gen_in_termination_irq_scenario(0);
        err_id_illegal_instr : gen_id_illegal_irq_scenario();
        dbg_sw_interrupt     : gen_dbg_sw_interrupt_irq_scenario();
        cmdblk_cmd_dropped   : gen_cmdblk_cmd_dropped_irq_scenario();
      endcase
    end
    wait_cycles($urandom_range(10,20));
    axi_reset_seq.start(env.sequencer);
    phase.drop_objection(this);

  endtask


//*****************************************************************************************
//*****************************************************************************************
  //active input stream 0 or 1 after the execution of a command
  task gen_act_stream_in_irq_scenario(bit gen_in0_not_in1 = 1);
    cfg_cmd_desc(.loop_only(1));

    cfg_program_and_start();

    cfg_streams();
    
    //generate extra data after cmd execution to generate err_act_stream_inX irq
    dpu_rnd_stream_seq.randomize();
    fork 
      begin
        if (gen_in0_not_in1) 
          dpu_rnd_stream_seq.start(env.axi_system_env.master[1].sequencer);
        else
          dpu_rnd_stream_seq.start(env.axi_system_env.master[2].sequencer);
      end
    join_none
    wait_cycles($urandom_range(50,80));
    dpu_rnd_stream_seq.kill();
    axi_reset_seq.start(env.sequencer);
  endtask : gen_act_stream_in_irq_scenario


//*****************************************************************************************
//*****************************************************************************************
  task gen_act_stream_out_irq_scenario();
    cfg_cmd_desc(.loop_only(1));

    cfg_program_and_start(.config_only(1));

    begin
      int last_idx = dpu_program_seq.cmd_desc.cmd.loop_start + dpu_program_seq.cmd_desc.cmd.loop_len-1;
      //injection error - last instruction sends out data wout tlast
      dpu_program_seq.prog_mem[last_idx].cmd.dst = $urandom_range(o,o_bp);
      dpu_program_seq.start(env.axi_system_env.master[0].sequencer);
      dpu_cmd_descriptor_seq.start(env.axi_system_env.master[0].sequencer);
    end
      
    cfg_streams(.config_only(1));
    fork : data_stream_fork
      dpu_ifd0_stream_seq.start(env.axi_system_env.master[1].sequencer);
      dpu_ifd1_stream_seq.start(env.axi_system_env.master[2].sequencer);
    join_none

    wait_cycles($urandom_range(200,300));
    disable data_stream_fork;
    axi_reset_seq.start(env.sequencer);
  endtask : gen_act_stream_out_irq_scenario


//*****************************************************************************************
//*****************************************************************************************
  task gen_act_illegal_format_irq_scenario();
    //gen illegal cmd_format in command descriptor
    cfg_cmd_desc(.loop_only(1));
    dpu_cmd_descriptor_seq.cmd_desc.header.cmd_format = 3; 
    dpu_cmd_descriptor_seq.start(env.axi_system_env.master[0].sequencer);

    wait_cycles($urandom_range(200,300));
    axi_reset_seq.start(env.sequencer);

  endtask : gen_act_illegal_format_irq_scenario


//*****************************************************************************************
//*****************************************************************************************
  task gen_empty_program_irq_scenario();
    //gen illegal cmd_format in command descriptor
    cfg_cmd_desc(.i_min(0), .i_max(0), .li_min(0), .li_max(0), .ll_min(0), .ll_max(0));

    wait_cycles($urandom_range(200,300));
    axi_reset_seq.start(env.sequencer);

  endtask : gen_empty_program_irq_scenario


//*****************************************************************************************
//*****************************************************************************************
  //generate a init or loop cmd that reads outside prog_mem
  task gen_segfault_irq_scenario(bit gen_loop_not_init = 1);
    dpu_cmd_descriptor_seq.randomize() with {
      cmd_desc.cmd.init_start inside {[PROG_MEM_DEPTH-5: PROG_MEM_DEPTH-1]};

      if (gen_loop_not_init) {
        cmd_desc.header.cmd_format == dpu_common_pkg::DPU_CMD_LOOPONLY;
        cmd_desc.cmd.loop_start    inside {[PROG_MEM_DEPTH-5: PROG_MEM_DEPTH-1]};
        cmd_desc.cmd.loop_iter     == 1; 
      }
      else { 
        cmd_desc.header.cmd_format == dpu_common_pkg::DPU_CMD_FULL;
        cmd_desc.cmd.loop_start    == 0; 
        cmd_desc.cmd.loop_iter     == 0; 
      }
    };
    //error injection to make program be outside the memory
    dpu_cmd_descriptor_seq.cmd_desc.cmd.loop_len = $urandom_range(5,10);
    dpu_cmd_descriptor_seq.cmd_desc.cmd.init_len = $urandom_range(5,10);
    dpu_cmd_descriptor_seq.start(env.axi_system_env.master[0].sequencer);


    cfg_program_and_start();

    cfg_streams(.config_only(1));

    fork : data_stream_fork
      dpu_ifd0_stream_seq.start(env.axi_system_env.master[1].sequencer);
      dpu_ifd1_stream_seq.start(env.axi_system_env.master[2].sequencer);
    join_none

    wait_cycles($urandom_range(100,200));
    disable data_stream_fork;

    axi_reset_seq.start(env.sequencer);
  endtask : gen_segfault_irq_scenario 


//*****************************************************************************************
//*****************************************************************************************
  //input data interrupted with tlast
  task gen_in_termination_irq_scenario(bit gen_in0_not_in1 = 1);
    for (int i = 0; i < 3; i++) begin
      instr_seq.randomize() with {
        if (gen_in0_not_in1) {
          instr.cmd.src0 inside {[i0 : i1_bp]};
          !(instr.cmd.src1 inside {[i0 : i1_bp]});
        }
        else {
          !(instr.cmd.src0 inside {[i0 : i1_bp]});
          instr.cmd.src1 inside {[i0 : i1_bp]};
        }
        addr == DPU_PRG_ADDR_OFFSET + i*4;
      };
      instr_seq.start(env.axi_system_env.master[0].sequencer);
    end
    dpu_cmd_descriptor_seq.randomize() with {
      cmd_desc.cmd.loop_start    == 0;
      cmd_desc.cmd.loop_len      == 3;
      cmd_desc.cmd.loop_iter     == 1;
      cmd_desc.header.cmd_format == dpu_common_pkg::DPU_CMD_LOOPONLY;
      cmd_desc.header.cmd_id     == 'd1;
    };
    dpu_cmd_descriptor_seq.start(env.axi_system_env.master[0].sequencer);

    dpu_rnd_stream_seq.randomize() with {
      data_stream_len inside {[1:2]};
    };
    if (gen_in0_not_in1) 
      dpu_rnd_stream_seq.start(env.axi_system_env.master[1].sequencer);
    else
      dpu_rnd_stream_seq.start(env.axi_system_env.master[2].sequencer);

    wait_cycles($urandom_range(50,100));
    axi_reset_seq.start(env.sequencer);
  endtask : gen_in_termination_irq_scenario


//*****************************************************************************************
//*****************************************************************************************
  //input data interrupted with tlast
  task gen_id_illegal_irq_scenario();
    int illegal_src;
    int illegal_dst;
    bit illegal_sel = $urandom_range(0,1);

    instr_seq.randomize() with {
      instr.cmd.opcode != NOP;
    };
    instr_seq.addr = DPU_PRG_ADDR_OFFSET;
    if (illegal_sel == 0) begin
      std::randomize(illegal_src) with {
        illegal_src inside { ['h4 : 'hf], ['h14 : 'h1f], ['h28 : 'h3f] };
      };

      instr_seq.instr.cmd.src0 = illegal_src;
    end
    else begin
      std::randomize(illegal_dst) with {
        illegal_dst inside { ['h4 : 'hf], ['h14 : 'h1f], ['h28 : 'h3f] };
      };
      instr_seq.instr.cmd.dst = illegal_dst;
    end

    instr_seq.start(env.axi_system_env.master[0].sequencer);

    dpu_cmd_descriptor_seq.randomize() with {
      cmd_desc.cmd.loop_start    == 0;
      cmd_desc.cmd.loop_len      == 1;
      cmd_desc.cmd.loop_iter     == 1;
      cmd_desc.header.cmd_format == dpu_common_pkg::DPU_CMD_LOOPONLY;
      cmd_desc.header.cmd_id     == 'd1;
    };
    dpu_cmd_descriptor_seq.start(env.axi_system_env.master[0].sequencer);

    wait_cycles($urandom_range(50,100));
    axi_reset_seq.start(env.sequencer);
  endtask : gen_id_illegal_irq_scenario 


//*****************************************************************************************
//*****************************************************************************************
  //writing into dp_ctrl.dbg_sw_irq and reading from irq_status.dbg_sw_interrupt
  task gen_dbg_sw_interrupt_irq_scenario();
    uvm_status_e status;
    bit [63:0] irq_data;
    for (int itr = 0; itr < 8; itr++) begin
      bit i = $urandom_range(0, 1);
      //write 0 and 1 randomly, but only 1 should trigger dbg_sw_interrupt
      env.regmodel.dp_ctrl.write(status, {i, 32'h0});

      wait_cycles($urandom_range(20,50));
      env.regmodel.irq_status.read(status, irq_data);

      //write 1 to clear dbg_sw_interrupt signal
      if (itr > 5) begin
        env.regmodel.irq_status.write(status, {1'b1, 32'h0});
        wait_cycles($urandom_range(30,50));
        env.regmodel.irq_status.read(status, irq_data);
      end
    end
    wait_cycles($urandom_range(50,100));
    axi_reset_seq.start(env.sequencer);
  endtask : gen_dbg_sw_interrupt_irq_scenario


//*****************************************************************************************
//*****************************************************************************************
  task gen_cmdblk_cmd_dropped_irq_scenario();
    cfg_cmd_desc(.loop_only(1));

    cfg_program_and_start();

    fork
      cfg_streams();
      begin
        repeat (4) cfg_cmd_desc();
      end
    join_none
    wait_cycles($urandom_range(30,50));
    disable fork;
    axi_reset_seq.start(env.sequencer);
  endtask : gen_cmdblk_cmd_dropped_irq_scenario

endclass
`endif

