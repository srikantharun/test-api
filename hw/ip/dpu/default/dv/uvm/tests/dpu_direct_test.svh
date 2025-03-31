`ifndef DPU_DIRECT_TEST_SVH
`define DPU_DIRECT_TEST_SVH

//test to handle issues pointed out in MR 321

class dpu_direct_test extends dpu_base_test;
  `uvm_component_utils(dpu_direct_test)

  dpu_instruction_sequence instr_seq;

  function new(string name = "dpu_direct_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
     instr_seq = dpu_instruction_sequence::type_id::create("instr_seq");
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);

    axi_reset_seq.start(env.sequencer);

    init_regs();

    dpu_csr_config_seq.dp_ctrl_reg = 'hFFFF_FFFF;
    dpu_csr_config_seq.start(env.sequencer);

    //run_issue_2840();

    run_issue_2651();

    phase.drop_objection(this);

  endtask


  //issue 2840 - Incorrect handling of signed FP zeroes in compute operations
  //should generate -0 for neg, mul and prelu result
  task run_issue_2840();
    dpu_pkg::dpu_dp_cmd_t prog_mem[int];
    dpu_pkg::opcode_e issue_2840_opcode[3] = {OPC_MUL, OPC_UNARY, OPC_PRELU};
    foreach (issue_2840_opcode[i]) begin
      instr_seq.set_rfs = 0;
      instr_seq.randomize() with {
        instr.opcode == issue_2840_opcode[i];
        instr.src0 inside {[i0 : i0_f32], [i1 : i1_f32]};
        if (issue_2840_opcode[i] == OPC_UNARY)
          instr.src1 == FUNC_NEG;
        else
          instr.src1 inside {[a0 : b_c63]};
        instr.dst == l;
        addr          == DPU_PRG_ADDR_ST;
      };
      instr_seq.start(env.axi_system_env.master[0].sequencer);

      send_cmd_desc();

      //Sending stream data ifd0
      dpu_ifd0_stream_seq.fix_data_rnd_type = 1;
      dpu_ifd0_stream_seq.fixed_data_type   = dpu_stream_sequence::MINUS_ZERO;
      dpu_ifd0_stream_seq.ifd_config        = dpu_ifd0_stream_seq.IFD0;
      dpu_ifd0_stream_seq.cmd_desc          = dpu_cmd_descriptor_seq.cmd_desc;
      dpu_ifd0_stream_seq.prog_mem[0]       = instr_seq.instr;

      dpu_ifd1_stream_seq.fix_data_rnd_type = 1;
      dpu_ifd1_stream_seq.fixed_data_type   = dpu_stream_sequence::MINUS_ZERO;
      dpu_ifd1_stream_seq.ifd_config        = dpu_ifd1_stream_seq.IFD1;
      dpu_ifd1_stream_seq.cmd_desc          = dpu_cmd_descriptor_seq.cmd_desc;
      dpu_ifd1_stream_seq.prog_mem[0]       = instr_seq.instr;

      fork : data_stream_fork
        dpu_ifd0_stream_seq.start(env.axi_system_env.master[1].sequencer);
        dpu_ifd1_stream_seq.start(env.axi_system_env.master[2].sequencer);
      join_none

      wait_for_end_of_program();
      disable data_stream_fork;
      wait_cycles($urandom_range(1,20));
    end // foreach_issue_2840
  endtask : run_issue_2840


  //issue 2651 - The command does not continue the execution after 7 instructions for full program memory having NOP operations
  //generate nops accordingly to issue 2841
  task run_issue_2651();
    int instr_cnt;
    dpu_pkg::dpu_dp_cmd_t prog_mem[int];
    instr_seq.set_rfs = 0;

    //sending random instrs
    repeat ($urandom_range(2,5)) begin
      instr_seq.randomize() with {
        instr.opcode inside {[OPC_MUL: OPC_MIN]};
        addr          == DPU_PRG_ADDR_ST + instr_cnt * 4;
      };
      instr_seq.start(env.axi_system_env.master[0].sequencer);
      prog_mem[instr_cnt] = instr_seq.instr;
      instr_cnt++;
    end

    //sending NOP instrs
    repeat ($urandom_range(5,30)) begin
      instr_seq.randomize() with {
        instr.opcode == OPC_UNARY;
        instr.src1   == FUNC_NOP;
        addr         == DPU_PRG_ADDR_ST + instr_cnt * 4;
      };
      instr_seq.start(env.axi_system_env.master[0].sequencer);
      prog_mem[instr_cnt] = instr_seq.instr;
      instr_cnt++;
    end

    //after NOPs, execute a random instr
    repeat ($urandom_range(1,3)) begin
      instr_seq.randomize() with {
        instr.opcode inside {[OPC_MUL: OPC_MIN]};
        instr.dst == o;
        addr      == DPU_PRG_ADDR_ST + instr_cnt * 4;
      };
      instr_seq.start(env.axi_system_env.master[0].sequencer);
      prog_mem[instr_cnt] = instr_seq.instr;
      instr_cnt++;
    end
    instr_seq.randomize() with {
      instr.opcode inside {[OPC_MUL: OPC_MIN]};
      instr.dst == l;
      addr      == DPU_PRG_ADDR_ST + instr_cnt * 4;
    };
    instr_seq.start(env.axi_system_env.master[0].sequencer);
    prog_mem[instr_cnt] = instr_seq.instr;
    instr_cnt++;

    foreach(prog_mem[i])
      `uvm_info(get_name, $sformatf("gen prog mem[%0d] : %p", i, prog_mem[i]) ,UVM_HIGH);

    dpu_cmd_descriptor_seq.randomize() with {
      start_0                       == 1;
      cmd_desc.cmd.main_0.start     == 0;
      cmd_desc.cmd.main_0.length    == instr_cnt; 
      cmd_desc.cmd.main_0.iteration == 1;
      cmd_desc.header.format        == aic_dp_cmd_gen_pkg::LoopsM1N0;
      cmd_desc.header.h_config[0]   == 0; 
    };
    dpu_cmd_descriptor_seq.start(env.axi_system_env.master[0].sequencer);


    //Sending stream data ifd0
    dpu_ifd0_stream_seq.dp_ctrl_reg = dpu_csr_config_seq.dp_ctrl_reg;
    dpu_ifd0_stream_seq.ifd_config  = dpu_ifd0_stream_seq.IFD0;
    dpu_ifd0_stream_seq.cmd_desc    = dpu_cmd_descriptor_seq.cmd_desc;
    dpu_ifd0_stream_seq.prog_mem    = prog_mem;

    dpu_ifd1_stream_seq.dp_ctrl_reg = dpu_csr_config_seq.dp_ctrl_reg;
    dpu_ifd1_stream_seq.ifd_config  = dpu_ifd1_stream_seq.IFD1;
    dpu_ifd1_stream_seq.cmd_desc    = dpu_cmd_descriptor_seq.cmd_desc;
    dpu_ifd1_stream_seq.prog_mem    = prog_mem;

    fork : data_stream_fork
      dpu_ifd0_stream_seq.start(env.axi_system_env.master[1].sequencer);
      dpu_ifd1_stream_seq.start(env.axi_system_env.master[2].sequencer);
    join_none

    wait_for_end_of_program();
    disable data_stream_fork;

    wait_cycles($urandom_range(1,20));
  endtask : run_issue_2651

  task send_cmd_desc();
    dpu_cmd_descriptor_seq.randomize() with {
      start_0                       == 1;
      cmd_desc.cmd.main_0.start     == 0;
      cmd_desc.cmd.main_0.length    == 1; 
      cmd_desc.cmd.main_0.iteration == 1;
      cmd_desc.header.format        == aic_dp_cmd_gen_pkg::LoopsM1N0;
      cmd_desc.header.h_config[0]   == 0; 
    };
    dpu_cmd_descriptor_seq.start(env.axi_system_env.master[0].sequencer);
  endtask

endclass

`endif
