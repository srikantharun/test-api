`ifndef DPU_SMOKE_TEST_SVH 
`define DPU_SMOKE_TEST_SVH


class dpu_smoke_test extends dpu_base_test;
  `uvm_component_utils(dpu_smoke_test)

  dpu_instruction_sequence instr_seq;

  opcode_e op = 0;
  function new(string name = "dpu_smoke_test", uvm_component parent = null);
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
    //Execute all instructions
    for (int i = 0; i < 10; i++) begin
      `uvm_info(get_name, $sformatf("executing operation: %s", op.name) , UVM_HIGH); 
      //TODO: issue in rtl with out_sign = 0 not giving int8 correct overflow value
      dpu_csr_config_seq.randomize() with { dp_ctrl_reg.out_int_sgn == 1;};
      dpu_csr_config_seq.start(env.sequencer);
      wait_cycles(20);

      instr_seq.set_rfs = 0;
      instr_seq.randomize() with {
        instr.opcode == op;
        instr.src0 inside {[i0 : i0_f32]};

        if ((op == OPC_RFS || op == OPC_LUT))
          instr.src1 inside {[0:63]};
        else
          instr.src1 inside {[i0 : i0_f32]};

        if (op == OPC_LUT)
          instr.src2 == FUNC_LUT;
        else if (i == OPC_RFS)
          instr.src2 == FUNC_NEG;
        else
          instr.src2 inside {[i0 : i0_f32]};
        
        instr.dst == l;
        addr      == DPU_PRG_ADDR_ST;
      };
      instr_seq.start(env.axi_system_env.master[0].sequencer);
      wait_cycles(10);

      dpu_cmd_descriptor_seq.randomize() with {
        start_0                       == 1;
        cmd_desc.cmd.main_0.start     == 0;
        cmd_desc.cmd.main_0.length    == 1; 
        cmd_desc.cmd.main_0.iteration == 1;
        cmd_desc.header.format        == aic_dp_cmd_gen_pkg::LoopsM1N0;
        cmd_desc.header.h_config[0]   == 0; 
      };
      dpu_cmd_descriptor_seq.start(env.axi_system_env.master[0].sequencer);

      //Sending stream data ifd0                                              
      dpu_ifd0_stream_seq.dp_ctrl_reg = dpu_csr_config_seq.dp_ctrl_reg;
      dpu_ifd0_stream_seq.ifd_config  = dpu_ifd0_stream_seq.IFD0;
      dpu_ifd0_stream_seq.cmd_desc    = dpu_cmd_descriptor_seq.cmd_desc;
      dpu_ifd0_stream_seq.prog_mem[0] = instr_seq.instr;
      
      dpu_ifd1_stream_seq.dp_ctrl_reg = dpu_csr_config_seq.dp_ctrl_reg;
      dpu_ifd1_stream_seq.ifd_config  = dpu_ifd1_stream_seq.IFD1;
      dpu_ifd1_stream_seq.cmd_desc    = dpu_cmd_descriptor_seq.cmd_desc;
      dpu_ifd1_stream_seq.prog_mem[0] = instr_seq.instr;
      
      fork : data_stream_fork
        dpu_ifd0_stream_seq.start(env.axi_system_env.master[1].sequencer);
        dpu_ifd1_stream_seq.start(env.axi_system_env.master[2].sequencer);     
      join_none
      
      wait_for_end_of_program();
      disable data_stream_fork;
      wait_cycles(5);
      op = op.next();
      //TODO: possible rtl issue, overflow not being properly made.
      if (op == OPC_MUL) op = op.next(); 
      //TODO: debug madd errors, implement pseudo instructions
      `uvm_info(get_name, $sformatf("next op: %s", op.name) , UVM_HIGH); 
      if (op == OPC_CMADD) begin 
        $display("trueeeee");
         break;
      end
    end

    phase.drop_objection(this);

  endtask

endclass

`endif

