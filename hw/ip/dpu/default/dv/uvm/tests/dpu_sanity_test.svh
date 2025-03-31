`ifndef DPU_SANITY_TEST_SVH 
`define DPU_SANITY_TEST_SVH


class dpu_sanity_test extends dpu_base_test;
  `uvm_component_utils(dpu_sanity_test)

  dpu_instruction_sequence instr_seq;

  opcode_e op = 0;
  function new(string name = "dpu_sanity_test", uvm_component parent = null);
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
    for (int i = 0; i < op.num(); i++) begin
      int func_size = 1;
      if (i == OPC_PSEUDO) break;

      if (i == OPC_UNARY) func_size = 24; //FUNC_NOP to FUNC_SUMR
      else if (i == OPC_LUT) func_size = 4; // FUNC_LUT to FUNC_CHLUT
      else if (i == OPC_RFS) func_size = 23; // FUNC_NEG to FUNC_CMADD
      for (int j = 0; j < func_size; j++) begin
  
        dpu_csr_config_seq.randomize();
        dpu_csr_config_seq.start(env.sequencer);
        wait_cycles(20);

        instr_seq.set_rfs = 0;
        instr_seq.randomize() with {
          instr.opcode == op;
          if (i == OPC_UNARY && j inside {FUNC_CLMV, FUNC_CHMV, FUNC_CLMVCL, FUNC_CHMVCL, FUNC_CLMVCH, FUNC_CHMVCH})
            instr.src0 inside {[0:63]};
          else if (i inside {OPC_RFS,OPC_MADD_RFS})
            instr.src0 inside {[i0 : i0_f24], [i1 : i1_f24]};
          else
            instr.src0 inside {[i0 : i1_bp]};

          if (i == OPC_UNARY)
            instr.src1 == j;
          else if ((i == OPC_RFS || i == OPC_LUT) && instr.src2 inside {FUNC_CLLUT, FUNC_CHLUT, FUNC_DLUT})
            instr.src1 inside {[0:63]};
          else
            instr.src1 inside {[i0 : i1_bp]};

          if (i == OPC_LUT)
            instr.src2 == FUNC_LUT + j;
          else if (i == OPC_RFS)
            instr.src2 == FUNC_NEG + j;
          else
            instr.src2 inside {[i0 : i1_bp]};

          if (i == OPC_UNARY && j inside {FUNC_MVCL, FUNC_MVCH, FUNC_CLMVCL, FUNC_CHMVCL, FUNC_CLMVCH, FUNC_CHMVCH, FUNC_MVCL, FUNC_MVCH64})
            instr.dst inside {[0:63]};
          else if (i == OPC_MADD_RFS || i == OPC_RFS && instr.src2 inside {[FUNC_NEG: FUNC_MV], FUNC_SUB, FUNC_PRELU, FUNC_CMADD})
            instr.dst inside {[l : l_f24]};
          else
            instr.dst == l;

          addr      == DPU_PRG_ADDR_ST + i * 4;
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
      end  
    end

    phase.drop_objection(this);

  endtask

endclass

`endif

