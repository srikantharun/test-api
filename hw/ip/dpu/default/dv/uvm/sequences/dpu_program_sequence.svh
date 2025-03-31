`ifndef DPU_PRG_SEQUENCE_SV
`define DPU_PRG_SEQUENCE_SV

class dpu_program_sequence extends svt_axi_master_base_sequence;
  `uvm_object_utils(dpu_program_sequence)

  dpu_cmd_descriptor_t cmd_desc;
  dpu_pkg::dpu_dp_cmd_t prog_mem[int];
  rand dpu_instruction_sequence instr_seq;
  bit [AXI_DW-1:0] data;
  bit [AXI_AW-1:0] addr;
  bit set_rfs;


  function new(string name = "dpu_program_sequence");
    super.new(name);
    instr_seq = new();
  endfunction


  function void pre_randomize();
    prog_mem.delete();
    `uvm_info(get_name, $sformatf("received cmd: %p", cmd_desc), UVM_HIGH);
    case (cmd_desc.header.format)
      aic_dp_cmd_gen_pkg::LoopsM1N0: begin
        for (int i = cmd_desc.cmd.main_0.start; i <= `_end_(cmd_desc.cmd.main_0); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N1: begin
        for (int i = cmd_desc.cmd.main_0.start; i <= `_end_(cmd_desc.cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.nested_0.start; i <= `_end_(cmd_desc.cmd.nested_0); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N2: begin
        for (int i = cmd_desc.cmd.main_0.start; i <= `_end_(cmd_desc.cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.nested_0.start; i <= `_end_(cmd_desc.cmd.nested_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.nested_1.start; i <= `_end_(cmd_desc.cmd.nested_1); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N0: begin
        for (int i = cmd_desc.cmd.main_0.start; i <= `_end_(cmd_desc.cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.main_1.start; i <= `_end_(cmd_desc.cmd.main_1); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N1: begin
        for (int i = cmd_desc.cmd.main_0.start; i <= `_end_(cmd_desc.cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.main_1.start; i <= `_end_(cmd_desc.cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.nested_0.start; i <= `_end_(cmd_desc.cmd.nested_0); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N2: begin
        for (int i = cmd_desc.cmd.main_0.start; i <= `_end_(cmd_desc.cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.main_1.start; i <= `_end_(cmd_desc.cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.nested_0.start; i <= `_end_(cmd_desc.cmd.nested_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.nested_1.start; i <= `_end_(cmd_desc.cmd.nested_1); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N0: begin
        for (int i = cmd_desc.cmd.main_0.start; i <= `_end_(cmd_desc.cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.main_1.start; i <= `_end_(cmd_desc.cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.main_2.start; i <= `_end_(cmd_desc.cmd.main_2); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N1: begin
        for (int i = cmd_desc.cmd.main_0.start; i <= `_end_(cmd_desc.cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.main_1.start; i <= `_end_(cmd_desc.cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.main_2.start; i <= `_end_(cmd_desc.cmd.main_2); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.nested_0.start; i <= `_end_(cmd_desc.cmd.nested_0); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N2: begin
        for (int i = cmd_desc.cmd.main_0.start; i <= `_end_(cmd_desc.cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.main_1.start; i <= `_end_(cmd_desc.cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.main_2.start; i <= `_end_(cmd_desc.cmd.main_2); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.nested_0.start; i <= `_end_(cmd_desc.cmd.nested_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd_desc.cmd.nested_1.start; i <= `_end_(cmd_desc.cmd.nested_1); i++)
          prog_mem[i] = 0;
      end
    endcase
  endfunction


  function void post_randomize();
    int rand_index;
    foreach (prog_mem[i]) begin
      $display("randomizing with set_rfs: %0b", set_rfs);
      if (set_rfs) begin
        instr_seq.randomize() with {
          instr.opcode dist { OPC_RFS := 80, OPC_MADD_RFS := 10};
          instr.dst   inside {[l : l_f24]};
        };
      end
      else
        assert(instr_seq.randomize() with {
          !(instr.opcode inside {OPC_RFS, OPC_MADD_RFS});
        });

      prog_mem[i] = instr_seq.instr;

      //DPU ISA Spec: the values for the bins in src1 must be monotononically increasing
      //if src1 = internal regs, populate them with mv op that follows this constraint
      if (prog_mem[i].opcode inside {OPC_LUT, OPC_RFS} && prog_mem[i].src2 == FUNC_LUT && !(prog_mem[i].src1 inside {[i0:i1_f24]})) begin

        assert(instr_seq.randomize() with {
          instr.opcode  == OPC_MV;
          instr.src0    inside {[i0 : i1_f24]};
          instr.dst     == dst_t'(prog_mem[i].src1);

          //not used, just to identify a MV before a LUT op
          instr.src1    == a0;
          instr.src2    == a0;
        });

        prog_mem[i-1] = instr_seq.instr;
      end
    end

    //verif program rules
    //at least one instruction should receive input data
    //at least one instruction send data with tlast at end of program
    case (cmd_desc.header.format)
      aic_dp_cmd_gen_pkg::LoopsM1N0: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
      end
      aic_dp_cmd_gen_pkg::LoopsM1N1: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
        gen_rnd_instr(cmd_desc.cmd.nested_0);
      end
      aic_dp_cmd_gen_pkg::LoopsM1N2: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
        gen_rnd_instr(cmd_desc.cmd.nested_0);
        gen_rnd_instr(cmd_desc.cmd.nested_1);
      end
      aic_dp_cmd_gen_pkg::LoopsM2N0: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
        gen_rnd_instr(cmd_desc.cmd.main_1);
      end
      aic_dp_cmd_gen_pkg::LoopsM2N1: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
        gen_rnd_instr(cmd_desc.cmd.main_1);
        gen_rnd_instr(cmd_desc.cmd.nested_0);
      end
      aic_dp_cmd_gen_pkg::LoopsM2N2: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
        gen_rnd_instr(cmd_desc.cmd.main_1);
        gen_rnd_instr(cmd_desc.cmd.nested_0);
        gen_rnd_instr(cmd_desc.cmd.nested_1);
      end
      aic_dp_cmd_gen_pkg::LoopsM3N0: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
        gen_rnd_instr(cmd_desc.cmd.main_1);
        gen_rnd_instr(cmd_desc.cmd.main_2);
      end
      aic_dp_cmd_gen_pkg::LoopsM3N1: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
        gen_rnd_instr(cmd_desc.cmd.main_1);
        gen_rnd_instr(cmd_desc.cmd.main_2);
        gen_rnd_instr(cmd_desc.cmd.nested_0);
      end
      aic_dp_cmd_gen_pkg::LoopsM3N2: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
        gen_rnd_instr(cmd_desc.cmd.main_1);
        gen_rnd_instr(cmd_desc.cmd.main_2);
        gen_rnd_instr(cmd_desc.cmd.nested_0);
        gen_rnd_instr(cmd_desc.cmd.nested_1);
      end
      default: begin
        gen_rnd_instr(cmd_desc.cmd.main_0);
        gen_rnd_instr(cmd_desc.cmd.nested_0);
      end

    endcase

    `uvm_info(get_name, "generated program:", UVM_HIGH)
    foreach (prog_mem[i]) 
      `uvm_info(get_name, $sformatf("prog mem[%0h]: %p", i, prog_mem[i]), UVM_HIGH)
  endfunction

  function void gen_rnd_instr(aic_dp_cmd_gen_pkg::loop_description_t loop_desc);
    int idx = $urandom_range(loop_desc.start, `_end_(loop_desc));
    assert(instr_seq.randomize() with {instr.src0 inside {[i0 : i1_f24]};});
    prog_mem[idx] = instr_seq.instr;

    assert(instr_seq.randomize() with {instr.dst inside {[l : l_f24]};});
    prog_mem[`_end_(loop_desc)] = instr_seq.instr;
  endfunction


  virtual task body();
    svt_axi_master_transaction write_tran;
    svt_configuration get_cfg;
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal(get_name, "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end
    foreach (prog_mem[i]) begin
      `uvm_create(write_tran)
      write_tran.port_cfg        = cfg;
      write_tran.xact_type       = svt_axi_transaction::WRITE;
      write_tran.burst_type      = svt_axi_transaction::INCR;
      write_tran.burst_size      = svt_axi_transaction::BURST_SIZE_32BIT;
      write_tran.atomic_type     = svt_axi_transaction::NORMAL;
      write_tran.burst_length    = 1;
      write_tran.data            = new[write_tran.burst_length];
      write_tran.wstrb           = new[write_tran.burst_length];
      write_tran.data_user       = new[write_tran.burst_length];
      write_tran.wvalid_delay    = new[write_tran.burst_length];
      write_tran.wstrb[0]        = 8'h0f;
      write_tran.wvalid_delay[0] = $urandom_range(0,2);
      write_tran.addr            = DPU_PRG_ADDR_ST + i* 4;
      write_tran.data[0]         = prog_mem[i];
      `uvm_info(get_name, $sformatf("writing instr @%0h, prog mem[%0h]: %p", write_tran.addr, i, prog_mem[i]), UVM_HIGH)

      `uvm_send(write_tran)
      get_response(rsp);
    end

  endtask

endclass


`endif
