`ifndef DPU_INSTRUCTION_SEQUENCE
`define DPU_INSTRUCTION_SEQUENCE

class dpu_instruction_sequence extends svt_axi_master_base_sequence;

  `uvm_object_utils(dpu_instruction_sequence)

  rand bit [31:0] addr;
  rand dpu_pkg::dpu_dp_cmd_t instr;
  bit set_rfs = 0;

  constraint c_addr {
    addr inside {[DPU_PRG_ADDR_ST : DPU_PRG_ADDR_ST + PROG_MEM_DEPTH * 4]};
    addr % 4 == 0;
  }

  //TODO implement pseudo commands
  constraint c_instr {
    if (set_rfs) {
      instr.opcode inside {OPC_RFS,OPC_MADD_RFS};
    }
    else {
      instr.opcode dist {
        OPC_UNARY                := 60,
        [OPC_MV : OPC_LUT]       :/ 20,
        OPC_RFS                  := 10,
        [OPC_MUL : OPC_MADD_RFS] :/ 10
      };
    }

    //2 instruction types and the struct is packed, so need to fully constraint all the struct
    //components for both instr types
    if (instr.opcode inside {OPC_RFS, OPC_MADD_RFS}) { 
      instr.src0 inside {[i0 : i0_f24],[i1 : i1_f24]};

      instr.src1 dist {
        [i0   : i0_f24]  := 5,
        [pi0  : pi0_f24] := 3,
        [i1   : i1_f24]  := 5,
        [pi1  : pi1_f24] := 3,
        [a0   : a7]      :/ 20,
        [b_c0 : b_c63]   :/ 20
      };
  
      if (instr.opcode == OPC_RFS) {
        instr.src2 inside {[FUNC_NEG : FUNC_CMADD]}; 
      } 
      
      instr.dst inside {[o:l_f24]};
    }
    else {
      //more chance to source get input data
      //than internal regs
      instr.src0 dist {
        [i0 : i0_f24]  := 5,
        [pi0 : pi0_f24] := 3,
        [i1 : i1_f24]  := 5,
        [pi1 : pi1_f24] := 3,
        [a0 : a7]      :/ 20,
        [b_c0 : b_c63] :/ 20
      };

      if (instr.opcode == OPC_UNARY) {
        instr.src1 dist {
          FUNC_NOP :/1,
          [FUNC_MVCL : FUNC_SUMR] := 1
        };
        //mask_size
        instr.src2 inside {[0 : 63], [7'h40 : 7'h7F]}; //-64 to -1
      } 

      else if (instr.opcode == OPC_MV) {
        //mask_value_sel
        instr.src1 inside {[0 : 7'h7F]};
        //mask_size
        instr.src2 inside {[0 : 63], [7'h40 : 7'h7F]}; //-64 to -1
      }

      else if (instr.opcode inside {OPC_LUT, [OPC_MUL:OPC_CMADD]}) {
        if (instr.opcode == OPC_LUT) 
          instr.src2 inside {[FUNC_LUT: FUNC_CHLUT]};

        if (instr.opcode == OPC_LUT && instr.src2 inside {[FUNC_DLUT:FUNC_CHLUT]})
          instr.src1 inside {[0 : 63]};
        else {
          instr.src1 dist {
            [i0 : i0_f24]   := 5,
            [pi0 : pi0_f24] := 3,
            [i1 : i1_f24]   := 5,
            [pi1 : pi1_f24] := 3,
            [a0 : a7]      :/ 20,
            [b_c0 : b_c63] :/ 20
          };
        }  
        if (instr.opcode inside {[OPC_MUL: OPC_CMADD]}) {
          //   1      |   0    | desc
          //broadcast | offset | enable bits
          instr.src2[1:0] dist { 
            1 := 10,
            3 := 10,
            0 := 90
          };

          //offset/broadcast ctrl bits
          //0 : MAIN
          //1 : NESTED_0
          //2 : NESTED_1
          instr.src2[6:2] inside {[0:2]};
        }
      }

      else if (instr.opcode == OPC_MADD) {
        instr.src1 dist {
          [i0 : i0_f24]   := 5,
          [pi0 : pi0_f24] := 3,
          [i1 : i1_f24]   := 5,
          [pi1 : pi1_f24] := 3,
          [a0 : a7]      :/ 20,
          [b_c0 : b_c63] :/ 20
        };

        instr.src2 dist {
          [i0 : i0_f24]   := 5,
          [pi0 : pi0_f24] := 3,
          [i1 : i1_f24]   := 5,
          [pi1 : pi1_f24] := 3,
          [a0 : a7]      :/ 20,
          [b_c0 : b_c63] :/ 20
        };
      }

      //more chance to destination pushes data
      //than store in internal regs
      instr.dst dist {
        [o : o_f24]            := 5,
        [l : l_f24]            := 1,
        [dst_a0 : dst_a7]      :/ 20,
        [dst_b_c0 : dst_b_c63] :/ 20
      };
    }
  }

  

  //if LUT op with src1 = internal regs, a MV op is executed first, this constraint
  //avoids generation of MVs with src1 and src2 = a0, turning it exclusive to identify a
  //MV before LUT with src0 = internal regs
  constraint c_mv_for_lut_op {
    if (instr.opcode == OPC_MV) {
      soft instr.src1 != a0;
      soft instr.src2 != a0;
    }
  }


  function void post_randomize();
    instr_src_t num_srcs = get_instr_num_srcs(instr);
    bit src0_ifd0 = instr.src0 inside {[i0 : i0_f24], [pi0 : pi0_f24]};
    bit src1_ifd0 = instr.src1 inside {[i0 : i0_f24], [pi0 : pi0_f24]};
    bit src2_ifd0 = instr.src2 inside {[i0 : i0_f24], [pi0 : pi0_f24]};
    bit src0_ifd1 = instr.src0 inside {[i1 : i1_f24], [pi1 : pi1_f24]};
    bit src1_ifd1 = instr.src1 inside {[i1 : i1_f24], [pi1 : pi1_f24]};
    bit src2_ifd1 = instr.src2 inside {[i1 : i1_f24], [pi1 : pi1_f24]};

    //you cannot use different formats on the same stream in the same instruction
    //e.g <add a0, i0, i0-f16> is not valid
    if (num_srcs >= DUAL_INSTR_SRC) begin
      if ( src0_ifd0 && src1_ifd0 || src0_ifd1 && src1_ifd1)
        instr.src1 = instr.src0;
    end
    if (num_srcs == TRIPLE_INSTR_SRC) begin
      if ( src0_ifd0 && src2_ifd0 || src0_ifd1 && src2_ifd1)
        instr.src2 = instr.src0;
      else if ( src1_ifd0 && src2_ifd0 || src1_ifd1 && src2_ifd1)
        instr.src2 = instr.src1;
    end

    `uvm_info(get_name, $sformatf("rand instruction: %p", instr), UVM_HIGH)
  endfunction


  function new(string name = "dpu_instruction_sequence");
    super.new(name);
  endfunction


  virtual task body();
    svt_axi_master_transaction write_tran;
    svt_configuration get_cfg;

    instr_src_t num_srcs = get_instr_num_srcs(instr);

    //sources that get data from input feeders should use the same data format
    bit src0_ifd0 = instr.src0 inside {[i0 : i0_f24]};
    bit src1_ifd0 = num_srcs >= DUAL_INSTR_SRC && instr.src1 inside {[i0 : i0_f24]};
    bit src2_ifd0 = num_srcs == TRIPLE_INSTR_SRC && instr.src2 inside {[i0 : i0_f24]};

    bit src0_ifd1 = instr.src0 inside {[i1 : i1_f24]};
    bit src1_ifd1 = num_srcs >= DUAL_INSTR_SRC && instr.src1 inside {[i1 : i1_f24]};
    bit src2_ifd1 = num_srcs == TRIPLE_INSTR_SRC && instr.src2 inside {[i1 : i1_f24]};

    bit src0_diff_src1 = (src0_ifd0 && src1_ifd0 || src0_ifd1 && src1_ifd1) && instr.src0 != instr.src1;
    bit src0_diff_src2 = (src0_ifd0 && src2_ifd0 || src0_ifd1 && src2_ifd1) && instr.src0 != instr.src2;
    bit src1_diff_src2 = (src1_ifd0 && src2_ifd0 || src1_ifd1 && src2_ifd1) && instr.src1 != instr.src2;

    if ( src0_diff_src1 || src0_diff_src2 || src1_diff_src2 ) begin 
      `uvm_fatal(get_name, $sformatf("Error! If sources get data from the same  IFD, they should have the same data format, instr: %p", instr))
    end

    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg))
      `uvm_fatal(get_name, "Unable to $cast the configuration to a svt_axi_port_configuration class");

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
    write_tran.wstrb[0]        = 8'h0F;
    write_tran.wvalid_delay[0] = 0;
    write_tran.addr            = addr;
    write_tran.data[0]         = instr;

    `uvm_info(get_name, $sformatf("writing @%0h %0h  instruction: %p",addr,instr, instr), UVM_HIGH)
    `uvm_send(write_tran)
    get_response(rsp);
  endtask

endclass

`endif
