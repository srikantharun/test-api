/*
 * Copyright 2020 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

class riscv_compressed_instr extends riscv_instr;

  int imm_align;

  constraint rvc_csr_c {
    //  Registers specified by the three-bit rs1’, rs2’, and rd’
    if (format inside {CIW_FORMAT, CL_FORMAT, CS_FORMAT, CB_FORMAT, CA_FORMAT}) {
      if (has_rs1) {
        rs1 inside {[S0:A5]};
      }
      if (has_rs2) {
        rs2 inside {[S0:A5]};
      }
      if (has_rd) {
        rd inside {[S0:A5]};
      }
    }
    // C_ADDI16SP is only valid when rd == SP
    if (instr_name == C_ADDI16SP) {
      rd  == SP;
    }
    if (instr_name inside {C_JR, C_JALR}) {
      rs2 == ZERO;
      rs1 != ZERO;
    }
  }

  constraint imm_val_c {
    if(imm_type inside {NZIMM, NZUIMM}) {
      imm[5:0] != 0;
      if (instr_name == C_LUI) {
        // TODO(taliu) Check why bit 6 cannot be zero
        imm[31:5] == 0;
      }
      if (instr_name inside {C_SRAI, C_SRLI, C_SLLI}) {
        imm[31:5] == 0;
      }
    }
    if (instr_name == C_ADDI4SPN) {
      imm[1:0] == 0;
    }
  }

  // C_JAL is RV32C only instruction
  constraint jal_c {
    if (XLEN != 32) {
      instr_name != C_JAL;
    }
  }

  // Avoid generating HINT or illegal instruction by default as it's not supported by the compiler
  constraint no_hint_illegal_instr_c {
    if (instr_name inside {C_ADDI, C_ADDIW, C_LI, C_LUI, C_SLLI, C_SLLI64,
                           C_LQSP, C_LDSP, C_MV, C_ADD, C_LWSP}) {
      rd != ZERO;
    }
    if (instr_name == C_JR) {
      rs1 != ZERO;
    }
    if (instr_name inside {C_ADD, C_MV}) {
      rs2 != ZERO;
    }
    (instr_name == C_LUI) -> (rd != SP);
  }

  `uvm_object_utils(riscv_compressed_instr)

  function new(string name = "");
    super.new(name);
    rs1 = S0;
    rs2 = S0;
    rd  = S0;
    is_compressed = 1'b1;
  endfunction : new

  virtual function void set_imm_len();
    if (format inside {CI_FORMAT, CSS_FORMAT}) begin
      imm_len = 6;
    end else if (format inside {CL_FORMAT, CS_FORMAT}) begin
      imm_len = 5;
    end else if (format inside {CJ_FORMAT}) begin
      imm_len = 11;
    end else if (format inside {CB_FORMAT}) begin
      if (instr_name == C_ANDI) begin
        imm_len = 6;
      end else begin
        imm_len = 7;
      end
    end else if (format inside {CB_FORMAT, CIW_FORMAT}) begin
      imm_len = 8;
    end
    if (instr_name inside {C_SQ, C_LQ, C_LQSP, C_SQSP, C_ADDI16SP}) begin
      imm_align = 4;
    end else if (instr_name inside {C_SD, C_LD, C_LDSP, C_SDSP}) begin
      imm_align = 3;
    end else if (instr_name inside {C_SW, C_LW, C_LWSP, C_SWSP, C_ADDI4SPN}) begin
      imm_align = 2;
    end else if (instr_name inside {C_LUI}) begin
      imm_align = 12;
    end else if (instr_name inside {C_J, C_JAL, C_BNEZ, C_BEQZ}) begin
      imm_align = 1;
    end
  endfunction : set_imm_len

  virtual function riscv_instr do_clone();
    riscv_compressed_instr item;

    if(!$cast(item, this.clone()))
      `uvm_fatal(get_full_name(), "Clone failed")

    return item;
  endfunction

/*
  virtual function void do_copy(uvm_object rhs);
    riscv_compressed_instr rhs_;
    super.copy(rhs);
    assert($cast(rhs_, rhs));
    this.imm_align = rhs_.imm_align;
  endfunction : do_copy
*/

  virtual function void extend_imm();
    if (instr_name != C_LUI) begin
      super.extend_imm();
      imm = imm << imm_align;
    end
  endfunction : extend_imm

  virtual function void set_rand_mode();
    case (format) inside
      CR_FORMAT : begin
        if (category == JUMP) begin
          has_rd = 1'b0;
        end else begin
          has_rs1 = 1'b0;
        end
        has_imm = 1'b0;
      end
      CSS_FORMAT : begin
        has_rs1 = 1'b0;
        has_rd  = 1'b0;
      end
      CL_FORMAT: begin
        has_rs2 = 1'b0;
      end
      CS_FORMAT : begin
        has_rd = 1'b0;
      end
      CA_FORMAT: begin
        has_rs1 = 1'b0;
        has_imm = 1'b0;
      end
      CI_FORMAT, CIW_FORMAT: begin
        has_rs1 = 1'b0;
        has_rs2 = 1'b0;
      end
      CJ_FORMAT: begin
        has_rs1 = 1'b0;
        has_rs2 = 1'b0;
        has_rd  = 1'b0;
      end
      CB_FORMAT: begin
        if (instr_name != C_ANDI) has_rd = 1'b0;
        has_rs2 = 1'b0;
      end
    endcase
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    if (category != SYSTEM) begin
      case(format)
        CI_FORMAT, CIW_FORMAT:
          if (instr_name == C_NOP)
            asm_str = "c.nop";
          else if (instr_name == C_ADDI16SP)
            asm_str = $sformatf("%0ssp, %0s", asm_str, get_imm());
          else if (instr_name == C_ADDI4SPN)
            asm_str = $sformatf("%0s%0s, sp, %0s", asm_str, rd.name(), get_imm());
          else if (instr_name inside {C_LDSP, C_LWSP, C_LQSP})
            asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, rd.name(), get_imm());
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
        CL_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
        CS_FORMAT:
          if (category == STORE)
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), rs2.name());
        CA_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
        CB_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), get_imm());
        CSS_FORMAT:
          if (category == STORE)
            asm_str = $sformatf("%0s%0s, %0s(sp)", asm_str, rs2.name(), get_imm());
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rs2.name(), get_imm());
        CR_FORMAT:
          if (instr_name inside {C_JR, C_JALR}) begin
            asm_str = $sformatf("%0s%0s", asm_str, rs1.name());
          end else begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
          end
        CJ_FORMAT:
          asm_str = $sformatf("%0s%0s", asm_str, get_imm());
        default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
      endcase
    end else begin
      // For EBREAK,C.EBREAK, making sure pc+4 is a valid instruction boundary
      // This is needed to resume execution from epc+4 after ebreak handling
      if (instr_name == C_EBREAK) begin
        asm_str = "c.ebreak;c.nop;";
      end
    end
    if (comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction : convert2asm

  // Convert the instruction to assembly code
  virtual function string convert2bin(string prefix = "");
    string binary;
    case (instr_name) inside
      C_ADDI4SPN:
        binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[9:6],
                                   imm[2], imm[3], get_c_gpr(rd), get_c_opcode()});
      C_LQ:
        binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[8],
                                   get_c_gpr(rs1), imm[7:6], get_c_gpr(rd), get_c_opcode()});
      C_LD:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[7:6], get_c_gpr(rd), get_c_opcode()});
      C_LW:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[2], imm[6], get_c_gpr(rd), get_c_opcode()});
      C_SQ:
        binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[8],
                                   get_c_gpr(rs1), imm[7:6], get_c_gpr(rs2), get_c_opcode()});
      C_SD:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[7:6], get_c_gpr(rs2), get_c_opcode()});
      C_SW:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                   imm[2], imm[6], get_c_gpr(rs2), get_c_opcode()});
      C_NOP, C_ADDI, C_LI, C_ADDIW:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
      C_JAL, C_J:
        binary = $sformatf("%4h", {get_func3(), imm[11], imm[4], imm[9:8],
                                   imm[10], imm[6], imm[7], imm[3:1], imm[5], get_c_opcode()});
      C_ADDI16SP:
        binary = $sformatf("%4h", {get_func3(), imm[9], 5'b00010,
                                   imm[4], imm[6], imm[8:7], imm[5], get_c_opcode()});
      C_LUI:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
      C_SRLI:
        binary = $sformatf("%4h", {get_func3(), imm[5],
                                   2'b0, get_c_gpr(rd), imm[4:0], get_c_opcode()});
      C_SRLI64:
        binary = $sformatf("%4h", {get_func3(), 3'b0, get_c_gpr(rd), 5'b0, get_c_opcode()});
      C_SRAI:
        binary = $sformatf("%4h", {get_func3(), imm[5],
                                   2'b01, get_c_gpr(rd), imm[4:0], get_c_opcode()});
      C_SRAI64:
        binary = $sformatf("%4h", {get_func3(), 3'b001,
                                   get_c_gpr(rd), 5'b0, get_c_opcode()});
      C_ANDI:
        binary = $sformatf("%4h", {get_func3(), imm[5],
                                   2'b10, get_c_gpr(rd), imm[4:0], get_c_opcode()});
      C_SUB:
        binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                   2'b00, get_c_gpr(rs2), get_c_opcode()});
      C_XOR:
        binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                   2'b01, get_c_gpr(rs2), get_c_opcode()});
      C_OR:
        binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                   2'b10, get_c_gpr(rs2), get_c_opcode()});
      C_AND:
        binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                   2'b11, get_c_gpr(rs2), get_c_opcode()});
      C_SUBW:
        binary = $sformatf("%4h", {get_func3(), 3'b111, get_c_gpr(rd),
                                   2'b00, get_c_gpr(rs2), get_c_opcode()});
      C_ADDW:
        binary = $sformatf("%4h", {get_func3(), 3'b111, get_c_gpr(rd),
                                   2'b01, get_c_gpr(rs2), get_c_opcode()});
      C_BEQZ, C_BNEZ:
        binary = $sformatf("%4h", {get_func3(), imm[8], imm[4:3],
                                   get_c_gpr(rs1), imm[7:6], imm[2:1], imm[5], get_c_opcode()});
      C_SLLI:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
      C_SLLI64:
        binary = $sformatf("%4h", {get_func3(), 1'b0, rd, 5'b0, get_c_opcode()});
      C_LDSP:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:3], imm[8:6], get_c_opcode()});
      C_LQSP:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4], imm[9:6], get_c_opcode()});
      C_LWSP:
        binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:2], imm[7:6], get_c_opcode()});
      C_JR:
        binary = $sformatf("%4h", {get_func3(), 1'b0, rs1, 5'b0, get_c_opcode()});
      C_MV:
        binary = $sformatf("%4h", {get_func3(), 1'b0, rd, rs2, get_c_opcode()});
      C_EBREAK:
        binary = $sformatf("%4h", {get_func3(), 1'b1, 10'b0, get_c_opcode()});
      C_JALR:
        binary = $sformatf("%4h", {get_func3(), 1'b1, rs1, 5'b0, get_c_opcode()});
      C_ADD:
        binary = $sformatf("%4h", {get_func3(), 1'b1, rd, rs2, get_c_opcode()});
      C_SDSP:
        binary = $sformatf("%4h", {get_func3(), imm[5:3], imm[8:6], rs2, get_c_opcode()});
      C_SQSP:
        binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[9:6], rs2, get_c_opcode()});
      C_SWSP:
        binary = $sformatf("%4h", {get_func3(), imm[5:2], imm[7:6], rs2, get_c_opcode()});
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
    return {prefix, binary};
  endfunction : convert2bin

  // Get opcode for compressed instruction
  virtual function bit [1:0] get_c_opcode();
    case (instr_name) inside
      C_ADDI4SPN, C_LQ, C_LW,
      C_LD, C_SQ, C_SW, C_SD                          : get_c_opcode = 2'b00;
      C_NOP, C_ADDI, C_JAL, C_ADDIW, C_LI, C_ADDI16SP,
      C_LUI, C_SRLI, C_SRLI64, C_SRAI, C_SRAI64,
      C_ANDI, C_SUB, C_XOR, C_OR, C_AND, C_SUBW,
      C_ADDW, C_J, C_BEQZ, C_BNEZ                     : get_c_opcode = 2'b01;
      C_SLLI, C_SLLI64, C_LQSP, C_LWSP,
      C_LDSP, C_JR, C_MV, C_EBREAK, C_JALR,
      C_ADD, C_SQSP, C_SWSP, C_SDSP                   : get_c_opcode = 2'b10;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction : get_c_opcode

  virtual function bit [2:0] get_func3();
    case (instr_name) inside
      C_ADDI4SPN : get_func3 = 3'b000;
      C_LQ       : get_func3 = 3'b001;
      C_LW       : get_func3 = 3'b010;
      C_LD       : get_func3 = 3'b011;
      C_SQ       : get_func3 = 3'b101;
      C_SW       : get_func3 = 3'b110;
      C_SD       : get_func3 = 3'b111;
      C_NOP      : get_func3 = 3'b000;
      C_ADDI     : get_func3 = 3'b000;
      C_JAL      : get_func3 = 3'b001;
      C_ADDIW    : get_func3 = 3'b001;
      C_LI       : get_func3 = 3'b010;
      C_ADDI16SP : get_func3 = 3'b011;
      C_LUI      : get_func3 = 3'b011;
      C_SRLI     : get_func3 = 3'b100;
      C_SRLI64   : get_func3 = 3'b100;
      C_SRAI     : get_func3 = 3'b100;
      C_SRAI64   : get_func3 = 3'b100;
      C_ANDI     : get_func3 = 3'b100;
      C_SUB      : get_func3 = 3'b100;
      C_XOR      : get_func3 = 3'b100;
      C_OR       : get_func3 = 3'b100;
      C_AND      : get_func3 = 3'b100;
      C_SUBW     : get_func3 = 3'b100;
      C_ADDW     : get_func3 = 3'b100;
      C_J        : get_func3 = 3'b101;
      C_BEQZ     : get_func3 = 3'b110;
      C_BNEZ     : get_func3 = 3'b111;
      C_SLLI     : get_func3 = 3'b000;
      C_SLLI64   : get_func3 = 3'b000;
      C_LQSP     : get_func3 = 3'b001;
      C_LWSP     : get_func3 = 3'b010;
      C_LDSP     : get_func3 = 3'b011;
      C_JR       : get_func3 = 3'b100;
      C_MV       : get_func3 = 3'b100;
      C_EBREAK   : get_func3 = 3'b100;
      C_JALR     : get_func3 = 3'b100;
      C_ADD      : get_func3 = 3'b100;
      C_SQSP     : get_func3 = 3'b101;
      C_SWSP     : get_func3 = 3'b110;
      C_SDSP     : get_func3 = 3'b111;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction : get_func3

  virtual function void do_copy(uvm_object rhs);
    riscv_compressed_instr rhs_;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");
    if(!$cast(rhs_, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.group                      = rhs_.group;
    this.format                     = rhs_.format;
    this.category                   = rhs_.category;
    this.instr_name                 = rhs_.instr_name;
    this.csr                        = rhs_.csr;
    this.rs2                        = rhs_.rs2;
    this.rs1                        = rhs_.rs1;
    this.rd                         = rhs_.rd;
    this.imm                        = rhs_.imm;
    this.imm_type                   = rhs_.imm_type;
    this.imm_len                    = rhs_.imm_len;
    this.imm_mask                   = rhs_.imm_mask;
    this.imm_str                    = rhs_.imm_str;
    this.is_compressed              = rhs_.is_compressed;
    this.is_branch_target           = rhs_.is_branch_target;
    this.has_label                  = rhs_.has_label;
    this.atomic                     = rhs_.atomic;
    this.branch_assigned            = rhs_.branch_assigned;
    this.process_load_store         = rhs_.process_load_store;
    this.is_illegal_instr           = rhs_.is_illegal_instr;
    this.is_hint_instr              = rhs_.is_hint_instr;
    this.is_floating_point          = rhs_.is_floating_point;
    this.comment                    = rhs_.comment;
    this.label                      = rhs_.label;
    this.is_local_numeric_label     = rhs_.is_local_numeric_label;
    this.idx                        = rhs_.idx;
    this.has_rs2                    = rhs_.has_rs2;
    this.has_rs1                    = rhs_.has_rs1;
    this.has_rd                     = rhs_.has_rd;
    this.has_imm                    = rhs_.has_imm;
    this.fs3                        = rhs_.fs3;
    this.fs2                        = rhs_.fs2;
    this.fs1                        = rhs_.fs1;
    this.fd                         = rhs_.fd;
    this.has_fs3                    = rhs_.has_fs3;
    this.has_fs2                    = rhs_.has_fs2;
    this.has_fs1                    = rhs_.has_fs1;
    this.has_fd                     = rhs_.has_fd;
    this.aq                         = rhs_.aq;
    this.rl                         = rhs_.rl;
    this.vs1                        = rhs_.vs1;
    this.vs2                        = rhs_.vs2;
    this.vs3                        = rhs_.vs3;
    this.vd                         = rhs_.vd;
    this.va_variant                 = rhs_.va_variant;
    this.vm                         = rhs_.vm;
    this.ls_eew                     = rhs_.ls_eew;
    this.nfields                    = rhs_.nfields;
    this.has_vs1                    = rhs_.has_vs1;
    this.has_vs2                    = rhs_.has_vs2;
    this.has_vs3                    = rhs_.has_vs3;
    this.has_vd                     = rhs_.has_vd;
    this.has_va_variant             = rhs_.has_va_variant;
    this.is_widening_instr          = rhs_.is_widening_instr;
    this.is_narrowing_instr         = rhs_.is_narrowing_instr;
    this.is_convert_instr           = rhs_.is_convert_instr;
    this.is_reduction_instr         = rhs_.is_reduction_instr;
    this.is_mask_producing_instr    = rhs_.is_mask_producing_instr;
    this.is_mask_operands           = rhs_.is_mask_operands;
    this.is_fp_instr                = rhs_.is_fp_instr;
    this.is_segmented_ls_instr      = rhs_.is_segmented_ls_instr;
    this.is_whole_register_ls_instr = rhs_.is_whole_register_ls_instr;
    this.ext_widening_factor        = rhs_.ext_widening_factor;
    this.whole_register_move_cnt    = rhs_.whole_register_move_cnt;
    this.allowed_va_variants        = rhs_.allowed_va_variants;
    this.ls_emul_non_frac           = rhs_.ls_emul_non_frac;
    this.imm_align                  = rhs_.imm_align;
  endfunction : do_copy

endclass : riscv_compressed_instr
