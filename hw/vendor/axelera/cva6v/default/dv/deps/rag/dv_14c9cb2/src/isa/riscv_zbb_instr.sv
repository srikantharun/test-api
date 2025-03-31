/*
 * Copyright 2018 Google LLC
 * Copyright 2021 Silicon Labs, Inc.
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
class riscv_zbb_instr extends riscv_instr;
  `uvm_object_utils(riscv_zbb_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  virtual function void set_rand_mode();
    super.set_rand_mode();
    case (format) inside
      R_FORMAT: begin
        if (instr_name inside { ZEXT_H }) begin
          has_rs2 = 1'b0;
        end
      end

      I_FORMAT: begin
        if (instr_name inside { CLZ, CLZW, CTZ, CTZW, CPOP, CPOPW, ORC_B, SEXT_B, SEXT_H, REV8 })
        begin
          has_imm = 1'b0;
        end
      end

    endcase
  endfunction : set_rand_mode

  function void pre_randomize();
    super.pre_randomize();
  endfunction

  function bit is_rv64();
    is_rv64 = (group == RV64B);
  endfunction : is_rv64

  virtual function void set_imm_len();
    if (format inside {I_FORMAT}) begin
      if (instr_name inside {RORI}) begin
        imm_len = $clog2(XLEN);
      end else begin
        imm_len = 5;
      end
    end
    imm_mask = imm_mask << imm_len;
  endfunction : set_imm_len

  virtual function string convert2asm(string prefix = "");
    string asm_str_final;
    string asm_str;

    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);

    case (format)
      I_FORMAT : begin // instr rd rs1
        if (!has_imm) begin
          asm_str_final = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs1.name());
        end
      end

      R_FORMAT : begin // instr rd rs1
        if (!has_rs2) begin
          asm_str_final = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs1.name());
        end
      end

      default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
    endcase

    if (asm_str_final == "") begin
      return super.convert2asm(prefix);
    end

    if (comment != "") begin
      asm_str_final = { asm_str_final, " #", comment };
    end

    return asm_str_final.tolower();

  endfunction : convert2asm

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    return (cfg.enable_zbb_extension &&
           (RV32ZBB inside { supported_isa } || RV64ZBB inside { supported_isa }) &&
           instr_name inside {
             ANDN,
             CLZ, CLZW,
             CPOP, CPOPW,
             CTZ, CTZW,
             MAX, MAXU,
             MIN, MINU,
             ORC_B, ORN,
             REV8,
             ROL, ROLW,
             ROR, RORW,
             RORI, RORIW,
             SEXT_B, SEXT_H,
             XNOR,
             ZEXT_H
           });
  endfunction : is_supported

  virtual function void update_src_regs(string operands[$]);
    // All ZBB I_FORMAT instructions other than RORI use the immediate to specify the operation,
    // rather than being an explicit operand. Handle this case here, otherwise use the normal
    // `update_src_regs`
    if ((format == I_FORMAT) && (instr_name != RORI)) begin
      `DV_CHECK_FATAL(operands.size() == 2, instr_name)
      rs1 = get_gpr(operands[1]);
      rs1_value = get_gpr_state(operands[1]);
    end else begin
      super.update_src_regs(operands);
    end
  endfunction : update_src_regs

endclass : riscv_zbb_instr
