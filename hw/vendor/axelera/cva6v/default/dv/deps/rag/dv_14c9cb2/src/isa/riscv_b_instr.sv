/*
 * Copyright 2019 Google LLC
 * Copyright 2019 Mellanox Technologies Ltd
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

class riscv_b_instr extends riscv_instr;

  rand riscv_reg_t rs3;
  bit has_rs3 = 1'b0;

  `uvm_object_utils(riscv_b_instr)

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void set_rand_mode();
    super.set_rand_mode();
    has_rs3 = 1'b0;
    case (format) inside
      R_FORMAT: begin
        if (instr_name inside {BMATFLIP,
                               CRC32_B, CRC32_H, CRC32_W, CRC32C_B, CRC32C_H, CRC32C_W, CRC32_D,
                               CRC32C_D}) begin
          has_rs2 = 1'b0;
        end
      end
      R4_FORMAT: begin
        has_imm = 1'b0;
        has_rs3 = 1'b1;
      end
      I_FORMAT: begin
        has_rs2 = 1'b0;
        if (instr_name inside {FSRI, FSRIW}) begin
          has_rs3 = 1'b1;
        end
      end
    endcase

  endfunction

  function void pre_randomize();
    super.pre_randomize();
    rs3.rand_mode(has_rs3);
  endfunction


  virtual function void set_imm_len();

    if (format inside {I_FORMAT}) begin
      if (category inside {SHIFT, LOGICAL}) begin
        imm_len = $clog2(XLEN);
      end
      // ARITHMETIC RV32B
      if (instr_name inside {SHFLI, UNSHFLI}) begin
        imm_len = $clog2(XLEN) - 1;
      end
    end

    imm_mask = imm_mask << imm_len;
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str_final, asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);

    case (format)
      I_FORMAT: begin
        if (instr_name inside {FSRI, FSRIW}) begin  // instr rd,rs1,rs3,imm
          asm_str_final = $sformatf("%0s%0s, %0s, %0s, %0s", asm_str, rd.name(), rs1.name(),
                                    rs3.name(), get_imm());
        end
      end

      R_FORMAT: begin  //instr rd rs1
        if (!has_rs2) begin
          asm_str_final = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs1.name());
        end
      end

      R4_FORMAT: begin  // instr rd,rs1,rs2,rs3
        asm_str_final = $sformatf("%0s%0s, %0s, %0s, %0s", asm_str, rd.name(), rs1.name(),
                                  rs2.name(), rs3.name());
      end
      default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
    endcase

    if (asm_str_final == "") begin
      return super.convert2asm(prefix);
    end

    if (comment != "") asm_str_final = {asm_str_final, " #", comment};
    return asm_str_final.tolower();
  endfunction

  virtual function void do_copy(uvm_object rhs);
    riscv_b_instr rhs_;
    super.copy(rhs);
    assert($cast(rhs_, rhs));
    this.rs3 = rhs_.rs3;
    this.has_rs3 = rhs_.has_rs3;
  endfunction : do_copy

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    return cfg.enable_b_extension && (
           (ZBP inside {cfg.enable_bitmanip_groups} && instr_name inside {
               GREV, GREVW, GREVI, GREVIW,
               GORC, GORCW, GORCI, GORCIW,
               SHFL, SHFLW, UNSHFL, UNSHFLW, SHFLI, UNSHFLI,
               XPERM_N, XPERM_B, XPERM_H, XPERM_W,
               SLO, SLOW, SLOI, SLOIW,
               SRO, SROW, SROI, SROIW
               }) ||
           (ZBE inside {cfg.enable_bitmanip_groups} && instr_name inside {
               BCOMPRESS, BCOMPRESSW,
               BDECOMPRESS, BDECOMPRESSW
               }) ||
           (ZBF inside {cfg.enable_bitmanip_groups} && instr_name inside {BFP, BFPW}) ||
           (ZBR inside {cfg.enable_bitmanip_groups} && instr_name inside {
               CRC32_B, CRC32_H, CRC32_W, CRC32_D,
               CRC32C_B, CRC32C_H, CRC32C_W, CRC32C_D
               }) ||
           (ZBM inside {cfg.enable_bitmanip_groups} && instr_name inside {
               BMATOR, BMATXOR, BMATFLIP
               }) ||
           (ZBT inside {cfg.enable_bitmanip_groups} && instr_name inside {
               CMOV, CMIX,
               FSL, FSLW, FSR, FSRW, FSRI, FSRIW})
           );
  endfunction

  // coverage related functons
  virtual function void update_src_regs(string operands[$]);
    // handle special I_FORMAT (FSRI, FSRIW) and R4_FORMAT
    case(format)
      I_FORMAT: begin
        if (instr_name inside {FSRI, FSRIW}) begin
          `DV_CHECK_FATAL(operands.size() == 4, instr_name)
          // fsri rd, rs1, rs3, imm
          rs1 = get_gpr(operands[1]);
          rs1_value = get_gpr_state(operands[1]);
          rs3 = get_gpr(operands[2]);
          rs3_value = get_gpr_state(operands[2]);
          get_val(operands[3], imm);
          return;
        end
      end
      R4_FORMAT: begin
        `DV_CHECK_FATAL(operands.size() == 4)
        rs1 = get_gpr(operands[1]);
        rs1_value = get_gpr_state(operands[1]);
        rs2 = get_gpr(operands[2]);
        rs2_value = get_gpr_state(operands[2]);
        rs3 = get_gpr(operands[3]);
        rs3_value = get_gpr_state(operands[3]);
        return;
      end
      default: ;
    endcase
    // reuse base function to handle the other instructions
    super.update_src_regs(operands);
  endfunction : update_src_regs

endclass



