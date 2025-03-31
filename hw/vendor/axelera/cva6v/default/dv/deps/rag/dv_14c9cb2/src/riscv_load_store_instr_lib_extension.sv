/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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

class riscv_load_store_word_aligned_hazard_instr_stream extends riscv_hazard_instr_stream;

  `uvm_object_utils(riscv_load_store_word_aligned_hazard_instr_stream)
  `uvm_object_new

  virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i=0; i<num_load_store; i++) begin
      if (!std::randomize(offset_, addr_) with {
        if (locality == NARROW) {
          soft offset_ inside {[-16:16]};
        } else if (locality == HIGH) {
          soft offset_ inside {[-64:64]};
        } else if (locality == MEDIUM) {
          soft offset_ inside {[-256:256]};
        } else if (locality == SPARSE) {
          soft offset_ inside {[-2048:2047]};
        }
        addr_ == base + offset_;
        addr_ % 4 == 0; // WORD ALIGN
        addr_ inside {[0 : max_load_store_offset - 1]};
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize load/store offset")
      end
      offset[i] = offset_;
      addr[i] = addr_;
    end
  endfunction

endclass

// A random mix of load/store instructions combined with "events" to exercise hazards
class riscv_load_store_w_hazards_rand_instr_stream extends riscv_load_store_rand_addr_instr_stream;

  rand riscv_reg_t   rs1_hazard_reg; // "scratch" register
  int unsigned num_of_avail_regs = 10;
  int unsigned num_of_avail_fp_regs = 10;

  constraint rs1_hazard_c {
    !(rs1_hazard_reg inside {rs1_reg, cfg.reserved_regs, reserved_rd, ZERO});
  }

  constraint legal_c {
    num_load_store inside {[5:10]};
    num_mixed_instr inside {[10:100]};
  }

  `uvm_object_utils(riscv_load_store_w_hazards_rand_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    avail_regs = new[num_of_avail_regs];
    avail_fp_regs = new[num_of_avail_fp_regs];
    super.pre_randomize();
  endfunction

  function void post_randomize();
    randomize_offset();
    // rs1 & hazard backup reg cannot be modified by other instructions
    if(!(rs1_reg inside {reserved_rd})) begin
      reserved_rd = {reserved_rd, rs1_reg};
    end
    if(!(rs1_hazard_reg inside {reserved_rd})) begin
      reserved_rd = {reserved_rd, rs1_hazard_reg};
    end
    gen_load_store_instrs_w_hazards();
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);
    // Parent - class extended code
    foreach(instr_list[i]) begin
      // don't mute the jump/branch labels
      if (instr_list[i].label == "1") begin
        instr_list[i].has_label = 1'b1;
      end
      else begin
        instr_list[i].has_label = 1'b0;
      end
      instr_list[i].atomic = 1'b1;
    end
    instr_list[0].comment = $sformatf("Start %0s", get_name());
    instr_list[$].comment = $sformatf("End %0s", get_name());
    if(label != "") begin
      instr_list[0].label = label;
      instr_list[0].has_label = 1'b1;
    end
    `uvm_info(get_type_name(), "post_randomize called!", UVM_FULL)
  endfunction

  // Get random legal LD/ST instr, randomize it, set rs1 and immediate
  function riscv_instr get_and_randomize_load_store_instr(riscv_instr_name_t allowed_instr[$], riscv_reg_t rs1_reg, int offset);
    riscv_instr instr;
    instr = riscv_instr::get_load_store_instr(allowed_instr);
    instr.set_rand_mode();
    instr.has_rs1 = 0;
    instr.has_rs2 = 1;
    instr.has_fs2 = 1;
    instr.has_imm = 0;
    randomize_gpr(instr);
    instr.rs1 = rs1_reg;
    instr.imm_str = $sformatf("%0d", $signed(offset));
    instr.process_load_store = 0;
    return instr.do_clone();
  endfunction

  // Get a counterpart to the provided load instruction, randomize it and set rs1 + immediate
  function riscv_instr get_store_w_offset_instr(riscv_instr load_instr, int offset, string comment = "Load counterpart");
    riscv_instr_name_t store_instr_name;
    riscv_instr store_instr;
    case (load_instr.instr_name) inside
      LB, LBU : store_instr_name = SB;
      LH, LHU, FLH : store_instr_name = SH;
      LW, C_LW, C_LWSP, FLW, C_FLW, C_FLWSP : store_instr_name = SW;
      LD, C_LD, C_LDSP, FLD, C_FLD, LWU     : store_instr_name = SD;
      default : `uvm_fatal(`gfn, $sformatf("Cannot create store instr, counterpart for %s", load_instr.instr_name))
    endcase
    store_instr = riscv_instr::get_instr(store_instr_name);
    store_instr.has_rs1 = 0;
    store_instr.has_rs2 = 1; // randomize rs2
    store_instr.has_fs2 = 1; // randomize fs2
    store_instr.has_imm = 0;
    randomize_gpr(store_instr);
    store_instr.rs1 = load_instr.rs1;
    store_instr.imm_str = $sformatf("%0d", $signed(offset));
    store_instr.comment = comment;
    return store_instr.do_clone();
    //return store_instr;
  endfunction

  // Get a counterpart to the provided store instruction, randomize it and set rs1 + immediate
  function riscv_instr get_load_w_offset_instr(riscv_instr store_instr, int offset, string comment = "Store counterpart");
    riscv_instr_name_t load_instr_names[$];
    riscv_instr_name_t load_instr_name;
    riscv_instr load_instr;
    case (store_instr.instr_name) inside
      SB: load_instr_names = {LB, LBU};
      SH: load_instr_names = {LH, LHU};
      SW: load_instr_names = {LW, LWU};
      SD: load_instr_names = {LD, LWU};
      FSH: load_instr_names = {FLH};
      FSW: load_instr_names = {FLW};
      FSD: load_instr_names = {FLD};
      C_SW: load_instr_names = {C_LW};
      C_SWSP: load_instr_names = {C_LWSP};
      C_SD: load_instr_names = {C_LD};
      C_SDSP: load_instr_names = {C_LDSP};
      C_FSW: load_instr_names = {C_FLW};
      C_FSWSP: load_instr_names = {C_FLWSP};
      C_FSD: load_instr_names = {C_FLD};
      C_FSDSP: load_instr_names = {C_FLDSP};
      default : `uvm_fatal(`gfn, $sformatf("Cannot create load instruction, counterpart for %s", store_instr.instr_name))
    endcase
    if (!std::randomize(load_instr_name) with {
        load_instr_name inside {load_instr_names};
      }
    ) begin
      `uvm_fatal(`gfn, "Cannot randomize store instruction counterpart")
    end
    load_instr = riscv_instr::get_instr(load_instr_name);
    load_instr.has_rs1 = 0;
    load_instr.has_imm = 0;
    randomize_gpr(load_instr);
    load_instr.rs1 = store_instr.rs1;
    load_instr.imm_str = $sformatf("%0d", $signed(offset));
    load_instr.comment = comment;
    //return load_instr;
    return load_instr.do_clone();
  endfunction

  function void switch_dcache_state(ref dcache_state_t dcache_state, ref riscv_instr instr_list[$], riscv_reg_t avail_gpr);
    riscv_pseudo_instr li_dcache_bits_instr;
    riscv_instr dcache_switch_instr;
    li_dcache_bits_instr = riscv_common_functions::get_li_instr(.rd(avail_gpr), .imm_str("0x1")); // LSB
    if (dcache_state == ENABLED) begin
      dcache_switch_instr = riscv_common_functions::get_dcache_disable_instr(.rs1(avail_gpr));
      dcache_state = DISABLED;
    end else begin
      dcache_switch_instr = riscv_common_functions::get_dcache_enable_instr(.rs1(avail_gpr));
      dcache_state = ENABLED;
    end
    instr_list.push_back(li_dcache_bits_instr);
    instr_list.push_back(dcache_switch_instr);
  endfunction: switch_dcache_state

  // Generate each load/store instruction w hazards on address reg
  virtual function void gen_load_store_instrs_w_hazards();
    bit enable_compressed_load_store;
    riscv_instr instr;
    int hazard_offset;
    int increasing_offset;
    int offset_sign;
    int accumulated_offset;
    int repetition_steps;
    uvm_comparer comparer;
    jump_branch_state_t jump_branch_state = HAS_TARGET_LABEL;
    dcache_state_t dcache_state = ENABLED;

    randomize_avail_regs();
    if ((rs1_reg inside {[S0 : A5], SP}) && !cfg.disable_compressed_instr) begin
      enable_compressed_load_store = 1;
    end
    foreach (addr[i]) begin
      // Assign the allowed load/store instructions based on address alignment
      // This is done separately rather than a constraint to improve the randomization performance
      allowed_instr = {LB, LBU, SB};
      if (!cfg.enable_misaligned_load_store) begin
        if (addr[i][0] == 1'b0) begin
          allowed_instr = {LH, LHU, SH, allowed_instr};
        end
        if (addr[i] % 4 == 0) begin
          allowed_instr = {LW, SW, allowed_instr};
          if (cfg.enable_fp_extension) begin
            allowed_instr = {FLH, FSH, FLW, FSW, allowed_instr};
          end
          if((offset[i] inside {[0:127]}) && (offset[i] % 4 == 0) &&
             (RV32C inside {riscv_instr_pkg::supported_isa}) &&
             enable_compressed_load_store) begin
            if (rs1_reg == SP) begin
              //`uvm_info(`gfn, "RS1 == SP, adding LWSP/SWSP to allowed instr", UVM_LOW)
              allowed_instr = {C_LWSP, C_SWSP};
            end else begin
              allowed_instr = {C_LW, C_SW, allowed_instr};
              if (cfg.enable_fp_extension && (RV32FC inside {supported_isa})) begin
                allowed_instr = {C_FLW, C_FSW, allowed_instr};
              end
            end
          end
        end
        if ((XLEN >= 64) && (addr[i] % 8 == 0)) begin
          allowed_instr = {LWU, LD, SD, allowed_instr};
          if (cfg.enable_fp_extension && (RV32D inside {supported_isa})) begin
            allowed_instr = {FLD, FSD, allowed_instr};
          end
          if((offset[i] inside {[0:255]}) && (offset[i] % 8 == 0) &&
             (RV64C inside {riscv_instr_pkg::supported_isa} &&
             enable_compressed_load_store)) begin
            if (rs1_reg == SP) begin
              allowed_instr = {C_LDSP, C_SDSP};
            end else begin
              allowed_instr = {C_LD, C_SD, allowed_instr};
              if (cfg.enable_fp_extension && (RV32DC inside {supported_isa})) begin
                allowed_instr = {C_FLD, C_FSD, allowed_instr};
              end
            end
          end
        end
      end else begin // misaligned load/store
        allowed_instr = {LW, SW, LH, LHU, SH, allowed_instr};
        if (cfg.enable_fp_extension) begin
          allowed_instr = {FLH, FSH, FLW, FSW, allowed_instr};
        end
        // Compressed load/store still needs to be aligned
        if ((offset[i] inside {[0:127]}) && (offset[i] % 4 == 0) &&
            (RV32C inside {riscv_instr_pkg::supported_isa}) &&
            enable_compressed_load_store) begin
            if (rs1_reg == SP) begin
              allowed_instr = {C_LWSP, C_SWSP};
            end else begin
              allowed_instr = {C_LW, C_SW, allowed_instr};
            end
        end
        if (XLEN >= 64) begin
          allowed_instr = {LWU, LD, SD, allowed_instr};
          if ((offset[i] inside {[0:255]}) && (offset[i] % 8 == 0) &&
              (RV64C inside {riscv_instr_pkg::supported_isa}) &&
              enable_compressed_load_store) begin
              if (rs1_reg == SP) begin
                allowed_instr = {C_LWSP, C_SWSP};
              end else begin
                allowed_instr = {C_LD, C_SD, allowed_instr};
              end
           end
        end
      end

      // Get the "OG" LD/ST like in other classes
      instr = get_and_randomize_load_store_instr(allowed_instr, rs1_reg, offset[i]);
      instr.comment = $sformatf("og LD/ST no %d offset %d", i, offset[i]);
      //assert (instr.rs1 == rs1_reg)
      //  else $fatal("instr %p rs1 %p is not equal to requested %p", instr.instr_name, instr.rs1, rs1_reg);
      //`uvm_info(`gfn, $sformatf("og_instr %s ", instr.convert2string()), UVM_NONE)

      // Forward branch / jump events
      randcase
        5: begin
          instr_list.push_back(riscv_common_functions::get_forward_jump_instr());
          jump_branch_state = NEEDS_TARGET_LABEL;
        end
        5: begin
          instr_list.push_back(riscv_common_functions::get_random_forward_branch_instr());
          jump_branch_state = NEEDS_TARGET_LABEL;
        end
        50: begin
          if (jump_branch_state == NEEDS_TARGET_LABEL) begin
            instr_list[$].label = "1"; // end jump here
            instr_list[$].has_label = 1;
            jump_branch_state = HAS_TARGET_LABEL;
          end
        end
        40: ;
      endcase

      // Address register manipulation events
      if (!std::randomize(hazard_offset) with {
        if (locality == NARROW) {
          soft hazard_offset inside {[-16:16]};
        } else if (locality == HIGH) {
          soft hazard_offset inside {[-64:64]};
        } else if (locality == MEDIUM) {
          soft hazard_offset inside {[-256:256]};
        } else if (locality == SPARSE) {
          soft hazard_offset inside {[-2048:2047]};
        }
        addr[i]+hazard_offset inside {[0 : max_load_store_offset-1]}; // don't overdo it ; )
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize hazard load/store offset")
      end
      randcase
        3: begin
          if (cfg.init_privileged_mode == MACHINE_MODE) begin
            switch_dcache_state(.dcache_state(dcache_state), .instr_list(instr_list), .avail_gpr(avail_regs[0]));
            if (jump_branch_state == NEEDS_TARGET_LABEL) begin
              dcache_state = DISABLED; // since we skip over this with jump
            end
          end
        end
        10: begin // I type to LD/ST
          riscv_instr addi_instr;
          riscv_instr subi_instr;
          addi_instr = riscv_instr::get_instr(ADDI);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(addi_instr,
            rs1 == rs1_reg;
            rd  == rs1_reg;
            imm == hazard_offset;
          )
          subi_instr = riscv_instr::get_instr(ADDI);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(subi_instr,
            rs1 == rs1_reg;
            rd  == rs1_reg;
            imm == -hazard_offset;
          )
          addi_instr.comment = $sformatf("Addi for LD/ST no %d", i);
          instr_list.push_back(addi_instr);
          subi_instr.comment = $sformatf("Subi for LD/ST no %d", i);
          instr_list.push_back(subi_instr);
        end
        20: begin // R type to LD/ST
          riscv_instr addi_instr;
          riscv_instr subi_instr;
          riscv_instr mov_instr;
          addi_instr = riscv_instr::get_instr(ADDI);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(addi_instr,
            rd  == rs1_hazard_reg;
            rs1 == rs1_reg;
            imm == hazard_offset;
          )
          subi_instr = riscv_instr::get_instr(ADDI);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(subi_instr,
            rd  == rs1_hazard_reg;
            rs1 == rs1_hazard_reg;
            imm == -hazard_offset;
          )
          mov_instr = riscv_instr::get_instr(ADD);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(mov_instr,
            rd  == rs1_reg;
            rs1 == rs1_hazard_reg;
            rs2 == 0;
          )
          addi_instr.comment = $sformatf("Addi to another reg for LD/ST no %d", i);
          instr_list.push_back(addi_instr);
          subi_instr.comment = $sformatf("Subi in another reg for LD/ST no %d", i);
          instr_list.push_back(subi_instr);
          mov_instr.comment = $sformatf("Mov back for LD/ST no %d", i);
          instr_list.push_back(mov_instr);
        end
        20: begin  // another I type to LD/ST
          riscv_instr slli_instr;
          riscv_instr srli_instr;
          slli_instr = riscv_instr::get_instr(SLLI);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(slli_instr,
            rs1 == rs1_reg;
            rd  == rs1_reg;
            imm == 1;
          )
          srli_instr = riscv_instr::get_instr(SRLI);
          `DV_CHECK_RANDOMIZE_WITH_FATAL(srli_instr,
            rs1 == rs1_reg;
            rd  == rs1_reg;
            imm == 1;
          )
          slli_instr.comment = $sformatf("SLLI for LD/ST no %d", i);
          instr_list.push_back(slli_instr);
          srli_instr.comment = $sformatf("SRLI for LD/ST no %d", i);
          instr_list.push_back(srli_instr);
        end
        25: begin
          if (cfg.init_privileged_mode == MACHINE_MODE) begin
            if (dcache_state == DISABLED) begin
              switch_dcache_state(.dcache_state(dcache_state), .instr_list(instr_list), .avail_gpr(avail_regs[0]));
            end
          end
        end
        25: ;
      endcase

      // Repetition events
      accumulated_offset = 0;
      if (!std::randomize(increasing_offset) with {
        increasing_offset inside {4, 8, 16, 32};
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize increasing load/store offset")
      end
      if (!std::randomize(repetition_steps) with {
        repetition_steps inside {2, 3, 4};
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize load/store repetition steps")
      end

      randcase
        10: begin // Issue LD/ST twice
          riscv_instr extra_instr;
          extra_instr = riscv_instr::get_instr(instr.instr_name);
          extra_instr.do_copy(instr);
          if (!extra_instr.do_compare(instr, comparer)) begin
            `uvm_fatal(`gfn, $sformatf("do_copy failed! Exp: %s Act: %s", instr.convert2string(), extra_instr.convert2string()))
          end
          extra_instr.comment = $sformatf("repeated LD/ST no %d", i);
          instr_list.push_back(instr);
          load_store_instr.push_back(instr);
          instr_list.push_back(extra_instr); // repeat the same instruction
        end
        10: begin // Extra LD/ST, different RD/RS2 -> possible WAW memory hazard
          if (!(instr.group inside {RV32C, RV32FC, RV32DC, RV64C, RV128C})) begin
            riscv_instr extra_instr;
            extra_instr = riscv_instr::get_instr(instr.instr_name);
            extra_instr.do_copy(instr);
            if (instr.category == LOAD) begin
              riscv_reg_t new_rd;
              riscv_fpr_t new_fd;
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(new_rd,
                if (avail_regs.size() > 0) {
                    new_rd inside {avail_regs};
                }
                foreach (reserved_rd[i]) {
                    new_rd != reserved_rd[i];
                }
                foreach (cfg.reserved_regs[i]) {
                    new_rd != cfg.reserved_regs[i];
                }
                new_rd != instr.rd;
              )
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(new_fd,
                if (avail_fp_regs.size() > 0) {
                    new_fd inside {avail_fp_regs};
                }
                new_fd != instr.fd;
              )
              extra_instr.rd = new_rd;
              extra_instr.fd = new_fd;
              if (extra_instr.rs1 != instr.rs1 || extra_instr.rs2 != instr.rs2 || extra_instr.rd == instr.rd || extra_instr.fd == instr.fd) begin
                `uvm_fatal(get_type_name(), "Randomization failed. Different RS1 or RS2 or same RD/FD!")
              end
            end else if (instr.category == STORE) begin
              riscv_reg_t new_rs2;
              riscv_fpr_t new_fs2;
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(new_rs2,
                if (avail_regs.size() > 0) {
                    new_rs2 inside {avail_regs};
                }
                new_rs2 != instr.rs2;
              )
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(new_fs2,
                if (avail_fp_regs.size() > 0) {
                    new_fs2 inside {avail_fp_regs};
                }
                new_fs2 != instr.fs2;
              )
              extra_instr.rs2 = new_rs2;
              extra_instr.fs2 = new_fs2;
              if (extra_instr.rs1 != instr.rs1 || extra_instr.rs2 == instr.rs2 || extra_instr.fs2 == instr.fs2) begin
                `uvm_fatal(get_type_name(), "Randomization failed. Different RS1 or same RS2/FS2!")
              end
            end

            extra_instr.imm_str = $sformatf("%0d", offset[i]);
            extra_instr.comment = $sformatf("repeated w different rd LD/ST no %d", i);
            //`uvm_info(`gfn, $sformatf("extra_instr (RD randomized): %s orig instr: %s", extra_instr.convert2string(), instr.convert2string()), UVM_NONE)
            instr_list.push_back(instr);
            load_store_instr.push_back(instr);
            instr_list.push_back(extra_instr); // repeat the same instruction
          end
        end
        15: begin // WWR and WRW hazards
          if (!(instr.group inside {RV32C, RV32FC, RV32DC, RV64C, RV128C})) begin // 32b wont hold the addr
            riscv_instr extra_instr;
            riscv_instr extra_instr2;
            riscv_reg_t new_rs2;
            riscv_fpr_t new_fs2;
            if (instr.category == LOAD) begin
              extra_instr = get_store_w_offset_instr(instr, offset[i], $sformatf("WWR hazard pt1 for %d", i));
              extra_instr2 = get_store_w_offset_instr(instr, offset[i], $sformatf("WWR hazard pt2 for %d", i));
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(new_rs2,
                if (avail_regs.size() > 0) {
                    new_rs2 inside {avail_regs};
                }
                new_rs2 != extra_instr.rs2;
              )
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(new_fs2,
                if (avail_fp_regs.size() > 0) {
                    new_fs2 inside {avail_fp_regs};
                }
                new_fs2 != extra_instr.fs2;
              )
              extra_instr2.rs2 = new_rs2;
              extra_instr2.fs2 = new_fs2;

              instr_list.push_back(instr); // preload W source
              instr_list.push_back(extra_instr); // W
              instr_list.push_back(extra_instr2); // W
              instr_list.push_back(instr); // R
            end else begin
              extra_instr = get_load_w_offset_instr(instr, offset[i], $sformatf("WRW hazard pt2 for %d", i));
              extra_instr2 = get_store_w_offset_instr(extra_instr, offset[i], $sformatf("WRW hazard pt3 for %d", i));
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(new_rs2,
                if (avail_regs.size() > 0) {
                    new_rs2 inside {avail_regs};
                }
                new_rs2 != instr.rs2;
              )
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(new_fs2,
                if (avail_fp_regs.size() > 0) {
                    new_fs2 inside {avail_fp_regs};
                }
                new_fs2 != instr.fs2;
              )
              extra_instr2.rs2 = new_rs2;
              extra_instr2.fs2 = new_fs2;

              instr_list.push_back(instr); // W
              instr_list.push_back(extra_instr); // R
              instr_list.push_back(extra_instr2); // W
            end
            load_store_instr.push_back(instr);
          end
        end
        25: begin // RAW and WAR hazards
          if (!(instr.group inside {RV32C, RV32FC, RV32DC, RV64C, RV128C})) begin // 32b wont hold the addr
            riscv_instr extra_instr;
            if (instr.category == LOAD) begin
              extra_instr = get_store_w_offset_instr(instr, offset[i], $sformatf("WAR hazard for %d", i));
            end else begin
              extra_instr = get_load_w_offset_instr(instr, offset[i], $sformatf("RAW hazard for %d", i));
            end
            instr_list.push_back(instr);
            load_store_instr.push_back(instr);
            instr_list.push_back(extra_instr);
          end
        end
        20: begin // Random offsets from same base to exercise the cache
          riscv_instr extra_instr;
          int _offset;

          instr_list.push_back(instr);
          load_store_instr.push_back(instr);

          // Stream of offsets like +4, +8, -12, -16, +20, etc
          for (int rs = 0; rs < repetition_steps; rs++) begin
            if (!std::randomize(offset_sign) with {
              offset_sign inside {-1, +1};
            }) begin
              `uvm_fatal(`gfn, "Cannot randomize offset sign")
            end
            if (instr.group inside {RV32C, RV64C, RV32DC, RV32FC, RV128C}) begin
              offset_sign = 1; // can't have negative offsets
            end
            accumulated_offset += increasing_offset;
            _offset = $signed(offset[i] + offset_sign*accumulated_offset);
            if (instr.instr_name inside {C_LD, C_SD, SD, LD, C_LDSP, C_SDSP}) begin
              _offset = _offset - (_offset % 8); // align doubles
            end

            if (_offset < -2048 || _offset > 2047) begin // out of bounds
              break;
            end

            if (instr.category == LOAD) begin
              instr_list.push_back(get_store_w_offset_instr(instr, _offset, "Preload address"));
            end
            extra_instr = riscv_instr::get_instr(instr.instr_name);
            extra_instr.do_copy(instr);
            randomize_gpr(extra_instr);
            extra_instr.rs1 = instr.rs1;
            if (extra_instr.rs1 != instr.rs1) begin
              `uvm_fatal(get_type_name(), "Randomization failed. Not same RS1!")
            end
            extra_instr.imm_str = $sformatf("%0d", _offset);
            extra_instr.comment = $sformatf("Changing offset by %d for ld/st instr no %d, step %d", offset_sign*accumulated_offset, i, rs);
            //`uvm_info(`gfn, $sformatf("extra_instr (RS1 retained first): %s orig instr: %s", extra_instr.convert2string(), instr.convert2string()), UVM_NONE)
            instr_list.push_back(extra_instr);
          end
        end
        10: begin // Increasing offsets from same base to exercise the cache
          riscv_instr extra_instr;
          int _offset;
          offset_sign = 1;

          instr_list.push_back(instr);
          load_store_instr.push_back(instr);

          // Stream of offsets like +4, +8, +12, +16, etc
          for (int rs = 0; rs < repetition_steps; rs++) begin
            accumulated_offset += increasing_offset;
            _offset = $signed(offset[i] + offset_sign*accumulated_offset);
            if (instr.instr_name inside {C_LD, C_SD, SD, LD, C_LDSP, C_SDSP}) begin
              _offset = _offset - (_offset % 8); // align doubles
            end
            if (_offset < -2048 || _offset > 2047) begin // out of bounds
              break;
            end

            if (instr.category == LOAD) begin
              instr_list.push_back(get_store_w_offset_instr(instr, _offset, "Preload address"));
            end
            extra_instr = riscv_instr::get_instr(instr.instr_name);
            extra_instr.do_copy(instr);
            randomize_gpr(extra_instr);
            extra_instr.rs1 = instr.rs1;
            if (extra_instr.rs1 != instr.rs1) begin
              `uvm_fatal(get_type_name(), "Randomization failed. Not same RS1!")
            end
            extra_instr.imm_str = $sformatf("%0d", _offset);
            extra_instr.comment = $sformatf("Increasing offset by %d for ld/st instr no %d, step %d", offset_sign*accumulated_offset, i, rs);
            //`uvm_info(`gfn, $sformatf("extra_instr (RS1 retained second): %s orig instr: %s", extra_instr.convert2string(), instr.convert2string()), UVM_NONE)
            instr_list.push_back(extra_instr);
          end
        end
        10: begin
          instr_list.push_back(instr);
          load_store_instr.push_back(instr);
        end
      endcase

    end
    // Final "Cleanup"
    // Create a target for the last jump forward
    if (jump_branch_state == NEEDS_TARGET_LABEL) begin
      riscv_instr nop_instr;
      nop_instr = riscv_instr::get_instr(NOP);
      nop_instr.label = "1";
      nop_instr.has_label = 1;
      instr_list.push_back(nop_instr);
      jump_branch_state = HAS_TARGET_LABEL;
    end
    if (cfg.init_privileged_mode == MACHINE_MODE) begin
      if (dcache_state == DISABLED && jump_branch_state == HAS_TARGET_LABEL) begin
        switch_dcache_state(.dcache_state(dcache_state), .instr_list(instr_list), .avail_gpr(avail_regs[0]));
      end
    end
  endfunction

endclass
