/*
 * Copyright 2019 Google LLC
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

class riscv_instr extends uvm_object;

  // All derived instructions
  static bit                 instr_registry[riscv_instr_name_t];

  // Instruction list
  static riscv_instr_name_t  instr_names[$];

  // Categorized instruction list
  static riscv_instr_name_t  instr_group[riscv_instr_group_t][$];
  static riscv_instr_name_t  instr_category[riscv_instr_category_t][$];
  static riscv_instr_name_t  basic_instr[$];
  static riscv_instr         instr_template[riscv_instr_name_t];

  // Directed/forced instructions
  static riscv_instr_name_t  preferred_instr_names[$];
  static int                 preferred_instr_rate = 10; // in %, set to 0 to 100


  // Settings/configuration
  riscv_instr_gen_config        m_cfg;
  static rand_instr_dist_mode_e random_instr_distribution_mode = NONE;
  static int                    random_instr_distribution_value = 1;

  // Instruction attributes
  riscv_instr_t              instr_type;
  riscv_instr_group_t        group;
  riscv_instr_format_t       format;
  riscv_instr_category_t     category;
  riscv_instr_name_t         instr_name;
  imm_t                      imm_type;
  bit [4:0]                  imm_len;

  // Operands

  rand privileged_reg_t      csr;
  rand riscv_reg_t           rs2;
  rand riscv_reg_t           rs1;
  rand riscv_reg_t           rd;
  rand bit [31:0]            imm;

  // Helper fields
  bit [31:0]                 imm_mask = 32'hFFFF_FFFF;
  bit                        is_branch_target;
  bit                        has_label = 1'b1;
  bit                        atomic = 0;
  bit                        branch_assigned;
  bit                        process_load_store = 1'b1;
  bit                        is_compressed;
  bit                        is_illegal_instr;
  bit                        is_hint_instr;
  bit                        is_floating_point;
  string                     imm_str;
  string                     comment;
  string                     label;
  bit                        is_local_numeric_label;
  int                        idx = -1;
  bit                        has_rs1 = 1'b1;
  bit                        has_rs2 = 1'b1;
  bit                        has_rd = 1'b1;
  bit                        has_imm = 1'b1;

  static riscv_reg_t         base_directed_gpr_list[$] = {};

  constraint imm_c {
    if (instr_name inside {SLLIW, SRLIW, SRAIW}) {
      imm[11:5] == 0;
    }
    if (instr_name inside {SLLI, SRLI, SRAI}) {
      if (XLEN == 32) {
        imm[11:5] == 0;
      } else {
        imm[11:6] == 0;
      }
    }
  }

  constraint base_gpr_directed_c {
    (base_directed_gpr_list.size()!=0 && instr_type==BASE) ->  rd inside {base_directed_gpr_list};
    (base_directed_gpr_list.size()!=0 && instr_type==BASE) ->  rs1 inside {base_directed_gpr_list};
    (base_directed_gpr_list.size()!=0 && instr_type==BASE) ->  rs2 inside {base_directed_gpr_list};
  }

  `uvm_object_utils(riscv_instr)
  `uvm_object_new

  `include "riscv_instr_cov.svh"
  `include "riscv_floating_point_instr.sv"
  `include "riscv_amo_instr.sv"
  `include "riscv_csr_instr.sv"
  `include "riscv_vector_instr.sv"

  static function bit register(riscv_instr_name_t instr_name);
    instr_registry[instr_name] = 1;
    `uvm_info("riscv_instr", $sformatf("Registering %0s format: %s category: %s", instr_name.name(), format.name(), category.name()), UVM_LOW)
    return 1;
  endfunction : register

  // Create the list of instructions based on the supported ISA extensions and configuration of the
  // generator.
  static function void create_instr_list(riscv_instr_gen_config cfg);
    bit add_instr;
    instr_names.delete();
    instr_group.delete();
    instr_category.delete();
    foreach (instr_registry[instr_name]) begin
      riscv_instr instr_inst;
      if (instr_name inside {unsupported_instr}) continue;
      instr_inst = create_instr(instr_name);
      instr_template[instr_name] = instr_inst;
      if (!instr_inst.is_supported(cfg)) continue;
      // C_JAL is RV32C only instruction
      if ((XLEN != 32) && (instr_name == C_JAL)) continue;
      if ((SP inside {cfg.reserved_regs}) && (instr_name inside {C_ADDI16SP})) continue;
      if (!cfg.enable_sfence && instr_name == SFENCE_VMA) continue;
      if (cfg.no_fence && (instr_name inside {FENCE, FENCE_I, SFENCE_VMA})) continue;
      if ((instr_inst.group inside {supported_isa}) &&
          !(cfg.disable_compressed_instr &&
            (instr_inst.group inside {RV32C, RV64C, RV32DC, RV32FC, RV128C})) &&
          !(!cfg.enable_fp_extension &&
            (instr_inst.group inside {ZFH, RV32F, RV64F, RV32D, RV64D})) &&
          !(cfg.floating_point_instr_only &&
            !(instr_inst.group inside {ZFH, RV32F, RV64F, RV32D, RV64D})) &&
          !(!cfg.enable_vector_extension &&
            (instr_inst.group inside {RVV})) &&
          !(cfg.vector_instr_only &&
            !(instr_inst.group inside {RVV}))
          ) begin
        add_instr = 0;
        if (instr_inst.group inside {RVV}) begin
          if (instr_inst.category == CSR) add_instr =  1;
          else if (instr_inst.category inside {LOAD, STORE}) begin
            if (instr_name inside {cfg.specific_v_ls_instructions}) begin
              add_instr = 1;
            end else begin
              add_instr = (cfg.specific_v_ls_instructions.size()==0); // add when you dont specify any specific ld st, i.e. normal randomness
            end
          end else begin
            if (instr_name inside {cfg.specific_v_instructions}) begin
              add_instr = 1;
            end else begin
              add_instr = (cfg.specific_v_instructions.size()==0); // add when you dont specify any specific vector, i.e. normal randomness
            end
          end
        end else begin
          add_instr = 1; // non vector, always add
        end

        if (add_instr) begin
          instr_category[instr_inst.category].push_back(instr_name);
          instr_group[instr_inst.group].push_back(instr_name);
          instr_names.push_back(instr_name);
        end
      end
    end
    build_basic_instruction_list(cfg);
    extract_config_settings(cfg);
    foreach (cfg.base_directed_gpr_list[i]) base_directed_gpr_list.push_back(cfg.base_directed_gpr_list[i]);
    foreach (instr_names[i]) begin
      `uvm_info("riscv_instr-dbg", $sformatf("instr_names[%0d] %s", i, instr_names[i].name()), UVM_DEBUG)
    end
  endfunction : create_instr_list

  // Extract global settings from config for static functions
  static function void extract_config_settings(riscv_instr_gen_config cfg);
    random_instr_distribution_mode  = cfg.random_instr_distribution_mode;
    random_instr_distribution_value = cfg.random_instr_distribution_value;
  endfunction : extract_config_settings

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    case (instr_type)
      default: return 1;
      VECTOR: return (is_vector_supported(cfg));
    endcase
  endfunction

  static function riscv_instr create_instr(riscv_instr_name_t instr_name);
    uvm_object obj;
    riscv_instr inst;
    string instr_class_name;
    uvm_coreservice_t coreservice = uvm_coreservice_t::get();
    uvm_factory factory = coreservice.get_factory();
    instr_class_name = {"riscv_", instr_name.name(), "_instr"};
    obj = factory.create_object_by_name(instr_class_name, "riscv_instr", instr_class_name);
    if (obj == null) begin
      `uvm_fatal("riscv_instr", $sformatf("Failed to create instr: %0s", instr_class_name))
    end else begin
      `uvm_info("riscv_instr",  $sformatf("Created instr. instr_class_name:  %0s type: %s", instr_class_name, obj.get_type_name()), UVM_FULL)
    end
    if (!$cast(inst, obj)) begin
      `uvm_fatal("riscv_instr", $sformatf("Failed to cast instr: %0s", instr_class_name))
    end else begin
      `uvm_info("riscv_instr",  $sformatf("Created instr. inst.type:  %0s type: %s", inst.get_type_name(), obj.get_type_name()), UVM_FULL)
    end
    return inst;
  endfunction : create_instr

  static function void build_basic_instruction_list(riscv_instr_gen_config cfg);
    basic_instr = {instr_category[SHIFT], instr_category[ARITHMETIC],
                   instr_category[LOGICAL], instr_category[COMPARE]};
    if (!cfg.no_ebreak) begin
      basic_instr = {basic_instr, EBREAK};
      foreach (riscv_instr_pkg::supported_isa[i]) begin
        if (RV32C inside {riscv_instr_pkg::supported_isa[i]} &&
            !cfg.disable_compressed_instr) begin
          basic_instr = {basic_instr, C_EBREAK};
          break;
        end
      end
    end
    if (!cfg.no_ecall) begin
      basic_instr = {basic_instr, ECALL};
    end
    if (cfg.no_dret == 0) begin
      basic_instr = {basic_instr, DRET};
    end
    if (cfg.no_fence == 0) begin
      basic_instr = {basic_instr, instr_category[SYNCH]};
    end
    if (cfg.no_csr_instr == 0) begin
      basic_instr = {basic_instr, instr_category[CSR]};
    end
    if (cfg.no_wfi == 0) begin
      basic_instr = {basic_instr, WFI};
    end
  endfunction : build_basic_instruction_list

  static function riscv_instr get_rand_instr(riscv_instr instr_h = null,
                                             riscv_instr_name_t include_instr[$] = {},
                                             riscv_instr_name_t exclude_instr[$] = {},
                                             riscv_instr_category_t include_category[$] = {},
                                             riscv_instr_category_t exclude_category[$] = {},
                                             riscv_instr_group_t include_group[$] = {},
                                             riscv_instr_group_t exclude_group[$] = {});
    int unsigned idx;
    riscv_instr_name_t name;
    riscv_instr_name_t allowed_instr[$];
    riscv_instr_name_t disallowed_instr[$];
    riscv_instr_category_t allowed_categories[$];
    foreach (include_category[i]) begin
      allowed_instr = {allowed_instr, instr_category[include_category[i]]};
    end
    foreach (exclude_category[i]) begin
      if (instr_category.exists(exclude_category[i])) begin
        disallowed_instr = {disallowed_instr, instr_category[exclude_category[i]]};
      end
    end
    foreach (include_group[i]) begin
      allowed_instr = {allowed_instr, instr_group[include_group[i]]};
    end
    foreach (exclude_group[i]) begin
      if (instr_group.exists(exclude_group[i])) begin
        disallowed_instr = {disallowed_instr, instr_group[exclude_group[i]]};
      end
    end
    disallowed_instr = {disallowed_instr, exclude_instr};

    if (disallowed_instr.size() == 0) begin
      if (include_instr.size() > 0) begin
        if (preferred_instr_names.size() > 0 && ($urandom_range(1,100)> (100 - preferred_instr_rate))) begin
          idx = $urandom_range(0, preferred_instr_names.size()-1);
          name = preferred_instr_names[idx];
        end else begin
          idx = $urandom_range(0, include_instr.size()-1);
          name = include_instr[idx];
        end
      end else if (allowed_instr.size() > 0) begin
        idx = $urandom_range(0, allowed_instr.size()-1);
        name = allowed_instr[idx];
      end else begin
        idx = $urandom_range(0, instr_names.size()-1);
        name = instr_names[idx];
      end
    end else begin
      if (!std::randomize(name) with {
        name inside {instr_names};
        if (include_instr.size() > 0) {
          name inside {include_instr};
        }
        if (allowed_instr.size() > 0) {
          name inside {allowed_instr};
        }
        if (disallowed_instr.size() > 0) {
          !(name inside {disallowed_instr});
        }
        if (random_instr_distribution_mode == LIMIT_VRGATHER_VCOMPRESS) {
          // We want less vrgather{ei16} and vcompress instructions
          name dist {
            [LUI:VFSLIDE1DOWN] := random_instr_distribution_value,
            [VRGATHER:VCOMPRESS] := 1,
            [VMV1R_V:SFENCE_VMA] := random_instr_distribution_value
          };
      }
      }) begin
        `uvm_fatal("riscv_instr", "Cannot generate random instruction")
      end
    end

    // Shallow copy for all relevant fields, avoid using create() to improve performance
    instr_h = new instr_template[name];
    // Put instruction RNG in unique state
    instr_h.srandom($urandom());
    return instr_h;
  endfunction : get_rand_instr

  static function riscv_instr get_load_store_instr(riscv_instr_name_t load_store_instr[$] = {});
     riscv_instr instr_h;
     int unsigned idx;
     int unsigned i;
     riscv_instr_name_t name;
     if (load_store_instr.size() == 0) begin
       load_store_instr = {instr_category[LOAD], instr_category[STORE]};
     end
     // Filter out unsupported load/store instruction
     if (unsupported_instr.size() > 0) begin
       while (i < load_store_instr.size()) begin
         if (load_store_instr[i] inside {unsupported_instr}) begin
           load_store_instr.delete(i);
         end else begin
           i++;
         end
       end
     end
     if (load_store_instr.size() == 0) begin
       $error("Cannot find available load/store instruction");
       $fatal(1);
     end
     idx = $urandom_range(0, load_store_instr.size()-1);
     name = load_store_instr[idx];
     // Shallow copy for all relevant fields, avoid using create() to improve performance
     instr_h = new instr_template[name];
     // Put instruction RNG in unique state
     instr_h.srandom($urandom());
     return instr_h;
  endfunction : get_load_store_instr

  static function riscv_instr get_instr(riscv_instr_name_t name);
     riscv_instr instr_h;
     if (!instr_template.exists(name)) begin
       `uvm_fatal("riscv_instr", $sformatf("Cannot get instr %0s", name.name()))
     end
     // Shallow copy for all relevant fields, avoid using create() to improve performance
     instr_h = new instr_template[name];
     return instr_h;
  endfunction : get_instr

  // Disable the rand mode for unused operands to randomization performance
  virtual function void set_rand_mode();
    case (instr_type)
      default       : base_set_rand_mode();
      FLOATING_POINT: fp_set_rand_mode();
      CSR_INSTR     : csr_set_rand_mode();
      VECTOR        : vector_set_rand_mode();
    endcase
  endfunction

  virtual function void base_set_rand_mode();
    case (format) inside
      R_FORMAT : has_imm = 1'b0;
      I_FORMAT : has_rs2 = 1'b0;
      S_FORMAT, B_FORMAT : has_rd = 1'b0;
      U_FORMAT, J_FORMAT : begin
        has_rs1 = 1'b0;
        has_rs2 = 1'b0;
      end
    endcase
  endfunction

  function void pre_randomize();
    rs1.rand_mode(has_rs1);
    rs2.rand_mode(has_rs2);
    rd.rand_mode(has_rd);
    imm.rand_mode(has_imm);
    if (category != CSR) begin
      csr.rand_mode(0);
    end
    fs1.rand_mode(has_fs1);
    fs2.rand_mode(has_fs2);
    fs3.rand_mode(has_fs3);
    fd.rand_mode(has_fd);
    vs1.rand_mode(has_vs1);
    vs2.rand_mode(has_vs2);
    vs3.rand_mode(has_vs3);
    vd.rand_mode(has_vd);
    va_variant.rand_mode(has_va_variant);
  endfunction

  virtual function void set_imm_len();
    case (instr_type)
      default       : base_set_imm_len();
      FLOATING_POINT: fp_set_imm_len();
      VECTOR        : vector_set_imm_len();
    endcase
  endfunction

  virtual function void base_set_imm_len();
    if(format inside {U_FORMAT, J_FORMAT}) begin
      imm_len = 20;
    end else if(format inside {I_FORMAT, S_FORMAT, B_FORMAT}) begin
      if(imm_type == UIMM) begin
        imm_len = 5;
      end else begin
        imm_len = 12;
      end
    end
    imm_mask = imm_mask << imm_len;
  endfunction

  virtual function void extend_imm();
    bit sign;
    imm = imm << (32 - imm_len);
    sign = imm[31];
    imm = imm >> (32 - imm_len);
    // Signed extension
    if (sign && !((format == U_FORMAT) || (imm_type inside {UIMM, NZUIMM}))) begin
      imm = imm_mask | imm;
    end
  endfunction : extend_imm

  function void post_randomize();
    extend_imm();
    update_imm_str();
    `uvm_info(get_type_name(), "post_randomize called!", UVM_FULL)
  endfunction : post_randomize

  virtual function string convert2asm(string prefix = "");
    string asm_str;
    case (instr_type)
      BASE          : asm_str = base_convert2asm(prefix);
      FLOATING_POINT: asm_str = fp_convert2asm(prefix);
      ATOMIC        : asm_str = atomic_convert2asm(prefix);
      CSR_INSTR     : asm_str = csr_convert2asm(prefix);
      VECTOR        : asm_str = vector_convert2asm(prefix);
    endcase
    `uvm_info(get_type_name(), $sformatf("convert2asm: type: %s instr: %s asm %s", instr_type.name(), instr_name.name(), asm_str), UVM_DEBUG)
    return asm_str;
  endfunction

  // Convert the instruction to assembly code
  virtual function string base_convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    if(category != SYSTEM) begin
      case(format)
        J_FORMAT, U_FORMAT : // instr rd,imm
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
        I_FORMAT: // instr rd,rs1,imm
          if(instr_name == NOP)
            asm_str = "nop";
          else if(instr_name == WFI)
            asm_str = "wfi";
          else if(instr_name == FENCE)
            asm_str = $sformatf("fence"); // TODO: Support all fence combinations
          else if(instr_name == FENCE_I)
            asm_str = "fence.i";
          else if(category == LOAD) // Use psuedo instruction format
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), get_imm());
        S_FORMAT, B_FORMAT: // instr rs1,rs2,imm
          if(category == STORE) // Use psuedo instruction format
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rs1.name(), rs2.name(), get_imm());
        R_FORMAT: // instr rd,rs1,rs2
          if(instr_name == SFENCE_VMA) begin
            asm_str = "sfence.vma x0, x0"; // TODO: Support all possible sfence
          end else begin
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), rs2.name());
          end
        default: `uvm_fatal(`gfn, $sformatf("Unsupported format %0s [%0s]",
                                            format.name(), instr_name.name()))
      endcase
    end else begin
      // For EBREAK,C.EBREAK, making sure pc+4 is a valid instruction boundary
      // This is needed to resume execution from epc+4 after ebreak handling
      if(instr_name == EBREAK) begin
        asm_str = ".4byte 0x00100073 # ebreak";
      end
    end
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    `uvm_info(get_type_name(), $sformatf("convert2asm: %s", instr_name.name()), UVM_HIGH)
    return asm_str.tolower();
  endfunction

  virtual function string get_instr_name();
    string name = instr_name.name();
    if (instr_type inside {BASE, FLOATING_POINT, CSR, VECTOR}) begin
      foreach(name[i]) begin
        if (name[i] == "_") begin
          name[i] = ".";
        end
      end
      if (instr_type == VECTOR) get_vector_instr_name(name);
    end else if (instr_type== ATOMIC) begin
      if (group == RV32A) begin
        name = {name.substr(0, name.len() - 3), ".w"};
        name = aq ? {name, ".aq"} : rl ? {name, ".rl"} : name;
      end else if (group == RV64A) begin
        name = {name.substr(0, name.len() - 3), ".d"};
        name = aq ? {name, ".aq"} :  rl ? {name, ".rl"} : name;
      end else begin
        `uvm_fatal(`gfn, $sformatf("Unexpected amo instr group: %0s / %0s", group.name(), instr_name.name()))
      end
    end
    return name;
  endfunction

  // Get RVC register name for CIW, CL, CS, CB format
  function bit [2:0] get_c_gpr(riscv_reg_t gpr);
    return gpr[2:0];
  endfunction

  // Default return imm value directly, can be overriden to use labels and symbols
  // Example: %hi(symbol), %pc_rel(label) ...
  virtual function string get_imm();
    return imm_str;
  endfunction

  virtual function void clear_unused_label();
    if(has_label && !is_branch_target && is_local_numeric_label) begin
      has_label = 1'b0;
    end
  endfunction

  virtual function riscv_instr do_clone();
    riscv_instr item;

    if(!$cast(item, this.clone()))
      `uvm_fatal(get_full_name(), "Clone failed")

    return item;
  endfunction

  virtual function void do_copy(uvm_object rhs);
    riscv_instr rhs_;

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
  endfunction : do_copy

  virtual function void update_imm_str();
    imm_str = $sformatf("%0d", $signed(imm));
  endfunction

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n----------- RISCV INSTRUCTION ----------------") };
    s = {s, $sformatf("\n instr_name             : %s", instr_name.name())};
    s = {s, $sformatf("\n csr (rand)             : %s", csr.name())};
    s = {s, $sformatf("\n rs2 (rand)             : %s", rs2.name())};
    s = {s, $sformatf("\n rs1 (rand)             : %s", rs1.name())};
    s = {s, $sformatf("\n rd  (rand)             : %s", rd.name())};
    s = {s, $sformatf("\n fs1 (rand)             : %s", fs1.name())};
    s = {s, $sformatf("\n fs2 (rand)             : %s", fs2.name())};
    s = {s, $sformatf("\n fs3 (rand)             : %s", fs3.name())};
    s = {s, $sformatf("\n fd (rand)              : %s", fd.name())};
    s = {s, $sformatf("\n imm (rand)             : %0d", imm)};
    s = {s, $sformatf("\n group                  : %s", group.name())};
    s = {s, $sformatf("\n format                 : %s", format.name())};
    s = {s, $sformatf("\n category               : %s", category.name())};
    s = {s, $sformatf("\n imm_type               : %s", imm_type.name())};
    s = {s, $sformatf("\n imm_len                : %0d", imm_len)};
    s = {s, $sformatf("\n imm_mask               : 0x%0x", imm_mask)};
    s = {s, $sformatf("\n imm_str                : %s", imm_str)};
    s = {s, $sformatf("\n is_compressed          : %0d", is_compressed)};
    s = {s, $sformatf("\n is_branch_target       : %0d", is_branch_target)};
    s = {s, $sformatf("\n has_label              : %0d", has_label)};
    s = {s, $sformatf("\n atomic                 : %0d", atomic)};
    s = {s, $sformatf("\n branch_assigned        : %0d", branch_assigned)};
    s = {s, $sformatf("\n process_load_store     : %0d", process_load_store)};
    s = {s, $sformatf("\n is_illegal_instr       : %0d", is_illegal_instr)};
    s = {s, $sformatf("\n is_hint_instr          : %0d", is_hint_instr)};
    s = {s, $sformatf("\n is_floating_point      : %0d", is_floating_point)};
    s = {s, $sformatf("\n comment                : %s", comment)};
    s = {s, $sformatf("\n label                  : %s", label)};
    s = {s, $sformatf("\n is_local_numeric_label : %0d", is_local_numeric_label)};
    s = {s, $sformatf("\n idx                    : %0d", idx)};
    s = {s, $sformatf("\n has_rs2                : %0d", has_rs2)};
    s = {s, $sformatf("\n has_rs1                : %0d", has_rs1)};
    s = {s, $sformatf("\n has_rd                 : %0d", has_rd)};
    s = {s, $sformatf("\n has_imm                : %0d", has_imm)};
    s = {s, $sformatf("\n has_fs3                : %0d", has_fs3)};
    s = {s, $sformatf("\n has_fs2                : %0d", has_fs2)};
    s = {s, $sformatf("\n has_fs1                : %0d", has_fs1)};
    s = {s, $sformatf("\n has_fd                 : %0d", has_fd)};
    s = {s, $sformatf("\n aq                     : %0d", aq)};
    s = {s, $sformatf("\n rl                     : %0d", rl)};
    s = {s, $sformatf("\n vsl                    : %0d", vs1)};
    s = {s, $sformatf("\n vs2                    : %0d", vs2)};
    s = {s, $sformatf("\n vs3                    : %0d", vs3)};
    s = {s, $sformatf("\n vd                     : %0d", vd)};
    s = {s, $sformatf("\n va_variant             : %0d", va_variant)};
    s = {s, $sformatf("\n vm                     : %0d", vm)};
    s = {s, $sformatf("\n ls_eew                 : %0d", ls_eew)};
    s = {s, $sformatf("\n nfields                : %0d", nfields)};
    s = {s, $sformatf("\n has_vs1                : %0d", has_vs1)};
    s = {s, $sformatf("\n has_vs2                : %0d", has_vs2)};
    s = {s, $sformatf("\n has_vs3                : %0d", has_vs3)};
    s = {s, $sformatf("\n has_vd                 : %0d", has_vd)};
    s = {s, $sformatf("\n has_va_variant         : %0d", has_va_variant)};
    s = {s, $sformatf("\n is_widening_instr      : %0d", is_widening_instr)};
    s = {s, $sformatf("\n is_narrowing_instr     : %0d", is_narrowing_instr)};
    s = {s, $sformatf("\n is_convert_instr       : %0d", is_convert_instr)};
    s = {s, $sformatf("\n is_reduction_instr     : %0d", is_reduction_instr)};
    s = {s, $sformatf("\n is_mask_producing_instr : %0d", is_mask_producing_instr)};
    s = {s, $sformatf("\n is_mask_operands       : %0d", is_mask_operands)};
    s = {s, $sformatf("\n is_fp_instr            : %0d", is_fp_instr)};
    s = {s, $sformatf("\n is_segmented_ls_instr  : %0d", is_segmented_ls_instr)};
    s = {s, $sformatf("\n is_whole_register_ls_instr  : %0d", is_whole_register_ls_instr)};
    s = {s, $sformatf("\n ext_widening_factor    : %0d", ext_widening_factor)};
    s = {s, $sformatf("\n whole_register_move_cnt : %0d", whole_register_move_cnt)};
    s = {s, $sformatf("\n allowed_va_variants    : %0d", whole_register_move_cnt)};
    s = {s, $sformatf("\n ls_emul_non_frac       : %0d", ls_emul_non_frac)};
    s = {s, $sformatf("\n---------------------------------------------") };
    return s;
  endfunction

   virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    riscv_instr rhs_;

    if(!$cast(rhs_, rhs))
      `uvm_fatal(get_full_name(), "do_compare cast failed");

      return ( super.do_compare(rhs, comparer) &&
        this.group                   == rhs_.group  &&
        this.format                  == rhs_.format &&
        this.category                == rhs_.category &&
        this.instr_name              == rhs_.instr_name &&
        this.csr                     == rhs_.csr &&
        this.rs2                     == rhs_.rs2 &&
        this.rs1                     == rhs_.rs1 &&
        this.rd                      == rhs_.rd  &&
        this.imm                     == rhs_.imm &&
        this.imm_type                == rhs_.imm_type &&
        this.imm_len                 == rhs_.imm_len  &&
        this.imm_mask                == rhs_.imm_mask &&
        this.is_compressed           == rhs_.is_compressed &&
        this.is_branch_target        == rhs_.is_branch_target &&
        this.has_label               == rhs_.has_label &&
        this.atomic                  == rhs_.atomic &&
        this.branch_assigned         == rhs_.branch_assigned &&
        this.process_load_store      == rhs_.process_load_store &&
        this.is_illegal_instr        == rhs_.is_illegal_instr &&
        this.is_hint_instr           == rhs_.is_hint_instr &&
        this.is_floating_point       == rhs_.is_floating_point &&
        this.label                   == rhs_.label &&
        this.is_local_numeric_label  == rhs_.is_local_numeric_label &&
        this.idx                     == rhs_.idx &&
        this.has_rs1                 == rhs_.has_rs1 &&
        this.has_rd                  == rhs_.has_rd  &&
        this.has_imm                 == rhs_.has_imm &&
        this.has_fs3                 == rhs_.has_fs3 &&
        this.has_fs2                 == rhs_.has_fs2  &&
        this.has_fs1                 == rhs_.has_fs1 &&
        this.has_fd                  == rhs_.has_fd &&
        this.aq                      == rhs_.aq  &&
        this.rl                      == rhs_.rl
    );
  endfunction : do_compare

  // When enable =1, enables randomization only for the ones in the list
  // When enable =0, disables randomization only for the ones in the list
  virtual function void restrict_randomization(string list_of_fields[$], bit enable=0);
    // disable/enable all first
    csr.rand_mode(~enable);
    rs2.rand_mode(~enable);
    rs1.rand_mode(~enable);
    rd.rand_mode(~enable);
    imm.rand_mode(~enable);
    // then enable/disable below
    foreach (list_of_fields[i]) begin
      case (list_of_fields[i])
        "csr": csr.rand_mode(enable);
        "rs2": rs2.rand_mode(enable);
        "rs1": rs1.rand_mode(enable);
        "rd":  rd.rand_mode(enable);
        "imm": imm.rand_mode(enable);
        default: `uvm_info(get_full_name(), $sformatf("%s not found. Ignoring...", list_of_fields[i]), UVM_NONE) // can be uvm_warning if needed
      endcase
    end
    `uvm_info(get_full_name(), $sformatf("restrict_randomization: list_of_fields: %p enable: %0d", list_of_fields, enable), UVM_LOW)
  endfunction
endclass
