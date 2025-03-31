/*
 * Copyright 2018 Google LLC
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

`define add_instr(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  constraint riscv_``instr_group``_``instr_n``_c { \
    if (instr_name == ``instr_n) { \
        format     == ``instr_format; \
        category   == ``instr_category; \
        group      == ``instr_group; \
        imm_type   == ``imm_tp; \
    } \
  }

`define add_pseudo_instr(instr_n, instr_format, instr_category, instr_group)  \
  constraint riscv_``instr_group``_``instr_n``_c { \
    if (pseudo_instr_name  == ``instr_n) { \
        format             == ``instr_format; \
        category           == ``instr_category; \
        group              == ``instr_group; \
    } \
  }

`define INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM, instr_t=BASE, vav = {}) \
    static bit valid = riscv_instr::register(instr_n);  \
    `uvm_object_utils(riscv_``instr_n``_instr)  \
    function new(string name = "");  \
      super.new(name);  \
      this.instr_name = ``instr_n; \
      this.format = ``instr_format;  \
      this.group = ``instr_group;  \
      this.category = ``instr_category;  \
      this.imm_type = ``imm_tp;  \
      this.instr_type = ``instr_t;  \
      this.allowed_va_variants = ``vav; \
      if (this.instr_type == FLOATING_POINT) begin \
        has_fs1 = 1; \
        has_fs2 = 1; \
        has_fs3 = 1; \
        has_fd = 1; \
      end \
      if (this.instr_type == VECTOR) begin \
        has_vd = 1'b1;  \
        has_vs1 = 1'b1; \
        has_vs2 = 1'b1; \
        has_vs3 = 1'b0; \
        has_va_variant = 1'b0; \
        is_widening_instr = 1'b0; \
        is_narrowing_instr = 1'b0; \
        is_convert_instr = 1'b0; \
        is_reduction_instr = 1'b0; \
        is_mask_producing_instr = 1'b0; \
        is_mask_operands = 1'b0; \
        is_fp_instr = 1'b0; \
        is_segmented_ls_instr = 1'b0; \
        is_whole_register_ls_instr = 1'b0; \
        ext_widening_factor = 1; \
        whole_register_move_cnt = 1; \
      end \
      set_imm_len(); \
      set_rand_mode(); \
      `uvm_info("INSTR_BODY", $sformatf("class: %s name: %s instr_name: %s format: %s group: %s category: %s imm_type: %s instr_type: %s fd: %0d%0d%0d%0d", get_type_name(), name, instr_name.name(), format.name(), group.name(), category.name(), imm_type.name(), instr_type.name(), has_fs1, has_fs2, has_fs3, has_fd), UVM_DEBUG) \
    endfunction \
  endclass

// Regular integer instruction
`define DEFINE_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// CSR instructions
`define DEFINE_CSR_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM, instr_t=CSR_INSTR)  \
  class riscv_``instr_n``_instr extends riscv_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp, instr_t)

// Floating point instruction
`define DEFINE_FP_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM, instr_t=FLOATING_POINT)  \
  class riscv_``instr_n``_instr extends riscv_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp, instr_t)

// A-extension instruction
`define DEFINE_AMO_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM, instr_t=ATOMIC)  \
  class riscv_``instr_n``_instr extends riscv_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp, instr_t)

// Compressed instruction
`define DEFINE_C_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_compressed_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

// Floating point compressed instruction
`define DEFINE_FC_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM, instr_t=FLOATING_POINT)  \
  class riscv_``instr_n``_instr extends riscv_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp, instr_t)

// Vector instruction
`define DEFINE_V_INSTR(instr_n, instr_format, instr_category, instr_group, vav = {}, imm_tp = IMM, instr_t=VECTOR)\
  class riscv_``instr_n``_instr extends riscv_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp, instr_t, vav)

// Custom extension instruction
`define DEFINE_CUSTOM_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_custom_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

//B-extension instruction
`define DEFINE_B_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends riscv_b_instr;  \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

//Zba-extension instruction
`define DEFINE_ZBA_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM) \
  class riscv_``instr_n``_instr extends riscv_zba_instr; \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

//Zbb-extension instruction
`define DEFINE_ZBB_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM) \
  class riscv_``instr_n``_instr extends riscv_zbb_instr; \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

//Zbc-extension instruction
`define DEFINE_ZBC_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM) \
  class riscv_``instr_n``_instr extends riscv_zbc_instr; \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)

//Zbs-extension instruction
`define DEFINE_ZBS_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM) \
  class riscv_``instr_n``_instr extends riscv_zbs_instr; \
    `INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)
