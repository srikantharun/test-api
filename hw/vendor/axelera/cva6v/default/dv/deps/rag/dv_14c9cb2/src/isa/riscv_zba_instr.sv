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
class riscv_zba_instr extends riscv_instr;
  `uvm_object_utils(riscv_zba_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void pre_randomize();
    super.pre_randomize();
  endfunction

  virtual function void set_imm_len();
    if (!(instr_name inside {SLLI_UW})) begin
      imm_len = $clog2(XLEN) - 1;
    end else begin
      imm_len = $clog2(XLEN);
    end
    imm_mask = imm_mask << imm_len;
  endfunction : set_imm_len

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    return (cfg.enable_zba_extension &&
           (RV32ZBA inside { supported_isa } || RV64ZBA inside { supported_isa }) &&
           instr_name inside {
             ADD_UW,
             SH1ADD, SH1ADD_UW,
             SH2ADD, SH2ADD_UW,
             SH3ADD, SH3ADD_UW,
             SLLI_UW
           });
  endfunction : is_supported

endclass : riscv_zba_instr



