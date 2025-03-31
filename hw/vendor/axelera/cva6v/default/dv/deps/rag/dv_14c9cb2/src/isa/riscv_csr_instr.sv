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

static riscv_instr_pkg::privileged_reg_t unsafe_to_random_access_regs[$];
static riscv_reg_t csr_directed_gpr_list[$] = {};
rand bit write_csr;

// New selection process for CSR that does not depend on include_reg and exclude_reg
constraint csr_selection_c {
  (instr_type == CSR_INSTR) -> csr inside {implemented_csr};
}

constraint csr_exclusion_c {
  (instr_type == CSR_INSTR) -> !(csr inside {unimplemented_csr});
  (instr_type == CSR_INSTR) -> !(csr inside {unsafe_to_random_access_regs});
}

constraint csr_csrrw_c {
  if ((instr_name == CSRRW || instr_name == CSRRWI) && (instr_type == CSR_INSTR)) {
    write_csr == 1'b1;
  }
}

constraint csr_csrrsc_c {
  if ((instr_name == CSRRS || instr_name == CSRRC) && (instr_type == CSR_INSTR)) {
    (write_csr == 1'b1) || rs1 == 0;
  }
}

constraint csr_csrrsci_c {
  if ((instr_name == CSRRSI || instr_name == CSRRCI) && (instr_type == CSR_INSTR)) {
    (write_csr == 1'b1) || imm == 0;
  }
}

constraint csr_rd_directed_c {
  (csr_directed_gpr_list.size()!=0 && instr_type==CSR_INSTR) ->  rd inside {csr_directed_gpr_list};
}

// Don't do dummy writes to RO ID registers, traps here doesn't produce anything useful
constraint csr_ro_c {
  (csr inside {MVENDORID, MARCHID, MIMPID, MHARTID, MCONFIGPTR}) -> write_csr == 1'b0;
}

constraint csr_order_c {
  // Choose a CSR before deciding whether we want to write to the CSR values. Then choose whether
  // to read or write before choosing the rs1 and imm values. This ensures read-only accesses to
  // read-only CSRs with similar probability to other CSR accesses and ensures a reasonable write
  // vs read distribution for CSRs that can be written.
  solve csr before write_csr, rs1, imm;
  solve write_csr before rs1, imm;
}


static function void create_csr_filter(riscv_instr_gen_config cfg);
  unsafe_to_random_access_regs.delete();
  unsafe_to_random_access_regs = {implemented_csr}; // make every CSR unsafe and then only access the list of every specific csrs
  if (cfg.specific_csrs.size()>0) begin
    remove_csrs_from_queue(cfg.specific_csrs, unsafe_to_random_access_regs); // unexclude specific CSR's
  end else begin
    case (cfg.init_privileged_mode)
      default: remove_csrs_from_queue(safe_m_mode_csr, unsafe_to_random_access_regs);
      SUPERVISOR_MODE: remove_csrs_from_queue(safe_s_mode_csr, unsafe_to_random_access_regs);
      USER_MODE: remove_csrs_from_queue(safe_u_mode_csr, unsafe_to_random_access_regs);
    endcase
    // do not touch V/F CSR's if the V/F extension is disabled
    if (!cfg.enable_fp_extension) add_csrs_from_queue(implemented_f_csr, unsafe_to_random_access_regs);
    if (!cfg.enable_vector_extension) add_csrs_from_queue(implemented_v_csr, unsafe_to_random_access_regs);
  end
  `uvm_info("riscv_csr_instr", $sformatf("%s unsafe_to_random_access_regs: %p  \n", instr_type.name(), unsafe_to_random_access_regs), UVM_NONE)
  foreach (cfg.csr_directed_gpr_list[i]) csr_directed_gpr_list.push_back(cfg.csr_directed_gpr_list[i]);
endfunction : create_csr_filter

virtual function void csr_set_rand_mode();
  base_set_rand_mode();
  has_rs2 = 1'b0;
  if (format == I_FORMAT) begin
    has_rs1 = 1'b0;
  end
endfunction

// Convert the instruction to assembly code
virtual function string csr_convert2asm(string prefix = "");
  string asm_str;
  string csr_str;
  asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
  csr_str = (csr inside {custom_csr})? $sformatf("0x%3h", csr): csr.name();
  comment = (csr inside {custom_csr})? {comment, $sformatf("custom csr: %s", csr.name())}: comment;

  case(format)
      I_FORMAT: // instr rd,rs1,imm
        asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), csr_str, get_imm());
      R_FORMAT: // instr rd,rs1,rs2
        asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), csr_str, rs1.name());
      default:
        `uvm_fatal(`gfn, $sformatf("Unsupported format %0s [%0s]", format.name(), instr_name.name()))
  endcase

  if(comment != "") asm_str = {asm_str, " #",comment};
  asm_str = append_csr_wr(asm_str);
  return asm_str.tolower();
endfunction : csr_convert2asm

// Masking in CSV is not enough. We need to write values as well to not propagate the errors further
virtual function string append_csr_wr(string asm_str);
  string final_str;
  string appended_str;

  if (has_rd  && csr inside {implemented_counter_csr} && !(csr inside {read_only_counter_csr})) begin
    appended_str = {"\n                  ", format_string("csrrwi", MAX_INSTR_STR_LEN)};
    appended_str = $sformatf("%0s%0s, %0s, %0d # appended", appended_str, rd.name(), csr.name(), $urandom_range(0,31));
    final_str = {asm_str, appended_str};
  end else begin
    final_str = asm_str;
  end
  return final_str;
endfunction : append_csr_wr


static function void remove_csrs_from_queue(privileged_reg_t input_array[], ref privileged_reg_t main_queue[$]);

  // Iterate over the main queue
  for (int i = 0; i < main_queue.size(); i++) begin
    // Compare each element in the main queue with the input queue
    foreach (input_array[j]) begin
      if (main_queue[i] == input_array[j]) begin
        // Remove the element if it's found in the input queue
        main_queue.delete(i);
        i--;  // Adjust the index after deletion
        break;  // Move to the next element in the main queue
      end
    end
  end
endfunction

static function void add_csrs_from_queue(privileged_reg_t input_array[], ref privileged_reg_t main_queue[$]);
  foreach (input_array[i]) begin
    if (!(input_array[i] inside {main_queue})) begin
      main_queue.push_back(input_array[i]);
    end
  end
endfunction
