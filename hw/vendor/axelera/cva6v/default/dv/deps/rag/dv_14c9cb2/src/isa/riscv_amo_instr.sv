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

rand bit aq;
rand bit rl;

constraint aq_rl_c {
  (instr_type == ATOMIC) -> (aq && rl) == 0;
}

// Convert the instruction to assembly code
virtual function string atomic_convert2asm(string prefix = "");
  string asm_str;
  asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
  if (group inside {RV32A, RV64A}) begin
    if (instr_name inside {LR_W, LR_D}) begin
      asm_str = $sformatf("%0s %0s, (%0s)", asm_str, rd.name(), rs1.name());
    end else begin
      asm_str = $sformatf("%0s %0s, %0s, (%0s)", asm_str, rd.name(), rs2.name(), rs1.name());
    end
  end else begin
    `uvm_fatal(`gfn, $sformatf("Unexpected amo instr group: %0s / %0s",
                                group.name(), instr_name.name()))
  end
  if(comment != "")
    asm_str = {asm_str, " #",comment};
  return asm_str.tolower();
endfunction : atomic_convert2asm


