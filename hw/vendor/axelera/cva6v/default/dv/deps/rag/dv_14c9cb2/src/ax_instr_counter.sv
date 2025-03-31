/*
 (C) Copyright Axelera AI 2024
 All Rights Reserved
 *** Axelera AI Confidential ***

 Description: Instruction counter for generation statistics
 Owner: Pawel Wiecha <pawel.wiecha@axelera.ai>
*/

class riscv_instr_counter extends uvm_object;
  typedef int unsigned counter_t[riscv_instr_category_t];
  typedef string string_arr_t[];
  counter_t category_counter;
  int unsigned floating_point_count;
  int unsigned vector_count;
  int unsigned total_count;
  int unsigned report_size;

  `uvm_object_utils(riscv_instr_counter)

  function new(string name = "riscv_instr_counter");
    riscv_instr_category_t instr;
    riscv_instr_category_t category_enum_size;
    super.new(name);
    floating_point_count = 0;
    vector_count = 0;
    total_count = 0;
    for(int i = 0; i < category_enum_size.num(); i++) begin
      instr = riscv_instr_category_t'(i);
      category_counter[instr] = 0;
    end
    report_size = category_enum_size.num() + 5;
  endfunction

  function void count(riscv_instr instr);
    category_counter[instr.category]++;
    if (instr.group inside {RV32F, RV32FC, RV32D, RV32DC, RV64F, RV64D, ZFH}) begin
      floating_point_count++;
    end
    if (instr.group == RVV) begin
      vector_count++;
    end
    total_count++;
  endfunction

  function void display_report();
    $display("Generation statistics");
    foreach (category_counter[i]) begin
      $display("%s instructions : %0d (%.2f%%)", i.name(), category_counter[i], (category_counter[i]*100.0)/total_count);
    end
    $display("Floating point count: %0d (%.2f%%)", floating_point_count, (floating_point_count*100.0)/total_count);
    $display("Vector count: %0d (%.2f%%)", vector_count, (vector_count*100.0)/total_count);
    $display("Total count: %0d", total_count);
    $display("********************");
  endfunction

  function string_arr_t get_report();
    string lines [] = new [report_size];
    int index = 0;

    lines[index++] = "# Generation statistics";
    foreach (category_counter[i]) begin
      lines[index++] = $sformatf("# %s instructions: %0d (%.2f%%)", i.name(), category_counter[i], (category_counter[i] * 100.0) / total_count);
    end
    lines[index++] = $sformatf("# Floating point count: %0d (%.2f%%)", floating_point_count, (floating_point_count*100.0)/total_count);
    lines[index++] = $sformatf("# Vector count: %0d (%.2f%%)", vector_count, (vector_count*100.0)/total_count);
    lines[index++] = $sformatf("# Total count: %0d", total_count);
    lines[index++] = "# ********************";
    return lines;
  endfunction

  // Method to update the counter with values from another counter
  function void update_counter_from(riscv_instr_counter other);
    foreach (category_counter[i]) begin
      this.category_counter[i] += other.category_counter[i];
    end
    this.floating_point_count += other.floating_point_count;
    this.vector_count += other.vector_count;
    this.total_count += other.total_count;
  endfunction

endclass
