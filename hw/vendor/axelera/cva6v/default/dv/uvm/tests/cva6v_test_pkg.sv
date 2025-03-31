// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Test Package
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef GUARD_CVA6V_TEST_PACKAGE_SV
`define GUARD_CVA6V_TEST_PACKAGE_SV

package cva6v_test_pkg;

  timeunit 1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import cva6v_env_pkg::*;
  import cva6v_seq_pkg::*;

  import raptor_pkg::*;
  import cva6v_ariane_pkg::*;
  import cva6v_config_pkg::*;
  import cva6v_ai_core_pkg::*;

  // -----------------------------
  // Test Control
  // -----------------------------
  int unsigned drain_cycles = 2000;

  // -----------------------------
  // Memory Functions
  // -----------------------------
  bit[63:0] simple_mem [int unsigned];

  function void parse_c_mem_log();
    string line;
    int file_handle, index;
    int counter=0;
    int addr;
    int data;

    file_handle = $fopen("c_mem.log", "r");
    if (file_handle) begin
      while($fgets(line,file_handle)) begin
        line = line.substr(0,line.len()-2); // remove \n
        if (string_search(line, "Write byte")) begin
          // [raptor.write] Write byte 80000000 = 35
          void'($sscanf(line, "[raptor.write] Write byte %h = %h", addr,data));
          //$display("[raptor.write] Write byte 0x%0x = 0x%0x", addr, data);
          add_to_memory (addr, data);
        end
      end
      $fclose(file_handle);
    end
    
    //foreach (simple_mem[i]) begin
    //  $display("Write DW 0x%0x = 0x%0x", i, simple_mem[i]);
    //end
  endfunction

  function bit string_search(string message, string pattern);
    automatic int unsigned match_count;
    automatic int unsigned len         = message.len();
    automatic int unsigned pattern_len = pattern.len();
  
    // somehow .len() gives 0! This should avoid it.
    if (len==0)         foreach (message[i]) len += 1;
    if (pattern_len==0) foreach (pattern[i]) pattern_len += 1;
    for(int i =0; i < len;i++) begin
      if(message.substr(i,i+pattern_len-1) ==pattern) begin
        match_count +=1;
      end
    end
    return (match_count>0);
  endfunction
  
  function void add_to_memory(int addr, int data);
    automatic int unsigned aligned_addr = addr;
    automatic int unsigned index;
    aligned_addr[2:0] = 0;
    index = addr - aligned_addr;
    if (simple_mem.exists(aligned_addr)) begin
      simple_mem[aligned_addr][index*8 +: 8] = data;
    end else begin
      simple_mem[aligned_addr] = 0;
      simple_mem[aligned_addr][index*8 +: 8] = data;
    end
  endfunction

  `include "cva6v/include/rvfi_types.svh"
  `include "cva6v/include/cva6v/cva6v_tracing.svh"
  `include "../../rtl/cva6v_dv_typedefs.svh"

  `include "cva6v_base_test.sv"
  `include "cva6v_sanity_test.sv"
endpackage : cva6v_test_pkg
`endif
