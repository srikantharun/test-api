`include "ai_core_dp_cmd_gen_base_test.svh"

`ifndef GUARD_AI_CORE_DP_CMD_GEN_TEST_LIB
`define GUARD_AI_CORE_DP_CMD_GEN_TEST_LIB

class ai_core_dp_cmd_gen_legal_test extends ai_core_dp_cmd_gen_base_test;

  constraint c_cmdb_wait_on_done { wait_on_done dist {0        := 5,  1        := 1}; }
  constraint c_cmdb_rate         { rate         dist {[80:100] := 2,  [10:79]  :/ 1, [1:9] :/ 1}; }

  `uvm_component_utils(ai_core_dp_cmd_gen_legal_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type = ai_core_dp_cmd_gen_cmdb_legal::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_legal_test

class ai_core_dp_cmd_gen_random_test extends ai_core_dp_cmd_gen_base_test;

  constraint c_cmdb_n_transacations   { soft n_transactions inside {[40:60]}; }
  constraint c_cmdb_wait_on_done      { wait_on_done        dist   {0        := 5,  1        := 1}; }
  constraint c_cmdb_rate              { rate                dist   {[80:100] := 2,  [10:79]  :/ 1, [1:9] :/ 1}; }
  constraint c_cmdb_pc_error          { pc_error            dist   {[1:20]}; }

  `uvm_component_utils(ai_core_dp_cmd_gen_random_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_legal::get_type();
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_random_test

class ai_core_dp_cmd_gen_single_outstanding_cmdb_test extends ai_core_dp_cmd_gen_base_test;

  constraint c_cmdb_wait_on_done { wait_on_done  == 1; }

  `uvm_component_utils(ai_core_dp_cmd_gen_single_outstanding_cmdb_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_legal::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_single_outstanding_cmdb_test

class ai_core_dp_cmd_gen_slow_cmdb_test extends ai_core_dp_cmd_gen_base_test;

  constraint c_cmdb_wait_on_done { wait_on_done  == 1; }
  constraint c_cmdb_rate         { rate          inside {[1:3]}; }

  `uvm_component_utils(ai_core_dp_cmd_gen_slow_cmdb_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_short::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_slow_cmdb_test

class ai_core_dp_cmd_gen_multi_agent_test extends ai_core_dp_cmd_gen_legal_test;

  constraint c_cmdb_n_agents      { n_agents       inside {2,4};   }
  constraint c_cmdb_n_programs    { n_programs     inside {[2:4]}; }
  constraint c_cmd_n_transactions { n_transactions inside {[1:5]}; }

  `uvm_component_utils(ai_core_dp_cmd_gen_multi_agent_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
  endfunction : new

endclass : ai_core_dp_cmd_gen_multi_agent_test

class ai_core_dp_cmd_gen_bypass_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_bypass_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_bypass::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_bypass_test

class ai_core_dp_cmd_gen_m1n0_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_m1n0_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_m1n0::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_m1n0_test

class ai_core_dp_cmd_gen_m1n1_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_m1n1_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_m1n1::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_m1n1_test

class ai_core_dp_cmd_gen_m1n2_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_m1n2_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_m1n2::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_m1n2_test

class ai_core_dp_cmd_gen_m2n0_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_m2n0_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_m2n0::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_m2n0_test

class ai_core_dp_cmd_gen_m2n1_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_m2n1_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_m2n1::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_m2n1_test

class ai_core_dp_cmd_gen_m2n2_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_m2n2_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_m2n2::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_m2n2_test

class ai_core_dp_cmd_gen_m3n0_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_m3n0_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_m3n0::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_m3n0_test

class ai_core_dp_cmd_gen_m3n1_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_m3n1_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_m3n1::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_m3n1_test

class ai_core_dp_cmd_gen_m3n2_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_m3n2_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_m3n2::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_m3n2_test

class ai_core_dp_cmd_gen_separate_nested_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_separate_nested_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_separate_nested::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_separate_nested_test

class ai_core_dp_cmd_gen_nested_main_same_start_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_nested_main_same_start_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_nested_main_same_start::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_nested_main_same_start_test

class ai_core_dp_cmd_gen_nested_main_same_end_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_nested_main_same_end_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_nested_main_same_end::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_nested_main_same_end_test

class ai_core_dp_cmd_gen_overlapping_main_test extends ai_core_dp_cmd_gen_base_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_overlapping_main_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.legal_override_type   = ai_core_dp_cmd_gen_cmdb_overlapping_main::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_overlapping_main_test

// Error cases
class ai_core_dp_cmd_gen_error_test extends ai_core_dp_cmd_gen_base_test;

  constraint c_cmdb_pc_error  { pc_error == 100; }

  `uvm_component_utils(ai_core_dp_cmd_gen_error_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal::get_type();
  endfunction : new

  function void end_of_elaboration_phase(uvm_phase phase);
    // Disable command scoreboard
    m_env.m_command_sb.comp_min = 0;
    super.end_of_elaboration_phase(phase);
  endfunction : end_of_elaboration_phase

endclass : ai_core_dp_cmd_gen_error_test

class ai_core_dp_cmd_gen_illegal_format_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_format_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_format::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_format_test

class ai_core_dp_cmd_gen_empty_program_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_empty_program_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_empty_program::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_empty_program_test

class ai_core_dp_cmd_gen_illegal_main_0_length_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_main_0_length_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_main_0_length::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_main_0_length_test

class ai_core_dp_cmd_gen_illegal_main_1_length_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_main_1_length_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_main_1_length::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_main_1_length_test

class ai_core_dp_cmd_gen_illegal_main_2_length_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_main_2_length_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_main_2_length::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_main_2_length_test

class ai_core_dp_cmd_gen_illegal_nested_0_length_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_nested_0_length_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_nested_0_length::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_nested_0_length_test

class ai_core_dp_cmd_gen_illegal_nested_1_length_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_nested_1_length_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_nested_1_length::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_nested_1_length_test

class ai_core_dp_cmd_gen_illegal_nested_0_mapping_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_nested_0_mapping_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_nested_0_mapping::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_nested_0_mapping_test

class ai_core_dp_cmd_gen_illegal_nested_1_mapping_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_nested_1_mapping_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_nested_1_mapping::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_nested_1_mapping_test

class ai_core_dp_cmd_gen_illegal_nested_0_segfault_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_nested_0_segfault_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_nested_0_segfault::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_nested_0_segfault_test

class ai_core_dp_cmd_gen_illegal_nested_1_segfault_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_nested_1_segfault_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_nested_1_segfault::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_nested_1_segfault_test

class ai_core_dp_cmd_gen_illegal_nested_order_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_nested_order_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_nested_order::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_nested_order_test

class ai_core_dp_cmd_gen_illegal_nested_nesting_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_nested_nesting_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_nested_nesting::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_nested_nesting_test

class ai_core_dp_cmd_gen_illegal_nested_overlap_test extends ai_core_dp_cmd_gen_error_test;

  `uvm_component_utils(ai_core_dp_cmd_gen_illegal_nested_overlap_test)

  function new (string name="", uvm_component parent);
    super.new (name, parent);
    this.illegal_override_type = ai_core_dp_cmd_gen_cmdb_illegal_nested_overlap::get_type();
  endfunction : new

endclass : ai_core_dp_cmd_gen_illegal_nested_overlap_test

`endif	// GUARD_AI_CORE_DP_CMD_GEN_TEST_LIB
