package ai_core_dwpu_test_pkg;

  timeunit 1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
    import axi_icdf_pkg::*;
  `endif

  import aic_common_pkg::*;
  import dwpu_pkg::*;
  import dwpu_csr_ral_pkg::*;
  import ai_core_dwpu_seq_pkg::*;
  import ai_core_dwpu_env_pkg::*;
  import token_agent_uvm_pkg::*;
  import ai_core_dwpu_agent_pkg::*;
  import ai_core_dwpu_common_pkg::*;

  typedef string string_queue_t [$];
  typedef int int_index_arr_t[int];

  //include macros to be used in cmd sequence
  `include "ai_core_dp_cmd_gen_cmdb_macros.svh"

  //RAL and memory tests
  `include "ai_core_dwpu_base_test.sv"
  `include "ai_core_dwpu_ral_test.sv"
  `include "ai_core_dwpu_ral_custom_test.sv"
  `include "ai_core_dwpu_address_map_holes_resp_test.sv"
  `include "ai_core_dwpu_prog_mem_access_test.sv"

  //Validate ref model test
  `include "ai_core_dwpu_icdf_test.sv"

  //Functional tests
  `include "ai_core_dwpu_standard_test.sv"
  `include "ai_core_dwpu_extensive_standard_test.sv"
  `include "ai_core_dwpu_irq_test.sv"
  `include "ai_core_dwpu_stream_bypass_test.sv"
  `include "ai_core_dwpu_loop_test.sv"
  `include "ai_core_dwpu_parallel_loops_wo_interlog_test.sv"
  `include "ai_core_dwpu_cmd_fifo_overflow_test.sv"
  `include "ai_core_dwpu_small_cmds_fifo_overflow_test.sv"
  `include "ai_core_dwpu_concurrency_cmd_prog_test.sv"
  //`include "ai_core_dwpu_standard_greater_init_iter_num_test.sv"
  //`include "ai_core_dwpu_standard_greater_outer_iter_num_test.sv"
  //`include "ai_core_dwpu_standard_greater_inner0_iter_num_test.sv"
  //`include "ai_core_dwpu_standard_greater_inner1_iter_num_test.sv"
  `include "ai_core_dwpu_axi_access_coverage_test.sv"
  `include "ai_core_dwpu_single_instr_no_input_no_output_test.sv"
  `include "ai_core_dwpu_in_word_ptr_test.sv"
endpackage : ai_core_dwpu_test_pkg

