package ai_core_mvm_test_pkg;

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
  import mvm_pkg::*;

  import token_agent_uvm_pkg::*;
  import cc_clk_div_agent_uvm_pkg::*;
  import ai_core_mvm_common_pkg::*;
  import ai_core_mvm_ral_pkg::*;
  import ai_core_mvm_seq_pkg::*;
  import ai_core_mvm_env_pkg::*;


  `include "cust_svt_axi_master_transaction.svh"

  `include "ai_core_mvm_demoter.svh"
   //// AXI Tests
  `include "ai_core_mvm_base_test.svh"
  `include "ai_core_mvm_ral_base_test.svh"
  `include "ai_core_mvm_axi_rnd_discr_test.svh"
  // RAL Tests
  `include "ai_core_mvm_ral_hw_rst_test.svh"
  `include "ai_core_mvm_ral_bit_bash_test.svh"
  `include "ai_core_mvm_ral_single_wrrd_test.svh"
  // Register Tests
  `include "ai_core_mvm_reg_unmapped_address_access_test.svh"
  `include "ai_core_mvm_reg_burst_access_test.svh"
  `include "ai_core_mvm_reg_burst_with_crossing_boundary_test.svh"
  `include "ai_core_mvm_reg_narrow_access_test.svh"
  `include "ai_core_mvm_reg_write_to_read_only_reg_access_test.svh"

  // MVM Tests
  `include "ai_core_mvm_basic_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_test.svh"
  `include "ai_core_mvm_signed_single_matrix_multiplication_test.svh"
  `include "ai_core_mvm_random_matrix_multiplication_base_test.svh"
  `include "ai_core_mvm_random_matrix_multiplication_test.svh"
  `include "ai_core_mvm_random_matrix_multiplication_with_register_test.svh"
  `include "ai_core_mvm_bypass_test.svh"
  `include "ai_core_mvm_concurrent_prg_exe_random_matrix_multiplication_test.svh"
  `include "ai_core_irq_test.svh"
  `include "ai_core_mvm_random_matrix_multiplication_token_test.svh"
  `include "ai_core_mvm_clock_div_test.svh"
  // Power Surge Test
  `include "ai_core_mvm_power_surge_test.svh"
  `include "ai_core_mvm_b2b_test.svh"
  `include "ai_core_mvm_single_matrix_uns_mltplctn_bckprsr_test.svh"
  `include "ai_core_mvm_concurrent_prg_exe_random_matrix_mltplctn_bckprsr_test.svh"
  `include "ai_core_mvm_bist_no_error_test.svh"
  `include "ai_core_mvm_bist_error_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_test_1x2_sw_test_mode.svh"
  `include "ai_core_mvm_random_row_col_matrix_multiplication_test.svh"
  `include "ai_core_mvm_icdf_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_dibw_simple_mode_test.svh"
  `include "ai_core_mvm_random_matrix_multiplication_test_sw_test_mode.svh"
  `include "ai_core_mvm_rand_matrix_multiplication_fix_offset_dibw_simple_mode_test.svh"
  `include "ai_core_mvm_rand_matrix_multiplication_dibw_simple_mode_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_dibw_advance_mode_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_dibw_simple_mode_broadcast_test.svh"
  `include "ai_core_mvm_rand_matrix_multiplication_dibw_simple_mode_broadcast_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_rand_loop_len_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_prgmode_1_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_prgmode_1_broadcast_mode_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_prgmode_2_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_prgmode_2_broadcast_mode_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_rand_loop_len_test.svh"
  `include "ai_core_mvm_address_holes_with_slverr_resp_test.svh"
  `include "ai_core_mvm_random_matrix_multiplication_prgmode_1_test.svh"
  `include "ai_core_mvm_random_matrix_multiplication_prgmode_2_test.svh"
  `include "ai_core_mvm_concurrent_prg_exe_rand_matrix_multiplication_dibw_simple_mode_test.svh"
  `include "ai_core_mvm_concurrent_prg_exe_rand_matrix_multiplication_dibw_simple_mode_bckprsr_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_dibw_simple_mode_test_1x2.svh"
  `include "ai_core_mvm_random_matrix_multiplication_rand_prgmode_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_int16_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_test_fifo_overflow.svh"
  `include "ai_core_mvm_rand_offset_matrix_multiplication_test.svh"
  `include "ai_core_mvm_matrix_multiplication_dibw_advance_mode_test.svh"
  `include "ai_core_mvm_random_matrix_unsigned_multiplication_test.svh"
  `include "ai_core_mvm_single_matrix_multiplication_prgmode_1_1x1_test.svh"
  `include "ai_core_mvm_matrix_multiplication_dibw_advance_mode_loop_test.svh"
endpackage : ai_core_mvm_test_pkg
