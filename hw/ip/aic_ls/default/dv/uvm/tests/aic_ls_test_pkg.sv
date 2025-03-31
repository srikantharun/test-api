// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Test Package
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_DMC_TEST_PACKAGE_SV
`define GUARD_AIC_DMC_TEST_PACKAGE_SV

package aic_ls_test_pkg;

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
  import dmc_pkg::*;
  import l1_pkg::*;
  import mmio_pkg::*;
  import aic_ls_csr_ral_pkg::*;
  import v_utils_pkg::*;
  import dmc_addr_gen_agent_pkg::*;
  import dmc_addr_gen_ref_model_pkg::*;
  import token_agent_uvm_pkg::*;
  import aic_ls_agent_pkg::*;
  import aic_ls_env_pkg::*;
  import aic_ls_seq_pkg::*;
  import rvv_agent_pkg::*;

  localparam AXI_LP_DATA_WIDTH = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH;

  typedef aic_ls_ifd_seq#(aic_ls_env)            aic_ls_ifd_seq_t;
  typedef aic_ls_odr_seq#(aic_ls_env)            aic_ls_odr_seq_t;
  typedef aic_ls_l1_init_seq#(aic_ls_env)        aic_ls_l1_init_seq_t;
  typedef bit[AIC_HT_AXI_DATA_WIDTH/4-1:0] data_sb_axis_quarter_data_t; // memory blocks are divided into blocks of 128 bits of data
  typedef bit[L1_BANK_DATA_WIDTH-1:0] l1_data_t;
  typedef bit[L1_BANK_DATA_WIDTH/2-1:0] l1_half_data_t;
  typedef bit[L1_BANK_DATA_WIDTH/4-1:0] l1_quarter_data_t;
  typedef bit[AIC_LS_ENV_L1_SRAM_FULL_SIZE-1:0] l1_phys_data_t;
  typedef bit[AIC_LS_ENV_L1_SRAM_WORD_SIZE-1:0] l1_phys_word_t;
  typedef rvv_sequence#(MMIO_RVV_DATA_WIDTH, MMIO_RVV_ADDR_WIDTH) rvv_sequence_t;
  typedef string string_queue_t [$];

`ifdef AXI_VIP
  // AXI Tests
  `include "aic_ls_demoter.svh"
  `include "aic_ls_base_test.svh"
  `include "aic_ls_axi_cfg_rd_rnd_test.svh"
  `include "aic_ls_axi_cfg_rnd_test.svh"  // seems old and outdated to me. will not put into nightly
  `include "aic_ls_axi_hp_s_fixed_test.svh"
  `include "aic_ls_axi_directed_test.svh"
  `include "aic_ls_axi_rnd_test.svh"
  `include "aic_ls_axi_rnd_discr_test.svh"
  // `include "aic_ls_axi_m_wrrd_souts_perid_test.svh"
  // `include "aic_ls_axi_m_aligned_addr_test.svh"
  // `include "aic_ls_axi_m_blking_alt_wrrd_test.svh"
  // `include "aic_ls_axi_m_blking_wrrd_test.svh"
  // `include "aic_ls_axi_m_write_data_bfr_addr_test.svh"
  //   // RAL Tests
  // `include "aic_ls_ral_hw_rst_test.svh"
  // `include "aic_ls_ral_bit_bash_test.svh"
  `include "aic_ls_ral_single_wrrd_test.svh"
  // `include "aic_ls_ral_wrrd_test.svh"
  // `include "aic_ls_ral_check_test.svh"
  // `include "aic_ls_ral_woro_test.svh"
  `include "aic_ls_ral_decerr_test.svh"

  // // IFDs/ODRs TC Tests
  `include "aic_ls_dmc_cmdb_tc_test.svh"
  `include "aic_ls_dmc_cmdb_defbased_test.svh"
  `include "aic_ls_dmc_cmdb_lightcmd_test.svh"
  `include "aic_ls_dmc_cmdb_offsetbased_test.svh"
  `include "aic_ls_dmc_cmdb_3Dfallback_test.svh"
  `include "aic_ls_dmc_cmdb_4Dfallback_test.svh"
  `include "aic_ls_dmc_cmdb_addr_out_of_range_test.svh"
  // `include "aic_ls_dmc_cmdb_tlast_high_test.svh"
  // `include "aic_ls_dmc_cmdb_tlast_low_test.svh"
  // `include "aic_ls_dmc_cmdb_ringbuffer_test.svh"
  // `include "aic_ls_dmc_cmdb_sweep_mask_start_test.svh"
  // `include "aic_ls_dmc_cmdb_sweep_mask_end_test.svh"
  // `include "aic_ls_dmc_cmdb_sweep_mask_start_dim_test.svh"
  // `include "aic_ls_dmc_cmdb_sweep_mask_end_dim_test.svh"
  // `include "aic_ls_dmc_cmdb_sweep_inner_stride_test.svh"
  // `include "aic_ls_dmc_cmdb_sweep_outer_stride_test.svh"
  // `include "aic_ls_dmc_cmdb_sweep_dim_offset_test.svh"
  `include "aic_ls_dmc_cmdb_vtrsp_test.svh"
  `include "aic_ls_dmc_cmdb_vtrsp_sweep_test.svh"
  `include "aic_ls_dmc_cmdb_vtrsp_irq_test.svh"
  // `include "aic_ls_dmc_cmdb_vtrsp_access_error_test.svh"
  `include "aic_ls_dmc_cmdb_decompression_test.svh"
  // `include "aic_ls_dmc_cmdb_decomp_directed_test.svh"
  `include "aic_ls_dmc_cmdb_decomp_error_test.svh"
  // `include "aic_ls_dmc_cmdb_decomp_b2b_test.svh"
  // `include "aic_ls_dmc_cmdb_memstride_zero_test.svh"
  `include "aic_ls_dmc_cmdb_b2b_test.svh"
  `include "aic_ls_dmc_cmdb_b2b_concurrent_test.svh"
  `include "aic_ls_dmc_cmdb_fifo_overflow_test.svh"
  `include "aic_ls_dmc_cmdb_int_casting_test.svh"
  // `include "aic_ls_dmc_cmdb_high_dim_w_test.svh"
  // `include "aic_ls_dmc_cmdb_high_inner_len_test.svh"
  // `include "aic_ls_dmc_cmdb_high_outer_len_test.svh"
  // `include "aic_ls_dmc_cmdb_high_memstride_test.svh"
  // `include "aic_ls_dmc_cmdb_high_ringbuffsize_test.svh"
  // `include "aic_ls_dmc_cmdb_partial_defmem_test.svh"
  // `include "aic_ls_dmc_cmdb_membaseaddr_test.svh"
  // `include "aic_ls_dmc_cmdb_dim_loop_ptr_max_test.svh"
  // `include "aic_ls_dmc_cmdb_memoffset_test.svh"
  // `include "aic_ls_dmc_cmdb_memoffset_ringbuffer_test.svh"
  `include "aic_ls_dmc_defmem_access_test.svh"
  `include "aic_ls_dmc_defmem_bad_access_test.svh"
  `include "aic_ls_dmc_csr_bad_access_test.svh"
  // `include "aic_ls_dmc_va_test.svh"
  // `include "aic_ls_dmc_va_zero_test.svh"
  `include "aic_ls_sanity_test.svh"

  // // Token MGR Tests
  `include "aic_ls_tkn_mgr_dmc_test.svh"
  // `include "aic_ls_tkn_mgr_mvm_test.svh"
  // `include "aic_ls_tkn_mgr_swep_test.svh"
  // `include "aic_ls_tkn_mgr_swep_prod_sat_sweep_test.svh"
  // `include "aic_ls_tkn_mgr_swep_cons_sat_sweep_test.svh"
  // `include "aic_ls_tkn_mgr_swep_cons_nonzero_sweep_test.svh"
  // `include "aic_ls_tkn_mgr_generic_prod_sat_sweep_test.svh"
  // `include "aic_ls_tkn_mgr_dmc_b2b_test.svh"
  // `include "aic_ls_tkn_mgr_sweep_num_tokens_test.svh"

  // // L1 tests
  `include "aic_ls_l1_mem_test.svh"
  `include "aic_ls_l1_mem_b2b_test.svh"
  // `include "aic_ls_l1_tc_concurrency_test.svh"
  // `include "aic_ls_l1_same_bank_test.svh"
  `include "aic_ls_l1_mem_size_test.svh"
  // `include "aic_ls_l1_power_test.svh"
  // `include "aic_ls_l1_deadlock_test.svh"
  // `include "aic_ls_l1_fabric_sel_test.svh"
  // `include "aic_ls_l1_sram_sw_test.svh"

  // // LS tests in general
  // `include "aic_ls_reset_test.svh"
  // `include "aic_ls_clock_gate_test.svh"
  // `include "aic_ls_token_spill_test.svh"

  // RVV tests
  `include "aic_ls_rvv_basic_test.svh"
  `include "aic_ls_simple_concurrency_test.svh"
  `include "aic_ls_full_concurrency_test.svh"

  `include "aic_ls_icdf_stimuli_test.svh"

`endif
endpackage : aic_ls_test_pkg
`endif
