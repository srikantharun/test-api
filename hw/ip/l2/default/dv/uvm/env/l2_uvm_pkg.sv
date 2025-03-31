
`ifndef GUARD_L2_UVM_PKG_SV
`define GUARD_L2_UVM_PKG_SV

`define AXI_VIP
`define APB_VIP

// L2 UVM package
package l2_uvm_pkg;

  timeunit      1ns;
  timeprecision 1ns;
  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import l2_pkg::*;
  import chip_pkg::*;
  import l2_csr_ral_pkg::*;

  
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif
`ifdef APB_VIP
  import svt_apb_uvm_pkg::*;
 `endif

 // import ral_model_pkg::*;
 // import cc_clk_div_agent_uvm_pkg::*;

`ifdef AXI_VIP
   // Environment and environment Configurations
  `include "l2_tb_define.sv"
  `include "cust_svt_axi_system_configuration.sv"
  `include "cust_svt_axi_system_cc_configuration.sv"
  `include "cust_l2_svt_apb_system_cfg.sv"
  `include "axi_virtual_sequencer.sv"
  `include "apb_virtual_sequencer.svh"
  `include "cust_svt_apb_system_configuration.sv"
  // Scoreboard
  `include "axi_uvm_scoreboard.sv"
  `include "l2_env_cfg.sv"
  `include "l2_env.sv"
  `include "warning_catcher.sv"

  // Sequences
  `include "cust_svt_axi_master_transaction.sv"
  `include "axi_master_random_discrete_virtual_sequence.sv"
  `include "axi_slave_mem_response_sequence.sv"
  `include "axi_simple_reset_sequence.sv"
  `include "axi_null_virtual_sequence.sv"
  `include "axi_master_directed_sequence.sv"
  `include "axi_master_random_discrete_sequence.sv"
  `include "axi_master_wr_rd_wrap_sequence.sv"
  `include "l2_apb_seq_lib.svh"
  `include "l2_top_seq_library.sv" 
  `include "l2_top_seq_lib.sv"
  //`include "apb_write_master_directed_sequence.sv"
 // `include "apb_reset_if.svi"
  `include "apb_simple_reset_sequence.sv"

  // Tests

  `include "l2_base_test.sv"
  `include "l2_axi_sanity_test.sv"
  `include "l2_axi_directed_test.sv"
  `include "l2_axi_rnd_test.sv"
  `include "l2_axi_m_rnd_wrrd_test.sv"
  `include "l2_axi_rnd_discr_test.sv"
  `include "l2_axi_m_wrexact_test.sv"
  `include "l2_axi_m_wrrd_souts_perid_test.sv"
  `include "l2_axi_m_aligned_addr_test.sv"
  `include "l2_axi_m_blking_alt_wrrd_test.sv"
  `include "l2_axi_m_blking_wrrd_test.sv"
  `include "l2_axi_m_write_data_bfr_addr_test.sv"
  `include "l2_axi_brstsz_equalto_dataw_test.sv"
  `include "l2_axi_more_prob_wstrb_test.sv"
  `include "l2_axi_brst_aligned_addr_narrow_transf_test.sv"
  `include "l2_axi_brst_wrdata_bfr_addr_test.sv"
  `include "l2_axi_brst_wrrd_with_zero_delay_test.sv"
  `include "l2_axi_brst_wr_with_strb_deassrtd_test.sv"
  `include "l2_axi_ordr_wr_ovrlap_addr_same_id_test.sv"
  `include "l2_axi_ordr_wr_same_id_test.sv"
  `include "l2_basic_test.sv"
  `include "l2_all_bank_all_ram_addr_check_test.sv"
  `include "l2_addr_out_of_range_check_test.sv"
  `include "l2_parallel_wr_rd_check.sv"
  `include "l2_random_delay_wr_rd_test.sv"
  `include "l2_parallel_single_wr_rd_test.sv"
  `include "l2_sm_test.sv"
  `include "l2_axi_wrap_txn_test.sv"
  `include "l2_axi_max_len_txn_test.sv"
  `include "l2_axi_back_2_back_txn.sv"
  `include "l2_stress_check_test.sv"
  `include "l2_cons_bank_test.sv"
  `include "l2_all_burst_len_test.sv"
  `include "l2_unaligned_transfer_test.sv"
  `include "l2_narrow_transfer_test.sv"

`endif
endpackage:l2_uvm_pkg
`endif
