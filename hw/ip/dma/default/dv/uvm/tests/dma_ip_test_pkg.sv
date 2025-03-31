package dma_ip_test_pkg;

  timeunit 1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif


  import dma_pkg::*;

  import dma_ip_common_pkg::*;
  import dma_ip_ral_pkg::*;
  import dma_ip_seq_pkg::*;
  import dma_ip_env_pkg::*;


  // Base Files
  `include "cust_svt_axi_master_transaction.sv"
  `include "dma_ip_base_test.sv"
  `include "dma_ip_rand_transfers_test.sv"
  

  // RTL Designer ScratchPad Area
  `include "dma_ip_designer_scratchpad_test.svh"


  // Register Tests
  `include "dma_ip_basic_reg_test.sv"
  `include "dma_ip_csr_reg_access_test.sv"

  // 1D Tests : Extending and Over-Constraining "dma_ip_rand_transfers_test"
//  `include "dma_ip_1D_simple_test.svh"
//  `include "dma_ip_1D_basic_test.svh"

  `include "dma_ip_1D_ch0_align_align_xinc1_tsize0_64b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_align_xinc1_tsize0_4098b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_align_xinc1_tsize0_4096b_cross_cont_test.svh"
  `include "dma_ip_1D_ch0_align_align_xinc1_tsize0_4096b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_align_xinc1_tsize0_3b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_align_xinc1_tsize0_2b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_align_xinc1_tsize0_1b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_align_xinc1_tsize0_128b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_align_xinc2_tsize6_128b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_align_xinc1_tsize0_65b_cont_test.svh"

  `include "dma_ip_1D_ch0_align_unalign_xinc32_tsize1_8b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_unalign_xinc1_3b_cont_test.svh"
  `include "dma_ip_1D_ch0_align_unalign_xinc2_tsize6_133b_cont_test.svh"
  `include "dma_ip_1D_ch0_unalign_align_xinc2_tsize6_133b_cont_test.svh"
  `include "dma_ip_1D_ch0_unalign_unalign_xinc1_320b_cont_test.svh"

  `include "dma_ip_1D_ch0_no_transfer_dst_xbytesize_0_test.svh"
  `include "dma_ip_1D_ch0_no_transfer_xtype_disable_test.svh"
  `include "dma_ip_1D_ch0_no_transfer_src_xbytesize_0_test.svh"

  // Example how to use RAL Methods to access registers
  `include "dma_ip_ral_usage_examples_test.svh"

  // DMA MODEL - Files based Tests
  `include "dma_ip_model_files_based_tests.svh"
  `include "dma_ip_model_files_based_tests_cmdblk.svh"

  `include "dma_ip_gen_non_atex_dma_model_cases.svh"


  // ---------------------------------------------------------------------------------
  // Special Testbench Setup (AXI Master Agent Connected Directly to AXI SLAVE Agent)
  // To examine and pipeclean AXI Master and AXI Slave VIP operation indendent of DUT

  `include "axi_mstr_2_slv_connection_test.svh"
  // ---------------------------------------------------------------------------------


endpackage : dma_ip_test_pkg
