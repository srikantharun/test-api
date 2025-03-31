// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>

// Tssks for the soc management_testbench
//


//=============================================================================-
`include "reg_tasks.svh"
`include "tb_reset_tasks.svh"
`include "tb_clock_tasks.svh"
`include "rtc_tasks.svh"
`include "wtd_tasks.svh"
`include "tms_tasks.svh"
`include "otp_tasks.svh"
`include "kse_tasks.svh"
`include "tb_pctl_tasks.svh"

//=============================================================================-
task init_inputs();
  i_lt_axi_m_awready      = '0;
  i_lt_axi_m_wready       = '0;
  i_lt_axi_m_bvalid       = '0;
  i_lt_axi_m_bid          = '0;
  i_lt_axi_m_bresp        = '0;
  i_lt_axi_m_buser        = '0;
  i_lt_axi_m_arready      = '0;
  i_lt_axi_m_rvalid       = '0;
  i_lt_axi_m_rlast        = '0;
  i_lt_axi_m_rid          = '0;
  i_lt_axi_m_rdata        = '0;
  i_lt_axi_m_rresp        = '0;
  i_lt_axi_m_ruser        = '0;
  i_lt_axi_s_awvalid      = '0;
  i_lt_axi_s_awaddr       = '0;
  i_lt_axi_s_awid         = '0;
  i_lt_axi_s_awlen        = '0;
  i_lt_axi_s_awsize       = '0;
  i_lt_axi_s_awburst      = '0;
  i_lt_axi_s_awcache      = '0;
  i_lt_axi_s_awprot       = '0;
  i_lt_axi_s_awlock       = '0;
  i_lt_axi_s_awqos        = '0;
  i_lt_axi_s_awregion     = '0;
  i_lt_axi_s_awuser       = '0;
  i_lt_axi_s_wvalid       = '0;
  i_lt_axi_s_wlast        = '0;
  i_lt_axi_s_wstrb        = '0;
  i_lt_axi_s_wdata        = '0;
  i_lt_axi_s_wuser        = '0;
  i_lt_axi_s_bready       = '0;
  i_lt_axi_s_arvalid      = '0;
  i_lt_axi_s_araddr       = '0;
  i_lt_axi_s_arid         = '0;
  i_lt_axi_s_arlen        = '0;
  i_lt_axi_s_arsize       = '0;
  i_lt_axi_s_arburst      = '0;
  i_lt_axi_s_arcache      = '0;
  i_lt_axi_s_arprot       = '0;
  i_lt_axi_s_arqos        = '0;
  i_lt_axi_s_arregion     = '0;
  i_lt_axi_s_aruser       = '0;
  i_lt_axi_s_arlock       = '0;
  i_lt_axi_s_rready       = '0;
  tms                     = '0;
  tdi                     = '0;
  test_mode               = '0;
  i_dft_spare             = '0;
  ssn_bus_data_in         = '0;
  i_auto_repair_done      = '1;
  i_dft_otp_test_mode     = '0;
  i_dft_otp_tst_a         = '0;
  i_dft_otp_tst_din       = '0;
  i_dft_otp_tst_readen    = '0;
  i_dft_otp_tst_ceb       = '0;
  i_dft_otp_tst_cle       = '0;
  i_dft_otp_tst_dle       = '0;
  i_dft_otp_tst_web       = '0;
  i_dft_otp_tst_rstb      = '0;
  i_dft_otp_tst_cpumpen   = '0;
  i_dft_otp_tst_pgmen     = '0;
  i_dft_otp_tst_seltm     = '0;
  i_obs_bus               = '0;
  i_thermal_throttle      = '0;
  i_syscfg_apb4_s_paddr   = '0;
  i_syscfg_apb4_s_pwdata  = '0;
  i_syscfg_apb4_s_pwrite  = '0;
  i_syscfg_apb4_s_psel    = '0;
  i_syscfg_apb4_s_penable = '0;
  i_syscfg_apb4_s_pstrb   = '0;
  i_syscfg_apb4_s_pprot   = '0;
  i_hart_unavail          = '0;
  i_hart_under_reset      = '0;
  bisr_clk                = '0;
  bisr_reset              = '0;
  bisr_si                 = '0;
  bisr_shift_en           = '0;
endtask
