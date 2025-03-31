// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>


// block testbench for the soc management__
//
module soc_mgmt_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // import package for type declarations
  import soc_mgmt_pkg::*;
  import rot_pkg     ::*;
  import chip_pkg    ::*;

  // testbench packages
  import axi_pkg     ::*;

  //============================================================================
  // Set to 1.2 GHz
  localparam realtime TbCycleTime = 0.8333ns;

  // Setup AT timing
  localparam realtime TbApplTime = 0.1 * TbCycleTime;
  localparam realtime TbTestTime = 0.9 * TbCycleTime;

  localparam int NB_CLK   = 2;
  localparam int NB_RESET = 2;

  localparam real CLK_FREQ[NB_CLK] = '{
    50.0e6, // REF clock
   100.0e6  // TCK
  };

  localparam type gen_clk_t = logic [NB_CLK  -1:0];
  localparam type gen_rst_t = logic [NB_RESET-1:0];

  // Clock / Reset genereration and stop of simulation
  // clocks
  gen_clk_t                            gen_clk                    ;
  wire                                 i_ref_clk                  ;
  wire                                 o_fast_clk                 ;
  wire                                 o_apu_clk                  ;
  wire                                 o_ddr_ref_east_clk         ;

  // resets
  gen_rst_t                            gen_rst                    ;
  gen_rst_t                            drv_rst                    ;
  wire                                 i_por_rst_n                ;
  logic                                i_dmi_rst_n                ;
  wire                                 o_ao_rst_n                 ;
  wire                                 o_global_rst_n             ;

  wire                                 o_codec_clk                ;
  wire                                 o_emmc_clk                 ;
  wire                                 o_periph_clk               ;
  wire                                 o_noc_clk                  ;
  wire                                 o_noc_rst_n                ;

  // dlm
  soc_mgmt_pkg::aic_thrtl_t            o_aic_throttle             ;
  soc_mgmt_pkg::dlm_clk_thrtl_t        o_clock_throttle           ;
  soc_mgmt_pkg::aic_boost_t            i_aic_boost_req            ;
  soc_mgmt_pkg::aic_boost_t            o_aic_boost_ack            ;
  logic                                i_throttle                 ;
  soc_mgmt_pkg::dlm_int_t              o_irq                      ;
  logic                                o_dlm_irq_warning          ;
  logic                                o_dlm_irq_critical         ;

  chip_pkg::chip_axi_addr_t            o_lt_axi_m_awaddr          ;
  soc_mgmt_lt_axi_m_id_t               o_lt_axi_m_awid            ;
  axi_pkg::axi_len_t                   o_lt_axi_m_awlen           ;
  axi_pkg::axi_size_t                  o_lt_axi_m_awsize          ;
  axi_pkg::axi_burst_t                 o_lt_axi_m_awburst         ;
  axi_pkg::axi_cache_t                 o_lt_axi_m_awcache         ;
  axi_pkg::axi_prot_t                  o_lt_axi_m_awprot          ;
  logic                                o_lt_axi_m_awlock          ;
  axi_pkg::axi_qos_t                   o_lt_axi_m_awqos           ;
  axi_pkg::axi_region_t                o_lt_axi_m_awregion        ;
  chip_pkg::chip_axi_lt_awuser_t       o_lt_axi_m_awuser          ;
  logic                                o_lt_axi_m_awvalid         ;
  logic                                i_lt_axi_m_awready         ;
  //write data channel;
  logic                                o_lt_axi_m_wvalid          ;
  logic                                o_lt_axi_m_wlast           ;
  chip_pkg::chip_axi_lt_wstrb_t        o_lt_axi_m_wstrb           ;
  chip_pkg::chip_axi_lt_data_t         o_lt_axi_m_wdata           ;
  chip_pkg::chip_axi_ht_wuser_t        o_lt_axi_m_wuser           ;
  logic                                i_lt_axi_m_wready          ;
  //write response channel;
  logic                                i_lt_axi_m_bvalid          ;
  soc_mgmt_lt_axi_m_id_t               i_lt_axi_m_bid             ;
  axi_pkg::axi_resp_t                  i_lt_axi_m_bresp           ;
  chip_pkg::chip_axi_lt_buser_t        i_lt_axi_m_buser           ;
  logic                                o_lt_axi_m_bready          ;
  //read address channel;
  logic                                o_lt_axi_m_arvalid         ;
  chip_pkg::chip_axi_addr_t            o_lt_axi_m_araddr          ;
  soc_mgmt_lt_axi_m_id_t               o_lt_axi_m_arid            ;
  axi_pkg::axi_len_t                   o_lt_axi_m_arlen           ;
  axi_pkg::axi_size_t                  o_lt_axi_m_arsize          ;
  axi_pkg::axi_burst_t                 o_lt_axi_m_arburst         ;
  axi_pkg::axi_cache_t                 o_lt_axi_m_arcache         ;
  axi_pkg::axi_prot_t                  o_lt_axi_m_arprot          ;
  axi_pkg::axi_qos_t                   o_lt_axi_m_arqos           ;
  axi_pkg::axi_region_t                o_lt_axi_m_arregion        ;
  chip_pkg::chip_axi_lt_aruser_t       o_lt_axi_m_aruser          ;
  logic                                o_lt_axi_m_arlock          ;
  logic                                i_lt_axi_m_arready         ;
  //read data/response channel;
  logic                                i_lt_axi_m_rvalid          ;
  logic                                i_lt_axi_m_rlast           ;
  soc_mgmt_lt_axi_m_id_t               i_lt_axi_m_rid             ;
  chip_pkg::chip_axi_lt_data_t         i_lt_axi_m_rdata           ;
  axi_pkg::axi_resp_t                  i_lt_axi_m_rresp           ;
  chip_pkg::chip_axi_lt_ruser_t        i_lt_axi_m_ruser           ;
  logic                                o_lt_axi_m_rready          ;

  // Connections LP AXI Subordinate Interface;
  logic                                i_lt_axi_s_awvalid         ;
  chip_pkg::chip_axi_addr_t            i_lt_axi_s_awaddr          ;
  soc_mgmt_lt_axi_s_id_t               i_lt_axi_s_awid            ;
  axi_pkg::axi_len_t                   i_lt_axi_s_awlen           ;
  axi_pkg::axi_size_t                  i_lt_axi_s_awsize          ;
  axi_pkg::axi_burst_t                 i_lt_axi_s_awburst         ;
  axi_pkg::axi_cache_t                 i_lt_axi_s_awcache         ;
  axi_pkg::axi_prot_t                  i_lt_axi_s_awprot          ;
  logic                                i_lt_axi_s_awlock          ;
  axi_pkg::axi_qos_t                   i_lt_axi_s_awqos           ;
  axi_pkg::axi_region_t                i_lt_axi_s_awregion        ;
  chip_pkg::chip_axi_lt_awuser_t       i_lt_axi_s_awuser          ;
  logic                                o_lt_axi_s_awready         ;
  logic                                i_lt_axi_s_wvalid          ;
  logic                                i_lt_axi_s_wlast           ;
  chip_pkg::chip_axi_lt_wstrb_t        i_lt_axi_s_wstrb           ;
  chip_pkg::chip_axi_lt_data_t         i_lt_axi_s_wdata           ;
  chip_pkg::chip_axi_lt_wuser_t        i_lt_axi_s_wuser           ;
  logic                                o_lt_axi_s_wready          ;
  logic                                o_lt_axi_s_bvalid          ;
  soc_mgmt_lt_axi_s_id_t               o_lt_axi_s_bid             ;
  axi_pkg::axi_resp_t                  o_lt_axi_s_bresp           ;
  chip_pkg::chip_axi_lt_buser_t        o_lt_axi_s_buser           ;
  logic                                i_lt_axi_s_bready          ;
  logic                                i_lt_axi_s_arvalid         ;
  chip_pkg::chip_axi_addr_t            i_lt_axi_s_araddr          ;
  soc_mgmt_lt_axi_s_id_t               i_lt_axi_s_arid            ;
  axi_pkg::axi_len_t                   i_lt_axi_s_arlen           ;
  axi_pkg::axi_size_t                  i_lt_axi_s_arsize          ;
  axi_pkg::axi_burst_t                 i_lt_axi_s_arburst         ;
  axi_pkg::axi_cache_t                 i_lt_axi_s_arcache         ;
  axi_pkg::axi_prot_t                  i_lt_axi_s_arprot          ;
  axi_pkg::axi_qos_t                   i_lt_axi_s_arqos           ;
  axi_pkg::axi_region_t                i_lt_axi_s_arregion        ;
  chip_pkg::chip_axi_lt_aruser_t       i_lt_axi_s_aruser          ;
  logic                                i_lt_axi_s_arlock          ;
  logic                                o_lt_axi_s_arready         ;
  logic                                o_lt_axi_s_rvalid          ;
  logic                                o_lt_axi_s_rlast           ;
  soc_mgmt_lt_axi_s_id_t               o_lt_axi_s_rid             ;
  chip_pkg::chip_axi_lt_data_t         o_lt_axi_s_rdata           ;
  axi_pkg::axi_resp_t                  o_lt_axi_s_rresp           ;
  chip_pkg::chip_axi_lt_ruser_t        o_lt_axi_s_ruser           ;
  logic                                i_lt_axi_s_rready          ;

  logic [31:0]                         i_syscfg_apb4_s_paddr      ;
  chip_apb_syscfg_data_t               i_syscfg_apb4_s_pwdata     ;
  logic                                i_syscfg_apb4_s_pwrite     ;
  logic                                i_syscfg_apb4_s_psel       ;
  logic                                i_syscfg_apb4_s_penable    ;
  chip_apb_syscfg_strb_t               i_syscfg_apb4_s_pstrb      ;
  logic          [3-1:0]               i_syscfg_apb4_s_pprot      ;
  logic                                o_syscfg_apb4_s_pready     ;
  chip_apb_syscfg_data_t               o_syscfg_apb4_s_prdata     ;
  logic                                o_syscfg_apb4_s_pslverr    ;

  logic [15:0]                         o_mbist_apb_m_paddr        ;
  logic [31:0]                         o_mbist_apb_m_pwdata       ;
  logic                                o_mbist_apb_m_pwrite       ;
  logic                                o_mbist_apb_m_psel         ;
  logic                                o_mbist_apb_m_penable      ;
  logic                                i_mbist_apb_m_pready       ;
  logic [31:0]                         i_mbist_apb_m_prdata       ;
  logic                                i_mbist_apb_m_pslverr      ;

  // thermal throttle override
  logic                                i_thermal_throttle         ;
  // thermal throttle output to AI cores
  soc_mgmt_pkg::tms_temp_t             o_thermal_throttle         ;
  // thrermnal warning. From thermal throttle. Overheating warning to boardsystem
  logic                                o_thermal_throttle_warning_n;
  // thermal warning. To partition AI cores
  soc_mgmt_pkg::tms_temp_t             o_thermal_warning          ;
  // thermal shutdown. Will reset the chip via pcb controller
  logic                                o_thermal_shutdown_n       ;
  // tms interrupt
  logic                                o_irq_tms_throttle         ;
  logic                                o_irq_tms_warning          ;
  logic                                o_irq_tms_shutdown         ;
  /// Interrupts
  // RTC interrupt
  logic                                o_rtc_irq                  ;
  // Watchdog interrupt
  logic                                o_wdt_irq                  ;
  // Security interrupt
  logic                                o_security_irq             ;

  logic                                test_mode                  ;
  logic [24:0]                         i_dft_spare                ;
  logic [24:0]                         o_dft_spare                ;

  wire                                 ssn_bus_clk                ;
  logic [23:0]                         ssn_bus_data_in            ;
  logic [23:0]                         ssn_bus_data_out           ;

  logic                                bisr_clk                   ;
  logic                                bisr_reset                 ;
  logic                                bisr_shift_en              ;
  logic                                bisr_si                    ;
  logic                                bisr_so                    ;

  wire                                 tck                        ;
  wire                                 trst                       ;
  logic                                tms                        ;
  logic                                tdi                        ;
  logic                                tdo_en                     ;
  logic                                tdo                        ;

  /// DFT reset override signals;
  logic                                i_auto_repair_done         ;

  // Trace debug interface
  dbg_hart_t                           o_debugint                 ;
  dbg_hart_t                           o_resethaltreq             ;
  dbg_hart_t                           i_hart_unavail             ;
  dbg_hart_t                           i_hart_under_reset         ;

  /// Placeholder for DFT Signals - OTP Wrapper;
  logic                                i_dft_otp_test_mode        ;
  otp_wrapper_pkg::otp_addr_t          i_dft_otp_tst_a            ;
  logic                                i_dft_otp_tst_din          ;
  logic                                i_dft_otp_tst_readen       ;
  logic                                i_dft_otp_tst_ceb          ;
  logic                                i_dft_otp_tst_cle          ;
  logic                                i_dft_otp_tst_dle          ;
  logic                                i_dft_otp_tst_web          ;
  logic                                i_dft_otp_tst_rstb         ;
  logic                                i_dft_otp_tst_cpumpen      ;
  logic                                i_dft_otp_tst_pgmen        ;
  logic                                i_dft_otp_tst_seltm        ;
  logic                                i_dft_otp_tst_vddrdy       ;
  logic                                i_dft_otp_tst_clken        ;
  otp_wrapper_pkg::otp_data_t          o_dft_otp_tst_d            ;
  otp_wrapper_pkg::otp_lock_t          o_dft_otp_tst_lock         ;
  logic                                o_dft_enable               ;
  logic                                o_dft_reenable             ;
  logic                                o_dft_sts_done             ;

  /// Observability signal interface.;
  logic [OBS_IP_BUS_W-1:0]             i_obs_bus                  ;
  logic [OBS_OP_BUS_W-1:0]             o_obs_bus                  ;

  logic                                o_global_sync              ;

  /// OTP Analog signals to IO PAD;
  wire                                 io_otp_vtdo                ;
  wire                                 io_otp_vrefm               ;
  wire                                 io_otp_vpp                 ;

  /// PVT Sensor Analog signals to Remote Probe (to be manually routed).;
  wire  [62:0]                         io_pvt_ibias_ts            ;
  wire  [62:0]                         io_pvt_vsense_ts           ;
  wire                                 io_pvt_test_out_ts         ;
  // Efuse interface analog signals.;
  wire                                 io_efuse_vqps              ;
  wire                                 io_efuse_vddwl             ;

`ifdef POWER_PINS
  wire                                  io_pvt_dvdd075a_ts        ;
  wire                                  io_pvt_dvss0a_ts          ;
  wire                                  io_pvt_avdd18a_ts         ;
  wire                                  io_pvt_avss0a_ts          ;
  wire                                  io_pvt_avss_gd            ;
  wire                                  io_pll_avdd18             ;
  wire                                  io_pll_avss               ;
  wire                                  io_pll_dvdd075            ;
  wire                                  io_pll_dvss               ;
`endif

  int                                  fail_cnt                   ;
  soc_mgmt_clk_checker_pkg::pll_t      pll_meas_fail              ;
  soc_mgmt_clk_checker_pkg::div_fail_t div_meas_fail              ;


  chip_pkg::chip_axi_addr_t            reg_addr                   ;
  chip_pkg::chip_axi_lt_data_t         reg_read_data              ;
  axi_pkg::axi_resp_t                  reg_resp                   ;

  bit                                  syscfg_slverr              ;

  event                                ev_debug0                  ;
  event                                ev_debug1                  ;
  event                                ev_debug2                  ;

  int unsigned                         test_step                  ;
  bit                                  use_kse3_integr_rom        ;

  //============================================================================
  `include "tb_tasks.svh"

  `include "soc_mgmt_tests.svh"

  //============================================================================

  localparam int unsigned ResetCycles = 5;

  initial begin : proc_clk_rst_gen
    bit [32:0] resval;
    string integ_rom, sec_rom, rom;

    drv_rst  =   '0;
    use_kse3_integr_rom = 1'b0;

    init_inputs();

    // Load KSE3 ROM with integration code
    integ_rom = "$KUDELSKI_KSE3_HOME/rom/kse3_rom_integration.hex";
    sec_rom   = "$KUDELSKI_KSE3_HOME/../20241220_KSE3_ROM_2.8.0/rom/KSE3_2.8.0_ROM.hex";

    if (use_kse3_integr_rom) rom = integ_rom;
    else rom = sec_rom;

    $readmemh(rom, i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kudelski_kse3_rom.memory_q);

    @(posedge i_por_rst_n);
    #(1us);

    fast_clk_setup();
    #10us;

    // tests
    //reset_gen_test();
    //clock_test();
    //memory_map_test();
    //rtc_test();
    //wtd_test();
    //tms_test();
    otp_test();
    // kse_test();
    //pctl_test();
    //debugger_test();

    test_report(fail_cnt + |pll_meas_fail + |div_meas_fail);
  end

  // Design Under Test (DUT)
  soc_mgmt_p #(

  ) i_soc_mgmt_p_dut (
    .i_ref_clk                    ( i_ref_clk                                       ),
    .i_por_rst_n                  ( i_por_rst_n                                     ),
    .o_ao_rst_n                   ( o_ao_rst_n                                      ),
    .o_global_rst_n               ( o_global_rst_n                                  ),
    .o_fast_clk                   ( o_fast_clk                                      ),
    .o_apu_clk                    ( o_apu_clk                                       ),
    .o_ddr_ref_east_clk           ( o_ddr_ref_east_clk                              ),
    .o_codec_clk                  ( o_codec_clk                                     ),
    .o_emmc_clk                   ( o_emmc_clk                                      ),
    .o_periph_clk                 ( o_periph_clk                                    ),
    .o_noc_clk                    ( o_noc_clk                                       ),
    .o_noc_rst_n                  ( o_noc_rst_n                                     ),
    .o_aic_throttle               ( o_aic_throttle                                  ),
    .o_clock_throttle             ( o_clock_throttle                                ),
    .i_aic_boost_req              ( i_aic_boost_req                                 ),
    .o_aic_boost_ack              ( o_aic_boost_ack                                 ),
    .i_throttle                   ( i_throttle                                      ),
    .o_dlm_irq_warning            ( o_dlm_irq_warning                               ),
    .o_dlm_irq_critical           ( o_dlm_irq_critical                              ),
    .o_lt_axi_m_awaddr            ( o_lt_axi_m_awaddr                               ),
    .o_lt_axi_m_awid              ( o_lt_axi_m_awid                                 ),
    .o_lt_axi_m_awlen             ( o_lt_axi_m_awlen                                ),
    .o_lt_axi_m_awsize            ( o_lt_axi_m_awsize                               ),
    .o_lt_axi_m_awburst           ( o_lt_axi_m_awburst                              ),
    .o_lt_axi_m_awcache           ( o_lt_axi_m_awcache                              ),
    .o_lt_axi_m_awprot            ( o_lt_axi_m_awprot                               ),
    .o_lt_axi_m_awlock            ( o_lt_axi_m_awlock                               ),
    .o_lt_axi_m_awqos             ( o_lt_axi_m_awqos                                ),
    .o_lt_axi_m_awregion          ( o_lt_axi_m_awregion                             ),
    .o_lt_axi_m_awuser            ( o_lt_axi_m_awuser                               ),
    .o_lt_axi_m_awvalid           ( o_lt_axi_m_awvalid                              ),
    .i_lt_axi_m_awready           ( i_lt_axi_m_awready                              ),
    .o_lt_axi_m_wvalid            ( o_lt_axi_m_wvalid                               ),
    .o_lt_axi_m_wlast             ( o_lt_axi_m_wlast                                ),
    .o_lt_axi_m_wstrb             ( o_lt_axi_m_wstrb                                ),
    .o_lt_axi_m_wdata             ( o_lt_axi_m_wdata                                ),
    .o_lt_axi_m_wuser             ( o_lt_axi_m_wuser                                ),
    .i_lt_axi_m_wready            ( i_lt_axi_m_wready                               ),
    .i_lt_axi_m_bvalid            ( i_lt_axi_m_bvalid                               ),
    .i_lt_axi_m_bid               ( i_lt_axi_m_bid                                  ),
    .i_lt_axi_m_bresp             ( i_lt_axi_m_bresp                                ),
    .i_lt_axi_m_buser             ( i_lt_axi_m_buser                                ),
    .o_lt_axi_m_bready            ( o_lt_axi_m_bready                               ),
    .o_lt_axi_m_arvalid           ( o_lt_axi_m_arvalid                              ),
    .o_lt_axi_m_araddr            ( o_lt_axi_m_araddr                               ),
    .o_lt_axi_m_arid              ( o_lt_axi_m_arid                                 ),
    .o_lt_axi_m_arlen             ( o_lt_axi_m_arlen                                ),
    .o_lt_axi_m_arsize            ( o_lt_axi_m_arsize                               ),
    .o_lt_axi_m_arburst           ( o_lt_axi_m_arburst                              ),
    .o_lt_axi_m_arcache           ( o_lt_axi_m_arcache                              ),
    .o_lt_axi_m_arprot            ( o_lt_axi_m_arprot                               ),
    .o_lt_axi_m_arqos             ( o_lt_axi_m_arqos                                ),
    .o_lt_axi_m_arregion          ( o_lt_axi_m_arregion                             ),
    .o_lt_axi_m_aruser            ( o_lt_axi_m_aruser                               ),
    .o_lt_axi_m_arlock            ( o_lt_axi_m_arlock                               ),
    .i_lt_axi_m_arready           ( i_lt_axi_m_arready                              ),
    .i_lt_axi_m_rvalid            ( i_lt_axi_m_rvalid                               ),
    .i_lt_axi_m_rlast             ( i_lt_axi_m_rlast                                ),
    .i_lt_axi_m_rid               ( i_lt_axi_m_rid                                  ),
    .i_lt_axi_m_rdata             ( i_lt_axi_m_rdata                                ),
    .i_lt_axi_m_rresp             ( i_lt_axi_m_rresp                                ),
    .i_lt_axi_m_ruser             ( i_lt_axi_m_ruser                                ),
    .o_lt_axi_m_rready            ( o_lt_axi_m_rready                               ),
    .i_lt_axi_s_awvalid           ( i_lt_axi_s_awvalid                              ),
    .i_lt_axi_s_awaddr            ( i_lt_axi_s_awaddr                               ),
    .i_lt_axi_s_awid              ( i_lt_axi_s_awid                                 ),
    .i_lt_axi_s_awlen             ( i_lt_axi_s_awlen                                ),
    .i_lt_axi_s_awsize            ( i_lt_axi_s_awsize                               ),
    .i_lt_axi_s_awburst           ( i_lt_axi_s_awburst                              ),
    .i_lt_axi_s_awcache           ( i_lt_axi_s_awcache                              ),
    .i_lt_axi_s_awprot            ( i_lt_axi_s_awprot                               ),
    .i_lt_axi_s_awlock            ( i_lt_axi_s_awlock                               ),
    .i_lt_axi_s_awqos             ( i_lt_axi_s_awqos                                ),
    .i_lt_axi_s_awregion          ( i_lt_axi_s_awregion                             ),
    .i_lt_axi_s_awuser            ( i_lt_axi_s_awuser                               ),
    .o_lt_axi_s_awready           ( o_lt_axi_s_awready                              ),
    .i_lt_axi_s_wvalid            ( i_lt_axi_s_wvalid                               ),
    .i_lt_axi_s_wlast             ( i_lt_axi_s_wlast                                ),
    .i_lt_axi_s_wstrb             ( i_lt_axi_s_wstrb                                ),
    .i_lt_axi_s_wdata             ( i_lt_axi_s_wdata                                ),
    .i_lt_axi_s_wuser             ( i_lt_axi_s_wuser                                ),
    .o_lt_axi_s_wready            ( o_lt_axi_s_wready                               ),
    .o_lt_axi_s_bvalid            ( o_lt_axi_s_bvalid                               ),
    .o_lt_axi_s_bid               ( o_lt_axi_s_bid                                  ),
    .o_lt_axi_s_bresp             ( o_lt_axi_s_bresp                                ),
    .o_lt_axi_s_buser             ( o_lt_axi_s_buser                                ),
    .i_lt_axi_s_bready            ( i_lt_axi_s_bready                               ),
    .i_lt_axi_s_arvalid           ( i_lt_axi_s_arvalid                              ),
    .i_lt_axi_s_araddr            ( i_lt_axi_s_araddr                               ),
    .i_lt_axi_s_arid              ( i_lt_axi_s_arid                                 ),
    .i_lt_axi_s_arlen             ( i_lt_axi_s_arlen                                ),
    .i_lt_axi_s_arsize            ( i_lt_axi_s_arsize                               ),
    .i_lt_axi_s_arburst           ( i_lt_axi_s_arburst                              ),
    .i_lt_axi_s_arcache           ( i_lt_axi_s_arcache                              ),
    .i_lt_axi_s_arprot            ( i_lt_axi_s_arprot                               ),
    .i_lt_axi_s_arqos             ( i_lt_axi_s_arqos                                ),
    .i_lt_axi_s_arregion          ( i_lt_axi_s_arregion                             ),
    .i_lt_axi_s_aruser            ( i_lt_axi_s_aruser                               ),
    .i_lt_axi_s_arlock            ( i_lt_axi_s_arlock                               ),
    .o_lt_axi_s_arready           ( o_lt_axi_s_arready                              ),
    .o_lt_axi_s_rvalid            ( o_lt_axi_s_rvalid                               ),
    .o_lt_axi_s_rlast             ( o_lt_axi_s_rlast                                ),
    .o_lt_axi_s_rid               ( o_lt_axi_s_rid                                  ),
    .o_lt_axi_s_rdata             ( o_lt_axi_s_rdata                                ),
    .o_lt_axi_s_rresp             ( o_lt_axi_s_rresp                                ),
    .o_lt_axi_s_ruser             ( o_lt_axi_s_ruser                                ),
    .i_lt_axi_s_rready            ( i_lt_axi_s_rready                               ),
    .i_syscfg_apb4_s_paddr        ( i_syscfg_apb4_s_paddr[CHIP_SOC_MGMT_SYSCFG-1:0] ),
    .i_syscfg_apb4_s_pwdata       ( i_syscfg_apb4_s_pwdata                          ),
    .i_syscfg_apb4_s_pwrite       ( i_syscfg_apb4_s_pwrite                          ),
    .i_syscfg_apb4_s_psel         ( i_syscfg_apb4_s_psel                            ),
    .i_syscfg_apb4_s_penable      ( i_syscfg_apb4_s_penable                         ),
    .i_syscfg_apb4_s_pstrb        ( i_syscfg_apb4_s_pstrb                           ),
    .i_syscfg_apb4_s_pprot        ( i_syscfg_apb4_s_pprot                           ),
    .o_syscfg_apb4_s_pready       ( o_syscfg_apb4_s_pready                          ),
    .o_syscfg_apb4_s_prdata       ( o_syscfg_apb4_s_prdata                          ),
    .o_syscfg_apb4_s_pslverr      ( o_syscfg_apb4_s_pslverr                         ),
    .o_mbist_apb_m_paddr          ( o_mbist_apb_m_paddr                             ),
    .o_mbist_apb_m_pwdata         ( o_mbist_apb_m_pwdata                            ),
    .o_mbist_apb_m_pwrite         ( o_mbist_apb_m_pwrite                            ),
    .o_mbist_apb_m_psel           ( o_mbist_apb_m_psel                              ),
    .o_mbist_apb_m_penable        ( o_mbist_apb_m_penable                           ),
    .i_mbist_apb_m_pready         ( i_mbist_apb_m_pready                            ),
    .i_mbist_apb_m_prdata         ( i_mbist_apb_m_prdata                            ),
    .i_mbist_apb_m_pslverr        ( i_mbist_apb_m_pslverr                           ),
    .i_thermal_throttle           ( i_thermal_throttle                              ),
    .o_thermal_throttle           ( o_thermal_throttle                              ),
    .o_thermal_throttle_warning_n ( o_thermal_throttle_warning_n                    ),
    .o_thermal_warning            ( o_thermal_warning                               ),
    .o_thermal_shutdown_n         ( o_thermal_shutdown_n                            ),
    .o_irq_tms_throttle           ( o_irq_tms_throttle                              ),
    .o_irq_tms_warning            ( o_irq_tms_warning                               ),
    .o_irq_tms_shutdown           ( o_irq_tms_shutdown                              ),
    .o_rtc_irq                    ( o_rtc_irq                                       ),
    .o_wdt_irq                    ( o_wdt_irq                                       ),
    .o_security_irq               ( o_security_irq                                  ),
    .test_mode                    ( test_mode                                       ),
    .i_dft_spare                  ( i_dft_spare                                     ),
    .o_dft_spare                  ( o_dft_spare                                     ),
    .ssn_bus_clk                  ( ssn_bus_clk                                     ),
    .ssn_bus_data_in              ( ssn_bus_data_in                                 ),
    .ssn_bus_data_out             ( ssn_bus_data_out                                ),
    .bisr_clk                     ( bisr_clk                                        ),
    .bisr_reset                   ( bisr_reset                                      ),
    .bisr_shift_en                ( bisr_shift_en                                   ),
    .bisr_si                      ( bisr_si                                         ),
    .bisr_so                      ( bisr_so                                         ),
    .tck                          ( tck                                             ),
    .trst                         ( trst                                            ),
    .tms                          ( tms                                             ),
    .tdi                          ( tdi                                             ),
    .tdo_en                       ( tdo_en                                          ),
    .tdo                          ( tdo                                             ),
    .i_auto_repair_done           ( i_auto_repair_done                              ),
    .o_debugint                   ( o_debugint                                      ),
    .o_resethaltreq               ( o_resethaltreq                                  ),
    .i_hart_unavail               ( i_hart_unavail                                  ),
    .i_hart_under_reset           ( i_hart_under_reset                              ),
    .i_dft_otp_test_mode          ( i_dft_otp_test_mode                             ),
    .i_dft_otp_tst_a              ( i_dft_otp_tst_a                                 ),
    .i_dft_otp_tst_din            ( i_dft_otp_tst_din                               ),
    .i_dft_otp_tst_readen         ( i_dft_otp_tst_readen                            ),
    .i_dft_otp_tst_ceb            ( i_dft_otp_tst_ceb                               ),
    .i_dft_otp_tst_cle            ( i_dft_otp_tst_cle                               ),
    .i_dft_otp_tst_dle            ( i_dft_otp_tst_dle                               ),
    .i_dft_otp_tst_web            ( i_dft_otp_tst_web                               ),
    .i_dft_otp_tst_rstb           ( i_dft_otp_tst_rstb                              ),
    .i_dft_otp_tst_cpumpen        ( i_dft_otp_tst_cpumpen                           ),
    .i_dft_otp_tst_pgmen          ( i_dft_otp_tst_pgmen                             ),
    .i_dft_otp_tst_seltm          ( i_dft_otp_tst_seltm                             ),
    .i_dft_otp_tst_vddrdy         ( i_dft_otp_tst_vddrdy                            ),
    .i_dft_otp_tst_clken          ( i_dft_otp_tst_clken                             ),
    .o_dft_otp_tst_d              ( o_dft_otp_tst_d                                 ),
    .o_dft_otp_tst_lock           ( o_dft_otp_tst_lock                              ),
    .i_obs_bus                    ( i_obs_bus                                       ),
    .o_obs_bus                    ( o_obs_bus                                       ),
    .o_global_sync                ( o_global_sync                                   ),
    .io_otp_vtdo                  ( io_otp_vtdo                                     ),
    .io_otp_vrefm                 ( io_otp_vrefm                                    ),
    .io_otp_vpp                   ( io_otp_vpp                                      ),
    .io_pvt_ibias_ts              ( io_pvt_ibias_ts                                 ),
    .io_pvt_vsense_ts             ( io_pvt_vsense_ts                                ),
    .io_pvt_test_out_ts           ( io_pvt_test_out_ts                              ),
    .io_efuse_vqps                ( io_efuse_vqps                                   ),
    .io_efuse_vddwl               ( io_efuse_vddwl                                  )
`ifdef POWER_PINS
                                                                                     ,
    .io_pvt_dvdd075a_ts           ( io_pvt_dvdd075a_ts                              ),
    .io_pvt_dvss0a_ts             ( io_pvt_dvss0a_ts                                ),
    .io_pvt_avdd18a_ts            ( io_pvt_avdd18a_ts                               ),
    .io_pvt_avss0a_ts             ( io_pvt_avss0a_ts                                ),
    .io_pvt_avss_gd               ( io_pvt_avss_gd                                  ),
    .io_pll_avdd18                ( io_pll_avdd18                                   ),
    .io_pll_avss                  ( io_pll_avss                                     ),
    .io_pll_dvdd075               ( io_pll_dvdd075                                  ),
    .io_pll_dvss                  ( io_pll_dvss                                     )
`endif
  );

//==============================================================================
wire pvt_io_avss_ts;
wire pvt_io_avss_gd;

assign pvt_io_avss_ts = 1'h0;
assign pvt_io_avss_gd = 1'h0;

//`define POWER_PINS
// remote probes
//pvt_probe_wrapper #(
//) u_pvt_probe_wrapper (
//  .io_avss_ts   ( pvt_io_avss_ts      ),
//  .io_avss_gd   ( pvt_io_avss_gd      ),
//  .io_ibias_ts  ( io_pvt_ibias_ts [0] ),
//  .io_vsense_ts ( io_pvt_vsense_ts[0] )
//);

//==============================================================================
// Assertion
bind soc_mgmt_reset_gen soc_mgmt_reset_gen_assertions #(
  .STAGE_NUM ( STAGE_NUM )
) u_soc_mgmt_reset_gen_assertions_0 (
  .i_clk                 ( i_clk                                   ),
  .i_por_rst_n           ( i_por_rst_n                             ),
  .ao_stretch_delay      ( reg2hw.rst_cfg_ao_rst    .rst_stretch.q ),
  .dmi_stretch_delay     ( reg2hw.rst_cfg_dmi_rst   .rst_stretch.q ),
  .global_stretch_delay  ( reg2hw.rst_cfg_global_rst.rst_stretch.q ),
  .o_ao_rst_ip_n         ( o_ao_rst_ip_n                           ),
  .o_dmi_rst_ip_n        ( o_dmi_rst_ip_n                          ),
  .o_global_rst_ip_n     ( o_global_rst_ip_n                       ),
  .rst_stage             ( rst_stage                               ),
  .i_test_mode           ( test_mode                               ),
  .i_dft_clk_rst_ctrl    ( i_dft_clk_rst_ctrl                      ),
  .i_test_rst_n          ( 3'h7                                    ),
  .i_dmi_rst_n           ( i_dmi_rst_n                             ),
  .i_rot_rst_n           ( i_rot_rst_n                             ),
  .i_wdt_rst_n           ( i_wdt_rst_n                             ),
  .i_mbist_rst_n         ( 1'h1                                    ),
  .i_debug_rst_n         ( i_debug_rst_n                           ),
  .i_ao_rst_req_n        ( i_ao_rst_req_n                          ),
  .i_ao_rst_ip_ack       ( i_ao_rst_ip_ack                         ),
  .o_dmi_rst_ack_n       ( o_dmi_rst_ack_n                         ),
  .i_dmi_rst_ip_ack      ( i_dmi_rst_ip_ack                        ),
  .i_global_rst_req_n    ( i_global_rst_req_n                      ),
  .i_global_rst_ip_ack   ( i_global_rst_ip_ack                     ),
  .ppmu_fsm_state_q      ( u_noc_pctl.g_ppmu[0].u_ppmu.fsm_state_q ),
  .i_dmi_sw_rst_n        ( reg2hw.rst_sw_dmi_rst                   ),
  .i_global_sw_rst_n     ( reg2hw.rst_sw_global_rst                )
);

//==============================================================================
// clock generator

// connect clock to dut input clocks
assign i_ref_clk            = gen_clk[0];
assign tck                  = gen_clk[1];

for (genvar i=0; i<NB_CLK; i++) begin : gen_tb_clocks
  tb_clkgen #(
    .FREQ(CLK_FREQ[i])
  ) u_tb_clkgen (
    .o_clk( gen_clk[i] )
  );
end

//==============================================================================
// reset generator
assign i_por_rst_n         = gen_rst[0];
assign trst                = gen_rst[1];
initial begin
  i_dmi_rst_n         = 1'h1;////gen_rst[3];
end

for (genvar i=0; i<NB_RESET; i++) begin : gen_tb_resets
  tb_rstgen #(
    .ResetCycles ( 50 /*ResetCycles*/ )
  ) u_tb_rstgen (
    .i_clk       ( i_ref_clk   ),
    .i_drv_rst   ( drv_rst[i]  ),
    .o_rst_n     ( gen_rst[i]  )
  );
end

//============================================================================
// report test status
function void test_report(int fail_cnt);
  static uvm_report_server rs = uvm_report_server::get_server();

  `uvm_info("TEST REPORT", $sformatf("*****************************"), UVM_NONE)
  `uvm_info("TEST REPORT", $sformatf("*** TEST COMPLETE: %0s ****", !fail_cnt ? "PASSED" : "FAILED"), UVM_NONE)
  `uvm_info("TEST REPORT", $sformatf("*****************************"), UVM_NONE)


  `uvm_info("TEST REPORT", $sformatf("UVM_ERROR :    %0d", rs.get_severity_count(UVM_ERROR)), UVM_NONE)
  `uvm_info("TEST REPORT", $sformatf("UVM_FATAL :    %0d", rs.get_severity_count(UVM_FATAL)), UVM_NONE)

  $finish();
endfunction

//==============================================================================`
// clock checkers
// TODO: Fix clock checkers.
/*
soc_mgmt_clk_checker_pkg::pll_t       mon_pll_out_clk;
soc_mgmt_clk_checker_pkg::pll_t       mon_pll_clk    ;
soc_mgmt_clk_checker_pkg::pll_t       mon_pll_lock   ;
soc_mgmt_clk_checker_pkg::pllm_t      mon_pll_m      ;
soc_mgmt_clk_checker_pkg::pllp_t      mon_pll_p      ;
soc_mgmt_clk_checker_pkg::plls_t      mon_pll_s      ;
soc_mgmt_clk_checker_pkg::clk_sel_t   mon_clk_sel    ;

soc_mgmt_clk_checker_pkg::freq_t      meas_pll_freq[soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL]        ;

soc_mgmt_clk_checker_pkg::div_clk_t   meas_div_clk;
soc_mgmt_clk_checker_pkg::div_value_t div_clk_exp = '{
  2 , // codec_clk
  6 , // emmc_clk
  12, // periph clk
  1 , // noc_clk
  12, // slow_clk (100MHz)
  300 // pvt clk d2
};

//==============================================================================
// conenect inter signal to use for pll measurement
always_comb begin
  mon_pll_out_clk = {o_ddr_ref_east_clk, o_apu_clk, o_fast_clk};
  mon_pll_clk     = soc_mgmt_tb.i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_clk_gen.u_soc_mgmt_pll_and_mux.pll_clk;
  mon_pll_lock    = soc_mgmt_tb.i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_clk_gen.u_soc_mgmt_pll_and_mux.o_pll_lock;
  mon_pll_m       = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_clk_gen.u_soc_mgmt_pll_and_mux.i_csr_pll_feedback_div;
  mon_pll_p       = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_clk_gen.u_soc_mgmt_pll_and_mux.i_csr_pll_ref_output_div;
  mon_pll_s       = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_clk_gen.u_soc_mgmt_pll_and_mux.i_csr_pll_pre_output_div;
  mon_clk_sel     = soc_mgmt_tb.i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_clk_gen.u_soc_mgmt_pll_and_mux.i_csr_clk_mux_select;

  meas_div_clk[0] = o_codec_clk ;
  meas_div_clk[1] = o_emmc_clk  ;
  meas_div_clk[2] = o_periph_clk;
  meas_div_clk[3] = o_noc_clk   ;
  meas_div_clk[4] = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_clk_gen.o_pvt_clk;
end

//==============================================================================`
for (genvar i=0; i<soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL; i++) begin : gen_pll_clk_meas
  tb_gen_clk_checker #(
    .CH                ( i + 1 ),
    .PLL_OR_DIVN_CHECK ( 1     )
  ) u_tb_gen_pll_clk_checker (
    .i_ref_clk      (i_ref_clk           ),
    .i_rst_n        (i_por_rst_n         ),
    .i_gen_clk      ( mon_pll_out_clk[i] ),
    .i_mon_pll_lock ( mon_pll_lock   [i] ),
    .i_mon_pll_m    ( mon_pll_m      [i] ),
    .i_mon_pll_p    ( mon_pll_p      [i] ),
    .i_mon_pll_s    ( mon_pll_s      [i] ),
    .i_mon_clk_sel  ( mon_clk_sel    [i] ),
    .i_div          ( '1                 ),
    .o_fail         ( pll_meas_fail  [i] )
  );
end

// clock from pll[0]
for (genvar i=0; i<soc_mgmt_clk_checker_pkg::NUM_DIV_CLK; i++) begin : gen_div_clk_meas
  tb_gen_clk_checker #(
    .CH                ( i ),
    .PLL_OR_DIVN_CHECK ( 0 )
  ) u_tb_gen_div_clk_checker (
    .i_ref_clk      (o_fast_clk          ),
    .i_rst_n        (i_por_rst_n         ),
    .i_gen_clk      ( meas_div_clk   [i] ),
    .i_mon_pll_lock ( mon_pll_lock   [0] ),
    .i_mon_pll_m    ( '0                 ),
    .i_mon_pll_p    ( '0                 ),
    .i_mon_pll_s    ( '0                 ),
    .i_mon_clk_sel  ( mon_clk_sel    [0] ),
    .i_div          ( div_clk_exp    [i] ),
    .o_fail         ( div_meas_fail  [i] )
  );
end
*/

`ifdef POWER_PINS
  pullup   ( io_pvt_dvdd075a_ts );
  pulldown ( io_pvt_dvss0a_ts   );
  pullup   ( io_pvt_avdd18a_ts  );
  pulldown ( io_pvt_avss0a_ts   );
  pulldown ( io_pvt_avss_gd     );
  pullup   ( io_pll_avdd18      );
  pulldown ( io_pll_avss        );
  pullup   ( io_pll_dvdd075     );
  pulldown ( io_pll_dvss        );
`endif

//==============================================================================`
// debugger connections assetions
`include "soc_mgmt_debugger_connectivity_assertions.svh"

//==============================================================================`
// DEBUG o chck div_by_pt operation
//wire [9:0] tmp_d_clk;
//wire [9:0] tmp_d_clk5;
//wire [9:0] tmp_d_clk6;
//logic [3:0] incr[10] = '{
//  4'h0, 4'h1, 4'h2, 4'h3, 4'h4, 4'h5, 4'h6, 4'h7, 4'h8, 4'h19
//};
//
//logic [4:0] incr5[10] = '{
//  5'h0, 5'h1, 5'h2, 5'h3, 5'h4, 5'h5, 5'h6, 5'h7, 5'h8, 5'h19
//};
//
//logic [9:0] incr6[10] = '{
// 'd41, 'd40, 'd39, 'd42, 'd38, 'd19, 'd26, 'd20, 'd21, 'd25
//};
//
//for (genvar i=0; i<10; i++) begin : gen_clk_div
//  axe_ccl_clk_div_by_pt #(
//    .PhaseAccWidth ( 4    ), //PHASEACCWIDTH_D6 ),
//    .ResetValClkEn ( 1'h1 ), //RESETVALCLKEN    ),
//    .DelayClkPulse ( 1'h0 )  //DELAYCLKPULSE    )
//  ) u_axe_emmc_clk_div (
//    .i_clk      ( i_ref_clk   ),
//    .i_rst_n    ( i_por_rst_n ),
//    .i_test_en  ( 1'h0        ),
//    .i_div_en   ( 1'h1        ),
//    .i_acc_clr  ( 1'h0        ),
//    .i_acc_incr ( incr     [i]),
//    .o_active   (             ),
//    .o_clk      ( tmp_d_clk[i])
//  );
//end
//
//for (genvar i=0; i<10; i++) begin : gen_clk_div_5
//  axe_ccl_clk_div_by_pt #(
//    .PhaseAccWidth ( 5    ), //PHASEACCWIDTH_D6 ),
//    .ResetValClkEn ( 1'h1 ), //RESETVALCLKEN    ),
//    .DelayClkPulse ( 1'h0 )  //DELAYCLKPULSE    )
//  ) u_axe_emmc_clk_div_5 (
//    .i_clk      ( i_ref_clk   ),
//    .i_rst_n    ( i_por_rst_n ),
//    .i_test_en  ( 1'h0        ),
//    .i_div_en   ( 1'h1        ),
//    .i_acc_clr  ( 1'h0        ),
//    .i_acc_incr ( incr5    [i]),
//    .o_active   (             ),
//    .o_clk      ( tmp_d_clk5[i])
//  );
//
//  axe_ccl_clk_div_by_pt #(
//    .PhaseAccWidth ( 10   ), //PHASEACCWIDTH_D6 ),
//    .ResetValClkEn ( 1'h1 ), //RESETVALCLKEN    ),
//    .DelayClkPulse ( 1'h0 )  //DELAYCLKPULSE    )
//  ) u_axe_emmc_clk_div_6 (
//    .i_clk      ( i_ref_clk    ),
//    .i_rst_n    ( i_por_rst_n  ),
//    .i_test_en  ( 1'h0         ),
//    .i_div_en   ( 1'h1         ),
//    .i_acc_clr  ( 1'h0         ),
//    .i_acc_incr ( incr6     [i]),
//    .o_active   (              ),
//    .o_clk      ( tmp_d_clk6[i])
//  );
//end

endmodule
