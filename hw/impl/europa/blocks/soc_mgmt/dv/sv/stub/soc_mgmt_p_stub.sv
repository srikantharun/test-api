// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

module soc_mgmt_p_stub
  import chip_pkg    ::*;
  import axi_pkg     ::*;
  import soc_mgmt_pkg::*;
  import rot_pkg     ::*;
(
  /// Reference clock and external resets.
  input  wire                              i_ref_clk                  ,
  /// Asynchronous Power On Reset, active low
  input  wire                              i_por_rst_n                ,
  /// Asynchroonous Always On state reset to all partitions, active low.
  output wire                              o_ao_rst_n                 ,
  /// Asynchroonous Global Reset to all partitions, active low.
  output wire                              o_global_rst_n             ,
  /// Fast Clock output from PLL-0
  output wire                              o_fast_clk                 ,
  // APU Clock output from PLL-1
  output wire                              o_apu_clk                  ,
  // DDR clock -> direct from the pll2
  output wire                              o_ddr_ref_east_clk         ,

  // Output clocks
  output wire                              o_codec_clk                ,
  output wire                              o_emmc_clk                 ,
  output wire                              o_periph_clk               ,
  output wire                              o_noc_clk                  ,

  // noc reset
  output wire                              o_noc_rst_n                ,

  // dlm
  output aic_thrtl_t                       o_aic_throttle             ,
  output dlm_clk_thrtl_t                   o_clock_throttle           ,
  input  aic_boost_t                       i_aic_boost_req            ,
  output aic_boost_t                       o_aic_boost_ack            ,
  input  logic                             i_throttle                 ,
  output logic                             o_dlm_irq_warning          ,
  output logic                             o_dlm_irq_critical         ,

  // mbist reset
  /// NoC Connections LP AXI Manager Interface
  // AXI address write channel
  output chip_pkg::chip_axi_addr_t         o_lt_axi_m_awaddr          ,
  output soc_mgmt_lt_axi_m_id_t            o_lt_axi_m_awid            ,
  output axi_pkg::axi_len_t                o_lt_axi_m_awlen           ,
  output axi_pkg::axi_size_t               o_lt_axi_m_awsize          ,
  output axi_pkg::axi_burst_t              o_lt_axi_m_awburst         ,
  output axi_pkg::axi_cache_t              o_lt_axi_m_awcache         ,
  output axi_pkg::axi_prot_t               o_lt_axi_m_awprot          ,
  output logic                             o_lt_axi_m_awlock          ,
  output axi_pkg::axi_qos_t                o_lt_axi_m_awqos           ,
  output axi_pkg::axi_region_t             o_lt_axi_m_awregion        ,
  output chip_pkg::chip_axi_lt_awuser_t    o_lt_axi_m_awuser          ,
  output logic                             o_lt_axi_m_awvalid         ,
  input  logic                             i_lt_axi_m_awready         ,
  // AXI write data channel
  output logic                             o_lt_axi_m_wvalid          ,
  output logic                             o_lt_axi_m_wlast           ,
  output chip_pkg::chip_axi_lt_wstrb_t     o_lt_axi_m_wstrb           ,
  output chip_pkg::chip_axi_lt_data_t      o_lt_axi_m_wdata           ,
  output chip_pkg::chip_axi_ht_wuser_t     o_lt_axi_m_wuser           ,
  input  logic                             i_lt_axi_m_wready          ,
  // AXI write response channel
  input  logic                             i_lt_axi_m_bvalid          ,
  input  soc_mgmt_lt_axi_m_id_t            i_lt_axi_m_bid             ,
  input  axi_pkg::axi_resp_t               i_lt_axi_m_bresp           ,
  input  chip_pkg::chip_axi_lt_buser_t     i_lt_axi_m_buser           ,
  output logic                             o_lt_axi_m_bready          ,
  // AXI read address channel
  output logic                             o_lt_axi_m_arvalid         ,
  output chip_pkg::chip_axi_addr_t         o_lt_axi_m_araddr          ,
  output soc_mgmt_lt_axi_m_id_t            o_lt_axi_m_arid            ,
  output axi_pkg::axi_len_t                o_lt_axi_m_arlen           ,
  output axi_pkg::axi_size_t               o_lt_axi_m_arsize          ,
  output axi_pkg::axi_burst_t              o_lt_axi_m_arburst         ,
  output axi_pkg::axi_cache_t              o_lt_axi_m_arcache         ,
  output axi_pkg::axi_prot_t               o_lt_axi_m_arprot          ,
  output axi_pkg::axi_qos_t                o_lt_axi_m_arqos           ,
  output axi_pkg::axi_region_t             o_lt_axi_m_arregion        ,
  output chip_pkg::chip_axi_lt_aruser_t    o_lt_axi_m_aruser          ,
  output logic                             o_lt_axi_m_arlock          ,
  input  logic                             i_lt_axi_m_arready         ,
  // AXI read data/response channel
  input  logic                             i_lt_axi_m_rvalid          ,
  input  logic                             i_lt_axi_m_rlast           ,
  input  soc_mgmt_lt_axi_m_id_t            i_lt_axi_m_rid             ,
  input  chip_pkg::chip_axi_lt_data_t      i_lt_axi_m_rdata           ,
  input  axi_pkg::axi_resp_t               i_lt_axi_m_rresp           ,
  input  chip_pkg::chip_axi_lt_ruser_t     i_lt_axi_m_ruser           ,
  output logic                             o_lt_axi_m_rready          ,

  /// NoC Connections LP AXI Subordinate Interface
  input  logic                             i_lt_axi_s_awvalid         ,
  input  chip_pkg::chip_axi_addr_t         i_lt_axi_s_awaddr          ,
  input  soc_mgmt_lt_axi_s_id_t            i_lt_axi_s_awid            ,
  input  axi_pkg::axi_len_t                i_lt_axi_s_awlen           ,
  input  axi_pkg::axi_size_t               i_lt_axi_s_awsize          ,
  input  axi_pkg::axi_burst_t              i_lt_axi_s_awburst         ,
  input  axi_pkg::axi_cache_t              i_lt_axi_s_awcache         ,
  input  axi_pkg::axi_prot_t               i_lt_axi_s_awprot          ,
  input  logic                             i_lt_axi_s_awlock          ,
  input  axi_pkg::axi_qos_t                i_lt_axi_s_awqos           ,
  input  axi_pkg::axi_region_t             i_lt_axi_s_awregion        ,
  input  chip_pkg::chip_axi_lt_awuser_t    i_lt_axi_s_awuser          ,
  output logic                             o_lt_axi_s_awready         ,
  input  logic                             i_lt_axi_s_wvalid          ,
  input  logic                             i_lt_axi_s_wlast           ,
  input  chip_pkg::chip_axi_lt_wstrb_t     i_lt_axi_s_wstrb           ,
  input  chip_pkg::chip_axi_lt_data_t      i_lt_axi_s_wdata           ,
  input  chip_pkg::chip_axi_lt_wuser_t     i_lt_axi_s_wuser           ,
  output logic                             o_lt_axi_s_wready          ,
  output logic                             o_lt_axi_s_bvalid          ,
  output soc_mgmt_lt_axi_s_id_t            o_lt_axi_s_bid             ,
  output axi_pkg::axi_resp_t               o_lt_axi_s_bresp           ,
  output chip_pkg::chip_axi_lt_buser_t     o_lt_axi_s_buser           ,
  input  logic                             i_lt_axi_s_bready          ,
  input  logic                             i_lt_axi_s_arvalid         ,
  input  chip_pkg::chip_axi_addr_t         i_lt_axi_s_araddr          ,
  input  soc_mgmt_lt_axi_s_id_t            i_lt_axi_s_arid            ,
  input  axi_pkg::axi_len_t                i_lt_axi_s_arlen           ,
  input  axi_pkg::axi_size_t               i_lt_axi_s_arsize          ,
  input  axi_pkg::axi_burst_t              i_lt_axi_s_arburst         ,
  input  axi_pkg::axi_cache_t              i_lt_axi_s_arcache         ,
  input  axi_pkg::axi_prot_t               i_lt_axi_s_arprot          ,
  input  axi_pkg::axi_qos_t                i_lt_axi_s_arqos           ,
  input  axi_pkg::axi_region_t             i_lt_axi_s_arregion        ,
  input  chip_pkg::chip_axi_lt_aruser_t    i_lt_axi_s_aruser          ,
  input  logic                             i_lt_axi_s_arlock          ,
  output logic                             o_lt_axi_s_arready         ,
  output logic                             o_lt_axi_s_rvalid          ,
  output logic                             o_lt_axi_s_rlast           ,
  output soc_mgmt_lt_axi_s_id_t            o_lt_axi_s_rid             ,
  output chip_pkg::chip_axi_lt_data_t      o_lt_axi_s_rdata           ,
  output axi_pkg::axi_resp_t               o_lt_axi_s_rresp           ,
  output chip_pkg::chip_axi_lt_ruser_t     o_lt_axi_s_ruser           ,
  input  logic                             i_lt_axi_s_rready          ,

  /// SYSCFG APB slave signals
  input  chip_soc_mgmt_syscfg_addr_t       i_syscfg_apb4_s_paddr      ,
  input  chip_apb_syscfg_data_t            i_syscfg_apb4_s_pwdata     ,
  input  logic                             i_syscfg_apb4_s_pwrite     ,
  input  logic                             i_syscfg_apb4_s_psel       ,
  input  logic                             i_syscfg_apb4_s_penable    ,
  input  chip_apb_syscfg_strb_t            i_syscfg_apb4_s_pstrb      ,
  input  logic          [3-1:0]            i_syscfg_apb4_s_pprot      ,
  output logic                             o_syscfg_apb4_s_pready     ,
  output chip_apb_syscfg_data_t            o_syscfg_apb4_s_prdata     ,
  output logic                             o_syscfg_apb4_s_pslverr    ,

  output logic [15:0]                      o_mbist_apb_m_paddr        ,
  output logic [31:0]                      o_mbist_apb_m_pwdata       ,
  output logic                             o_mbist_apb_m_pwrite       ,
  output logic                             o_mbist_apb_m_psel         ,
  output logic                             o_mbist_apb_m_penable      ,
  input  logic                             i_mbist_apb_m_pready       ,
  input  logic [31:0]                      i_mbist_apb_m_prdata       ,
  input  logic                             i_mbist_apb_m_pslverr      ,

  // thermal throttle override
  input  logic                             i_thermal_throttle         ,
  // thermal throttle output to AI cores
  output tms_temp_t                        o_thermal_throttle         ,
  // thrermnal warning. From thermal throttle. Overheating warning to boardsystem
  output logic                             o_thermal_throttle_warning_n ,
  // thermal warning. To partition AI cores
  output tms_temp_t                        o_thermal_warning          ,
  // thermal shutdown. Will reset the chip via pcb controller
  output logic                             o_thermal_shutdown_n       ,
  // tms interrupt output
  output logic                             o_irq_tms_throttle         ,
  output logic                             o_irq_tms_warning          ,
  output logic                             o_irq_tms_shutdown         ,
  /// Interrupts
  // RTC interrupt
  output logic                             o_rtc_irq                  ,
  // Watchdog interrupt
  output logic                             o_wdt_irq                  ,
  // Security interrupt
  output logic                             o_security_irq             ,

  /// DFT Interface
  input  logic                             test_mode                  ,
  input  logic [24:0]                      i_dft_spare                ,
  output logic [24:0]                      o_dft_spare                ,

  input  wire                              ssn_bus_clk                ,
  output logic [23:0]                      ssn_bus_data_in            ,
  input  logic [23:0]                      ssn_bus_data_out           ,

  input  wire                              bisr_clk                   ,
  input  wire                              bisr_reset                 ,
  input  logic                             bisr_shift_en              ,
  input  logic                             bisr_si                    ,
  output logic                             bisr_so                    ,

  input  wire                              tck                        ,
  input  wire                              trst                       ,
  input  logic                             tms                        ,
  input  logic                             tdi                        ,
  output logic                             tdo_en                     ,
  output logic                             tdo                        ,

  /// MBIST enable

  // resrt request for stage 1
  input  logic                             i_auto_repair_done         ,
  // reset request for stage 2.

  // Trace debug interface
  output dbg_hart_t                        o_debugint                 ,
  output dbg_hart_t                        o_resethaltreq             ,
  input  dbg_hart_t                        i_hart_unavail             ,
  input  dbg_hart_t                        i_hart_under_reset         ,

  /// Debug TAPs enable signals
  output dbg_taps_en_t                     o_dbg_taps_en              ,
  /// OTP TAP enable signal
  output logic                             o_otp_tap_en               ,

  /// Placeholder for DFT Signals
  /// Placeholder for DFT Signals - OTP Wrapper
  input  logic                             i_dft_otp_test_mode        ,
  input  otp_wrapper_pkg::otp_addr_t       i_dft_otp_tst_a            ,
  input  logic                             i_dft_otp_tst_din          ,
  input  logic                             i_dft_otp_tst_readen       ,
  input  logic                             i_dft_otp_tst_ceb          ,
  input  logic                             i_dft_otp_tst_cle          ,
  input  logic                             i_dft_otp_tst_dle          ,
  input  logic                             i_dft_otp_tst_web          ,
  input  logic                             i_dft_otp_tst_rstb         ,
  input  logic                             i_dft_otp_tst_cpumpen      ,
  input  logic                             i_dft_otp_tst_pgmen        ,
  input  logic                             i_dft_otp_tst_seltm        ,
  input  logic                             i_dft_otp_tst_vddrdy       ,
  input  logic                             i_dft_otp_tst_clken        ,
  output otp_wrapper_pkg::otp_data_t       o_dft_otp_tst_d            ,
  output otp_wrapper_pkg::otp_lock_t       o_dft_otp_tst_lock         ,

  /// Observability signal interface.
  input  obs_in_t                          i_obs_bus                  ,
  output obs_out_t                         o_obs_bus                  ,

  // global sync
  output logic                             o_global_sync              ,

  /// OTP Analog signals to IO PAD
  inout  wire                              io_otp_vtdo                ,
  inout  wire                              io_otp_vrefm               ,
  inout  wire                              io_otp_vpp                 ,

  /// PVT Sensor Analog signals to Remote Probe (to be manually routed).
  /// Temperature sensor signals for providing bias current to IBIAS_TS of remote probes (tu_tem0501ar01_ln05lpe_4007002).
  /// It must be connected with IBIAS_TS in each remote probe if you want to use remote probes. For unused signals, leave as floating
  inout  wire  [62:0]                      io_pvt_ibias_ts            ,
  /// Temperature sensor signals for voltage sensing from VSENSE_TS of remote probes (tu_tem0501ar01_ln05lpe_4007002).
  /// It must be connected with VSENSE_TS in each remote probe if you want to use remote probes. For unused signals, leave as floating
  inout  wire  [62:0]                      io_pvt_vsense_ts           ,
  /// PVT Sensor Analog signals to IO-PAD.
  /// Analog monitoring signal for test purposes: refer to test MUX control guide in DataSheet
  /// MUX_ADDR_TS can select internal analog voltage. Connect with AY500 (500ohm) port
  inout  wire                              io_pvt_test_out_ts         ,

  // Efuse interface analog signals.
  inout  wire                              io_efuse_vqps              ,
  inout  wire                              io_efuse_vddwl
`ifdef POWER_PINS
                                                                      ,
  inout  wire                              io_pvt_dvdd075a_ts         ,
  inout  wire                              io_pvt_dvss0a_ts           ,
  inout  wire                              io_pvt_avdd18a_ts          ,
  inout  wire                              io_pvt_avss0a_ts           ,
  inout  wire                              io_pvt_avss_gd             ,
  input  wire                              io_pll_avdd18              ,
  input  wire                              io_pll_avss                ,
  input  wire                              io_pll_dvdd075             ,
  input  wire                              io_pll_dvss
`endif
);

  bit clk_20MHz, clk_13333KHz;

  `ifndef SYNTHESIS
  bit clk_enable = 0;

    axe_clk_generator i_axe_clk_generator_20MHz (
        .i_enable(clk_enable),
        .o_clk(clk_20MHz)
    );
    axe_clk_generator i_axe_clk_generator_13333KHz (
        .i_enable(clk_enable),
        .o_clk(clk_13333KHz)
    );

    initial begin
      i_axe_clk_generator_20MHz.set_clock(.freq_mhz(20), .duty(50));
      i_axe_clk_generator_13333KHz.set_clock(.freq_mhz(13.33), .duty(50));
      clk_enable = 1;
    end

  `endif

  assign o_ao_rst_n = i_por_rst_n;
  assign o_global_rst_n = i_por_rst_n;
  assign o_fast_clk = clk_20MHz;
  assign o_apu_clk = clk_20MHz;
  assign o_ddr_ref_east_clk = clk_13333KHz;
  assign o_codec_clk = clk_20MHz;
  assign o_emmc_clk = clk_20MHz;
  assign o_periph_clk = clk_20MHz;
  assign o_noc_clk = clk_20MHz;
  assign o_noc_rst_n = i_por_rst_n;
  assign o_aic_throttle = '0;
  assign o_clock_throttle = '0;
  assign o_aic_boost_ack = '0;
  assign o_dlm_irq_warning = 1'b0;
  assign o_dlm_irq_critica = 1'b0;
  assign o_lt_axi_m_awaddr = '0;
  assign o_lt_axi_m_awid = '0;
  assign o_lt_axi_m_awlen = '0;
  assign o_lt_axi_m_awsize = '0;
  assign o_lt_axi_m_awburst = '0;
  assign o_lt_axi_m_awcache = '0;
  assign o_lt_axi_m_awprot = '0;
  assign o_lt_axi_m_awlock = 1'b0;
  assign o_lt_axi_m_awqos = '0;
  assign o_lt_axi_m_awregion = '0;
  assign o_lt_axi_m_awuser = '0;
  assign o_lt_axi_m_awvalid = 1'b0;
  assign o_lt_axi_m_wvalid = 1'b0;
  assign o_lt_axi_m_wlast = 1'b0;
  assign o_lt_axi_m_wstrb = '0;
  assign o_lt_axi_m_wdata = '0;
  assign o_lt_axi_m_wuser = '0;
  assign o_lt_axi_m_bready = 1'b1;
  assign o_lt_axi_m_arvalid = 1'b0;
  assign o_lt_axi_m_araddr = '0;
  assign o_lt_axi_m_arid = '0;
  assign o_lt_axi_m_arlen = '0;
  assign o_lt_axi_m_arsize = '0;
  assign o_lt_axi_m_arburst = '0;
  assign o_lt_axi_m_arcache = '0;
  assign o_lt_axi_m_arprot = '0;
  assign o_lt_axi_m_arqos = '0;
  assign o_lt_axi_m_arregion = '0;
  assign o_lt_axi_m_aruser = '0;
  assign o_lt_axi_m_arlock = 1'b0;
  assign o_lt_axi_m_rready = 1'b1;
  assign o_lt_axi_s_awready = 1'b1;
  assign o_lt_axi_s_wready = 1'b1;
  assign o_lt_axi_s_bvalid = 1'b0;
  assign o_lt_axi_s_bid = '0;
  assign o_lt_axi_s_bresp = '0;
  assign o_lt_axi_s_buser = '0;
  assign o_lt_axi_s_arready = 1'b1;
  assign o_lt_axi_s_rvalid = 1'b0;
  assign o_lt_axi_s_rlast = 1'b0;
  assign o_lt_axi_s_rid = '0;
  assign o_lt_axi_s_rdata = '0;
  assign o_lt_axi_s_rresp = '0;
  assign o_lt_axi_s_ruser = '0;
  assign o_syscfg_apb4_s_pready = 1'b1;
  assign o_syscfg_apb4_s_prdata = '0;
  assign o_syscfg_apb4_s_pslverr = 1'b0;
  assign o_thermal_throttle = '0;
  assign o_thermal_throttle_warning_n = 1'b0;
  assign o_thermal_warning = '0;
  assign o_thermal_shutdown_n = 1'b0;
  assign o_irq_tms_throttle = 1'b0;
  assign o_irq_tms_warning = 1'b0;
  assign o_irq_tms_shutdown = 1'b0;
  assign o_rtc_irq = 1'b0;
  assign o_wdt_irq = 1'b0;
  assign o_security_irq = 1'b0;
  assign ssn_bus_data_out = '0;
  assign bisr_so = 1'b0;
  assign tdo = 1'b0;
  assign tdo_en = 1'b0;
  assign o_debugint = '0;
  assign o_resethaltreq = '0;
  assign o_dbg_taps_en = '0;
  assign o_otp_tap_en = 1'b0;
  assign o_dft_otp_tst_d = '0;
  assign o_dft_otp_tst_lock = '0;
  assign o_obs_bus = '0;
  assign o_global_sync = 1'b0;

endmodule
