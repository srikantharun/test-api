// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Timir Soni <timir.soni@axelera.ai>

// Description: Top module for the SoC Management Block.


// SOC_MGMT hdl top
`define AXI_VIP

`define DUT dut

`define SOC_MGMT_DUT `DUT

module hdl_top;
  // Time unit and precision
  timeunit 1ns; timeprecision 1ns;

  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"
   // import package for type declarations
  import soc_mgmt_pkg::*;
  import chip_pkg    ::*;

  // testbench packages
  import axi_pkg::*;


`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif
  import soc_mgmt_test_pkg::*;

  //============================================================================
  // Set to 1.2 GHz
  localparam realtime TbCycleTime = 0.8333ns;

  // Setup AT timing
  localparam realtime TbApplTime = 0.1 * TbCycleTime;
  localparam realtime TbTestTime = 0.9 * TbCycleTime;

  localparam int NB_CLK   = 2;
  localparam int NB_RESET = 2;

  localparam type gen_clk_t = logic [NB_CLK  -1:0];
  localparam type gen_rst_t = logic [NB_RESET-1:0];

  // Clock / Reset genereration and stop of simulation
  // clocks
  gen_clk_t                            gen_clk                    ;
  gen_rst_t                            gen_rst                    ;
  wire                                 i_ref_clk                  ;
  wire                                 o_fast_clk                 ;
  wire                                 o_apu_clk                  ;
  wire                                 o_ddr_ref_east_clk         ;

  // resets
  wire                                 i_por_rst_n                ;
  wire                                 o_ao_rst_n                 ;
  wire                                 o_global_rst_n             ;

  wire                                 o_codec_clk                ;
  wire                                 o_emmc_clk                 ;
  wire                                 o_periph_clk               ;
  wire                                 o_noc_clk                  ;
  wire                                 o_noc_rst_n                ;

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

  chip_soc_mgmt_syscfg_addr_t          i_syscfg_apb4_s_paddr      ;
  chip_apb_syscfg_data_t               i_syscfg_apb4_s_pwdata     ;
  logic                                i_syscfg_apb4_s_pwrite     ;
  logic                                i_syscfg_apb4_s_psel       ;
  logic                                i_syscfg_apb4_s_penable    ;
  chip_apb_syscfg_strb_t               i_syscfg_apb4_s_pstrb      ;
  logic          [3-1:0]               i_syscfg_apb4_s_pprot      ;
  logic                                o_syscfg_apb4_s_pready     ;
  chip_apb_syscfg_data_t               o_syscfg_apb4_s_prdata     ;
  logic                                o_syscfg_apb4_s_pslverr    ;

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
                                                                  ;
  logic                                bisr_clk                   ;
  logic                                bisr_reset                 ;
  logic                                bisr_shift_en              ;
  logic                                bisr_si                    ;
  logic                                bisr_so                    ;

  /// jtag serial test data in.;
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

  chip_pkg::chip_axi_addr_t            reg_addr                   ;
  chip_pkg::chip_axi_lt_data_t         reg_read_data              ;
  axi_pkg::axi_resp_t                  reg_resp                   ;

  event                                ev_debug0                  ;
  event                                ev_debug1                  ;
  event                                ev_debug2                  ;

  int unsigned                         test_step                  ;
  logic                                clk_en                     ;


  // =============================================================================================================
  // Instantiate interfaces and BFMs and assignments
  // =============================================================================================================

`ifdef AXI_VIP
  // VIP Interface instance representing the AXI system
  svt_axi_if axi_if ();
  assign axi_if.common_aclk = o_periph_clk;
  // TB Interface instance to provide access to the reset signal
  axi_reset_if axi_reset_if ();
  assign axi_reset_if.clk = o_periph_clk;

  assign axi_if.master_if[0].aresetn =  i_por_rst_n;
  assign axi_if.slave_if[0].aresetn =   i_por_rst_n;
`endif

`ifdef APB_VIP
  // VIP Interface instance representing the AXI system
  svt_apb_if apb_dut_master_if ();
  assign apb_dut_master_if.pclk = i_ref_clk;
  assign apb_dut_master_if.presetn              = apb_reset_if.presetn;
  // TB Interface instance to provide access to the reset signal
  apb_reset_if apb_reset_if ();
  assign apb_reset_if.pclk           = i_ref_clk;
  assign apb_reset_if.presetn        = i_por_rst_n;

`endif


  // AXI Msster LT interface
  assign i_lt_axi_s_awvalid = axi_if.master_if[0].awvalid;
  assign i_lt_axi_s_awaddr  = axi_if.master_if[0].awaddr;
  assign i_lt_axi_s_awid    = axi_if.master_if[0].awid;
  assign i_lt_axi_s_awlen   = axi_if.master_if[0].awlen;
  assign i_lt_axi_s_awsize  = axi_if.master_if[0].awsize;
  assign i_lt_axi_s_awburst = axi_if.master_if[0].awburst;


  assign axi_if.master_if[0].awready = o_lt_axi_s_awready;

  assign i_lt_axi_s_wvalid  = axi_if.master_if[0].wvalid;
  assign i_lt_axi_s_wlast   = axi_if.master_if[0].wlast;
  assign i_lt_axi_s_wdata   = axi_if.master_if[0].wdata;
  assign i_lt_axi_s_wstrb   = axi_if.master_if[0].wstrb;

  assign axi_if.master_if[0].wready = o_lt_axi_s_wready;

  assign axi_if.master_if[0].bvalid = o_lt_axi_s_bvalid;
  assign axi_if.master_if[0].bid    = o_lt_axi_s_bid;
  assign axi_if.master_if[0].bresp  = o_lt_axi_s_bresp;

  assign i_lt_axi_s_bready  = axi_if.master_if[0].bready;

  assign i_lt_axi_s_arvalid = axi_if.master_if[0].arvalid;
  assign i_lt_axi_s_araddr  = axi_if.master_if[0].araddr;
  assign i_lt_axi_s_arid    = axi_if.master_if[0].arid;
  assign i_lt_axi_s_arlen   = axi_if.master_if[0].arlen;
  assign i_lt_axi_s_arsize  = axi_if.master_if[0].arsize;
  assign i_lt_axi_s_arburst = axi_if.master_if[0].arburst;

  assign axi_if.master_if[0].arready = o_lt_axi_s_arready;

  assign axi_if.master_if[0].rvalid = o_lt_axi_s_rvalid;
  assign axi_if.master_if[0].rlast  = o_lt_axi_s_rlast;
  assign axi_if.master_if[0].rid    = o_lt_axi_s_rid;
  assign axi_if.master_if[0].rdata  = o_lt_axi_s_rdata;
  assign axi_if.master_if[0].rresp  = o_lt_axi_s_rresp;

  assign i_lt_axi_s_rready  = axi_if.master_if[0].rready;

  // AXI Slave LT interface
  assign axi_if.slave_if[0].awvalid  = o_lt_axi_m_awvalid;
  assign axi_if.slave_if[0].awaddr   = o_lt_axi_m_awaddr;
  assign axi_if.slave_if[0].awid     = o_lt_axi_m_awid;
  assign axi_if.slave_if[0].awlen    = o_lt_axi_m_awlen;
  assign axi_if.slave_if[0].awsize   = o_lt_axi_m_awsize;
  assign axi_if.slave_if[0].awburst  = o_lt_axi_m_awburst;


  assign i_lt_axi_m_awready = axi_if.slave_if[0].awready;

  assign axi_if.slave_if[0].wvalid= o_lt_axi_m_wvalid;
  assign axi_if.slave_if[0].wlast = o_lt_axi_m_wlast;
  assign axi_if.slave_if[0].wdata = o_lt_axi_m_wdata;
  assign axi_if.slave_if[0].wstrb = o_lt_axi_m_wstrb;

  assign i_lt_axi_m_wready   = axi_if.slave_if[0].wready;//

  assign i_lt_axi_m_bvalid = axi_if.slave_if[0].bvalid;
  assign i_lt_axi_m_bid    = axi_if.slave_if[0].bid;
  assign i_lt_axi_m_bresp  = axi_if.slave_if[0].bresp;

  assign axi_if.slave_if[0].bready = o_lt_axi_m_bready;

  assign axi_if.slave_if[0].arvalid = o_lt_axi_m_arvalid;
  assign axi_if.slave_if[0].araddr  = o_lt_axi_m_araddr;
  assign axi_if.slave_if[0].arid    = o_lt_axi_m_arid;
  assign axi_if.slave_if[0].arlen   = o_lt_axi_m_arlen;
  assign axi_if.slave_if[0].arsize  = o_lt_axi_m_arsize;
  assign axi_if.slave_if[0].arburst = o_lt_axi_m_arburst;

  assign i_lt_axi_m_arready = axi_if.slave_if[0].arready;

  assign i_lt_axi_m_rvalid = axi_if.slave_if[0].rvalid;
  assign i_lt_axi_m_rlast  = axi_if.slave_if[0].rlast;
  assign i_lt_axi_m_rid    = axi_if.slave_if[0].rid;
  assign i_lt_axi_m_rdata  = axi_if.slave_if[0].rdata;
  assign i_lt_axi_m_rresp  = axi_if.slave_if[0].rresp;

  assign axi_if.slave_if[0].rready = o_lt_axi_m_rready;
///////////////////////////////////////////////////////////
  assign i_syscfg_apb4_s_paddr   = apb_dut_master_if.paddr;
  assign i_syscfg_apb4_s_pwdata  = apb_dut_master_if.pwdata;
  assign i_syscfg_apb4_s_pwrite  = apb_dut_master_if.pwrite;
  assign i_syscfg_apb4_s_psel    = apb_dut_master_if.psel[0];
  assign i_syscfg_apb4_s_penable = apb_dut_master_if.penable;
  assign i_syscfg_apb4_s_pstrb   = apb_dut_master_if.pstrb;
  assign i_syscfg_apb4_s_pprot   = apb_dut_master_if.pprot;

  assign apb_dut_master_if.slave_if[0].pready   = o_syscfg_apb4_s_pready;
  assign apb_dut_master_if.slave_if[0].prdata   = o_syscfg_apb4_s_prdata;
  assign apb_dut_master_if.slave_if[0].pslverr   = o_syscfg_apb4_s_pslverr;

  assign soc_mgmt_if.o_ao_rst_n = o_ao_rst_n;
  assign soc_mgmt_if.o_global_rst_n = o_global_rst_n;


  initial begin : proc_clk_rst_gen
    bit [32:0] resval;

    tms                     = '0;
    tdi                     = '0;
    test_mode               = '0;
    i_dft_spare             = '0;
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
    i_hart_unavail          = '0;
    i_hart_under_reset      = '0;

    #(1us);

  end



/////////////////////////////////////////////////////////////////////////

  localparam real CLK_FREQ[NB_CLK] = '{
    50,//.0e6, // REF clock
   100//.0e6  // TCK
  };

  int  fast_clk_freq_mhz = 1200;
  time fast_clk_tol_ps  = 10;
  wire fast_clk_check_en;
  
  int  apu_clk_freq_mhz = 1000;
  time apu_clk_tol_ps  = 10;
  wire apu_clk_check_en;
  
  int  codec_clk_freq_mhz = 600;
  time codec_clk_tol_ps  = 10;
  wire codec_clk_check_en;
  
  int  emmc_clk_freq_mhz = 200;
  time emmc_clk_tol_ps  = 10;
  wire emmc_clk_check_en;

  int  periph_clk_freq_mhz = 100;
  time periph_clk_tol_ps  = 10;
  wire periph_clk_check_en;
  
  int  pvt_clk_freq_mhz = 4;
  time pvt_clk_tol_ps  = 10;
  wire pvt_clk_check_en;

  int  ddr_clk_freq_mhz = 800;
  time ddr_clk_tol_ps  = 10;
  wire ddr_clk_check_en;
  
    
  assign fast_clk_check_en   = soc_mgmt_if.fast_clk_check_en;
  assign apu_clk_check_en    = soc_mgmt_if.apu_clk_check_en;
  assign codec_clk_check_en  = soc_mgmt_if.codec_clk_check_en;
  assign emmc_clk_check_en   = soc_mgmt_if.emmc_clk_check_en;
  assign periph_clk_check_en = soc_mgmt_if.periph_clk_check_en;
  assign pvt_clk_check_en    = soc_mgmt_if.pvt_clk_check_en;
  assign ddr_clk_check_en    = soc_mgmt_if.ddr_clk_check_en;
    
  // clock generator
  for (genvar i=0; i<NB_CLK; i++) begin : gen_tb_clocks
    axe_clk_generator u_soc_mgmt_clk_generator(.i_enable(clk_en),
			              .o_clk(gen_clk[i])
				      );
  end

  // fast_clk frequency checker
  axe_clk_assert u_axe_clk_assert_fast_clk(.clk(o_fast_clk),
 		 .rst_n(fast_clk_check_en),
 		 .freq_mhz(fast_clk_freq_mhz),
 		 .tol_ps  (fast_clk_tol_ps)
 		 );

  // apu_clk frequency checker
  axe_clk_assert u_axe_clk_assert_apu_clk(.clk(o_apu_clk),
 		 .rst_n(apu_clk_check_en),
 		 .freq_mhz(apu_clk_freq_mhz),
 		 .tol_ps  (apu_clk_tol_ps)
 		 );

  // codec_clk frequency checker
  axe_clk_assert u_axe_clk_assert_codec_clk(.clk(o_codec_clk),
 		 .rst_n(codec_clk_check_en),
 		 .freq_mhz(codec_clk_freq_mhz),
 		 .tol_ps  (codec_clk_tol_ps)
 		 );

  // emmc_clk frequency checker
  axe_clk_assert u_axe_clk_assert_emmc_clk(.clk(o_emmc_clk),
 		 .rst_n(emmc_clk_check_en),
 		 .freq_mhz(emmc_clk_freq_mhz),
 		 .tol_ps  (emmc_clk_tol_ps)
 		 );

  // periph_clk frequency checker
  axe_clk_assert u_axe_clk_assert_periph_clk(.clk(o_periph_clk),
 		 .rst_n(periph_clk_check_en),
 		 .freq_mhz(periph_clk_freq_mhz),
 		 .tol_ps  (periph_clk_tol_ps)
 		 );

  // pvt_clk frequency checker
  axe_clk_assert u_axe_clk_assert_pvt_clk(.clk(i_soc_mgmt_p_dut.u_soc_mgmt.pvt_clk),
 		 .rst_n(pvt_clk_check_en),
 		 .freq_mhz(pvt_clk_freq_mhz),
 		 .tol_ps  (pvt_clk_tol_ps)
 		 );

  // ddr_ref_east_clk frequency checker
  axe_clk_assert u_axe_clk_assert_ddr_clk(.clk(o_ddr_ref_east_clk),
 		 .rst_n(ddr_clk_check_en),
 		 .freq_mhz(ddr_clk_freq_mhz),
 		 .tol_ps  (ddr_clk_tol_ps)
 		 );


  // Set clock frequency and duty cycle outside the loop
  initial begin
        gen_tb_clocks[0].u_soc_mgmt_clk_generator.set_clock(.freq_mhz(CLK_FREQ[0]), .duty(50));
        gen_tb_clocks[1].u_soc_mgmt_clk_generator.set_clock(.freq_mhz(CLK_FREQ[1]), .duty(50));
        clk_en <= 1'b1;
  end

  // connect clock to dut input clocks
  assign i_ref_clk            = gen_clk[0];
  assign tck                  = gen_clk[1];

  //==============================================================================
  // reset generator
  for (genvar i=0; i<NB_RESET; i++) begin : gen_tb_resets
    axe_rst_generator u_soc_mgmt_rst_generator(.i_clk(gen_clk[i]),
			              .o_rst(gen_rst[i])
				      );
  end


  // Set asynchronous reset delay outside the loop
  initial begin
    gen_tb_resets[0].u_soc_mgmt_rst_generator.async_rst(50);
    gen_tb_resets[1].u_soc_mgmt_rst_generator.async_rst(50);
  end

  assign i_por_rst_n         = ~gen_rst[0];
  assign trst                = ~gen_rst[1];

  // =============================================================================================================
  // SOC_MGMT user define INTERFACE
  // =============================================================================================================
  soc_mgmt_if soc_mgmt_if (i_ref_clk, i_por_rst_n);

`ifndef NO_DUT
  // Design Under Test (DUT)
  soc_mgmt_p  i_soc_mgmt_p_dut (
    .i_ref_clk                    ( i_ref_clk                  ),
    .i_por_rst_n                  ( i_por_rst_n                ),
    .o_ao_rst_n                   ( o_ao_rst_n                 ),
    .o_global_rst_n               ( o_global_rst_n             ),
    .o_fast_clk                   ( o_fast_clk                 ),
    .o_apu_clk                    ( o_apu_clk                  ),
    .o_ddr_ref_east_clk           ( o_ddr_ref_east_clk         ),
    .o_codec_clk                  ( o_codec_clk                ),
    .o_emmc_clk                   ( o_emmc_clk                 ),
    .o_periph_clk                 ( o_periph_clk               ),
    .o_noc_clk                    ( o_noc_clk                  ),
    .o_noc_rst_n                  ( o_noc_rst_n                ),
    .o_lt_axi_m_awaddr            ( o_lt_axi_m_awaddr          ),
    .o_lt_axi_m_awid              ( o_lt_axi_m_awid            ),
    .o_lt_axi_m_awlen             ( o_lt_axi_m_awlen           ),
    .o_lt_axi_m_awsize            ( o_lt_axi_m_awsize          ),
    .o_lt_axi_m_awburst           ( o_lt_axi_m_awburst         ),
    .o_lt_axi_m_awcache           ( o_lt_axi_m_awcache         ),
    .o_lt_axi_m_awprot            ( o_lt_axi_m_awprot          ),
    .o_lt_axi_m_awlock            ( o_lt_axi_m_awlock          ),
    .o_lt_axi_m_awqos             ( o_lt_axi_m_awqos           ),
    .o_lt_axi_m_awregion          ( o_lt_axi_m_awregion        ),
    .o_lt_axi_m_awuser            ( o_lt_axi_m_awuser          ),
    .o_lt_axi_m_awvalid           ( o_lt_axi_m_awvalid         ),
    .i_lt_axi_m_awready           ( i_lt_axi_m_awready         ),
    .o_lt_axi_m_wvalid            ( o_lt_axi_m_wvalid          ),
    .o_lt_axi_m_wlast             ( o_lt_axi_m_wlast           ),
    .o_lt_axi_m_wstrb             ( o_lt_axi_m_wstrb           ),
    .o_lt_axi_m_wdata             ( o_lt_axi_m_wdata           ),
    .o_lt_axi_m_wuser             ( o_lt_axi_m_wuser           ),
    .i_lt_axi_m_wready            ( i_lt_axi_m_wready          ),
    .i_lt_axi_m_bvalid            ( i_lt_axi_m_bvalid          ),
    .i_lt_axi_m_bid               ( i_lt_axi_m_bid             ),
    .i_lt_axi_m_bresp             ( i_lt_axi_m_bresp           ),
    .i_lt_axi_m_buser             ( i_lt_axi_m_buser           ),
    .o_lt_axi_m_bready            ( o_lt_axi_m_bready          ),
    .o_lt_axi_m_arvalid           ( o_lt_axi_m_arvalid         ),
    .o_lt_axi_m_araddr            ( o_lt_axi_m_araddr          ),
    .o_lt_axi_m_arid              ( o_lt_axi_m_arid            ),
    .o_lt_axi_m_arlen             ( o_lt_axi_m_arlen           ),
    .o_lt_axi_m_arsize            ( o_lt_axi_m_arsize          ),
    .o_lt_axi_m_arburst           ( o_lt_axi_m_arburst         ),
    .o_lt_axi_m_arcache           ( o_lt_axi_m_arcache         ),
    .o_lt_axi_m_arprot            ( o_lt_axi_m_arprot          ),
    .o_lt_axi_m_arqos             ( o_lt_axi_m_arqos           ),
    .o_lt_axi_m_arregion          ( o_lt_axi_m_arregion        ),
    .o_lt_axi_m_aruser            ( o_lt_axi_m_aruser          ),
    .o_lt_axi_m_arlock            ( o_lt_axi_m_arlock          ),
    .i_lt_axi_m_arready           ( i_lt_axi_m_arready         ),
    .i_lt_axi_m_rvalid            ( i_lt_axi_m_rvalid          ),
    .i_lt_axi_m_rlast             ( i_lt_axi_m_rlast           ),
    .i_lt_axi_m_rid               ( i_lt_axi_m_rid             ),
    .i_lt_axi_m_rdata             ( i_lt_axi_m_rdata           ),
    .i_lt_axi_m_rresp             ( i_lt_axi_m_rresp           ),
    .i_lt_axi_m_ruser             ( i_lt_axi_m_ruser           ),
    .o_lt_axi_m_rready            ( o_lt_axi_m_rready          ),
    .i_lt_axi_s_awvalid           ( i_lt_axi_s_awvalid         ),
    .i_lt_axi_s_awaddr            ( i_lt_axi_s_awaddr          ),
    .i_lt_axi_s_awid              ( i_lt_axi_s_awid            ),
    .i_lt_axi_s_awlen             ( i_lt_axi_s_awlen           ),
    .i_lt_axi_s_awsize            ( i_lt_axi_s_awsize          ),
    .i_lt_axi_s_awburst           ( i_lt_axi_s_awburst         ),
    .i_lt_axi_s_awcache           ( i_lt_axi_s_awcache         ),
    .i_lt_axi_s_awprot            ( i_lt_axi_s_awprot          ),
    .i_lt_axi_s_awlock            ( i_lt_axi_s_awlock          ),
    .i_lt_axi_s_awqos             ( i_lt_axi_s_awqos           ),
    .i_lt_axi_s_awregion          ( i_lt_axi_s_awregion        ),
    .i_lt_axi_s_awuser            ( i_lt_axi_s_awuser          ),
    .o_lt_axi_s_awready           ( o_lt_axi_s_awready         ),
    .i_lt_axi_s_wvalid            ( i_lt_axi_s_wvalid          ),
    .i_lt_axi_s_wlast             ( i_lt_axi_s_wlast           ),
    .i_lt_axi_s_wstrb             ( i_lt_axi_s_wstrb           ),
    .i_lt_axi_s_wdata             ( i_lt_axi_s_wdata           ),
    .i_lt_axi_s_wuser             ( i_lt_axi_s_wuser           ),
    .o_lt_axi_s_wready            ( o_lt_axi_s_wready          ),
    .o_lt_axi_s_bvalid            ( o_lt_axi_s_bvalid          ),
    .o_lt_axi_s_bid               ( o_lt_axi_s_bid             ),
    .o_lt_axi_s_bresp             ( o_lt_axi_s_bresp           ),
    .o_lt_axi_s_buser             ( o_lt_axi_s_buser           ),
    .i_lt_axi_s_bready            ( i_lt_axi_s_bready          ),
    .i_lt_axi_s_arvalid           ( i_lt_axi_s_arvalid         ),
    .i_lt_axi_s_araddr            ( i_lt_axi_s_araddr          ),
    .i_lt_axi_s_arid              ( i_lt_axi_s_arid            ),
    .i_lt_axi_s_arlen             ( i_lt_axi_s_arlen           ),
    .i_lt_axi_s_arsize            ( i_lt_axi_s_arsize          ),
    .i_lt_axi_s_arburst           ( i_lt_axi_s_arburst         ),
    .i_lt_axi_s_arcache           ( i_lt_axi_s_arcache         ),
    .i_lt_axi_s_arprot            ( i_lt_axi_s_arprot          ),
    .i_lt_axi_s_arqos             ( i_lt_axi_s_arqos           ),
    .i_lt_axi_s_arregion          ( i_lt_axi_s_arregion        ),
    .i_lt_axi_s_aruser            ( i_lt_axi_s_aruser          ),
    .i_lt_axi_s_arlock            ( i_lt_axi_s_arlock          ),
    .o_lt_axi_s_arready           ( o_lt_axi_s_arready         ),
    .o_lt_axi_s_rvalid            ( o_lt_axi_s_rvalid          ),
    .o_lt_axi_s_rlast             ( o_lt_axi_s_rlast           ),
    .o_lt_axi_s_rid               ( o_lt_axi_s_rid             ),
    .o_lt_axi_s_rdata             ( o_lt_axi_s_rdata           ),
    .o_lt_axi_s_rresp             ( o_lt_axi_s_rresp           ),
    .o_lt_axi_s_ruser             ( o_lt_axi_s_ruser           ),
    .i_lt_axi_s_rready            ( i_lt_axi_s_rready          ),
    .i_syscfg_apb4_s_paddr        ( i_syscfg_apb4_s_paddr      ),
    .i_syscfg_apb4_s_pwdata       ( i_syscfg_apb4_s_pwdata     ),
    .i_syscfg_apb4_s_pwrite       ( i_syscfg_apb4_s_pwrite     ),
    .i_syscfg_apb4_s_psel         ( i_syscfg_apb4_s_psel       ),
    .i_syscfg_apb4_s_penable      ( i_syscfg_apb4_s_penable    ),
    .i_syscfg_apb4_s_pstrb        ( i_syscfg_apb4_s_pstrb      ),
    .i_syscfg_apb4_s_pprot        ( i_syscfg_apb4_s_pprot      ),
    .o_syscfg_apb4_s_pready       ( o_syscfg_apb4_s_pready     ),
    .o_syscfg_apb4_s_prdata       ( o_syscfg_apb4_s_prdata     ),
    .o_syscfg_apb4_s_pslverr      ( o_syscfg_apb4_s_pslverr    ),
    .i_thermal_throttle           ( i_thermal_throttle         ),
    .o_thermal_throttle           ( o_thermal_throttle         ),
    .o_thermal_throttle_warning_n ( o_thermal_throttle_warning_n ),
    .o_thermal_warning            ( o_thermal_warning          ),
    .o_thermal_shutdown_n         ( o_thermal_shutdown_n       ),
    .o_rtc_irq                    ( o_rtc_irq                  ),
    .o_wdt_irq                    ( o_wdt_irq                  ),
    .o_security_irq               ( o_security_irq             ),
    .tck                          ( tck                        ),
    .trst                         ( trst                       ),
    .tms                          ( tms                        ),
    .tdi                          ( tdi                        ),
    .tdo_en                       ( tdo_en                     ),
    .tdo                          ( tdo                        ),
    .test_mode                    ( test_mode                  ),

    .bisr_clk                     ( bisr_clk                   ),
    .bisr_reset                   ( bisr_reset                 ),
    .bisr_shift_en                ( bisr_shift_en              ),
    .bisr_si                      ( bisr_si                    ),
    .bisr_so                      ( bisr_so                    ),
    .i_auto_repair_done           ( i_auto_repair_done         ),
    .o_debugint                   ( o_debugint                 ),
    .o_resethaltreq               ( o_resethaltreq             ),
    .i_hart_unavail               ( i_hart_unavail             ),
    .i_hart_under_reset           ( i_hart_under_reset         ),
    .i_dft_otp_test_mode          ( i_dft_otp_test_mode        ),
    .i_dft_otp_tst_a              ( i_dft_otp_tst_a            ),
    .i_dft_otp_tst_din            ( i_dft_otp_tst_din          ),
    .i_dft_otp_tst_readen         ( i_dft_otp_tst_readen       ),
    .i_dft_otp_tst_ceb            ( i_dft_otp_tst_ceb          ),
    .i_dft_otp_tst_cle            ( i_dft_otp_tst_cle          ),
    .i_dft_otp_tst_dle            ( i_dft_otp_tst_dle          ),
    .i_dft_otp_tst_web            ( i_dft_otp_tst_web          ),
    .i_dft_otp_tst_rstb           ( i_dft_otp_tst_rstb         ),
    .i_dft_otp_tst_cpumpen        ( i_dft_otp_tst_cpumpen      ),
    .i_dft_otp_tst_pgmen          ( i_dft_otp_tst_pgmen        ),
    .i_dft_otp_tst_seltm          ( i_dft_otp_tst_seltm        ),
    .i_dft_otp_tst_vddrdy         ( i_dft_otp_tst_vddrdy       ),
    .i_dft_otp_tst_clken          ( i_dft_otp_tst_clken        ),
    .o_dft_otp_tst_d              ( o_dft_otp_tst_d            ),
    .o_dft_otp_tst_lock           ( o_dft_otp_tst_lock         ),
    .i_obs_bus                    ( i_obs_bus                  ),
    .o_obs_bus                    ( o_obs_bus                  ),
    .o_global_sync                ( o_global_sync              ),
    .io_otp_vtdo                  ( io_otp_vtdo                ),
    .io_otp_vrefm                 ( io_otp_vrefm               ),
    .io_otp_vpp                   ( io_otp_vpp                 ),
    .io_pvt_ibias_ts              ( io_pvt_ibias_ts            ),
    .io_pvt_vsense_ts             ( io_pvt_vsense_ts           ),
    .io_pvt_test_out_ts           ( io_pvt_test_out_ts         ),
    .io_efuse_vqps                ( io_efuse_vqps              ),
    .io_efuse_vddwl               ( io_efuse_vddwl             )
  );

`endif

//==============================================================================
  wire pvt_io_avss_ts;
  wire pvt_io_avss_gd;

  assign pvt_io_avss_ts = 1'h0;
  assign pvt_io_avss_gd = 1'h0;

  initial begin
    import uvm_pkg::uvm_config_db;
    `ifdef AXI_VIP
    // Set the reset interface on the virtual sequencer
    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(
        uvm_root::get(), "uvm_test_top.env.sequencer", "reset_mp", axi_reset_if.axi_reset_modport);

    // =============================================================================================================
    // Provide the AXI SV interface to the AXI System ENV. This step establishes the connection between the AXI
    // System ENV and the DUT through the AXI interface.
    // =============================================================================================================
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.env.axi_system_env", "vif", axi_if);
    `endif

    `ifdef APB_VIP
     uvm_config_db#(virtual apb_reset_if.apb_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.apb_sequencer", "reset_mp",apb_reset_if.apb_reset_modport);
     uvm_config_db#(virtual svt_apb_if )::set(uvm_root::get(), "uvm_test_top.env.apb_master_env", "vif", apb_dut_master_if);

    `endif
    /** Provide token agent interfaces */

    uvm_config_db#(virtual soc_mgmt_if)::set(uvm_root::get(), "*", "soc_mgmt_if", soc_mgmt_if);

  end


  // Run test
  initial begin
    run_test();
  end
endmodule : hdl_top
