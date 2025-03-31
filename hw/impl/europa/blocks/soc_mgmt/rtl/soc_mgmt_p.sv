// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

/// Description: Top module for the SoC Management Block.
///
module soc_mgmt_p
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

  // SoC Mgmt fence
  output logic                             o_noc_async_idle_req,
  input  logic                             i_noc_async_idle_ack,
  input  logic                             i_noc_async_idle_val,

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

  ////////////////////////////
  // MBIST Manager APB3 port//
  ////////////////////////////
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
  output logic                             o_thermal_throttle_warning_n,
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

  // Boot Mode
  input  logic [2:0]                       i_boot_mode                ,
  /// DFT Interface
  input  logic                             test_mode                  ,
  input  logic [24:0]                      i_dft_spare                ,
  output logic [24:0]                      o_dft_spare                ,

  input  wire                              ssn_bus_clk                ,
  input  logic [23:0]                      ssn_bus_data_in            ,
  output logic [23:0]                      ssn_bus_data_out           ,

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

//==============================================================================
// signal declaration
// global sync from CSR
logic  global_sync_async      ;

logic pctl_ret                ;
logic pctl_pde                ;
logic pctl_prn                ;

wire  fast_clk_int            ;

// APB demux output
chip_syscfg_addr_t           apb_m_paddr  [SYSCFG_NB_APBOUT] ;
chip_apb_syscfg_data_t       apb_m_pwdata [SYSCFG_NB_APBOUT] ;
logic                        apb_m_pwrite [SYSCFG_NB_APBOUT] ;
logic                        apb_m_psel   [SYSCFG_NB_APBOUT] ;
logic                        apb_m_penable[SYSCFG_NB_APBOUT] ;
chip_apb_syscfg_strb_t       apb_m_pstrb  [SYSCFG_NB_APBOUT] ;
axe_apb_pkg::apb_prot_t      apb_m_pprot  [SYSCFG_NB_APBOUT] ;
logic                        apb_m_pready [SYSCFG_NB_APBOUT] ;
chip_apb_syscfg_data_t       apb_m_prdata [SYSCFG_NB_APBOUT] ;
logic                        apb_m_pslverr[SYSCFG_NB_APBOUT] ;
// Selected subordinate from address decoder
syscfg_apb_mux_idx_t         sub_idx_from_dec         ;

logic                        pslverr_demux            ;
logic                        pslverr_decode           ;

//==============================================================================
// JTAG serial data daisy chain.
// KSE3 TAP and dft TAP are placed by DFT. RTL only contains the Debugger TAP.
// The JTAG chain is connected by DFT.
//
// tms ----------+-------------+-----------------+
//               V             v                 V
//        +-----------+    +---------+    +--------------+
// tdi -> | KSE3_TAP  | -> | dft TAP | -> | Debugger TAP | -> tdo
//        +-----------+    +---------+    +--------------+
//

//==============================================================================
soc_mgmt u_soc_mgmt (
  /// Reference clock and external resets.
  .i_ref_clk                  ( i_ref_clk                  ),
  /// Asynchronous Power On Reset, active low
  .i_por_rst_n                ( i_por_rst_n                ),
  /// Asynchronous Always On state reset to all partitions, active low.
  .o_ao_rst_n                 ( o_ao_rst_n                 ),
  /// Asynchroonous Global Reset to all partitions, active low.
  .o_global_rst_n             ( o_global_rst_n             ),
  /// Fast Clock output from PLL-0
  .o_fast_clk_ext             ( o_fast_clk                 ),
  .o_fast_clk_int             ( fast_clk_int               ),
  // APU Clock output from PLL-1
  .o_apu_clk                  ( o_apu_clk                  ),
  // DDR clock -> direct from the pll2
  .o_ddr_ref_east_clk         ( o_ddr_ref_east_clk         ),

  // Output clocks
  .o_codec_clk                ( o_codec_clk                ),
  .o_emmc_clk                 ( o_emmc_clk                 ),
  .o_periph_clk               ( o_periph_clk               ),

  // dlm
  .o_aic_throttle             ( o_aic_throttle             ),
  .o_clock_throttle           ( o_clock_throttle           ),
  .i_aic_boost_req            ( i_aic_boost_req            ),
  .o_aic_boost_ack            ( o_aic_boost_ack            ),
  .i_throttle                 ( i_throttle                 ),
  .o_dlm_irq_warning          ( o_dlm_irq_warning          ),
  .o_dlm_irq_critical         ( o_dlm_irq_critical         ),

  /// AXI Connections LP AXI Manager Interface
  // AXI address write channel
  .o_lt_axi_m_awaddr          ( o_lt_axi_m_awaddr          ),
  .o_lt_axi_m_awid            ( o_lt_axi_m_awid            ),
  .o_lt_axi_m_awlen           ( o_lt_axi_m_awlen           ),
  .o_lt_axi_m_awsize          ( o_lt_axi_m_awsize          ),
  .o_lt_axi_m_awburst         ( o_lt_axi_m_awburst         ),
  .o_lt_axi_m_awcache         ( o_lt_axi_m_awcache         ),
  .o_lt_axi_m_awprot          ( o_lt_axi_m_awprot          ),
  .o_lt_axi_m_awlock          ( o_lt_axi_m_awlock          ),
  .o_lt_axi_m_awqos           ( o_lt_axi_m_awqos           ),
  .o_lt_axi_m_awregion        ( o_lt_axi_m_awregion        ),
  .o_lt_axi_m_awuser          ( o_lt_axi_m_awuser          ),
  .o_lt_axi_m_awvalid         ( o_lt_axi_m_awvalid         ),
  .i_lt_axi_m_awready         ( i_lt_axi_m_awready         ),
  // AXI write data channel
  .o_lt_axi_m_wvalid          ( o_lt_axi_m_wvalid          ),
  .o_lt_axi_m_wlast           ( o_lt_axi_m_wlast           ),
  .o_lt_axi_m_wstrb           ( o_lt_axi_m_wstrb           ),
  .o_lt_axi_m_wdata           ( o_lt_axi_m_wdata           ),
  .o_lt_axi_m_wuser           ( o_lt_axi_m_wuser           ),
  .i_lt_axi_m_wready          ( i_lt_axi_m_wready          ),
  // AXI write response channel
  .i_lt_axi_m_bvalid          ( i_lt_axi_m_bvalid          ),
  .i_lt_axi_m_bid             ( i_lt_axi_m_bid             ),
  .i_lt_axi_m_bresp           ( i_lt_axi_m_bresp           ),
  .i_lt_axi_m_buser           ( i_lt_axi_m_buser           ),
  .o_lt_axi_m_bready          ( o_lt_axi_m_bready          ),
  // AXI read address channel
  .o_lt_axi_m_arvalid         ( o_lt_axi_m_arvalid         ),
  .o_lt_axi_m_araddr          ( o_lt_axi_m_araddr          ),
  .o_lt_axi_m_arid            ( o_lt_axi_m_arid            ),
  .o_lt_axi_m_arlen           ( o_lt_axi_m_arlen           ),
  .o_lt_axi_m_arsize          ( o_lt_axi_m_arsize          ),
  .o_lt_axi_m_arburst         ( o_lt_axi_m_arburst         ),
  .o_lt_axi_m_arcache         ( o_lt_axi_m_arcache         ),
  .o_lt_axi_m_arprot          ( o_lt_axi_m_arprot          ),
  .o_lt_axi_m_arqos           ( o_lt_axi_m_arqos           ),
  .o_lt_axi_m_arregion        ( o_lt_axi_m_arregion        ),
  .o_lt_axi_m_aruser          ( o_lt_axi_m_aruser          ),
  .o_lt_axi_m_arlock          ( o_lt_axi_m_arlock          ),
  .i_lt_axi_m_arready         ( i_lt_axi_m_arready         ),
  // AXI read data/response channel
  .i_lt_axi_m_rvalid          ( i_lt_axi_m_rvalid          ),
  .i_lt_axi_m_rlast           ( i_lt_axi_m_rlast           ),
  .i_lt_axi_m_rid             ( i_lt_axi_m_rid             ),
  .i_lt_axi_m_rdata           ( i_lt_axi_m_rdata           ),
  .i_lt_axi_m_rresp           ( i_lt_axi_m_rresp           ),
  .i_lt_axi_m_ruser           ( i_lt_axi_m_ruser           ),
  .o_lt_axi_m_rready          ( o_lt_axi_m_rready          ),

  /// AXI Connections LP AXI Subordinate Interface
  .i_lt_axi_s_awvalid         ( i_lt_axi_s_awvalid         ),
  .i_lt_axi_s_awaddr          ( i_lt_axi_s_awaddr          ),
  .i_lt_axi_s_awid            ( i_lt_axi_s_awid            ),
  .i_lt_axi_s_awlen           ( i_lt_axi_s_awlen           ),
  .i_lt_axi_s_awsize          ( i_lt_axi_s_awsize          ),
  .i_lt_axi_s_awburst         ( i_lt_axi_s_awburst         ),
  .i_lt_axi_s_awcache         ( i_lt_axi_s_awcache         ),
  .i_lt_axi_s_awprot          ( i_lt_axi_s_awprot          ),
  .i_lt_axi_s_awlock          ( i_lt_axi_s_awlock          ),
  .i_lt_axi_s_awqos           ( i_lt_axi_s_awqos           ),
  .i_lt_axi_s_awregion        ( i_lt_axi_s_awregion        ),
  .i_lt_axi_s_awuser          ( i_lt_axi_s_awuser          ),
  .o_lt_axi_s_awready         ( o_lt_axi_s_awready         ),
  .i_lt_axi_s_wvalid          ( i_lt_axi_s_wvalid          ),
  .i_lt_axi_s_wlast           ( i_lt_axi_s_wlast           ),
  .i_lt_axi_s_wstrb           ( i_lt_axi_s_wstrb           ),
  .i_lt_axi_s_wdata           ( i_lt_axi_s_wdata           ),
  .i_lt_axi_s_wuser           ( i_lt_axi_s_wuser           ),
  .o_lt_axi_s_wready          ( o_lt_axi_s_wready          ),
  .o_lt_axi_s_bvalid          ( o_lt_axi_s_bvalid          ),
  .o_lt_axi_s_bid             ( o_lt_axi_s_bid             ),
  .o_lt_axi_s_bresp           ( o_lt_axi_s_bresp           ),
  .o_lt_axi_s_buser           ( o_lt_axi_s_buser           ),
  .i_lt_axi_s_bready          ( i_lt_axi_s_bready          ),
  .i_lt_axi_s_arvalid         ( i_lt_axi_s_arvalid         ),
  .i_lt_axi_s_araddr          ( i_lt_axi_s_araddr          ),
  .i_lt_axi_s_arid            ( i_lt_axi_s_arid            ),
  .i_lt_axi_s_arlen           ( i_lt_axi_s_arlen           ),
  .i_lt_axi_s_arsize          ( i_lt_axi_s_arsize          ),
  .i_lt_axi_s_arburst         ( i_lt_axi_s_arburst         ),
  .i_lt_axi_s_arcache         ( i_lt_axi_s_arcache         ),
  .i_lt_axi_s_arprot          ( i_lt_axi_s_arprot          ),
  .i_lt_axi_s_arqos           ( i_lt_axi_s_arqos           ),
  .i_lt_axi_s_arregion        ( i_lt_axi_s_arregion        ),
  .i_lt_axi_s_aruser          ( i_lt_axi_s_aruser          ),
  .i_lt_axi_s_arlock          ( i_lt_axi_s_arlock          ),
  .o_lt_axi_s_arready         ( o_lt_axi_s_arready         ),
  .o_lt_axi_s_rvalid          ( o_lt_axi_s_rvalid          ),
  .o_lt_axi_s_rlast           ( o_lt_axi_s_rlast           ),
  .o_lt_axi_s_rid             ( o_lt_axi_s_rid             ),
  .o_lt_axi_s_rdata           ( o_lt_axi_s_rdata           ),
  .o_lt_axi_s_rresp           ( o_lt_axi_s_rresp           ),
  .o_lt_axi_s_ruser           ( o_lt_axi_s_ruser           ),
  .i_lt_axi_s_rready          ( i_lt_axi_s_rready          ),

  // clock gen csr apb
  .i_clk_gen_csr_apb_paddr    ( apb_m_paddr  [0]           ),
  .i_clk_gen_csr_apb_pwdata   ( apb_m_pwdata [0]           ),
  .i_clk_gen_csr_apb_pwrite   ( apb_m_pwrite [0]           ),
  .i_clk_gen_csr_apb_psel     ( apb_m_psel   [0]           ),
  .i_clk_gen_csr_apb_penable  ( apb_m_penable[0]           ),
  .i_clk_gen_csr_apb_pstrb    ( apb_m_pstrb  [0]           ),
  .i_clk_gen_csr_apb_pprot    ( apb_m_pprot  [0]           ),
  .o_clk_gen_csr_apb_pready   ( apb_m_pready [0]           ),
  .o_clk_gen_csr_apb_prdata   ( apb_m_prdata [0]           ),
  .o_clk_gen_csr_apb_pslverr  ( apb_m_pslverr[0]           ),

  // reset gen csr apb
  .i_rst_gen_csr_apb_paddr    ( apb_m_paddr  [1]           ),
  .i_rst_gen_csr_apb_pwdata   ( apb_m_pwdata [1]           ),
  .i_rst_gen_csr_apb_pwrite   ( apb_m_pwrite [1]           ),
  .i_rst_gen_csr_apb_psel     ( apb_m_psel   [1]           ),
  .i_rst_gen_csr_apb_penable  ( apb_m_penable[1]           ),
  .i_rst_gen_csr_apb_pstrb    ( apb_m_pstrb  [1]           ),
  .i_rst_gen_csr_apb_pprot    ( apb_m_pprot  [1]           ),
  .o_rst_gen_csr_apb_pready   ( apb_m_pready [1]           ),
  .o_rst_gen_csr_apb_prdata   ( apb_m_prdata [1]           ),
  .o_rst_gen_csr_apb_pslverr  ( apb_m_pslverr[1]           ),

  .i_apb_misc_csr_paddr  (apb_m_paddr[3]),
  .i_apb_misc_csr_pwdata (apb_m_pwdata[3]),
  .i_apb_misc_csr_pwrite (apb_m_pwrite[3]),
  .i_apb_misc_csr_psel   (apb_m_psel[3]),
  .i_apb_misc_csr_penable(apb_m_penable[3]),
  .i_apb_misc_csr_pstrb  (apb_m_pstrb[3]),
  .i_apb_misc_csr_pprot  (apb_m_pprot[3]),
  .o_apb_misc_csr_pready (apb_m_pready[3]),
  .o_apb_misc_csr_prdata (apb_m_prdata[3]),
  .o_apb_misc_csr_pslverr(apb_m_pslverr[3]),

  .o_mbist_apb_m_paddr   (o_mbist_apb_m_paddr),
  .o_mbist_apb_m_pwdata  (o_mbist_apb_m_pwdata),
  .o_mbist_apb_m_pwrite  (o_mbist_apb_m_pwrite),
  .o_mbist_apb_m_psel    (o_mbist_apb_m_psel),
  .o_mbist_apb_m_penable (o_mbist_apb_m_penable),
  .i_mbist_apb_m_pready  (i_mbist_apb_m_pready),
  .i_mbist_apb_m_prdata  (i_mbist_apb_m_prdata),
  .i_mbist_apb_m_pslverr (i_mbist_apb_m_pslverr),

  // thermal throttle override
  .i_thermal_throttle         ( i_thermal_throttle         ),
  // thermal throttle output to AI cores
  .o_thermal_throttle         ( o_thermal_throttle         ),
  // thrermnal warning. From thermal throttle. Overheating warning to boardsystem
  .o_thermal_throttle_warning_n ( o_thermal_throttle_warning_n ),
  // thermal warning. To partition AI cores
  .o_thermal_warning          ( o_thermal_warning          ),
  // thermal shutdown. Will reset the chip via pcb controller
  .o_thermal_shutdown_n       ( o_thermal_shutdown_n       ),
  // tms int
  .o_irq_tms_throttle         ( o_irq_tms_throttle         ),
  .o_irq_tms_warning          ( o_irq_tms_warning          ),
  .o_irq_tms_shutdown         ( o_irq_tms_shutdown         ),

  /// Interrupts
  // RTC interrupt
  .o_rtc_irq                  ( o_rtc_irq                  ),
  // Watchdog interrupt
  .o_wdt_irq                  ( o_wdt_irq                  ),

  // Securinty interrupt
  .o_security_irq             ( o_security_irq             ),

  // Boot Mode
  .i_boot_mode                ( i_boot_mode                ),

  /// Jtag Interface
  /// Test Clock
  .tck                        ( tck                        ),
  .trst                       ( trst                       ),
  .tms                        ( tms                        ),
  /// Debugger
  .jtag_tdi_dbg               ( tdi                        ),
  .jtag_tdo_dbg               ( tdo                        ),
  .jtag_tdo_en_dbg            ( tdo_en                     ),
  /// DFT reset override signals
  .test_mode                  ( test_mode                  ),

  // resrt request for stage 1
  .i_auto_repair_done         ( i_auto_repair_done         ),
  // reset request for stage 2.

  // Trace debug interface
  .o_debugint                 ( o_debugint                 ),
  .o_resethaltreq             ( o_resethaltreq             ),
  .i_hart_unavail             ( i_hart_unavail             ),
  .i_hart_under_reset         ( i_hart_under_reset         ),
  // Debug TAPs enable signals
  .o_dbg_taps_en              ( o_dbg_taps_en              ),
  // OTP TAP enable signal
  .o_otp_tap_en               ( o_otp_tap_en               ),
  /// Placeholder for DFT Signals
  /// Placeholder for DFT Signals - OTP Wrapper
  .i_dft_otp_test_mode        ( i_dft_otp_test_mode        ),
  .i_dft_otp_tst_a            ( i_dft_otp_tst_a            ),
  .i_dft_otp_tst_din          ( i_dft_otp_tst_din          ),
  .i_dft_otp_tst_readen       ( i_dft_otp_tst_readen       ),
  .i_dft_otp_tst_ceb          ( i_dft_otp_tst_ceb          ),
  .i_dft_otp_tst_cle          ( i_dft_otp_tst_cle          ),
  .i_dft_otp_tst_dle          ( i_dft_otp_tst_dle          ),
  .i_dft_otp_tst_web          ( i_dft_otp_tst_web          ),
  .i_dft_otp_tst_rstb         ( i_dft_otp_tst_rstb         ),
  .i_dft_otp_tst_cpumpen      ( i_dft_otp_tst_cpumpen      ),
  .i_dft_otp_tst_pgmen        ( i_dft_otp_tst_pgmen        ),
  .i_dft_otp_tst_seltm        ( i_dft_otp_tst_seltm        ),
  .i_dft_otp_tst_vddrdy       ( i_dft_otp_tst_vddrdy       ),
  .i_dft_otp_tst_clken        ( i_dft_otp_tst_clken        ),
  .o_dft_otp_tst_d            ( o_dft_otp_tst_d            ),
  .o_dft_otp_tst_lock         ( o_dft_otp_tst_lock         ),

  /// Observability signal interface.
  .i_obs_bus                  ( i_obs_bus                  ),
  .o_obs_bus                  ( o_obs_bus                  ),

  // global sync
  .o_global_sync              ( global_sync_async          ),

  /// OTP Analog signals to IO PAD
  .io_otp_vtdo                ( io_otp_vtdo                ),
  .io_otp_vrefm               ( io_otp_vrefm               ),
  .io_otp_vpp                 ( io_otp_vpp                 ),

  /// PVT Sensor Analog signals to Remote Probe (to be manually routed).
  /// Temperature sensor signals for providing bias current to IBIAS_TS of remote probes (tu_tem0501ar01_ln05lpe_4007002).
  /// It must be connected with IBIAS_TS in each remote probe if you want to use remote probes. For unused signals, leave as floating
  .io_pvt_ibias_ts            ( io_pvt_ibias_ts            ),
  /// Temperature sensor signals for voltage sensing from VSENSE_TS of remote probes (tu_tem0501ar01_ln05lpe_4007002).
  /// It must be connected with VSENSE_TS in each remote probe if you want to use remote probes. For unused signals, leave as floating
  .io_pvt_vsense_ts           ( io_pvt_vsense_ts           ),
  /// PVT Sensor Analog signals to IO-PAD.
  /// Analog monitoring signal for test purposes: refer to test MUX control guide in DataSheet
  /// MUX_ADDR_TS can select internal analog voltage. Connect with AY500 (500ohm) port
  .io_pvt_test_out_ts         ( io_pvt_test_out_ts         ),

  // Efuse interface analog signals.
  .io_efuse_vqps              ( io_efuse_vqps              ),
  .io_efuse_vddwl             ( io_efuse_vddwl             )

`ifdef POWER_PINS
                                                            ,
  .io_pvt_dvdd075a_ts         ( io_pvt_dvdd075a_ts         ),
  .io_pvt_dvss0a_ts           ( io_pvt_dvss0a_ts           ),
  .io_pvt_avdd18a_ts          ( io_pvt_avdd18a_ts          ),
  .io_pvt_avss0a_ts           ( io_pvt_avss0a_ts           ),
  .io_pvt_avss_gd             ( io_pvt_avss_gd             ),
  .io_pll_avdd18              ( io_pll_avdd18              ),
  .io_pll_avss                ( io_pll_avss                ),
  .io_pll_dvdd075             ( io_pll_dvdd075             ),
  .io_pll_dvss
`endif
);

//============================================================================
// APB Demux
// TODO(jmartins, Silver, Review the APB Demux.)
axe_apb_demux #(
  .NB_APBOUT      (SYSCFG_NB_APBOUT),
  .PAW            (SYSCFG_APB_DEMUX_PAW),
  .PDW            (SYSCFG_APB_DEMUX_PDW),
  .PSTRBW         (PSTRBW),
  .IDXW           (SYSCFG_APB_IDXW),
  .DEFAULT_SUB_IDX(2)
) u_axe_apb_demux (
  .i_clk             (i_ref_clk),
  .i_rst_n           (o_ao_rst_n),
  .i_apb_s_paddr     (SYSCFG_APB_DEMUX_PAW'(i_syscfg_apb4_s_paddr)),
  .i_apb_s_pwdata    (i_syscfg_apb4_s_pwdata),
  .i_apb_s_pwrite    (i_syscfg_apb4_s_pwrite),
  .i_apb_s_psel      (i_syscfg_apb4_s_psel),
  .i_apb_s_penable   (i_syscfg_apb4_s_penable),
  .i_apb_s_pstrb     (i_syscfg_apb4_s_pstrb),
  .i_apb_s_pprot     (i_syscfg_apb4_s_pprot),
  .o_apb_s_pready    (o_syscfg_apb4_s_pready),
  .o_apb_s_prdata    (o_syscfg_apb4_s_prdata),
  .o_apb_s_pslverr   (pslverr_demux),
  .o_apb_m_paddr     (apb_m_paddr),
  .o_apb_m_pwdata    (apb_m_pwdata),
  .o_apb_m_pwrite    (apb_m_pwrite),
  .o_apb_m_psel      (apb_m_psel),
  .o_apb_m_penable   (apb_m_penable),
  .o_apb_m_pstrb     (apb_m_pstrb),
  .o_apb_m_pprot     (apb_m_pprot),
  .i_apb_m_pready    (apb_m_pready),
  .i_apb_m_prdata    (apb_m_prdata),
  .i_apb_m_pslverr   (apb_m_pslverr),
  .i_sub_idx_from_dec(sub_idx_from_dec)
);

// TOOO: apb slave 4 not connected.
always_comb begin
  // reserved_sco_mgmgt_csr = 0x4_0000;
  apb_m_pready [4] = 1'h1;
  apb_m_prdata [4] =   '0;
  apb_m_pslverr[4] = 1'h1;//TODO: tie to error as module not yet implemented.
end

// Slave error
always_comb begin
  o_syscfg_apb4_s_pslverr = pslverr_demux | pslverr_decode;
end

//============================================================================
// APB address decodec
soc_mgmt_sycscfg_apb_decode u_soc_mgmt_sycscfg_apb_decode (
  .i_paddr    ( i_syscfg_apb4_s_paddr ),
  .o_pslv_err ( pslverr_decode        ),
  .o_sub_idx  ( sub_idx_from_dec      )
);

//============================================================================
// NoC PCTL
wire pctl_partition_clk  ;
wire pctl_partition_rst_n;

pctl #(
  .N_FAST_CLKS      (1),
  .N_RESETS         (1),
  .N_MEM_PG         (1),
  .N_FENCES         (1), // TODO(jmartins, should be 0 but no support in PCTL)
  .N_THROTTLE_PINS  (0),
  .CLKRST_MATRIX    (1'b1),
  .PLL_CLK_IS_I_CLK (1'b0),
  .AUTO_RESET_REMOVE(1'b1)
) u_noc_pctl (
  .i_clk          (i_ref_clk     ),
  .i_ao_rst_n     (o_ao_rst_n    ),
  .i_global_rst_n (o_global_rst_n),

  .i_pll_clk      (fast_clk_int      ),
  .o_partition_clk(pctl_partition_clk),

  .i_throttle     (1'b0),

  .o_partition_rst_n(pctl_partition_rst_n),
  .o_ao_rst_sync_n  (/*NC*/),

  // No fences
  .o_noc_async_idle_req (/*NC*/), // There's no fence for NoC
  .i_noc_async_idle_ack (1'h1),
  .i_noc_async_idle_val (1'h1),
  .o_noc_clken          (noc_clk_en ),
  .o_noc_rst_n          (/*NC*/),

  .o_int_shutdown_req(/*NC*/),
  .i_int_shutdown_ack(1'h0  ),

  .i_cfg_apb4_s_paddr   (apb_m_paddr  [2]),
  .i_cfg_apb4_s_pwdata  (apb_m_pwdata [2]),
  .i_cfg_apb4_s_pwrite  (apb_m_pwrite [2]),
  .i_cfg_apb4_s_psel    (apb_m_psel   [2]),
  .i_cfg_apb4_s_penable (apb_m_penable[2]),
  .i_cfg_apb4_s_pstrb   (apb_m_pstrb  [2]),
  .i_cfg_apb4_s_pprot   (apb_m_pprot  [2]),
  .o_cfg_apb4_s_pready  (apb_m_pready [2]),
  .o_cfg_apb4_s_prdata  (apb_m_prdata [2]),
  .o_cfg_apb4_s_pslverr (apb_m_pslverr[2]),

  // No RAMs
  .o_ret(/*NC*/),
  .o_pde(/*NC*/),
  .i_prn(1'b0),

  .i_global_sync_async  (global_sync_async       ),
  .o_global_sync        (o_global_sync           ),

  // No CSRs downstream
  .o_ao_csr_apb_req(/*NC*/), // NOT USED
  .i_ao_csr_apb_rsp('1),

  .i_test_mode     (test_mode)
);

assign o_noc_clk   = pctl_partition_clk;
assign o_noc_rst_n = pctl_partition_rst_n;

  // TODO(jmartins/kluciani, Silver, Drive these properly)
  always_comb o_noc_async_idle_req = 1'b0;

endmodule
