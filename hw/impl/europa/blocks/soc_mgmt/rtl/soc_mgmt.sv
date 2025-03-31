// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

/// Description: Top module for the SoC Management Block.
///
module soc_mgmt
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
  output wire                              o_fast_clk_ext             ,
  output wire                              o_fast_clk_int             ,
  // APU Clock output from PLL-1
  output wire                              o_apu_clk                  ,
  // DDR clock -> direct from the pll2
  output wire                              o_ddr_ref_east_clk         ,

  // Output clocks
  output wire                              o_codec_clk                ,
  output wire                              o_emmc_clk                 ,
  output wire                              o_periph_clk               ,

  // dlm
  output aic_thrtl_t                       o_aic_throttle             ,
  output dlm_clk_thrtl_t                   o_clock_throttle           ,
  input  aic_boost_t                       i_aic_boost_req            ,
  output aic_boost_t                       o_aic_boost_ack            ,
  input  logic                             i_throttle                 ,
  output logic                             o_dlm_irq_warning          ,
  output logic                             o_dlm_irq_critical         ,

  // AXI Connections LP AXI Manager Interface
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

  /// AXI Connections LP AXI Subordinate Interface
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

  // clock gen csr apb
  input  chip_syscfg_addr_t                i_clk_gen_csr_apb_paddr    ,
  input  chip_apb_syscfg_data_t            i_clk_gen_csr_apb_pwdata   ,
  input  logic                             i_clk_gen_csr_apb_pwrite   ,
  input  logic                             i_clk_gen_csr_apb_psel     ,
  input  logic                             i_clk_gen_csr_apb_penable  ,
  input  chip_apb_syscfg_strb_t            i_clk_gen_csr_apb_pstrb    ,
  input  axe_apb_pkg::apb_prot_t           i_clk_gen_csr_apb_pprot    ,
  output logic                             o_clk_gen_csr_apb_pready   ,
  output chip_apb_syscfg_data_t            o_clk_gen_csr_apb_prdata   ,
  output logic                             o_clk_gen_csr_apb_pslverr  ,

  // reset gen csr apb
  input  chip_syscfg_addr_t                i_rst_gen_csr_apb_paddr    ,
  input  chip_apb_syscfg_data_t            i_rst_gen_csr_apb_pwdata   ,
  input  logic                             i_rst_gen_csr_apb_pwrite   ,
  input  logic                             i_rst_gen_csr_apb_psel     ,
  input  logic                             i_rst_gen_csr_apb_penable  ,
  input  chip_apb_syscfg_strb_t            i_rst_gen_csr_apb_pstrb    ,
  input  axe_apb_pkg::apb_prot_t           i_rst_gen_csr_apb_pprot    ,
  output logic                             o_rst_gen_csr_apb_pready   ,
  output chip_apb_syscfg_data_t            o_rst_gen_csr_apb_prdata   ,
  output logic                             o_rst_gen_csr_apb_pslverr  ,

  //////////////////
  // MISC CSR APB //
  //////////////////
  input  chip_syscfg_addr_t                i_apb_misc_csr_paddr,
  input  chip_apb_syscfg_data_t            i_apb_misc_csr_pwdata,
  input  logic                             i_apb_misc_csr_pwrite,
  input  logic                             i_apb_misc_csr_psel,
  input  logic                             i_apb_misc_csr_penable,
  input  chip_apb_syscfg_strb_t            i_apb_misc_csr_pstrb,
  input  axe_apb_pkg::apb_prot_t           i_apb_misc_csr_pprot,
  output logic                             o_apb_misc_csr_pready,
  output chip_apb_syscfg_data_t            o_apb_misc_csr_prdata,
  output logic                             o_apb_misc_csr_pslverr,

  ////////////////////////////
  // MBIST Manager APB3 port//
  ////////////////////////////
  output logic [15:0]                      o_mbist_apb_m_paddr,
  output logic [31:0]                      o_mbist_apb_m_pwdata,
  output logic                             o_mbist_apb_m_pwrite,
  output logic                             o_mbist_apb_m_psel,
  output logic                             o_mbist_apb_m_penable,
  input  logic                             i_mbist_apb_m_pready,
  input  logic [31:0]                      i_mbist_apb_m_prdata,
  input  logic                             i_mbist_apb_m_pslverr,

  // thermal throttle override
  input  logic                             i_thermal_throttle,
  // thermal throttle output to AI cores
  output tms_temp_t                        o_thermal_throttle,
  // thermal warning. From thermal throttle. Overheating warning to boardsystem. Active low.
  output logic                             o_thermal_throttle_warning_n,
  // thermal warning. To partition AI cores
  output tms_temp_t                        o_thermal_warning,
  // thermal shutdown. Will reset the chip via pcb controller. Active low.
  output logic                             o_thermal_shutdown_n,
  //tms interrupt
  output logic                             o_irq_tms_throttle,
  output logic                             o_irq_tms_warning,
  output logic                             o_irq_tms_shutdown,

  /// Interrupts
  // RTC interrupt
  output logic                             o_rtc_irq                  ,
  // Watchdog interrupt
  output logic                             o_wdt_irq                  ,
  // Security interrupt
  output logic                             o_security_irq             ,

  // Boot Mode
  input  logic [2:0]                       i_boot_mode                ,

  /// Jtag Interface
  /// Test Clock
  input  logic                             tck                        ,
  /// (Optional) test reset, active low.
  input  wire                              trst                       ,
  /// JTAG Interface
  input  wire                              tms                        ,
  /// Jtag Debug Unit
  /// jtag serial test data in.
  input  logic                             jtag_tdi_dbg               ,
  /// Serial test data out.
  output logic                             jtag_tdo_dbg               ,
  /// Serial test data out enable.
  output logic                             jtag_tdo_en_dbg            ,
  /// DFT reset override signals
  input  logic                             test_mode                  ,

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

  // Observability signal interface.
  input  obs_in_t                          i_obs_bus                  ,
  output obs_out_t                         o_obs_bus                  ,

  // global sync
  output logic                             o_global_sync              ,

  // OTP Analog signals to IO PAD
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
// Parameters

// number of sync stages
localparam int unsigned STAGE_NUM = 3;

//============================================================================
// Signal declarations
soc_mgmt_clk_gen_csr_reg_pkg::apb_h2d_t mbist_apb_h2d                   ; // TODO: ADI: change package to use debugger APB
soc_mgmt_clk_gen_csr_reg_pkg::apb_d2h_t mbist_apb_d2h                   ; // TODO: ADI: change package to use debugger APB
// CLKGEN APB bus registers' interface
soc_mgmt_reset_gen_csr_reg_pkg::apb_h2d_t rstgen_csr_apb_h2d              ;
soc_mgmt_reset_gen_csr_reg_pkg::apb_d2h_t rstgen_csr_apb_d2h              ;
soc_mgmt_clk_gen_csr_reg_pkg::apb_h2d_t tms_csr_apb_h2d                 ; // TODO: ADI: change package to use debugger APB
soc_mgmt_clk_gen_csr_reg_pkg::apb_d2h_t tms_csr_apb_d2h                 ; // TODO: ADI: change package to use debugger APB

// RoT AHB interface
soc_mgmt_hdata_t                            rot_ahb_s_hrdata    ;
logic                                       rot_ahb_s_hready    ;
soc_mgmt_hresp_t                            rot_ahb_s_hresp     ;
soc_mgmt_haddr_t                            rot_ahb_s_haddr     ;
axe_ahb_pkg::hburst_e                       rot_ahb_s_hburst    ;
axe_ahb_pkg::hsize_e                        rot_ahb_s_hsize     ;
axe_ahb_pkg::htrans_e                       rot_ahb_s_htrans    ;
soc_mgmt_hdata_t                            rot_ahb_s_hwdata    ;
logic                                       rot_ahb_s_hwrite    ;

axe_ahb_pkg::hburst_t                       rot_ahb_s_hburst_bus_fabric  ;
axe_ahb_pkg::hsize_t                        rot_ahb_s_hsize_bus_fabric   ;
axe_ahb_pkg::htrans_t                       rot_ahb_s_htrans_bus_fabric  ;

// RoT APB interface
soc_mgmt_secu_encl_paddr_t                  rot_apb_s_paddr     ;
logic                                       rot_apb_s_pwrite    ;
soc_mgmt_secu_encl_pdata_t                  rot_apb_s_pwdata    ;
logic                                       rot_apb_s_psel      ;
soc_mgmt_pprot_t                            rot_apb_s_pprot     ;
logic                                       rot_apb_s_penable   ;
soc_mgmt_secu_encl_pstrb_t                  rot_apb_s_pstrb     ;
logic                                       rot_apb_s_pslverr   ;
soc_mgmt_secu_encl_pdata_t                  rot_apb_s_prdata    ;
logic                                       rot_apb_s_pready    ;

// PVT clock
wire                                        periph_clk_int                  ;
wire                                        pvt_clk                         ;
// These signals will be output from their respective functional modules.
wire                                        wdt_rst_n                       ;
wire                                        debug_rst_n                     ;
wire                                        dmi_rst_req_n                   ;
wire                                        dmi_rst_n                       ;
wire                                        rot_rst_n                       ;
wire                                        mbist_rst_n                     ;
wire                                        global_rst_ack_n                ;
wire                                        rtc_clk                         ;

logic                                       ao_rst_ack_n                    ;
logic                                       dmi_rst_ack_n                   ;

// interrupts
logic                                       rtc_irq_n                       ;
logic                                       wdt_irq_n                       ;

// Ports for Interface ex_smu_axi_fabric_lt_axi_dbgr_s
// TODO: use types for buses
chip_pkg::chip_axi_addr_t                   lt_axi_dbgr_s_araddr            ;
axi_pkg::axi_burst_t                        lt_axi_dbgr_s_arburst           ;
axi_pkg::axi_cache_t                        lt_axi_dbgr_s_arcache           ;
soc_mgmt_lt_axi_s_id_t                      lt_axi_dbgr_s_arid              ;
axi_pkg::axi_len_t                          lt_axi_dbgr_s_arlen             ;
logic                                       lt_axi_dbgr_s_arlock            ;
axi_pkg::axi_prot_t                         lt_axi_dbgr_s_arprot            ;
axi_pkg::axi_size_t                         lt_axi_dbgr_s_arsize            ;
logic                                       lt_axi_dbgr_s_arvalid           ;
chip_pkg::chip_axi_addr_t                   lt_axi_dbgr_s_awaddr            ;
axi_pkg::axi_burst_t                        lt_axi_dbgr_s_awburst           ;
axi_pkg::axi_cache_t                        lt_axi_dbgr_s_awcache           ;
soc_mgmt_lt_axi_s_id_t                      lt_axi_dbgr_s_awid              ;
axi_pkg::axi_len_t                          lt_axi_dbgr_s_awlen             ;
logic                                       lt_axi_dbgr_s_awlock            ;
axi_pkg::axi_prot_t                         lt_axi_dbgr_s_awprot            ;
axi_pkg::axi_size_t                         lt_axi_dbgr_s_awsize            ;
logic                                       lt_axi_dbgr_s_awvalid           ;
logic                                       lt_axi_dbgr_s_bready            ;
logic                                       lt_axi_dbgr_s_rready            ;
chip_pkg::chip_axi_lt_data_t                lt_axi_dbgr_s_wdata             ;
soc_mgmt_lt_axi_s_id_t                      lt_axi_dbgr_s_wid               ;
logic                                       lt_axi_dbgr_s_wlast             ;
chip_pkg::chip_axi_lt_wstrb_t               lt_axi_dbgr_s_wstrb             ;
logic                                       lt_axi_dbgr_s_wvalid            ;
logic                                       lt_axi_dbgr_s_arready           ;
logic                                       lt_axi_dbgr_s_awready           ;
soc_mgmt_lt_axi_s_id_t                      lt_axi_dbgr_s_bid               ;
axi_pkg::axi_resp_t                         lt_axi_dbgr_s_bresp             ;
logic                                       lt_axi_dbgr_s_bvalid            ;
chip_pkg::chip_axi_lt_data_t                lt_axi_dbgr_s_rdata             ;
soc_mgmt_lt_axi_s_id_t                      lt_axi_dbgr_s_rid               ;
logic                                       lt_axi_dbgr_s_rlast             ;
axi_pkg::axi_resp_t                         lt_axi_dbgr_s_rresp             ;
logic                                       lt_axi_dbgr_s_rvalid            ;
logic                                       lt_axi_dbgr_s_wready            ;

// DMI IF
ahb_haddr_t                                 dmi_haddr                       ;
ahb_htrans_t                                dmi_htrans                      ;
logic                                       dmi_hwrite                      ;
ahb_hsize_t                                 dmi_hsize                       ;
ahb_hburst_t                                dmi_hburst                      ;
logic                                       dmi_hlock                       ;
ahb_hprot_t                                 dmi_hprot                       ;
ahb_hdata_t                                 dmi_hwdata                      ;
logic                                       dmi_hsel                        ;
ahb_hdata_t                                 dmi_hrdata                      ;
logic                                       dmi_hreadyout                   ;
ahb_hresp_t                                 dmi_hresp                       ;

// Debugger active flag. Used to pause the watchdog timer in debug mode.
logic                                       dmactive                        ;

// Triggers - NOT USED
dbg_trigger_t                               xtrigger_halt_in                ;
dbg_trigger_t                               xtrigger_halt_out               ;
dbg_trigger_t                               xtrigger_resume_in              ;
dbg_trigger_t                               xtrigger_resume_out             ;

// AXI DEbug outupts from smu fabric - all outputs and not used.
logic                                       smu_axi_fabric_dbg_active_trans ;
chip_pkg::chip_axi_addr_t                   smu_axi_fabric_dbg_araddr_s0    ;
axi_pkg::axi_burst_t                        smu_axi_fabric_dbg_arburst_s0   ;
axi_pkg::axi_cache_t                        smu_axi_fabric_dbg_arcache_s0   ;
soc_mgmt_lt_axi_s_id_t                      smu_axi_fabric_dbg_arid_s0      ;
axi_pkg::axi_len_t                          smu_axi_fabric_dbg_arlen_s0     ;
logic                                       smu_axi_fabric_dbg_arlock_s0    ;
axi_pkg::axi_prot_t                         smu_axi_fabric_dbg_arprot_s0    ;
logic                                       smu_axi_fabric_dbg_arready_s0   ;
axi_pkg::axi_size_t                         smu_axi_fabric_dbg_arsize_s0    ;
logic                                       smu_axi_fabric_dbg_arvalid_s0   ;
chip_pkg::chip_axi_addr_t                   smu_axi_fabric_dbg_awaddr_s0    ;
axi_pkg::axi_burst_t                        smu_axi_fabric_dbg_awburst_s0   ;
axi_pkg::axi_cache_t                        smu_axi_fabric_dbg_awcache_s0   ;
soc_mgmt_lt_axi_s_id_t                      smu_axi_fabric_dbg_awid_s0      ;
axi_pkg::axi_len_t                          smu_axi_fabric_dbg_awlen_s0     ;
logic                                       smu_axi_fabric_dbg_awlock_s0    ;
axi_pkg::axi_prot_t                         smu_axi_fabric_dbg_awprot_s0    ;
logic                                       smu_axi_fabric_dbg_awready_s0   ;
axi_pkg::axi_size_t                         smu_axi_fabric_dbg_awsize_s0    ;
logic                                       smu_axi_fabric_dbg_awvalid_s0   ;
soc_mgmt_lt_axi_s_id_t                      smu_axi_fabric_dbg_bid_s0       ;
logic                                       smu_axi_fabric_dbg_bready_s0    ;
axi_pkg::axi_resp_t                         smu_axi_fabric_dbg_bresp_s0     ;
logic                                       smu_axi_fabric_dbg_bvalid_s0    ;
chip_pkg::chip_axi_lt_data_t                smu_axi_fabric_dbg_rdata_s0     ;
soc_mgmt_lt_axi_s_id_t                      smu_axi_fabric_dbg_rid_s0       ;
logic                                       smu_axi_fabric_dbg_rlast_s0     ;
logic                                       smu_axi_fabric_dbg_rready_s0    ;
axi_pkg::axi_resp_t                         smu_axi_fabric_dbg_rresp_s0     ;
logic                                       smu_axi_fabric_dbg_rvalid_s0    ;
chip_pkg::chip_axi_lt_data_t                smu_axi_fabric_dbg_wdata_s0     ;
soc_mgmt_lt_axi_s_id_t                      smu_axi_fabric_dbg_wid_s0       ;
logic                                       smu_axi_fabric_dbg_wlast_s0     ;
logic                                       smu_axi_fabric_dbg_wready_s0    ;
chip_pkg::chip_axi_lt_wstrb_t               smu_axi_fabric_dbg_wstrb_s0     ;
logic                                       smu_axi_fabric_dbg_wvalid_s0    ;

axe_tcl_sram_pkg::impl_inp_t                impl_inp;
axe_tcl_sram_pkg::impl_oup_t                impl_oup;

tms_int_t                                   tms_irq                         ;
wire [13:0]                                 pvt_vol_ts                      ;
logic                                       thermal_throttle_warning        ;
logic                                       thermal_shutdown                ;

wire [2:0]                                  test_rst_n;

//==============================================================================
// RTL
// TODO connect DLM interrupts
always_comb begin
  o_dlm_irq_warning  = 1'h0;
  o_dlm_irq_critical = 1'h0;
end

always_comb o_thermal_throttle_warning_n = ~thermal_throttle_warning;
always_comb o_thermal_shutdown_n         = ~thermal_shutdown;

always_comb begin
  o_irq_tms_throttle  = tms_irq[0];
  o_irq_tms_warning   = tms_irq[1];
  o_irq_tms_shutdown  = tms_irq[2];
end

// DW X2P does not drive PPROT or PSTRB. Tie off these inputs on h2d to avoid
// undriven inputs,
always_comb begin

  rot_apb_s_pprot          = PPROT_VAL;
  rot_apb_s_pstrb          = PSTRB_VAL;
  tms_csr_apb_h2d.pprot    = PPROT_VAL;
  tms_csr_apb_h2d.pstrb    = PSTRB_VAL;

end

// Tie off unconnected
// TODO: ADI: Remove when peripherals are added. EXcept for reserved.
always_comb begin
  mbist_apb_d2h.prdata     = 32'hDEAD_000B;
  mbist_apb_d2h.pready     = 1'b1;
  mbist_apb_d2h.pslverr    = 1'b1;
end

  //////////////////////////////////////
  // Soc-Mgmt Clock Gen instantiation //
  //////////////////////////////////////
  soc_mgmt_clk_gen_csr_reg_pkg::apb_h2d_t clkgen_csr_apb_h2d;
  soc_mgmt_clk_gen_csr_reg_pkg::apb_d2h_t clkgen_csr_apb_d2h;

  always_comb clkgen_csr_apb_h2d = soc_mgmt_clk_gen_csr_reg_pkg::apb_h2d_t'{
    psel:    i_clk_gen_csr_apb_psel,
    penable: i_clk_gen_csr_apb_penable,
    pwrite:  i_clk_gen_csr_apb_pwrite,
    paddr:   32'(i_clk_gen_csr_apb_paddr),
    pwdata:  i_clk_gen_csr_apb_pwdata,
    pprot:   i_clk_gen_csr_apb_pprot,
    pstrb:   i_clk_gen_csr_apb_pstrb
  };
  always_comb o_clk_gen_csr_apb_pready  = clkgen_csr_apb_d2h.pready;
  always_comb o_clk_gen_csr_apb_prdata  = clkgen_csr_apb_d2h.prdata;
  always_comb o_clk_gen_csr_apb_pslverr = clkgen_csr_apb_d2h.pslverr;

  soc_mgmt_clk_gen_csr_reg_pkg::soc_mgmt_clk_gen_csr_reg2hw_t clk_gen_csr_reg2hw;
  soc_mgmt_clk_gen_csr_reg_pkg::soc_mgmt_clk_gen_csr_hw2reg_t clk_gen_csr_hw2reg;

  // Control and status registers
  soc_mgmt_clk_gen_csr_reg_top u_soc_mgmt_clk_gen_csr_reg_top (
    .clk_i    (i_ref_clk),
    .rst_ni   (o_ao_rst_n),
    .apb_i    (clkgen_csr_apb_h2d),
    .apb_o    (clkgen_csr_apb_d2h),
    .reg2hw   (clk_gen_csr_reg2hw),
    .hw2reg   (clk_gen_csr_hw2reg),
    .devmode_i(1'b1)
  );

  soc_mgmt_pkg::pll_config_t     csr_pll_config[soc_mgmt_pkg::NUM_PLL];
  soc_mgmt_pkg::mux_div_config_t csr_mux_div_config[soc_mgmt_pkg::NUM_SYS_CLK];
  soc_mgmt_pkg::mux_ddr_config_t csr_mux_ddr_config;

  always_comb csr_pll_config[soc_mgmt_pkg::PLL_SYS_0] = soc_mgmt_pkg::pll_config_t'{
    afc_enb:      clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_0].afc_enb.q,
    bypass:       clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_0].bypass.q,
    extafc:       clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_0].extafc.q,
    feed_en:      clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_0].feed_en.q,
    fout_mask:    clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_0].fout_mask.q,
    fsel:         clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_0].fsel.q,
    icp:          clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_0].icp.q,
    lock_con_dly: clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_0].lock_con_dly.q,
    lock_con_in:  clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_0].lock_con_in.q,
    lock_con_out: clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_0].lock_con_out.q,
    div_main:     clk_gen_csr_reg2hw.pll_config_div_0.main.q,
    div_pre:      clk_gen_csr_reg2hw.pll_config_div_0.pre.q,
    resetb:       clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_0].resetb.q,
    rsel:         clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_0].rsel.q,
    div_scalar:   clk_gen_csr_reg2hw.pll_config_div_0.scalar.q
  };
  always_comb csr_pll_config[soc_mgmt_pkg::PLL_SYS_1] = soc_mgmt_pkg::pll_config_t'{
    afc_enb:      clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_1].afc_enb.q,
    bypass:       clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_1].bypass.q,
    extafc:       clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_1].extafc.q,
    feed_en:      clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_1].feed_en.q,
    fout_mask:    clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_1].fout_mask.q,
    fsel:         clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_1].fsel.q,
    icp:          clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_1].icp.q,
    lock_con_dly: clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_1].lock_con_dly.q,
    lock_con_in:  clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_1].lock_con_in.q,
    lock_con_out: clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_1].lock_con_out.q,
    div_main:     clk_gen_csr_reg2hw.pll_config_div_1.main.q,
    div_pre:      clk_gen_csr_reg2hw.pll_config_div_1.pre.q,
    resetb:       clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_SYS_1].resetb.q,
    rsel:         clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_SYS_1].rsel.q,
    div_scalar:   clk_gen_csr_reg2hw.pll_config_div_1.scalar.q
  };
  always_comb csr_pll_config[soc_mgmt_pkg::PLL_DDR] = soc_mgmt_pkg::pll_config_t'{
    afc_enb:      clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_DDR].afc_enb.q,
    bypass:       clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_DDR].bypass.q,
    extafc:       clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_DDR].extafc.q,
    feed_en:      clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_DDR].feed_en.q,
    fout_mask:    clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_DDR].fout_mask.q,
    fsel:         clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_DDR].fsel.q,
    icp:          clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_DDR].icp.q,
    lock_con_dly: clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_DDR].lock_con_dly.q,
    lock_con_in:  clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_DDR].lock_con_in.q,
    lock_con_out: clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_DDR].lock_con_out.q,
    div_main:     clk_gen_csr_reg2hw.pll_config_div_2.main.q,
    div_pre:      clk_gen_csr_reg2hw.pll_config_div_2.pre.q,
    resetb:       clk_gen_csr_reg2hw.pll_config_ctrl[soc_mgmt_pkg::PLL_DDR].resetb.q,
    rsel:         clk_gen_csr_reg2hw.pll_config_static[soc_mgmt_pkg::PLL_DDR].rsel.q,
    div_scalar:   clk_gen_csr_reg2hw.pll_config_div_2.scalar.q
  };

  //////////////////////////////////
  // DFT Hook into CLK GEN CONFIG //
  //////////////////////////////////
  logic [soc_mgmt_pkg::PllConfigWidth   -1:0] test_pll_config[soc_mgmt_pkg::NUM_PLL];
  logic [soc_mgmt_pkg::MuxDivConfigWidth-1:0] test_mux_div_config[soc_mgmt_pkg::NUM_SYS_CLK];
  logic [soc_mgmt_pkg::MuxDdrConfigWidth-1:0] test_mux_ddr_config;

  always_comb test_pll_config[0] = '0; // TODO(DFT): Hook in here.
  always_comb test_pll_config[1] = '0; // TODO(DFT): Hook in here.
  always_comb test_pll_config[2] = '0; // TODO(DFT): Hook in here.

  always_comb test_mux_div_config[0] = '0; // TODO(DFT): Hook in here.
  always_comb test_mux_div_config[1] = '0; // TODO(DFT): Hook in here.
  always_comb test_mux_div_config[2] = '0; // TODO(DFT): Hook in here.
  always_comb test_mux_div_config[3] = '0; // TODO(DFT): Hook in here.
  always_comb test_mux_div_config[4] = '0; // TODO(DFT): Hook in here.
  always_comb test_mux_div_config[5] = '0; // TODO(DFT): Hook in here.

  always_comb test_mux_ddr_config = '0; // TODO(DFT): Hook in here.

  soc_mgmt_pkg::pll_config_t     pll_config[soc_mgmt_pkg::NUM_PLL];
  soc_mgmt_pkg::pll_status_t     pll_status[soc_mgmt_pkg::NUM_PLL];
  soc_mgmt_pkg::mux_div_config_t mux_div_config[soc_mgmt_pkg::NUM_SYS_CLK];
  soc_mgmt_pkg::mux_div_status_t mux_div_status[soc_mgmt_pkg::NUM_SYS_CLK];
  soc_mgmt_pkg::mux_ddr_config_t mux_ddr_config;
  soc_mgmt_pkg::mux_ddr_status_t mux_ddr_status;

  logic       test_clk_gen_cfg_override;
  always_comb test_clk_gen_cfg_override = 1'b0; // TODO: DFT insertion hook

  for (genvar pll_index = 0; unsigned'(pll_index) < soc_mgmt_pkg::NUM_PLL; pll_index++) begin : gen_pll_csr_conn
    always_comb pll_config[pll_index] = test_clk_gen_cfg_override ? test_pll_config[pll_index] : csr_pll_config[pll_index];

    assign clk_gen_csr_hw2reg.pll_status[pll_index].lock.d     = pll_status[pll_index].lock;
    assign clk_gen_csr_hw2reg.pll_status[pll_index].feed_out.d = pll_status[pll_index].feed_out;
    assign clk_gen_csr_hw2reg.pll_status[pll_index].afc_code.d = pll_status[pll_index].afc_code;
  end

  for (genvar clk_index = 0; unsigned'(clk_index) < soc_mgmt_pkg::NUM_SYS_CLK; clk_index++) begin : gen_sys_clk_csr_conn
    always_comb csr_mux_div_config[clk_index] = soc_mgmt_pkg::mux_div_config_t'{
      updated:    clk_gen_csr_reg2hw.mux_div_config[clk_index].divisor.qe
                | clk_gen_csr_reg2hw.mux_div_config[clk_index].pll_mux_select.qe
                | clk_gen_csr_reg2hw.mux_div_config[clk_index].pll_mux_enable.qe
                | clk_gen_csr_reg2hw.mux_div_config[clk_index].div_mux_select.qe
                | clk_gen_csr_reg2hw.mux_div_config[clk_index].div_mux_enable.qe,
      divisor:    clk_gen_csr_reg2hw.mux_div_config[clk_index].divisor.q,
      pll_mux_select: soc_mgmt_pkg::clk_pll_mux_select_e'(clk_gen_csr_reg2hw.mux_div_config[clk_index].pll_mux_select.q),
      pll_mux_enable: clk_gen_csr_reg2hw.mux_div_config[clk_index].pll_mux_enable.q,
      div_mux_select: soc_mgmt_pkg::clk_div_mux_select_e'(clk_gen_csr_reg2hw.mux_div_config[clk_index].div_mux_select.q),
      div_mux_enable: clk_gen_csr_reg2hw.mux_div_config[clk_index].div_mux_enable.q
    };

    always_comb mux_div_config[clk_index] = test_clk_gen_cfg_override ? test_mux_div_config[clk_index] : csr_mux_div_config[clk_index];

    assign clk_gen_csr_hw2reg.mux_div_status[clk_index].max_divisor.d = soc_mgmt_pkg::ClkMaxIntDivisorWidth'(soc_mgmt_pkg::CLK_MAX_INT_DIVISION);
    assign clk_gen_csr_hw2reg.mux_div_status[clk_index].pll_mux_active.d  = mux_div_status[clk_index].pll_mux_active;
    assign clk_gen_csr_hw2reg.mux_div_status[clk_index].pll_mux_is_on.d   = mux_div_status[clk_index].pll_mux_is_on;
    assign clk_gen_csr_hw2reg.mux_div_status[clk_index].div_mux_active.d  = mux_div_status[clk_index].div_mux_active;
    assign clk_gen_csr_hw2reg.mux_div_status[clk_index].div_mux_is_on.d   = mux_div_status[clk_index].div_mux_is_on;
  end

  always_comb csr_mux_ddr_config = soc_mgmt_pkg::mux_ddr_config_t'{
    mux_select: clk_gen_csr_reg2hw.mux_ddr_config.mux_select.q,
    mux_enable: clk_gen_csr_reg2hw.mux_ddr_config.mux_enable.q
  };

  always_comb mux_ddr_config = test_clk_gen_cfg_override ? test_mux_ddr_config : csr_mux_ddr_config;

  assign clk_gen_csr_hw2reg.mux_ddr_status.mux_is_on.d  = mux_ddr_status.mux_is_on;
  assign clk_gen_csr_hw2reg.mux_ddr_status.mux_active.d = mux_ddr_status.mux_active;

  soc_mgmt_clk_gen #(
    .SyncStages(STAGE_NUM)
  ) u_soc_mgmt_clk_gen (
    .i_clk             (i_ref_clk),
    .i_rst_n           (o_ao_rst_n),
    .i_pll_config      (pll_config),
    .o_pll_status      (pll_status),
    .i_mux_div_config  (mux_div_config),
    .o_mux_div_status  (mux_div_status),
    .i_mux_ddr_config  (mux_ddr_config),
    .o_mux_ddr_status  (mux_ddr_status),
    .o_fast_clk_ext,
    .o_fast_clk_int,
    .o_apu_clk,
    .o_codec_clk,
    .o_emmc_clk,
    .o_periph_clk_ext  (o_periph_clk),
    .o_periph_clk_int  (periph_clk_int),
    .o_pvt_clk         (pvt_clk),
    .o_ddr_ref_east_clk,
    .o_ref_clk         (rtc_clk) // TODO: Is this correct?
  `ifdef POWER_PINS
    ,
    .io_pll_avdd18,
    .io_pll_avss,
    .io_pll_dvdd075,
    .io_pll_dvss
  `endif
  );

  // TODO (Add CLOCK_GEN TDR wrapper.)

  /////////////////////
  // Frequency meter //
  /////////////////////

  // frequency meter width
  localparam int unsigned FREQ_METER_WIDTH = 32;

  // The number of clks for debug and freq_meter is +2 to include the DDR_CLK and REF_CLK
  wire  [soc_mgmt_pkg::NUM_SYS_CLK+1:0]                       freq_meter_obs_clk;
  logic [soc_mgmt_pkg::NUM_SYS_CLK+1:0][FREQ_METER_WIDTH-1:0] freq_meter_obs_freq;

  assign freq_meter_obs_clk = {
    i_ref_clk,
    o_ddr_ref_east_clk,
    pvt_clk,
    periph_clk_int,
    o_emmc_clk,
    o_codec_clk,
    o_apu_clk,
    o_fast_clk_int
  };

  freq_meter #(
    .NumClks   (soc_mgmt_pkg::NUM_SYS_CLK+2),
    .Width     (FREQ_METER_WIDTH),
    .SyncStages(STAGE_NUM)
  ) u_freq_meter (
    .i_clk     (i_ref_clk),
    .i_rst_n   (o_global_rst_n),
    .i_clk_ref (i_ref_clk), // TODO (kluciani, Silver, replace with a divided-down version of i_ref_clk.)
    .test_mode (test_mode),
    .i_obs_clk (freq_meter_obs_clk ),
    .o_obs_freq(freq_meter_obs_freq)
  );

// connect frequency meter to register
for (genvar obs_clk_index = 0; unsigned'(obs_clk_index) < soc_mgmt_pkg::NUM_SYS_CLK+2; obs_clk_index++) begin : gen_clk_freq_csr_conn
  assign clk_gen_csr_hw2reg.freq_counter[obs_clk_index].d = freq_meter_obs_freq[obs_clk_index];
end

// ---------------------------------------
// Soc-Mgmt Reset Gen instantiation
// ---------------------------------------
// TODO: fix these connection
assign mbist_rst_n  = 1'h1;

// TODO (kluciani, Silver, check if DFT needs more granularity on reset generation, only cold reset supported at the moment.)
// AO reset when test_mode is 1.
assign test_rst_n[0] = i_por_rst_n;
// Global + debugger reset when test_mode is 1.
assign test_rst_n[1] = i_por_rst_n;
// Global reset when test_mode is 1.
assign test_rst_n[2] = i_por_rst_n;

soc_mgmt_reset_gen #(
  .NUM_RESETS_RSTGEN (3),
  .STAGE_NUM         (STAGE_NUM)
) u_soc_mgmt_reset_gen (
  .i_clk                   (i_ref_clk),
  .i_por_rst_n             (i_por_rst_n),
  .i_test_rst_n            (test_rst_n),
  .test_mode               (test_mode),
  .i_dft_clk_rst_ctrl      ('0),
  .i_dmi_rst_n             (dmi_rst_req_n),
  .i_rot_rst_n             (rot_rst_n),
  .i_wdt_rst_n             (~wdt_rst_n),
  .i_mbist_rst_n           (mbist_rst_n),
  .i_debug_rst_n           (debug_rst_n),       // From debugger wrapper.
  .i_ao_rst_req_n          (1'b1),
  .o_ao_rst_ack_n          (/* Open */),
  .i_ao_rst_ip_ack         (1'b0),
  .o_ao_rst_ip_n           (o_ao_rst_n),
  .o_dmi_rst_ack_n         (dmi_rst_ack_n),     // NOT connected
  .i_dmi_rst_ip_ack        (1'h0),              // TODO - ADI: check if connection is required.
  .o_dmi_rst_ip_n          (dmi_rst_n),
  .i_global_rst_req_n      (1'h1),
  .o_global_rst_ack_n      (global_rst_ack_n),  // Not connected
  .i_global_rst_ip_ack     (1'h0),              // TODO - ADI: check if connection is required.
  .o_global_rst_ip_n       (o_global_rst_n),
  .i_apb                   (rstgen_csr_apb_h2d),
  .o_apb                   (rstgen_csr_apb_d2h)
);

// TODO: TIE OFF Until rstgen APB is availble
always_comb begin
  rstgen_csr_apb_h2d.paddr   = 32'(i_rst_gen_csr_apb_paddr);
  rstgen_csr_apb_h2d.pwrite  = i_rst_gen_csr_apb_pwrite       ;
  rstgen_csr_apb_h2d.pwdata  = i_rst_gen_csr_apb_pwdata       ;
  rstgen_csr_apb_h2d.psel    = i_rst_gen_csr_apb_psel         ;
  rstgen_csr_apb_h2d.penable = i_rst_gen_csr_apb_penable      ;
  rstgen_csr_apb_h2d.pprot   = i_rst_gen_csr_apb_pprot        ;
  rstgen_csr_apb_h2d.pstrb   = i_rst_gen_csr_apb_pstrb        ;

  // outputs
  o_rst_gen_csr_apb_pready   = rstgen_csr_apb_d2h.pready      ;
  o_rst_gen_csr_apb_prdata   = rstgen_csr_apb_d2h.prdata      ;
  o_rst_gen_csr_apb_pslverr  = rstgen_csr_apb_d2h.pslverr     ;
end

  // ---------------------------------------
  // Soc-Mgmt eFUSE Wrapper instantiation
  // ---------------------------------------
  soc_mgmt_efuse_wrapper u_soc_mgmt_efuse_wrapper (
    .i_clk          ( i_ref_clk      ),
    .i_rst_n        ( i_por_rst_n    ),
    // Efuse interface analog signals.
    .io_efuse_vqps  ( io_efuse_vqps  ),
    .io_efuse_vddwl ( io_efuse_vddwl )

  );

  //============================================================================
  // TMS
  tms #(
    .NB_EXT_TEMP_SENSE ( TMS_NB_EXT_TSENSE ),
    .NB_INT_TEMP_SENSE ( TMS_NB_INT_TSENSE ),
    .PAW               ( TMS_PAW           ),
    .PDW               ( TMS_PDW           ),
    .PSTRBW            ( PSTRBW            ),
    .PPROTW            ( PPROTW            ),
    .PVT_TW            ( TMS_TW            ),
    .PVT_PROBEW        ( TMS_PROBEW        ),
    .PVT_VOLW          ( TMS_VOLW          )
  ) u_tms (
    .i_clk                      ( periph_clk_int                     ),
    .i_rst_n                    ( o_global_rst_n                     ),
    .i_ao_rst_n                 ( o_ao_rst_n                         ),
    .i_pvt_clk                  ( pvt_clk                            ),
    .i_pvt_rst_n                ( o_global_rst_n                     ),
    .i_cfg_apb4_s_paddr         ( tms_csr_apb_h2d.paddr[TMS_PAW-1:0] ),
    .i_cfg_apb4_s_pwdata        ( tms_csr_apb_h2d.pwdata             ),
    .i_cfg_apb4_s_pwrite        ( tms_csr_apb_h2d.pwrite             ),
    .i_cfg_apb4_s_psel          ( tms_csr_apb_h2d.psel               ),
    .i_cfg_apb4_s_penable       ( tms_csr_apb_h2d.penable            ),
    .i_cfg_apb4_s_pstrb         ( tms_csr_apb_h2d.pstrb              ),
    .i_cfg_apb4_s_pprot         ( tms_csr_apb_h2d.pprot              ),
    .o_cfg_apb4_s_pready        ( tms_csr_apb_d2h.pready             ),
    .o_cfg_apb4_s_prdata        ( tms_csr_apb_d2h.prdata             ),
    .o_cfg_apb4_s_pslverr       ( tms_csr_apb_d2h.pslverr            ),
    .i_jtag_tck                 ( tck                                ),
    .i_jtag_rst_n               ( trst                               ),
    .i_thermal_throttle         ( i_thermal_throttle                 ),
    .o_thermal_throttle         ( o_thermal_throttle                 ),
    .o_thermal_throttle_warning ( thermal_throttle_warning           ),
    .o_thermal_warning          ( o_thermal_warning                  ),
    .o_thermal_shutdown         ( thermal_shutdown                   ),
    .o_irq                      ( tms_irq                            ),
    .io_pvt_ibias_ts            ( io_pvt_ibias_ts                    ),
    .io_pvt_vsense_ts           ( io_pvt_vsense_ts                   ),
    .io_pvt_test_out_ts         ( io_pvt_test_out_ts                 ),
    .io_pvt_vol_ts              ( pvt_vol_ts                         )
`ifdef POWER_PINS
                                                                      ,
    .io_pvt_dvdd075a_ts         (  io_pvt_dvdd075a_ts                ),
    .io_pvt_dvss0a_ts           (  io_pvt_dvss0a_ts                  ),
    .io_pvt_avdd18a_ts          (  io_pvt_avdd18a_ts                 ),
    .io_pvt_avss0a_ts           (  io_pvt_avss0a_ts                  ),
    .io_pvt_avss_gd             (  io_pvt_avss_gd                    )
`endif
);

// TODO (kluciani, Silver, pvt_vol_ts[0] shall be connected to VDD_CORE by PD, see issue #2381)
assign pvt_vol_ts = '0;

//============================================================================
// Secure Enclave
soc_mgmt_secu_enclave
  u_soc_mgmt_secu_enclave (
  .i_clk                      ( periph_clk_int                                           ),
  .i_rst_n                    ( o_global_rst_n                                           ),
  .i_otp_wrapper_clk          ( i_ref_clk                                                ),
  .i_otp_wrapper_rst_n        ( i_por_rst_n                                              ),
  .i_ao_rst_n                 ( i_por_rst_n                                              ),
  .o_kse3_jtag_rst_n          ( rot_rst_n                                                ),
  .tcki                       ( tck                                                      ),
  .trsti                      ( trst                                                     ),
  .o_ahb_s_hrdata             ( rot_ahb_s_hrdata                                         ),
  .o_ahb_s_hready             ( rot_ahb_s_hready                                         ),
  .o_ahb_s_hresp              ( rot_ahb_s_hresp[0]                                       ),
  .i_ahb_s_haddr              ( rot_ahb_s_haddr[kudelski_kse3_pkg::KSE3_AHB_ADDR_W-1:0]  ), // TODO(kluciani, Should we make any check on MSbits?)
  .i_ahb_s_hburst             ( rot_ahb_s_hburst                                         ),
  .i_ahb_s_hsize              ( rot_ahb_s_hsize                                          ),
  .i_ahb_s_htrans             ( rot_ahb_s_htrans                                         ),
  .i_ahb_s_hwdata             ( rot_ahb_s_hwdata                                         ),
  .i_ahb_s_hwrite             ( rot_ahb_s_hwrite                                         ),
  .i_apb_s_paddr              ( rot_apb_s_paddr                                          ),
  .i_apb_s_pwrite             ( rot_apb_s_pwrite                                         ),
  .i_apb_s_pwdata             ( rot_apb_s_pwdata                                         ),
  .i_apb_s_psel               ( rot_apb_s_psel                                           ),
  .i_apb_s_pprot              ( rot_apb_s_pprot                                          ),
  .i_apb_s_penable            ( rot_apb_s_penable                                        ),
  .i_apb_s_pstrb              ( rot_apb_s_pstrb                                          ),
  .o_apb_s_pslverr            ( rot_apb_s_pslverr                                        ),
  .o_apb_s_prdata             ( rot_apb_s_prdata                                         ),
  .o_apb_s_pready             ( rot_apb_s_pready                                         ),
  .i_dft_scan_test_mode       ( test_mode                                                ),
  .i_dft_otp_test_mode        ( i_dft_otp_test_mode                                      ),
  .i_dft_otp_tst_a            ( i_dft_otp_tst_a                                          ),
  .i_dft_otp_tst_din          ( i_dft_otp_tst_din                                        ),
  .i_dft_otp_tst_readen       ( i_dft_otp_tst_readen                                     ),
  .i_dft_otp_tst_ceb          ( i_dft_otp_tst_ceb                                        ),
  .i_dft_otp_tst_cle          ( i_dft_otp_tst_cle                                        ),
  .i_dft_otp_tst_dle          ( i_dft_otp_tst_dle                                        ),
  .i_dft_otp_tst_web          ( i_dft_otp_tst_web                                        ),
  .i_dft_otp_tst_rstb         ( i_dft_otp_tst_rstb                                       ),
  .i_dft_otp_tst_cpumpen      ( i_dft_otp_tst_cpumpen                                    ),
  .i_dft_otp_tst_pgmen        ( i_dft_otp_tst_pgmen                                      ),
  .i_dft_otp_tst_seltm        ( i_dft_otp_tst_seltm                                      ),
  .i_dft_otp_tst_vddrdy       ( i_dft_otp_tst_vddrdy                                     ),
  .i_dft_otp_tst_clken        ( i_dft_otp_tst_clken                                      ),
  .o_dft_otp_tst_d            ( o_dft_otp_tst_d                                          ),
  .o_dft_otp_tst_lock         ( o_dft_otp_tst_lock                                       ),
  .o_kse3_interrupt           ( o_security_irq                                           ),
  .o_dbg_taps_en              ( o_dbg_taps_en                                            ),
  .o_otp_tap_en               ( o_otp_tap_en                                             ),
  .io_otp_vtdo                ( io_otp_vtdo                                              ),
  .io_otp_vrefm               ( io_otp_vrefm                                             ),
  .io_otp_vpp                 ( io_otp_vpp                                               ),
  .i_impl_inp                 ( impl_inp                                                 ),
  .o_impl_oup                 ( impl_oup                                                 )
);

// KSE3 subordinate is AHB-lite, only possible response is OK (0b00) or ERROR (0b01)
// TODO: Can we generate the AHB manager without HRESP[1] ?
always_comb rot_ahb_s_hresp[1] = 1'b0;

always_comb rot_ahb_s_hburst  = axe_ahb_pkg::hburst_e'(rot_ahb_s_hburst_bus_fabric);
always_comb rot_ahb_s_hsize   = axe_ahb_pkg::hsize_e'(rot_ahb_s_hsize_bus_fabric);
always_comb rot_ahb_s_htrans  = axe_ahb_pkg::htrans_e'(rot_ahb_s_htrans_bus_fabric);

//============================================================================--
// Debugger wrapper
nds_pldm_wrapper #(
  .ADDR_WIDTH                ( chip_pkg::CHIP_AXI_ADDR_W                         ),
  .DATA_WIDTH                ( chip_pkg::CHIP_AXI_LT_DATA_W                      ),
  .SYS_ADDR_WIDTH            ( chip_pkg::CHIP_AXI_ADDR_W                         ),
  .SYS_DATA_WIDTH            ( chip_pkg::CHIP_AXI_LT_DATA_W                      ),
  .NHART                     ( NHART                                             ),
  .DTM_ADDR_WIDTH            ( DTM_ADDR_WIDTH                                    ),
  .RV_ID_WIDTH               ( SOC_MGMT_LT_AXI_M_ID_W                            ),
  .SYS_ID_WIDTH              ( SOC_MGMT_LT_AXI_M_ID_W                            ),
  .SYNC_STAGE                ( 2                                                 ),
  .SERIAL_COUNT              ( SERIAL_COUNT                                      ),
  .SERIAL0                   ( SERIAL0                                           ),
  .PROGBUF_SIZE              ( PROGBUF_SIZE                                      ),
  .HALTGROUP_COUNT           ( HALTGROUP_COUNT                                   ),
  .DMXTRIGGER_COUNT          ( DMXTRIGGER_COUNT                                  ),
  .NEXTDM_ADDR               ( NEXTDM_ADDR                                       ),
  .SYSTEM_BUS_ACCESS_SUPPORT ( SYSTEM_BUS_ACCESS_SUPPORT                         ),
  .RESUMEGROUP_SUPPORT       ( (DMXTRIGGER_COUNT > 0) ? 1'b1 : 1'b0              ),
  .HASEL_SUPPORT             ( HASEL_SUPPORT                                     ),
  .DMXTRIGGER_MSB            ( (DMXTRIGGER_COUNT > 0) ? DMXTRIGGER_COUNT - 1 : 0 )
) u_nds_pldm_wrapper (
  .i_clk                     ( periph_clk_int                ),
  .o_ndmreset                ( debug_rst_n                   ),
  .i_dmi_resetn              ( dmi_rst_n                     ),
  .i_bus_resetn              ( o_ao_rst_n                    ),

  .o_debugint                ( o_debugint                    ),
  .o_resethaltreq            ( o_resethaltreq                ),
  .o_dmactive                ( dmactive                      ),
  .i_hart_nonexistent        ( {NHART{1'b0}}                 ),
  .i_hart_unavail            ( i_hart_unavail                ),
  .i_hart_under_reset        ( i_hart_under_reset            ),

  // RV AXI
  .i_rv_araddr               ( lt_axi_dbgr_s_araddr          ),
  .i_rv_arburst              ( lt_axi_dbgr_s_arburst         ),
  .i_rv_arcache              ( lt_axi_dbgr_s_arcache         ),
  .i_rv_arid                 ( lt_axi_dbgr_s_arid            ),
  .i_rv_arlen                ( lt_axi_dbgr_s_arlen           ),
  .i_rv_arlock               ( lt_axi_dbgr_s_arlock          ),
  .i_rv_arprot               ( lt_axi_dbgr_s_arprot          ),
  .i_rv_arsize               ( lt_axi_dbgr_s_arsize          ),
  .i_rv_arvalid              ( lt_axi_dbgr_s_arvalid         ),
  .i_rv_awaddr               ( lt_axi_dbgr_s_awaddr          ),
  .i_rv_awburst              ( lt_axi_dbgr_s_awburst         ),
  .i_rv_awcache              ( lt_axi_dbgr_s_awcache         ),
  .i_rv_awid                 ( lt_axi_dbgr_s_awid            ),
  .i_rv_awlen                ( lt_axi_dbgr_s_awlen           ),
  .i_rv_awlock               ( lt_axi_dbgr_s_awlock          ),
  .i_rv_awprot               ( lt_axi_dbgr_s_awprot          ),
  .i_rv_awsize               ( lt_axi_dbgr_s_awsize          ),
  .i_rv_awvalid              ( lt_axi_dbgr_s_awvalid         ),
  .i_rv_bready               ( lt_axi_dbgr_s_bready          ),
  .i_rv_rready               ( lt_axi_dbgr_s_rready          ),
  .i_rv_wdata                ( lt_axi_dbgr_s_wdata           ),
  .i_rv_wlast                ( lt_axi_dbgr_s_wlast           ),
  .i_rv_wstrb                ( lt_axi_dbgr_s_wstrb           ),
  .i_rv_wvalid               ( lt_axi_dbgr_s_wvalid          ),
  .o_rv_arready              ( lt_axi_dbgr_s_arready         ),
  .o_rv_awready              ( lt_axi_dbgr_s_awready         ),
  .o_rv_bid                  ( lt_axi_dbgr_s_bid             ),
  .o_rv_bresp                ( lt_axi_dbgr_s_bresp           ),
  .o_rv_bvalid               ( lt_axi_dbgr_s_bvalid          ),
  .o_rv_rdata                ( lt_axi_dbgr_s_rdata           ),
  .o_rv_rid                  ( lt_axi_dbgr_s_rid             ),
  .o_rv_rlast                ( lt_axi_dbgr_s_rlast           ),
  .o_rv_rresp                ( lt_axi_dbgr_s_rresp           ),
  .o_rv_rvalid               ( lt_axi_dbgr_s_rvalid          ),
  .o_rv_wready               ( lt_axi_dbgr_s_wready          ),

  // SYS AXI IF
  .i_sys_arready             ( i_lt_axi_m_arready            ),
  .i_sys_awready             ( i_lt_axi_m_awready            ),
  .i_sys_bid                 ( i_lt_axi_m_bid                ),
  .i_sys_bresp               ( i_lt_axi_m_bresp              ),
  .i_sys_bvalid              ( i_lt_axi_m_bvalid             ),
  .i_sys_rdata               ( i_lt_axi_m_rdata              ),
  .i_sys_rid                 ( i_lt_axi_m_rid                ),
  .i_sys_rlast               ( i_lt_axi_m_rlast              ),
  .i_sys_rresp               ( i_lt_axi_m_rresp              ),
  .i_sys_rvalid              ( i_lt_axi_m_rvalid             ),
  .i_sys_wready              ( i_lt_axi_m_wready             ),
  .o_sys_araddr              ( o_lt_axi_m_araddr             ),
  .o_sys_arburst             ( o_lt_axi_m_arburst            ),
  .o_sys_arcache             ( o_lt_axi_m_arcache            ),
  .o_sys_arid                ( o_lt_axi_m_arid               ),
  .o_sys_arlen               ( o_lt_axi_m_arlen              ),
  .o_sys_arlock              ( o_lt_axi_m_arlock             ),
  .o_sys_arprot              ( o_lt_axi_m_arprot             ),
  .o_sys_arsize              ( o_lt_axi_m_arsize             ),
  .o_sys_arvalid             ( o_lt_axi_m_arvalid            ),
  .o_sys_awaddr              ( o_lt_axi_m_awaddr             ),
  .o_sys_awburst             ( o_lt_axi_m_awburst            ),
  .o_sys_awcache             ( o_lt_axi_m_awcache            ),
  .o_sys_awid                ( o_lt_axi_m_awid               ),
  .o_sys_awlen               ( o_lt_axi_m_awlen              ),
  .o_sys_awsize              ( o_lt_axi_m_awsize             ),
  .o_sys_awlock              ( o_lt_axi_m_awlock             ),
  .o_sys_awprot              ( o_lt_axi_m_awprot             ),
  .o_sys_awvalid             ( o_lt_axi_m_awvalid            ),
  .o_sys_bready              ( o_lt_axi_m_bready             ),
  .o_sys_rready              ( o_lt_axi_m_rready             ),
  .o_sys_wdata               ( o_lt_axi_m_wdata              ),
  .o_sys_wlast               ( o_lt_axi_m_wlast              ),
  .o_sys_wstrb               ( o_lt_axi_m_wstrb              ),
  .o_sys_wvalid              ( o_lt_axi_m_wvalid             ),

  // DMI IF
  .i_dmi_haddr               ( dmi_haddr[DTM_ADDR_WIDTH-1:0] ),
  .i_dmi_htrans              ( dmi_htrans                    ),
  .i_dmi_hwrite              ( dmi_hwrite                    ),
  .i_dmi_hsize               ( dmi_hsize                     ),
  .i_dmi_hburst              ( dmi_hburst                    ),
  .i_dmi_hprot               ( dmi_hprot                     ),
  .i_dmi_hwdata              ( dmi_hwdata                    ),
  .i_dmi_hsel                ( dmi_hsel                      ),
  .i_dmi_hready              ( dmi_hreadyout                 ),
  .o_dmi_hrdata              ( dmi_hrdata                    ),
  .o_dmi_hreadyout           ( dmi_hreadyout                 ),
  .o_dmi_hresp               ( dmi_hresp                     ),

  // Triggers
  .i_xtrigger_halt_in        ( xtrigger_halt_in              ), // NOT USED
  .o_xtrigger_halt_out       ( xtrigger_halt_out             ), // NOT USED
  .i_xtrigger_resume_in      ( xtrigger_resume_in            ), // NOT USED
  .o_xtrigger_resume_out     ( xtrigger_resume_out           )  // NOT USED
);

// JTAG Debug Transport Module
ncejdtm200 #(
  .DEBUG_INTERFACE  ("jtag"),
  .SYNC_STAGE       (2),
  .DMI_ADDR_BITS    (DTM_ADDR_WIDTH)
) u_ncejdtm200 (
  .dbg_wakeup_req   (),
  .tms_out_en       (/* unused in JTAG mode */),
  .test_mode        (test_mode),
  .pwr_rst_n        (o_ao_rst_n),
  .tck              (tck),
  .tms              (tms),
  .tdi              (jtag_tdi_dbg),
  .tdo              (jtag_tdo_dbg),
  .tdo_out_en       (),
  .dmi_hresetn      (dmi_rst_req_n),
  .dmi_hclk         (periph_clk_int),
  .dmi_hsel         (dmi_hsel),
  .dmi_htrans       (dmi_htrans),
  .dmi_haddr        (dmi_haddr),
  .dmi_hsize        (dmi_hsize),
  .dmi_hburst       (dmi_hburst),
  .dmi_hprot        (dmi_hprot),
  .dmi_hwdata       (dmi_hwdata),
  .dmi_hwrite       (dmi_hwrite),
  .dmi_hrdata       (dmi_hrdata),
  .dmi_hready       (dmi_hreadyout),
  .dmi_hresp        (dmi_hresp[0])
);

// Tie off xtrgger inputs. I/f not used
always_comb begin
  xtrigger_halt_in    = 1'h0;
  xtrigger_resume_in  = 1'h0;
end

//============================================================================--
// SMU fabric
soc_mgmt_bus_fabric_wrapper u_soc_mgmt_bus_fabric_wrapper (
  .i_aclk                                      ( periph_clk_int                  ),
  .i_aresetn                                   ( o_global_rst_n                  ),
  .i_pclk                                      ( periph_clk_int                  ),
  .i_presetn                                   ( o_global_rst_n                  ),
  .i_hclk                                      ( periph_clk_int                  ),
  .i_hresetn                                   ( o_global_rst_n                  ),
  .i_mbist_prdata                              ( mbist_apb_d2h.prdata            ),
  .i_apb_mbist_pready                          ( mbist_apb_d2h.pready            ),
  .i_apb_mbist_pslverr                         ( mbist_apb_d2h.pslverr           ),
  .o_mbist_paddr                               ( mbist_apb_h2d.paddr             ),
  .o_mbist_penable                             ( mbist_apb_h2d.penable           ),
  .o_mbist_psel                                ( mbist_apb_h2d.psel              ),
  .o_mbist_pwdata                              ( mbist_apb_h2d.pwdata            ),
  .o_mbist_pwrite                              ( mbist_apb_h2d.pwrite            ),
  .i_apb_tms_prdata                            ( tms_csr_apb_d2h.prdata          ),
  .i_apb_tms_pready                            ( tms_csr_apb_d2h.pready          ),
  .i_apb_tms_pslverr                           ( tms_csr_apb_d2h.pslverr         ),
  .o_apb_tms_csr_paddr                         ( tms_csr_apb_h2d.paddr           ),
  .o_apb_tms_csr_penable                       ( tms_csr_apb_h2d.penable         ),
  .o_apb_tms_csr_psel                          ( tms_csr_apb_h2d.psel            ),
  .o_apb_tms_csr_pwdata                        ( tms_csr_apb_h2d.pwdata          ),
  .o_apb_tms_csr_pwrite                        ( tms_csr_apb_h2d.pwrite          ),
  // OTP and ROT AO APB Interface
  .i_apb_rot_ao_and_otp_prdata                 ( rot_apb_s_prdata                ),
  .i_apb_rot_ao_and_otp_pready                 ( rot_apb_s_pready                ),
  .i_apb_rot_ao_and_otp_pslverr                ( rot_apb_s_pslverr               ),
  .o_apb_rot_ao_and_otp_paddr                  ( rot_apb_s_paddr                 ),
  .o_apb_rot_ao_and_otp_penable                ( rot_apb_s_penable               ),
  .o_apb_rot_ao_and_otp_psel                   ( rot_apb_s_psel                  ),
  .o_apb_rot_ao_and_otp_pwdata                 ( rot_apb_s_pwdata                ),
  .o_apb_rot_ao_and_otp_pwrite                 ( rot_apb_s_pwrite                ),
  // Ports for Interface ex_o_rtc_Intr,
  .o_ex_o_rtc_intr_irq                         ( rtc_irq_n                       ),
  // Ports for Interface ex_o_wdt_Intr,
  .o_ex_o_wdt_intr_irq                         ( wdt_irq_n                       ),
  // LT AXI to DEBUGGER AXI RV
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_arready   ( lt_axi_dbgr_s_arready           ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_awready   ( lt_axi_dbgr_s_awready           ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_bid       ( lt_axi_dbgr_s_bid               ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_bresp     ( lt_axi_dbgr_s_bresp             ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_bvalid    ( lt_axi_dbgr_s_bvalid            ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_rdata     ( lt_axi_dbgr_s_rdata             ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_rid       ( lt_axi_dbgr_s_rid               ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_rlast     ( lt_axi_dbgr_s_rlast             ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_rresp     ( lt_axi_dbgr_s_rresp             ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_rvalid    ( lt_axi_dbgr_s_rvalid            ),
  .i_ex_smu_axi_fabric_lt_axi_dbgr_m_wready    ( lt_axi_dbgr_s_wready            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_araddr    ( lt_axi_dbgr_s_araddr            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_arburst   ( lt_axi_dbgr_s_arburst           ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_arcache   ( lt_axi_dbgr_s_arcache           ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_arid      ( lt_axi_dbgr_s_arid              ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_arlen     ( lt_axi_dbgr_s_arlen             ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_arlock    ( lt_axi_dbgr_s_arlock            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_arprot    ( lt_axi_dbgr_s_arprot            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_arsize    ( lt_axi_dbgr_s_arsize            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_arvalid   ( lt_axi_dbgr_s_arvalid           ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_awaddr    ( lt_axi_dbgr_s_awaddr            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_awburst   ( lt_axi_dbgr_s_awburst           ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_awcache   ( lt_axi_dbgr_s_awcache           ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_awid      ( lt_axi_dbgr_s_awid              ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_awlen     ( lt_axi_dbgr_s_awlen             ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_awlock    ( lt_axi_dbgr_s_awlock            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_awprot    ( lt_axi_dbgr_s_awprot            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_awsize    ( lt_axi_dbgr_s_awsize            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_awvalid   ( lt_axi_dbgr_s_awvalid           ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_bready    ( lt_axi_dbgr_s_bready            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_rready    ( lt_axi_dbgr_s_rready            ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_wdata     ( lt_axi_dbgr_s_wdata             ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_wlast     ( lt_axi_dbgr_s_wlast             ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_wstrb     ( lt_axi_dbgr_s_wstrb             ),
  .o_ex_smu_axi_fabric_lt_axi_dbgr_m_wvalid    ( lt_axi_dbgr_s_wvalid            ),
  // AHB For KSE
  .i_ext_axi_x2h_m_kse_hrdata                  ( rot_ahb_s_hrdata                ),
  .i_ext_axi_x2h_m_kse_hready                  ( rot_ahb_s_hready                ),
  .i_ext_axi_x2h_m_kse_hresp                   ( rot_ahb_s_hresp                 ),
  .o_ext_axi_x2h_m_kse_haddr                   ( rot_ahb_s_haddr                 ),
  .o_ext_axi_x2h_m_kse_hburst                  ( rot_ahb_s_hburst_bus_fabric     ),
  .o_ext_axi_x2h_m_kse_hlock                   ( /*NOT SUPPORTED BY KSE3*/       ),
  .o_ext_axi_x2h_m_kse_hprot                   ( /*NOT SUPPORTED BY KSE3*/       ),
  .o_ext_axi_x2h_m_kse_hsize                   ( rot_ahb_s_hsize_bus_fabric      ),
  .o_ext_axi_x2h_m_kse_htrans                  ( rot_ahb_s_htrans_bus_fabric     ),
  .o_ext_axi_x2h_m_kse_hwdata                  ( rot_ahb_s_hwdata                ),
  .o_ext_axi_x2h_m_kse_hwrite                  ( rot_ahb_s_hwrite                ),
  // LT AXI Slave
  .i_ext_smu_fabric_lt_axi_s_araddr            ( i_lt_axi_s_araddr               ),
  .i_ext_smu_fabric_lt_axi_s_arburst           ( i_lt_axi_s_arburst              ),
  .i_ext_smu_fabric_lt_axi_s_arcache           ( i_lt_axi_s_arcache              ),
  .i_ext_smu_fabric_lt_axi_s_arid              ( i_lt_axi_s_arid                 ),
  .i_ext_smu_fabric_lt_axi_s_arlen             ( i_lt_axi_s_arlen                ),
  .i_ext_smu_fabric_lt_axi_s_arlock            ( i_lt_axi_s_arlock               ),
  .i_ext_smu_fabric_lt_axi_s_arprot            ( i_lt_axi_s_arprot               ),
  .i_ext_smu_fabric_lt_axi_s_arsize            ( i_lt_axi_s_arsize               ),
  .i_ext_smu_fabric_lt_axi_s_arvalid           ( i_lt_axi_s_arvalid              ),
  .i_ext_smu_fabric_lt_axi_s_awaddr            ( i_lt_axi_s_awaddr               ),
  .i_ext_smu_fabric_lt_axi_s_awburst           ( i_lt_axi_s_awburst              ),
  .i_ext_smu_fabric_lt_axi_s_awcache           ( i_lt_axi_s_awcache              ),
  .i_ext_smu_fabric_lt_axi_s_awid              ( i_lt_axi_s_awid                 ),
  .i_ext_smu_fabric_lt_axi_s_awlen             ( i_lt_axi_s_awlen                ),
  .i_ext_smu_fabric_lt_axi_s_awlock            ( i_lt_axi_s_awlock               ),
  .i_ext_smu_fabric_lt_axi_s_awprot            ( i_lt_axi_s_awprot               ),
  .i_ext_smu_fabric_lt_axi_s_awsize            ( i_lt_axi_s_awsize               ),
  .i_ext_smu_fabric_lt_axi_s_awvalid           ( i_lt_axi_s_awvalid              ),
  .i_ext_smu_fabric_lt_axi_s_bready            ( i_lt_axi_s_bready               ),
  .i_ext_smu_fabric_lt_axi_s_rready            ( i_lt_axi_s_rready               ),
  .i_ext_smu_fabric_lt_axi_s_wdata             ( i_lt_axi_s_wdata                ),
  .i_ext_smu_fabric_lt_axi_s_wlast             ( i_lt_axi_s_wlast                ),
  .i_ext_smu_fabric_lt_axi_s_wstrb             ( i_lt_axi_s_wstrb                ),
  .i_ext_smu_fabric_lt_axi_s_wvalid            ( i_lt_axi_s_wvalid               ),
  .o_ext_smu_fabric_lt_axi_s_arready           ( o_lt_axi_s_arready              ),
  .o_ext_smu_fabric_lt_axi_s_awready           ( o_lt_axi_s_awready              ),
  .o_ext_smu_fabric_lt_axi_s_bid               ( o_lt_axi_s_bid                  ),
  .o_ext_smu_fabric_lt_axi_s_bresp             ( o_lt_axi_s_bresp                ),
  .o_ext_smu_fabric_lt_axi_s_bvalid            ( o_lt_axi_s_bvalid               ),
  .o_ext_smu_fabric_lt_axi_s_rdata             ( o_lt_axi_s_rdata                ),
  .o_ext_smu_fabric_lt_axi_s_rid               ( o_lt_axi_s_rid                  ),
  .o_ext_smu_fabric_lt_axi_s_rlast             ( o_lt_axi_s_rlast                ),
  .o_ext_smu_fabric_lt_axi_s_rresp             ( o_lt_axi_s_rresp                ),
  .o_ext_smu_fabric_lt_axi_s_rvalid            ( o_lt_axi_s_rvalid               ),
  .o_ext_smu_fabric_lt_axi_s_wready            ( o_lt_axi_s_wready               ),
  .i_rtc_rtc_clk                               ( rtc_clk                         ),
  .i_rtc_rtc_fpclk                             ( o_fast_clk_int                  ),
  .i_rtc_rtc_rst_n                             ( o_ao_rst_n                      ),
  .i_rtc_scan_mode                             ( 1'h0                            ),
  .i_wdt_scan_mode                             ( 1'h0                            ),
  .i_wdt_speed_up                              ( 1'h0                            ),
  .i_wdt_pause                                 ( dmactive                        ),
  .o_wdt_wdt_sys_rst                           ( wdt_rst_n                       ),
  // AXI Debig IF - NOT USED
  .o_smu_axi_fabric_dbg_active_trans           ( smu_axi_fabric_dbg_active_trans ),
  .o_smu_axi_fabric_dbg_araddr_s0              ( smu_axi_fabric_dbg_araddr_s0    ),
  .o_smu_axi_fabric_dbg_arburst_s0             ( smu_axi_fabric_dbg_arburst_s0   ),
  .o_smu_axi_fabric_dbg_arcache_s0             ( smu_axi_fabric_dbg_arcache_s0   ),
  .o_smu_axi_fabric_dbg_arid_s0                ( smu_axi_fabric_dbg_arid_s0      ),
  .o_smu_axi_fabric_dbg_arlen_s0               ( smu_axi_fabric_dbg_arlen_s0     ),
  .o_smu_axi_fabric_dbg_arlock_s0              ( smu_axi_fabric_dbg_arlock_s0    ),
  .o_smu_axi_fabric_dbg_arprot_s0              ( smu_axi_fabric_dbg_arprot_s0    ),
  .o_smu_axi_fabric_dbg_arready_s0             ( smu_axi_fabric_dbg_arready_s0   ),
  .o_smu_axi_fabric_dbg_arsize_s0              ( smu_axi_fabric_dbg_arsize_s0    ),
  .o_smu_axi_fabric_dbg_arvalid_s0             ( smu_axi_fabric_dbg_arvalid_s0   ),
  .o_smu_axi_fabric_dbg_awaddr_s0              ( smu_axi_fabric_dbg_awaddr_s0    ),
  .o_smu_axi_fabric_dbg_awburst_s0             ( smu_axi_fabric_dbg_awburst_s0   ),
  .o_smu_axi_fabric_dbg_awcache_s0             ( smu_axi_fabric_dbg_awcache_s0   ),
  .o_smu_axi_fabric_dbg_awid_s0                ( smu_axi_fabric_dbg_awid_s0      ),
  .o_smu_axi_fabric_dbg_awlen_s0               ( smu_axi_fabric_dbg_awlen_s0     ),
  .o_smu_axi_fabric_dbg_awlock_s0              ( smu_axi_fabric_dbg_awlock_s0    ),
  .o_smu_axi_fabric_dbg_awprot_s0              ( smu_axi_fabric_dbg_awprot_s0    ),
  .o_smu_axi_fabric_dbg_awready_s0             ( smu_axi_fabric_dbg_awready_s0   ),
  .o_smu_axi_fabric_dbg_awsize_s0              ( smu_axi_fabric_dbg_awsize_s0    ),
  .o_smu_axi_fabric_dbg_awvalid_s0             ( smu_axi_fabric_dbg_awvalid_s0   ),
  .o_smu_axi_fabric_dbg_bid_s0                 ( smu_axi_fabric_dbg_bid_s0       ),
  .o_smu_axi_fabric_dbg_bready_s0              ( smu_axi_fabric_dbg_bready_s0    ),
  .o_smu_axi_fabric_dbg_bresp_s0               ( smu_axi_fabric_dbg_bresp_s0     ),
  .o_smu_axi_fabric_dbg_bvalid_s0              ( smu_axi_fabric_dbg_bvalid_s0    ),
  .o_smu_axi_fabric_dbg_rdata_s0               ( smu_axi_fabric_dbg_rdata_s0     ),
  .o_smu_axi_fabric_dbg_rid_s0                 ( smu_axi_fabric_dbg_rid_s0       ),
  .o_smu_axi_fabric_dbg_rlast_s0               ( smu_axi_fabric_dbg_rlast_s0     ),
  .o_smu_axi_fabric_dbg_rready_s0              ( smu_axi_fabric_dbg_rready_s0    ),
  .o_smu_axi_fabric_dbg_rresp_s0               ( smu_axi_fabric_dbg_rresp_s0     ),
  .o_smu_axi_fabric_dbg_rvalid_s0              ( smu_axi_fabric_dbg_rvalid_s0    ),
  .o_smu_axi_fabric_dbg_wdata_s0               ( smu_axi_fabric_dbg_wdata_s0     ),
  .o_smu_axi_fabric_dbg_wid_s0                 ( smu_axi_fabric_dbg_wid_s0       ),
  .o_smu_axi_fabric_dbg_wlast_s0               ( smu_axi_fabric_dbg_wlast_s0     ),
  .o_smu_axi_fabric_dbg_wready_s0              ( smu_axi_fabric_dbg_wready_s0    ),
  .o_smu_axi_fabric_dbg_wstrb_s0               ( smu_axi_fabric_dbg_wstrb_s0     ),
  .o_smu_axi_fabric_dbg_wvalid_s0              ( smu_axi_fabric_dbg_wvalid_s0    )
);

// Invert watchdog and rtc resets
always_comb begin
  o_rtc_irq = ~rtc_irq_n;
  o_wdt_irq = ~wdt_irq_n;

  // TODO - replace the output resets logic with the reset gen.
end

  ///////////////
  // MISC CSRs //
  ///////////////
  soc_mgmt_misc_csr_reg_pkg::soc_mgmt_misc_csr_reg2hw_t misc_csr_reg2hw;
  soc_mgmt_misc_csr_reg_pkg::soc_mgmt_misc_csr_hw2reg_t misc_csr_hw2reg;

  soc_mgmt_misc_csr_reg_pkg::apb_h2d_t apb_misc_csr_req;
  soc_mgmt_misc_csr_reg_pkg::apb_d2h_t apb_misc_csr_rsp;

  always_comb begin
    apb_misc_csr_req.paddr   = 32'(i_apb_misc_csr_paddr);
    apb_misc_csr_req.pwrite  = i_apb_misc_csr_pwrite;
    apb_misc_csr_req.pwdata  = i_apb_misc_csr_pwdata;
    apb_misc_csr_req.psel    = i_apb_misc_csr_psel;
    apb_misc_csr_req.penable = i_apb_misc_csr_penable;
    apb_misc_csr_req.pprot   = i_apb_misc_csr_pprot;
    apb_misc_csr_req.pstrb   = i_apb_misc_csr_pstrb;
  end
  always_comb o_apb_misc_csr_pready  = apb_misc_csr_rsp.pready;
  always_comb o_apb_misc_csr_prdata  = apb_misc_csr_rsp.prdata;
  always_comb o_apb_misc_csr_pslverr = apb_misc_csr_rsp.pslverr;

  soc_mgmt_misc_csr_reg_top #(
    .StageNum(STAGE_NUM)
  ) u_soc_mgmt_misc_csr_reg_top (
    .clk_i    (i_ref_clk),
    .rst_ni   (o_ao_rst_n),
    .apb_i    (apb_misc_csr_req),
    .apb_o    (apb_misc_csr_rsp),
    .reg2hw   (misc_csr_reg2hw),
    .hw2reg   (misc_csr_hw2reg),
    .devmode_i(1'b1)
  );

  // The RAM impl is only used by secure enclave
  always_comb begin
    // Inputs
    impl_inp.ret = misc_csr_reg2hw.mem_power_mode.ret.q;
    impl_inp.pde = misc_csr_reg2hw.mem_power_mode.pde.q;
    // scan_enable will be hooked up by the synthesis tool
    impl_inp.se  = 1'b0;
    // Outputs
    misc_csr_hw2reg.mem_power_up_ready.d = impl_oup.prn;
  end

  //============================================================================
  // Boot mode sampling

  localparam int unsigned BOOT_MODE_NUM_SAMPLE_CYCLES = 16; // I think 16 cycles is good enough and not long enough for the APU to reach the CSR

  logic [BOOT_MODE_NUM_SAMPLE_CYCLES-1:0] cold_reset_sample_extended_q;
  always_ff @(posedge i_ref_clk or negedge o_ao_rst_n) begin
    if (~o_ao_rst_n) cold_reset_sample_extended_q <= {(BOOT_MODE_NUM_SAMPLE_CYCLES){1'b1}};
    else             cold_reset_sample_extended_q <= {1'b0,cold_reset_sample_extended_q[BOOT_MODE_NUM_SAMPLE_CYCLES-1:1]};
  end

  always_comb misc_csr_hw2reg.boot_mode.d  = i_boot_mode;
  always_comb misc_csr_hw2reg.boot_mode.de = |cold_reset_sample_extended_q;

  //============================================================================
  // Global Sync Output (Direct from CSR)
  always_comb o_global_sync = misc_csr_reg2hw.global_sync.q;

  //============================================================================
  // -- Observability Mux

  if (soc_mgmt_pkg::OBS_IP_BUS_W % soc_mgmt_pkg::OBS_OP_BUS_W != 0) $fatal(
    1,
    "'soc_mgmt_pkg::OBS_OP_BUS_W (%d)' not a divider of 'soc_mgmt_pkg::OBS_IP_BUS_W (%d)'",
    soc_mgmt_pkg::OBS_OP_BUS_W,
    soc_mgmt_pkg::OBS_IP_BUS_W
  );

  localparam int unsigned NumObsSignals  = soc_mgmt_pkg::OBS_IP_BUS_W / soc_mgmt_pkg::OBS_OP_BUS_W;
  localparam int unsigned ObsSelectWidth = cc_math_pkg::index_width(NumObsSignals);

  if ($bits(misc_csr_reg2hw.obs_mux_select.q) != ObsSelectWidth)
    $fatal(
      1,
      "CSR: '$bits(misc_csr_reg2hw.obs_mux_select.q) (%d)' does not match localparam 'ObsSelectWidth (%d)'.",
      $bits(misc_csr_reg2hw.obs_mux_select.q),
      ObsSelectWidth
    );

  logic [ObsSelectWidth-1:0] obs_mux_select;
  always_comb obs_mux_select = (misc_csr_reg2hw.obs_mux_select.q >= ObsSelectWidth'(NumObsSignals)) ? ObsSelectWidth'(0) : misc_csr_reg2hw.obs_mux_select.q;
  always_comb o_obs_bus      = i_obs_bus[(obs_mux_select*soc_mgmt_pkg::OBS_OP_BUS_W)+:soc_mgmt_pkg::OBS_OP_BUS_W];

  //============================================================================
  // -- C2C
  // TODO(jmartins, Connect outputs to DLM when available)
  //
  // - Functionality
  //    - There are CDC assumptions here
  //      - The enable signal is being properly CDC'd inside the C2C Monitor
  //      - The configuration goes through a CDC bus but also around it so we must be careful.
  //      - The signals come from ref_clk domain into fast_clk domain so if we disable the C2C, configure it and then
  //      re-enable, the CDC of the enable signal ensures that the config is static.
  //    - The configuration must therefore ALWAYS follow the sequence:
  //      - i_enable = 0 -> change c2c_control CSR -> i_enable = 1

  logic                                     c2c_axis_valid;
  c2c_monitor_wrapper_pkg::c2c_data_width_t c2c_axis_data;

  // Configuration signals
  c2c_monitor_wrapper_pkg::c2c_cfg_t c2c_cfg;
  always_comb c2c_cfg.vote  = c2c_monitor_wrapper_pkg::c2c_vote_opt_e'(misc_csr_reg2hw.c2c_control.voting_cfg);
  always_comb c2c_cfg.scale = misc_csr_reg2hw.c2c_control.scale;

  // Map each C2C constant from CSR into internal struct
  //  -> Need to loop as many times as there are margin compute blocks
  for (genvar idx=0; idx<soc_mgmt_misc_csr_reg_pkg::C2C_CONSTANTS_GRP; idx++) begin : gen_connect_c2c_constants
    always_comb begin
      c2c_cfg.constants[idx].A = misc_csr_reg2hw.c2c_constants_ab[idx].a;
      c2c_cfg.constants[idx].B = misc_csr_reg2hw.c2c_constants_ab[idx].b;
      c2c_cfg.constants[idx].C = misc_csr_reg2hw.c2c_constants_cd[idx].c;
      c2c_cfg.constants[idx].D = misc_csr_reg2hw.c2c_constants_cd[idx].d;
    end
  end

  assign misc_csr_hw2reg.c2c_margin = '0; // TODO(jmartins, Connect inputs to DLM when available)

  c2c_monitor_wrapper u_c2c (
    .i_pll_clk   (o_fast_clk_int),
    .i_clk       (o_fast_clk_int),
    .i_rst_n     (o_global_rst_n),
    .i_test_mode (test_mode),
    .i_enable    (misc_csr_reg2hw.c2c_control.enable),
    .i_cfg       (c2c_cfg),
    .o_axis_valid(c2c_axis_valid),
    .o_axis_data (c2c_axis_data)
  );

endmodule
