// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

/// DDR west clock gen block p_wrapper.
module ddr_west_clock_gen_p
  import chip_pkg::*;
  import ddr_west_clock_gen_pkg::*;
(
  // APB Clock, positive edge triggered
  input   wire   i_ref_clk,
  // Asynchronous POR / always On reset, active low
  input   wire   i_ao_rst_n,
  // Asynchronous global reset, active low
  input   wire   i_global_rst_n,

  // PLL Output clock
  output wire    o_ddr_west_clk,

  /// SYSCFG APB slave signals
  input  chip_syscfg_addr_t     i_cfg_apb4_s_paddr      ,
  input  chip_apb_syscfg_data_t i_cfg_apb4_s_pwdata     ,
  input  logic                  i_cfg_apb4_s_pwrite     ,
  input  logic                  i_cfg_apb4_s_psel       ,
  input  logic                  i_cfg_apb4_s_penable    ,
  input  chip_apb_syscfg_strb_t i_cfg_apb4_s_pstrb      ,
  input  logic          [3-1:0] i_cfg_apb4_s_pprot      ,
  output logic                  o_cfg_apb4_s_pready     ,
  output chip_apb_syscfg_data_t o_cfg_apb4_s_prdata     ,
  output logic                  o_cfg_apb4_s_pslverr    ,

  // Observation port
  output logic [15:0]           o_ddr_west_clkgen_obs      ,

  // -- DFT
  input wire          tck,
  input wire          trst,
  input logic         tms,
  input logic         tdi,
  output logic        tdo_en,
  output logic        tdo,

  input  wire         test_clk,
  input  logic        test_mode,
  input  logic        edt_update,
  input  logic        scan_en,
  input  logic [11:0] scan_in,
  output logic [11:0] scan_out,

  input  wire         bisr_clk,
  input  wire         bisr_reset,
  input  logic        bisr_shift_en,
  input  logic        bisr_si,
  output logic        bisr_so

`ifdef POWER_PINS
                                                           ,
  inout  wire                   io_pll_avdd18              ,
  inout  wire                   io_pll_avss                ,
  inout  wire                   io_pll_dvdd075             ,
  inout  wire                   io_pll_dvss
`endif
);

  // --------------------------------------------------------------
  // Signals
  pctl_ao_csr_reg_pkg::apb_h2d_t ao_csr_apb_req;
  pctl_ao_csr_reg_pkg::apb_d2h_t ao_csr_apb_rsp;

  ddr_west_clock_gen_csr_reg_pkg::ddr_west_clock_gen_csr_reg2hw_t reg2hw; // Write
  ddr_west_clock_gen_csr_reg_pkg::ddr_west_clock_gen_csr_hw2reg_t hw2reg; // Read

  clksel_t csr_clk_sel;
  logic    csr_pll_bypass;
  pllm_t   csr_pll_feedback_div;
  pllp_t   csr_pll_ref_output_div;
  plls_t   csr_pll_pre_output_div;
  logic    csr_pll_reset;
  logic    csr_pll_lock;

  // Internal Clocks and Resets
  wire ao_rst_sync_n;
  wire partition_clk;

  // --------------------------------------------------------------
  // RTL
  // TODO(jmartins, Silver, Connect some observation signals here)
  assign o_sysspm_obs = '0;
  // ---------------
  // -- Partition Control
  pctl #(
    .N_FAST_CLKS      (1),
    .N_RESETS         (1),
    .N_MEM_PG         (1),
    .N_FENCES         (1), // TODO(jmartins, Silver, Should be 0)
    .N_THROTTLE_PINS  (0),
    .CLKRST_MATRIX    (1'b1),
    .PLL_CLK_IS_I_CLK (1'b0),
    .NOC_RST_IDX      (1'b0),
    .SYNC_CLK_IDX     (1'b0),
    .AUTO_RESET_REMOVE(1'b1), // DDR West Clock Gen should leave reset automatically
    .paddr_t          (chip_pkg::chip_syscfg_addr_t),
    .pdata_t          (chip_pkg::chip_apb_syscfg_data_t),
    .pstrb_t          (chip_pkg::chip_apb_syscfg_strb_t)
  ) u_pctl (
    // Input clocks and resets
    .i_clk    (i_ref_clk),
    .i_pll_clk(i_ref_clk),

    .i_ao_rst_n    (i_ao_rst_n),
    .i_global_rst_n(i_ao_rst_n), // There's no global reset need

    .i_test_mode   (test_mode),
    .i_throttle(1'b0),

    // Output clocks and resets
    .o_partition_clk  (partition_clk),
    .o_partition_rst_n(/*NC*/), // Everything runs on AO Reset
    .o_ao_rst_sync_n  (ao_rst_sync_n),

    // Isolation interface
    // --> There is no fencing since this partition operates only on the AO domain
    .o_noc_async_idle_req (/*NC*/),
    .i_noc_async_idle_ack (1'b0), // Tie to not leave undriven
    .i_noc_async_idle_val (1'b0), // Tie to not leave undriven
    .o_noc_clken (/*NC*/),
    .o_noc_rst_n (/*NC*/),

    .o_int_shutdown_req  (/*NC*/),
    .i_int_shutdown_ack  (1'b1),

    // SRAM control signals
    .o_ret(/*NC*/),
    .o_pde(/*NC*/),
    .i_prn('0),

    // SYS_CFG Bus
    .i_cfg_apb4_s_paddr,
    .i_cfg_apb4_s_pwdata,
    .i_cfg_apb4_s_pwrite,
    .i_cfg_apb4_s_psel,
    .i_cfg_apb4_s_penable,
    .i_cfg_apb4_s_pstrb,
    .i_cfg_apb4_s_pprot,
    .o_cfg_apb4_s_pready,
    .o_cfg_apb4_s_prdata,
    .o_cfg_apb4_s_pslverr,
    // Sync interface
    .i_global_sync_async(1'b0),
    .o_global_sync      (/*NC*/),
    // External APB interface
    .o_ao_csr_apb_req(ao_csr_apb_req),
    .i_ao_csr_apb_rsp(ao_csr_apb_rsp)
  );

  // CSR
  ddr_west_clock_gen_csr_reg_top u_ddr_west_clock_gen_ao_csr (
    .clk_i (i_ref_clk),
    .rst_ni(ao_rst_sync_n),
    // APB interface
    .apb_i(ao_csr_apb_req),
    .apb_o(ao_csr_apb_rsp),
    // HW interface
    .reg2hw,
    .hw2reg,
    // Config
    .devmode_i ( 1'h1)    // If 1, explicit error return for unmapped register access
  );

  //============================================================================
  // Clock gen
  ddr_west_clock_gen u_ddr_west_clock_gen (
    .i_ref_clk                ( partition_clk), // We use the clock gateable clock from PCTL
    .i_rst_n                  ( ao_rst_sync_n), // We use the synchronised AO Reset
    .i_csr_clk_mux_select     ( reg2hw.clk_select.q[0]),
    .i_csr_pll_bypass         ( reg2hw.pll_bypass.q),
    .i_csr_pll_feedback_div   ( reg2hw.pll_divider.feedback_divider.q   ),
    .i_csr_pll_ref_output_div ( reg2hw.pll_divider.ref_output_divider.q ),
    .i_csr_pll_pre_output_div ( reg2hw.pll_divider.pre_output_divider.q ),
    .i_csr_pll_reset          ( reg2hw.pll_reset.q),
    .o_csr_pll_lock           ( hw2reg.pll_lock.d),
    .o_ddr_west_clk           ( o_ddr_west_clk),
    .test_mode                ( 1'h0 )
  `ifdef POWER_PINS
    ,
    .io_pll_avdd18            ( io_pll_avdd18  ),
    .io_pll_avss              ( io_pll_avss    ),
    .io_pll_dvdd075           ( io_pll_dvdd075 ),
    .io_pll_dvss              ( io_pll_dvss    )
  `endif
  );

endmodule

