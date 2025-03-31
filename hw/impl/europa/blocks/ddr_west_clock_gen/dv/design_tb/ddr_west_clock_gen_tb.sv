// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>

// block testbench for the ddr_west clock gen module
//
module ddr_west_clock_gen_tb;
import uvm_pkg::*;
`include "uvm_macros.svh"

import chip_pkg                      ::*;
//import axi_pkg                       ::*;

import ddr_west_clock_gen_csr_reg_pkg::*;

//============================================================================
// signal declaration
logic                  i_ref_clk                  ;
logic                  i_rst_n                    ;

// PLL Output clock
wire                   o_ddr_west_clk             ;

  /// SYSCFG APB slave signals
chip_syscfg_addr_t     i_syscfg_apb4_s_paddr      ;
chip_apb_syscfg_data_t i_syscfg_apb4_s_pwdata     ;
logic                  i_syscfg_apb4_s_pwrite     ;
logic                  i_syscfg_apb4_s_psel       ;
logic                  i_syscfg_apb4_s_penable    ;
chip_apb_syscfg_strb_t i_syscfg_apb4_s_pstrb      ;
logic          [3-1:0] i_syscfg_apb4_s_pprot      ;
logic                  o_syscfg_apb4_s_pready     ;
chip_apb_syscfg_data_t o_syscfg_apb4_s_prdata     ;
logic                  o_syscfg_apb4_s_pslverr    ;

// jtag interface
logic                  ijtag_tck                  ;
logic                  ijtag_reset                ;
logic                  ijtag_sel                  ;
logic                  ijtag_ue                   ;
logic                  ijtag_se                   ;
logic                  ijtag_ce                   ;
logic                  ijtag_si                   ;
logic                  ijtag_so                   ;

// test interface
logic                  test_clk                   ;
logic                  test_mode                  ;
logic                  edt_update                 ;
logic                  scan_en                    ;
logic [11:0]           scan_in                    ;
logic [11:0]           scan_out                   ;

logic                  bisr_clk                   ;
logic                  bisr_reset                 ;
logic                  bisr_shift_en              ;
logic                  bisr_si                    ;
logic                  bisr_so                    ;

supply1                io_pll_avdd18              ;
supply0                io_pll_avss                ;
supply1                io_pll_dvdd075             ;
supply0                io_pll_dvss                ;

int unsigned           fail_cnt                   ;
chip_apb_syscfg_data_t reg_read_data              ;

//============================================================================
`include "tb_tasks.svh"

initial begin
  init_inputs();
  drv_ref_clk();
  do_reset();

  // enable pll
  #10us;
  ddr_clk_setup();

  #10us;
  test_report(fail_cnt);
  $finish();
end

//============================================================================
// DUT
ddr_west_clock_gen_p u_ddr_west_clock_gen_p (
  .i_ref_clk                ( i_ref_clk               ),
  .i_rst_n                  ( i_rst_n                 ),

  .o_ddr_west_clk           ( o_ddr_west_clk          ),

  /// SYSCFG APB slave signals
  .i_syscfg_apb4_s_paddr    ( i_syscfg_apb4_s_paddr   ),
  .i_syscfg_apb4_s_pwdata   ( i_syscfg_apb4_s_pwdata  ),
  .i_syscfg_apb4_s_pwrite   ( i_syscfg_apb4_s_pwrite  ),
  .i_syscfg_apb4_s_psel     ( i_syscfg_apb4_s_psel    ),
  .i_syscfg_apb4_s_penable  ( i_syscfg_apb4_s_penable ),
  .i_syscfg_apb4_s_pstrb    ( i_syscfg_apb4_s_pstrb   ),
  .i_syscfg_apb4_s_pprot    ( i_syscfg_apb4_s_pprot   ),
  .o_syscfg_apb4_s_pready   ( o_syscfg_apb4_s_pready  ),
  .o_syscfg_apb4_s_prdata   ( o_syscfg_apb4_s_prdata  ),
  .o_syscfg_apb4_s_pslverr  ( o_syscfg_apb4_s_pslverr ),

  // jtag interface
  .ijtag_tck                ( ijtag_tck               ),
  .ijtag_reset              ( ijtag_reset             ),
  .ijtag_sel                ( ijtag_sel               ),
  .ijtag_ue                 ( ijtag_ue                ),
  .ijtag_se                 ( ijtag_se                ),
  .ijtag_ce                 ( ijtag_ce                ),
  .ijtag_si                 ( ijtag_si                ),
  .ijtag_so                 ( ijtag_so                ),

  .bisr_clk                 ( bisr_clk                ),
  .bisr_reset               ( bisr_reset              ),
  .bisr_shift_en            ( bisr_shift_en           ),
  .bisr_si                  ( bisr_si                 ),
  .bisr_so                  ( bisr_so                 ),

  // test interface
  .test_clk                 ( test_clk                ),
  .test_mode                ( test_mode               ),
  .edt_update               ( edt_update              ),
  .scan_en                  ( scan_en                 ),
  .scan_in                  ( scan_in                 ),
  .scan_out                 ( scan_out                )
`ifdef POWER_PINS
                                        ,
  .io_pll_avdd18            ( io_pll_avdd18           ),
  .io_pll_avss              ( io_pll_avss             ),
  .io_pll_dvdd075           ( io_pll_dvdd075          ),
  .io_pll_dvss              ( io_pll_dvss             )
`endif
);


endmodule

