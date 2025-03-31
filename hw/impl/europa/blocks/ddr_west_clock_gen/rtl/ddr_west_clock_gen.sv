// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

/// DDR west clock gen block. Instantiate pll wrapper and connects CSR to
///
module ddr_west_clock_gen
  import ddr_west_clock_gen_pkg::*;
  import chip_pkg              ::*;
(
  /// Clock, positive edge triggered
  input  wire         i_ref_clk                ,
  /// Asynchronous reset, active low
  input  wire         i_rst_n                  ,
  // clock select
  input  clksel_t     i_csr_clk_mux_select     ,
  // PLL CSR
  input  logic        i_csr_pll_bypass         ,
  input  pllm_t       i_csr_pll_feedback_div   ,
  input  pllp_t       i_csr_pll_ref_output_div ,
  input  plls_t       i_csr_pll_pre_output_div ,
  input  logic        i_csr_pll_reset          ,
  output logic        o_csr_pll_lock           ,

  // PLL Output clock
  output wire         o_ddr_west_clk           ,

  input  logic        test_mode

`ifdef POWER_PINS
                                               ,
  inout  wire         io_pll_avdd18            ,
  inout  wire         io_pll_avss              ,
  inout  wire         io_pll_dvdd075           ,
  inout  wire         io_pll_dvss
`endif
);

//============================================================================
// parameters
// clock mux active clock reset
localparam bit          CLKACTIVERESET    = 1'h1 ;
// clock mux active clock index
localparam int unsigned CLKACTIVERESETIDX = 0    ;

localparam int unsigned NB_CLKMUX_CLK_IN  = 2    ;

typedef logic [NB_CLKMUX_CLK_IN-1:0] clkmux_active_t;

//============================================================================
// signal declaration
wire            pll_clk                        ;

clkmux_active_t clk_mux_active                 ;
logic           clk_mux_clk_is_on              ;

wire            clkmux_clk_in[NB_CLKMUX_CLK_IN];
wire            clk_mux_out                    ;

//============================================================================
// RTL

// PLL wrapper
pll_wrapper u_pll_wrapper (
  .o_pll_afc_code     (                          ),
  .o_pll_feed_out     (                          ),
  .o_pll_fout         ( pll_clk                  ),
  .o_pll_lock         ( o_csr_pll_lock           ),
  `ifdef POWER_PINS
  .i_pll_avdd18       ( io_pll_avdd18            ),
  .i_pll_avss         ( io_pll_avss              ),
  .i_pll_dvdd075      ( io_pll_dvdd075           ),
  .i_pll_dvss         ( io_pll_dvss              ),
  `endif
  .i_pll_afc_enb      ( '0                       ),
  .i_pll_bypass       ( i_csr_pll_bypass         ),
  .i_pll_extafc       ( '0                       ),
  .i_pll_feed_en      ( '0                       ),
  .i_pll_fin          ( i_ref_clk                ),
  .i_pll_fout_mask    ( '0                       ),
  .i_pll_fsel         ( '0                       ),
  .i_pll_icp          ( PLL_ICP                  ),
  .i_pll_lock_con_dly (  2'h3                    ),
  .i_pll_lock_con_in  (  2'h3                    ),
  .i_pll_lock_con_out (  2'h3                    ),
  .i_pll_m            ( i_csr_pll_feedback_div   ),
  .i_pll_p            ( i_csr_pll_ref_output_div ),
  .i_pll_resetb       ( i_csr_pll_reset          ),
  // Reserved value
  .i_pll_rsel         ( PLL_RSEL                 ),
  .i_pll_s            ( i_csr_pll_pre_output_div )
);

// connecrt clock mux input clock
assign clkmux_clk_in[0] = i_ref_clk;
assign clkmux_clk_in[1] = pll_clk;

// Glitch-free clock select
axe_ccl_clk_mux #(
  .SyncStages        ( STAGE_NUM          ),
  .NumClocks         ( NB_CLKMUX_CLK_IN   ),
  .ClkActiveReset    ( CLKACTIVERESET     ),
  .ClkActiveResetIdx ( CLKACTIVERESETIDX  )
) u_axe_ccl_clk_mux (
   // Configuration //
  .i_clk_cfg   ( i_ref_clk            ),
  .i_rst_cfg_n ( i_rst_n              ),
  .i_test_mode ( test_mode            ),
  .i_select    ( i_csr_clk_mux_select ),
  .i_enable    ( '1                   ),
  // Observability
  .o_active    ( clk_mux_active       ), // not used
  .o_is_on     ( clk_mux_clk_is_on    ), // not used
  // Clocks to select
  .i_clk       ( clkmux_clk_in        ),
  .o_clk       ( clk_mux_out          )
);

// output clock
assign o_ddr_west_clk = clk_mux_out;

endmodule

