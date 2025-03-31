// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson    <andrew.dickson@axelera.ai>
//        Kevin Luciani     <kevin.luciani@axelera.ai>

/// Description: SoC Management Reset Generator module.
///

module soc_mgmt_reset_gen
   import soc_mgmt_reset_gen_csr_reg_pkg::*;
   import chip_pkg                      ::*;
   import axi_pkg                       ::*;
   import soc_mgmt_pkg                  ::*;
#(
  parameter int unsigned NUM_RESETS_RSTGEN = 3,
  parameter int unsigned STAGE_NUM         = 3
) (
  // reference clock
  input  wire                           i_clk,
  // fast clock for noc reset
  input  wire                           i_por_rst_n,
  input  logic                          test_mode,
  input  logic                          i_dft_clk_rst_ctrl,
  input  wire  [NUM_RESETS_RSTGEN-1:0]  i_test_rst_n,
  input  wire                           i_dmi_rst_n,
  input  wire                           i_rot_rst_n,
  // Watch dog reset
  input  wire                           i_wdt_rst_n,
  // Reset strobe from MBIST
  input  wire                           i_mbist_rst_n,
  // Reset strobe from DEBUGGER
  input  wire                           i_debug_rst_n,
  // different "full reset" sources for every stage
  // consistently reset request from particular stage
  input  wire                           i_ao_rst_req_n,
  // reset ack for particular stage
  output logic                          o_ao_rst_ack_n,
  // rst ack for particular IP
  input  logic                          i_ao_rst_ip_ack,
  // Reset stage 0. Always on reset output.
  output wire                           o_ao_rst_ip_n,
  // reset ack for particular stage
  output logic                          o_dmi_rst_ack_n,
  // rst ack for particular IP
  input  logic                          i_dmi_rst_ip_ack,
  // Reset stage 1. Reset strobe for particular IP
  output wire                           o_dmi_rst_ip_n,
  // consistently reset request from particular stage
  input  wire                           i_global_rst_req_n,
  // reset ack for particular stage
  output logic                          o_global_rst_ack_n,
  // rst ack for particular IP
  input  logic                          i_global_rst_ip_ack,
  // Resert Stage 2 reset strobe output
  output wire                           o_global_rst_ip_n,
  // CSR APB if
  input  apb_h2d_t                      i_apb,
  output apb_d2h_t                      o_apb
);

  //============================================================================
  // Parameters
  localparam int unsigned RST_SRC_NUM         = 2;
  localparam int unsigned RST_IP_NUM          = 1;
  localparam int unsigned RST_STRETCH_USE     = 1;

  // Stretch ocunter
  localparam int unsigned STRETCHW            = 12;

  //============================================================================
  // Signal declarations
  soc_mgmt_reset_gen_csr_reg_pkg::soc_mgmt_reset_gen_csr_reg2hw_t reg2hw;

  wire                         [STAGE_NUM  -1:0] rst_stage;

  // Basic reset gen signal declarations to support generate
  wire  [NUM_RESETS_RSTGEN-1:0]                  bb_i_rst_n;
  wire  [NUM_RESETS_RSTGEN-1:0]                  bb_i_rst_req_n;
  wire  [NUM_RESETS_RSTGEN-1:0]                  bb_o_rst_ack_n; // TODO: ADI check if some of these can be logic and then create types
  wire  [NUM_RESETS_RSTGEN-1:0][STRETCHW   -1:0] bb_i_stretch_cycles;
  wire  [NUM_RESETS_RSTGEN-1:0][RST_SRC_NUM-1:0] bb_i_rst_src_n;
  wire  [NUM_RESETS_RSTGEN-1:0][RST_SRC_NUM-1:0] bb_i_mask_reset_src;
  wire  [NUM_RESETS_RSTGEN-1:0][RST_IP_NUM -1:0] bb_i_rst_ip_sw_n;
  wire  [NUM_RESETS_RSTGEN-1:0][RST_IP_NUM -1:0] bb_i_rst_ip_force;
  wire  [NUM_RESETS_RSTGEN-1:0][RST_IP_NUM -1:0] bb_i_ack_reset_ip;
  wire  [NUM_RESETS_RSTGEN-1:0][RST_IP_NUM -1:0] bb_o_rst_ip_n;

  // clock mux signal declarations to support generate
  wire  [NUM_RESETS_RSTGEN-1:0]                  dft_mux_func_rst_n;  // Functional-mode reset input of DFT MUX
  wire  [NUM_RESETS_RSTGEN-1:0]                  dft_mux_test_rst_n;  // Test-mode reset input of DFT MUX
  wire  [NUM_RESETS_RSTGEN-1:0]                  dft_mux_rst_out_n;   // DFT MUX reset output

  wire                                           wdt_ao_rst_n;
  wire                                           wdt_global_rst_n;

  //============================================================================
  // RESET STAGES
  // generate NUM_RESETS_RSTGEN = 3
  //                                 reset_gen_basic_block
  //                            +------------------------------+
  //  i_clk                  -->| i_clk            o_rst_ack_n |--> bb_o_rst_ack_n[N]
  //  bb_i_rst_n         [N] -->| i_rst_n          o_rst_ip_n  |--> bb_o_rst_ip_n [N]
  //  i_test_mode            -->| test_mode        o_rst_n     |--> rst_stage     [N]
  //  i_por_rst_n            -->| i_test_rst_n                 |
  //  bb_i_rst_req_n     [N] -->| i_rst_req_n                  |
  //  bb_i_stretch_cycles[N] -->| i_stretch_cycles             |
  //  bb_i_rst_src_n     [N] -->| i_rst_src_n                  |
  //  bb_i_mask_reset_src[N] -->| i_mask_reset_src             |
  //  bb_i_rst_ip_sw_n   [N] -->| i_rst_ip_sw_n                |
  //  bb_i_rst_ip_force  [N] -->| i_rst_ip_force               |
  //  bb_i_ack_reset_ip  [N] -->| i_ack_reset_ip               |
  //                             +------------------------------+
  //
  //============================================================================
  // Connections for the reseet_gen_basic_block for each stage
  // STAGE 0
  assign bb_i_rst_n         [0] = i_por_rst_n; // Master reset input
  assign bb_i_rst_req_n     [0] = i_ao_rst_req_n;
  assign bb_i_stretch_cycles[0] = reg2hw.rst_cfg_ao_rst.rst_stretch.q;
  assign bb_i_rst_src_n     [0] = {1'b1, wdt_ao_rst_n};
  assign bb_i_rst_ip_force  [0] = {RST_SRC_NUM {1'b0}};
  assign bb_i_mask_reset_src[0] = reg2hw.rst_cfg_ao_rst.rst_src_mask.q;
  assign bb_i_rst_ip_sw_n   [0] = reg2hw.rst_sw_ao_rst;
  assign bb_i_ack_reset_ip  [0] = i_ao_rst_ip_ack;
  assign o_ao_rst_ack_n         = bb_o_rst_ack_n[0];

  // test mux
  assign dft_mux_func_rst_n [0] = bb_o_rst_ip_n     [0];
  assign dft_mux_test_rst_n [0] = i_test_rst_n      [0];
  assign o_ao_rst_ip_n          = dft_mux_rst_out_n [0];

  // STAGE 1
  assign bb_i_rst_n         [1] = rst_stage[0]; // Stage 1 Reset input from previous stage
  assign bb_i_rst_req_n     [1] = i_dmi_rst_n;
  assign bb_i_stretch_cycles[1] = reg2hw.rst_cfg_dmi_rst.rst_stretch.q;
  assign bb_i_rst_src_n     [1] = {i_rot_rst_n, i_mbist_rst_n};
  assign bb_i_rst_ip_force  [1] = {RST_SRC_NUM {1'b0}};
  assign bb_i_mask_reset_src[1] = reg2hw.rst_cfg_dmi_rst.rst_src_mask.q;
  assign bb_i_rst_ip_sw_n   [1] = reg2hw.rst_sw_dmi_rst;
  assign bb_i_ack_reset_ip  [1] = i_dmi_rst_ip_ack;
  assign o_dmi_rst_ack_n        = bb_o_rst_ack_n[1];

  // test mux
  assign dft_mux_func_rst_n [1] = bb_o_rst_ip_n     [1];
  assign dft_mux_test_rst_n [1] = i_test_rst_n      [1];
  assign o_dmi_rst_ip_n         = dft_mux_rst_out_n [1];

  // STAGE 2
  assign bb_i_rst_n         [2] = rst_stage[1]; // Reset input from previous stage
  assign bb_i_rst_req_n     [2] = i_global_rst_req_n;
  assign bb_i_stretch_cycles[2] = reg2hw.rst_cfg_global_rst.rst_stretch.q;
  assign bb_i_rst_src_n     [2] = {wdt_global_rst_n, i_debug_rst_n};
  assign bb_i_rst_ip_force  [2] = {RST_IP_NUM{1'b0}};
  assign bb_i_mask_reset_src[2] = reg2hw.rst_cfg_global_rst.rst_src_mask.q;
  assign bb_i_rst_ip_sw_n   [2] = reg2hw.rst_sw_global_rst;
  assign bb_i_ack_reset_ip  [2] = i_global_rst_ip_ack;
  assign o_global_rst_ack_n     = bb_o_rst_ack_n[2];

  // test mux
  assign dft_mux_func_rst_n [2] = bb_o_rst_ip_n     [2];
  assign dft_mux_test_rst_n [2] = i_test_rst_n      [2];
  assign o_global_rst_ip_n      = dft_mux_rst_out_n [2];

  //============================================================================
  for (genvar i=0; i<NUM_RESETS_RSTGEN; i++) begin : gen_reset_stages
    //
    // reset generation
    reset_gen_basic_block #(
      .RST_SRC_NUM      (RST_SRC_NUM),
      .RST_IP_NUM       (RST_IP_NUM),
      .RST_STRETCH_USE  (RST_STRETCH_USE)
    ) u_reset_gen_basic_block_rst (
      .i_clk            (i_clk                   ),
      .i_rst_n          (bb_i_rst_n          [i] ),
      .i_test_mode      (test_mode               ),
      .i_test_rst_n     (i_por_rst_n             ),
      .i_rst_req_n      (bb_i_rst_req_n      [i] ),
      .o_rst_ack_n      (bb_o_rst_ack_n      [i] ),
      .i_stretch_cycles (bb_i_stretch_cycles [i] ),
      .i_rst_src_n      (bb_i_rst_src_n      [i] ),
      .i_mask_reset_src (bb_i_mask_reset_src [i] ),
      .i_rst_ip_sw_n    (bb_i_rst_ip_sw_n    [i] ),
      .i_rst_ip_force   (bb_i_rst_ip_force   [i] ),
      .i_ack_reset_ip   (bb_i_ack_reset_ip   [i] ),
      .o_rst_ip_n       (bb_o_rst_ip_n       [i] ),
      .o_rst_n          (rst_stage           [i] )
    );

    // reset mux for test mode
    axe_tcl_clk_mux2 u_dft_mux_ctrl_rst (
      .i_clk0 ( dft_mux_func_rst_n[i]  ),
      .i_clk1 ( dft_mux_test_rst_n[i]  ),
      .i_sel  ( i_dft_clk_rst_ctrl     ),
      .o_clk  ( dft_mux_rst_out_n [i]  )
    );

  end

  //============================================================================
  // CSR
  soc_mgmt_reset_gen_csr_reg_top #(
    .StageNum (STAGE_NUM)
  ) u_soc_mgmt_reset_gen_csr_reg_top (
    .clk_i     ( i_clk         ),
    .rst_ni    ( o_ao_rst_ip_n ), // Always on reset
    .apb_i     ( i_apb         ),
    .apb_o     ( o_apb         ),
    .reg2hw    ( reg2hw        ),
    .devmode_i ( 1'b1          )
  );

  // Watchdog timer reset can be routed to either reset stage 0 (AO reset) or reset stage 2 (Global reset - default).
  axe_tcl_clk_mux2 u_wdt_ao_rst_mux (
    .i_clk0 (1'b1),
    .i_clk1 (i_wdt_rst_n),
    .i_sel  (reg2hw.wdt_reset_config.q),
    .o_clk  (wdt_ao_rst_n)
  );

  axe_tcl_clk_mux2 u_wdt_global_rst_mux (
    .i_clk0 (i_wdt_rst_n),
    .i_clk1 (1'b1),
    .i_sel  (reg2hw.wdt_reset_config.q),
    .o_clk  (wdt_global_rst_n)
  );

endmodule
