// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Clock generation on
///
module soc_mgmt_clk_gen #(
  /// The number of syncronizer stages
  parameter int unsigned SyncStages = 3
)(
  /// Clock, positive edge triggered (Reference Clock)
  input  wire  i_clk,
  /// Asynchronous reset, active low (Always on reset)
  input  wire  i_rst_n,

  ///////////////////////
  // PLL Configuration //
  ///////////////////////
  /// The PLL configuration values for the respective PLLS
  input  soc_mgmt_pkg::pll_config_t i_pll_config[soc_mgmt_pkg::NUM_PLL],
  /// The PLL status values for observability
  output soc_mgmt_pkg::pll_status_t o_pll_status[soc_mgmt_pkg::NUM_PLL],

  ///////////////////////////////////////
  // CLK MUX and Divisor Configuration //
  ///////////////////////////////////////
  /// The MUX and Divider configuration values for the respective SYS_CLK
  input  soc_mgmt_pkg::mux_div_config_t i_mux_div_config[soc_mgmt_pkg::NUM_SYS_CLK],
  /// The MUX and Divider status values for observability
  output soc_mgmt_pkg::mux_div_status_t o_mux_div_status[soc_mgmt_pkg::NUM_SYS_CLK],

  //////////////////
  // DDR EAST CLK //
  //////////////////
  /// MUX selection for the east DDR selection
  input  soc_mgmt_pkg::mux_ddr_config_t i_mux_ddr_config,
  /// MUX selection for the east DDR selection
  output soc_mgmt_pkg::mux_ddr_status_t o_mux_ddr_status,

  ///////////////////
  // Output Clocks //
  ///////////////////
  /// Fast clock output (external)
  output wire o_fast_clk_ext,
  /// Fast clock output (internal)
  output wire o_fast_clk_int,
  /// APU clock output
  output wire o_apu_clk,
  /// CODEC clock output
  output wire o_codec_clk,
  /// EMMC clock output
  output wire o_emmc_clk,
  /// PERIPH clock output (external)
  output wire o_periph_clk_ext,
  /// PERIPH clock output (internal)
  output wire o_periph_clk_int,
  /// PVT clock output
  output wire o_pvt_clk,
  /// DDR ref east output
  output wire o_ddr_ref_east_clk,
  /// Reference clock output
  output wire o_ref_clk
`ifdef POWER_PINS
  ,
  inout  wire io_pll_avdd18,
  inout  wire io_pll_avss,
  inout  wire io_pll_dvdd075,
  inout  wire io_pll_dvss
`endif
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if (soc_mgmt_pkg::NUM_PLL != soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL)
    $fatal(1, "Parameter: 'NUM_PLL' must match between soc_mgmt_pkg(%d) and soc_mgmt_clk_gen_csr_reg_pkg(%d).",
           soc_mgmt_pkg::NUM_PLL, soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL);
  if (soc_mgmt_pkg::NUM_SYS_CLK != soc_mgmt_clk_gen_csr_reg_pkg::NUM_SYS_CLK)
    $fatal(1, "Parameter: 'NUM_SYS_CLK' must match between soc_mgmt_pkg(%d) and soc_mgmt_clk_gen_csr_reg_pkg(%d).",
           soc_mgmt_pkg::NUM_SYS_CLK, soc_mgmt_clk_gen_csr_reg_pkg::NUM_SYS_CLK);

  ////////////////////////
  // PLL Instantiations //
  ////////////////////////
  wire pll_clk[soc_mgmt_pkg::NUM_PLL];

  for (genvar pll_index = 0; unsigned'(pll_index) < soc_mgmt_pkg::NUM_PLL; pll_index++) begin : gen_plls
    pll_wrapper u_pll_wrapper (
      .o_pll_afc_code    (o_pll_status[pll_index].afc_code),
      .o_pll_feed_out    (o_pll_status[pll_index].feed_out),
      .o_pll_fout        (pll_clk[pll_index]),
      .o_pll_lock        (o_pll_status[pll_index].lock),
      `ifdef POWER_PINS
      .i_pll_avdd18      (io_pll_avdd18),
      .i_pll_avss        (io_pll_avss),
      .i_pll_dvdd075     (io_pll_dvdd075),
      .i_pll_dvss        (io_pll_dvss),
      `endif
      .i_pll_afc_enb     (i_pll_config[pll_index].afc_enb),
      .i_pll_bypass      (i_pll_config[pll_index].bypass),
      .i_pll_extafc      (i_pll_config[pll_index].extafc),
      .i_pll_feed_en     (i_pll_config[pll_index].feed_en),
      .i_pll_fin         (i_clk), // Reference Clock
      .i_pll_fout_mask   (i_pll_config[pll_index].fout_mask),
      .i_pll_fsel        (i_pll_config[pll_index].fsel),
      .i_pll_icp         (i_pll_config[pll_index].icp),
      .i_pll_lock_con_dly(i_pll_config[pll_index].lock_con_dly),
      .i_pll_lock_con_in (i_pll_config[pll_index].lock_con_in),
      .i_pll_lock_con_out(i_pll_config[pll_index].lock_con_out),
      .i_pll_m           (i_pll_config[pll_index].div_main),
      .i_pll_p           (i_pll_config[pll_index].div_pre),
      .i_pll_resetb      (i_pll_config[pll_index].resetb),
      .i_pll_rsel        (i_pll_config[pll_index].rsel),
      .i_pll_s           (i_pll_config[pll_index].div_scalar)
    );
  end

  //////////////////
  // Clock Muxing //
  //////////////////
  wire selected_clk[soc_mgmt_pkg::NUM_SYS_CLK];

  for (genvar clk_index = 0; unsigned'(clk_index) < soc_mgmt_pkg::NUM_SYS_CLK; clk_index++) begin : gen_clk_mux

    wire   to_be_divided_clks[soc_mgmt_pkg::CLK_MUX_CHOICES];
    assign to_be_divided_clks[soc_mgmt_pkg::PLL_SYS_0_CLK] = pll_clk[soc_mgmt_pkg::PLL_SYS_0];
    assign to_be_divided_clks[soc_mgmt_pkg::PLL_SYS_1_CLK] = pll_clk[soc_mgmt_pkg::PLL_SYS_1];
    wire   to_be_divided_clk;

    axe_ccl_clk_mux #(
      .NumClocks        (soc_mgmt_pkg::CLK_MUX_CHOICES),
      .SyncStages       (SyncStages),
      .ClkActiveReset   (soc_mgmt_pkg::CLK_ACTIVE_RESET),
      .ClkActiveResetIdx(soc_mgmt_pkg::REF_CLK)
    ) u_axe_ccl_clk_mux_pll (
      .i_clk_cfg  (i_clk),
      .i_rst_cfg_n(i_rst_n),
      .i_test_mode(1'b0),
      .i_select   (i_mux_div_config[clk_index].pll_mux_select),
      .i_enable   (i_mux_div_config[clk_index].pll_mux_enable),
      .o_active   (o_mux_div_status[clk_index].pll_mux_active),
      .o_is_on    (o_mux_div_status[clk_index].pll_mux_is_on),
      .i_clk      (to_be_divided_clks),
      .o_clk      (to_be_divided_clk)
    );

    soc_mgmt_pkg::clk_int_divisor_t fast_divisor;

    axe_ccl_cdc_bus #(
      .SyncStages(SyncStages),
      .data_t    (soc_mgmt_pkg::clk_int_divisor_t),
      .ResetValue(soc_mgmt_pkg::clk_int_divisor_t'(soc_mgmt_pkg::CLK_ACTIVE_RESET))
    ) u_axe_ccl_cdc_bus_divisor (
      .i_src_clk   (i_clk),
      .i_src_rst_n (i_rst_n),
      .i_src_en    (i_mux_div_config[clk_index].updated),
      .i_src_data  (i_mux_div_config[clk_index].divisor),
      .o_src_busy  (/* not used */), // ASO-UNUSED_OUTPUT : Updates should be infrequent enough that this would be busy.
      .i_dst_clk   (to_be_divided_clk),
      .i_dst_rst_n (i_rst_n),
      .o_dst_data  (fast_divisor),
      .o_dst_update(/* not used */) // ASO-UNUSED_OUTPUT : The output data is statically read.
    );

    wire divided_clk;

    axe_ccl_clk_div_by_int #(
      .MaxDivision (soc_mgmt_pkg::CLK_MAX_INT_DIVISION),
      .ClkOnInReset(1'b1)
    ) u_axe_ccl_clk_div_by_int (
      .i_clk      (to_be_divided_clk),
      .i_rst_n,
      .i_test_mode(1'b0),
      .i_divisor  (fast_divisor),
      .o_clk      (divided_clk)
    );

    wire   to_be_selected_clk[soc_mgmt_pkg::CLK_MUX_CHOICES];
    assign to_be_selected_clk[soc_mgmt_pkg::REF_CLK] = i_clk;
    assign to_be_selected_clk[soc_mgmt_pkg::DIV_CLK] = divided_clk;

    axe_ccl_clk_mux #(
      .NumClocks        (soc_mgmt_pkg::CLK_MUX_CHOICES),
      .SyncStages       (SyncStages),
      .ClkActiveReset   (soc_mgmt_pkg::CLK_ACTIVE_RESET),
      .ClkActiveResetIdx(soc_mgmt_pkg::REF_CLK)
    ) u_axe_ccl_clk_mux_div (
      .i_clk_cfg  (i_clk),
      .i_rst_cfg_n(i_rst_n),
      .i_test_mode(1'b0),
      .i_select   (i_mux_div_config[clk_index].div_mux_select),
      .i_enable   (i_mux_div_config[clk_index].div_mux_enable),
      .o_active   (o_mux_div_status[clk_index].div_mux_active),
      .o_is_on    (o_mux_div_status[clk_index].div_mux_is_on),
      .i_clk      (to_be_selected_clk),
      .o_clk      (selected_clk[clk_index])
    );
  end

  ///////////////////////////
  // DDR EAST Clock Select //
  ///////////////////////////
  wire   ddr_to_be_selected_clk[2];
  assign ddr_to_be_selected_clk[0] = i_clk;
  assign ddr_to_be_selected_clk[1] = pll_clk[soc_mgmt_pkg::PLL_DDR];

  axe_ccl_clk_mux #(
    .NumClocks        (2),
    .SyncStages       (SyncStages),
    .ClkActiveReset   (soc_mgmt_pkg::CLK_ACTIVE_RESET),
    .ClkActiveResetIdx(soc_mgmt_pkg::REF_CLK)
  ) u_axe_ccl_clk_mux_ddr (
    .i_clk_cfg  (i_clk),
    .i_rst_cfg_n(i_rst_n),
    .i_test_mode(1'b0),
    .i_select   (i_mux_ddr_config.mux_select),
    .i_enable   (i_mux_ddr_config.mux_enable),
    .o_active   (o_mux_ddr_status.mux_active),
    .o_is_on    (o_mux_ddr_status.mux_is_on),
    .i_clk      (ddr_to_be_selected_clk),
    .o_clk      (o_ddr_ref_east_clk)
  );

  ////////////////////////
  // Output Assignments //
  ////////////////////////
  assign o_fast_clk_ext     = selected_clk[soc_mgmt_pkg::CLK_FAST];
  assign o_fast_clk_int     = selected_clk[soc_mgmt_pkg::CLK_FAST];
  assign o_apu_clk          = selected_clk[soc_mgmt_pkg::CLK_APU];
  assign o_codec_clk        = selected_clk[soc_mgmt_pkg::CLK_CODEC];
  assign o_emmc_clk         = selected_clk[soc_mgmt_pkg::CLK_EMMC];
  assign o_periph_clk_ext   = selected_clk[soc_mgmt_pkg::CLK_PERIPH];
  assign o_periph_clk_int   = selected_clk[soc_mgmt_pkg::CLK_PERIPH];
  assign o_pvt_clk          = selected_clk[soc_mgmt_pkg::CLK_PVT];
  assign o_ref_clk          = i_clk; // TODO: should there be a tech_cell clock buffer in between?

endmodule
