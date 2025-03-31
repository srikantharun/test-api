module europa_io #(
  parameter int unsigned NumPowerPadsPerRow = 2
)(

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // ref_clk (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_ref_clk,
  input  logic [1:0] i_ref_clk_sel_freq,
  output wire        o_pad_ref_clk,
  input  wire        i_pad_ref_clk,
  input  wire        i_pad_ref_clk_bypass,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // tck (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic o_tck,
  input  logic i_clk_schmitt,
  input  wire  i_pad_tck,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // spi_clk_out (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_spi_clk,
  input  logic [1:0] i_spi_drive,
  output wire        o_pad_spi_clk_out,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // sd_emmc_clk_out (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_sd_emmc_clk,
  input  logic       i_sd_emmc_clk_oe,
  input  logic [2:0] i_emmc_drive,
  input  logic       i_emmc_schmitt,
  output wire        o_pad_sd_emmc_clk_out,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // ssn_bus_0_clk (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_ssn_bus_0_clk,
  input  logic       i_dft_pulldown,
  input  logic [1:0] i_dft_drive,
  /* Port already declared:
  input  logic       i_clk_schmitt, */
  input  wire        i_pad_ssn_bus_0_clk,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // ssn_bus_1_clk (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_ssn_bus_1_clk,
  /* Port already declared:
  input  logic       i_dft_pulldown, */
  /* Port already declared:
  input  logic [1:0] i_dft_drive, */
  /* Port already declared:
  input  logic       i_clk_schmitt, */
  input  wire        i_pad_ssn_bus_1_clk,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // por_rst_n (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic o_por_rst_n,
  input  logic i_rst_schmitt,
  input  wire  i_pad_por_rst_n,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // pcie_perst_n (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic o_pcie_perst_n,
  /* Port already declared:
  input  logic i_rst_schmitt, */
  input  wire  i_pad_pcie_perst_n,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // trst_n (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic o_trst_n,
  /* Port already declared:
  input  logic i_rst_schmitt, */
  input  wire  i_pad_trst_n,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // uart_rx (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_uart_rx,
  input  logic       i_uart_rx_pd_en,
  input  logic       i_uart_schmitt,
  output logic       o_dft_uart_rx_inp,
  input  logic       i_dft_uart_rx_inp_en,
  input  logic       i_dft_uart_rx_pull_type,
  input  logic       i_dft_uart_rx_pull_en,
  input  logic       i_dft_uart_rx_schmitt,
  input  logic [1:0] i_dft_uart_rx_drive,
  input  wire        i_pad_uart_rx,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // uart_tx (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_uart_tx,
  input  logic [1:0] i_uart_drive,
  input  logic       i_dft_uart_tx_oup,
  input  logic       i_dft_uart_tx_oup_en,
  input  logic       i_dft_uart_tx_pull_type,
  input  logic       i_dft_uart_tx_pull_en,
  input  logic       i_dft_uart_tx_schmitt,
  input  logic [1:0] i_dft_uart_tx_drive,
  output wire        o_pad_uart_tx,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // uart_cts_n (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_uart_cts_n,
  input  logic       i_uart_cts_n_pd_en,
  /* Port already declared:
  input  logic       i_uart_schmitt, */
  output logic       o_dft_uart_cts_n_inp,
  input  logic       i_dft_uart_cts_n_inp_en,
  input  logic       i_dft_uart_cts_n_pull_type,
  input  logic       i_dft_uart_cts_n_pull_en,
  input  logic       i_dft_uart_cts_n_schmitt,
  input  logic [1:0] i_dft_uart_cts_n_drive,
  input  wire        i_pad_uart_cts_n,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // uart_rts_n (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_uart_rts_n,
  /* Port already declared:
  input  logic [1:0] i_uart_drive, */
  input  logic       i_dft_uart_rts_n_oup,
  input  logic       i_dft_uart_rts_n_oup_en,
  input  logic       i_dft_uart_rts_n_pull_type,
  input  logic       i_dft_uart_rts_n_pull_en,
  input  logic       i_dft_uart_rts_n_schmitt,
  input  logic [1:0] i_dft_uart_rts_n_drive,
  output wire        o_pad_uart_rts_n,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // spi_ss_n (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic [3:0] i_spi_ss_n,
  /* Port already declared:
  input  logic [1:0] i_spi_drive, */
  input  logic [3:0] i_dft_spi_ss_n_oup,
  input  logic [3:0] i_dft_spi_ss_n_oup_en,
  input  logic       i_dft_spi_ss_n_pull_type,
  input  logic       i_dft_spi_ss_n_pull_en,
  input  logic       i_dft_spi_ss_n_schmitt,
  input  logic [1:0] i_dft_spi_ss_n_drive,
  output wire  [3:0] o_pad_spi_ss_n,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // spi_sd (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic [3:0] i_spi_sd,
  input  logic [3:0] i_spi_sd_oe_n,
  output logic [3:0] o_spi_sd,
  /* Port already declared:
  input  logic [3:0] i_spi_sd_oe_n, */
  input  logic [3:0] i_spi_sd_pd_en,
  /* Port already declared:
  input  logic [1:0] i_spi_drive, */
  input  logic       i_spi_schmitt,
  input  logic [3:0] i_dft_spi_sd_oup,
  input  logic [3:0] i_dft_spi_sd_oup_en,
  output logic [3:0] o_dft_spi_sd_inp,
  input  logic [3:0] i_dft_spi_sd_inp_en,
  input  logic       i_dft_spi_sd_pull_type,
  input  logic       i_dft_spi_sd_pull_en,
  input  logic       i_dft_spi_sd_schmitt,
  input  logic [1:0] i_dft_spi_sd_drive,
  inout  wire  [3:0] io_pad_spi_sd,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // i2c_0_clk (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_i2c_0_clk_oe,
  output logic       o_i2c_0_clk,
  input  logic [1:0] i_i2c_drive,
  input  logic       i_i2c_schmitt,
  input  logic       i_dft_i2c_0_clk_oup,
  input  logic       i_dft_i2c_0_clk_oup_en,
  output logic       o_dft_i2c_0_clk_inp,
  input  logic       i_dft_i2c_0_clk_inp_en,
  input  logic       i_dft_i2c_0_clk_pull_type,
  input  logic       i_dft_i2c_0_clk_pull_en,
  input  logic       i_dft_i2c_0_clk_schmitt,
  input  logic [1:0] i_dft_i2c_0_clk_drive,
  inout  wire        io_pad_i2c_0_clk,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // i2c_1_clk (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_i2c_1_clk_oe,
  output logic       o_i2c_1_clk,
  /* Port already declared:
  input  logic [1:0] i_i2c_drive, */
  /* Port already declared:
  input  logic       i_i2c_schmitt, */
  input  logic       i_dft_i2c_1_clk_oup,
  input  logic       i_dft_i2c_1_clk_oup_en,
  output logic       o_dft_i2c_1_clk_inp,
  input  logic       i_dft_i2c_1_clk_inp_en,
  input  logic       i_dft_i2c_1_clk_pull_type,
  input  logic       i_dft_i2c_1_clk_pull_en,
  input  logic       i_dft_i2c_1_clk_schmitt,
  input  logic [1:0] i_dft_i2c_1_clk_drive,
  inout  wire        io_pad_i2c_1_clk,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // i2c_0_data (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_i2c_0_data_oe,
  output logic       o_i2c_0_data,
  /* Port already declared:
  input  logic [1:0] i_i2c_drive, */
  /* Port already declared:
  input  logic       i_i2c_schmitt, */
  input  logic       i_dft_i2c_0_data_oup,
  input  logic       i_dft_i2c_0_data_oup_en,
  output logic       o_dft_i2c_0_data_inp,
  input  logic       i_dft_i2c_0_data_inp_en,
  input  logic       i_dft_i2c_0_data_pull_type,
  input  logic       i_dft_i2c_0_data_pull_en,
  input  logic       i_dft_i2c_0_data_schmitt,
  input  logic [1:0] i_dft_i2c_0_data_drive,
  inout  wire        io_pad_i2c_0_data,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // i2c_1_data (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_i2c_1_data_oe,
  output logic       o_i2c_1_data,
  /* Port already declared:
  input  logic [1:0] i_i2c_drive, */
  /* Port already declared:
  input  logic       i_i2c_schmitt, */
  input  logic       i_dft_i2c_1_data_oup,
  input  logic       i_dft_i2c_1_data_oup_en,
  output logic       o_dft_i2c_1_data_inp,
  input  logic       i_dft_i2c_1_data_inp_en,
  input  logic       i_dft_i2c_1_data_pull_type,
  input  logic       i_dft_i2c_1_data_pull_en,
  input  logic       i_dft_i2c_1_data_schmitt,
  input  logic [1:0] i_dft_i2c_1_data_drive,
  inout  wire        io_pad_i2c_1_data,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // gpio (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic [15:0] i_gpio,
  input  logic [15:0] i_gpio_oe,
  output logic [15:0] o_gpio,
  input  logic [15:0] i_gpio_pd_en,
  input  logic [1:0]  i_gpio_drive,
  input  logic        i_gpio_schmitt,
  input  logic [15:0] i_dft_gpio_oup,
  input  logic [15:0] i_dft_gpio_oup_en,
  output logic [15:0] o_dft_gpio_inp,
  input  logic [15:0] i_dft_gpio_inp_en,
  input  logic        i_dft_gpio_pull_type,
  input  logic        i_dft_gpio_pull_en,
  input  logic        i_dft_gpio_schmitt,
  input  logic [1:0]  i_dft_gpio_drive,
  inout  wire  [15:0] io_pad_gpio,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // sd_emmc_cmd (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_sd_emmc_cmd,
  input  logic       i_sd_emmc_cmd_oe,
  output logic       o_sd_emmc_cmd,
  input  logic       i_sd_emmc_cmd_ie,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  inout  wire        io_pad_sd_emmc_cmd,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // sd_emmc_data (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic [7:0] i_sd_emmc_data,
  input  logic [7:0] i_sd_emmc_data_oe,
  output logic [7:0] o_sd_emmc_data,
  input  logic [7:0] i_sd_emmc_data_ie,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  inout  wire  [7:0] io_pad_sd_emmc_data,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // sd_emmc_strobe (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_sd_emmc_strobe,
  input  logic       i_sd_emmc_strobe_ie,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  input  wire        i_pad_sd_emmc_strobe,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // emmc_reset (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_emmc_reset,
  input  logic       i_emmc_reset_oe,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  output wire        o_pad_emmc_reset,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // emmc_power (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_emmc_power,
  input  logic       i_emmc_power_oe,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  output wire        o_pad_emmc_power,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // sd_emmc_detect (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_sd_emmc_detect,
  input  logic       i_sd_emmc_detect_ie,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  output logic       o_dft_sd_emmc_detect_inp,
  input  logic       i_dft_sd_emmc_detect_inp_en,
  input  logic       i_dft_sd_emmc_detect_pull_type,
  input  logic       i_dft_sd_emmc_detect_pull_en,
  input  logic       i_dft_sd_emmc_detect_schmitt,
  input  logic [2:0] i_dft_sd_emmc_detect_drive,
  input  wire        i_pad_sd_emmc_detect,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // sd_emmc_wp (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_sd_emmc_wp,
  input  logic       i_sd_emmc_wp_ie,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  output logic       o_dft_sd_emmc_wp_inp,
  input  logic       i_dft_sd_emmc_wp_inp_en,
  input  logic       i_dft_sd_emmc_wp_pull_type,
  input  logic       i_dft_sd_emmc_wp_pull_en,
  input  logic       i_dft_sd_emmc_wp_schmitt,
  input  logic [2:0] i_dft_sd_emmc_wp_drive,
  input  wire        i_pad_sd_emmc_wp,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // sd_emmc_pu_pd (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_sd_emmc_pu_pd,
  input  logic       i_sd_emmc_pu_pd_oe,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  output wire        o_pad_sd_emmc_pu_pd,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // emmc_rebar (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_emmc_rebar,
  input  logic       i_emmc_rebar_oe,
  output logic       o_emmc_rebar,
  input  logic       i_emmc_rebar_ie,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  inout  wire        io_pad_emmc_rebar,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // emmc_lpbk_dqs (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_emmc_lpbk_dqs,
  input  logic       i_emmc_lpbk_dqs_ie,
  /* Port already declared:
  input  logic [2:0] i_emmc_drive, */
  /* Port already declared:
  input  logic       i_emmc_schmitt, */
  input  wire        i_pad_emmc_lpbk_dqs,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // observability (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic [15:0] i_observability,
  input  logic [1:0]  i_obs_drive,
  input  logic [15:0] i_dft_observability_oup,
  input  logic [15:0] i_dft_observability_oup_en,
  input  logic        i_dft_observability_pull_type,
  input  logic        i_dft_observability_pull_en,
  input  logic        i_dft_observability_schmitt,
  input  logic [1:0]  i_dft_observability_drive,
  output wire  [15:0] o_pad_observability,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // thermal_warning_n (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_thermal_warning_n,
  /* Port already declared:
  input  logic [1:0] i_obs_drive, */
  output wire        o_pad_thermal_warning_n,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // thermal_shutdown_n (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_thermal_shutdown_n,
  /* Port already declared:
  input  logic [1:0] i_obs_drive, */
  output wire        o_pad_thermal_shutdown_n,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // thermal_throttle (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic o_thermal_throttle,
  input  wire  i_pad_thermal_throttle,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // throttle (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic       o_throttle,
  output logic       o_dft_throttle_inp,
  input  logic       i_dft_throttle_inp_en,
  input  logic       i_dft_throttle_pull_type,
  input  logic       i_dft_throttle_pull_en,
  input  logic       i_dft_throttle_schmitt,
  input  logic [1:0] i_dft_throttle_drive,
  input  wire        i_pad_throttle,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // boot_mode (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic [2:0] o_boot_mode,
  input  logic [2:0] i_bootmode_pull_en,
  input  wire  [2:0] i_pad_boot_mode,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // tms (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic o_tms,
  input  wire  i_pad_tms,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // td_in (INPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  output logic o_td,
  input  wire  i_pad_td_in,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // td_out (OUTPUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic       i_td,
  input  logic [1:0] i_jtag_drive,
  output wire        o_pad_td_out,


  //////////////////////////////////////////////////////////////////////////////////////////////////
  // dft_test (INOUT)
  //////////////////////////////////////////////////////////////////////////////////////////////////
  input  logic [44:0] i_dft_test,
  input  logic [44:0] i_dft_test_oe,
  output logic [44:0] o_dft_test,
  input  logic        i_dft_pull_en,
  input  logic        i_dft_pull_type,
  /* Port already declared:
  input  logic [1:0]  i_dft_drive, */
  input  logic        i_dft_schmitt,
  inout  wire  [44:0] io_pad_dft_test,

  input logic i_dft_enable
);
  //////////////////////////////
  // Power Pad Instantiations //
  //////////////////////////////
  localparam int unsigned NUM_PAD_ROWS = 2;

  // Note one can not declare a wire in s struct, however declare it when decalred.
  wire axe_tcl_pad_pkg::impl_pwr_t impl_power[NUM_PAD_ROWS];

  for (genvar pad_row_idx = 0; unsigned'(pad_row_idx) < NUM_PAD_ROWS; pad_row_idx++) begin : gen_rows
    for (genvar power_pad_idx = 0; unsigned'(power_pad_idx) < NumPowerPadsPerRow; power_pad_idx++) begin : gen_power
      axe_tcl_pad_power #(
        .ImplementationKey("vertical"),
        .impl_inp_t       (logic), // Not used
        .impl_oup_t       (axe_tcl_pad_pkg::impl_pwr_t)
      ) u_pad_power (
        .i_impl(1'b0), // Not used
        .o_impl(impl_power[pad_row_idx])
      );
    end
  end

  ///////////////////////////////////
  // Oscillator Pad Instantiations //
  ///////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for ref_clk
  //////////////////////////////////////////////////////////////////////////////////////////////////
  axe_tcl_pad_pkg::impl_oscillator_fast_inp_t ref_clk_impl_inp;
  axe_tcl_pad_pkg::impl_oscillator_fast_oup_t ref_clk_impl_oup; // Stubbed

  always_comb ref_clk_impl_inp = '{
    sf:  i_ref_clk_sel_freq,
    poe: 1'b0  // Stubbed
  };

  // Bypass signal, must be mutually exclusive with oscillator enable, bypass is overwrite
  logic ref_clk_oscillation_enable;
  logic ref_clk_bypass;

  always_comb ref_clk_oscillation_enable = ref_clk_bypass ? 1'b0 : 1'b1;

  axe_tcl_pad_oscillator #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_oscillator_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_oscillator_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_ref_clk (
    .o_clk     (o_ref_clk),
    .i_enable  (ref_clk_oscillation_enable),
    .i_test_en (ref_clk_bypass),
    .i_impl    (ref_clk_impl_inp),
    .o_impl    (ref_clk_impl_oup),
    .i_impl_pwr(impl_power[1]),
    .o_pad     (o_pad_ref_clk),
    .i_pad     (i_pad_ref_clk)
  );

  // External pad to control clock bypass
  axe_tcl_pad_pkg::impl_pad_slow_inp_t ref_clk_bypass_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t ref_clk_bypass_impl_oup; // Stubbed

  always_comb ref_clk_bypass_impl_inp = '{
    is:  1'b1,
    ds:  2'b00,
    poe: 1'b0
  };

  logic ref_clk_pull_type;
  logic ref_clk_pull_en;

  // By default have the pad pull itself down such that the oscillator is in oscillating mode.
  always_comb ref_clk_pull_type = 1'b0;
  always_comb ref_clk_pull_en   = 1'b1;

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_ref_clk_bypass (
    .o_inp      (ref_clk_bypass),
    .i_inp_en   (1'b1),
    .i_pull_type(ref_clk_pull_type),
    .i_pull_en  (ref_clk_pull_en),
    .i_impl     (ref_clk_bypass_impl_inp),
    .o_impl     (ref_clk_bypass_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .i_pad      (i_pad_ref_clk_bypass)
  );

  ///////////////////////////////////
  // Functional Pad Instantiations //
  ///////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for tck
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic tck_inp;
  logic tck_inp_en;
  logic tck_pull_type;
  logic tck_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       tck_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       tck_impl_oup; // Stubbed
  always_comb o_tck = tck_inp;
  always_comb tck_inp_en    = 1'b1;
  always_comb tck_pull_type = 1'b0;
  always_comb tck_pull_en   = 1'b0;

  always_comb tck_impl_inp = '{
    is:  i_clk_schmitt,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_tck (
    .o_inp      (tck_inp),
    .i_inp_en   (tck_inp_en),
    .i_pull_type(tck_pull_type),
    .i_pull_en  (tck_pull_en),
    .i_impl     (tck_impl_inp),
    .o_impl     (tck_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_tck)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for spi_clk_out
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic spi_clk_out_oup;
  logic spi_clk_out_oup_en;
  logic spi_clk_out_pull_type;
  logic spi_clk_out_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       spi_clk_out_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       spi_clk_out_impl_oup; // Stubbed
  always_comb spi_clk_out_oup       = i_spi_clk;
  always_comb spi_clk_out_oup_en    = 1'b1;
  always_comb spi_clk_out_pull_type = 1'b0;
  always_comb spi_clk_out_pull_en   = 1'b0;

  always_comb spi_clk_out_impl_inp = '{
    is:  1'b0,
    ds:  i_spi_drive,
    poe: 1'b0
  };

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_spi_clk_out (
    .i_oup      (spi_clk_out_oup),
    .i_oup_en   (spi_clk_out_oup_en),
    .i_pull_type(spi_clk_out_pull_type),
    .i_pull_en  (spi_clk_out_pull_en),
    .i_impl     (spi_clk_out_impl_inp),
    .o_impl     (spi_clk_out_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_spi_clk_out)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for sd_emmc_clk_out
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_clk_out_oup;
  logic sd_emmc_clk_out_oup_en;
  logic sd_emmc_clk_out_pull_type;
  logic sd_emmc_clk_out_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_clk_out_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_clk_out_impl_oup; // Stubbed
  always_comb sd_emmc_clk_out_oup       = i_sd_emmc_clk;
  always_comb sd_emmc_clk_out_oup_en    = (1'b1 ^ i_sd_emmc_clk_oe);
  always_comb sd_emmc_clk_out_pull_type = 1'b0;
  always_comb sd_emmc_clk_out_pull_en   = 1'b0;

  always_comb sd_emmc_clk_out_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_output #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_sd_emmc_clk_out (
    .i_oup      (sd_emmc_clk_out_oup),
    .i_oup_en   (sd_emmc_clk_out_oup_en),
    .i_pull_type(sd_emmc_clk_out_pull_type),
    .i_pull_en  (sd_emmc_clk_out_pull_en),
    .i_impl     (sd_emmc_clk_out_impl_inp),
    .o_impl     (sd_emmc_clk_out_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_sd_emmc_clk_out)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for ssn_bus_0_clk
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic ssn_bus_0_clk_inp;
  logic ssn_bus_0_clk_inp_en;
  logic ssn_bus_0_clk_pull_type;
  logic ssn_bus_0_clk_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       ssn_bus_0_clk_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       ssn_bus_0_clk_impl_oup; // Stubbed
  always_comb o_ssn_bus_0_clk = ssn_bus_0_clk_inp;
  always_comb ssn_bus_0_clk_inp_en    = 1'b1;
  always_comb ssn_bus_0_clk_pull_type = 1'b0;
  always_comb ssn_bus_0_clk_pull_en   = i_dft_pulldown;

  always_comb ssn_bus_0_clk_impl_inp = '{
    is:  i_clk_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_ssn_bus_0_clk (
    .o_inp      (ssn_bus_0_clk_inp),
    .i_inp_en   (ssn_bus_0_clk_inp_en),
    .i_pull_type(ssn_bus_0_clk_pull_type),
    .i_pull_en  (ssn_bus_0_clk_pull_en),
    .i_impl     (ssn_bus_0_clk_impl_inp),
    .o_impl     (ssn_bus_0_clk_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .i_pad      (i_pad_ssn_bus_0_clk)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for ssn_bus_1_clk
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic ssn_bus_1_clk_inp;
  logic ssn_bus_1_clk_inp_en;
  logic ssn_bus_1_clk_pull_type;
  logic ssn_bus_1_clk_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       ssn_bus_1_clk_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       ssn_bus_1_clk_impl_oup; // Stubbed
  always_comb o_ssn_bus_1_clk = ssn_bus_1_clk_inp;
  always_comb ssn_bus_1_clk_inp_en    = 1'b1;
  always_comb ssn_bus_1_clk_pull_type = 1'b0;
  always_comb ssn_bus_1_clk_pull_en   = i_dft_pulldown;

  always_comb ssn_bus_1_clk_impl_inp = '{
    is:  i_clk_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_ssn_bus_1_clk (
    .o_inp      (ssn_bus_1_clk_inp),
    .i_inp_en   (ssn_bus_1_clk_inp_en),
    .i_pull_type(ssn_bus_1_clk_pull_type),
    .i_pull_en  (ssn_bus_1_clk_pull_en),
    .i_impl     (ssn_bus_1_clk_impl_inp),
    .o_impl     (ssn_bus_1_clk_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_ssn_bus_1_clk)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for por_rst_n
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic por_rst_n_inp;
  logic por_rst_n_inp_en;
  logic por_rst_n_pull_type;
  logic por_rst_n_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       por_rst_n_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       por_rst_n_impl_oup; // Stubbed
  always_comb o_por_rst_n = por_rst_n_inp;
  always_comb por_rst_n_inp_en    = 1'b1;
  always_comb por_rst_n_pull_type = 1'b0;
  always_comb por_rst_n_pull_en   = 1'b0;

  always_comb por_rst_n_impl_inp = '{
    is:  i_rst_schmitt,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_por_rst_n (
    .o_inp      (por_rst_n_inp),
    .i_inp_en   (por_rst_n_inp_en),
    .i_pull_type(por_rst_n_pull_type),
    .i_pull_en  (por_rst_n_pull_en),
    .i_impl     (por_rst_n_impl_inp),
    .o_impl     (por_rst_n_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_por_rst_n)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for pcie_perst_n
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic pcie_perst_n_inp;
  logic pcie_perst_n_inp_en;
  logic pcie_perst_n_pull_type;
  logic pcie_perst_n_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       pcie_perst_n_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       pcie_perst_n_impl_oup; // Stubbed
  always_comb o_pcie_perst_n = pcie_perst_n_inp;
  always_comb pcie_perst_n_inp_en    = 1'b1;
  always_comb pcie_perst_n_pull_type = 1'b0;
  always_comb pcie_perst_n_pull_en   = 1'b0;

  always_comb pcie_perst_n_impl_inp = '{
    is:  i_rst_schmitt,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_pcie_perst_n (
    .o_inp      (pcie_perst_n_inp),
    .i_inp_en   (pcie_perst_n_inp_en),
    .i_pull_type(pcie_perst_n_pull_type),
    .i_pull_en  (pcie_perst_n_pull_en),
    .i_impl     (pcie_perst_n_impl_inp),
    .o_impl     (pcie_perst_n_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_pcie_perst_n)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for trst_n
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic trst_n_inp;
  logic trst_n_inp_en;
  logic trst_n_pull_type;
  logic trst_n_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       trst_n_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       trst_n_impl_oup; // Stubbed
  always_comb o_trst_n = trst_n_inp;
  always_comb trst_n_inp_en    = 1'b1;
  always_comb trst_n_pull_type = 1'b0;
  always_comb trst_n_pull_en   = 1'b0;

  always_comb trst_n_impl_inp = '{
    is:  i_rst_schmitt,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_trst_n (
    .o_inp      (trst_n_inp),
    .i_inp_en   (trst_n_inp_en),
    .i_pull_type(trst_n_pull_type),
    .i_pull_en  (trst_n_pull_en),
    .i_impl     (trst_n_impl_inp),
    .o_impl     (trst_n_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .i_pad      (i_pad_trst_n)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for uart_rx
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic uart_rx_inp;
  logic uart_rx_inp_en;
  logic uart_rx_pull_type;
  logic uart_rx_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       uart_rx_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       uart_rx_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] uart_rx_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] uart_rx_impl_oup_mux; // Stubbed

  always_comb begin
    uart_rx_impl_inp_mux[0] = '{
      is:  i_uart_schmitt,
      ds:  '0,
      poe: 1'b0  // Stubbed
    };
    uart_rx_impl_inp_mux[1] = '{
      is:  i_dft_uart_rx_schmitt,
      ds:  i_dft_uart_rx_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_input #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_input_uart_rx_dft_mux (
    .i_dft_enable,
    .o_func_inp          (o_uart_rx),
    .i_func_inp_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_uart_rx_pd_en),
    .i_func_impl_inp     (uart_rx_impl_inp_mux[0]),
    .o_func_impl_oup     (uart_rx_impl_oup_mux[0]),
    .o_dft_inp           (o_dft_uart_rx_inp),
    .i_dft_inp_en        (i_dft_uart_rx_inp_en),
    .i_dft_pull_type     (i_dft_uart_rx_pull_type),
    .i_dft_pull_en       (i_dft_uart_rx_pull_en),
    .i_dft_impl_inp      (uart_rx_impl_inp_mux[1]),
    .o_dft_impl_oup      (uart_rx_impl_oup_mux[1]),
    .i_padside_inp       (uart_rx_inp),
    .o_padside_inp_en    (uart_rx_inp_en),
    .o_padside_pull_type (uart_rx_pull_type),
    .o_padside_pull_en   (uart_rx_pull_en),
    .o_padside_impl_inp  (uart_rx_impl_inp),
    .i_padside_impl_oup  (uart_rx_impl_oup)
  );

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_uart_rx (
    .o_inp      (uart_rx_inp),
    .i_inp_en   (uart_rx_inp_en),
    .i_pull_type(uart_rx_pull_type),
    .i_pull_en  (uart_rx_pull_en),
    .i_impl     (uart_rx_impl_inp),
    .o_impl     (uart_rx_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_uart_rx)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for uart_tx
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic uart_tx_oup;
  logic uart_tx_oup_en;
  logic uart_tx_pull_type;
  logic uart_tx_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       uart_tx_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       uart_tx_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] uart_tx_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] uart_tx_impl_oup_mux; // Stubbed

  always_comb begin
    uart_tx_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_uart_drive,
      poe: 1'b0  // Stubbed
    };
    uart_tx_impl_inp_mux[1] = '{
      is:  i_dft_uart_tx_schmitt,
      ds:  i_dft_uart_tx_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_uart_tx_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_uart_tx),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (uart_tx_impl_inp_mux[0]),
    .o_func_impl_oup     (uart_tx_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_uart_tx_oup),
    .i_dft_oup_en        (i_dft_uart_tx_oup_en),
    .i_dft_pull_type     (i_dft_uart_tx_pull_type),
    .i_dft_pull_en       (i_dft_uart_tx_pull_en),
    .i_dft_impl_inp      (uart_tx_impl_inp_mux[1]),
    .o_dft_impl_oup      (uart_tx_impl_oup_mux[1]),
    .o_padside_oup       (uart_tx_oup),
    .o_padside_oup_en    (uart_tx_oup_en),
    .o_padside_pull_type (uart_tx_pull_type),
    .o_padside_pull_en   (uart_tx_pull_en),
    .o_padside_impl_inp  (uart_tx_impl_inp),
    .i_padside_impl_oup  (uart_tx_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_uart_tx (
    .i_oup      (uart_tx_oup),
    .i_oup_en   (uart_tx_oup_en),
    .i_pull_type(uart_tx_pull_type),
    .i_pull_en  (uart_tx_pull_en),
    .i_impl     (uart_tx_impl_inp),
    .o_impl     (uart_tx_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_uart_tx)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for uart_cts_n
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic uart_cts_n_inp;
  logic uart_cts_n_inp_en;
  logic uart_cts_n_pull_type;
  logic uart_cts_n_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       uart_cts_n_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       uart_cts_n_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] uart_cts_n_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] uart_cts_n_impl_oup_mux; // Stubbed

  always_comb begin
    uart_cts_n_impl_inp_mux[0] = '{
      is:  i_uart_schmitt,
      ds:  '0,
      poe: 1'b0  // Stubbed
    };
    uart_cts_n_impl_inp_mux[1] = '{
      is:  i_dft_uart_cts_n_schmitt,
      ds:  i_dft_uart_cts_n_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_input #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_input_uart_cts_n_dft_mux (
    .i_dft_enable,
    .o_func_inp          (o_uart_cts_n),
    .i_func_inp_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_uart_cts_n_pd_en),
    .i_func_impl_inp     (uart_cts_n_impl_inp_mux[0]),
    .o_func_impl_oup     (uart_cts_n_impl_oup_mux[0]),
    .o_dft_inp           (o_dft_uart_cts_n_inp),
    .i_dft_inp_en        (i_dft_uart_cts_n_inp_en),
    .i_dft_pull_type     (i_dft_uart_cts_n_pull_type),
    .i_dft_pull_en       (i_dft_uart_cts_n_pull_en),
    .i_dft_impl_inp      (uart_cts_n_impl_inp_mux[1]),
    .o_dft_impl_oup      (uart_cts_n_impl_oup_mux[1]),
    .i_padside_inp       (uart_cts_n_inp),
    .o_padside_inp_en    (uart_cts_n_inp_en),
    .o_padside_pull_type (uart_cts_n_pull_type),
    .o_padside_pull_en   (uart_cts_n_pull_en),
    .o_padside_impl_inp  (uart_cts_n_impl_inp),
    .i_padside_impl_oup  (uart_cts_n_impl_oup)
  );

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_uart_cts_n (
    .o_inp      (uart_cts_n_inp),
    .i_inp_en   (uart_cts_n_inp_en),
    .i_pull_type(uart_cts_n_pull_type),
    .i_pull_en  (uart_cts_n_pull_en),
    .i_impl     (uart_cts_n_impl_inp),
    .o_impl     (uart_cts_n_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_uart_cts_n)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for uart_rts_n
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic uart_rts_n_oup;
  logic uart_rts_n_oup_en;
  logic uart_rts_n_pull_type;
  logic uart_rts_n_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       uart_rts_n_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       uart_rts_n_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] uart_rts_n_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] uart_rts_n_impl_oup_mux; // Stubbed

  always_comb begin
    uart_rts_n_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_uart_drive,
      poe: 1'b0  // Stubbed
    };
    uart_rts_n_impl_inp_mux[1] = '{
      is:  i_dft_uart_rts_n_schmitt,
      ds:  i_dft_uart_rts_n_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_uart_rts_n_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_uart_rts_n),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (uart_rts_n_impl_inp_mux[0]),
    .o_func_impl_oup     (uart_rts_n_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_uart_rts_n_oup),
    .i_dft_oup_en        (i_dft_uart_rts_n_oup_en),
    .i_dft_pull_type     (i_dft_uart_rts_n_pull_type),
    .i_dft_pull_en       (i_dft_uart_rts_n_pull_en),
    .i_dft_impl_inp      (uart_rts_n_impl_inp_mux[1]),
    .o_dft_impl_oup      (uart_rts_n_impl_oup_mux[1]),
    .o_padside_oup       (uart_rts_n_oup),
    .o_padside_oup_en    (uart_rts_n_oup_en),
    .o_padside_pull_type (uart_rts_n_pull_type),
    .o_padside_pull_en   (uart_rts_n_pull_en),
    .o_padside_impl_inp  (uart_rts_n_impl_inp),
    .i_padside_impl_oup  (uart_rts_n_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_uart_rts_n (
    .i_oup      (uart_rts_n_oup),
    .i_oup_en   (uart_rts_n_oup_en),
    .i_pull_type(uart_rts_n_pull_type),
    .i_pull_en  (uart_rts_n_pull_en),
    .i_impl     (uart_rts_n_impl_inp),
    .o_impl     (uart_rts_n_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_uart_rts_n)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for spi_ss_n[3]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic spi_ss_n_3_oup;
  logic spi_ss_n_3_oup_en;
  logic spi_ss_n_3_pull_type;
  logic spi_ss_n_3_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       spi_ss_n_3_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       spi_ss_n_3_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] spi_ss_n_3_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] spi_ss_n_3_impl_oup_mux; // Stubbed

  always_comb begin
    spi_ss_n_3_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_spi_drive,
      poe: 1'b0  // Stubbed
    };
    spi_ss_n_3_impl_inp_mux[1] = '{
      is:  i_dft_spi_ss_n_schmitt,
      ds:  i_dft_spi_ss_n_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_spi_ss_n_3_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_spi_ss_n[3]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (spi_ss_n_3_impl_inp_mux[0]),
    .o_func_impl_oup     (spi_ss_n_3_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_spi_ss_n_oup[3]),
    .i_dft_oup_en        (i_dft_spi_ss_n_oup_en[3]),
    .i_dft_pull_type     (i_dft_spi_ss_n_pull_type),
    .i_dft_pull_en       (i_dft_spi_ss_n_pull_en),
    .i_dft_impl_inp      (spi_ss_n_3_impl_inp_mux[1]),
    .o_dft_impl_oup      (spi_ss_n_3_impl_oup_mux[1]),
    .o_padside_oup       (spi_ss_n_3_oup),
    .o_padside_oup_en    (spi_ss_n_3_oup_en),
    .o_padside_pull_type (spi_ss_n_3_pull_type),
    .o_padside_pull_en   (spi_ss_n_3_pull_en),
    .o_padside_impl_inp  (spi_ss_n_3_impl_inp),
    .i_padside_impl_oup  (spi_ss_n_3_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_spi_ss_n_3 (
    .i_oup      (spi_ss_n_3_oup),
    .i_oup_en   (spi_ss_n_3_oup_en),
    .i_pull_type(spi_ss_n_3_pull_type),
    .i_pull_en  (spi_ss_n_3_pull_en),
    .i_impl     (spi_ss_n_3_impl_inp),
    .o_impl     (spi_ss_n_3_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_spi_ss_n[3])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for spi_ss_n[2]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic spi_ss_n_2_oup;
  logic spi_ss_n_2_oup_en;
  logic spi_ss_n_2_pull_type;
  logic spi_ss_n_2_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       spi_ss_n_2_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       spi_ss_n_2_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] spi_ss_n_2_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] spi_ss_n_2_impl_oup_mux; // Stubbed

  always_comb begin
    spi_ss_n_2_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_spi_drive,
      poe: 1'b0  // Stubbed
    };
    spi_ss_n_2_impl_inp_mux[1] = '{
      is:  i_dft_spi_ss_n_schmitt,
      ds:  i_dft_spi_ss_n_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_spi_ss_n_2_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_spi_ss_n[2]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (spi_ss_n_2_impl_inp_mux[0]),
    .o_func_impl_oup     (spi_ss_n_2_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_spi_ss_n_oup[2]),
    .i_dft_oup_en        (i_dft_spi_ss_n_oup_en[2]),
    .i_dft_pull_type     (i_dft_spi_ss_n_pull_type),
    .i_dft_pull_en       (i_dft_spi_ss_n_pull_en),
    .i_dft_impl_inp      (spi_ss_n_2_impl_inp_mux[1]),
    .o_dft_impl_oup      (spi_ss_n_2_impl_oup_mux[1]),
    .o_padside_oup       (spi_ss_n_2_oup),
    .o_padside_oup_en    (spi_ss_n_2_oup_en),
    .o_padside_pull_type (spi_ss_n_2_pull_type),
    .o_padside_pull_en   (spi_ss_n_2_pull_en),
    .o_padside_impl_inp  (spi_ss_n_2_impl_inp),
    .i_padside_impl_oup  (spi_ss_n_2_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_spi_ss_n_2 (
    .i_oup      (spi_ss_n_2_oup),
    .i_oup_en   (spi_ss_n_2_oup_en),
    .i_pull_type(spi_ss_n_2_pull_type),
    .i_pull_en  (spi_ss_n_2_pull_en),
    .i_impl     (spi_ss_n_2_impl_inp),
    .o_impl     (spi_ss_n_2_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_spi_ss_n[2])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for spi_ss_n[1]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic spi_ss_n_1_oup;
  logic spi_ss_n_1_oup_en;
  logic spi_ss_n_1_pull_type;
  logic spi_ss_n_1_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       spi_ss_n_1_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       spi_ss_n_1_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] spi_ss_n_1_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] spi_ss_n_1_impl_oup_mux; // Stubbed

  always_comb begin
    spi_ss_n_1_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_spi_drive,
      poe: 1'b0  // Stubbed
    };
    spi_ss_n_1_impl_inp_mux[1] = '{
      is:  i_dft_spi_ss_n_schmitt,
      ds:  i_dft_spi_ss_n_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_spi_ss_n_1_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_spi_ss_n[1]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (spi_ss_n_1_impl_inp_mux[0]),
    .o_func_impl_oup     (spi_ss_n_1_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_spi_ss_n_oup[1]),
    .i_dft_oup_en        (i_dft_spi_ss_n_oup_en[1]),
    .i_dft_pull_type     (i_dft_spi_ss_n_pull_type),
    .i_dft_pull_en       (i_dft_spi_ss_n_pull_en),
    .i_dft_impl_inp      (spi_ss_n_1_impl_inp_mux[1]),
    .o_dft_impl_oup      (spi_ss_n_1_impl_oup_mux[1]),
    .o_padside_oup       (spi_ss_n_1_oup),
    .o_padside_oup_en    (spi_ss_n_1_oup_en),
    .o_padside_pull_type (spi_ss_n_1_pull_type),
    .o_padside_pull_en   (spi_ss_n_1_pull_en),
    .o_padside_impl_inp  (spi_ss_n_1_impl_inp),
    .i_padside_impl_oup  (spi_ss_n_1_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_spi_ss_n_1 (
    .i_oup      (spi_ss_n_1_oup),
    .i_oup_en   (spi_ss_n_1_oup_en),
    .i_pull_type(spi_ss_n_1_pull_type),
    .i_pull_en  (spi_ss_n_1_pull_en),
    .i_impl     (spi_ss_n_1_impl_inp),
    .o_impl     (spi_ss_n_1_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_spi_ss_n[1])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for spi_ss_n[0]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic spi_ss_n_0_oup;
  logic spi_ss_n_0_oup_en;
  logic spi_ss_n_0_pull_type;
  logic spi_ss_n_0_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       spi_ss_n_0_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       spi_ss_n_0_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] spi_ss_n_0_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] spi_ss_n_0_impl_oup_mux; // Stubbed

  always_comb begin
    spi_ss_n_0_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_spi_drive,
      poe: 1'b0  // Stubbed
    };
    spi_ss_n_0_impl_inp_mux[1] = '{
      is:  i_dft_spi_ss_n_schmitt,
      ds:  i_dft_spi_ss_n_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_spi_ss_n_0_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_spi_ss_n[0]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (spi_ss_n_0_impl_inp_mux[0]),
    .o_func_impl_oup     (spi_ss_n_0_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_spi_ss_n_oup[0]),
    .i_dft_oup_en        (i_dft_spi_ss_n_oup_en[0]),
    .i_dft_pull_type     (i_dft_spi_ss_n_pull_type),
    .i_dft_pull_en       (i_dft_spi_ss_n_pull_en),
    .i_dft_impl_inp      (spi_ss_n_0_impl_inp_mux[1]),
    .o_dft_impl_oup      (spi_ss_n_0_impl_oup_mux[1]),
    .o_padside_oup       (spi_ss_n_0_oup),
    .o_padside_oup_en    (spi_ss_n_0_oup_en),
    .o_padside_pull_type (spi_ss_n_0_pull_type),
    .o_padside_pull_en   (spi_ss_n_0_pull_en),
    .o_padside_impl_inp  (spi_ss_n_0_impl_inp),
    .i_padside_impl_oup  (spi_ss_n_0_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_spi_ss_n_0 (
    .i_oup      (spi_ss_n_0_oup),
    .i_oup_en   (spi_ss_n_0_oup_en),
    .i_pull_type(spi_ss_n_0_pull_type),
    .i_pull_en  (spi_ss_n_0_pull_en),
    .i_impl     (spi_ss_n_0_impl_inp),
    .o_impl     (spi_ss_n_0_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_spi_ss_n[0])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for spi_sd[3]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic spi_sd_3_oup;
  logic spi_sd_3_oup_en;
  logic spi_sd_3_inp;
  logic spi_sd_3_inp_en;
  logic spi_sd_3_pull_type;
  logic spi_sd_3_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       spi_sd_3_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       spi_sd_3_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] spi_sd_3_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] spi_sd_3_impl_oup_mux; // Stubbed

  always_comb begin
    spi_sd_3_impl_inp_mux[0] = '{
      is:  i_spi_schmitt,
      ds:  i_spi_drive,
      poe: 1'b0  // Stubbed
    };
    spi_sd_3_impl_inp_mux[1] = '{
      is:  i_dft_spi_sd_schmitt,
      ds:  i_dft_spi_sd_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_spi_sd_3_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_spi_sd[3]),
    .i_func_oup_en       ((1'b1 ^ i_spi_sd_oe_n[3])),
    .o_func_inp          (o_spi_sd[3]),
    .i_func_inp_en       (i_spi_sd_oe_n[3]),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_spi_sd_pd_en[3]),
    .i_func_impl_inp     (spi_sd_3_impl_inp_mux[0]),
    .o_func_impl_oup     (spi_sd_3_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_spi_sd_oup[3]),
    .i_dft_oup_en        (i_dft_spi_sd_oup_en[3]),
    .o_dft_inp           (o_dft_spi_sd_inp[3]),
    .i_dft_inp_en        (i_dft_spi_sd_inp_en[3]),
    .i_dft_pull_type     (i_dft_spi_sd_pull_type),
    .i_dft_pull_en       (i_dft_spi_sd_pull_en),
    .i_dft_impl_inp      (spi_sd_3_impl_inp_mux[1]),
    .o_dft_impl_oup      (spi_sd_3_impl_oup_mux[1]),
    .o_padside_oup       (spi_sd_3_oup),
    .o_padside_oup_en    (spi_sd_3_oup_en),
    .i_padside_inp       (spi_sd_3_inp),
    .o_padside_inp_en    (spi_sd_3_inp_en),
    .o_padside_pull_type (spi_sd_3_pull_type),
    .o_padside_pull_en   (spi_sd_3_pull_en),
    .o_padside_impl_inp  (spi_sd_3_impl_inp),
    .i_padside_impl_oup  (spi_sd_3_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_spi_sd_3 (
    .i_oup      (spi_sd_3_oup),
    .i_oup_en   (spi_sd_3_oup_en),
    .o_inp      (spi_sd_3_inp),
    .i_inp_en   (spi_sd_3_inp_en),
    .i_pull_type(spi_sd_3_pull_type),
    .i_pull_en  (spi_sd_3_pull_en),
    .i_impl     (spi_sd_3_impl_inp),
    .o_impl     (spi_sd_3_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_spi_sd[3])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for spi_sd[2]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic spi_sd_2_oup;
  logic spi_sd_2_oup_en;
  logic spi_sd_2_inp;
  logic spi_sd_2_inp_en;
  logic spi_sd_2_pull_type;
  logic spi_sd_2_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       spi_sd_2_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       spi_sd_2_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] spi_sd_2_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] spi_sd_2_impl_oup_mux; // Stubbed

  always_comb begin
    spi_sd_2_impl_inp_mux[0] = '{
      is:  i_spi_schmitt,
      ds:  i_spi_drive,
      poe: 1'b0  // Stubbed
    };
    spi_sd_2_impl_inp_mux[1] = '{
      is:  i_dft_spi_sd_schmitt,
      ds:  i_dft_spi_sd_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_spi_sd_2_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_spi_sd[2]),
    .i_func_oup_en       ((1'b1 ^ i_spi_sd_oe_n[2])),
    .o_func_inp          (o_spi_sd[2]),
    .i_func_inp_en       (i_spi_sd_oe_n[2]),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_spi_sd_pd_en[2]),
    .i_func_impl_inp     (spi_sd_2_impl_inp_mux[0]),
    .o_func_impl_oup     (spi_sd_2_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_spi_sd_oup[2]),
    .i_dft_oup_en        (i_dft_spi_sd_oup_en[2]),
    .o_dft_inp           (o_dft_spi_sd_inp[2]),
    .i_dft_inp_en        (i_dft_spi_sd_inp_en[2]),
    .i_dft_pull_type     (i_dft_spi_sd_pull_type),
    .i_dft_pull_en       (i_dft_spi_sd_pull_en),
    .i_dft_impl_inp      (spi_sd_2_impl_inp_mux[1]),
    .o_dft_impl_oup      (spi_sd_2_impl_oup_mux[1]),
    .o_padside_oup       (spi_sd_2_oup),
    .o_padside_oup_en    (spi_sd_2_oup_en),
    .i_padside_inp       (spi_sd_2_inp),
    .o_padside_inp_en    (spi_sd_2_inp_en),
    .o_padside_pull_type (spi_sd_2_pull_type),
    .o_padside_pull_en   (spi_sd_2_pull_en),
    .o_padside_impl_inp  (spi_sd_2_impl_inp),
    .i_padside_impl_oup  (spi_sd_2_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_spi_sd_2 (
    .i_oup      (spi_sd_2_oup),
    .i_oup_en   (spi_sd_2_oup_en),
    .o_inp      (spi_sd_2_inp),
    .i_inp_en   (spi_sd_2_inp_en),
    .i_pull_type(spi_sd_2_pull_type),
    .i_pull_en  (spi_sd_2_pull_en),
    .i_impl     (spi_sd_2_impl_inp),
    .o_impl     (spi_sd_2_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_spi_sd[2])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for spi_sd[1]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic spi_sd_1_oup;
  logic spi_sd_1_oup_en;
  logic spi_sd_1_inp;
  logic spi_sd_1_inp_en;
  logic spi_sd_1_pull_type;
  logic spi_sd_1_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       spi_sd_1_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       spi_sd_1_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] spi_sd_1_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] spi_sd_1_impl_oup_mux; // Stubbed

  always_comb begin
    spi_sd_1_impl_inp_mux[0] = '{
      is:  i_spi_schmitt,
      ds:  i_spi_drive,
      poe: 1'b0  // Stubbed
    };
    spi_sd_1_impl_inp_mux[1] = '{
      is:  i_dft_spi_sd_schmitt,
      ds:  i_dft_spi_sd_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_spi_sd_1_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_spi_sd[1]),
    .i_func_oup_en       ((1'b1 ^ i_spi_sd_oe_n[1])),
    .o_func_inp          (o_spi_sd[1]),
    .i_func_inp_en       (i_spi_sd_oe_n[1]),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_spi_sd_pd_en[1]),
    .i_func_impl_inp     (spi_sd_1_impl_inp_mux[0]),
    .o_func_impl_oup     (spi_sd_1_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_spi_sd_oup[1]),
    .i_dft_oup_en        (i_dft_spi_sd_oup_en[1]),
    .o_dft_inp           (o_dft_spi_sd_inp[1]),
    .i_dft_inp_en        (i_dft_spi_sd_inp_en[1]),
    .i_dft_pull_type     (i_dft_spi_sd_pull_type),
    .i_dft_pull_en       (i_dft_spi_sd_pull_en),
    .i_dft_impl_inp      (spi_sd_1_impl_inp_mux[1]),
    .o_dft_impl_oup      (spi_sd_1_impl_oup_mux[1]),
    .o_padside_oup       (spi_sd_1_oup),
    .o_padside_oup_en    (spi_sd_1_oup_en),
    .i_padside_inp       (spi_sd_1_inp),
    .o_padside_inp_en    (spi_sd_1_inp_en),
    .o_padside_pull_type (spi_sd_1_pull_type),
    .o_padside_pull_en   (spi_sd_1_pull_en),
    .o_padside_impl_inp  (spi_sd_1_impl_inp),
    .i_padside_impl_oup  (spi_sd_1_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_spi_sd_1 (
    .i_oup      (spi_sd_1_oup),
    .i_oup_en   (spi_sd_1_oup_en),
    .o_inp      (spi_sd_1_inp),
    .i_inp_en   (spi_sd_1_inp_en),
    .i_pull_type(spi_sd_1_pull_type),
    .i_pull_en  (spi_sd_1_pull_en),
    .i_impl     (spi_sd_1_impl_inp),
    .o_impl     (spi_sd_1_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_spi_sd[1])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for spi_sd[0]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic spi_sd_0_oup;
  logic spi_sd_0_oup_en;
  logic spi_sd_0_inp;
  logic spi_sd_0_inp_en;
  logic spi_sd_0_pull_type;
  logic spi_sd_0_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       spi_sd_0_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       spi_sd_0_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] spi_sd_0_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] spi_sd_0_impl_oup_mux; // Stubbed

  always_comb begin
    spi_sd_0_impl_inp_mux[0] = '{
      is:  i_spi_schmitt,
      ds:  i_spi_drive,
      poe: 1'b0  // Stubbed
    };
    spi_sd_0_impl_inp_mux[1] = '{
      is:  i_dft_spi_sd_schmitt,
      ds:  i_dft_spi_sd_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_spi_sd_0_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_spi_sd[0]),
    .i_func_oup_en       ((1'b1 ^ i_spi_sd_oe_n[0])),
    .o_func_inp          (o_spi_sd[0]),
    .i_func_inp_en       (i_spi_sd_oe_n[0]),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_spi_sd_pd_en[0]),
    .i_func_impl_inp     (spi_sd_0_impl_inp_mux[0]),
    .o_func_impl_oup     (spi_sd_0_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_spi_sd_oup[0]),
    .i_dft_oup_en        (i_dft_spi_sd_oup_en[0]),
    .o_dft_inp           (o_dft_spi_sd_inp[0]),
    .i_dft_inp_en        (i_dft_spi_sd_inp_en[0]),
    .i_dft_pull_type     (i_dft_spi_sd_pull_type),
    .i_dft_pull_en       (i_dft_spi_sd_pull_en),
    .i_dft_impl_inp      (spi_sd_0_impl_inp_mux[1]),
    .o_dft_impl_oup      (spi_sd_0_impl_oup_mux[1]),
    .o_padside_oup       (spi_sd_0_oup),
    .o_padside_oup_en    (spi_sd_0_oup_en),
    .i_padside_inp       (spi_sd_0_inp),
    .o_padside_inp_en    (spi_sd_0_inp_en),
    .o_padside_pull_type (spi_sd_0_pull_type),
    .o_padside_pull_en   (spi_sd_0_pull_en),
    .o_padside_impl_inp  (spi_sd_0_impl_inp),
    .i_padside_impl_oup  (spi_sd_0_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_spi_sd_0 (
    .i_oup      (spi_sd_0_oup),
    .i_oup_en   (spi_sd_0_oup_en),
    .o_inp      (spi_sd_0_inp),
    .i_inp_en   (spi_sd_0_inp_en),
    .i_pull_type(spi_sd_0_pull_type),
    .i_pull_en  (spi_sd_0_pull_en),
    .i_impl     (spi_sd_0_impl_inp),
    .o_impl     (spi_sd_0_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_spi_sd[0])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for i2c_0_clk
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic i2c_0_clk_oup;
  logic i2c_0_clk_oup_en;
  logic i2c_0_clk_inp;
  logic i2c_0_clk_inp_en;
  logic i2c_0_clk_pull_type;
  logic i2c_0_clk_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       i2c_0_clk_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       i2c_0_clk_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] i2c_0_clk_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] i2c_0_clk_impl_oup_mux; // Stubbed

  always_comb begin
    i2c_0_clk_impl_inp_mux[0] = '{
      is:  i_i2c_schmitt,
      ds:  i_i2c_drive,
      poe: 1'b0  // Stubbed
    };
    i2c_0_clk_impl_inp_mux[1] = '{
      is:  i_dft_i2c_0_clk_schmitt,
      ds:  i_dft_i2c_0_clk_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_i2c_0_clk_dft_mux (
    .i_dft_enable,
    .i_func_oup          (1'b0),
    .i_func_oup_en       (i_i2c_0_clk_oe),
    .o_func_inp          (o_i2c_0_clk),
    .i_func_inp_en       ((1'b1 ^ i_i2c_0_clk_oe)),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (i2c_0_clk_impl_inp_mux[0]),
    .o_func_impl_oup     (i2c_0_clk_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_i2c_0_clk_oup),
    .i_dft_oup_en        (i_dft_i2c_0_clk_oup_en),
    .o_dft_inp           (o_dft_i2c_0_clk_inp),
    .i_dft_inp_en        (i_dft_i2c_0_clk_inp_en),
    .i_dft_pull_type     (i_dft_i2c_0_clk_pull_type),
    .i_dft_pull_en       (i_dft_i2c_0_clk_pull_en),
    .i_dft_impl_inp      (i2c_0_clk_impl_inp_mux[1]),
    .o_dft_impl_oup      (i2c_0_clk_impl_oup_mux[1]),
    .o_padside_oup       (i2c_0_clk_oup),
    .o_padside_oup_en    (i2c_0_clk_oup_en),
    .i_padside_inp       (i2c_0_clk_inp),
    .o_padside_inp_en    (i2c_0_clk_inp_en),
    .o_padside_pull_type (i2c_0_clk_pull_type),
    .o_padside_pull_en   (i2c_0_clk_pull_en),
    .o_padside_impl_inp  (i2c_0_clk_impl_inp),
    .i_padside_impl_oup  (i2c_0_clk_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_i2c_0_clk (
    .i_oup      (i2c_0_clk_oup),
    .i_oup_en   (i2c_0_clk_oup_en),
    .o_inp      (i2c_0_clk_inp),
    .i_inp_en   (i2c_0_clk_inp_en),
    .i_pull_type(i2c_0_clk_pull_type),
    .i_pull_en  (i2c_0_clk_pull_en),
    .i_impl     (i2c_0_clk_impl_inp),
    .o_impl     (i2c_0_clk_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_i2c_0_clk)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for i2c_1_clk
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic i2c_1_clk_oup;
  logic i2c_1_clk_oup_en;
  logic i2c_1_clk_inp;
  logic i2c_1_clk_inp_en;
  logic i2c_1_clk_pull_type;
  logic i2c_1_clk_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       i2c_1_clk_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       i2c_1_clk_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] i2c_1_clk_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] i2c_1_clk_impl_oup_mux; // Stubbed

  always_comb begin
    i2c_1_clk_impl_inp_mux[0] = '{
      is:  i_i2c_schmitt,
      ds:  i_i2c_drive,
      poe: 1'b0  // Stubbed
    };
    i2c_1_clk_impl_inp_mux[1] = '{
      is:  i_dft_i2c_1_clk_schmitt,
      ds:  i_dft_i2c_1_clk_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_i2c_1_clk_dft_mux (
    .i_dft_enable,
    .i_func_oup          (1'b0),
    .i_func_oup_en       (i_i2c_1_clk_oe),
    .o_func_inp          (o_i2c_1_clk),
    .i_func_inp_en       ((1'b1 ^ i_i2c_1_clk_oe)),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (i2c_1_clk_impl_inp_mux[0]),
    .o_func_impl_oup     (i2c_1_clk_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_i2c_1_clk_oup),
    .i_dft_oup_en        (i_dft_i2c_1_clk_oup_en),
    .o_dft_inp           (o_dft_i2c_1_clk_inp),
    .i_dft_inp_en        (i_dft_i2c_1_clk_inp_en),
    .i_dft_pull_type     (i_dft_i2c_1_clk_pull_type),
    .i_dft_pull_en       (i_dft_i2c_1_clk_pull_en),
    .i_dft_impl_inp      (i2c_1_clk_impl_inp_mux[1]),
    .o_dft_impl_oup      (i2c_1_clk_impl_oup_mux[1]),
    .o_padside_oup       (i2c_1_clk_oup),
    .o_padside_oup_en    (i2c_1_clk_oup_en),
    .i_padside_inp       (i2c_1_clk_inp),
    .o_padside_inp_en    (i2c_1_clk_inp_en),
    .o_padside_pull_type (i2c_1_clk_pull_type),
    .o_padside_pull_en   (i2c_1_clk_pull_en),
    .o_padside_impl_inp  (i2c_1_clk_impl_inp),
    .i_padside_impl_oup  (i2c_1_clk_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_i2c_1_clk (
    .i_oup      (i2c_1_clk_oup),
    .i_oup_en   (i2c_1_clk_oup_en),
    .o_inp      (i2c_1_clk_inp),
    .i_inp_en   (i2c_1_clk_inp_en),
    .i_pull_type(i2c_1_clk_pull_type),
    .i_pull_en  (i2c_1_clk_pull_en),
    .i_impl     (i2c_1_clk_impl_inp),
    .o_impl     (i2c_1_clk_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_i2c_1_clk)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for i2c_0_data
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic i2c_0_data_oup;
  logic i2c_0_data_oup_en;
  logic i2c_0_data_inp;
  logic i2c_0_data_inp_en;
  logic i2c_0_data_pull_type;
  logic i2c_0_data_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       i2c_0_data_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       i2c_0_data_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] i2c_0_data_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] i2c_0_data_impl_oup_mux; // Stubbed

  always_comb begin
    i2c_0_data_impl_inp_mux[0] = '{
      is:  i_i2c_schmitt,
      ds:  i_i2c_drive,
      poe: 1'b0  // Stubbed
    };
    i2c_0_data_impl_inp_mux[1] = '{
      is:  i_dft_i2c_0_data_schmitt,
      ds:  i_dft_i2c_0_data_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_i2c_0_data_dft_mux (
    .i_dft_enable,
    .i_func_oup          (1'b0),
    .i_func_oup_en       (i_i2c_0_data_oe),
    .o_func_inp          (o_i2c_0_data),
    .i_func_inp_en       ((1'b1 ^ i_i2c_0_data_oe)),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (i2c_0_data_impl_inp_mux[0]),
    .o_func_impl_oup     (i2c_0_data_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_i2c_0_data_oup),
    .i_dft_oup_en        (i_dft_i2c_0_data_oup_en),
    .o_dft_inp           (o_dft_i2c_0_data_inp),
    .i_dft_inp_en        (i_dft_i2c_0_data_inp_en),
    .i_dft_pull_type     (i_dft_i2c_0_data_pull_type),
    .i_dft_pull_en       (i_dft_i2c_0_data_pull_en),
    .i_dft_impl_inp      (i2c_0_data_impl_inp_mux[1]),
    .o_dft_impl_oup      (i2c_0_data_impl_oup_mux[1]),
    .o_padside_oup       (i2c_0_data_oup),
    .o_padside_oup_en    (i2c_0_data_oup_en),
    .i_padside_inp       (i2c_0_data_inp),
    .o_padside_inp_en    (i2c_0_data_inp_en),
    .o_padside_pull_type (i2c_0_data_pull_type),
    .o_padside_pull_en   (i2c_0_data_pull_en),
    .o_padside_impl_inp  (i2c_0_data_impl_inp),
    .i_padside_impl_oup  (i2c_0_data_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_i2c_0_data (
    .i_oup      (i2c_0_data_oup),
    .i_oup_en   (i2c_0_data_oup_en),
    .o_inp      (i2c_0_data_inp),
    .i_inp_en   (i2c_0_data_inp_en),
    .i_pull_type(i2c_0_data_pull_type),
    .i_pull_en  (i2c_0_data_pull_en),
    .i_impl     (i2c_0_data_impl_inp),
    .o_impl     (i2c_0_data_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_i2c_0_data)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for i2c_1_data
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic i2c_1_data_oup;
  logic i2c_1_data_oup_en;
  logic i2c_1_data_inp;
  logic i2c_1_data_inp_en;
  logic i2c_1_data_pull_type;
  logic i2c_1_data_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       i2c_1_data_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       i2c_1_data_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] i2c_1_data_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] i2c_1_data_impl_oup_mux; // Stubbed

  always_comb begin
    i2c_1_data_impl_inp_mux[0] = '{
      is:  i_i2c_schmitt,
      ds:  i_i2c_drive,
      poe: 1'b0  // Stubbed
    };
    i2c_1_data_impl_inp_mux[1] = '{
      is:  i_dft_i2c_1_data_schmitt,
      ds:  i_dft_i2c_1_data_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_i2c_1_data_dft_mux (
    .i_dft_enable,
    .i_func_oup          (1'b0),
    .i_func_oup_en       (i_i2c_1_data_oe),
    .o_func_inp          (o_i2c_1_data),
    .i_func_inp_en       ((1'b1 ^ i_i2c_1_data_oe)),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (i2c_1_data_impl_inp_mux[0]),
    .o_func_impl_oup     (i2c_1_data_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_i2c_1_data_oup),
    .i_dft_oup_en        (i_dft_i2c_1_data_oup_en),
    .o_dft_inp           (o_dft_i2c_1_data_inp),
    .i_dft_inp_en        (i_dft_i2c_1_data_inp_en),
    .i_dft_pull_type     (i_dft_i2c_1_data_pull_type),
    .i_dft_pull_en       (i_dft_i2c_1_data_pull_en),
    .i_dft_impl_inp      (i2c_1_data_impl_inp_mux[1]),
    .o_dft_impl_oup      (i2c_1_data_impl_oup_mux[1]),
    .o_padside_oup       (i2c_1_data_oup),
    .o_padside_oup_en    (i2c_1_data_oup_en),
    .i_padside_inp       (i2c_1_data_inp),
    .o_padside_inp_en    (i2c_1_data_inp_en),
    .o_padside_pull_type (i2c_1_data_pull_type),
    .o_padside_pull_en   (i2c_1_data_pull_en),
    .o_padside_impl_inp  (i2c_1_data_impl_inp),
    .i_padside_impl_oup  (i2c_1_data_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_i2c_1_data (
    .i_oup      (i2c_1_data_oup),
    .i_oup_en   (i2c_1_data_oup_en),
    .o_inp      (i2c_1_data_inp),
    .i_inp_en   (i2c_1_data_inp_en),
    .i_pull_type(i2c_1_data_pull_type),
    .i_pull_en  (i2c_1_data_pull_en),
    .i_impl     (i2c_1_data_impl_inp),
    .o_impl     (i2c_1_data_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_i2c_1_data)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[15]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_15_oup;
  logic gpio_15_oup_en;
  logic gpio_15_inp;
  logic gpio_15_inp_en;
  logic gpio_15_pull_type;
  logic gpio_15_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_15_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_15_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_15_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_15_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_15_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_15_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_15_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[15]),
    .i_func_oup_en       (i_gpio_oe[15]),
    .o_func_inp          (o_gpio[15]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[15])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[15]),
    .i_func_impl_inp     (gpio_15_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_15_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[15]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[15]),
    .o_dft_inp           (o_dft_gpio_inp[15]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[15]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_15_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_15_impl_oup_mux[1]),
    .o_padside_oup       (gpio_15_oup),
    .o_padside_oup_en    (gpio_15_oup_en),
    .i_padside_inp       (gpio_15_inp),
    .o_padside_inp_en    (gpio_15_inp_en),
    .o_padside_pull_type (gpio_15_pull_type),
    .o_padside_pull_en   (gpio_15_pull_en),
    .o_padside_impl_inp  (gpio_15_impl_inp),
    .i_padside_impl_oup  (gpio_15_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_15 (
    .i_oup      (gpio_15_oup),
    .i_oup_en   (gpio_15_oup_en),
    .o_inp      (gpio_15_inp),
    .i_inp_en   (gpio_15_inp_en),
    .i_pull_type(gpio_15_pull_type),
    .i_pull_en  (gpio_15_pull_en),
    .i_impl     (gpio_15_impl_inp),
    .o_impl     (gpio_15_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_gpio[15])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[14]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_14_oup;
  logic gpio_14_oup_en;
  logic gpio_14_inp;
  logic gpio_14_inp_en;
  logic gpio_14_pull_type;
  logic gpio_14_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_14_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_14_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_14_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_14_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_14_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_14_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_14_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[14]),
    .i_func_oup_en       (i_gpio_oe[14]),
    .o_func_inp          (o_gpio[14]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[14])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[14]),
    .i_func_impl_inp     (gpio_14_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_14_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[14]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[14]),
    .o_dft_inp           (o_dft_gpio_inp[14]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[14]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_14_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_14_impl_oup_mux[1]),
    .o_padside_oup       (gpio_14_oup),
    .o_padside_oup_en    (gpio_14_oup_en),
    .i_padside_inp       (gpio_14_inp),
    .o_padside_inp_en    (gpio_14_inp_en),
    .o_padside_pull_type (gpio_14_pull_type),
    .o_padside_pull_en   (gpio_14_pull_en),
    .o_padside_impl_inp  (gpio_14_impl_inp),
    .i_padside_impl_oup  (gpio_14_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_14 (
    .i_oup      (gpio_14_oup),
    .i_oup_en   (gpio_14_oup_en),
    .o_inp      (gpio_14_inp),
    .i_inp_en   (gpio_14_inp_en),
    .i_pull_type(gpio_14_pull_type),
    .i_pull_en  (gpio_14_pull_en),
    .i_impl     (gpio_14_impl_inp),
    .o_impl     (gpio_14_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_gpio[14])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[13]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_13_oup;
  logic gpio_13_oup_en;
  logic gpio_13_inp;
  logic gpio_13_inp_en;
  logic gpio_13_pull_type;
  logic gpio_13_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_13_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_13_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_13_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_13_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_13_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_13_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_13_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[13]),
    .i_func_oup_en       (i_gpio_oe[13]),
    .o_func_inp          (o_gpio[13]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[13])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[13]),
    .i_func_impl_inp     (gpio_13_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_13_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[13]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[13]),
    .o_dft_inp           (o_dft_gpio_inp[13]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[13]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_13_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_13_impl_oup_mux[1]),
    .o_padside_oup       (gpio_13_oup),
    .o_padside_oup_en    (gpio_13_oup_en),
    .i_padside_inp       (gpio_13_inp),
    .o_padside_inp_en    (gpio_13_inp_en),
    .o_padside_pull_type (gpio_13_pull_type),
    .o_padside_pull_en   (gpio_13_pull_en),
    .o_padside_impl_inp  (gpio_13_impl_inp),
    .i_padside_impl_oup  (gpio_13_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_13 (
    .i_oup      (gpio_13_oup),
    .i_oup_en   (gpio_13_oup_en),
    .o_inp      (gpio_13_inp),
    .i_inp_en   (gpio_13_inp_en),
    .i_pull_type(gpio_13_pull_type),
    .i_pull_en  (gpio_13_pull_en),
    .i_impl     (gpio_13_impl_inp),
    .o_impl     (gpio_13_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_gpio[13])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[12]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_12_oup;
  logic gpio_12_oup_en;
  logic gpio_12_inp;
  logic gpio_12_inp_en;
  logic gpio_12_pull_type;
  logic gpio_12_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_12_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_12_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_12_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_12_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_12_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_12_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_12_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[12]),
    .i_func_oup_en       (i_gpio_oe[12]),
    .o_func_inp          (o_gpio[12]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[12])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[12]),
    .i_func_impl_inp     (gpio_12_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_12_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[12]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[12]),
    .o_dft_inp           (o_dft_gpio_inp[12]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[12]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_12_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_12_impl_oup_mux[1]),
    .o_padside_oup       (gpio_12_oup),
    .o_padside_oup_en    (gpio_12_oup_en),
    .i_padside_inp       (gpio_12_inp),
    .o_padside_inp_en    (gpio_12_inp_en),
    .o_padside_pull_type (gpio_12_pull_type),
    .o_padside_pull_en   (gpio_12_pull_en),
    .o_padside_impl_inp  (gpio_12_impl_inp),
    .i_padside_impl_oup  (gpio_12_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_12 (
    .i_oup      (gpio_12_oup),
    .i_oup_en   (gpio_12_oup_en),
    .o_inp      (gpio_12_inp),
    .i_inp_en   (gpio_12_inp_en),
    .i_pull_type(gpio_12_pull_type),
    .i_pull_en  (gpio_12_pull_en),
    .i_impl     (gpio_12_impl_inp),
    .o_impl     (gpio_12_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_gpio[12])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[11]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_11_oup;
  logic gpio_11_oup_en;
  logic gpio_11_inp;
  logic gpio_11_inp_en;
  logic gpio_11_pull_type;
  logic gpio_11_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_11_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_11_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_11_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_11_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_11_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_11_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_11_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[11]),
    .i_func_oup_en       (i_gpio_oe[11]),
    .o_func_inp          (o_gpio[11]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[11])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[11]),
    .i_func_impl_inp     (gpio_11_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_11_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[11]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[11]),
    .o_dft_inp           (o_dft_gpio_inp[11]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[11]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_11_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_11_impl_oup_mux[1]),
    .o_padside_oup       (gpio_11_oup),
    .o_padside_oup_en    (gpio_11_oup_en),
    .i_padside_inp       (gpio_11_inp),
    .o_padside_inp_en    (gpio_11_inp_en),
    .o_padside_pull_type (gpio_11_pull_type),
    .o_padside_pull_en   (gpio_11_pull_en),
    .o_padside_impl_inp  (gpio_11_impl_inp),
    .i_padside_impl_oup  (gpio_11_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_11 (
    .i_oup      (gpio_11_oup),
    .i_oup_en   (gpio_11_oup_en),
    .o_inp      (gpio_11_inp),
    .i_inp_en   (gpio_11_inp_en),
    .i_pull_type(gpio_11_pull_type),
    .i_pull_en  (gpio_11_pull_en),
    .i_impl     (gpio_11_impl_inp),
    .o_impl     (gpio_11_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_gpio[11])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[10]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_10_oup;
  logic gpio_10_oup_en;
  logic gpio_10_inp;
  logic gpio_10_inp_en;
  logic gpio_10_pull_type;
  logic gpio_10_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_10_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_10_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_10_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_10_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_10_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_10_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_10_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[10]),
    .i_func_oup_en       (i_gpio_oe[10]),
    .o_func_inp          (o_gpio[10]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[10])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[10]),
    .i_func_impl_inp     (gpio_10_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_10_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[10]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[10]),
    .o_dft_inp           (o_dft_gpio_inp[10]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[10]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_10_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_10_impl_oup_mux[1]),
    .o_padside_oup       (gpio_10_oup),
    .o_padside_oup_en    (gpio_10_oup_en),
    .i_padside_inp       (gpio_10_inp),
    .o_padside_inp_en    (gpio_10_inp_en),
    .o_padside_pull_type (gpio_10_pull_type),
    .o_padside_pull_en   (gpio_10_pull_en),
    .o_padside_impl_inp  (gpio_10_impl_inp),
    .i_padside_impl_oup  (gpio_10_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_10 (
    .i_oup      (gpio_10_oup),
    .i_oup_en   (gpio_10_oup_en),
    .o_inp      (gpio_10_inp),
    .i_inp_en   (gpio_10_inp_en),
    .i_pull_type(gpio_10_pull_type),
    .i_pull_en  (gpio_10_pull_en),
    .i_impl     (gpio_10_impl_inp),
    .o_impl     (gpio_10_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_gpio[10])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[9]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_9_oup;
  logic gpio_9_oup_en;
  logic gpio_9_inp;
  logic gpio_9_inp_en;
  logic gpio_9_pull_type;
  logic gpio_9_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_9_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_9_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_9_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_9_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_9_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_9_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_9_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[9]),
    .i_func_oup_en       (i_gpio_oe[9]),
    .o_func_inp          (o_gpio[9]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[9])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[9]),
    .i_func_impl_inp     (gpio_9_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_9_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[9]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[9]),
    .o_dft_inp           (o_dft_gpio_inp[9]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[9]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_9_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_9_impl_oup_mux[1]),
    .o_padside_oup       (gpio_9_oup),
    .o_padside_oup_en    (gpio_9_oup_en),
    .i_padside_inp       (gpio_9_inp),
    .o_padside_inp_en    (gpio_9_inp_en),
    .o_padside_pull_type (gpio_9_pull_type),
    .o_padside_pull_en   (gpio_9_pull_en),
    .o_padside_impl_inp  (gpio_9_impl_inp),
    .i_padside_impl_oup  (gpio_9_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_9 (
    .i_oup      (gpio_9_oup),
    .i_oup_en   (gpio_9_oup_en),
    .o_inp      (gpio_9_inp),
    .i_inp_en   (gpio_9_inp_en),
    .i_pull_type(gpio_9_pull_type),
    .i_pull_en  (gpio_9_pull_en),
    .i_impl     (gpio_9_impl_inp),
    .o_impl     (gpio_9_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_gpio[9])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[8]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_8_oup;
  logic gpio_8_oup_en;
  logic gpio_8_inp;
  logic gpio_8_inp_en;
  logic gpio_8_pull_type;
  logic gpio_8_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_8_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_8_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_8_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_8_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_8_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_8_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_8_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[8]),
    .i_func_oup_en       (i_gpio_oe[8]),
    .o_func_inp          (o_gpio[8]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[8])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[8]),
    .i_func_impl_inp     (gpio_8_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_8_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[8]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[8]),
    .o_dft_inp           (o_dft_gpio_inp[8]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[8]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_8_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_8_impl_oup_mux[1]),
    .o_padside_oup       (gpio_8_oup),
    .o_padside_oup_en    (gpio_8_oup_en),
    .i_padside_inp       (gpio_8_inp),
    .o_padside_inp_en    (gpio_8_inp_en),
    .o_padside_pull_type (gpio_8_pull_type),
    .o_padside_pull_en   (gpio_8_pull_en),
    .o_padside_impl_inp  (gpio_8_impl_inp),
    .i_padside_impl_oup  (gpio_8_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_8 (
    .i_oup      (gpio_8_oup),
    .i_oup_en   (gpio_8_oup_en),
    .o_inp      (gpio_8_inp),
    .i_inp_en   (gpio_8_inp_en),
    .i_pull_type(gpio_8_pull_type),
    .i_pull_en  (gpio_8_pull_en),
    .i_impl     (gpio_8_impl_inp),
    .o_impl     (gpio_8_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_gpio[8])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[7]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_7_oup;
  logic gpio_7_oup_en;
  logic gpio_7_inp;
  logic gpio_7_inp_en;
  logic gpio_7_pull_type;
  logic gpio_7_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_7_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_7_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_7_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_7_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_7_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_7_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_7_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[7]),
    .i_func_oup_en       (i_gpio_oe[7]),
    .o_func_inp          (o_gpio[7]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[7])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[7]),
    .i_func_impl_inp     (gpio_7_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_7_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[7]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[7]),
    .o_dft_inp           (o_dft_gpio_inp[7]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[7]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_7_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_7_impl_oup_mux[1]),
    .o_padside_oup       (gpio_7_oup),
    .o_padside_oup_en    (gpio_7_oup_en),
    .i_padside_inp       (gpio_7_inp),
    .o_padside_inp_en    (gpio_7_inp_en),
    .o_padside_pull_type (gpio_7_pull_type),
    .o_padside_pull_en   (gpio_7_pull_en),
    .o_padside_impl_inp  (gpio_7_impl_inp),
    .i_padside_impl_oup  (gpio_7_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_7 (
    .i_oup      (gpio_7_oup),
    .i_oup_en   (gpio_7_oup_en),
    .o_inp      (gpio_7_inp),
    .i_inp_en   (gpio_7_inp_en),
    .i_pull_type(gpio_7_pull_type),
    .i_pull_en  (gpio_7_pull_en),
    .i_impl     (gpio_7_impl_inp),
    .o_impl     (gpio_7_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_gpio[7])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[6]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_6_oup;
  logic gpio_6_oup_en;
  logic gpio_6_inp;
  logic gpio_6_inp_en;
  logic gpio_6_pull_type;
  logic gpio_6_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_6_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_6_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_6_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_6_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_6_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_6_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_6_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[6]),
    .i_func_oup_en       (i_gpio_oe[6]),
    .o_func_inp          (o_gpio[6]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[6])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[6]),
    .i_func_impl_inp     (gpio_6_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_6_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[6]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[6]),
    .o_dft_inp           (o_dft_gpio_inp[6]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[6]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_6_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_6_impl_oup_mux[1]),
    .o_padside_oup       (gpio_6_oup),
    .o_padside_oup_en    (gpio_6_oup_en),
    .i_padside_inp       (gpio_6_inp),
    .o_padside_inp_en    (gpio_6_inp_en),
    .o_padside_pull_type (gpio_6_pull_type),
    .o_padside_pull_en   (gpio_6_pull_en),
    .o_padside_impl_inp  (gpio_6_impl_inp),
    .i_padside_impl_oup  (gpio_6_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_6 (
    .i_oup      (gpio_6_oup),
    .i_oup_en   (gpio_6_oup_en),
    .o_inp      (gpio_6_inp),
    .i_inp_en   (gpio_6_inp_en),
    .i_pull_type(gpio_6_pull_type),
    .i_pull_en  (gpio_6_pull_en),
    .i_impl     (gpio_6_impl_inp),
    .o_impl     (gpio_6_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_gpio[6])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[5]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_5_oup;
  logic gpio_5_oup_en;
  logic gpio_5_inp;
  logic gpio_5_inp_en;
  logic gpio_5_pull_type;
  logic gpio_5_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_5_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_5_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_5_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_5_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_5_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_5_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_5_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[5]),
    .i_func_oup_en       (i_gpio_oe[5]),
    .o_func_inp          (o_gpio[5]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[5])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[5]),
    .i_func_impl_inp     (gpio_5_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_5_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[5]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[5]),
    .o_dft_inp           (o_dft_gpio_inp[5]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[5]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_5_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_5_impl_oup_mux[1]),
    .o_padside_oup       (gpio_5_oup),
    .o_padside_oup_en    (gpio_5_oup_en),
    .i_padside_inp       (gpio_5_inp),
    .o_padside_inp_en    (gpio_5_inp_en),
    .o_padside_pull_type (gpio_5_pull_type),
    .o_padside_pull_en   (gpio_5_pull_en),
    .o_padside_impl_inp  (gpio_5_impl_inp),
    .i_padside_impl_oup  (gpio_5_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_5 (
    .i_oup      (gpio_5_oup),
    .i_oup_en   (gpio_5_oup_en),
    .o_inp      (gpio_5_inp),
    .i_inp_en   (gpio_5_inp_en),
    .i_pull_type(gpio_5_pull_type),
    .i_pull_en  (gpio_5_pull_en),
    .i_impl     (gpio_5_impl_inp),
    .o_impl     (gpio_5_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_gpio[5])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[4]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_4_oup;
  logic gpio_4_oup_en;
  logic gpio_4_inp;
  logic gpio_4_inp_en;
  logic gpio_4_pull_type;
  logic gpio_4_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_4_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_4_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_4_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_4_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_4_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_4_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_4_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[4]),
    .i_func_oup_en       (i_gpio_oe[4]),
    .o_func_inp          (o_gpio[4]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[4])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[4]),
    .i_func_impl_inp     (gpio_4_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_4_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[4]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[4]),
    .o_dft_inp           (o_dft_gpio_inp[4]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[4]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_4_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_4_impl_oup_mux[1]),
    .o_padside_oup       (gpio_4_oup),
    .o_padside_oup_en    (gpio_4_oup_en),
    .i_padside_inp       (gpio_4_inp),
    .o_padside_inp_en    (gpio_4_inp_en),
    .o_padside_pull_type (gpio_4_pull_type),
    .o_padside_pull_en   (gpio_4_pull_en),
    .o_padside_impl_inp  (gpio_4_impl_inp),
    .i_padside_impl_oup  (gpio_4_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_4 (
    .i_oup      (gpio_4_oup),
    .i_oup_en   (gpio_4_oup_en),
    .o_inp      (gpio_4_inp),
    .i_inp_en   (gpio_4_inp_en),
    .i_pull_type(gpio_4_pull_type),
    .i_pull_en  (gpio_4_pull_en),
    .i_impl     (gpio_4_impl_inp),
    .o_impl     (gpio_4_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_gpio[4])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[3]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_3_oup;
  logic gpio_3_oup_en;
  logic gpio_3_inp;
  logic gpio_3_inp_en;
  logic gpio_3_pull_type;
  logic gpio_3_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_3_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_3_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_3_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_3_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_3_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_3_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_3_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[3]),
    .i_func_oup_en       (i_gpio_oe[3]),
    .o_func_inp          (o_gpio[3]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[3])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[3]),
    .i_func_impl_inp     (gpio_3_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_3_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[3]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[3]),
    .o_dft_inp           (o_dft_gpio_inp[3]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[3]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_3_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_3_impl_oup_mux[1]),
    .o_padside_oup       (gpio_3_oup),
    .o_padside_oup_en    (gpio_3_oup_en),
    .i_padside_inp       (gpio_3_inp),
    .o_padside_inp_en    (gpio_3_inp_en),
    .o_padside_pull_type (gpio_3_pull_type),
    .o_padside_pull_en   (gpio_3_pull_en),
    .o_padside_impl_inp  (gpio_3_impl_inp),
    .i_padside_impl_oup  (gpio_3_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_3 (
    .i_oup      (gpio_3_oup),
    .i_oup_en   (gpio_3_oup_en),
    .o_inp      (gpio_3_inp),
    .i_inp_en   (gpio_3_inp_en),
    .i_pull_type(gpio_3_pull_type),
    .i_pull_en  (gpio_3_pull_en),
    .i_impl     (gpio_3_impl_inp),
    .o_impl     (gpio_3_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_gpio[3])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[2]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_2_oup;
  logic gpio_2_oup_en;
  logic gpio_2_inp;
  logic gpio_2_inp_en;
  logic gpio_2_pull_type;
  logic gpio_2_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_2_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_2_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_2_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_2_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_2_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_2_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_2_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[2]),
    .i_func_oup_en       (i_gpio_oe[2]),
    .o_func_inp          (o_gpio[2]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[2])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[2]),
    .i_func_impl_inp     (gpio_2_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_2_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[2]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[2]),
    .o_dft_inp           (o_dft_gpio_inp[2]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[2]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_2_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_2_impl_oup_mux[1]),
    .o_padside_oup       (gpio_2_oup),
    .o_padside_oup_en    (gpio_2_oup_en),
    .i_padside_inp       (gpio_2_inp),
    .o_padside_inp_en    (gpio_2_inp_en),
    .o_padside_pull_type (gpio_2_pull_type),
    .o_padside_pull_en   (gpio_2_pull_en),
    .o_padside_impl_inp  (gpio_2_impl_inp),
    .i_padside_impl_oup  (gpio_2_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_2 (
    .i_oup      (gpio_2_oup),
    .i_oup_en   (gpio_2_oup_en),
    .o_inp      (gpio_2_inp),
    .i_inp_en   (gpio_2_inp_en),
    .i_pull_type(gpio_2_pull_type),
    .i_pull_en  (gpio_2_pull_en),
    .i_impl     (gpio_2_impl_inp),
    .o_impl     (gpio_2_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_gpio[2])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[1]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_1_oup;
  logic gpio_1_oup_en;
  logic gpio_1_inp;
  logic gpio_1_inp_en;
  logic gpio_1_pull_type;
  logic gpio_1_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_1_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_1_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_1_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_1_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_1_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_1_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_1_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[1]),
    .i_func_oup_en       (i_gpio_oe[1]),
    .o_func_inp          (o_gpio[1]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[1])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[1]),
    .i_func_impl_inp     (gpio_1_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_1_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[1]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[1]),
    .o_dft_inp           (o_dft_gpio_inp[1]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[1]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_1_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_1_impl_oup_mux[1]),
    .o_padside_oup       (gpio_1_oup),
    .o_padside_oup_en    (gpio_1_oup_en),
    .i_padside_inp       (gpio_1_inp),
    .o_padside_inp_en    (gpio_1_inp_en),
    .o_padside_pull_type (gpio_1_pull_type),
    .o_padside_pull_en   (gpio_1_pull_en),
    .o_padside_impl_inp  (gpio_1_impl_inp),
    .i_padside_impl_oup  (gpio_1_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_1 (
    .i_oup      (gpio_1_oup),
    .i_oup_en   (gpio_1_oup_en),
    .o_inp      (gpio_1_inp),
    .i_inp_en   (gpio_1_inp_en),
    .i_pull_type(gpio_1_pull_type),
    .i_pull_en  (gpio_1_pull_en),
    .i_impl     (gpio_1_impl_inp),
    .o_impl     (gpio_1_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_gpio[1])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for gpio[0]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic gpio_0_oup;
  logic gpio_0_oup_en;
  logic gpio_0_inp;
  logic gpio_0_inp_en;
  logic gpio_0_pull_type;
  logic gpio_0_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       gpio_0_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       gpio_0_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] gpio_0_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] gpio_0_impl_oup_mux; // Stubbed

  always_comb begin
    gpio_0_impl_inp_mux[0] = '{
      is:  i_gpio_schmitt,
      ds:  i_gpio_drive,
      poe: 1'b0  // Stubbed
    };
    gpio_0_impl_inp_mux[1] = '{
      is:  i_dft_gpio_schmitt,
      ds:  i_dft_gpio_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_inout #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_inout_gpio_0_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_gpio[0]),
    .i_func_oup_en       (i_gpio_oe[0]),
    .o_func_inp          (o_gpio[0]),
    .i_func_inp_en       ((1'b1 ^ i_gpio_oe[0])),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (i_gpio_pd_en[0]),
    .i_func_impl_inp     (gpio_0_impl_inp_mux[0]),
    .o_func_impl_oup     (gpio_0_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_gpio_oup[0]),
    .i_dft_oup_en        (i_dft_gpio_oup_en[0]),
    .o_dft_inp           (o_dft_gpio_inp[0]),
    .i_dft_inp_en        (i_dft_gpio_inp_en[0]),
    .i_dft_pull_type     (i_dft_gpio_pull_type),
    .i_dft_pull_en       (i_dft_gpio_pull_en),
    .i_dft_impl_inp      (gpio_0_impl_inp_mux[1]),
    .o_dft_impl_oup      (gpio_0_impl_oup_mux[1]),
    .o_padside_oup       (gpio_0_oup),
    .o_padside_oup_en    (gpio_0_oup_en),
    .i_padside_inp       (gpio_0_inp),
    .o_padside_inp_en    (gpio_0_inp_en),
    .o_padside_pull_type (gpio_0_pull_type),
    .o_padside_pull_en   (gpio_0_pull_en),
    .o_padside_impl_inp  (gpio_0_impl_inp),
    .i_padside_impl_oup  (gpio_0_impl_oup)
  );

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_gpio_0 (
    .i_oup      (gpio_0_oup),
    .i_oup_en   (gpio_0_oup_en),
    .o_inp      (gpio_0_inp),
    .i_inp_en   (gpio_0_inp_en),
    .i_pull_type(gpio_0_pull_type),
    .i_pull_en  (gpio_0_pull_en),
    .i_impl     (gpio_0_impl_inp),
    .o_impl     (gpio_0_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_gpio[0])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for sd_emmc_cmd
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_cmd_oup;
  logic sd_emmc_cmd_oup_en;
  logic sd_emmc_cmd_inp;
  logic sd_emmc_cmd_inp_en;
  logic sd_emmc_cmd_pull_type;
  logic sd_emmc_cmd_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_cmd_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_cmd_impl_oup; // Stubbed
  always_comb sd_emmc_cmd_oup       = i_sd_emmc_cmd;
  always_comb sd_emmc_cmd_oup_en    = (1'b1 ^ i_sd_emmc_cmd_oe);
  always_comb o_sd_emmc_cmd = sd_emmc_cmd_inp;
  always_comb sd_emmc_cmd_inp_en    = (1'b1 ^ i_sd_emmc_cmd_ie);
  always_comb sd_emmc_cmd_pull_type = 1'b0;
  always_comb sd_emmc_cmd_pull_en   = 1'b0;

  always_comb sd_emmc_cmd_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_sd_emmc_cmd (
    .i_oup      (sd_emmc_cmd_oup),
    .i_oup_en   (sd_emmc_cmd_oup_en),
    .o_inp      (sd_emmc_cmd_inp),
    .i_inp_en   (sd_emmc_cmd_inp_en),
    .i_pull_type(sd_emmc_cmd_pull_type),
    .i_pull_en  (sd_emmc_cmd_pull_en),
    .i_impl     (sd_emmc_cmd_impl_inp),
    .o_impl     (sd_emmc_cmd_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_sd_emmc_cmd)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for sd_emmc_data[7]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_data_7_oup;
  logic sd_emmc_data_7_oup_en;
  logic sd_emmc_data_7_inp;
  logic sd_emmc_data_7_inp_en;
  logic sd_emmc_data_7_pull_type;
  logic sd_emmc_data_7_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_data_7_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_data_7_impl_oup; // Stubbed
  always_comb sd_emmc_data_7_oup       = i_sd_emmc_data[7];
  always_comb sd_emmc_data_7_oup_en    = (1'b1 ^ i_sd_emmc_data_oe[7]);
  always_comb o_sd_emmc_data[7] = sd_emmc_data_7_inp;
  always_comb sd_emmc_data_7_inp_en    = (1'b1 ^ i_sd_emmc_data_ie[7]);
  always_comb sd_emmc_data_7_pull_type = 1'b0;
  always_comb sd_emmc_data_7_pull_en   = 1'b0;

  always_comb sd_emmc_data_7_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_sd_emmc_data_7 (
    .i_oup      (sd_emmc_data_7_oup),
    .i_oup_en   (sd_emmc_data_7_oup_en),
    .o_inp      (sd_emmc_data_7_inp),
    .i_inp_en   (sd_emmc_data_7_inp_en),
    .i_pull_type(sd_emmc_data_7_pull_type),
    .i_pull_en  (sd_emmc_data_7_pull_en),
    .i_impl     (sd_emmc_data_7_impl_inp),
    .o_impl     (sd_emmc_data_7_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_sd_emmc_data[7])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for sd_emmc_data[6]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_data_6_oup;
  logic sd_emmc_data_6_oup_en;
  logic sd_emmc_data_6_inp;
  logic sd_emmc_data_6_inp_en;
  logic sd_emmc_data_6_pull_type;
  logic sd_emmc_data_6_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_data_6_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_data_6_impl_oup; // Stubbed
  always_comb sd_emmc_data_6_oup       = i_sd_emmc_data[6];
  always_comb sd_emmc_data_6_oup_en    = (1'b1 ^ i_sd_emmc_data_oe[6]);
  always_comb o_sd_emmc_data[6] = sd_emmc_data_6_inp;
  always_comb sd_emmc_data_6_inp_en    = (1'b1 ^ i_sd_emmc_data_ie[6]);
  always_comb sd_emmc_data_6_pull_type = 1'b0;
  always_comb sd_emmc_data_6_pull_en   = 1'b0;

  always_comb sd_emmc_data_6_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_sd_emmc_data_6 (
    .i_oup      (sd_emmc_data_6_oup),
    .i_oup_en   (sd_emmc_data_6_oup_en),
    .o_inp      (sd_emmc_data_6_inp),
    .i_inp_en   (sd_emmc_data_6_inp_en),
    .i_pull_type(sd_emmc_data_6_pull_type),
    .i_pull_en  (sd_emmc_data_6_pull_en),
    .i_impl     (sd_emmc_data_6_impl_inp),
    .o_impl     (sd_emmc_data_6_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_sd_emmc_data[6])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for sd_emmc_data[5]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_data_5_oup;
  logic sd_emmc_data_5_oup_en;
  logic sd_emmc_data_5_inp;
  logic sd_emmc_data_5_inp_en;
  logic sd_emmc_data_5_pull_type;
  logic sd_emmc_data_5_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_data_5_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_data_5_impl_oup; // Stubbed
  always_comb sd_emmc_data_5_oup       = i_sd_emmc_data[5];
  always_comb sd_emmc_data_5_oup_en    = (1'b1 ^ i_sd_emmc_data_oe[5]);
  always_comb o_sd_emmc_data[5] = sd_emmc_data_5_inp;
  always_comb sd_emmc_data_5_inp_en    = (1'b1 ^ i_sd_emmc_data_ie[5]);
  always_comb sd_emmc_data_5_pull_type = 1'b0;
  always_comb sd_emmc_data_5_pull_en   = 1'b0;

  always_comb sd_emmc_data_5_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_sd_emmc_data_5 (
    .i_oup      (sd_emmc_data_5_oup),
    .i_oup_en   (sd_emmc_data_5_oup_en),
    .o_inp      (sd_emmc_data_5_inp),
    .i_inp_en   (sd_emmc_data_5_inp_en),
    .i_pull_type(sd_emmc_data_5_pull_type),
    .i_pull_en  (sd_emmc_data_5_pull_en),
    .i_impl     (sd_emmc_data_5_impl_inp),
    .o_impl     (sd_emmc_data_5_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_sd_emmc_data[5])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for sd_emmc_data[4]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_data_4_oup;
  logic sd_emmc_data_4_oup_en;
  logic sd_emmc_data_4_inp;
  logic sd_emmc_data_4_inp_en;
  logic sd_emmc_data_4_pull_type;
  logic sd_emmc_data_4_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_data_4_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_data_4_impl_oup; // Stubbed
  always_comb sd_emmc_data_4_oup       = i_sd_emmc_data[4];
  always_comb sd_emmc_data_4_oup_en    = (1'b1 ^ i_sd_emmc_data_oe[4]);
  always_comb o_sd_emmc_data[4] = sd_emmc_data_4_inp;
  always_comb sd_emmc_data_4_inp_en    = (1'b1 ^ i_sd_emmc_data_ie[4]);
  always_comb sd_emmc_data_4_pull_type = 1'b0;
  always_comb sd_emmc_data_4_pull_en   = 1'b0;

  always_comb sd_emmc_data_4_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_sd_emmc_data_4 (
    .i_oup      (sd_emmc_data_4_oup),
    .i_oup_en   (sd_emmc_data_4_oup_en),
    .o_inp      (sd_emmc_data_4_inp),
    .i_inp_en   (sd_emmc_data_4_inp_en),
    .i_pull_type(sd_emmc_data_4_pull_type),
    .i_pull_en  (sd_emmc_data_4_pull_en),
    .i_impl     (sd_emmc_data_4_impl_inp),
    .o_impl     (sd_emmc_data_4_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_sd_emmc_data[4])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for sd_emmc_data[3]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_data_3_oup;
  logic sd_emmc_data_3_oup_en;
  logic sd_emmc_data_3_inp;
  logic sd_emmc_data_3_inp_en;
  logic sd_emmc_data_3_pull_type;
  logic sd_emmc_data_3_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_data_3_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_data_3_impl_oup; // Stubbed
  always_comb sd_emmc_data_3_oup       = i_sd_emmc_data[3];
  always_comb sd_emmc_data_3_oup_en    = (1'b1 ^ i_sd_emmc_data_oe[3]);
  always_comb o_sd_emmc_data[3] = sd_emmc_data_3_inp;
  always_comb sd_emmc_data_3_inp_en    = (1'b1 ^ i_sd_emmc_data_ie[3]);
  always_comb sd_emmc_data_3_pull_type = 1'b0;
  always_comb sd_emmc_data_3_pull_en   = 1'b0;

  always_comb sd_emmc_data_3_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_sd_emmc_data_3 (
    .i_oup      (sd_emmc_data_3_oup),
    .i_oup_en   (sd_emmc_data_3_oup_en),
    .o_inp      (sd_emmc_data_3_inp),
    .i_inp_en   (sd_emmc_data_3_inp_en),
    .i_pull_type(sd_emmc_data_3_pull_type),
    .i_pull_en  (sd_emmc_data_3_pull_en),
    .i_impl     (sd_emmc_data_3_impl_inp),
    .o_impl     (sd_emmc_data_3_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_sd_emmc_data[3])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for sd_emmc_data[2]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_data_2_oup;
  logic sd_emmc_data_2_oup_en;
  logic sd_emmc_data_2_inp;
  logic sd_emmc_data_2_inp_en;
  logic sd_emmc_data_2_pull_type;
  logic sd_emmc_data_2_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_data_2_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_data_2_impl_oup; // Stubbed
  always_comb sd_emmc_data_2_oup       = i_sd_emmc_data[2];
  always_comb sd_emmc_data_2_oup_en    = (1'b1 ^ i_sd_emmc_data_oe[2]);
  always_comb o_sd_emmc_data[2] = sd_emmc_data_2_inp;
  always_comb sd_emmc_data_2_inp_en    = (1'b1 ^ i_sd_emmc_data_ie[2]);
  always_comb sd_emmc_data_2_pull_type = 1'b0;
  always_comb sd_emmc_data_2_pull_en   = 1'b0;

  always_comb sd_emmc_data_2_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_sd_emmc_data_2 (
    .i_oup      (sd_emmc_data_2_oup),
    .i_oup_en   (sd_emmc_data_2_oup_en),
    .o_inp      (sd_emmc_data_2_inp),
    .i_inp_en   (sd_emmc_data_2_inp_en),
    .i_pull_type(sd_emmc_data_2_pull_type),
    .i_pull_en  (sd_emmc_data_2_pull_en),
    .i_impl     (sd_emmc_data_2_impl_inp),
    .o_impl     (sd_emmc_data_2_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_sd_emmc_data[2])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for sd_emmc_data[1]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_data_1_oup;
  logic sd_emmc_data_1_oup_en;
  logic sd_emmc_data_1_inp;
  logic sd_emmc_data_1_inp_en;
  logic sd_emmc_data_1_pull_type;
  logic sd_emmc_data_1_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_data_1_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_data_1_impl_oup; // Stubbed
  always_comb sd_emmc_data_1_oup       = i_sd_emmc_data[1];
  always_comb sd_emmc_data_1_oup_en    = (1'b1 ^ i_sd_emmc_data_oe[1]);
  always_comb o_sd_emmc_data[1] = sd_emmc_data_1_inp;
  always_comb sd_emmc_data_1_inp_en    = (1'b1 ^ i_sd_emmc_data_ie[1]);
  always_comb sd_emmc_data_1_pull_type = 1'b0;
  always_comb sd_emmc_data_1_pull_en   = 1'b0;

  always_comb sd_emmc_data_1_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_sd_emmc_data_1 (
    .i_oup      (sd_emmc_data_1_oup),
    .i_oup_en   (sd_emmc_data_1_oup_en),
    .o_inp      (sd_emmc_data_1_inp),
    .i_inp_en   (sd_emmc_data_1_inp_en),
    .i_pull_type(sd_emmc_data_1_pull_type),
    .i_pull_en  (sd_emmc_data_1_pull_en),
    .i_impl     (sd_emmc_data_1_impl_inp),
    .o_impl     (sd_emmc_data_1_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_sd_emmc_data[1])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for sd_emmc_data[0]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_data_0_oup;
  logic sd_emmc_data_0_oup_en;
  logic sd_emmc_data_0_inp;
  logic sd_emmc_data_0_inp_en;
  logic sd_emmc_data_0_pull_type;
  logic sd_emmc_data_0_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_data_0_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_data_0_impl_oup; // Stubbed
  always_comb sd_emmc_data_0_oup       = i_sd_emmc_data[0];
  always_comb sd_emmc_data_0_oup_en    = (1'b1 ^ i_sd_emmc_data_oe[0]);
  always_comb o_sd_emmc_data[0] = sd_emmc_data_0_inp;
  always_comb sd_emmc_data_0_inp_en    = (1'b1 ^ i_sd_emmc_data_ie[0]);
  always_comb sd_emmc_data_0_pull_type = 1'b0;
  always_comb sd_emmc_data_0_pull_en   = 1'b0;

  always_comb sd_emmc_data_0_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_sd_emmc_data_0 (
    .i_oup      (sd_emmc_data_0_oup),
    .i_oup_en   (sd_emmc_data_0_oup_en),
    .o_inp      (sd_emmc_data_0_inp),
    .i_inp_en   (sd_emmc_data_0_inp_en),
    .i_pull_type(sd_emmc_data_0_pull_type),
    .i_pull_en  (sd_emmc_data_0_pull_en),
    .i_impl     (sd_emmc_data_0_impl_inp),
    .o_impl     (sd_emmc_data_0_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_sd_emmc_data[0])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for sd_emmc_strobe
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_strobe_inp;
  logic sd_emmc_strobe_inp_en;
  logic sd_emmc_strobe_pull_type;
  logic sd_emmc_strobe_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_strobe_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_strobe_impl_oup; // Stubbed
  always_comb o_sd_emmc_strobe = sd_emmc_strobe_inp;
  always_comb sd_emmc_strobe_inp_en    = (1'b1 ^ i_sd_emmc_strobe_ie);
  always_comb sd_emmc_strobe_pull_type = 1'b0;
  always_comb sd_emmc_strobe_pull_en   = 1'b0;

  always_comb sd_emmc_strobe_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_sd_emmc_strobe (
    .o_inp      (sd_emmc_strobe_inp),
    .i_inp_en   (sd_emmc_strobe_inp_en),
    .i_pull_type(sd_emmc_strobe_pull_type),
    .i_pull_en  (sd_emmc_strobe_pull_en),
    .i_impl     (sd_emmc_strobe_impl_inp),
    .o_impl     (sd_emmc_strobe_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .i_pad      (i_pad_sd_emmc_strobe)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for emmc_reset
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic emmc_reset_oup;
  logic emmc_reset_oup_en;
  logic emmc_reset_pull_type;
  logic emmc_reset_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       emmc_reset_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       emmc_reset_impl_oup; // Stubbed
  always_comb emmc_reset_oup       = i_emmc_reset;
  always_comb emmc_reset_oup_en    = (1'b1 ^ i_emmc_reset_oe);
  always_comb emmc_reset_pull_type = 1'b0;
  always_comb emmc_reset_pull_en   = 1'b0;

  always_comb emmc_reset_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_output #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_emmc_reset (
    .i_oup      (emmc_reset_oup),
    .i_oup_en   (emmc_reset_oup_en),
    .i_pull_type(emmc_reset_pull_type),
    .i_pull_en  (emmc_reset_pull_en),
    .i_impl     (emmc_reset_impl_inp),
    .o_impl     (emmc_reset_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_emmc_reset)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for emmc_power
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic emmc_power_oup;
  logic emmc_power_oup_en;
  logic emmc_power_pull_type;
  logic emmc_power_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       emmc_power_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       emmc_power_impl_oup; // Stubbed
  always_comb emmc_power_oup       = i_emmc_power;
  always_comb emmc_power_oup_en    = (1'b1 ^ i_emmc_power_oe);
  always_comb emmc_power_pull_type = 1'b0;
  always_comb emmc_power_pull_en   = 1'b0;

  always_comb emmc_power_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_output #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_emmc_power (
    .i_oup      (emmc_power_oup),
    .i_oup_en   (emmc_power_oup_en),
    .i_pull_type(emmc_power_pull_type),
    .i_pull_en  (emmc_power_pull_en),
    .i_impl     (emmc_power_impl_inp),
    .o_impl     (emmc_power_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_emmc_power)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for sd_emmc_detect
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_detect_inp;
  logic sd_emmc_detect_inp_en;
  logic sd_emmc_detect_pull_type;
  logic sd_emmc_detect_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_detect_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_detect_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_fast_inp_t [1:0] sd_emmc_detect_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t [1:0] sd_emmc_detect_impl_oup_mux; // Stubbed

  always_comb begin
    sd_emmc_detect_impl_inp_mux[0] = '{
      is:  i_emmc_schmitt,
      ds:  i_emmc_drive,
      poe: 1'b0  // Stubbed
    };
    sd_emmc_detect_impl_inp_mux[1] = '{
      is:  i_dft_sd_emmc_detect_schmitt,
      ds:  i_dft_sd_emmc_detect_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_input #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_fast_oup_t)
  ) u_input_sd_emmc_detect_dft_mux (
    .i_dft_enable,
    .o_func_inp          (o_sd_emmc_detect),
    .i_func_inp_en       ((1'b1 ^ i_sd_emmc_detect_ie)),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (sd_emmc_detect_impl_inp_mux[0]),
    .o_func_impl_oup     (sd_emmc_detect_impl_oup_mux[0]),
    .o_dft_inp           (o_dft_sd_emmc_detect_inp),
    .i_dft_inp_en        (i_dft_sd_emmc_detect_inp_en),
    .i_dft_pull_type     (i_dft_sd_emmc_detect_pull_type),
    .i_dft_pull_en       (i_dft_sd_emmc_detect_pull_en),
    .i_dft_impl_inp      (sd_emmc_detect_impl_inp_mux[1]),
    .o_dft_impl_oup      (sd_emmc_detect_impl_oup_mux[1]),
    .i_padside_inp       (sd_emmc_detect_inp),
    .o_padside_inp_en    (sd_emmc_detect_inp_en),
    .o_padside_pull_type (sd_emmc_detect_pull_type),
    .o_padside_pull_en   (sd_emmc_detect_pull_en),
    .o_padside_impl_inp  (sd_emmc_detect_impl_inp),
    .i_padside_impl_oup  (sd_emmc_detect_impl_oup)
  );

  axe_tcl_pad_input #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_sd_emmc_detect (
    .o_inp      (sd_emmc_detect_inp),
    .i_inp_en   (sd_emmc_detect_inp_en),
    .i_pull_type(sd_emmc_detect_pull_type),
    .i_pull_en  (sd_emmc_detect_pull_en),
    .i_impl     (sd_emmc_detect_impl_inp),
    .o_impl     (sd_emmc_detect_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_sd_emmc_detect)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for sd_emmc_wp
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_wp_inp;
  logic sd_emmc_wp_inp_en;
  logic sd_emmc_wp_pull_type;
  logic sd_emmc_wp_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_wp_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_wp_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_fast_inp_t [1:0] sd_emmc_wp_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t [1:0] sd_emmc_wp_impl_oup_mux; // Stubbed

  always_comb begin
    sd_emmc_wp_impl_inp_mux[0] = '{
      is:  i_emmc_schmitt,
      ds:  i_emmc_drive,
      poe: 1'b0  // Stubbed
    };
    sd_emmc_wp_impl_inp_mux[1] = '{
      is:  i_dft_sd_emmc_wp_schmitt,
      ds:  i_dft_sd_emmc_wp_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_input #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_fast_oup_t)
  ) u_input_sd_emmc_wp_dft_mux (
    .i_dft_enable,
    .o_func_inp          (o_sd_emmc_wp),
    .i_func_inp_en       ((1'b1 ^ i_sd_emmc_wp_ie)),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (sd_emmc_wp_impl_inp_mux[0]),
    .o_func_impl_oup     (sd_emmc_wp_impl_oup_mux[0]),
    .o_dft_inp           (o_dft_sd_emmc_wp_inp),
    .i_dft_inp_en        (i_dft_sd_emmc_wp_inp_en),
    .i_dft_pull_type     (i_dft_sd_emmc_wp_pull_type),
    .i_dft_pull_en       (i_dft_sd_emmc_wp_pull_en),
    .i_dft_impl_inp      (sd_emmc_wp_impl_inp_mux[1]),
    .o_dft_impl_oup      (sd_emmc_wp_impl_oup_mux[1]),
    .i_padside_inp       (sd_emmc_wp_inp),
    .o_padside_inp_en    (sd_emmc_wp_inp_en),
    .o_padside_pull_type (sd_emmc_wp_pull_type),
    .o_padside_pull_en   (sd_emmc_wp_pull_en),
    .o_padside_impl_inp  (sd_emmc_wp_impl_inp),
    .i_padside_impl_oup  (sd_emmc_wp_impl_oup)
  );

  axe_tcl_pad_input #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_sd_emmc_wp (
    .o_inp      (sd_emmc_wp_inp),
    .i_inp_en   (sd_emmc_wp_inp_en),
    .i_pull_type(sd_emmc_wp_pull_type),
    .i_pull_en  (sd_emmc_wp_pull_en),
    .i_impl     (sd_emmc_wp_impl_inp),
    .o_impl     (sd_emmc_wp_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .i_pad      (i_pad_sd_emmc_wp)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for sd_emmc_pu_pd
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic sd_emmc_pu_pd_oup;
  logic sd_emmc_pu_pd_oup_en;
  logic sd_emmc_pu_pd_pull_type;
  logic sd_emmc_pu_pd_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       sd_emmc_pu_pd_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       sd_emmc_pu_pd_impl_oup; // Stubbed
  always_comb sd_emmc_pu_pd_oup       = i_sd_emmc_pu_pd;
  always_comb sd_emmc_pu_pd_oup_en    = (1'b1 ^ i_sd_emmc_pu_pd_oe);
  always_comb sd_emmc_pu_pd_pull_type = 1'b0;
  always_comb sd_emmc_pu_pd_pull_en   = 1'b0;

  always_comb sd_emmc_pu_pd_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_output #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_sd_emmc_pu_pd (
    .i_oup      (sd_emmc_pu_pd_oup),
    .i_oup_en   (sd_emmc_pu_pd_oup_en),
    .i_pull_type(sd_emmc_pu_pd_pull_type),
    .i_pull_en  (sd_emmc_pu_pd_pull_en),
    .i_impl     (sd_emmc_pu_pd_impl_inp),
    .o_impl     (sd_emmc_pu_pd_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_sd_emmc_pu_pd)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for emmc_rebar
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic emmc_rebar_oup;
  logic emmc_rebar_oup_en;
  logic emmc_rebar_inp;
  logic emmc_rebar_inp_en;
  logic emmc_rebar_pull_type;
  logic emmc_rebar_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       emmc_rebar_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       emmc_rebar_impl_oup; // Stubbed
  always_comb emmc_rebar_oup       = i_emmc_rebar;
  always_comb emmc_rebar_oup_en    = (1'b1 ^ i_emmc_rebar_oe);
  always_comb o_emmc_rebar = emmc_rebar_inp;
  always_comb emmc_rebar_inp_en    = (1'b1 ^ i_emmc_rebar_ie);
  always_comb emmc_rebar_pull_type = 1'b0;
  always_comb emmc_rebar_pull_en   = 1'b0;

  always_comb emmc_rebar_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_emmc_rebar (
    .i_oup      (emmc_rebar_oup),
    .i_oup_en   (emmc_rebar_oup_en),
    .o_inp      (emmc_rebar_inp),
    .i_inp_en   (emmc_rebar_inp_en),
    .i_pull_type(emmc_rebar_pull_type),
    .i_pull_en  (emmc_rebar_pull_en),
    .i_impl     (emmc_rebar_impl_inp),
    .o_impl     (emmc_rebar_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_emmc_rebar)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for emmc_lpbk_dqs
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic emmc_lpbk_dqs_inp;
  logic emmc_lpbk_dqs_inp_en;
  logic emmc_lpbk_dqs_pull_type;
  logic emmc_lpbk_dqs_pull_en;

  axe_tcl_pad_pkg::impl_pad_fast_inp_t       emmc_lpbk_dqs_impl_inp;
  axe_tcl_pad_pkg::impl_pad_fast_oup_t       emmc_lpbk_dqs_impl_oup; // Stubbed
  always_comb o_emmc_lpbk_dqs = emmc_lpbk_dqs_inp;
  always_comb emmc_lpbk_dqs_inp_en    = (1'b1 ^ i_emmc_lpbk_dqs_ie);
  always_comb emmc_lpbk_dqs_pull_type = 1'b0;
  always_comb emmc_lpbk_dqs_pull_en   = 1'b0;

  always_comb emmc_lpbk_dqs_impl_inp = '{
    is:  i_emmc_schmitt,
    ds:  i_emmc_drive,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("fast_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_fast_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_fast_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_emmc_lpbk_dqs (
    .o_inp      (emmc_lpbk_dqs_inp),
    .i_inp_en   (emmc_lpbk_dqs_inp_en),
    .i_pull_type(emmc_lpbk_dqs_pull_type),
    .i_pull_en  (emmc_lpbk_dqs_pull_en),
    .i_impl     (emmc_lpbk_dqs_impl_inp),
    .o_impl     (emmc_lpbk_dqs_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .i_pad      (i_pad_emmc_lpbk_dqs)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[15]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_15_oup;
  logic observability_15_oup_en;
  logic observability_15_pull_type;
  logic observability_15_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_15_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_15_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_15_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_15_impl_oup_mux; // Stubbed

  always_comb begin
    observability_15_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_15_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_15_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[15]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_15_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_15_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[15]),
    .i_dft_oup_en        (i_dft_observability_oup_en[15]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_15_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_15_impl_oup_mux[1]),
    .o_padside_oup       (observability_15_oup),
    .o_padside_oup_en    (observability_15_oup_en),
    .o_padside_pull_type (observability_15_pull_type),
    .o_padside_pull_en   (observability_15_pull_en),
    .o_padside_impl_inp  (observability_15_impl_inp),
    .i_padside_impl_oup  (observability_15_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_15 (
    .i_oup      (observability_15_oup),
    .i_oup_en   (observability_15_oup_en),
    .i_pull_type(observability_15_pull_type),
    .i_pull_en  (observability_15_pull_en),
    .i_impl     (observability_15_impl_inp),
    .o_impl     (observability_15_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_observability[15])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[14]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_14_oup;
  logic observability_14_oup_en;
  logic observability_14_pull_type;
  logic observability_14_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_14_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_14_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_14_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_14_impl_oup_mux; // Stubbed

  always_comb begin
    observability_14_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_14_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_14_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[14]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_14_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_14_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[14]),
    .i_dft_oup_en        (i_dft_observability_oup_en[14]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_14_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_14_impl_oup_mux[1]),
    .o_padside_oup       (observability_14_oup),
    .o_padside_oup_en    (observability_14_oup_en),
    .o_padside_pull_type (observability_14_pull_type),
    .o_padside_pull_en   (observability_14_pull_en),
    .o_padside_impl_inp  (observability_14_impl_inp),
    .i_padside_impl_oup  (observability_14_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_14 (
    .i_oup      (observability_14_oup),
    .i_oup_en   (observability_14_oup_en),
    .i_pull_type(observability_14_pull_type),
    .i_pull_en  (observability_14_pull_en),
    .i_impl     (observability_14_impl_inp),
    .o_impl     (observability_14_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_observability[14])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[13]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_13_oup;
  logic observability_13_oup_en;
  logic observability_13_pull_type;
  logic observability_13_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_13_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_13_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_13_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_13_impl_oup_mux; // Stubbed

  always_comb begin
    observability_13_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_13_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_13_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[13]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_13_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_13_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[13]),
    .i_dft_oup_en        (i_dft_observability_oup_en[13]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_13_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_13_impl_oup_mux[1]),
    .o_padside_oup       (observability_13_oup),
    .o_padside_oup_en    (observability_13_oup_en),
    .o_padside_pull_type (observability_13_pull_type),
    .o_padside_pull_en   (observability_13_pull_en),
    .o_padside_impl_inp  (observability_13_impl_inp),
    .i_padside_impl_oup  (observability_13_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_13 (
    .i_oup      (observability_13_oup),
    .i_oup_en   (observability_13_oup_en),
    .i_pull_type(observability_13_pull_type),
    .i_pull_en  (observability_13_pull_en),
    .i_impl     (observability_13_impl_inp),
    .o_impl     (observability_13_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_observability[13])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[12]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_12_oup;
  logic observability_12_oup_en;
  logic observability_12_pull_type;
  logic observability_12_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_12_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_12_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_12_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_12_impl_oup_mux; // Stubbed

  always_comb begin
    observability_12_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_12_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_12_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[12]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_12_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_12_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[12]),
    .i_dft_oup_en        (i_dft_observability_oup_en[12]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_12_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_12_impl_oup_mux[1]),
    .o_padside_oup       (observability_12_oup),
    .o_padside_oup_en    (observability_12_oup_en),
    .o_padside_pull_type (observability_12_pull_type),
    .o_padside_pull_en   (observability_12_pull_en),
    .o_padside_impl_inp  (observability_12_impl_inp),
    .i_padside_impl_oup  (observability_12_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_12 (
    .i_oup      (observability_12_oup),
    .i_oup_en   (observability_12_oup_en),
    .i_pull_type(observability_12_pull_type),
    .i_pull_en  (observability_12_pull_en),
    .i_impl     (observability_12_impl_inp),
    .o_impl     (observability_12_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_observability[12])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[11]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_11_oup;
  logic observability_11_oup_en;
  logic observability_11_pull_type;
  logic observability_11_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_11_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_11_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_11_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_11_impl_oup_mux; // Stubbed

  always_comb begin
    observability_11_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_11_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_11_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[11]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_11_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_11_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[11]),
    .i_dft_oup_en        (i_dft_observability_oup_en[11]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_11_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_11_impl_oup_mux[1]),
    .o_padside_oup       (observability_11_oup),
    .o_padside_oup_en    (observability_11_oup_en),
    .o_padside_pull_type (observability_11_pull_type),
    .o_padside_pull_en   (observability_11_pull_en),
    .o_padside_impl_inp  (observability_11_impl_inp),
    .i_padside_impl_oup  (observability_11_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_11 (
    .i_oup      (observability_11_oup),
    .i_oup_en   (observability_11_oup_en),
    .i_pull_type(observability_11_pull_type),
    .i_pull_en  (observability_11_pull_en),
    .i_impl     (observability_11_impl_inp),
    .o_impl     (observability_11_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_observability[11])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[10]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_10_oup;
  logic observability_10_oup_en;
  logic observability_10_pull_type;
  logic observability_10_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_10_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_10_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_10_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_10_impl_oup_mux; // Stubbed

  always_comb begin
    observability_10_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_10_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_10_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[10]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_10_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_10_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[10]),
    .i_dft_oup_en        (i_dft_observability_oup_en[10]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_10_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_10_impl_oup_mux[1]),
    .o_padside_oup       (observability_10_oup),
    .o_padside_oup_en    (observability_10_oup_en),
    .o_padside_pull_type (observability_10_pull_type),
    .o_padside_pull_en   (observability_10_pull_en),
    .o_padside_impl_inp  (observability_10_impl_inp),
    .i_padside_impl_oup  (observability_10_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_10 (
    .i_oup      (observability_10_oup),
    .i_oup_en   (observability_10_oup_en),
    .i_pull_type(observability_10_pull_type),
    .i_pull_en  (observability_10_pull_en),
    .i_impl     (observability_10_impl_inp),
    .o_impl     (observability_10_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_observability[10])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[9]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_9_oup;
  logic observability_9_oup_en;
  logic observability_9_pull_type;
  logic observability_9_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_9_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_9_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_9_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_9_impl_oup_mux; // Stubbed

  always_comb begin
    observability_9_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_9_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_9_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[9]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_9_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_9_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[9]),
    .i_dft_oup_en        (i_dft_observability_oup_en[9]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_9_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_9_impl_oup_mux[1]),
    .o_padside_oup       (observability_9_oup),
    .o_padside_oup_en    (observability_9_oup_en),
    .o_padside_pull_type (observability_9_pull_type),
    .o_padside_pull_en   (observability_9_pull_en),
    .o_padside_impl_inp  (observability_9_impl_inp),
    .i_padside_impl_oup  (observability_9_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_9 (
    .i_oup      (observability_9_oup),
    .i_oup_en   (observability_9_oup_en),
    .i_pull_type(observability_9_pull_type),
    .i_pull_en  (observability_9_pull_en),
    .i_impl     (observability_9_impl_inp),
    .o_impl     (observability_9_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_observability[9])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[8]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_8_oup;
  logic observability_8_oup_en;
  logic observability_8_pull_type;
  logic observability_8_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_8_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_8_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_8_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_8_impl_oup_mux; // Stubbed

  always_comb begin
    observability_8_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_8_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_8_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[8]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_8_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_8_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[8]),
    .i_dft_oup_en        (i_dft_observability_oup_en[8]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_8_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_8_impl_oup_mux[1]),
    .o_padside_oup       (observability_8_oup),
    .o_padside_oup_en    (observability_8_oup_en),
    .o_padside_pull_type (observability_8_pull_type),
    .o_padside_pull_en   (observability_8_pull_en),
    .o_padside_impl_inp  (observability_8_impl_inp),
    .i_padside_impl_oup  (observability_8_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_8 (
    .i_oup      (observability_8_oup),
    .i_oup_en   (observability_8_oup_en),
    .i_pull_type(observability_8_pull_type),
    .i_pull_en  (observability_8_pull_en),
    .i_impl     (observability_8_impl_inp),
    .o_impl     (observability_8_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_observability[8])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[7]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_7_oup;
  logic observability_7_oup_en;
  logic observability_7_pull_type;
  logic observability_7_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_7_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_7_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_7_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_7_impl_oup_mux; // Stubbed

  always_comb begin
    observability_7_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_7_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_7_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[7]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_7_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_7_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[7]),
    .i_dft_oup_en        (i_dft_observability_oup_en[7]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_7_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_7_impl_oup_mux[1]),
    .o_padside_oup       (observability_7_oup),
    .o_padside_oup_en    (observability_7_oup_en),
    .o_padside_pull_type (observability_7_pull_type),
    .o_padside_pull_en   (observability_7_pull_en),
    .o_padside_impl_inp  (observability_7_impl_inp),
    .i_padside_impl_oup  (observability_7_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_7 (
    .i_oup      (observability_7_oup),
    .i_oup_en   (observability_7_oup_en),
    .i_pull_type(observability_7_pull_type),
    .i_pull_en  (observability_7_pull_en),
    .i_impl     (observability_7_impl_inp),
    .o_impl     (observability_7_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_observability[7])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[6]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_6_oup;
  logic observability_6_oup_en;
  logic observability_6_pull_type;
  logic observability_6_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_6_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_6_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_6_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_6_impl_oup_mux; // Stubbed

  always_comb begin
    observability_6_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_6_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_6_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[6]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_6_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_6_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[6]),
    .i_dft_oup_en        (i_dft_observability_oup_en[6]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_6_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_6_impl_oup_mux[1]),
    .o_padside_oup       (observability_6_oup),
    .o_padside_oup_en    (observability_6_oup_en),
    .o_padside_pull_type (observability_6_pull_type),
    .o_padside_pull_en   (observability_6_pull_en),
    .o_padside_impl_inp  (observability_6_impl_inp),
    .i_padside_impl_oup  (observability_6_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_6 (
    .i_oup      (observability_6_oup),
    .i_oup_en   (observability_6_oup_en),
    .i_pull_type(observability_6_pull_type),
    .i_pull_en  (observability_6_pull_en),
    .i_impl     (observability_6_impl_inp),
    .o_impl     (observability_6_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_observability[6])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[5]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_5_oup;
  logic observability_5_oup_en;
  logic observability_5_pull_type;
  logic observability_5_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_5_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_5_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_5_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_5_impl_oup_mux; // Stubbed

  always_comb begin
    observability_5_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_5_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_5_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[5]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_5_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_5_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[5]),
    .i_dft_oup_en        (i_dft_observability_oup_en[5]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_5_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_5_impl_oup_mux[1]),
    .o_padside_oup       (observability_5_oup),
    .o_padside_oup_en    (observability_5_oup_en),
    .o_padside_pull_type (observability_5_pull_type),
    .o_padside_pull_en   (observability_5_pull_en),
    .o_padside_impl_inp  (observability_5_impl_inp),
    .i_padside_impl_oup  (observability_5_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_5 (
    .i_oup      (observability_5_oup),
    .i_oup_en   (observability_5_oup_en),
    .i_pull_type(observability_5_pull_type),
    .i_pull_en  (observability_5_pull_en),
    .i_impl     (observability_5_impl_inp),
    .o_impl     (observability_5_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_observability[5])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[4]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_4_oup;
  logic observability_4_oup_en;
  logic observability_4_pull_type;
  logic observability_4_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_4_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_4_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_4_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_4_impl_oup_mux; // Stubbed

  always_comb begin
    observability_4_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_4_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_4_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[4]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_4_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_4_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[4]),
    .i_dft_oup_en        (i_dft_observability_oup_en[4]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_4_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_4_impl_oup_mux[1]),
    .o_padside_oup       (observability_4_oup),
    .o_padside_oup_en    (observability_4_oup_en),
    .o_padside_pull_type (observability_4_pull_type),
    .o_padside_pull_en   (observability_4_pull_en),
    .o_padside_impl_inp  (observability_4_impl_inp),
    .i_padside_impl_oup  (observability_4_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_4 (
    .i_oup      (observability_4_oup),
    .i_oup_en   (observability_4_oup_en),
    .i_pull_type(observability_4_pull_type),
    .i_pull_en  (observability_4_pull_en),
    .i_impl     (observability_4_impl_inp),
    .o_impl     (observability_4_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_observability[4])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[3]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_3_oup;
  logic observability_3_oup_en;
  logic observability_3_pull_type;
  logic observability_3_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_3_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_3_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_3_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_3_impl_oup_mux; // Stubbed

  always_comb begin
    observability_3_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_3_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_3_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[3]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_3_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_3_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[3]),
    .i_dft_oup_en        (i_dft_observability_oup_en[3]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_3_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_3_impl_oup_mux[1]),
    .o_padside_oup       (observability_3_oup),
    .o_padside_oup_en    (observability_3_oup_en),
    .o_padside_pull_type (observability_3_pull_type),
    .o_padside_pull_en   (observability_3_pull_en),
    .o_padside_impl_inp  (observability_3_impl_inp),
    .i_padside_impl_oup  (observability_3_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_3 (
    .i_oup      (observability_3_oup),
    .i_oup_en   (observability_3_oup_en),
    .i_pull_type(observability_3_pull_type),
    .i_pull_en  (observability_3_pull_en),
    .i_impl     (observability_3_impl_inp),
    .o_impl     (observability_3_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_observability[3])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[2]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_2_oup;
  logic observability_2_oup_en;
  logic observability_2_pull_type;
  logic observability_2_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_2_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_2_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_2_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_2_impl_oup_mux; // Stubbed

  always_comb begin
    observability_2_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_2_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_2_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[2]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_2_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_2_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[2]),
    .i_dft_oup_en        (i_dft_observability_oup_en[2]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_2_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_2_impl_oup_mux[1]),
    .o_padside_oup       (observability_2_oup),
    .o_padside_oup_en    (observability_2_oup_en),
    .o_padside_pull_type (observability_2_pull_type),
    .o_padside_pull_en   (observability_2_pull_en),
    .o_padside_impl_inp  (observability_2_impl_inp),
    .i_padside_impl_oup  (observability_2_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_2 (
    .i_oup      (observability_2_oup),
    .i_oup_en   (observability_2_oup_en),
    .i_pull_type(observability_2_pull_type),
    .i_pull_en  (observability_2_pull_en),
    .i_impl     (observability_2_impl_inp),
    .o_impl     (observability_2_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_observability[2])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[1]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_1_oup;
  logic observability_1_oup_en;
  logic observability_1_pull_type;
  logic observability_1_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_1_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_1_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_1_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_1_impl_oup_mux; // Stubbed

  always_comb begin
    observability_1_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_1_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_1_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[1]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_1_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_1_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[1]),
    .i_dft_oup_en        (i_dft_observability_oup_en[1]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_1_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_1_impl_oup_mux[1]),
    .o_padside_oup       (observability_1_oup),
    .o_padside_oup_en    (observability_1_oup_en),
    .o_padside_pull_type (observability_1_pull_type),
    .o_padside_pull_en   (observability_1_pull_en),
    .o_padside_impl_inp  (observability_1_impl_inp),
    .i_padside_impl_oup  (observability_1_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_1 (
    .i_oup      (observability_1_oup),
    .i_oup_en   (observability_1_oup_en),
    .i_pull_type(observability_1_pull_type),
    .i_pull_en  (observability_1_pull_en),
    .i_impl     (observability_1_impl_inp),
    .o_impl     (observability_1_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_observability[1])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for observability[0]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic observability_0_oup;
  logic observability_0_oup_en;
  logic observability_0_pull_type;
  logic observability_0_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       observability_0_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       observability_0_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] observability_0_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] observability_0_impl_oup_mux; // Stubbed

  always_comb begin
    observability_0_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  i_obs_drive,
      poe: 1'b0  // Stubbed
    };
    observability_0_impl_inp_mux[1] = '{
      is:  i_dft_observability_schmitt,
      ds:  i_dft_observability_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_output #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_output_observability_0_dft_mux (
    .i_dft_enable,
    .i_func_oup          (i_observability[0]),
    .i_func_oup_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b0),
    .i_func_impl_inp     (observability_0_impl_inp_mux[0]),
    .o_func_impl_oup     (observability_0_impl_oup_mux[0]),
    .i_dft_oup           (i_dft_observability_oup[0]),
    .i_dft_oup_en        (i_dft_observability_oup_en[0]),
    .i_dft_pull_type     (i_dft_observability_pull_type),
    .i_dft_pull_en       (i_dft_observability_pull_en),
    .i_dft_impl_inp      (observability_0_impl_inp_mux[1]),
    .o_dft_impl_oup      (observability_0_impl_oup_mux[1]),
    .o_padside_oup       (observability_0_oup),
    .o_padside_oup_en    (observability_0_oup_en),
    .o_padside_pull_type (observability_0_pull_type),
    .o_padside_pull_en   (observability_0_pull_en),
    .o_padside_impl_inp  (observability_0_impl_inp),
    .i_padside_impl_oup  (observability_0_impl_oup)
  );

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_observability_0 (
    .i_oup      (observability_0_oup),
    .i_oup_en   (observability_0_oup_en),
    .i_pull_type(observability_0_pull_type),
    .i_pull_en  (observability_0_pull_en),
    .i_impl     (observability_0_impl_inp),
    .o_impl     (observability_0_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_observability[0])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for thermal_warning_n
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic thermal_warning_n_oup;
  logic thermal_warning_n_oup_en;
  logic thermal_warning_n_pull_type;
  logic thermal_warning_n_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       thermal_warning_n_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       thermal_warning_n_impl_oup; // Stubbed
  always_comb thermal_warning_n_oup       = 1'b0;
  always_comb thermal_warning_n_oup_en    = (1'b1 ^ i_thermal_warning_n);
  always_comb thermal_warning_n_pull_type = 1'b0;
  always_comb thermal_warning_n_pull_en   = 1'b0;

  always_comb thermal_warning_n_impl_inp = '{
    is:  1'b0,
    ds:  i_obs_drive,
    poe: 1'b0
  };

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_thermal_warning_n (
    .i_oup      (thermal_warning_n_oup),
    .i_oup_en   (thermal_warning_n_oup_en),
    .i_pull_type(thermal_warning_n_pull_type),
    .i_pull_en  (thermal_warning_n_pull_en),
    .i_impl     (thermal_warning_n_impl_inp),
    .o_impl     (thermal_warning_n_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_thermal_warning_n)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for thermal_shutdown_n
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic thermal_shutdown_n_oup;
  logic thermal_shutdown_n_oup_en;
  logic thermal_shutdown_n_pull_type;
  logic thermal_shutdown_n_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       thermal_shutdown_n_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       thermal_shutdown_n_impl_oup; // Stubbed
  always_comb thermal_shutdown_n_oup       = 1'b0;
  always_comb thermal_shutdown_n_oup_en    = (1'b1 ^ i_thermal_shutdown_n);
  always_comb thermal_shutdown_n_pull_type = 1'b0;
  always_comb thermal_shutdown_n_pull_en   = 1'b0;

  always_comb thermal_shutdown_n_impl_inp = '{
    is:  1'b0,
    ds:  i_obs_drive,
    poe: 1'b0
  };

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_thermal_shutdown_n (
    .i_oup      (thermal_shutdown_n_oup),
    .i_oup_en   (thermal_shutdown_n_oup_en),
    .i_pull_type(thermal_shutdown_n_pull_type),
    .i_pull_en  (thermal_shutdown_n_pull_en),
    .i_impl     (thermal_shutdown_n_impl_inp),
    .o_impl     (thermal_shutdown_n_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .o_pad      (o_pad_thermal_shutdown_n)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for thermal_throttle
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic thermal_throttle_inp;
  logic thermal_throttle_inp_en;
  logic thermal_throttle_pull_type;
  logic thermal_throttle_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       thermal_throttle_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       thermal_throttle_impl_oup; // Stubbed
  always_comb o_thermal_throttle = thermal_throttle_inp;
  always_comb thermal_throttle_inp_en    = 1'b1;
  always_comb thermal_throttle_pull_type = 1'b0;
  always_comb thermal_throttle_pull_en   = 1'b1;

  always_comb thermal_throttle_impl_inp = '{
    is:  1'b0,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_thermal_throttle (
    .o_inp      (thermal_throttle_inp),
    .i_inp_en   (thermal_throttle_inp_en),
    .i_pull_type(thermal_throttle_pull_type),
    .i_pull_en  (thermal_throttle_pull_en),
    .i_impl     (thermal_throttle_impl_inp),
    .o_impl     (thermal_throttle_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .i_pad      (i_pad_thermal_throttle)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for throttle
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic throttle_inp;
  logic throttle_inp_en;
  logic throttle_pull_type;
  logic throttle_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       throttle_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       throttle_impl_oup; // Stubbed
  axe_tcl_pad_pkg::impl_pad_slow_inp_t [1:0] throttle_impl_inp_mux;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t [1:0] throttle_impl_oup_mux; // Stubbed

  always_comb begin
    throttle_impl_inp_mux[0] = '{
      is:  1'b0,
      ds:  '0,
      poe: 1'b0  // Stubbed
    };
    throttle_impl_inp_mux[1] = '{
      is:  i_dft_throttle_schmitt,
      ds:  i_dft_throttle_drive,
      poe: 1'b0  // Stubbed
    };
  end

  axe_ccl_dft_pad_mux_input #(
    .impl_inp_t(axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t(axe_tcl_pad_pkg::impl_pad_slow_oup_t)
  ) u_input_throttle_dft_mux (
    .i_dft_enable,
    .o_func_inp          (o_throttle),
    .i_func_inp_en       (1'b1),
    .i_func_pull_type    (1'b0),
    .i_func_pull_en      (1'b1),
    .i_func_impl_inp     (throttle_impl_inp_mux[0]),
    .o_func_impl_oup     (throttle_impl_oup_mux[0]),
    .o_dft_inp           (o_dft_throttle_inp),
    .i_dft_inp_en        (i_dft_throttle_inp_en),
    .i_dft_pull_type     (i_dft_throttle_pull_type),
    .i_dft_pull_en       (i_dft_throttle_pull_en),
    .i_dft_impl_inp      (throttle_impl_inp_mux[1]),
    .o_dft_impl_oup      (throttle_impl_oup_mux[1]),
    .i_padside_inp       (throttle_inp),
    .o_padside_inp_en    (throttle_inp_en),
    .o_padside_pull_type (throttle_pull_type),
    .o_padside_pull_en   (throttle_pull_en),
    .o_padside_impl_inp  (throttle_impl_inp),
    .i_padside_impl_oup  (throttle_impl_oup)
  );

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_throttle (
    .o_inp      (throttle_inp),
    .i_inp_en   (throttle_inp_en),
    .i_pull_type(throttle_pull_type),
    .i_pull_en  (throttle_pull_en),
    .i_impl     (throttle_impl_inp),
    .o_impl     (throttle_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_throttle)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for boot_mode[2]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic boot_mode_2_inp;
  logic boot_mode_2_inp_en;
  logic boot_mode_2_pull_type;
  logic boot_mode_2_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       boot_mode_2_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       boot_mode_2_impl_oup; // Stubbed
  always_comb o_boot_mode[2] = boot_mode_2_inp;
  always_comb boot_mode_2_inp_en    = 1'b1;
  always_comb boot_mode_2_pull_type = 1'b0;
  always_comb boot_mode_2_pull_en   = i_bootmode_pull_en[2];

  always_comb boot_mode_2_impl_inp = '{
    is:  1'b0,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_boot_mode_2 (
    .o_inp      (boot_mode_2_inp),
    .i_inp_en   (boot_mode_2_inp_en),
    .i_pull_type(boot_mode_2_pull_type),
    .i_pull_en  (boot_mode_2_pull_en),
    .i_impl     (boot_mode_2_impl_inp),
    .o_impl     (boot_mode_2_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_boot_mode[2])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for boot_mode[1]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic boot_mode_1_inp;
  logic boot_mode_1_inp_en;
  logic boot_mode_1_pull_type;
  logic boot_mode_1_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       boot_mode_1_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       boot_mode_1_impl_oup; // Stubbed
  always_comb o_boot_mode[1] = boot_mode_1_inp;
  always_comb boot_mode_1_inp_en    = 1'b1;
  always_comb boot_mode_1_pull_type = 1'b0;
  always_comb boot_mode_1_pull_en   = i_bootmode_pull_en[1];

  always_comb boot_mode_1_impl_inp = '{
    is:  1'b0,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_boot_mode_1 (
    .o_inp      (boot_mode_1_inp),
    .i_inp_en   (boot_mode_1_inp_en),
    .i_pull_type(boot_mode_1_pull_type),
    .i_pull_en  (boot_mode_1_pull_en),
    .i_impl     (boot_mode_1_impl_inp),
    .o_impl     (boot_mode_1_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .i_pad      (i_pad_boot_mode[1])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for boot_mode[0]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic boot_mode_0_inp;
  logic boot_mode_0_inp_en;
  logic boot_mode_0_pull_type;
  logic boot_mode_0_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       boot_mode_0_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       boot_mode_0_impl_oup; // Stubbed
  always_comb o_boot_mode[0] = boot_mode_0_inp;
  always_comb boot_mode_0_inp_en    = 1'b1;
  always_comb boot_mode_0_pull_type = 1'b1;
  always_comb boot_mode_0_pull_en   = i_bootmode_pull_en[0];

  always_comb boot_mode_0_impl_inp = '{
    is:  1'b0,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_boot_mode_0 (
    .o_inp      (boot_mode_0_inp),
    .i_inp_en   (boot_mode_0_inp_en),
    .i_pull_type(boot_mode_0_pull_type),
    .i_pull_en  (boot_mode_0_pull_en),
    .i_impl     (boot_mode_0_impl_inp),
    .o_impl     (boot_mode_0_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_boot_mode[0])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for tms
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic tms_inp;
  logic tms_inp_en;
  logic tms_pull_type;
  logic tms_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       tms_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       tms_impl_oup; // Stubbed
  always_comb o_tms = tms_inp;
  always_comb tms_inp_en    = 1'b1;
  always_comb tms_pull_type = 1'b0;
  always_comb tms_pull_en   = 1'b0;

  always_comb tms_impl_inp = '{
    is:  1'b0,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_tms (
    .o_inp      (tms_inp),
    .i_inp_en   (tms_inp_en),
    .i_pull_type(tms_pull_type),
    .i_pull_en  (tms_pull_en),
    .i_impl     (tms_impl_inp),
    .o_impl     (tms_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .i_pad      (i_pad_tms)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Input Pad instantiation for td_in
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic td_in_inp;
  logic td_in_inp_en;
  logic td_in_pull_type;
  logic td_in_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       td_in_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       td_in_impl_oup; // Stubbed
  always_comb o_td = td_in_inp;
  always_comb td_in_inp_en    = 1'b1;
  always_comb td_in_pull_type = 1'b0;
  always_comb td_in_pull_en   = 1'b0;

  always_comb td_in_impl_inp = '{
    is:  1'b0,
    ds:  '0,
    poe: 1'b0
  };

  axe_tcl_pad_input #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_input_td_in (
    .o_inp      (td_in_inp),
    .i_inp_en   (td_in_inp_en),
    .i_pull_type(td_in_pull_type),
    .i_pull_en  (td_in_pull_en),
    .i_impl     (td_in_impl_inp),
    .o_impl     (td_in_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .i_pad      (i_pad_td_in)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Output Pad instantiation for td_out
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic td_out_oup;
  logic td_out_oup_en;
  logic td_out_pull_type;
  logic td_out_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       td_out_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       td_out_impl_oup; // Stubbed
  always_comb td_out_oup       = i_td;
  always_comb td_out_oup_en    = 1'b1;
  always_comb td_out_pull_type = 1'b0;
  always_comb td_out_pull_en   = 1'b0;

  always_comb td_out_impl_inp = '{
    is:  1'b0,
    ds:  i_jtag_drive,
    poe: 1'b0
  };

  axe_tcl_pad_output #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_output_td_out (
    .i_oup      (td_out_oup),
    .i_oup_en   (td_out_oup_en),
    .i_pull_type(td_out_pull_type),
    .i_pull_en  (td_out_pull_en),
    .i_impl     (td_out_impl_inp),
    .o_impl     (td_out_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .o_pad      (o_pad_td_out)
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[44]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_44_oup;
  logic dft_test_44_oup_en;
  logic dft_test_44_inp;
  logic dft_test_44_inp_en;
  logic dft_test_44_pull_type;
  logic dft_test_44_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_44_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_44_impl_oup; // Stubbed
  always_comb dft_test_44_oup       = i_dft_test[44];
  always_comb dft_test_44_oup_en    = i_dft_test_oe[44];
  always_comb o_dft_test[44] = dft_test_44_inp;
  always_comb dft_test_44_inp_en    = (1'b1 ^ i_dft_test_oe[44]);
  always_comb dft_test_44_pull_type = i_dft_pull_type;
  always_comb dft_test_44_pull_en   = i_dft_pull_en;

  always_comb dft_test_44_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_44 (
    .i_oup      (dft_test_44_oup),
    .i_oup_en   (dft_test_44_oup_en),
    .o_inp      (dft_test_44_inp),
    .i_inp_en   (dft_test_44_inp_en),
    .i_pull_type(dft_test_44_pull_type),
    .i_pull_en  (dft_test_44_pull_en),
    .i_impl     (dft_test_44_impl_inp),
    .o_impl     (dft_test_44_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[44])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[43]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_43_oup;
  logic dft_test_43_oup_en;
  logic dft_test_43_inp;
  logic dft_test_43_inp_en;
  logic dft_test_43_pull_type;
  logic dft_test_43_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_43_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_43_impl_oup; // Stubbed
  always_comb dft_test_43_oup       = i_dft_test[43];
  always_comb dft_test_43_oup_en    = i_dft_test_oe[43];
  always_comb o_dft_test[43] = dft_test_43_inp;
  always_comb dft_test_43_inp_en    = (1'b1 ^ i_dft_test_oe[43]);
  always_comb dft_test_43_pull_type = i_dft_pull_type;
  always_comb dft_test_43_pull_en   = i_dft_pull_en;

  always_comb dft_test_43_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_43 (
    .i_oup      (dft_test_43_oup),
    .i_oup_en   (dft_test_43_oup_en),
    .o_inp      (dft_test_43_inp),
    .i_inp_en   (dft_test_43_inp_en),
    .i_pull_type(dft_test_43_pull_type),
    .i_pull_en  (dft_test_43_pull_en),
    .i_impl     (dft_test_43_impl_inp),
    .o_impl     (dft_test_43_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[43])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[42]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_42_oup;
  logic dft_test_42_oup_en;
  logic dft_test_42_inp;
  logic dft_test_42_inp_en;
  logic dft_test_42_pull_type;
  logic dft_test_42_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_42_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_42_impl_oup; // Stubbed
  always_comb dft_test_42_oup       = i_dft_test[42];
  always_comb dft_test_42_oup_en    = i_dft_test_oe[42];
  always_comb o_dft_test[42] = dft_test_42_inp;
  always_comb dft_test_42_inp_en    = (1'b1 ^ i_dft_test_oe[42]);
  always_comb dft_test_42_pull_type = i_dft_pull_type;
  always_comb dft_test_42_pull_en   = i_dft_pull_en;

  always_comb dft_test_42_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_42 (
    .i_oup      (dft_test_42_oup),
    .i_oup_en   (dft_test_42_oup_en),
    .o_inp      (dft_test_42_inp),
    .i_inp_en   (dft_test_42_inp_en),
    .i_pull_type(dft_test_42_pull_type),
    .i_pull_en  (dft_test_42_pull_en),
    .i_impl     (dft_test_42_impl_inp),
    .o_impl     (dft_test_42_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[42])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[41]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_41_oup;
  logic dft_test_41_oup_en;
  logic dft_test_41_inp;
  logic dft_test_41_inp_en;
  logic dft_test_41_pull_type;
  logic dft_test_41_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_41_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_41_impl_oup; // Stubbed
  always_comb dft_test_41_oup       = i_dft_test[41];
  always_comb dft_test_41_oup_en    = i_dft_test_oe[41];
  always_comb o_dft_test[41] = dft_test_41_inp;
  always_comb dft_test_41_inp_en    = (1'b1 ^ i_dft_test_oe[41]);
  always_comb dft_test_41_pull_type = i_dft_pull_type;
  always_comb dft_test_41_pull_en   = i_dft_pull_en;

  always_comb dft_test_41_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_41 (
    .i_oup      (dft_test_41_oup),
    .i_oup_en   (dft_test_41_oup_en),
    .o_inp      (dft_test_41_inp),
    .i_inp_en   (dft_test_41_inp_en),
    .i_pull_type(dft_test_41_pull_type),
    .i_pull_en  (dft_test_41_pull_en),
    .i_impl     (dft_test_41_impl_inp),
    .o_impl     (dft_test_41_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[41])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[40]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_40_oup;
  logic dft_test_40_oup_en;
  logic dft_test_40_inp;
  logic dft_test_40_inp_en;
  logic dft_test_40_pull_type;
  logic dft_test_40_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_40_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_40_impl_oup; // Stubbed
  always_comb dft_test_40_oup       = i_dft_test[40];
  always_comb dft_test_40_oup_en    = i_dft_test_oe[40];
  always_comb o_dft_test[40] = dft_test_40_inp;
  always_comb dft_test_40_inp_en    = (1'b1 ^ i_dft_test_oe[40]);
  always_comb dft_test_40_pull_type = i_dft_pull_type;
  always_comb dft_test_40_pull_en   = i_dft_pull_en;

  always_comb dft_test_40_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_40 (
    .i_oup      (dft_test_40_oup),
    .i_oup_en   (dft_test_40_oup_en),
    .o_inp      (dft_test_40_inp),
    .i_inp_en   (dft_test_40_inp_en),
    .i_pull_type(dft_test_40_pull_type),
    .i_pull_en  (dft_test_40_pull_en),
    .i_impl     (dft_test_40_impl_inp),
    .o_impl     (dft_test_40_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[40])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[39]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_39_oup;
  logic dft_test_39_oup_en;
  logic dft_test_39_inp;
  logic dft_test_39_inp_en;
  logic dft_test_39_pull_type;
  logic dft_test_39_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_39_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_39_impl_oup; // Stubbed
  always_comb dft_test_39_oup       = i_dft_test[39];
  always_comb dft_test_39_oup_en    = i_dft_test_oe[39];
  always_comb o_dft_test[39] = dft_test_39_inp;
  always_comb dft_test_39_inp_en    = (1'b1 ^ i_dft_test_oe[39]);
  always_comb dft_test_39_pull_type = i_dft_pull_type;
  always_comb dft_test_39_pull_en   = i_dft_pull_en;

  always_comb dft_test_39_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_39 (
    .i_oup      (dft_test_39_oup),
    .i_oup_en   (dft_test_39_oup_en),
    .o_inp      (dft_test_39_inp),
    .i_inp_en   (dft_test_39_inp_en),
    .i_pull_type(dft_test_39_pull_type),
    .i_pull_en  (dft_test_39_pull_en),
    .i_impl     (dft_test_39_impl_inp),
    .o_impl     (dft_test_39_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[39])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[38]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_38_oup;
  logic dft_test_38_oup_en;
  logic dft_test_38_inp;
  logic dft_test_38_inp_en;
  logic dft_test_38_pull_type;
  logic dft_test_38_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_38_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_38_impl_oup; // Stubbed
  always_comb dft_test_38_oup       = i_dft_test[38];
  always_comb dft_test_38_oup_en    = i_dft_test_oe[38];
  always_comb o_dft_test[38] = dft_test_38_inp;
  always_comb dft_test_38_inp_en    = (1'b1 ^ i_dft_test_oe[38]);
  always_comb dft_test_38_pull_type = i_dft_pull_type;
  always_comb dft_test_38_pull_en   = i_dft_pull_en;

  always_comb dft_test_38_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_38 (
    .i_oup      (dft_test_38_oup),
    .i_oup_en   (dft_test_38_oup_en),
    .o_inp      (dft_test_38_inp),
    .i_inp_en   (dft_test_38_inp_en),
    .i_pull_type(dft_test_38_pull_type),
    .i_pull_en  (dft_test_38_pull_en),
    .i_impl     (dft_test_38_impl_inp),
    .o_impl     (dft_test_38_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[38])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[37]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_37_oup;
  logic dft_test_37_oup_en;
  logic dft_test_37_inp;
  logic dft_test_37_inp_en;
  logic dft_test_37_pull_type;
  logic dft_test_37_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_37_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_37_impl_oup; // Stubbed
  always_comb dft_test_37_oup       = i_dft_test[37];
  always_comb dft_test_37_oup_en    = i_dft_test_oe[37];
  always_comb o_dft_test[37] = dft_test_37_inp;
  always_comb dft_test_37_inp_en    = (1'b1 ^ i_dft_test_oe[37]);
  always_comb dft_test_37_pull_type = i_dft_pull_type;
  always_comb dft_test_37_pull_en   = i_dft_pull_en;

  always_comb dft_test_37_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_37 (
    .i_oup      (dft_test_37_oup),
    .i_oup_en   (dft_test_37_oup_en),
    .o_inp      (dft_test_37_inp),
    .i_inp_en   (dft_test_37_inp_en),
    .i_pull_type(dft_test_37_pull_type),
    .i_pull_en  (dft_test_37_pull_en),
    .i_impl     (dft_test_37_impl_inp),
    .o_impl     (dft_test_37_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[37])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[36]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_36_oup;
  logic dft_test_36_oup_en;
  logic dft_test_36_inp;
  logic dft_test_36_inp_en;
  logic dft_test_36_pull_type;
  logic dft_test_36_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_36_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_36_impl_oup; // Stubbed
  always_comb dft_test_36_oup       = i_dft_test[36];
  always_comb dft_test_36_oup_en    = i_dft_test_oe[36];
  always_comb o_dft_test[36] = dft_test_36_inp;
  always_comb dft_test_36_inp_en    = (1'b1 ^ i_dft_test_oe[36]);
  always_comb dft_test_36_pull_type = i_dft_pull_type;
  always_comb dft_test_36_pull_en   = i_dft_pull_en;

  always_comb dft_test_36_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_36 (
    .i_oup      (dft_test_36_oup),
    .i_oup_en   (dft_test_36_oup_en),
    .o_inp      (dft_test_36_inp),
    .i_inp_en   (dft_test_36_inp_en),
    .i_pull_type(dft_test_36_pull_type),
    .i_pull_en  (dft_test_36_pull_en),
    .i_impl     (dft_test_36_impl_inp),
    .o_impl     (dft_test_36_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[36])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[35]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_35_oup;
  logic dft_test_35_oup_en;
  logic dft_test_35_inp;
  logic dft_test_35_inp_en;
  logic dft_test_35_pull_type;
  logic dft_test_35_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_35_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_35_impl_oup; // Stubbed
  always_comb dft_test_35_oup       = i_dft_test[35];
  always_comb dft_test_35_oup_en    = i_dft_test_oe[35];
  always_comb o_dft_test[35] = dft_test_35_inp;
  always_comb dft_test_35_inp_en    = (1'b1 ^ i_dft_test_oe[35]);
  always_comb dft_test_35_pull_type = i_dft_pull_type;
  always_comb dft_test_35_pull_en   = i_dft_pull_en;

  always_comb dft_test_35_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_35 (
    .i_oup      (dft_test_35_oup),
    .i_oup_en   (dft_test_35_oup_en),
    .o_inp      (dft_test_35_inp),
    .i_inp_en   (dft_test_35_inp_en),
    .i_pull_type(dft_test_35_pull_type),
    .i_pull_en  (dft_test_35_pull_en),
    .i_impl     (dft_test_35_impl_inp),
    .o_impl     (dft_test_35_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[35])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[34]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_34_oup;
  logic dft_test_34_oup_en;
  logic dft_test_34_inp;
  logic dft_test_34_inp_en;
  logic dft_test_34_pull_type;
  logic dft_test_34_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_34_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_34_impl_oup; // Stubbed
  always_comb dft_test_34_oup       = i_dft_test[34];
  always_comb dft_test_34_oup_en    = i_dft_test_oe[34];
  always_comb o_dft_test[34] = dft_test_34_inp;
  always_comb dft_test_34_inp_en    = (1'b1 ^ i_dft_test_oe[34]);
  always_comb dft_test_34_pull_type = i_dft_pull_type;
  always_comb dft_test_34_pull_en   = i_dft_pull_en;

  always_comb dft_test_34_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_34 (
    .i_oup      (dft_test_34_oup),
    .i_oup_en   (dft_test_34_oup_en),
    .o_inp      (dft_test_34_inp),
    .i_inp_en   (dft_test_34_inp_en),
    .i_pull_type(dft_test_34_pull_type),
    .i_pull_en  (dft_test_34_pull_en),
    .i_impl     (dft_test_34_impl_inp),
    .o_impl     (dft_test_34_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[34])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[33]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_33_oup;
  logic dft_test_33_oup_en;
  logic dft_test_33_inp;
  logic dft_test_33_inp_en;
  logic dft_test_33_pull_type;
  logic dft_test_33_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_33_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_33_impl_oup; // Stubbed
  always_comb dft_test_33_oup       = i_dft_test[33];
  always_comb dft_test_33_oup_en    = i_dft_test_oe[33];
  always_comb o_dft_test[33] = dft_test_33_inp;
  always_comb dft_test_33_inp_en    = (1'b1 ^ i_dft_test_oe[33]);
  always_comb dft_test_33_pull_type = i_dft_pull_type;
  always_comb dft_test_33_pull_en   = i_dft_pull_en;

  always_comb dft_test_33_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_33 (
    .i_oup      (dft_test_33_oup),
    .i_oup_en   (dft_test_33_oup_en),
    .o_inp      (dft_test_33_inp),
    .i_inp_en   (dft_test_33_inp_en),
    .i_pull_type(dft_test_33_pull_type),
    .i_pull_en  (dft_test_33_pull_en),
    .i_impl     (dft_test_33_impl_inp),
    .o_impl     (dft_test_33_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[33])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[32]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_32_oup;
  logic dft_test_32_oup_en;
  logic dft_test_32_inp;
  logic dft_test_32_inp_en;
  logic dft_test_32_pull_type;
  logic dft_test_32_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_32_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_32_impl_oup; // Stubbed
  always_comb dft_test_32_oup       = i_dft_test[32];
  always_comb dft_test_32_oup_en    = i_dft_test_oe[32];
  always_comb o_dft_test[32] = dft_test_32_inp;
  always_comb dft_test_32_inp_en    = (1'b1 ^ i_dft_test_oe[32]);
  always_comb dft_test_32_pull_type = i_dft_pull_type;
  always_comb dft_test_32_pull_en   = i_dft_pull_en;

  always_comb dft_test_32_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_32 (
    .i_oup      (dft_test_32_oup),
    .i_oup_en   (dft_test_32_oup_en),
    .o_inp      (dft_test_32_inp),
    .i_inp_en   (dft_test_32_inp_en),
    .i_pull_type(dft_test_32_pull_type),
    .i_pull_en  (dft_test_32_pull_en),
    .i_impl     (dft_test_32_impl_inp),
    .o_impl     (dft_test_32_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[32])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[31]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_31_oup;
  logic dft_test_31_oup_en;
  logic dft_test_31_inp;
  logic dft_test_31_inp_en;
  logic dft_test_31_pull_type;
  logic dft_test_31_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_31_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_31_impl_oup; // Stubbed
  always_comb dft_test_31_oup       = i_dft_test[31];
  always_comb dft_test_31_oup_en    = i_dft_test_oe[31];
  always_comb o_dft_test[31] = dft_test_31_inp;
  always_comb dft_test_31_inp_en    = (1'b1 ^ i_dft_test_oe[31]);
  always_comb dft_test_31_pull_type = i_dft_pull_type;
  always_comb dft_test_31_pull_en   = i_dft_pull_en;

  always_comb dft_test_31_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_31 (
    .i_oup      (dft_test_31_oup),
    .i_oup_en   (dft_test_31_oup_en),
    .o_inp      (dft_test_31_inp),
    .i_inp_en   (dft_test_31_inp_en),
    .i_pull_type(dft_test_31_pull_type),
    .i_pull_en  (dft_test_31_pull_en),
    .i_impl     (dft_test_31_impl_inp),
    .o_impl     (dft_test_31_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[31])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[30]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_30_oup;
  logic dft_test_30_oup_en;
  logic dft_test_30_inp;
  logic dft_test_30_inp_en;
  logic dft_test_30_pull_type;
  logic dft_test_30_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_30_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_30_impl_oup; // Stubbed
  always_comb dft_test_30_oup       = i_dft_test[30];
  always_comb dft_test_30_oup_en    = i_dft_test_oe[30];
  always_comb o_dft_test[30] = dft_test_30_inp;
  always_comb dft_test_30_inp_en    = (1'b1 ^ i_dft_test_oe[30]);
  always_comb dft_test_30_pull_type = i_dft_pull_type;
  always_comb dft_test_30_pull_en   = i_dft_pull_en;

  always_comb dft_test_30_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_30 (
    .i_oup      (dft_test_30_oup),
    .i_oup_en   (dft_test_30_oup_en),
    .o_inp      (dft_test_30_inp),
    .i_inp_en   (dft_test_30_inp_en),
    .i_pull_type(dft_test_30_pull_type),
    .i_pull_en  (dft_test_30_pull_en),
    .i_impl     (dft_test_30_impl_inp),
    .o_impl     (dft_test_30_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[30])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[29]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_29_oup;
  logic dft_test_29_oup_en;
  logic dft_test_29_inp;
  logic dft_test_29_inp_en;
  logic dft_test_29_pull_type;
  logic dft_test_29_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_29_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_29_impl_oup; // Stubbed
  always_comb dft_test_29_oup       = i_dft_test[29];
  always_comb dft_test_29_oup_en    = i_dft_test_oe[29];
  always_comb o_dft_test[29] = dft_test_29_inp;
  always_comb dft_test_29_inp_en    = (1'b1 ^ i_dft_test_oe[29]);
  always_comb dft_test_29_pull_type = i_dft_pull_type;
  always_comb dft_test_29_pull_en   = i_dft_pull_en;

  always_comb dft_test_29_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_29 (
    .i_oup      (dft_test_29_oup),
    .i_oup_en   (dft_test_29_oup_en),
    .o_inp      (dft_test_29_inp),
    .i_inp_en   (dft_test_29_inp_en),
    .i_pull_type(dft_test_29_pull_type),
    .i_pull_en  (dft_test_29_pull_en),
    .i_impl     (dft_test_29_impl_inp),
    .o_impl     (dft_test_29_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[29])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[28]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_28_oup;
  logic dft_test_28_oup_en;
  logic dft_test_28_inp;
  logic dft_test_28_inp_en;
  logic dft_test_28_pull_type;
  logic dft_test_28_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_28_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_28_impl_oup; // Stubbed
  always_comb dft_test_28_oup       = i_dft_test[28];
  always_comb dft_test_28_oup_en    = i_dft_test_oe[28];
  always_comb o_dft_test[28] = dft_test_28_inp;
  always_comb dft_test_28_inp_en    = (1'b1 ^ i_dft_test_oe[28]);
  always_comb dft_test_28_pull_type = i_dft_pull_type;
  always_comb dft_test_28_pull_en   = i_dft_pull_en;

  always_comb dft_test_28_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_28 (
    .i_oup      (dft_test_28_oup),
    .i_oup_en   (dft_test_28_oup_en),
    .o_inp      (dft_test_28_inp),
    .i_inp_en   (dft_test_28_inp_en),
    .i_pull_type(dft_test_28_pull_type),
    .i_pull_en  (dft_test_28_pull_en),
    .i_impl     (dft_test_28_impl_inp),
    .o_impl     (dft_test_28_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[28])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[27]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_27_oup;
  logic dft_test_27_oup_en;
  logic dft_test_27_inp;
  logic dft_test_27_inp_en;
  logic dft_test_27_pull_type;
  logic dft_test_27_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_27_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_27_impl_oup; // Stubbed
  always_comb dft_test_27_oup       = i_dft_test[27];
  always_comb dft_test_27_oup_en    = i_dft_test_oe[27];
  always_comb o_dft_test[27] = dft_test_27_inp;
  always_comb dft_test_27_inp_en    = (1'b1 ^ i_dft_test_oe[27]);
  always_comb dft_test_27_pull_type = i_dft_pull_type;
  always_comb dft_test_27_pull_en   = i_dft_pull_en;

  always_comb dft_test_27_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_27 (
    .i_oup      (dft_test_27_oup),
    .i_oup_en   (dft_test_27_oup_en),
    .o_inp      (dft_test_27_inp),
    .i_inp_en   (dft_test_27_inp_en),
    .i_pull_type(dft_test_27_pull_type),
    .i_pull_en  (dft_test_27_pull_en),
    .i_impl     (dft_test_27_impl_inp),
    .o_impl     (dft_test_27_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[27])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[26]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_26_oup;
  logic dft_test_26_oup_en;
  logic dft_test_26_inp;
  logic dft_test_26_inp_en;
  logic dft_test_26_pull_type;
  logic dft_test_26_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_26_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_26_impl_oup; // Stubbed
  always_comb dft_test_26_oup       = i_dft_test[26];
  always_comb dft_test_26_oup_en    = i_dft_test_oe[26];
  always_comb o_dft_test[26] = dft_test_26_inp;
  always_comb dft_test_26_inp_en    = (1'b1 ^ i_dft_test_oe[26]);
  always_comb dft_test_26_pull_type = i_dft_pull_type;
  always_comb dft_test_26_pull_en   = i_dft_pull_en;

  always_comb dft_test_26_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_26 (
    .i_oup      (dft_test_26_oup),
    .i_oup_en   (dft_test_26_oup_en),
    .o_inp      (dft_test_26_inp),
    .i_inp_en   (dft_test_26_inp_en),
    .i_pull_type(dft_test_26_pull_type),
    .i_pull_en  (dft_test_26_pull_en),
    .i_impl     (dft_test_26_impl_inp),
    .o_impl     (dft_test_26_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[26])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[25]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_25_oup;
  logic dft_test_25_oup_en;
  logic dft_test_25_inp;
  logic dft_test_25_inp_en;
  logic dft_test_25_pull_type;
  logic dft_test_25_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_25_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_25_impl_oup; // Stubbed
  always_comb dft_test_25_oup       = i_dft_test[25];
  always_comb dft_test_25_oup_en    = i_dft_test_oe[25];
  always_comb o_dft_test[25] = dft_test_25_inp;
  always_comb dft_test_25_inp_en    = (1'b1 ^ i_dft_test_oe[25]);
  always_comb dft_test_25_pull_type = i_dft_pull_type;
  always_comb dft_test_25_pull_en   = i_dft_pull_en;

  always_comb dft_test_25_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_25 (
    .i_oup      (dft_test_25_oup),
    .i_oup_en   (dft_test_25_oup_en),
    .o_inp      (dft_test_25_inp),
    .i_inp_en   (dft_test_25_inp_en),
    .i_pull_type(dft_test_25_pull_type),
    .i_pull_en  (dft_test_25_pull_en),
    .i_impl     (dft_test_25_impl_inp),
    .o_impl     (dft_test_25_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[25])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[24]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_24_oup;
  logic dft_test_24_oup_en;
  logic dft_test_24_inp;
  logic dft_test_24_inp_en;
  logic dft_test_24_pull_type;
  logic dft_test_24_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_24_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_24_impl_oup; // Stubbed
  always_comb dft_test_24_oup       = i_dft_test[24];
  always_comb dft_test_24_oup_en    = i_dft_test_oe[24];
  always_comb o_dft_test[24] = dft_test_24_inp;
  always_comb dft_test_24_inp_en    = (1'b1 ^ i_dft_test_oe[24]);
  always_comb dft_test_24_pull_type = i_dft_pull_type;
  always_comb dft_test_24_pull_en   = i_dft_pull_en;

  always_comb dft_test_24_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_24 (
    .i_oup      (dft_test_24_oup),
    .i_oup_en   (dft_test_24_oup_en),
    .o_inp      (dft_test_24_inp),
    .i_inp_en   (dft_test_24_inp_en),
    .i_pull_type(dft_test_24_pull_type),
    .i_pull_en  (dft_test_24_pull_en),
    .i_impl     (dft_test_24_impl_inp),
    .o_impl     (dft_test_24_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[24])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[23]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_23_oup;
  logic dft_test_23_oup_en;
  logic dft_test_23_inp;
  logic dft_test_23_inp_en;
  logic dft_test_23_pull_type;
  logic dft_test_23_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_23_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_23_impl_oup; // Stubbed
  always_comb dft_test_23_oup       = i_dft_test[23];
  always_comb dft_test_23_oup_en    = i_dft_test_oe[23];
  always_comb o_dft_test[23] = dft_test_23_inp;
  always_comb dft_test_23_inp_en    = (1'b1 ^ i_dft_test_oe[23]);
  always_comb dft_test_23_pull_type = i_dft_pull_type;
  always_comb dft_test_23_pull_en   = i_dft_pull_en;

  always_comb dft_test_23_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_23 (
    .i_oup      (dft_test_23_oup),
    .i_oup_en   (dft_test_23_oup_en),
    .o_inp      (dft_test_23_inp),
    .i_inp_en   (dft_test_23_inp_en),
    .i_pull_type(dft_test_23_pull_type),
    .i_pull_en  (dft_test_23_pull_en),
    .i_impl     (dft_test_23_impl_inp),
    .o_impl     (dft_test_23_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[23])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[22]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_22_oup;
  logic dft_test_22_oup_en;
  logic dft_test_22_inp;
  logic dft_test_22_inp_en;
  logic dft_test_22_pull_type;
  logic dft_test_22_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_22_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_22_impl_oup; // Stubbed
  always_comb dft_test_22_oup       = i_dft_test[22];
  always_comb dft_test_22_oup_en    = i_dft_test_oe[22];
  always_comb o_dft_test[22] = dft_test_22_inp;
  always_comb dft_test_22_inp_en    = (1'b1 ^ i_dft_test_oe[22]);
  always_comb dft_test_22_pull_type = i_dft_pull_type;
  always_comb dft_test_22_pull_en   = i_dft_pull_en;

  always_comb dft_test_22_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_22 (
    .i_oup      (dft_test_22_oup),
    .i_oup_en   (dft_test_22_oup_en),
    .o_inp      (dft_test_22_inp),
    .i_inp_en   (dft_test_22_inp_en),
    .i_pull_type(dft_test_22_pull_type),
    .i_pull_en  (dft_test_22_pull_en),
    .i_impl     (dft_test_22_impl_inp),
    .o_impl     (dft_test_22_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[22])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[21]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_21_oup;
  logic dft_test_21_oup_en;
  logic dft_test_21_inp;
  logic dft_test_21_inp_en;
  logic dft_test_21_pull_type;
  logic dft_test_21_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_21_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_21_impl_oup; // Stubbed
  always_comb dft_test_21_oup       = i_dft_test[21];
  always_comb dft_test_21_oup_en    = i_dft_test_oe[21];
  always_comb o_dft_test[21] = dft_test_21_inp;
  always_comb dft_test_21_inp_en    = (1'b1 ^ i_dft_test_oe[21]);
  always_comb dft_test_21_pull_type = i_dft_pull_type;
  always_comb dft_test_21_pull_en   = i_dft_pull_en;

  always_comb dft_test_21_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_21 (
    .i_oup      (dft_test_21_oup),
    .i_oup_en   (dft_test_21_oup_en),
    .o_inp      (dft_test_21_inp),
    .i_inp_en   (dft_test_21_inp_en),
    .i_pull_type(dft_test_21_pull_type),
    .i_pull_en  (dft_test_21_pull_en),
    .i_impl     (dft_test_21_impl_inp),
    .o_impl     (dft_test_21_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[21])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[20]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_20_oup;
  logic dft_test_20_oup_en;
  logic dft_test_20_inp;
  logic dft_test_20_inp_en;
  logic dft_test_20_pull_type;
  logic dft_test_20_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_20_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_20_impl_oup; // Stubbed
  always_comb dft_test_20_oup       = i_dft_test[20];
  always_comb dft_test_20_oup_en    = i_dft_test_oe[20];
  always_comb o_dft_test[20] = dft_test_20_inp;
  always_comb dft_test_20_inp_en    = (1'b1 ^ i_dft_test_oe[20]);
  always_comb dft_test_20_pull_type = i_dft_pull_type;
  always_comb dft_test_20_pull_en   = i_dft_pull_en;

  always_comb dft_test_20_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_20 (
    .i_oup      (dft_test_20_oup),
    .i_oup_en   (dft_test_20_oup_en),
    .o_inp      (dft_test_20_inp),
    .i_inp_en   (dft_test_20_inp_en),
    .i_pull_type(dft_test_20_pull_type),
    .i_pull_en  (dft_test_20_pull_en),
    .i_impl     (dft_test_20_impl_inp),
    .o_impl     (dft_test_20_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[20])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[19]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_19_oup;
  logic dft_test_19_oup_en;
  logic dft_test_19_inp;
  logic dft_test_19_inp_en;
  logic dft_test_19_pull_type;
  logic dft_test_19_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_19_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_19_impl_oup; // Stubbed
  always_comb dft_test_19_oup       = i_dft_test[19];
  always_comb dft_test_19_oup_en    = i_dft_test_oe[19];
  always_comb o_dft_test[19] = dft_test_19_inp;
  always_comb dft_test_19_inp_en    = (1'b1 ^ i_dft_test_oe[19]);
  always_comb dft_test_19_pull_type = i_dft_pull_type;
  always_comb dft_test_19_pull_en   = i_dft_pull_en;

  always_comb dft_test_19_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_19 (
    .i_oup      (dft_test_19_oup),
    .i_oup_en   (dft_test_19_oup_en),
    .o_inp      (dft_test_19_inp),
    .i_inp_en   (dft_test_19_inp_en),
    .i_pull_type(dft_test_19_pull_type),
    .i_pull_en  (dft_test_19_pull_en),
    .i_impl     (dft_test_19_impl_inp),
    .o_impl     (dft_test_19_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[19])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[18]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_18_oup;
  logic dft_test_18_oup_en;
  logic dft_test_18_inp;
  logic dft_test_18_inp_en;
  logic dft_test_18_pull_type;
  logic dft_test_18_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_18_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_18_impl_oup; // Stubbed
  always_comb dft_test_18_oup       = i_dft_test[18];
  always_comb dft_test_18_oup_en    = i_dft_test_oe[18];
  always_comb o_dft_test[18] = dft_test_18_inp;
  always_comb dft_test_18_inp_en    = (1'b1 ^ i_dft_test_oe[18]);
  always_comb dft_test_18_pull_type = i_dft_pull_type;
  always_comb dft_test_18_pull_en   = i_dft_pull_en;

  always_comb dft_test_18_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_18 (
    .i_oup      (dft_test_18_oup),
    .i_oup_en   (dft_test_18_oup_en),
    .o_inp      (dft_test_18_inp),
    .i_inp_en   (dft_test_18_inp_en),
    .i_pull_type(dft_test_18_pull_type),
    .i_pull_en  (dft_test_18_pull_en),
    .i_impl     (dft_test_18_impl_inp),
    .o_impl     (dft_test_18_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[18])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[17]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_17_oup;
  logic dft_test_17_oup_en;
  logic dft_test_17_inp;
  logic dft_test_17_inp_en;
  logic dft_test_17_pull_type;
  logic dft_test_17_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_17_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_17_impl_oup; // Stubbed
  always_comb dft_test_17_oup       = i_dft_test[17];
  always_comb dft_test_17_oup_en    = i_dft_test_oe[17];
  always_comb o_dft_test[17] = dft_test_17_inp;
  always_comb dft_test_17_inp_en    = (1'b1 ^ i_dft_test_oe[17]);
  always_comb dft_test_17_pull_type = i_dft_pull_type;
  always_comb dft_test_17_pull_en   = i_dft_pull_en;

  always_comb dft_test_17_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_17 (
    .i_oup      (dft_test_17_oup),
    .i_oup_en   (dft_test_17_oup_en),
    .o_inp      (dft_test_17_inp),
    .i_inp_en   (dft_test_17_inp_en),
    .i_pull_type(dft_test_17_pull_type),
    .i_pull_en  (dft_test_17_pull_en),
    .i_impl     (dft_test_17_impl_inp),
    .o_impl     (dft_test_17_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[17])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[16]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_16_oup;
  logic dft_test_16_oup_en;
  logic dft_test_16_inp;
  logic dft_test_16_inp_en;
  logic dft_test_16_pull_type;
  logic dft_test_16_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_16_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_16_impl_oup; // Stubbed
  always_comb dft_test_16_oup       = i_dft_test[16];
  always_comb dft_test_16_oup_en    = i_dft_test_oe[16];
  always_comb o_dft_test[16] = dft_test_16_inp;
  always_comb dft_test_16_inp_en    = (1'b1 ^ i_dft_test_oe[16]);
  always_comb dft_test_16_pull_type = i_dft_pull_type;
  always_comb dft_test_16_pull_en   = i_dft_pull_en;

  always_comb dft_test_16_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_16 (
    .i_oup      (dft_test_16_oup),
    .i_oup_en   (dft_test_16_oup_en),
    .o_inp      (dft_test_16_inp),
    .i_inp_en   (dft_test_16_inp_en),
    .i_pull_type(dft_test_16_pull_type),
    .i_pull_en  (dft_test_16_pull_en),
    .i_impl     (dft_test_16_impl_inp),
    .o_impl     (dft_test_16_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[16])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[15]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_15_oup;
  logic dft_test_15_oup_en;
  logic dft_test_15_inp;
  logic dft_test_15_inp_en;
  logic dft_test_15_pull_type;
  logic dft_test_15_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_15_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_15_impl_oup; // Stubbed
  always_comb dft_test_15_oup       = i_dft_test[15];
  always_comb dft_test_15_oup_en    = i_dft_test_oe[15];
  always_comb o_dft_test[15] = dft_test_15_inp;
  always_comb dft_test_15_inp_en    = (1'b1 ^ i_dft_test_oe[15]);
  always_comb dft_test_15_pull_type = i_dft_pull_type;
  always_comb dft_test_15_pull_en   = i_dft_pull_en;

  always_comb dft_test_15_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_15 (
    .i_oup      (dft_test_15_oup),
    .i_oup_en   (dft_test_15_oup_en),
    .o_inp      (dft_test_15_inp),
    .i_inp_en   (dft_test_15_inp_en),
    .i_pull_type(dft_test_15_pull_type),
    .i_pull_en  (dft_test_15_pull_en),
    .i_impl     (dft_test_15_impl_inp),
    .o_impl     (dft_test_15_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[15])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[14]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_14_oup;
  logic dft_test_14_oup_en;
  logic dft_test_14_inp;
  logic dft_test_14_inp_en;
  logic dft_test_14_pull_type;
  logic dft_test_14_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_14_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_14_impl_oup; // Stubbed
  always_comb dft_test_14_oup       = i_dft_test[14];
  always_comb dft_test_14_oup_en    = i_dft_test_oe[14];
  always_comb o_dft_test[14] = dft_test_14_inp;
  always_comb dft_test_14_inp_en    = (1'b1 ^ i_dft_test_oe[14]);
  always_comb dft_test_14_pull_type = i_dft_pull_type;
  always_comb dft_test_14_pull_en   = i_dft_pull_en;

  always_comb dft_test_14_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_14 (
    .i_oup      (dft_test_14_oup),
    .i_oup_en   (dft_test_14_oup_en),
    .o_inp      (dft_test_14_inp),
    .i_inp_en   (dft_test_14_inp_en),
    .i_pull_type(dft_test_14_pull_type),
    .i_pull_en  (dft_test_14_pull_en),
    .i_impl     (dft_test_14_impl_inp),
    .o_impl     (dft_test_14_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[14])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[13]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_13_oup;
  logic dft_test_13_oup_en;
  logic dft_test_13_inp;
  logic dft_test_13_inp_en;
  logic dft_test_13_pull_type;
  logic dft_test_13_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_13_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_13_impl_oup; // Stubbed
  always_comb dft_test_13_oup       = i_dft_test[13];
  always_comb dft_test_13_oup_en    = i_dft_test_oe[13];
  always_comb o_dft_test[13] = dft_test_13_inp;
  always_comb dft_test_13_inp_en    = (1'b1 ^ i_dft_test_oe[13]);
  always_comb dft_test_13_pull_type = i_dft_pull_type;
  always_comb dft_test_13_pull_en   = i_dft_pull_en;

  always_comb dft_test_13_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_13 (
    .i_oup      (dft_test_13_oup),
    .i_oup_en   (dft_test_13_oup_en),
    .o_inp      (dft_test_13_inp),
    .i_inp_en   (dft_test_13_inp_en),
    .i_pull_type(dft_test_13_pull_type),
    .i_pull_en  (dft_test_13_pull_en),
    .i_impl     (dft_test_13_impl_inp),
    .o_impl     (dft_test_13_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[13])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[12]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_12_oup;
  logic dft_test_12_oup_en;
  logic dft_test_12_inp;
  logic dft_test_12_inp_en;
  logic dft_test_12_pull_type;
  logic dft_test_12_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_12_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_12_impl_oup; // Stubbed
  always_comb dft_test_12_oup       = i_dft_test[12];
  always_comb dft_test_12_oup_en    = i_dft_test_oe[12];
  always_comb o_dft_test[12] = dft_test_12_inp;
  always_comb dft_test_12_inp_en    = (1'b1 ^ i_dft_test_oe[12]);
  always_comb dft_test_12_pull_type = i_dft_pull_type;
  always_comb dft_test_12_pull_en   = i_dft_pull_en;

  always_comb dft_test_12_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_12 (
    .i_oup      (dft_test_12_oup),
    .i_oup_en   (dft_test_12_oup_en),
    .o_inp      (dft_test_12_inp),
    .i_inp_en   (dft_test_12_inp_en),
    .i_pull_type(dft_test_12_pull_type),
    .i_pull_en  (dft_test_12_pull_en),
    .i_impl     (dft_test_12_impl_inp),
    .o_impl     (dft_test_12_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[12])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[11]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_11_oup;
  logic dft_test_11_oup_en;
  logic dft_test_11_inp;
  logic dft_test_11_inp_en;
  logic dft_test_11_pull_type;
  logic dft_test_11_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_11_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_11_impl_oup; // Stubbed
  always_comb dft_test_11_oup       = i_dft_test[11];
  always_comb dft_test_11_oup_en    = i_dft_test_oe[11];
  always_comb o_dft_test[11] = dft_test_11_inp;
  always_comb dft_test_11_inp_en    = (1'b1 ^ i_dft_test_oe[11]);
  always_comb dft_test_11_pull_type = i_dft_pull_type;
  always_comb dft_test_11_pull_en   = i_dft_pull_en;

  always_comb dft_test_11_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_11 (
    .i_oup      (dft_test_11_oup),
    .i_oup_en   (dft_test_11_oup_en),
    .o_inp      (dft_test_11_inp),
    .i_inp_en   (dft_test_11_inp_en),
    .i_pull_type(dft_test_11_pull_type),
    .i_pull_en  (dft_test_11_pull_en),
    .i_impl     (dft_test_11_impl_inp),
    .o_impl     (dft_test_11_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[11])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[10]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_10_oup;
  logic dft_test_10_oup_en;
  logic dft_test_10_inp;
  logic dft_test_10_inp_en;
  logic dft_test_10_pull_type;
  logic dft_test_10_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_10_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_10_impl_oup; // Stubbed
  always_comb dft_test_10_oup       = i_dft_test[10];
  always_comb dft_test_10_oup_en    = i_dft_test_oe[10];
  always_comb o_dft_test[10] = dft_test_10_inp;
  always_comb dft_test_10_inp_en    = (1'b1 ^ i_dft_test_oe[10]);
  always_comb dft_test_10_pull_type = i_dft_pull_type;
  always_comb dft_test_10_pull_en   = i_dft_pull_en;

  always_comb dft_test_10_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_10 (
    .i_oup      (dft_test_10_oup),
    .i_oup_en   (dft_test_10_oup_en),
    .o_inp      (dft_test_10_inp),
    .i_inp_en   (dft_test_10_inp_en),
    .i_pull_type(dft_test_10_pull_type),
    .i_pull_en  (dft_test_10_pull_en),
    .i_impl     (dft_test_10_impl_inp),
    .o_impl     (dft_test_10_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[10])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[9]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_9_oup;
  logic dft_test_9_oup_en;
  logic dft_test_9_inp;
  logic dft_test_9_inp_en;
  logic dft_test_9_pull_type;
  logic dft_test_9_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_9_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_9_impl_oup; // Stubbed
  always_comb dft_test_9_oup       = i_dft_test[9];
  always_comb dft_test_9_oup_en    = i_dft_test_oe[9];
  always_comb o_dft_test[9] = dft_test_9_inp;
  always_comb dft_test_9_inp_en    = (1'b1 ^ i_dft_test_oe[9]);
  always_comb dft_test_9_pull_type = i_dft_pull_type;
  always_comb dft_test_9_pull_en   = i_dft_pull_en;

  always_comb dft_test_9_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_9 (
    .i_oup      (dft_test_9_oup),
    .i_oup_en   (dft_test_9_oup_en),
    .o_inp      (dft_test_9_inp),
    .i_inp_en   (dft_test_9_inp_en),
    .i_pull_type(dft_test_9_pull_type),
    .i_pull_en  (dft_test_9_pull_en),
    .i_impl     (dft_test_9_impl_inp),
    .o_impl     (dft_test_9_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[9])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[8]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_8_oup;
  logic dft_test_8_oup_en;
  logic dft_test_8_inp;
  logic dft_test_8_inp_en;
  logic dft_test_8_pull_type;
  logic dft_test_8_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_8_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_8_impl_oup; // Stubbed
  always_comb dft_test_8_oup       = i_dft_test[8];
  always_comb dft_test_8_oup_en    = i_dft_test_oe[8];
  always_comb o_dft_test[8] = dft_test_8_inp;
  always_comb dft_test_8_inp_en    = (1'b1 ^ i_dft_test_oe[8]);
  always_comb dft_test_8_pull_type = i_dft_pull_type;
  always_comb dft_test_8_pull_en   = i_dft_pull_en;

  always_comb dft_test_8_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_8 (
    .i_oup      (dft_test_8_oup),
    .i_oup_en   (dft_test_8_oup_en),
    .o_inp      (dft_test_8_inp),
    .i_inp_en   (dft_test_8_inp_en),
    .i_pull_type(dft_test_8_pull_type),
    .i_pull_en  (dft_test_8_pull_en),
    .i_impl     (dft_test_8_impl_inp),
    .o_impl     (dft_test_8_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[8])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[7]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_7_oup;
  logic dft_test_7_oup_en;
  logic dft_test_7_inp;
  logic dft_test_7_inp_en;
  logic dft_test_7_pull_type;
  logic dft_test_7_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_7_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_7_impl_oup; // Stubbed
  always_comb dft_test_7_oup       = i_dft_test[7];
  always_comb dft_test_7_oup_en    = i_dft_test_oe[7];
  always_comb o_dft_test[7] = dft_test_7_inp;
  always_comb dft_test_7_inp_en    = (1'b1 ^ i_dft_test_oe[7]);
  always_comb dft_test_7_pull_type = i_dft_pull_type;
  always_comb dft_test_7_pull_en   = i_dft_pull_en;

  always_comb dft_test_7_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_7 (
    .i_oup      (dft_test_7_oup),
    .i_oup_en   (dft_test_7_oup_en),
    .o_inp      (dft_test_7_inp),
    .i_inp_en   (dft_test_7_inp_en),
    .i_pull_type(dft_test_7_pull_type),
    .i_pull_en  (dft_test_7_pull_en),
    .i_impl     (dft_test_7_impl_inp),
    .o_impl     (dft_test_7_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[7])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[6]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_6_oup;
  logic dft_test_6_oup_en;
  logic dft_test_6_inp;
  logic dft_test_6_inp_en;
  logic dft_test_6_pull_type;
  logic dft_test_6_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_6_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_6_impl_oup; // Stubbed
  always_comb dft_test_6_oup       = i_dft_test[6];
  always_comb dft_test_6_oup_en    = i_dft_test_oe[6];
  always_comb o_dft_test[6] = dft_test_6_inp;
  always_comb dft_test_6_inp_en    = (1'b1 ^ i_dft_test_oe[6]);
  always_comb dft_test_6_pull_type = i_dft_pull_type;
  always_comb dft_test_6_pull_en   = i_dft_pull_en;

  always_comb dft_test_6_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_6 (
    .i_oup      (dft_test_6_oup),
    .i_oup_en   (dft_test_6_oup_en),
    .o_inp      (dft_test_6_inp),
    .i_inp_en   (dft_test_6_inp_en),
    .i_pull_type(dft_test_6_pull_type),
    .i_pull_en  (dft_test_6_pull_en),
    .i_impl     (dft_test_6_impl_inp),
    .o_impl     (dft_test_6_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[6])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[5]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_5_oup;
  logic dft_test_5_oup_en;
  logic dft_test_5_inp;
  logic dft_test_5_inp_en;
  logic dft_test_5_pull_type;
  logic dft_test_5_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_5_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_5_impl_oup; // Stubbed
  always_comb dft_test_5_oup       = i_dft_test[5];
  always_comb dft_test_5_oup_en    = i_dft_test_oe[5];
  always_comb o_dft_test[5] = dft_test_5_inp;
  always_comb dft_test_5_inp_en    = (1'b1 ^ i_dft_test_oe[5]);
  always_comb dft_test_5_pull_type = i_dft_pull_type;
  always_comb dft_test_5_pull_en   = i_dft_pull_en;

  always_comb dft_test_5_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_5 (
    .i_oup      (dft_test_5_oup),
    .i_oup_en   (dft_test_5_oup_en),
    .o_inp      (dft_test_5_inp),
    .i_inp_en   (dft_test_5_inp_en),
    .i_pull_type(dft_test_5_pull_type),
    .i_pull_en  (dft_test_5_pull_en),
    .i_impl     (dft_test_5_impl_inp),
    .o_impl     (dft_test_5_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[5])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[4]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_4_oup;
  logic dft_test_4_oup_en;
  logic dft_test_4_inp;
  logic dft_test_4_inp_en;
  logic dft_test_4_pull_type;
  logic dft_test_4_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_4_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_4_impl_oup; // Stubbed
  always_comb dft_test_4_oup       = i_dft_test[4];
  always_comb dft_test_4_oup_en    = i_dft_test_oe[4];
  always_comb o_dft_test[4] = dft_test_4_inp;
  always_comb dft_test_4_inp_en    = (1'b1 ^ i_dft_test_oe[4]);
  always_comb dft_test_4_pull_type = i_dft_pull_type;
  always_comb dft_test_4_pull_en   = i_dft_pull_en;

  always_comb dft_test_4_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_4 (
    .i_oup      (dft_test_4_oup),
    .i_oup_en   (dft_test_4_oup_en),
    .o_inp      (dft_test_4_inp),
    .i_inp_en   (dft_test_4_inp_en),
    .i_pull_type(dft_test_4_pull_type),
    .i_pull_en  (dft_test_4_pull_en),
    .i_impl     (dft_test_4_impl_inp),
    .o_impl     (dft_test_4_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[4])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[3]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_3_oup;
  logic dft_test_3_oup_en;
  logic dft_test_3_inp;
  logic dft_test_3_inp_en;
  logic dft_test_3_pull_type;
  logic dft_test_3_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_3_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_3_impl_oup; // Stubbed
  always_comb dft_test_3_oup       = i_dft_test[3];
  always_comb dft_test_3_oup_en    = i_dft_test_oe[3];
  always_comb o_dft_test[3] = dft_test_3_inp;
  always_comb dft_test_3_inp_en    = (1'b1 ^ i_dft_test_oe[3]);
  always_comb dft_test_3_pull_type = i_dft_pull_type;
  always_comb dft_test_3_pull_en   = i_dft_pull_en;

  always_comb dft_test_3_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_3 (
    .i_oup      (dft_test_3_oup),
    .i_oup_en   (dft_test_3_oup_en),
    .o_inp      (dft_test_3_inp),
    .i_inp_en   (dft_test_3_inp_en),
    .i_pull_type(dft_test_3_pull_type),
    .i_pull_en  (dft_test_3_pull_en),
    .i_impl     (dft_test_3_impl_inp),
    .o_impl     (dft_test_3_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[3])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[2]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_2_oup;
  logic dft_test_2_oup_en;
  logic dft_test_2_inp;
  logic dft_test_2_inp_en;
  logic dft_test_2_pull_type;
  logic dft_test_2_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_2_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_2_impl_oup; // Stubbed
  always_comb dft_test_2_oup       = i_dft_test[2];
  always_comb dft_test_2_oup_en    = i_dft_test_oe[2];
  always_comb o_dft_test[2] = dft_test_2_inp;
  always_comb dft_test_2_inp_en    = (1'b1 ^ i_dft_test_oe[2]);
  always_comb dft_test_2_pull_type = i_dft_pull_type;
  always_comb dft_test_2_pull_en   = i_dft_pull_en;

  always_comb dft_test_2_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_2 (
    .i_oup      (dft_test_2_oup),
    .i_oup_en   (dft_test_2_oup_en),
    .o_inp      (dft_test_2_inp),
    .i_inp_en   (dft_test_2_inp_en),
    .i_pull_type(dft_test_2_pull_type),
    .i_pull_en  (dft_test_2_pull_en),
    .i_impl     (dft_test_2_impl_inp),
    .o_impl     (dft_test_2_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[2])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[1]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_1_oup;
  logic dft_test_1_oup_en;
  logic dft_test_1_inp;
  logic dft_test_1_inp_en;
  logic dft_test_1_pull_type;
  logic dft_test_1_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_1_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_1_impl_oup; // Stubbed
  always_comb dft_test_1_oup       = i_dft_test[1];
  always_comb dft_test_1_oup_en    = i_dft_test_oe[1];
  always_comb o_dft_test[1] = dft_test_1_inp;
  always_comb dft_test_1_inp_en    = (1'b1 ^ i_dft_test_oe[1]);
  always_comb dft_test_1_pull_type = i_dft_pull_type;
  always_comb dft_test_1_pull_en   = i_dft_pull_en;

  always_comb dft_test_1_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_1 (
    .i_oup      (dft_test_1_oup),
    .i_oup_en   (dft_test_1_oup_en),
    .o_inp      (dft_test_1_inp),
    .i_inp_en   (dft_test_1_inp_en),
    .i_pull_type(dft_test_1_pull_type),
    .i_pull_en  (dft_test_1_pull_en),
    .i_impl     (dft_test_1_impl_inp),
    .o_impl     (dft_test_1_impl_oup),
    .i_impl_pwr (impl_power[1]),
    .io_pad     (io_pad_dft_test[1])
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Inout Pad instantiation for dft_test[0]
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic dft_test_0_oup;
  logic dft_test_0_oup_en;
  logic dft_test_0_inp;
  logic dft_test_0_inp_en;
  logic dft_test_0_pull_type;
  logic dft_test_0_pull_en;

  axe_tcl_pad_pkg::impl_pad_slow_inp_t       dft_test_0_impl_inp;
  axe_tcl_pad_pkg::impl_pad_slow_oup_t       dft_test_0_impl_oup; // Stubbed
  always_comb dft_test_0_oup       = i_dft_test[0];
  always_comb dft_test_0_oup_en    = i_dft_test_oe[0];
  always_comb o_dft_test[0] = dft_test_0_inp;
  always_comb dft_test_0_inp_en    = (1'b1 ^ i_dft_test_oe[0]);
  always_comb dft_test_0_pull_type = i_dft_pull_type;
  always_comb dft_test_0_pull_en   = i_dft_pull_en;

  always_comb dft_test_0_impl_inp = '{
    is:  i_dft_schmitt,
    ds:  i_dft_drive,
    poe: 1'b0
  };

  axe_tcl_pad_inout #(
    .ImplementationKey("slow_vertical"),
    .impl_inp_t       (axe_tcl_pad_pkg::impl_pad_slow_inp_t),
    .impl_oup_t       (axe_tcl_pad_pkg::impl_pad_slow_oup_t),
    .impl_pwr_t       (axe_tcl_pad_pkg::impl_pwr_t)
  ) u_inout_dft_test_0 (
    .i_oup      (dft_test_0_oup),
    .i_oup_en   (dft_test_0_oup_en),
    .o_inp      (dft_test_0_inp),
    .i_inp_en   (dft_test_0_inp_en),
    .i_pull_type(dft_test_0_pull_type),
    .i_pull_en  (dft_test_0_pull_en),
    .i_impl     (dft_test_0_impl_inp),
    .o_impl     (dft_test_0_impl_oup),
    .i_impl_pwr (impl_power[0]),
    .io_pad     (io_pad_dft_test[0])
  );

endmodule
