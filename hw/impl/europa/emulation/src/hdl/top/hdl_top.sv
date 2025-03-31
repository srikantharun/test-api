module hdl_top;

  //-----------------------------------------------------------
  // bypass: IMC banks
  //-----------------------------------------------------------
  `define DEFPARAM_BYPASS_IMC_BANK_ON_AICORE(
      ai_core) \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[0].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[0].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[0].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[0].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[1].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[1].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[1].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[1].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[2].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[2].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[2].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[2].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[3].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[3].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[3].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[3].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[4].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[4].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[4].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[4].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[5].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[5].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[5].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[5].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[6].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[6].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[6].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[6].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[7].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[7].inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[7].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[0].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1; \
    defparam i_europa.u_aipu.u_ai_core_p_``ai_core``.u_ai_core.u_aic_mid_p.u_aic_mid.u_mvm.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[7].inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[1].u_mvm_imc_bank_wrapper.u_imc_bank.BYPASS = 1;

`ifdef BYPASS_IMC_BANK_AI_CORE_0
  `DEFPARAM_BYPASS_IMC_BANK_ON_AICORE(0)
`endif
`ifdef BYPASS_IMC_BANK_AI_CORE_1
  `DEFPARAM_BYPASS_IMC_BANK_ON_AICORE(1)
`endif
`ifdef BYPASS_IMC_BANK_AI_CORE_2
  `DEFPARAM_BYPASS_IMC_BANK_ON_AICORE(2)
`endif
`ifdef BYPASS_IMC_BANK_AI_CORE_3
  `DEFPARAM_BYPASS_IMC_BANK_ON_AICORE(3)
`endif
`ifdef BYPASS_IMC_BANK_AI_CORE_4
  `DEFPARAM_BYPASS_IMC_BANK_ON_AICORE(4)
`endif
`ifdef BYPASS_IMC_BANK_AI_CORE_5
  `DEFPARAM_BYPASS_IMC_BANK_ON_AICORE(5)
`endif
`ifdef BYPASS_IMC_BANK_AI_CORE_6
  `DEFPARAM_BYPASS_IMC_BANK_ON_AICORE(6)
`endif
`ifdef BYPASS_IMC_BANK_AI_CORE_7
  `DEFPARAM_BYPASS_IMC_BANK_ON_AICORE(7)
`endif

  //-----------------------------------------------------------
  // instantiate: Europa
  //-----------------------------------------------------------
  bit i_ref_clk;
  wire o_ref_clk;
  bit i_ref_clk_bypass;
  bit i_tck;
  logic o_spi_clk_out;
  wire io_i2c_0_clk;
  wire io_i2c_1_clk;
  logic o_sd_emmc_clk_out;
  bit i_por_rst_n;
  bit i_trst_n;
  bit i_uart_rx;
  logic o_uart_tx;
  bit i_uart_cts_n;
  logic o_uart_rts_n;
  logic [3:0] o_spi_ss_n;
  wire [3:0] io_spi_sd;
  wire io_i2c_0_data;
  wire io_i2c_1_data;
  wire [15:0] io_gpio;
  wire io_gpio_lpbk;
  wire io_sd_emmc_cmd;
  wire [7:0] io_sd_emmc_data;
  bit i_sd_emmc_strobe;
  logic o_emmc_reset;
  logic o_emmc_power;
  bit i_sd_emmc_detect;
  logic i_sd_emmc_wp;
  logic o_sd_emmc_pu_pd;
  logic i_emmc_lpbk_dqs;
  wire io_emmc_rebar;
  logic [15:0] o_observability;
  logic o_thermal_warning_n;
  logic o_thermal_shutdown_n;
  bit i_thermal_throttle;
  bit i_throttle;
  bit [2:0] i_boot_mode;
  bit i_tms;
  bit i_td_in;
  logic o_td_out;
  wire [44:0] io_dft_test;
  wire io_efuse_vqps;
  wire io_efuse_vddwl;
  wire io_pvt_test_out_ts;
  wire io_otp_vtdo;
  wire io_otp_vrefm;
  wire io_otp_vpp;
  wire o_lpddr_ppp_0_bp_memreset_l;
  wire o_lpddr_ppp_1_bp_memreset_l;
  wire o_lpddr_ppp_2_bp_memreset_l;
  wire o_lpddr_ppp_3_bp_memreset_l;
  wire [19:0] io_lpddr_ppp_0_bp_a;
  wire [19:0] io_lpddr_ppp_1_bp_a;
  wire [19:0] io_lpddr_ppp_2_bp_a;
  wire [19:0] io_lpddr_ppp_3_bp_a;
  wire io_lpddr_ppp_0_bp_ato;
  wire io_lpddr_ppp_1_bp_ato;
  wire io_lpddr_ppp_2_bp_ato;
  wire io_lpddr_ppp_3_bp_ato;
  wire io_lpddr_ppp_0_bp_ato_pll;
  wire io_lpddr_ppp_1_bp_ato_pll;
  wire io_lpddr_ppp_2_bp_ato_pll;
  wire io_lpddr_ppp_3_bp_ato_pll;
  wire [12:0] io_lpddr_ppp_0_bp_b0_d;
  wire [12:0] io_lpddr_ppp_1_bp_b0_d;
  wire [12:0] io_lpddr_ppp_2_bp_b0_d;
  wire [12:0] io_lpddr_ppp_3_bp_b0_d;
  wire [12:0] io_lpddr_ppp_0_bp_b1_d;
  wire [12:0] io_lpddr_ppp_1_bp_b1_d;
  wire [12:0] io_lpddr_ppp_2_bp_b1_d;
  wire [12:0] io_lpddr_ppp_3_bp_b1_d;
  wire [12:0] io_lpddr_ppp_0_bp_b2_d;
  wire [12:0] io_lpddr_ppp_1_bp_b2_d;
  wire [12:0] io_lpddr_ppp_2_bp_b2_d;
  wire [12:0] io_lpddr_ppp_3_bp_b2_d;
  wire [12:0] io_lpddr_ppp_0_bp_b3_d;
  wire [12:0] io_lpddr_ppp_1_bp_b3_d;
  wire [12:0] io_lpddr_ppp_2_bp_b3_d;
  wire [12:0] io_lpddr_ppp_3_bp_b3_d;
  wire io_lpddr_ppp_0_bp_ck0_c;
  wire io_lpddr_ppp_1_bp_ck0_c;
  wire io_lpddr_ppp_2_bp_ck0_c;
  wire io_lpddr_ppp_3_bp_ck0_c;
  wire io_lpddr_ppp_0_bp_ck0_t;
  wire io_lpddr_ppp_1_bp_ck0_t;
  wire io_lpddr_ppp_2_bp_ck0_t;
  wire io_lpddr_ppp_3_bp_ck0_t;
  wire io_lpddr_ppp_0_bp_ck1_c;
  wire io_lpddr_ppp_1_bp_ck1_c;
  wire io_lpddr_ppp_2_bp_ck1_c;
  wire io_lpddr_ppp_3_bp_ck1_c;
  wire io_lpddr_ppp_0_bp_ck1_t;
  wire io_lpddr_ppp_1_bp_ck1_t;
  wire io_lpddr_ppp_2_bp_ck1_t;
  wire io_lpddr_ppp_3_bp_ck1_t;
  wire io_lpddr_ppp_0_bp_zn;
  wire io_lpddr_ppp_1_bp_zn;
  wire io_lpddr_ppp_2_bp_zn;
  wire io_lpddr_ppp_3_bp_zn;
  wire o_lpddr_graph_0_bp_memreset_l;
  wire o_lpddr_graph_1_bp_memreset_l;
  wire o_lpddr_graph_2_bp_memreset_l;
  wire o_lpddr_graph_3_bp_memreset_l;
  wire [19:0] io_lpddr_graph_0_bp_a;
  wire [19:0] io_lpddr_graph_1_bp_a;
  wire [19:0] io_lpddr_graph_2_bp_a;
  wire [19:0] io_lpddr_graph_3_bp_a;
  wire io_lpddr_graph_0_bp_ato;
  wire io_lpddr_graph_1_bp_ato;
  wire io_lpddr_graph_2_bp_ato;
  wire io_lpddr_graph_3_bp_ato;
  wire io_lpddr_graph_0_bp_ato_pll;
  wire io_lpddr_graph_1_bp_ato_pll;
  wire io_lpddr_graph_2_bp_ato_pll;
  wire io_lpddr_graph_3_bp_ato_pll;
  wire [12:0] io_lpddr_graph_0_bp_b0_d;
  wire [12:0] io_lpddr_graph_1_bp_b0_d;
  wire [12:0] io_lpddr_graph_2_bp_b0_d;
  wire [12:0] io_lpddr_graph_3_bp_b0_d;
  wire [12:0] io_lpddr_graph_0_bp_b1_d;
  wire [12:0] io_lpddr_graph_1_bp_b1_d;
  wire [12:0] io_lpddr_graph_2_bp_b1_d;
  wire [12:0] io_lpddr_graph_3_bp_b1_d;
  wire [12:0] io_lpddr_graph_0_bp_b2_d;
  wire [12:0] io_lpddr_graph_1_bp_b2_d;
  wire [12:0] io_lpddr_graph_2_bp_b2_d;
  wire [12:0] io_lpddr_graph_3_bp_b2_d;
  wire [12:0] io_lpddr_graph_0_bp_b3_d;
  wire [12:0] io_lpddr_graph_1_bp_b3_d;
  wire [12:0] io_lpddr_graph_2_bp_b3_d;
  wire [12:0] io_lpddr_graph_3_bp_b3_d;
  wire io_lpddr_graph_0_bp_ck0_c;
  wire io_lpddr_graph_1_bp_ck0_c;
  wire io_lpddr_graph_2_bp_ck0_c;
  wire io_lpddr_graph_3_bp_ck0_c;
  wire io_lpddr_graph_0_bp_ck0_t;
  wire io_lpddr_graph_1_bp_ck0_t;
  wire io_lpddr_graph_2_bp_ck0_t;
  wire io_lpddr_graph_3_bp_ck0_t;
  wire io_lpddr_graph_0_bp_ck1_c;
  wire io_lpddr_graph_1_bp_ck1_c;
  wire io_lpddr_graph_2_bp_ck1_c;
  wire io_lpddr_graph_3_bp_ck1_c;
  wire io_lpddr_graph_0_bp_ck1_t;
  wire io_lpddr_graph_1_bp_ck1_t;
  wire io_lpddr_graph_2_bp_ck1_t;
  wire io_lpddr_graph_3_bp_ck1_t;
  wire io_lpddr_graph_0_bp_zn;
  wire io_lpddr_graph_1_bp_zn;
  wire io_lpddr_graph_2_bp_zn;
  wire io_lpddr_graph_3_bp_zn;
  wire io_pcie_resref;
  bit i_ref_pad_clk_p;
  bit i_ref_pad_clk_m;
  bit i_pcie_perst_n;
  bit i_pcie_rxm_00;
  bit i_pcie_rxm_01;
  bit i_pcie_rxm_02;
  bit i_pcie_rxm_03;
  bit i_pcie_rxp_00;
  bit i_pcie_rxp_01;
  bit i_pcie_rxp_02;
  bit i_pcie_rxp_03;
  logic o_pcie_txm_00;
  logic o_pcie_txm_01;
  logic o_pcie_txm_02;
  logic o_pcie_txm_03;
  logic o_pcie_txp_00;
  logic o_pcie_txp_01;
  logic o_pcie_txp_02;
  logic o_pcie_txp_03;

  // Reset signal for spi softmodel
  bit i_spi_rst_n;

  europa i_europa (
      .i_ref_clk                    (i_ref_clk),
      .o_ref_clk                    (o_ref_clk),
      .i_ref_clk_bypass             (i_ref_clk_bypass),
      .i_tck                        (i_tck),
      .o_spi_clk_out                (o_spi_clk_out),
      .io_i2c_0_clk                 (io_i2c_0_clk),
      .io_i2c_1_clk                 (io_i2c_1_clk),
      .o_sd_emmc_clk_out            (o_sd_emmc_clk_out),
      .i_por_rst_n                  (i_por_rst_n),
      .i_trst_n                     (i_trst_n),
      .i_uart_rx                    (i_uart_rx),
      .o_uart_tx                    (o_uart_tx),
      .i_uart_cts_n                 (i_uart_cts_n),
      .o_uart_rts_n                 (o_uart_rts_n),
      .o_spi_ss_n                   (o_spi_ss_n),
      .io_spi_sd                    (io_spi_sd),
      .io_i2c_0_data                (io_i2c_0_data),
      .io_i2c_1_data                (io_i2c_1_data),
      .io_gpio                      ({io_gpio[15:2], io_gpio_lpbk, io_gpio_lpbk}),
      .io_sd_emmc_cmd               (io_sd_emmc_cmd),
      .io_sd_emmc_data              (io_sd_emmc_data),
      .i_sd_emmc_strobe             (i_sd_emmc_strobe),
      .o_emmc_reset                 (o_emmc_reset),
      .o_emmc_power                 (o_emmc_power),
      .i_emmc_lpbk_dqs              (i_emmc_lpbk_dqs),
      .io_emmc_rebar                (io_emmc_rebar),
      .i_sd_emmc_detect             (i_sd_emmc_detect),
      .i_sd_emmc_wp                 (i_sd_emmc_wp),
      .o_sd_emmc_pu_pd              (o_sd_emmc_pu_pd),
      .o_observability              (o_observability),
      .o_thermal_warning_n          (o_thermal_warning),
      .o_thermal_shutdown_n         (o_thermal_shutdown),
      .i_thermal_throttle           (i_thermal_throttle),
      .i_throttle                   (i_throttle),
      .i_boot_mode                  (i_boot_mode),
      .i_tms                        (i_tms),
      .i_td_in                      (i_td_in),
      .o_td_out                     (o_td_out),
      .io_dft_test                  (io_dft_test),
      .io_efuse_vqps                (io_efuse_vqps),
      .io_efuse_vddwl               (io_efuse_vddwl),
      .io_pvt_test_out_ts           (io_pvt_test_out_ts),
      .io_otp_vtdo                  (io_otp_vtdo),
      .io_otp_vrefm                 (io_otp_vrefm),
      .io_otp_vpp                   (io_otp_vpp),
      .o_lpddr_ppp_0_bp_memreset_l  (o_lpddr_ppp_0_bp_memreset_l),
      .o_lpddr_ppp_1_bp_memreset_l  (o_lpddr_ppp_1_bp_memreset_l),
      .o_lpddr_ppp_2_bp_memreset_l  (o_lpddr_ppp_2_bp_memreset_l),
      .o_lpddr_ppp_3_bp_memreset_l  (o_lpddr_ppp_3_bp_memreset_l),
      .io_lpddr_ppp_0_bp_a          (io_lpddr_ppp_0_bp_a),
      .io_lpddr_ppp_1_bp_a          (io_lpddr_ppp_1_bp_a),
      .io_lpddr_ppp_2_bp_a          (io_lpddr_ppp_2_bp_a),
      .io_lpddr_ppp_3_bp_a          (io_lpddr_ppp_3_bp_a),
      .io_lpddr_ppp_0_bp_ato        (io_lpddr_ppp_0_bp_ato),
      .io_lpddr_ppp_1_bp_ato        (io_lpddr_ppp_1_bp_ato),
      .io_lpddr_ppp_2_bp_ato        (io_lpddr_ppp_2_bp_ato),
      .io_lpddr_ppp_3_bp_ato        (io_lpddr_ppp_3_bp_ato),
      .io_lpddr_ppp_0_bp_ato_pll    (io_lpddr_ppp_0_bp_ato_pll),
      .io_lpddr_ppp_1_bp_ato_pll    (io_lpddr_ppp_1_bp_ato_pll),
      .io_lpddr_ppp_2_bp_ato_pll    (io_lpddr_ppp_2_bp_ato_pll),
      .io_lpddr_ppp_3_bp_ato_pll    (io_lpddr_ppp_3_bp_ato_pll),
      .io_lpddr_ppp_0_bp_b0_d       (io_lpddr_ppp_0_bp_b0_d),
      .io_lpddr_ppp_1_bp_b0_d       (io_lpddr_ppp_1_bp_b0_d),
      .io_lpddr_ppp_2_bp_b0_d       (io_lpddr_ppp_2_bp_b0_d),
      .io_lpddr_ppp_3_bp_b0_d       (io_lpddr_ppp_3_bp_b0_d),
      .io_lpddr_ppp_0_bp_b1_d       (io_lpddr_ppp_0_bp_b1_d),
      .io_lpddr_ppp_1_bp_b1_d       (io_lpddr_ppp_1_bp_b1_d),
      .io_lpddr_ppp_2_bp_b1_d       (io_lpddr_ppp_2_bp_b1_d),
      .io_lpddr_ppp_3_bp_b1_d       (io_lpddr_ppp_3_bp_b1_d),
      .io_lpddr_ppp_0_bp_b2_d       (io_lpddr_ppp_0_bp_b2_d),
      .io_lpddr_ppp_1_bp_b2_d       (io_lpddr_ppp_1_bp_b2_d),
      .io_lpddr_ppp_2_bp_b2_d       (io_lpddr_ppp_2_bp_b2_d),
      .io_lpddr_ppp_3_bp_b2_d       (io_lpddr_ppp_3_bp_b2_d),
      .io_lpddr_ppp_0_bp_b3_d       (io_lpddr_ppp_0_bp_b3_d),
      .io_lpddr_ppp_1_bp_b3_d       (io_lpddr_ppp_1_bp_b3_d),
      .io_lpddr_ppp_2_bp_b3_d       (io_lpddr_ppp_2_bp_b3_d),
      .io_lpddr_ppp_3_bp_b3_d       (io_lpddr_ppp_3_bp_b3_d),
      .io_lpddr_ppp_0_bp_ck0_c      (io_lpddr_ppp_0_bp_ck0_c),
      .io_lpddr_ppp_1_bp_ck0_c      (io_lpddr_ppp_1_bp_ck0_c),
      .io_lpddr_ppp_2_bp_ck0_c      (io_lpddr_ppp_2_bp_ck0_c),
      .io_lpddr_ppp_3_bp_ck0_c      (io_lpddr_ppp_3_bp_ck0_c),
      .io_lpddr_ppp_0_bp_ck0_t      (io_lpddr_ppp_0_bp_ck0_t),
      .io_lpddr_ppp_1_bp_ck0_t      (io_lpddr_ppp_1_bp_ck0_t),
      .io_lpddr_ppp_2_bp_ck0_t      (io_lpddr_ppp_2_bp_ck0_t),
      .io_lpddr_ppp_3_bp_ck0_t      (io_lpddr_ppp_3_bp_ck0_t),
      .io_lpddr_ppp_0_bp_ck1_c      (io_lpddr_ppp_0_bp_ck1_c),
      .io_lpddr_ppp_1_bp_ck1_c      (io_lpddr_ppp_1_bp_ck1_c),
      .io_lpddr_ppp_2_bp_ck1_c      (io_lpddr_ppp_2_bp_ck1_c),
      .io_lpddr_ppp_3_bp_ck1_c      (io_lpddr_ppp_3_bp_ck1_c),
      .io_lpddr_ppp_0_bp_ck1_t      (io_lpddr_ppp_0_bp_ck1_t),
      .io_lpddr_ppp_1_bp_ck1_t      (io_lpddr_ppp_1_bp_ck1_t),
      .io_lpddr_ppp_2_bp_ck1_t      (io_lpddr_ppp_2_bp_ck1_t),
      .io_lpddr_ppp_3_bp_ck1_t      (io_lpddr_ppp_3_bp_ck1_t),
      .io_lpddr_ppp_0_bp_zn         (io_lpddr_ppp_0_bp_zn),
      .io_lpddr_ppp_1_bp_zn         (io_lpddr_ppp_1_bp_zn),
      .io_lpddr_ppp_2_bp_zn         (io_lpddr_ppp_2_bp_zn),
      .io_lpddr_ppp_3_bp_zn         (io_lpddr_ppp_3_bp_zn),
      .o_lpddr_graph_0_bp_memreset_l(o_lpddr_graph_0_bp_memreset_l),
      .o_lpddr_graph_1_bp_memreset_l(o_lpddr_graph_1_bp_memreset_l),
      .o_lpddr_graph_2_bp_memreset_l(o_lpddr_graph_2_bp_memreset_l),
      .o_lpddr_graph_3_bp_memreset_l(o_lpddr_graph_3_bp_memreset_l),
      .io_lpddr_graph_0_bp_a        (io_lpddr_graph_0_bp_a),
      .io_lpddr_graph_1_bp_a        (io_lpddr_graph_1_bp_a),
      .io_lpddr_graph_2_bp_a        (io_lpddr_graph_2_bp_a),
      .io_lpddr_graph_3_bp_a        (io_lpddr_graph_3_bp_a),
      .io_lpddr_graph_0_bp_ato      (io_lpddr_graph_0_bp_ato),
      .io_lpddr_graph_1_bp_ato      (io_lpddr_graph_1_bp_ato),
      .io_lpddr_graph_2_bp_ato      (io_lpddr_graph_2_bp_ato),
      .io_lpddr_graph_3_bp_ato      (io_lpddr_graph_3_bp_ato),
      .io_lpddr_graph_0_bp_ato_pll  (io_lpddr_graph_0_bp_ato_pll),
      .io_lpddr_graph_1_bp_ato_pll  (io_lpddr_graph_1_bp_ato_pll),
      .io_lpddr_graph_2_bp_ato_pll  (io_lpddr_graph_2_bp_ato_pll),
      .io_lpddr_graph_3_bp_ato_pll  (io_lpddr_graph_3_bp_ato_pll),
      .io_lpddr_graph_0_bp_b0_d     (io_lpddr_graph_0_bp_b0_d),
      .io_lpddr_graph_1_bp_b0_d     (io_lpddr_graph_1_bp_b0_d),
      .io_lpddr_graph_2_bp_b0_d     (io_lpddr_graph_2_bp_b0_d),
      .io_lpddr_graph_3_bp_b0_d     (io_lpddr_graph_3_bp_b0_d),
      .io_lpddr_graph_0_bp_b1_d     (io_lpddr_graph_0_bp_b1_d),
      .io_lpddr_graph_1_bp_b1_d     (io_lpddr_graph_1_bp_b1_d),
      .io_lpddr_graph_2_bp_b1_d     (io_lpddr_graph_2_bp_b1_d),
      .io_lpddr_graph_3_bp_b1_d     (io_lpddr_graph_3_bp_b1_d),
      .io_lpddr_graph_0_bp_b2_d     (io_lpddr_graph_0_bp_b2_d),
      .io_lpddr_graph_1_bp_b2_d     (io_lpddr_graph_1_bp_b2_d),
      .io_lpddr_graph_2_bp_b2_d     (io_lpddr_graph_2_bp_b2_d),
      .io_lpddr_graph_3_bp_b2_d     (io_lpddr_graph_3_bp_b2_d),
      .io_lpddr_graph_0_bp_b3_d     (io_lpddr_graph_0_bp_b3_d),
      .io_lpddr_graph_1_bp_b3_d     (io_lpddr_graph_1_bp_b3_d),
      .io_lpddr_graph_2_bp_b3_d     (io_lpddr_graph_2_bp_b3_d),
      .io_lpddr_graph_3_bp_b3_d     (io_lpddr_graph_3_bp_b3_d),
      .io_lpddr_graph_0_bp_ck0_c    (io_lpddr_graph_0_bp_ck0_c),
      .io_lpddr_graph_1_bp_ck0_c    (io_lpddr_graph_1_bp_ck0_c),
      .io_lpddr_graph_2_bp_ck0_c    (io_lpddr_graph_2_bp_ck0_c),
      .io_lpddr_graph_3_bp_ck0_c    (io_lpddr_graph_3_bp_ck0_c),
      .io_lpddr_graph_0_bp_ck0_t    (io_lpddr_graph_0_bp_ck0_t),
      .io_lpddr_graph_1_bp_ck0_t    (io_lpddr_graph_1_bp_ck0_t),
      .io_lpddr_graph_2_bp_ck0_t    (io_lpddr_graph_2_bp_ck0_t),
      .io_lpddr_graph_3_bp_ck0_t    (io_lpddr_graph_3_bp_ck0_t),
      .io_lpddr_graph_0_bp_ck1_c    (io_lpddr_graph_0_bp_ck1_c),
      .io_lpddr_graph_1_bp_ck1_c    (io_lpddr_graph_1_bp_ck1_c),
      .io_lpddr_graph_2_bp_ck1_c    (io_lpddr_graph_2_bp_ck1_c),
      .io_lpddr_graph_3_bp_ck1_c    (io_lpddr_graph_3_bp_ck1_c),
      .io_lpddr_graph_0_bp_ck1_t    (io_lpddr_graph_0_bp_ck1_t),
      .io_lpddr_graph_1_bp_ck1_t    (io_lpddr_graph_1_bp_ck1_t),
      .io_lpddr_graph_2_bp_ck1_t    (io_lpddr_graph_2_bp_ck1_t),
      .io_lpddr_graph_3_bp_ck1_t    (io_lpddr_graph_3_bp_ck1_t),
      .io_lpddr_graph_0_bp_zn       (io_lpddr_graph_0_bp_zn),
      .io_lpddr_graph_1_bp_zn       (io_lpddr_graph_1_bp_zn),
      .io_lpddr_graph_2_bp_zn       (io_lpddr_graph_2_bp_zn),
      .io_lpddr_graph_3_bp_zn       (io_lpddr_graph_3_bp_zn),
      .io_pcie_resref               (io_pcie_resref),
      .i_ref_pad_clk_p              (i_ref_pad_clk_p),
      .i_ref_pad_clk_m              (i_ref_pad_clk_m),
      .i_pcie_perst_n               (i_pcie_perst_n),
      .i_pcie_rxm_00                (i_pcie_rxm_00),
      .i_pcie_rxm_01                (i_pcie_rxm_01),
      .i_pcie_rxm_02                (i_pcie_rxm_02),
      .i_pcie_rxm_03                (i_pcie_rxm_03),
      .i_pcie_rxp_00                (i_pcie_rxp_00),
      .i_pcie_rxp_01                (i_pcie_rxp_01),
      .i_pcie_rxp_02                (i_pcie_rxp_02),
      .i_pcie_rxp_03                (i_pcie_rxp_03),
      .o_pcie_txm_00                (o_pcie_txm_00),
      .o_pcie_txm_01                (o_pcie_txm_01),
      .o_pcie_txm_02                (o_pcie_txm_02),
      .o_pcie_txm_03                (o_pcie_txm_03),
      .o_pcie_txp_00                (o_pcie_txp_00),
      .o_pcie_txp_01                (o_pcie_txp_01),
      .o_pcie_txp_02                (o_pcie_txp_02),
      .o_pcie_txp_03                (o_pcie_txp_03)
  );

  //-----------------------------------------------------------
  // generate: resets
  //-----------------------------------------------------------
  // tbx clkgen
  initial begin
    i_por_rst_n = 0;
    i_trst_n = 0;
    i_spi_rst_n = 0;
    #1000;
    i_por_rst_n = 1;
    i_trst_n = 1;
    i_spi_rst_n = 1;
  end

  //-----------------------------------------------------------
  // bind: CPU traces
  //-----------------------------------------------------------
  logic enable_ax65_instruction_dump = 0;
  logic new_file_ax65_instruction_dump = 0;
  bind ax65_core_top instn_simple_pipe_mon instn_simple_pipe_mon (
      .enable  (hdl_top.enable_ax65_instruction_dump),
      .new_file(hdl_top.new_file_ax65_instruction_dump)
  );

  logic enable_cva6v_instruction_dump = 0;
  logic new_file_cva6v_instruction_dump = 0;
  bind cva6v_top cva6v_monitor i_cva6v_monitor (
      .clk_i        (clk_i),
      .rst_ni       (rst_ni),
      .hart_id_i    (hart_id_i),
      .enable       (hdl_top.enable_cva6v_instruction_dump),
      .new_file     (hdl_top.new_file_cva6v_instruction_dump),
      .rvfi_probes_o(rvfi_probes_o)
  );

  //-----------------------------------------------------------
  // instantiate: UART transactor
  //-----------------------------------------------------------
  bit uart_clk_4x;
  uart_xactor i_uart_xactor (
      .clk(uart_clk_4x),
      .rx (o_uart_tx),
      .tx (i_uart_rx)
  );

`ifdef TARGET_EMMC_SOFTMODEL
  //-----------------------------------------------------------
  // instantiate: EMMC softmodel
  //-----------------------------------------------------------
 `define USER_DENSITY   28  //== 256MB
 `define BOOT1_DENSITY  18  //==
 `define BOOT2_DENSITY  18  //== 256KB
 `define GP1_DENSITY    20  //== 1MB
 `define GP2_DENSITY    20  //== 1MB
 `define GP3_DENSITY    20  //== 1MB
 `define GP4_DENSITY    20  //== 1MB
 `define RPMB_DENSITY   18 //== 256KB
 `define FFU_DENSITY    20   //== 1 MB
 `define ready_for_execution_delay 100 // Must be at least 74
 `define FFU_EN             //Enable FFU

 // Minimum 10 cycles after CMD was low for 74 cycles, the softmodel will drive the boot acknowledge pattern
 `define BOOT_ACK_TIMING 84

 // Minimum size of a write protection group, which can be configured during runtime by preloading CSD and
 // EXT_CSD registers. The value is interpreted like the above listed DENSITY parameters:
 // *_WP_UNIT_SIZE_MIN 9 is 512 bytes
 // *_WP_UNIT_SIZE_MIN 13 is 8192 bytes
 // *_WP_UNIT_SIZE_MIN 19 is 524288 bytes (512kB)
 // i.e. 2**(WP_UNIT_SIZE_MIN)
 // The smallest possible size of a write protection unit is 512 bytes.
 // The maximum number of write protection units that are possible are:
 // ([2**(USER_DENSITY-US_WP_UNIT_SIZE_MIN)]-1)
 // ([2**(GP*_DENSITY-GP_WP_UNIT_SIZE_MIN)]-1)
 // It's possible to constraint the USER area differently than the GP partitions
 `define US_WP_UNIT_SIZE_MIN 19
 `define GP_WP_UNIT_SIZE_MIN 13

 // The softmodel will drive boot data 20 cycles after the boot acknowledge pattern was output
 `define BOOT_DATA_TIMING 84+20

 // Added 07mar12
 // CRC status token output timing after block writes
 // CRC_EARLY = 0 is 4 cycles after end bit of data block
 // CRC_EARLY = 1 is 3 cycles after end bit of data block
 // CRC_EARLY = 2 is 2 cycles after end bit of data block
 `define CRC_EARLY 2

  // Tie card detect at 0 -> card inserted
  always_comb i_sd_emmc_detect = 1'b0;
  // Use external lpbk dqs for data sampling
  always_comb i_emmc_lpbk_dqs = io_emmc_rebar;
  // Tie write protect signal to 1 (as per EMMC spec)
  always_comb i_sd_emmc_wp = 1'b1;

  veloce_emmc_sm  #(.USER_DENSITY(`USER_DENSITY),
                    .BOOT1_DENSITY(`BOOT1_DENSITY),
                    .BOOT2_DENSITY(`BOOT2_DENSITY),
                    .GP0_DENSITY(`GP1_DENSITY),
                    .GP1_DENSITY(`GP2_DENSITY),
                    .GP2_DENSITY(`GP3_DENSITY),
                    .GP3_DENSITY(`GP4_DENSITY),
                    .RPMB_DENSITY(`RPMB_DENSITY),
  `ifdef FFU_EN
                    .FFU_DENSITY(`FFU_DENSITY),
  `endif
                    .ready_for_execution_delay(`ready_for_execution_delay),
                    .tBA(`BOOT_ACK_TIMING),
                    .tBD(`BOOT_DATA_TIMING),
                    .NCRC(`CRC_EARLY),
                    .US_WP_UNIT_SIZE_MIN (`US_WP_UNIT_SIZE_MIN),
                    .GP_WP_UNIT_SIZE_MIN (`GP_WP_UNIT_SIZE_MIN)) i_emmc_softmodel (
                    //-- Input
                    .CLK                 (o_sd_emmc_clk_out),
                    .RST_N               (o_emmc_reset),
                    .WRONG_CRC           (1'b0), // Do not generate wrong CRC
                    .PoweredOff          (1'b0), // Do not model power cycles
                    //-- Output
                    .DS                  (i_sd_emmc_strobe),
                    //-- InOut
                    .DAT                 (io_sd_emmc_data),
                    .CMD                 (io_sd_emmc_cmd)
          );
`endif

`ifdef TARGET_SPINOR_S25FS512S
  logic spi_clk2x;
  //-----------------------------------------------------------
  // instantiate: SPI softmodel
  //-----------------------------------------------------------

  veloce_s25fs512s i_spi_softmodel (
    .RST_N                    (i_spi_rst_n),
    .clk2x                    (spi_clk2x),
    .C                        (o_spi_clk_out),
    .S_N                      (o_spi_ss_n),
    .SIO0                     (io_spi_sd[0]),
    .SIO1                     (io_spi_sd[1]),
    .SIO2_WP_N                (io_spi_sd[2]),
    .SIO3                     (io_spi_sd[3])
  );
`endif

  //-----------------------------------------------------------
  // instantiate: LPDDR DRAM models
  //-----------------------------------------------------------
  // TODO: @rodrigo.borges - currently only adding DRAM connections to graph_0
  // Need to expand to all LPDDR modules by adding a macro
  `ifdef TARGET_SIMULATION
    `ifndef LPDDR_P_GRAPH_0_STUB
      // /data/foundry/dram_simulation_models/samsung/lpddr5x_qst_behav_rev0.30_D1z_16Gb_x16.vp
      // Based on Table 4-2 LPDDR5/5X DFI-to-SDRAM Pin Map (Dual Channel, Two Ranks) - page 115 of
      // LPDDR5X/5/4X PHY Utility Block (PUB) Databook - Version 2.30a (May 7, 2024)
      LPDDRV_PKG_MONO_X16 sdram_graph_0_channel_a_rank_0 (
        .CK_t     (io_lpddr_graph_0_bp_ck0_t                                        ),
        .CK_c     (io_lpddr_graph_0_bp_ck0_c                                        ),
        .CS       (io_lpddr_graph_0_bp_a[4]                                         ),
        .CA       ({io_lpddr_graph_0_bp_a[8:6]     , io_lpddr_graph_0_bp_a[3:0]   } ),
        .DQ       ({io_lpddr_graph_0_bp_b1_d[7:0]  , io_lpddr_graph_0_bp_b0_d[7:0]} ),
        .WCK_t    ({io_lpddr_graph_0_bp_b1_d[11]   , io_lpddr_graph_0_bp_b0_d[11] } ),
        .WCK_c    ({io_lpddr_graph_0_bp_b1_d[10]   , io_lpddr_graph_0_bp_b0_d[10] } ),
        .DMI      ({io_lpddr_graph_0_bp_b1_d[12]   , io_lpddr_graph_0_bp_b0_d[12] } ),
        .RESET_n  (o_lpddr_graph_0_bp_memreset_l                                    ),
        .RDQS_t   ({io_lpddr_graph_0_bp_b1_d[9]    , io_lpddr_graph_0_bp_b0_d[9]  } ),
        .RDQS_c   ({io_lpddr_graph_0_bp_b1_d[8]    , io_lpddr_graph_0_bp_b0_d[8]  } ),
        // ZQ is used to calibrate the output drive strentgh and the termination resistance
        // as calibration resistance.
        .ZQ       (/* unconnected */                                                )
      );

      LPDDRV_PKG_MONO_X16 sdram_graph_0_channel_a_rank_1 (
        .CK_t     (io_lpddr_graph_0_bp_ck0_t                                        ),
        .CK_c     (io_lpddr_graph_0_bp_ck0_c                                        ),
        .CS       (io_lpddr_graph_0_bp_a[5]                                         ),
        .CA       ({io_lpddr_graph_0_bp_a[8:6]     , io_lpddr_graph_0_bp_a[3:0]   } ),
        .DQ       ({io_lpddr_graph_0_bp_b1_d[7:0]  , io_lpddr_graph_0_bp_b0_d[7:0]} ),
        .WCK_t    ({io_lpddr_graph_0_bp_b1_d[11]   , io_lpddr_graph_0_bp_b0_d[11] } ),
        .WCK_c    ({io_lpddr_graph_0_bp_b1_d[10]   , io_lpddr_graph_0_bp_b0_d[10] } ),
        .DMI      ({io_lpddr_graph_0_bp_b1_d[12]   , io_lpddr_graph_0_bp_b0_d[12] } ),
        .RESET_n  (o_lpddr_graph_0_bp_memreset_l                                    ),
        .RDQS_t   ({io_lpddr_graph_0_bp_b1_d[9]    , io_lpddr_graph_0_bp_b0_d[9]  } ),
        .RDQS_c   ({io_lpddr_graph_0_bp_b1_d[8]    , io_lpddr_graph_0_bp_b0_d[8]  } ),
        // ZQ is used to calibrate the output drive strentgh and the termination resistance
        // as calibration resistance.
        .ZQ       (/* unconnected */                                                )
      );

      LPDDRV_PKG_MONO_X16 sdram_graph_0_channel_b_rank_0 (
        .CK_t     (io_lpddr_graph_0_bp_ck1_t                                        ),
        .CK_c     (io_lpddr_graph_0_bp_ck1_c                                        ),
        .CS       (io_lpddr_graph_0_bp_a[14]                                        ),
        .CA       ({io_lpddr_graph_0_bp_a[18:16]   , io_lpddr_graph_0_bp_a[13:10] } ),
        .DQ       ({io_lpddr_graph_0_bp_b3_d[7:0]  , io_lpddr_graph_0_bp_b2_d[7:0]} ),
        .WCK_t    ({io_lpddr_graph_0_bp_b3_d[11]   , io_lpddr_graph_0_bp_b2_d[11] } ),
        .WCK_c    ({io_lpddr_graph_0_bp_b3_d[10]   , io_lpddr_graph_0_bp_b2_d[10] } ),
        .DMI      ({io_lpddr_graph_0_bp_b3_d[12]   , io_lpddr_graph_0_bp_b2_d[12] } ),
        .RESET_n  (o_lpddr_graph_0_bp_memreset_l                                    ),
        .RDQS_t   ({io_lpddr_graph_0_bp_b3_d[9]    , io_lpddr_graph_0_bp_b2_d[9]  } ),
        .RDQS_c   ({io_lpddr_graph_0_bp_b3_d[8]    , io_lpddr_graph_0_bp_b2_d[8]  } ),
        // ZQ is used to calibrate the output drive strentgh and the termination resistance
        // as calibration resistance.
        .ZQ       (/* unconnected */                                                )
      );

      LPDDRV_PKG_MONO_X16 sdram_graph_0_channel_b_rank_1 (
        .CK_t     (io_lpddr_graph_0_bp_ck1_t                                        ),
        .CK_c     (io_lpddr_graph_0_bp_ck1_c                                        ),
        .CS       (io_lpddr_graph_0_bp_a[15]                                        ),
        .CA       ({io_lpddr_graph_0_bp_a[18:16]   , io_lpddr_graph_0_bp_a[13:10] } ),
        .DQ       ({io_lpddr_graph_0_bp_b3_d[7:0]  , io_lpddr_graph_0_bp_b2_d[7:0]} ),
        .WCK_t    ({io_lpddr_graph_0_bp_b3_d[11]   , io_lpddr_graph_0_bp_b2_d[11] } ),
        .WCK_c    ({io_lpddr_graph_0_bp_b3_d[10]   , io_lpddr_graph_0_bp_b2_d[10] } ),
        .DMI      ({io_lpddr_graph_0_bp_b3_d[12]   , io_lpddr_graph_0_bp_b2_d[12] } ),
        .RESET_n  (o_lpddr_graph_0_bp_memreset_l                                    ),
        .RDQS_t   ({io_lpddr_graph_0_bp_b3_d[9]    , io_lpddr_graph_0_bp_b2_d[9]  } ),
        .RDQS_c   ({io_lpddr_graph_0_bp_b3_d[8]    , io_lpddr_graph_0_bp_b2_d[8]  } ),
        // ZQ is used to calibrate the output drive strentgh and the termination resistance
        // as calibration resistance.
        .ZQ       (/* unconnected */                                                )
      );
    `endif // !LPDDR_P_GRAPH_0_STUB
  `endif // TARGET_SIMULATION

  //-----------------------------------------------------------
  // workarounds: should be removed when fixed
  //-----------------------------------------------------------
  import apu_pkg::*;
  bit [CORE_WIDTH - 1:0][47:0] cores_reset_vector;
  initial begin
    // FIXME: connect to input once accessible
    cores_reset_vector[0] = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
    cores_reset_vector[1] = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
    cores_reset_vector[2] = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
    cores_reset_vector[3] = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
    cores_reset_vector[4] = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
    cores_reset_vector[5] = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
    force i_europa.u_aipu.u_apu_p.u_apu.i_cores_reset_vector = cores_reset_vector;
  end

  // FIXME: avoid "Invalid value on memory instance" error
  initial begin
    `ifndef LPDDR_P_PPP_0_STUB
      force i_europa.u_aipu.u_lpddr_p_ppp_0.i_lpddr_clk = 0;
    `endif
    `ifndef LPDDR_P_PPP_1_STUB
      force i_europa.u_aipu.u_lpddr_p_ppp_2.i_lpddr_clk = 0;
    `endif
    `ifndef LPDDR_P_PPP_2_STUB
      force i_europa.u_aipu.u_lpddr_p_ppp_2.i_lpddr_clk = 0;
    `endif
    `ifndef LPDDR_P_PPP_3_STUB
      force i_europa.u_aipu.u_lpddr_p_ppp_3.i_lpddr_clk = 0;
    `endif
    `ifndef LPDDR_P_GRAPH_0_STUB
      force i_europa.u_aipu.u_lpddr_p_graph_0.i_lpddr_clk = 0;
    `endif
    `ifndef LPDDR_P_GRAPH_1_STUB
      force i_europa.u_aipu.u_lpddr_p_graph_1.i_lpddr_clk = 0;
    `endif
    `ifndef LPDDR_P_GRAPH_2_STUB
      force i_europa.u_aipu.u_lpddr_p_graph_2.i_lpddr_clk = 0;
    `endif
    `ifndef LPDDR_P_GRAPH_3_STUB
      force i_europa.u_aipu.u_lpddr_p_graph_3.i_lpddr_clk = 0;
    `endif
  end

  // FIXME (LPDDR): support interleaving (https://git.axelera.ai/prod/europa/-/issues/2173)
  // With current forces, DDR0 and DDR1 are continuous
  initial begin
    force i_europa.u_aipu.u_noc_top.i_lpddr_graph_addr_mode_port_b0 = '0;
    force i_europa.u_aipu.u_noc_top.i_lpddr_graph_addr_mode_port_b1 = '0;
    force i_europa.u_aipu.u_noc_top.i_lpddr_graph_intr_mode_port_b0 = '0;
    force i_europa.u_aipu.u_noc_top.i_lpddr_graph_intr_mode_port_b1 = '0;
    force i_europa.u_aipu.u_noc_top.i_lpddr_ppp_addr_mode_port_b0 = '0;
    force i_europa.u_aipu.u_noc_top.i_lpddr_ppp_addr_mode_port_b1 = '0;
    force i_europa.u_aipu.u_noc_top.i_lpddr_ppp_intr_mode_port_b0 = '0;
    force i_europa.u_aipu.u_noc_top.i_lpddr_ppp_intr_mode_port_b1 = '0;
  end

  //-----------------------------------------------------------
  // Connect: i2c wires for interrupt tests
  //-----------------------------------------------------------
  pullup(io_i2c_0_data);
  pullup(io_i2c_1_data);
  pullup(io_i2c_0_clk);
  pullup(io_i2c_1_clk);

`ifdef TARGET_EMULATION

  //Ring Oscilator
  `define SECU_ENCLAVE_INST_PATH hdl_top.i_europa.u_aipu.u_soc_mgmt_p.u_soc_mgmt.u_soc_mgmt_secu_enclave
  bit [31:0] rand0;

  initial begin
    rand0 = 32'h8ecf4837; //initial value
    force `SECU_ENCLAVE_INST_PATH.ro_clk = rand0[7:0];
  end
  always @(posedge `SECU_ENCLAVE_INST_PATH.i_clk) begin
    if (`SECU_ENCLAVE_INST_PATH.ro_en) begin
      rand0 ^= rand0 << 13;
      rand0 ^= rand0 >> 7;
      rand0 ^= rand0 << 17;
    end
  end
`endif // TARGET_EMULATION
endmodule
