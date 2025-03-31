// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: A wrapper that groups the IMC row instances, the imc_ctrl_delay and the strb_buf into one IMC and acc stage of the mvm DP.
// Backpressure implemented using a single clock gate for all instances.
// To be seen if this is ok in physical. Could be split into one clock gate for each imc_row
// Takes the serial output data from the par2bser stage as input data.
// Produces the mvm output result after alle serial cycles have passed + the imc delay.
// Owner: Roel Uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_IMC_ACC_SV
`define MVM_IMC_ACC_SV

module mvm_imc_acc
  import imc_bank_pkg::*;
  import mvm_pkg::*;
  import imc_bist_pkg::*;
#(
  parameter type aic_csr_hw2reg_t = imc_bist_pkg::aic_csr_hw2reg_t,
  parameter type aic_csr_reg2hw_t = imc_bist_pkg::aic_csr_reg2hw_t,
  parameter type aic_csr_reg2hw_imc_status_t = imc_bist_pkg::hw2reg_imc_bist_status_reg_t
) (
  input wire i_clk,
  input wire i_rst_n,
  input logic jtag_tcki,
  input logic jtag_i_rst_n,

  // Incoming programming ctrl stream
  input  logic                           prg_cmd_tvalid,
  input  mvm_prg_dp_cmd_t                prg_cmd_tdata,
  output logic                           prg_cmd_tready,
  // Weight input PWs
  input  logic  [PW_LEN-1:0][DATA_W-1:0] weight_pw,

  // Serial input bits
  // Incoming IMC ACC OUT ctrl stream
  // IFD0
  //input logic                            imc_acc_dp_cmd_tvalid,
  input imc_acc_dp_cmd_t                 ifd0_imc_acc_dp_cmd_tdata,
  input logic                            ifd0_imc_acc_stall_i,
  input logic                            ifd0_serial_conversion_valid_i,
  input logic          [IMC_NB_ROWS-1:0] ifd0_c_in_ser,
  // IFD2
  input imc_acc_dp_cmd_t                 ifd2_imc_acc_dp_cmd_tdata,
  input logic                            ifd2_imc_acc_stall_i,
  input logic                            ifd2_serial_conversion_valid_i,
  input logic          [IMC_NB_ROWS-1:0] ifd2_c_in_ser,

  // output results
  output logic compute_output_32_valid,
  output compute_out_ctrl_t compute_output_32_ctrl,
  output logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] compute_output_32,
  output logic compute_output_64_valid,
  output compute_out_ctrl_t compute_output_64_ctrl,
  output logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] compute_output_64,

  // CSR signals
  input logic csr_signed_weights_i,
  input logic csr_signed_inputs_i,
  input logic csr_power_smooth_dummy_ops_i,
  input logic csr_disable_imc_acc_clock_gating_i,

  // Error signals
  output logic err_concurrent_exe_prg_on_ws_o,

  // DFT signals
  input logic test_mode_i,
  input logic scan_en,
  // IMC BIST
  input  aic_csr_reg2hw_t imc_bist_tdr2hw_i,
  output aic_csr_hw2reg_t imc_bist_hw2tdr_o,
  input  aic_csr_reg2hw_t imc_bist_csr2hw_i,
  output aic_csr_hw2reg_t imc_bist_hw2csr_o

);
  localparam int unsigned MvmNbImcBanksOnRow = PW_LEN / IMC_NB_COLS_PER_BANK;

  logic [MVM_NB_IMC_BANKS/2-1:0] err_concurrent_exe_prg_on_ws_all_banks;
  assign err_concurrent_exe_prg_on_ws_o = |err_concurrent_exe_prg_on_ws_all_banks;

  // Wait programming is always ready. As a long term feature this could detect a conflict with an exe operation on the same weight set.
  // However, that also requires determining who should get priority to guarantee data consitency
  // For now, an interrupt is triggered in the event of concurrent access to the same weight set by PRG and EXE, and it is upto software to avoid this situation.
  assign prg_cmd_tready = 1'b1;

  // Block gating inferral from input/output gating, can be enabled or disabled through csr at any time (even during compute operation).
  // compute block enable signals
  logic [MVM_NB_IMC_BANKS-1:0][IMC_NB_ROWS/IMC_BLOCK_GATING_GRANULARITY-1:0] ifd0_imc_compute_block_enable;
  always_comb begin
    for (int col = 0; col < MVM_NB_IMC_BANKS; col++) begin
      for (int row = 0; row < IMC_NB_ROWS / IMC_BLOCK_GATING_GRANULARITY; row++) begin
        ifd0_imc_compute_block_enable[col][row] = ifd0_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.inp_gating[row]
                                                & ifd0_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.oup_gating[col];
      end
    end
  end
  logic [MVM_NB_IMC_BANKS-1:0][IMC_NB_ROWS/IMC_BLOCK_GATING_GRANULARITY-1:0] ifd2_imc_compute_block_enable;
  always_comb begin
    foreach (ifd2_imc_compute_block_enable[col,row]) begin
      ifd2_imc_compute_block_enable[col][row] = ifd2_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.inp_gating[row]
                                              & ifd2_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.oup_gating[col];
    end
  end

  // Gate write enable from prg_cmd_tdata with valid and ready to avoid unvalid weights being written
  logic [PW_LEN-1:0][DATA_W-1:0] weight_pw_packed;
  logic prg_global_we;
  logic [MVM_NB_IMC_BANKS-1:0] prg_bank_we;
  assign prg_global_we = prg_cmd_tvalid & prg_cmd_tready;
  assign prg_bank_we   = prg_cmd_tdata.imc_prg_we & {MVM_NB_IMC_BANKS{prg_global_we}};

  always_comb begin
    foreach (weight_pw_packed[i]) weight_pw_packed[i] = weight_pw[i];
  end

  //////////////////////////
  // IMC with accs instantiations linked together using pipeline registers

  // verilog_lint: waive-start line-length
  logic [MVM_NB_IMC_BANKS/2-1:0] imc_compute_output_valids;
  compute_out_ctrl_t [MVM_NB_IMC_BANKS/2-1:0] imc_compute_output_ctrls;
  logic [MVM_NB_IMC_BANKS/2-1:0] [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] imc_compute_outputs;
  logic [MVM_NB_IMC_BANKS/2-3:0] imc_compute_out_valids_muxed;
  compute_out_ctrl_t [MVM_NB_IMC_BANKS/2-1:0] imc_compute_out_ctrls_muxed;
  logic [MVM_NB_IMC_BANKS/2-3:0] [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] imc_compute_outs_muxed;

  logic [MVM_NB_IMC_BANKS/2-1:0] [1:0] imc_compute_in_valid, imc_compute_in_valid_piped;
  logic [MVM_NB_IMC_BANKS/2-1:0] [1:0] imc_compute_in_stall, imc_compute_in_stall_piped;
  imc_compute_struct_t [MVM_NB_IMC_BANKS/2-1:0] [1:0] imc_compute_in, imc_compute_in_piped;
  imc_compute_struct_t ifd0_imc_par2bser_compute_in, ifd2_imc_par2bser_compute_in;
  imc_compute_struct_t imc_bist_compute_in, imc_bank_compute_in;

  logic [MVM_NB_IMC_BANKS/2-1:0] imc_weight_in_valid, imc_weight_in_valid_piped;
  imc_weight_struct_t  [MVM_NB_IMC_BANKS/2-1:0] imc_weight_in, imc_weight_in_piped;
  imc_weight_struct_t imc_ifd_weight_in, imc_bist_weight_in, imc_bank_weight_in;

  imc_repair_struct_t imc_repair_in;
  imc_repair_struct_t [MVM_NB_IMC_BANKS/2-1:0] imc_repair_intf_in, imc_repair_intf_piped;
  // verilog_lint: waive-stop line-length

  //synopsys translate_off
`ifdef ASSERTIONS_ON
  logic [MVM_NB_IMC_BANKS-1:0] active_banks;
`endif  //ASSERTIONS_ON
  //synopsys translate_on

  //////////////////////////
  // IMC BIST

  // IMC BIST CTL <-> GEN
  logic imc_bist_start_p, imc_bist_resume_p, imc_bist_stop_p, imc_bist_gen_busy;

  imc_bist_pkg::bist_type_e imc_bist_type;

  // IMC BIST CTL <-> IMUX/IMUXC
  logic imc_bist_mode;
  wire i_clk_bist_cg;

  // IMC BIST CTL <-> COLL
  logic imc_bist_fault_det, imc_bist_fault_valid, imc_bist_fault_pop;

  logic [mvm_pkg::MVM_IMC_BANK_PW-1:0] imc_bist_fault_bank;
  logic [imc_bank_pkg::IMC_BANK_COL_PW-1:0] imc_bist_fault_col;
  logic [imc_bist_pkg::IMC_BIST_CYCLE_PW-1:0] imc_bist_fault_cycle;

  // IMC BIST GEN <-> IMUX
  logic imc_bist_write_enable;
  logic [imc_bank_pkg::IMC_NB_COLS_PER_BANK-1:0][mvm_pkg::DATA_W-1:0] imc_bist_write_values;
  logic [imc_bank_pkg::IMC_ROW_PW-1:0] imc_bist_write_row;
  logic [imc_bank_pkg::IMC_WEIGHT_SET_PW-1:0] imc_bist_write_wss;
  logic [mvm_pkg::PW_LEN-1:0][mvm_pkg::DATA_W-1:0] imc_bist_weight_pw;

  // IMC BIST GEN <-> IMUXC
  logic imc_bist_compute_enable;
  logic [imc_bank_pkg::IMC_BLOCK_ENABLE_W-1:0] imc_bist_compute_block_enable;
  logic imc_bist_compute_gate_clock;
  logic imc_bist_compute_signed_weights;
  logic [imc_bank_pkg::IMC_NB_ROWS-1:0] imc_bist_compute_inp;
  logic [imc_bank_pkg::IMC_WEIGHT_SET_PW-1:0] imc_bist_compute_wss;

  // verilog_lint: waive-start line-length
  // IMC BIST GEN -> COMP -> COMP -> ... -> COLL
  // Compare bus for first pair (is all 0s)
  imc_bist_pkg::compare_bus_t [imc_bist_pkg::NUM_COMPARATORS-1:0] imc_bist_compare_bus_gen;
  // Compare bus to the pairs
  imc_bist_pkg::compare_bus_t [imc_bist_pkg::NUM_COMPARATORS-1:0][imc_bist_pkg::NUM_COMPARATORS-1:0] imc_bist_compare_bus;
  // Compare bus from the pairs
  imc_bist_pkg::compare_bus_t [imc_bist_pkg::NUM_COMPARATORS-1:0][imc_bist_pkg::NUM_COMPARATORS-1:0] imc_bist_compare_bus_piped;
  // Expect strobe from the generator
  logic imc_bist_expect_strobe_gen;
  // IMC BIST mode to the pairs
  logic [imc_bist_pkg::NUM_COMPARATORS-1:0] imc_pair_bist_mode;
  // IMC BIST mode from the pairs
  logic [imc_bist_pkg::NUM_COMPARATORS-1:0] imc_pair_bist_mode_piped;
  // Expect strobe to the pairs
  logic [imc_bist_pkg::NUM_COMPARATORS:0] imc_bist_expect_strobe;
  // Expect strobe from the pairs
  logic [imc_bist_pkg::NUM_COMPARATORS:0] imc_bist_expect_strobe_piped;
  // Expect type from the generator
  imc_bist_pkg::expect_type_e imc_bist_expect_type_gen;
  // Expect type to the pairs
  imc_bist_pkg::expect_type_e [imc_bist_pkg::NUM_COMPARATORS-1:0] imc_bist_expect_type;
  // Expect type from the pairs
  imc_bist_pkg::expect_type_e [imc_bist_pkg::NUM_COMPARATORS-1:0] imc_bist_expect_type_piped;
  // verilog_lint: waive-stop line-length

  // IMC BIST IMUX <-> IMC BANK
  logic imc_bank_write_enable;
  logic [imc_bank_pkg::IMC_NB_COLS_PER_BANK-1:0][mvm_pkg::DATA_W-1:0] imc_bank_write_values;
  logic [imc_bank_pkg::IMC_ROW_PW-1:0] imc_bank_write_row;
  logic [imc_bank_pkg::IMC_WEIGHT_SET_PW-1:0] imc_bank_write_wss;

  // JTAG/CSR <-> IMC BIST INTF MUX <-> IMC BIRA BISR
  aic_csr_reg2hw_t imc_bist_mux2hw;
  aic_csr_hw2reg_t imc_bist_hw2mux;
  aic_csr_reg2hw_t imc_bist_bira2hw;
  aic_csr_hw2reg_t imc_bist_hw2bira;
  // IMC BIRA BISR <-> REPAIR HOOKS
  logic imc_bisr_mux_mode;
  logic imc_bisr_shift_en;
  logic imc_bisr_ue;
  logic imc_bisr_si;
  logic imc_bisr_so;

  imc_bist_intf_mux #(
    .aic_csr_hw2reg_t(aic_csr_hw2reg_t),
    .aic_csr_reg2hw_t(aic_csr_reg2hw_t)
  ) u_imc_bist_intf_mux (
    .i_clk,
    .i_rst_n,
    .i_regcsr(imc_bist_csr2hw_i),
    .o_regcsr(imc_bist_hw2csr_o),
    .i_regjtag(imc_bist_tdr2hw_i),
    .o_regjtag(imc_bist_hw2tdr_o),
    .i_regmuxed(imc_bist_hw2mux),
    .o_regmuxed(imc_bist_mux2hw)
  );

  imc_bira_bisr #(
    .aic_csr_hw2reg_t(aic_csr_hw2reg_t),
    .aic_csr_reg2hw_t(aic_csr_reg2hw_t)
  ) u_imc_bira_bisr (
    .i_clk,
    .i_rst_n,
    .i_mux_reg(imc_bist_mux2hw),
    .o_mux_reg(imc_bist_hw2mux),
    .o_ctl_reg(imc_bist_bira2hw),
    .i_ctl_reg(imc_bist_hw2bira),
    .o_imc_bisr_mux_mode(imc_bisr_mux_mode),
    .o_imc_bisr_shift_en(imc_bisr_shift_en),
    .o_imc_bisr_ue(imc_bisr_ue),
    .o_imc_bisr_si(imc_bisr_si),
    .i_imc_bisr_so(imc_bisr_so)
  );

  imc_bist_ctl  #(
    .aic_csr_hw2reg_t(aic_csr_hw2reg_t),
    .aic_csr_reg2hw_t(aic_csr_reg2hw_t),
    .aic_csr_reg2hw_imc_status_t(aic_csr_reg2hw_imc_status_t)
  ) i_imc_bist_ctl (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .jtag_tck_i(jtag_tcki),
    .jtag_ti_rst_n(jtag_i_rst_n),

    // <-> CSR/JTAG
    .regcsr_i ('0), // TODO: regcsr can be removed (moved to imc_bist_intf_mux)
    .regcsr_o (),
    .regjtag_i(imc_bist_bira2hw),
    .regjtag_o(imc_bist_hw2bira),

    // <-> GEN
    .start_po(imc_bist_start_p),
    .resume_po(imc_bist_resume_p),
    .stop_po(imc_bist_stop_p),
    .bist_type_o(imc_bist_type),
    .busy_i(imc_bist_gen_busy),

    // <-> IMUX/IMUXC
    .bist_mode_o(imc_bist_mode),

    // <-> COLL
    .fault_det_i  (imc_bist_fault_det),
    .fault_valid_i(imc_bist_fault_valid),
    .fault_bank_i (imc_bist_fault_bank),
    .fault_col_i  (imc_bist_fault_col),
    .fault_cycle_i(imc_bist_fault_cycle),
    .fault_pop_o  (imc_bist_fault_pop)
  );

  axe_tcl_clk_gating i_bist_cg (
    .i_clk(i_clk),
    .i_en(imc_bist_mode),
    .i_test_en(scan_en),
    .o_clk(i_clk_bist_cg)
  );

  imc_bist_gen i_imc_bist_gen (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    // <-> CTL
    .start_pi(imc_bist_start_p),
    .resume_pi(imc_bist_resume_p),
    .stop_pi(imc_bist_stop_p),
    .bist_type_i(imc_bist_type),
    .busy_o(imc_bist_gen_busy),

    // <-> IMUX
    .write_enable_o(imc_bist_write_enable),
    .write_values_o(imc_bist_write_values),
    .write_row_o(imc_bist_write_row),
    .write_wss_o(imc_bist_write_wss),

    // <-> IMUXC
    .compute_enable_o(imc_bist_compute_enable),
    .compute_block_enable_o(imc_bist_compute_block_enable),
    .compute_gate_clock_o(imc_bist_compute_gate_clock),
    .compute_signed_weights_o(imc_bist_compute_signed_weights),
    .compute_inp_o(imc_bist_compute_inp),
    .compute_wss_o(imc_bist_compute_wss),

    // <-> COMP
    .expect_strobe_o(imc_bist_expect_strobe_gen),
    .expect_type_o  (imc_bist_expect_type_gen)
  );

  always_comb begin
    foreach (imc_bist_weight_pw[i])
      imc_bist_weight_pw[i] = (i >= 32) ? imc_bist_write_values[i-32] : imc_bist_write_values[i];
  end

  logic ultimate_last;
  logic ifd0_stream_last;
  logic ifd0_last_sticky_bit;
  logic ifd0_last;
  logic ifd0_valid_beat;
  logic ifd2_stream_last;
  logic ifd2_last_sticky_bit;
  logic ifd2_last;
  logic ifd2_valid_beat;
  logic adv_mode;

  always_comb adv_mode = (ifd0_serial_conversion_valid_i && ifd0_imc_acc_dp_cmd_tdata.adv_mode_en)
                      || (ifd2_serial_conversion_valid_i && ifd2_imc_acc_dp_cmd_tdata.adv_mode_en);

  always_comb ifd0_valid_beat = ifd0_serial_conversion_valid_i && !ifd0_imc_acc_stall_i;
  always_comb ifd2_valid_beat = ifd2_serial_conversion_valid_i && !ifd2_imc_acc_stall_i;

  always_comb ifd0_stream_last = ifd0_imc_acc_dp_cmd_tdata.out_dp_cmd_sig.tlast;
  always_comb ifd2_stream_last = ifd2_imc_acc_dp_cmd_tdata.out_dp_cmd_sig.tlast;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : seq_ifd0_sticky_last_proc
    if (!i_rst_n)                                                          ifd0_last_sticky_bit <= '0;
    else if (ultimate_last && ifd0_valid_beat)                             ifd0_last_sticky_bit <= '0;
    else if ((ifd0_stream_last ^ ifd0_last_sticky_bit) && ifd0_valid_beat) ifd0_last_sticky_bit <= '1;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin : seq_ifd2_sticky_last_proc
    if (!i_rst_n)                                                          ifd2_last_sticky_bit <= '0;
    else if (ultimate_last && ifd2_valid_beat)                             ifd2_last_sticky_bit <= '0;
    else if ((ifd2_stream_last ^ ifd2_last_sticky_bit) && ifd2_valid_beat) ifd2_last_sticky_bit <= '1;
  end

  always_comb ifd0_last = ifd0_last_sticky_bit || ifd0_stream_last;
  always_comb ifd2_last = ifd2_last_sticky_bit || ifd2_stream_last;

  always_comb ultimate_last = ifd0_last && (ifd2_last || !adv_mode);

  // Compute Bist_Mode mux
  assign imc_bist_compute_in = '{
          serial_input: imc_bist_compute_inp,
          weight_set: imc_bist_compute_wss,
          block_enable: {MVM_NB_IMC_BANKS{imc_bist_compute_block_enable}},
          block_valid: {MVM_NB_IMC_BANKS{|imc_bist_compute_block_enable}},
          acc_shift_pos: '0,  // Acc bypass: multiplier is 1
          acc_output_enable: '1,  // Acc bypass: allow output
          acc_clear: 1'b1,  // Acc bypass: force internal sum to 0
          acc_signed_weights: imc_bist_compute_signed_weights,
          acc_signed_inputs: 1'b0,  // Acc bypass: don't sign....?
          acc_weight_precision: 1'b0,
          acc_input_precision: 1'b0,
          tlast: 1'b0,
          bist_mode: 1'b1
      };

  block_valid_t ifd0_imc_compute_block_valid;

  always_comb foreach(ifd0_imc_compute_block_valid[index]) ifd0_imc_compute_block_valid[index] = |ifd0_imc_compute_block_enable[index];

  assign ifd0_imc_par2bser_compute_in = '{
          serial_input: ifd0_c_in_ser,
          weight_set: ifd0_imc_acc_dp_cmd_tdata.imc_cmd_sig.imc_compute_weight_set,
          block_enable: ifd0_imc_compute_block_enable,
          block_valid: ifd0_imc_compute_block_valid,
          acc_shift_pos: ifd0_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_shift_pos,
          acc_output_enable: ifd0_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_output_enable,
          acc_clear: ifd0_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_clear,
          acc_signed_inputs: csr_signed_inputs_i,
          acc_signed_weights: csr_signed_weights_i,
          acc_weight_precision: ifd0_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_weight_precision,
          acc_input_precision: ifd0_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_input_precision,
          tlast: ultimate_last,
          bist_mode: 1'b0
      };

  block_valid_t ifd2_imc_compute_block_valid;

  always_comb foreach(ifd2_imc_compute_block_valid[index]) ifd2_imc_compute_block_valid[index] = |ifd2_imc_compute_block_enable[index];

  always_comb ifd2_imc_par2bser_compute_in = '{
          serial_input: ifd2_c_in_ser,
          weight_set: ifd2_imc_acc_dp_cmd_tdata.imc_cmd_sig.imc_compute_weight_set,
          block_enable: ifd2_imc_compute_block_enable,
          block_valid: ifd2_imc_compute_block_valid,
          acc_shift_pos: ifd2_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_shift_pos,
          acc_output_enable: ifd2_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_output_enable,
          acc_clear: ifd2_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_clear,
          acc_signed_inputs: csr_signed_inputs_i,
          acc_signed_weights: csr_signed_weights_i,
          acc_weight_precision: ifd2_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_weight_precision,
          acc_input_precision: ifd2_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_input_precision,
          tlast: ultimate_last,
          bist_mode: 1'b0
      };

  assign imc_bank_compute_in = imc_bist_mode ? imc_bist_compute_in : ifd0_imc_par2bser_compute_in;

  // Weight Write Bist_Mode mux
  assign imc_bist_weight_in = '{
          w_weight_pw: imc_bist_weight_pw,
          w_set: imc_bist_write_wss,
          w_wen: {MVM_NB_IMC_BANKS{imc_bist_write_enable}},
          w_row: imc_bist_write_row,
          bist_mode: 1'b1
      };

  assign imc_ifd_weight_in = '{
          w_weight_pw: weight_pw_packed,
          w_set: prg_cmd_tdata.imc_prg_weight_set,
          w_wen: prg_bank_we,
          w_row: prg_cmd_tdata.imc_prg_row,
          bist_mode: 1'b0
      };

  assign imc_bank_weight_in = imc_bist_mode ? imc_bist_weight_in : imc_ifd_weight_in;

  assign imc_repair_in = '{
          mux_mode: imc_bisr_mux_mode,
          shift_en: imc_bisr_shift_en,
          ue: imc_bisr_ue,
          s: imc_bisr_si
      };

  assign imc_bisr_so = imc_repair_intf_piped[MVM_NB_IMC_BANKS/2-1].s;

`ifdef ASSERTIONS_ON
  // verilog_lint: waive-start line-length
  ap_no_collision_weight_in :
  assert property (@(posedge i_clk) disable iff (!i_rst_n) imc_bist_mode |-> ~prg_global_we)
  else $error("[%t] !ERROR! - MVM DATA LOSS: weight write attemped while IMC BIST is busy.", $time);

  ap_no_collision_compute_in :
  assert property (@(posedge i_clk) disable iff (!i_rst_n) imc_bist_mode |-> ~ifd0_serial_conversion_valid_i)
  else $error("[%t] !ERROR! - MVM DATA LOSS: compute attemped while IMC BIST is busy.", $time);
  // verilog_lint: waive-stop line-length
`endif  // ASSERTIONS_ON

  // verilog_lint: waive-start line-length
  for (genvar g = 0; unsigned'(g) < MVM_NB_IMC_BANKS / 2; g++) begin : g_imc_acc_pairs
    // Instantiation and interconnection of imc_acc_pairs
    // Their interconnection results in the following chain of imc_acc_pairs
    // 0 -> 2 -> 4 -> 6
    // ---------------|
    // ---------------v
    // 7 <- 5 <- 3 <- 1

    // IMC 0
    if (g == 0) begin : gen_imc_connect_0
      assign imc_compute_in_valid[g][0] = imc_bist_mode ? imc_bist_compute_enable : ifd0_serial_conversion_valid_i;
      assign imc_compute_in_stall[g][0] = imc_bist_mode ? 1'b0 : ifd0_imc_acc_stall_i;
      assign imc_compute_in[g][0] = imc_bank_compute_in;
      assign imc_compute_in_valid[g][1] = ifd2_serial_conversion_valid_i;
      assign imc_compute_in_stall[g][1] = ifd2_imc_acc_stall_i;
      assign imc_compute_in[g][1] = ifd2_imc_par2bser_compute_in;
      assign imc_weight_in_valid[g] = imc_bist_mode ? imc_bist_write_enable : prg_global_we;
      assign imc_weight_in[g] = imc_bank_weight_in;
      assign imc_repair_intf_in[g] = imc_repair_in;
      assign imc_pair_bist_mode[g] = imc_bist_mode;
      assign imc_bist_expect_strobe[g] = imc_bist_expect_strobe_gen;
      assign imc_bist_expect_type[g] = imc_bist_expect_type_gen;
      assign imc_bist_compare_bus[g] = '0;
    end
    // IMC 1
    else
    if (g == 1) begin : gen_imc_connect_1
      assign imc_compute_in_valid[g] = imc_compute_in_valid_piped[MVM_NB_IMC_BANKS/2-2];
      assign imc_compute_in_stall[g] = imc_compute_in_stall_piped[MVM_NB_IMC_BANKS/2-2];
      assign imc_compute_in[g] = imc_compute_in_piped[MVM_NB_IMC_BANKS/2-2];
      assign imc_weight_in_valid[g] = imc_weight_in_valid_piped[MVM_NB_IMC_BANKS/2-2];
      assign imc_weight_in[g] = imc_weight_in_piped[MVM_NB_IMC_BANKS/2-2];
      assign imc_repair_intf_in[g] = imc_repair_intf_piped[MVM_NB_IMC_BANKS/2-2];
      assign imc_pair_bist_mode[g] = imc_pair_bist_mode_piped[MVM_NB_IMC_BANKS/2-2];
      assign imc_bist_expect_strobe[g] = imc_bist_expect_strobe_piped[MVM_NB_IMC_BANKS/2-2];
      assign imc_bist_expect_type[g] = imc_bist_expect_type_piped[MVM_NB_IMC_BANKS/2-2];
      assign imc_bist_compare_bus[g] = imc_bist_compare_bus_piped[MVM_NB_IMC_BANKS/2-2];
    end
    // Others
    else
    begin : gen_imc_connect
      assign imc_compute_in_valid[g] = imc_compute_in_valid_piped[g-2];
      assign imc_compute_in_stall[g] = imc_compute_in_stall_piped[g-2];
      assign imc_compute_in[g] = imc_compute_in_piped[g-2];
      assign imc_weight_in_valid[g] = imc_weight_in_valid_piped[g-2];
      assign imc_weight_in[g] = imc_weight_in_piped[g-2];
      assign imc_repair_intf_in[g] = imc_repair_intf_piped[g-2];
      assign imc_pair_bist_mode[g] = imc_pair_bist_mode_piped[g-2];
      assign imc_bist_expect_strobe[g] = imc_bist_expect_strobe_piped[g-2];
      assign imc_bist_expect_type[g] = imc_bist_expect_type_piped[g-2];
      assign imc_bist_compare_bus[g] = imc_bist_compare_bus_piped[g-2];
    end
    // verilog_lint: waive-stop line-length

    // PairId equals lowest BANK_ID number in pair
    localparam int unsigned PairId = g * 2 - g % 2;

    // IMC ACC PAIR instantiation, contains 2 imc_bank_accs with a
    // pipeline between their in and out compute signals
    mvm_imc_acc_pair #(
      .IMC_PAIR_ID(PairId)
    ) inst_mvm_imc_acc_pair (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),

      // Repair interface
      .i_repair_intf(imc_repair_intf_in[g]),
      .o_repair_intf(imc_repair_intf_piped[g]),

      // Weight write signals in
      .weight_in_valid_i(imc_weight_in_valid[g]),
      .weight_in_data_i (imc_weight_in[g]),
      // Weight write signals out piped
      .weight_in_valid_o(imc_weight_in_valid_piped[g]),
      .weight_in_data_o (imc_weight_in_piped[g]),

      // Compute signals in
      .compute_in_valid_i(imc_compute_in_valid[g]),
      .compute_in_stall_i(imc_compute_in_stall[g]),
      .compute_in_data_i (imc_compute_in[g]),
      // Compute signals out pipelined
      .compute_in_valid_o(imc_compute_in_valid_piped[g]),
      .compute_in_stall_o(imc_compute_in_stall_piped[g]),
      .compute_in_data_o (imc_compute_in_piped[g]),

      // Compute results out
      .compute_out_o      (imc_compute_outputs[g]),
      .compute_out_valid_o(imc_compute_output_valids[g]),
      .compute_out_ctrl_o (imc_compute_output_ctrls[g]),

      // IMC static settings
      .csr_power_smooth_dummy_ops_i(csr_power_smooth_dummy_ops_i),
      .csr_disable_imc_acc_clock_gating_i(csr_disable_imc_acc_clock_gating_i),
      .test_mode_i(test_mode_i),
      .scan_en(scan_en),

      // IMC status signals
      .err_concurrent_exe_prg_on_ws_o(err_concurrent_exe_prg_on_ws_all_banks[g]),

      // IMC BIST inputs
      .i_imc_bist_mode         (imc_pair_bist_mode[g]),
      .o_imc_bist_mode         (imc_pair_bist_mode_piped[g]),
      .imc_bist_expect_strobe_i(imc_bist_expect_strobe[g]),
      .imc_bist_expect_type_i  (imc_bist_expect_type[g]),
      .imc_bist_compare_bus_i  (imc_bist_compare_bus[g]),

      // IMC BIST outputs
      .imc_bist_expect_strobe_o(imc_bist_expect_strobe_piped[g]),
      .imc_bist_expect_type_o  (imc_bist_expect_type_piped[g]),
      .imc_bist_compare_bus_o  (imc_bist_compare_bus_piped[g])
    );
    // Assertions
    //synopsys translate_off
`ifdef ASSERTIONS_ON
    // verilog_lint: waive-start line-length
    // n-hot encoding of (comptue) active banks
    assign active_banks[g*2] = inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_valid
                             | inst_mvm_imc_acc_pair.inst_imc_bank_acc_a.inst_imc_w_acc.compute_power_dummy;
    assign active_banks[g*2+1] = inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_valid
                               | inst_mvm_imc_acc_pair.inst_imc_bank_acc_b.inst_imc_w_acc.compute_power_dummy;
    // verilog_lint: waive-stop line-length
`endif  //ASSERTIONS_ON
    //synopsys translate_on
  end

  // verilog_lint: waive-start line-length
  imc_bist_coll i_imc_bist_coll (
    .i_clk  (i_clk_bist_cg),
    .i_rst_n(i_rst_n),

    // <-> CTL
    .bist_mode_i(imc_bist_mode),
    .start_pi(imc_bist_start_p),
    .resume_pi(imc_bist_resume_p),
    .stop_pi(imc_bist_stop_p),

    // <-> COMPs
    .compare_bus_strobe_i(imc_bist_expect_strobe_piped[imc_bist_pkg::NUM_COMPARATORS-1]),
    .compare_bus_i(imc_bist_compare_bus_piped[imc_bist_pkg::NUM_COMPARATORS-1]),

    // <-> CTL
    .fault_det_o  (imc_bist_fault_det),
    .fault_valid_o(imc_bist_fault_valid),
    .fault_bank_o (imc_bist_fault_bank),
    .fault_col_o  (imc_bist_fault_col),
    .fault_cycle_o(imc_bist_fault_cycle),
    .fault_pop_i  (imc_bist_fault_pop)
  );

  // Distributed output muxing (second level, first level of muxing takes place inside the imc_acc_pairs)
  // Mux the output values of all imc_acc pairs.
  // For the even pairs this scheme applies
  //     0 -----> 2 -----> 4 -----> 6 (imc_acc_pairs)
  //     |        |        |        | (imc_acc_pair outputs)
  //<--mux0<-----mux2<-----mux4<----| (muxing)
  for (
      genvar g = 0; unsigned'(g) < (MVM_NB_IMC_BANKS / 2) - 2; g = g + 2
  ) begin : gen_imc_acc_left_pair_muxes
    // MUX4, this one takes two pairs as inputs
    if (g == (MVM_NB_IMC_BANKS / 2) - 4) begin : gen_mux
      mvm_dist_mux #(
        .OR_DATA(1), // This is a mux that gets inputs from mvm_imc_acc_pairs. Inside these pairs, it is already ensured that only when valid is 1, data is non-zero. Hence we can just use an OR-gate to mux the outputs from different pairs.
        .IN1_PIPELINE_EN(GLOBAL_MUX_PIPELINE_EN[g])
      ) inst_dist_mux (
        .i_clk,
        .i_rst_n,
        .in_0(imc_compute_outputs[g]),
        .in_0_ctrl(imc_compute_output_ctrls[g]),
        .in_0_valid(imc_compute_output_valids[g]),
        .in_1(imc_compute_outputs[g+2]),
        .in_1_ctrl(imc_compute_output_ctrls[g+2]),
        .in_1_valid(imc_compute_output_valids[g+2]),
        .out_data(imc_compute_outs_muxed[g]),
        .out_ctrl(imc_compute_out_ctrls_muxed[g]),
        .out_valid(imc_compute_out_valids_muxed[g])
      );

      //synopsys translate_off
`ifdef ASSERTIONS_ON
      // Check that only one of the inputs to the mux is valid
      property dual_valid;
        @(posedge i_clk) disable iff (!i_rst_n || imc_bist_mode) not (inst_dist_mux.in_0_valid && inst_dist_mux.int_in1_valid);
      endproperty

      property data_gated;
        @(posedge i_clk) disable iff (!i_rst_n || imc_bist_mode) (inst_dist_mux.in_0 === '0 || inst_dist_mux.int_in1_data === '0);
      endproperty

      initial begin
        $assertoff(0, dist_mux_dual_valid);
        $assertoff(0, dist_mux_data_gated);
        @(negedge i_rst_n);
        $display("Enabling assertions for mvm_imc_acc_right_pair_muxes after reset");
        $asserton(0, dist_mux_dual_valid);
        $asserton(0, dist_mux_data_gated);
      end

      dist_mux_dual_valid :
      assert property (dual_valid)
      else $error("Both valid inputs of a distributed mux, this is not allowed!");

      dist_mux_data_gated :
      assert property (data_gated)
      else
        $error(
            "Dist mux with OR_DATA set true requires one of both inputs to be '0, this is violated here");
`endif
      //synopsys translate_on
      // MUX0/2, they take one pair as input and the output of a mux
    end else begin : gen_mux
      mvm_dist_mux #(
        .OR_DATA(1), // This is a mux that gets inputs from mvm_imc_acc_pairs. Inside these pairs, it is already ensured that only when valid is 1, data is non-zero. Hence we can just use an OR-gate to mux the outputs from different pairs.
        .IN1_PIPELINE_EN(GLOBAL_MUX_PIPELINE_EN[g])
      ) inst_dist_mux (
        .i_clk,
        .i_rst_n,
        .in_0(imc_compute_outputs[g]),
        .in_0_ctrl(imc_compute_output_ctrls[g]),
        .in_0_valid(imc_compute_output_valids[g]),
        .in_1(imc_compute_outs_muxed[g+2]),
        .in_1_ctrl(imc_compute_out_ctrls_muxed[g+2]),
        .in_1_valid(imc_compute_out_valids_muxed[g+2]),
        .out_data(imc_compute_outs_muxed[g]),
        .out_ctrl(imc_compute_out_ctrls_muxed[g]),
        .out_valid(imc_compute_out_valids_muxed[g])
      );
      //synopsys translate_off
`ifdef ASSERTIONS_ON
      // Check that only one of the inputs to the mux is valid
      property dual_valid;
        @(posedge i_clk) disable iff (!i_rst_n || imc_bist_mode) not (inst_dist_mux.in_0_valid && inst_dist_mux.int_in1_valid);
      endproperty

      property data_gated;
        @(posedge i_clk) disable iff (!i_rst_n || imc_bist_mode) (inst_dist_mux.in_0 === '0 || inst_dist_mux.int_in1_data === '0);
      endproperty

      initial begin
        $assertoff(0, dist_mux_dual_valid);
        $assertoff(0, dist_mux_data_gated);
        @(negedge i_rst_n);
        $display("Enabling assertions for mvm_imc_acc_right_pair_muxes after reset");
        $asserton(0, dist_mux_dual_valid);
        $asserton(0, dist_mux_data_gated);
      end

      dist_mux_dual_valid :
      assert property (dual_valid)
      else $error("Both valid inputs of a distributed mux, this is not allowed!");

      dist_mux_data_gated :
      assert property (data_gated)
      else
        $error(
            "Dist mux with OR_DATA set true requires one of both inputs to be '0, this is violated here");
`endif
      //synopsys translate_on
    end
  end
  // For the odd pairs this scheme applies
  //     7 <----- 5 <----- 3 <----- 1 (imc_acc_pairs)
  //     |        |        |        | (imc_acc_pair outputs)
  //<--mux5<-----mux3<-----mux1<----| (muxing)
  for (genvar g = 1; g < (MVM_NB_IMC_BANKS / 2) - 2; g = g + 2) begin : gen_imc_acc_right_pair_muxes
    // MUX1, this one takes two pairs as inputs
    // Spyglass complains that the 'gen_mux' label is multiple times. This is correct and intended so BE can find these muxes easier
    if (g == 1) begin : gen_mux
      mvm_dist_mux #(
        .OR_DATA(1), // This is a mux that gets inputs from mvm_imc_acc_pairs. Inside these pairs, it is already ensured that only when valid is 1, data is non-zero. Hence we can just use an OR-gate to mux the outputs from different pairs.
        .IN1_PIPELINE_EN(GLOBAL_MUX_PIPELINE_EN[g])
      ) inst_dist_mux (
        .i_clk,
        .i_rst_n,
        .in_0(imc_compute_outputs[g]),
        .in_0_ctrl(imc_compute_output_ctrls[g]),
        .in_0_valid(imc_compute_output_valids[g]),
        .in_1(imc_compute_outputs[g+2]),
        .in_1_ctrl(imc_compute_output_ctrls[g+2]),
        .in_1_valid(imc_compute_output_valids[g+2]),
        .out_data(imc_compute_outs_muxed[g]),
        .out_ctrl(imc_compute_out_ctrls_muxed[g]),
        .out_valid(imc_compute_out_valids_muxed[g])
      );
      // MUX5/3, they take one pair as input and the output of a mux
      //synopsys translate_off
`ifdef ASSERTIONS_ON
      // Check that only one of the inputs to the mux is valid
      property dual_valid;
        @(posedge i_clk) disable iff (!i_rst_n || imc_bist_mode) not (inst_dist_mux.in_0_valid && inst_dist_mux.int_in1_valid);
      endproperty

      property data_gated;
        @(posedge i_clk) disable iff (!i_rst_n || imc_bist_mode) (inst_dist_mux.in_0 === '0 || inst_dist_mux.int_in1_data === '0);
      endproperty

      initial begin
        $assertoff(0, dist_mux_dual_valid);
        $assertoff(0, dist_mux_data_gated);
        @(negedge i_rst_n);
        $display("Enabling assertions for mvm_imc_acc_right_pair_muxes after reset");
        $asserton(0, dist_mux_dual_valid);
        $asserton(0, dist_mux_data_gated);
      end

      dist_mux_dual_valid :
      assert property (dual_valid)
      else $error("Both valid inputs of a distributed mux, this is not allowed!");

      dist_mux_data_gated :
      assert property (data_gated)
      else
        $error(
            "Dist mux with OR_DATA set true requires one of both inputs to be '0, this is violated here");
`endif
      //synopsys translate_on
    end else begin : gen_mux
      mvm_dist_mux #(
        .OR_DATA(1), // This is a mux that gets inputs from mvm_imc_acc_pairs. Inside these pairs, it is already ensured that only when valid is 1, data is non-zero. Hence we can just use an OR-gate to mux the outputs from different pairs.
        .IN1_PIPELINE_EN(GLOBAL_MUX_PIPELINE_EN[g])
      ) inst_dist_mux (
        .i_clk,
        .i_rst_n,
        .in_0(imc_compute_outputs[g+2]),
        .in_0_ctrl(imc_compute_output_ctrls[g+2]),
        .in_0_valid(imc_compute_output_valids[g+2]),
        .in_1(imc_compute_outs_muxed[g-2]),
        .in_1_ctrl(imc_compute_out_ctrls_muxed[g-2]),
        .in_1_valid(imc_compute_out_valids_muxed[g-2]),
        .out_data(imc_compute_outs_muxed[g]),
        .out_ctrl(imc_compute_out_ctrls_muxed[g]),
        .out_valid(imc_compute_out_valids_muxed[g])
      );
      //synopsys translate_off
`ifdef ASSERTIONS_ON
      // Check that only one of the inputs to the mux is valid
      property dual_valid;
        @(posedge i_clk) disable iff (!i_rst_n || imc_bist_mode) not (inst_dist_mux.in_0_valid && inst_dist_mux.int_in1_valid);
      endproperty

      property data_gated;
        @(posedge i_clk) disable iff (!i_rst_n || imc_bist_mode) (inst_dist_mux.in_0 === '0 || inst_dist_mux.int_in1_data === '0);
      endproperty

      initial begin
        $assertoff(0, dist_mux_dual_valid);
        $assertoff(0, dist_mux_data_gated);
        @(negedge i_rst_n);
        $display("Enabling assertions for mvm_imc_acc_right_pair_muxes after reset");
        $asserton(0, dist_mux_dual_valid);
        $asserton(0, dist_mux_data_gated);
      end

      dist_mux_dual_valid :
      assert property (dual_valid)
      else $error("Both valid inputs of a distributed mux, this is not allowed!");

      dist_mux_data_gated :
      assert property (data_gated)
      else
        $error(
            "Dist mux with OR_DATA set true requires one of both inputs to be '0, this is violated here");
`endif
      //synopsys translate_on
    end
  end

  assign compute_output_32 = imc_compute_outs_muxed[0];
  assign compute_output_64 = imc_compute_outs_muxed[MVM_NB_IMC_BANKS/2-3];
  assign compute_output_32_valid = imc_compute_out_valids_muxed[0] & (~imc_bist_mode);
  assign compute_output_64_valid = imc_compute_out_valids_muxed[MVM_NB_IMC_BANKS/2-3] & (~imc_bist_mode);
  assign compute_output_32_ctrl = imc_compute_out_ctrls_muxed[0];
  assign compute_output_64_ctrl = imc_compute_out_ctrls_muxed[MVM_NB_IMC_BANKS/2-3];

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON

  logic signed [$clog2(MVM_NB_IMC_BANKS)+1:0] nb_active_banks;
  logic signed [1:0] power_smooth_setting;
  logic has_been_rsted = 0;
  always @(negedge i_rst_n) has_been_rsted = 1;
  assign power_smooth_setting = csr_power_smooth_dummy_ops_i ? 1 : 0;
  assign nb_active_banks = $countones(active_banks);
  property imc_banks_ramp;
    @(posedge i_clk) disable iff (!i_rst_n || test_mode_i || !has_been_rsted) ##1 ((nb_active_banks <= $past(
        nb_active_banks
    ) + 2 - power_smooth_setting) && (nb_active_banks >= $past(
        nb_active_banks
    ) - 2 + power_smooth_setting));
  endproperty

  imc_banks_ramp_assertion :
  assert property (imc_banks_ramp)
  else $error("More than one imc_banks activated or deactivated in a single cycle!");
`endif  // ASSERTIONS_ON
  //synopsys translate_on
  // verilog_lint: waive-stop line-length
endmodule

`endif  // MVM_IMC_ACC_SV
