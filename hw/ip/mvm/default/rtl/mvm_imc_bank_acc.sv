// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Combination of one imc bank with IMC_NB_COLS_PER_BANK serial accumulator instances.
// Having this hierarchical makes for better/easier placement of accs close to the correct imc bank
// Owner: roel uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_IMC_BANK_ACC_SV
`define MVM_IMC_BANK_ACC_SV

module mvm_imc_bank_acc
  import imc_bank_pkg::*;
  import mvm_pkg::*;
  import imc_bist_pkg::*;
#(
  parameter int unsigned IMC_BANK_ID = 0
) (
  input wire i_clk,
  input wire i_rst_n,

  input  imc_repair_struct_t i_repair_intf,
  output imc_repair_struct_t o_repair_intf,

  input logic weight_in_valid_i,
  input imc_weight_struct_t weight_in_data_i,

  // IMC compute signals
  input logic [1:0] compute_in_valid_i,
  input logic [1:0] compute_in_stall_i,
  input imc_compute_struct_t [1:0] compute_in_data_i,

  output logic compute_out_valid_o,
  output compute_out_ctrl_t compute_out_ctrl_o,
  // output vectors of all columns from all blocks
  output logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] compute_out_o,

  // IMC static settings
  input logic csr_disable_imc_acc_clock_gating_i,
  input logic csr_power_smooth_dummy_ops_i,
  input logic test_mode_i,
  input logic scan_en,

  // IMC errors
  output logic err_concurrent_exe_prg_on_ws_o
);

  // Unconnected OK: bist_mode is only used at mvm_imc_acc_pair level
  logic unconnected_ok_bist_mode;

  logic [IMC_NB_COLS_PER_BANK-1:0] [DATA_W-1:0] w_vec_in;
  logic [$clog2(IMC_NB_WEIGHT_SETS)-1:0] w_set;
  logic w_wen;
  logic [$clog2(IMC_NB_ROWS)-1:0] w_row;

  logic r_repair_intf_shift_en;

  // If the imc clock is on for this bank, either one or
  // more exe ops are flowing through its pipeline, or a prg op takes place
  logic repair_clock_enable;
  logic imc_clock_enable;
  logic compute_valid_acc_in, compute_valid_acc_out;

  logic compute_valid;
  logic compute_power_dummy;
  logic compute_last;

  logic [IMC_NB_COLS_PER_BANK-1:0] [MVM_IMC_OUT_DATA_W-1:0] c_out_imc;
  logic [IMC_NB_COLS_PER_BANK-1:0] [MVM_IMC_OUT_DATA_W-1:0] c_out_imc_pipe;

  logic [IMC_NB_ROWS/IMC_BLOCK_GATING_GRANULARITY-1:0]
      c_be_test_mode, c_be_power_dummy, c_be_imc_bank;

  // Accumulator control signal pipeline. Signals that are still
  // required after the accumulator get an pipeline stage to
  // account for the accumulator's delay cycle
  // IMC_NB_DELAY_CYCLES +1 (for imc pipeline) +1 (for accumulator reg)
  // deep as we need these signals after the accumulator
  logic [IMC_NB_DELAY_CYCLES+1:0] compute_valid_pipe_q, compute_valid_pipe_next;
  logic [IMC_NB_DELAY_CYCLES+1:0] acc_output_enable_next, acc_output_enable_q;
  logic [IMC_NB_DELAY_CYCLES+1:0] acc_last_next, acc_last_q;
  logic [IMC_NB_DELAY_CYCLES+1:0] acc_weight_precision_next, acc_weight_precision_q;
  logic [IMC_NB_DELAY_CYCLES+1:0] acc_input_precision_next, acc_input_precision_q;
  logic [IMC_NB_DELAY_CYCLES:0] compute_power_dummy_pipe_next, compute_power_dummy_q;

  // Only IMC_NB_DELAY_CYCLES +1 (for imc pipeline) deep as these signals
  // are no longer needed after the accumulator
  logic [IMC_NB_DELAY_CYCLES:0][$clog2(MAX_INPUT_DATA_W)-1:0] acc_shift_pos_next;
  logic [IMC_NB_DELAY_CYCLES:0][$clog2(MAX_INPUT_DATA_W)-1:0] acc_shift_pos_q;
  logic [IMC_NB_DELAY_CYCLES:0] acc_clear_next, acc_clear_q;
  logic [IMC_NB_DELAY_CYCLES:0] acc_signed_weights_next, acc_signed_weights_q;
  logic [IMC_NB_DELAY_CYCLES:0] acc_signed_inputs_next, acc_signed_inputs_q;

  // Input mux between data streams
  logic                int_compute_in_valid;
  logic                int_compute_in_stall;
  imc_compute_struct_t int_compute_in_data;
  block_enable_t       group_block_enable;
  logic          [1:0] input_stream_valid;
  logic                input_stream_select_d;
  logic                input_stream_select_q;

  logic [3:0] off_reset_detect;
  logic       off_reset_pulse;

  assign c_be_test_mode = {(IMC_NB_ROWS / IMC_BLOCK_GATING_GRANULARITY) {!test_mode_i}};
  assign c_be_power_dummy = {(IMC_NB_ROWS / IMC_BLOCK_GATING_GRANULARITY) {compute_power_dummy}};
  assign c_be_imc_bank = (int_compute_in_data.block_enable[IMC_BANK_ID] | c_be_power_dummy)
                         & c_be_test_mode;
  // Selecting the input stream
  always_comb foreach(input_stream_valid[i])
    input_stream_valid[i] = compute_in_valid_i[i] & compute_in_data_i[i].block_valid[IMC_BANK_ID];

  always_comb begin : select_input_stream_comb_proc
    unique case (input_stream_valid)
    2'b01  : input_stream_select_d = 1'b0;
    2'b10  : input_stream_select_d = 1'b1;
    default: input_stream_select_d = input_stream_select_q;
    endcase
  end

  always_ff @(posedge i_clk or negedge i_rst_n) begin : keep_input_stream_selection_seq_proc
    if      (!i_rst_n)                                      input_stream_select_q <= 1'b0;
    else if (input_stream_select_d ^ input_stream_select_q) input_stream_select_q <= input_stream_select_d;
  end

  always_comb int_compute_in_valid = input_stream_select_d ? compute_in_valid_i[1] : compute_in_valid_i[0];
  // MVM stall depends on output ready of MVM, if output drainer is not ready, both streams will be stall
  always_comb int_compute_in_stall = input_stream_select_d ? compute_in_stall_i[1] : compute_in_stall_i[0];
  always_comb int_compute_in_data  = input_stream_select_d ? compute_in_data_i[1]  : compute_in_data_i[0];

  always_comb group_block_enable = compute_in_data_i[1].block_enable | compute_in_data_i[0].block_enable;

  assign unconnected_ok_bist_mode = &{weight_in_data_i.bist_mode, int_compute_in_data.bist_mode};

  // Delay line to compensate for internal IMC bank delay
  always_comb begin
    compute_valid = 1'b0;
    compute_power_dummy = 1'b0;
    compute_last = 1'b0;
    if (int_compute_in_valid) begin
      // The current IMC column is only active when it has at least one block that is enabled
      compute_valid = int_compute_in_data.block_valid[IMC_BANK_ID];
      // Even when not valid we need to do a dummy compute for power smoothing
      // reasons if this non active bank is followed by any active banks further down the line
      if ((!compute_valid) && csr_power_smooth_dummy_ops_i) begin
        // For even banks we look for the first bank that does a computation,
        // from there on out we need the power dummy
        if (IMC_BANK_ID % 2 == 0) begin
          for (int i = 0; i < IMC_BANK_ID; i = i + 2) begin
            if (|int_compute_in_data.block_enable[i]) compute_power_dummy = 1'b1;
          end
        end
        // For the odd banks we look for the last bank that does a computation,
        // from there on out we no longer need the power dummy
        else
        begin
          for (int i = IMC_BANK_ID + 2; i < MVM_NB_IMC_BANKS; i = i + 2) begin
            if (|int_compute_in_data.block_enable[i]) compute_power_dummy = 1'b1;
          end
        end
      end
      // The current IMC column is the last column if no columns beyond
      // it have an active block (and ofc if the tlast is set for the current op)
      if (int_compute_in_data.tlast && compute_valid) begin
        compute_last = 1'b1;
        for (int i = IMC_BANK_ID + 2; i < MVM_NB_IMC_BANKS; i = i + 2) begin
          if (|group_block_enable[i]) compute_last = 1'b0;
        end
      end
    end

    compute_valid_pipe_next = {compute_valid_pipe_q[IMC_NB_DELAY_CYCLES:0], compute_valid};
    acc_output_enable_next = {
      acc_output_enable_q[IMC_NB_DELAY_CYCLES:0], int_compute_in_data.acc_output_enable[IMC_BANK_ID]
    };
    acc_last_next = {acc_last_q[IMC_NB_DELAY_CYCLES:0], compute_last};

    compute_power_dummy_pipe_next = {
      compute_power_dummy_q[IMC_NB_DELAY_CYCLES-1:0], compute_power_dummy
    };
    acc_clear_next = {acc_clear_q[IMC_NB_DELAY_CYCLES-1:0], int_compute_in_data.acc_clear};
    acc_signed_weights_next = {
      acc_signed_weights_q[IMC_NB_DELAY_CYCLES-1:0], int_compute_in_data.acc_signed_weights
    };
    acc_signed_inputs_next = {
      acc_signed_inputs_q[IMC_NB_DELAY_CYCLES-1:0], int_compute_in_data.acc_signed_inputs
    };
    acc_weight_precision_next = {
      acc_weight_precision_q[IMC_NB_DELAY_CYCLES:0], int_compute_in_data.acc_weight_precision
    };
    acc_input_precision_next = {
      acc_input_precision_q[IMC_NB_DELAY_CYCLES:0], int_compute_in_data.acc_input_precision
    };
    acc_shift_pos_next[0] = int_compute_in_data.acc_shift_pos;
    for (int i = 1; i < IMC_NB_DELAY_CYCLES + 1; i++) begin
      acc_shift_pos_next[i] = acc_shift_pos_q[i-1];
    end
  end

  // Valid pipelining, needs reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin : compute_valid_pipe_ff
    if (!i_rst_n) begin
      compute_valid_pipe_q  <= 0;
      compute_power_dummy_q <= 0;
    end else if (!int_compute_in_stall) begin
      compute_valid_pipe_q  <= compute_valid_pipe_next;
      compute_power_dummy_q <= compute_power_dummy_pipe_next;
    end
  end

  // Ctrl values pipelining, does not need reset
  always_ff @(posedge i_clk) begin : acc_ctrl_pipe_ff
    if (!int_compute_in_stall) begin
      acc_shift_pos_q <= acc_shift_pos_next;
      acc_output_enable_q <= acc_output_enable_next;
      acc_clear_q <= acc_clear_next;
      acc_signed_weights_q <= acc_signed_weights_next;
      acc_signed_inputs_q <= acc_signed_inputs_next;
      acc_input_precision_q <= acc_input_precision_next;
      acc_weight_precision_q <= acc_weight_precision_next;
      acc_last_q <= acc_last_next;
    end
  end

  assign {>>{w_vec_in}} =
    weight_in_data_i.w_weight_pw[(IMC_BANK_ID%2)*IMC_NB_COLS_PER_BANK+:IMC_NB_COLS_PER_BANK];
  assign w_set = weight_in_data_i.w_set;
  assign w_wen = weight_in_valid_i & weight_in_data_i.w_wen[IMC_BANK_ID];
  assign w_row = weight_in_data_i.w_row;

  // Ungate the clock when new repair settings are generated by BIRA controller
  always_ff @(posedge i_clk, negedge i_rst_n)
    if(!i_rst_n) r_repair_intf_shift_en <= '0;
    else if(i_repair_intf.shift_en ^ r_repair_intf_shift_en)
      r_repair_intf_shift_en <= i_repair_intf.shift_en;

  // Ungate the clock for 3 cycles off-reset to apply repair settings on power-on repair
  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n) off_reset_detect <= 4'b0000;
    else if(~&off_reset_detect) off_reset_detect <= {off_reset_detect[2:0], 1'b1};

  wire i_clkmc_g;
  logic compute_valid_in_imc, compute_power_dummy_in_imc,
        compute_active_in_imc, compute_gate_clock;
  // If any compute in the pipe, compute_valid should be set
  assign compute_valid_in_imc = |compute_valid_pipe_next[IMC_NB_DELAY_CYCLES:0];
  assign compute_power_dummy_in_imc = |compute_power_dummy_pipe_next;
  // Make the compute active when compute is valid or when we need to run a dummy cycle
  // and we do not have to stall the bank
  assign compute_active_in_imc = (compute_valid_in_imc | compute_power_dummy_in_imc)
                                 & !int_compute_in_stall;
  // IMC compute clock should be on if there is at least one valid transaction
  // in its internal pipeline while we are not in a stall situation
  assign compute_gate_clock = !compute_active_in_imc;
  // IMC clock should be on if compute_clock is on or when we want to store weights.
  // (Note that internally in the IMC macro, compute_gate_clock can still gate computing
  // when writing is active)
  assign repair_clock_enable = i_repair_intf.shift_en | r_repair_intf_shift_en | (~off_reset_detect[3] & off_reset_detect[0]);
  assign imc_clock_enable = compute_active_in_imc | w_wen | repair_clock_enable;
  axe_tcl_clk_gating imc_clk_gate (
    .i_test_en(test_mode_i), // <-- Connection to test_mode is intentional, needed to guarantee isolation
    .i_clk(i_clk),
    .i_en(imc_clock_enable | csr_disable_imc_acc_clock_gating_i),
    .o_clk(i_clkmc_g)
  );

  // Flag error when we write and compute on the same weight set
  assign err_concurrent_exe_prg_on_ws_o = w_wen & compute_valid_in_imc
                                        & (int_compute_in_data.weight_set == w_set);

  mvm_imc_bank_combiner u_mvm_imc_bank_combiner (
    .i_clk                   (i_clkmc_g),
    .i_rst_n                 (i_rst_n),
    .i_imc_bisr_mux_mode     (i_repair_intf.mux_mode),
    .i_imc_bisr_shift_en     (i_repair_intf.shift_en),
    .i_imc_bisr_ue           (i_repair_intf.ue),
    .i_imc_bisr_si           (i_repair_intf.s),
    .o_imc_bisr_mux_mode     (o_repair_intf.mux_mode),
    .o_imc_bisr_shift_en     (o_repair_intf.shift_en),
    .o_imc_bisr_ue           (o_repair_intf.ue),
    .o_imc_bisr_so           (o_repair_intf.s),
    .i_write_enable          (w_wen & !test_mode_i),
    .i_write_row             (w_row),
    .i_write_wss             (w_set),
    .i_write_values          (w_vec_in),
    .i_compute_enable        (!(compute_gate_clock & !test_mode_i)),
    .i_compute_inp           (int_compute_in_data.serial_input),
    .i_compute_wss           (int_compute_in_data.weight_set),
    .i_compute_block_enable  (c_be_imc_bank),
    .i_compute_weight_format ({int_compute_in_data.acc_signed_weights, 1'b0}),
    .o_compute_out           (c_out_imc)
  );

  // Pipelining on imc_out and valid signaling for accumulators (does not need reset)
  always_ff @(posedge i_clk) begin : imc_bank_output_pipeline
    // Only clock in valid output results
    if (compute_valid_pipe_q[IMC_NB_DELAY_CYCLES-1] && !int_compute_in_stall) begin
      c_out_imc_pipe <= c_out_imc;
    end
  end

  assign compute_valid_acc_in  = compute_valid_pipe_q[IMC_NB_DELAY_CYCLES] & !int_compute_in_stall;
  assign compute_valid_acc_out = compute_valid_pipe_q[IMC_NB_DELAY_CYCLES+1] & !int_compute_in_stall;

  ///////////////
  // acc clock gate
  // Used to stall imc output pipe reg and acc when the output buffer cannot accept the result
  wire i_clk_acc_g;
  axe_tcl_clk_gating acc_clk_gate (
    .i_test_en(scan_en),
    .i_clk(i_clk),
    .i_en(compute_valid_acc_in | csr_disable_imc_acc_clock_gating_i),
    .o_clk(i_clk_acc_g)
  );

  // Internal acc valid signals
  assign compute_out_valid_o = compute_valid_acc_out & acc_output_enable_q[IMC_NB_DELAY_CYCLES+1];
  assign compute_out_ctrl_o.last  = compute_out_valid_o & acc_last_q[IMC_NB_DELAY_CYCLES+1];
  assign compute_out_ctrl_o.interleave_required = ~acc_weight_precision_q[IMC_NB_DELAY_CYCLES+1] & acc_input_precision_q[IMC_NB_DELAY_CYCLES+1];

  // Accumulators that belong to this imc_bank
  for (genvar g = 0; g < IMC_NB_COLS_PER_BANK/2; g++) begin : gen_combined_accumulators
    mvm_imc_bank_acc_combiner #(
      .IMC_DATA_WD(MVM_IMC_OUT_DATA_W),
      .ACC_DATA_WD(MVM_ACC_DATA_W),
      .COMB_DATA_WD(MVM_OUT_DATA_W)
    ) u_mvm_imc_bank_acc_combiner (
      .i_clk(i_clk_acc_g),
      .i_rst_n,

      .i_weight_precision(acc_weight_precision_q[IMC_NB_DELAY_CYCLES]),
      .i_input_precision(acc_input_precision_q[IMC_NB_DELAY_CYCLES]),

      .ctrl_acc_shift_pos_i(acc_shift_pos_q[IMC_NB_DELAY_CYCLES]),
      .ctrl_acc_group_enable_i(compute_valid_acc_in),
      .ctrl_acc_output_enable_i(acc_output_enable_q[IMC_NB_DELAY_CYCLES]),
      .ctrl_acc_clear_i(acc_clear_q[IMC_NB_DELAY_CYCLES]),
      .ctrl_acc_signed_weights(acc_signed_weights_q[IMC_NB_DELAY_CYCLES]), // Can this be tied to 1?
      .ctrl_acc_signed_inputs(acc_signed_inputs_q[IMC_NB_DELAY_CYCLES]),

      .i_imc_data(c_out_imc_pipe[g*2+:2]),
      .o_comb_data(compute_out_o[g*2+:2])
    );
  end

`ifndef SYNTHESIS
`ifdef ASSERTIONS_ON

  property test_mode_IMC_0_output(imc_output);
    @(posedge i_clk) test_mode_i |-> ##IMC_NB_DELAY_CYCLES(imc_output == 0);
  endproperty

  // verilog_lint: waive-start line-length
  for (genvar g = 0; unsigned'(g) < IMC_NB_COLS_PER_BANK; g++) begin : g_check_test_mode_isolates_imc_outputs
    check_test_mode_isolates_imc_outputs :
    assert property (test_mode_IMC_0_output(c_out_imc[g]))
    else $error("Output %2d is not a stable 0 when test_mode_i is active ", g);
  end
  // verilog_lint: waive-stop line-length

`endif
`endif

endmodule

`endif  // MVM_IMC_BANK_ACC_SV
