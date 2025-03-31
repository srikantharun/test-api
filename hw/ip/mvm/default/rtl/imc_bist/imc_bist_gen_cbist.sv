// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IMC CBIST pattern generator
// CBIST implements pseudo-random pattern generation for IMC bank
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef IMC_BIST_AIC_GEN_CBIST_SV
`define IMC_BIST_AIC_GEN_CBIST_SV

module imc_bist_gen_cbist
  import imc_bist_pkg::expect_type_e;
  import imc_bist_pkg::E_NEIGHBOR;
  import imc_bank_pkg::IMC_NB_ROWS;
  import imc_bank_pkg::IMC_NB_COLS_PER_BANK;
  import mvm_pkg::DATA_W;
  import imc_bank_pkg::IMC_ROW_PW;
  import imc_bank_pkg::IMC_WEIGHT_SET_PW;
  import imc_bank_pkg::IMC_BLOCK_ENABLE_W;
  import imc_bank_pkg::IMC_NB_DELAY_CYCLES;
(
  input wire i_clk,
  input wire i_rst_n,

  // <-> CTL
  input  logic start_pi,
  input  logic resume_pi,
  input  logic stop_pi,
  output logic busy_o,

  // <-> IMUX
  output logic write_enable_o,
  output logic [IMC_NB_COLS_PER_BANK-1:0][DATA_W-1:0] write_values_o,
  output logic [IMC_ROW_PW-1:0] write_row_o,
  output logic [IMC_WEIGHT_SET_PW-1:0] write_wss_o,

  // <-> IMUXC
  output logic compute_enable_o,
  output logic [IMC_BLOCK_ENABLE_W-1:0] compute_block_enable_o,
  output logic compute_gate_clock_o,
  output logic compute_signed_weights_o,
  output logic [IMC_NB_ROWS-1:0] compute_inp_o,
  output logic [IMC_WEIGHT_SET_PW-1:0] compute_wss_o,

  // <-> COMP
  output logic expect_strobe_o,
  output expect_type_e expect_type_o
);

  localparam int unsigned NCycles = 2 ** 15;  // 32K
  localparam int unsigned LfsrW = 16;
  localparam int unsigned NLfsr = IMC_NB_ROWS / LfsrW;
  localparam int unsigned VirtualAddrW = IMC_ROW_PW + IMC_WEIGHT_SET_PW;

  typedef enum logic [$clog2(3)-1:0] {
    E_IDLE = 'd0,
    E_WEIGHT_WRITE = 'd1,
    E_COMPUTE = 'd2
  } state_e;

  typedef struct packed {
    logic idle_from_invalid_state;
    logic weight_write_from_idle;
    logic weight_write_from_nonidle;
    logic compute_from_write_weights;
    logic weight_write_from_compute;
    logic idle_from_compute;
  } fsm_hint_t;

  typedef struct packed {logic [DATA_W-1:0] weight_values;} write_strategy_t;

  typedef struct packed {
    logic [15:0] and_mask;
    logic [15:0] or_mask;
  } compute_strategy_t;

  typedef struct packed {
    logic en;
    logic [DATA_W-1:0] weight_values;
    logic [IMC_ROW_PW-1:0] row;
    logic [IMC_WEIGHT_SET_PW-1:0] wss;
  } write_op_t;

  typedef struct packed {
    logic en;
    logic [IMC_BLOCK_ENABLE_W-1:0] block_en;
    logic [IMC_NB_ROWS-1:0] inp;
    logic signed_weights;
  } compute_op_t;

  typedef struct packed {
    write_op_t   write;
    compute_op_t compute;
  } imc_op_t;

  typedef struct packed {
    logic [IMC_WEIGHT_SET_PW-1:0] wss;
    logic [IMC_ROW_PW-1:0] row;
  } virtual_addr_s_t;

  typedef union packed {
    virtual_addr_s_t vaddr;
    logic [VirtualAddrW-1:0] raw;
  } virtual_addr_t;

  localparam int unsigned NIterationModes = 2;

  typedef enum logic [$clog2(NIterationModes)-1:0] {
    E_BASE_TEST = 'd0,
    E_EXTRA_RAND_TEST = 'd1
  } iteration_mode_e;

  /// --------------------------------------
  /// ----- TASK 0 : E_BASE_TEST -----------
  /// --------------------------------------
  localparam write_strategy_t WriteStrategyTask0 = '{weight_values: '1};
  localparam compute_strategy_t ComputeStrategyTask0 = '{and_mask: '1, or_mask: '1};

  /// --------------------------------------
  /// ----- TASK 1 : E_EXTRA_RAND_TEST -----
  /// --------------------------------------
  localparam write_strategy_t WriteStrategyTask1 = '{weight_values: '1};
  localparam compute_strategy_t ComputeStrategyTask1 = '{and_mask: '1, or_mask: '0};


  /// -----------------------
  /// ----- DESIGN ----------
  /// -----------------------

  // Global strategy
  iteration_mode_e r_cur_mode;
  logic clr_cur_mode, tgl_cur_mode;

  // FSM
  state_e s_state, r_state;
  fsm_hint_t s_fsm_hint;
  logic r_stopped, s_stopped, s_en;
  logic s_final_cycle;

  // Current strategy
  virtual_addr_t r_current_write_addr;
  write_strategy_t r_current_write_strategy;
  write_op_t s_write_op;

  logic [15:0] r_compute_cycle;
  compute_strategy_t r_current_compute_strategy;
  compute_op_t s_compute_op;

  imc_op_t s_imc_op;

  logic [$clog2(IMC_NB_DELAY_CYCLES+1)-1:0] s_cnt_clock_gating, r_cnt_clock_gating;

  /// -------------------------------------
  /// ----- FSM ---------------------------
  /// -------------------------------------
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_cur_mode <= E_BASE_TEST;
    else if (clr_cur_mode) r_cur_mode <= E_BASE_TEST;
    else if (tgl_cur_mode) r_cur_mode <= E_EXTRA_RAND_TEST;

  // Ensure mode is row-first whenever launching
  assign clr_cur_mode = s_fsm_hint.weight_write_from_idle;
  // Switch from row-first to set-first when first iteration of march-c finishes
  assign tgl_cur_mode = s_fsm_hint.weight_write_from_compute;

  // Calculate transition
  assign s_final_cycle = (r_compute_cycle == (NCycles + 1));
  assign s_fsm_hint.idle_from_invalid_state = ~(r_state inside {E_IDLE, E_WEIGHT_WRITE, E_COMPUTE});
  assign s_fsm_hint.weight_write_from_idle = (r_state == E_IDLE) & start_pi;
  assign s_fsm_hint.weight_write_from_nonidle = (r_state != E_IDLE) & start_pi;
  assign s_fsm_hint.compute_from_write_weights = (r_state == E_WEIGHT_WRITE)
                    & (r_current_write_addr.vaddr.row == (IMC_NB_ROWS-1))
                    & (r_current_write_addr.vaddr.wss == '1);
  assign s_fsm_hint.weight_write_from_compute =
                    (r_state == E_COMPUTE) & s_final_cycle & (r_cur_mode == E_BASE_TEST);
  assign s_fsm_hint.idle_from_compute = (r_state == E_COMPUTE)
                                      & s_final_cycle & (r_cur_mode != E_BASE_TEST);

  // Apply transitions
  always_comb begin : s_state_cproc
    s_state = r_state;
    if (s_fsm_hint.idle_from_invalid_state) s_state = E_IDLE;
    else if (s_fsm_hint.weight_write_from_idle) s_state = E_WEIGHT_WRITE;
    else if (s_fsm_hint.weight_write_from_nonidle) s_state = E_WEIGHT_WRITE;
    else if (s_fsm_hint.compute_from_write_weights) s_state = E_COMPUTE;
    else if (s_fsm_hint.weight_write_from_compute) s_state = E_WEIGHT_WRITE;
    else if (s_fsm_hint.idle_from_compute) s_state = E_IDLE;
  end : s_state_cproc

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_state <= E_IDLE;
    else if (s_en) r_state <= s_state;

  // If stopped, unstop at start_pi (or resume_pi), otherwise stop if stop_pi
  assign s_stopped = r_stopped ? ~(start_pi | resume_pi) : (stop_pi | (r_state == E_IDLE));

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_stopped <= 1'b1;
    else r_stopped <= s_stopped;

  // Evaluate s_stopped and r_stopped for loose leading/trailing enable
  assign s_en = ~(s_stopped & r_stopped);

  /// --------------------------------------
  /// ----- WEIGHT WRITE ROUTINE -----------
  /// --------------------------------------
  logic weight_write_en;
  assign weight_write_en = (r_state == E_WEIGHT_WRITE);

  /// Update the task strategy
  // Only supporting task0 but easily extendable...
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_current_write_strategy <= '0;
    else if (s_en & s_fsm_hint.weight_write_from_idle)
      r_current_write_strategy <= WriteStrategyTask0;
    else if (s_en & s_fsm_hint.weight_write_from_nonidle)
      r_current_write_strategy <= WriteStrategyTask0;
    else if (s_en & s_fsm_hint.weight_write_from_compute)
      r_current_write_strategy <= WriteStrategyTask1;

  /// Update the write pointer
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_current_write_addr.raw <= '0;
    else if (s_en & s_fsm_hint.weight_write_from_idle) r_current_write_addr.raw <= '0;
    else if (s_en & s_fsm_hint.weight_write_from_nonidle) r_current_write_addr.raw <= '0;
    else if (s_en & s_fsm_hint.weight_write_from_compute) r_current_write_addr.raw <= '0;
    else if (s_en & weight_write_en & r_current_write_addr.vaddr.row == (IMC_NB_ROWS-1))
      r_current_write_addr.vaddr <= '{wss: r_current_write_addr.vaddr.wss+1'b1, row: '0};
    else if (s_en & weight_write_en) r_current_write_addr.raw <= r_current_write_addr.raw + 1'b1;

  /// Decode write op
  assign s_write_op = '{
          en: weight_write_en,
          weight_values: r_current_write_strategy,
          row: r_current_write_addr.vaddr.row,
          wss: r_current_write_addr.vaddr.wss
      };

  /// --------------------------------------
  /// ----- COMPUTE ROUTINE ----------------
  /// --------------------------------------
  logic compute_en;
  logic lfsr_clr_en;
  logic lfsr_flip_en;
  logic lfsr_and_mask_en;
  logic lfsr_or_mask_en;
  logic compute_signed_weights;
  logic [IMC_NB_ROWS-1:0] compute_inp;
  logic [IMC_BLOCK_ENABLE_W-1:0] compute_block_en;

  logic [NIterationModes-1:0] compute_signed_weights_by_mode;
  logic [NIterationModes-1:0][IMC_BLOCK_ENABLE_W-1:0] compute_block_en_by_mode;

  logic [IMC_BLOCK_ENABLE_W-1:0] compute_block_en_by_mode_e_extra_rand_test;

  assign compute_signed_weights_by_mode[E_BASE_TEST] = r_compute_cycle[2];  // 0000111100001111...
  assign compute_block_en_by_mode[E_BASE_TEST] = {IMC_BLOCK_ENABLE_W{(r_state == E_COMPUTE)}};

  // Get signed_weights and block_en from LFSR data
  // The data is derived from the LFSR compute bus, the slice positions picked are entirely arbitrary
  assign compute_signed_weights_by_mode[E_EXTRA_RAND_TEST] =
    compute_inp[5] ^ compute_inp[21] ^ compute_inp[37] ^ compute_inp[53];
  always_comb begin
    foreach (compute_block_en_by_mode_e_extra_rand_test[i]) begin
      compute_block_en_by_mode_e_extra_rand_test[i] =
        compute_inp[i*16+2] ^ compute_inp[i*16+7] ^ compute_inp[i*16+14] ^ compute_inp[i*16+15];
    end
  end
  assign compute_block_en_by_mode[E_EXTRA_RAND_TEST] = compute_block_en_by_mode_e_extra_rand_test;

  assign compute_en = (r_state == E_COMPUTE);
  assign lfsr_clr_en = s_fsm_hint.compute_from_write_weights;
  assign lfsr_flip_en = ~r_compute_cycle[0];  // flip on even cycles
  assign compute_signed_weights = compute_signed_weights_by_mode[r_cur_mode];
  assign compute_block_en = compute_block_en_by_mode[r_cur_mode];
  // and-mask on even cycles except for the ones with or-mask
  assign lfsr_and_mask_en = ~r_compute_cycle[0] && ~(r_compute_cycle[4:0] == 5'b00000);
  // or-mask with slight jitter every ~16 cycles (15, 32, 47, 64, ...).
  // Jitter is to avoid coupling with signed_weights
  assign lfsr_or_mask_en = (r_compute_cycle[4:0] == 5'b01111 || r_compute_cycle[4:0] == 5'b00000);

  /// Update the task strategy
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_current_compute_strategy <= '0;
    else if (s_en & s_fsm_hint.compute_from_write_weights & (r_cur_mode == E_BASE_TEST))
      r_current_compute_strategy <= ComputeStrategyTask0;
    else if (s_en & s_fsm_hint.compute_from_write_weights & (r_cur_mode == E_EXTRA_RAND_TEST))
      r_current_compute_strategy <= ComputeStrategyTask1;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_compute_cycle <= '0;
    else if (s_en & s_fsm_hint.compute_from_write_weights) r_compute_cycle <= '0;
    else if (s_en & compute_en) r_compute_cycle <= r_compute_cycle + 1'b1;

  for (genvar lfsr_i = 0; lfsr_i < NLfsr; lfsr_i++) begin : gen_lfsr_16
    logic [15:0] data_o_vec;
    cc_cnt_lfsr #(
      .Width(16),
      .Seed (lfsr_i * 116 + 1)
    ) i_cc_cnt_lfsr_16 (
      .i_clk        (i_clk),
      .i_rst_n       (i_rst_n),
      .clear_i      (lfsr_clr_en),
      .enable_i     (s_en & compute_en),
      .taps_i       (cc_cnt_lfsr_pkg::AX_LFSR_TAPS_016),
      .state_o      (  /*open*/),
      .flip_enable_i(lfsr_flip_en),
      .mask_select_i({lfsr_or_mask_en, lfsr_and_mask_en}),
      .mask_and_i   (r_current_compute_strategy.and_mask),
      .mask_or_i    (r_current_compute_strategy.or_mask),
      .data_o       (data_o_vec)
    );
    logic [15:0] compute_inp_vec;
    assign compute_inp_vec[15] = (lfsr_i == (NLfsr-1) && (r_cur_mode == E_BASE_TEST)
                               && r_compute_cycle[4:0] == 5'b00000) ? 1'b0 : data_o_vec[15];
    assign compute_inp_vec[14:0] = data_o_vec[14:0];
    assign compute_inp[lfsr_i*LfsrW+:LfsrW] = compute_inp_vec;
  end

  assign s_compute_op = '{
          en: compute_en,
          block_en: compute_block_en,
          inp: compute_inp,
          signed_weights: compute_signed_weights
      };

  /// --------------------------------------
  /// ----- IMC OP -------------------------
  /// --------------------------------------
  assign s_imc_op = '{write: s_write_op, compute: s_compute_op};

  // Compute clock gating, ungate the compute when we are
  // computing and until bank is done computing
  // Last compute trailing counter
  always_comb begin : s_cnt_clock_gating_cproc
    if (s_imc_op.compute.en & (~r_stopped)) s_cnt_clock_gating = IMC_NB_DELAY_CYCLES;
    else if (|r_cnt_clock_gating) s_cnt_clock_gating = r_cnt_clock_gating - 1'b1;
    else s_cnt_clock_gating = '0;
  end

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_cnt_clock_gating <= '0;
    else r_cnt_clock_gating <= s_cnt_clock_gating;

  logic [IMC_BLOCK_ENABLE_W-1:0] compute_block_enable_mask;
  assign compute_block_enable_mask =
         {IMC_BLOCK_ENABLE_W{(~r_stopped & ~s_final_cycle & s_imc_op.compute.en)}};

  /// --------------------------------------
  /// ----- DRIVE OUTPUTS ------------------
  /// --------------------------------------
  // <-> CTL
  assign busy_o = (r_state != E_IDLE) & (~r_stopped);

  // <-> IMUX
  assign write_enable_o = (~r_stopped) & s_imc_op.write.en;
  always_comb foreach (write_values_o[i]) write_values_o[i] = s_imc_op.write.weight_values;
  assign write_row_o = s_imc_op.write.row;
  assign write_wss_o = s_imc_op.write.wss;

  // <-> IMUXC
  assign compute_enable_o = s_imc_op.compute.en;
  assign compute_block_enable_o = s_imc_op.compute.block_en & compute_block_enable_mask;
  assign compute_gate_clock_o = ~(s_imc_op.compute.en | (|r_cnt_clock_gating));
  assign compute_signed_weights_o = s_imc_op.compute.signed_weights;
  assign compute_inp_o = s_imc_op.compute.inp;
  // Weight set don't care, tested by MBIST
  assign compute_wss_o = s_imc_op.write.en ? ~s_imc_op.write.wss : '0;

  // <-> COMP
  assign expect_strobe_o = s_imc_op.compute.en & (~r_stopped);
  assign expect_type_o = E_NEIGHBOR;

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
`endif  // ASSERTIONS_ON
  //synopsys translate_on

endmodule
`endif  // IMC_BIST_AIC_GEN_CBIST_SV
