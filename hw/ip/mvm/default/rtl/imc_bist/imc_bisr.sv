// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   IMC self repair controller and datapath
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module imc_bisr
  import imc_bank_pkg::IMC_BANK_COL_PW;
  import mvm_pkg::MVM_IMC_BANK_PW;
  import mvm_pkg::MVM_NB_IMC_BANKS;
  import imc_bist_pkg::IMC_BIST_REPAIR_ATTEMPT_PW;
  import imc_bist_pkg::NUM_REPAIR_HOOKS;
  import imc_bist_pkg::NUM_REPAIR_HOOKS_PW;
  import imc_bist_pkg::compressed_repair_t;
  import imc_bist_pkg::uncompressed_repair_t;
(
  input  wire                                   i_clk,
  input  wire                                   i_rst_n,

  input  logic                                  i_clear,

  input  logic [IMC_BIST_REPAIR_ATTEMPT_PW-1:0] i_max_repair_attempts,

  input  logic      [1:0]                       i_imc_repair_req,
  input  logic      [1:0] [MVM_IMC_BANK_PW-1:0] i_imc_repair_bank,
  input  logic      [1:0] [IMC_BANK_COL_PW-1:0] i_imc_repair_col,
  output logic      [1:0]                       o_imc_repair_ack,
  output logic      [1:0]                       o_imc_repair_nack,

  output logic                                  o_imc_bisr_shift_en,
  output logic                                  o_imc_bisr_ue,
  output logic                                  o_imc_bisr_si,
  input  logic                                  i_imc_bisr_so
);

  localparam int unsigned N_SHIFT_CYCLES    = $bits(compressed_repair_t)*NUM_REPAIR_HOOKS;
  localparam int unsigned N_WAIT_CYCLES     = 32;
  localparam int unsigned N_SHIFT_CYCLES_PW = $clog2(N_SHIFT_CYCLES+N_WAIT_CYCLES);
  // Position 0 is the last bank to be shifted (bank 15)
  // bank  0: hooks 31,30
  // bank  2: hooks 29,28
  // ...
  // bank 14: hooks 17,16
  // bank 1 : hooks 15,14
  // bank 3 : hooks 13,12
  // ...
  // bank 15: hooks 1 ,0
  function automatic logic [NUM_REPAIR_HOOKS_PW-1:0] f_bankToLowHook(
    input logic [MVM_IMC_BANK_PW-1:0] i_bank
  );
    f_bankToLowHook = (NUM_REPAIR_HOOKS-2)/(i_bank[0]+1)-i_bank;
  endfunction

  function automatic logic [NUM_REPAIR_HOOKS_PW-1:0] f_bankColToHook(
    input logic [MVM_IMC_BANK_PW-1:0] i_bank,
    input logic [IMC_BANK_COL_PW-1:0] i_col
  );
    // Columns 31,...,16 mapped to high hook
    f_bankColToHook = f_bankToLowHook(i_bank) | {{(NUM_REPAIR_HOOKS_PW-1){1'b0}},i_col[IMC_BANK_COL_PW-1]};
  endfunction

  /// -----------------------
  /// ----- TYPES -----------
  /// -----------------------
  // FSM states
  typedef enum logic [1:0] {
    E_IDLE  = 'd0,
    E_APPLY = 'd1,
    E_SHIFT = 'd2
  } bisr_ctl_state_e_t;

  // Onehot FSM transition vector
  typedef struct packed {
    logic idle_from_invalid_state;
    logic apply_from_idle;
    logic idle_from_apply_max_attempts;
    logic idle_from_apply_already_repaired;
    logic shift_from_apply;
    logic idle_from_shift;
  } fsm_transition_t;

  typedef struct packed {
    logic capture_req;
    logic capture_shift;
    logic apply_repair;
    logic shift_en;
    logic assert_nack;
    logic assert_ack;
  } fsm_action_t;

  compressed_repair_t [NUM_REPAIR_HOOKS-1:0] r_repair_settings, s_repair_settings;
  logic [$bits(compressed_repair_t)*NUM_REPAIR_HOOKS-1:0] r_repair_settings_shift_reg;
  logic [N_SHIFT_CYCLES_PW-1:0] r_num_shifted_cycles;
  logic [IMC_BIST_REPAIR_ATTEMPT_PW-1:0] r_num_repair_attempts;
  bisr_ctl_state_e_t r_state, s_state;
  fsm_transition_t s_state_transition;
  fsm_action_t s_state_action;
  logic [1:0] sr_bank_already_repaired;
  logic       s_exceeded_max_repairs;
  logic [1:0] [NUM_REPAIR_HOOKS_PW-1:0] si_imc_repair_hook;
  logic [1:0]                       r_imc_repair_req;
  logic [1:0] [MVM_IMC_BANK_PW-1:0] r_imc_repair_bank;
  logic [1:0] [IMC_BANK_COL_PW-1:0] r_imc_repair_col;
  logic [1:0] [NUM_REPAIR_HOOKS_PW-1:0] r_imc_repair_hook;

  /// -----------------------
  /// ----- FSM -------------
  /// -----------------------
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_state <= E_IDLE;
    else begin
      if(i_clear) r_state <= E_IDLE;
      else        r_state <= s_state;
    end

  always_comb begin : s_state_cproc
    s_state = r_state;
         if(s_state_transition.idle_from_invalid_state)          s_state = E_IDLE;
    else if(s_state_transition.apply_from_idle)                  s_state = E_APPLY;
    else if(s_state_transition.idle_from_apply_max_attempts)     s_state = E_IDLE;
    else if(s_state_transition.idle_from_apply_already_repaired) s_state = E_IDLE;
    else if(s_state_transition.shift_from_apply)                 s_state = E_SHIFT;
    else if(s_state_transition.idle_from_shift)                  s_state = E_IDLE;
  end

  assign s_state_transition.idle_from_invalid_state =
    ~(r_state inside {E_IDLE, E_APPLY, E_SHIFT});
  assign s_state_transition.apply_from_idle =
    (r_state == E_IDLE)
    & (|i_imc_repair_req);
  assign s_state_transition.idle_from_apply_max_attempts =
    (r_state == E_APPLY)
    & s_exceeded_max_repairs;
  assign s_state_transition.idle_from_apply_already_repaired =
    (r_state == E_APPLY)
    & (r_imc_repair_req & sr_bank_already_repaired);
  assign s_state_transition.shift_from_apply =
    (r_state == E_APPLY)
    & ~s_exceeded_max_repairs
    & ~(r_imc_repair_req & sr_bank_already_repaired);
  assign s_state_transition.idle_from_shift =
    (r_state == E_SHIFT)
    & (r_num_shifted_cycles == (N_SHIFT_CYCLES+N_WAIT_CYCLES-1));

  assign s_state_action.capture_req   = s_state_transition.apply_from_idle;
  assign s_state_action.capture_shift = s_state_transition.shift_from_apply;
  assign s_state_action.apply_repair  = (r_state == E_APPLY);
  assign s_state_action.shift_en      = (r_state == E_SHIFT);
  assign s_state_action.assert_nack   =
    s_state_transition.idle_from_apply_already_repaired
    | s_state_transition.idle_from_apply_max_attempts;
  assign s_state_action.assert_ack    = s_state_transition.idle_from_shift;

  /// -----------------------
  /// ----- Design ----------
  /// -----------------------
  // Translate bank,col location to correct location in the shift reg
  always_comb foreach(si_imc_repair_hook[i])
    si_imc_repair_hook[i] = f_bankColToHook(
      .i_bank(i_imc_repair_bank[i]),
      .i_col (i_imc_repair_col[i])
    );

  // Latch request
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) begin
      r_imc_repair_req  <= '0;
      r_imc_repair_bank <= '0;
      r_imc_repair_col  <= '0;
      r_imc_repair_hook <= '0;
    end else begin
      if(i_clear) begin
        r_imc_repair_req  <= '0;
        r_imc_repair_bank <= '0;
        r_imc_repair_col  <= '0;
        r_imc_repair_hook <= '0;
      end else if(s_state_action.capture_req) begin
        r_imc_repair_req  <= i_imc_repair_req;
        r_imc_repair_bank <= i_imc_repair_bank;
        r_imc_repair_col  <= i_imc_repair_col;
        r_imc_repair_hook <= si_imc_repair_hook;
      end
    end

  // Only consider already repaired if both 4-bit columns attampted
  always_comb foreach(sr_bank_already_repaired[i])
    sr_bank_already_repaired[i] =
      r_repair_settings[r_imc_repair_hook[i]].repair_en
      & r_repair_settings[r_imc_repair_hook[i]].repair_col[0];

  assign s_exceeded_max_repairs = (r_num_repair_attempts > i_max_repair_attempts);

  always_comb begin : cproc_s_repair_settings
    s_repair_settings = r_repair_settings;
    foreach(r_imc_repair_req[i]) begin
      if(r_imc_repair_req[i]) begin
        // Repair col:
        // Remap col[31:0] into wrapper[1:0],col[31:0]
        // Discard MSB and multiply by 2, add offset if previously repaired
        s_repair_settings[r_imc_repair_hook[i]] = '{
          repair_en: 1'b1,
          repair_col: {
            r_imc_repair_col[i][IMC_BANK_COL_PW-2:0],
            r_repair_settings[r_imc_repair_hook[i]].repair_en
          }
        };
      end
    end
  end

  // Build repair settings
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_repair_settings <= '0;
    else begin
      if(i_clear) r_repair_settings <= '0;
      else if(s_state_action.apply_repair) r_repair_settings <= s_repair_settings;
    end

  // This is useful for debugging chain shift, keep it around for now
  //compressed_repair_t [NUM_REPAIR_HOOKS-1:0] s_debug_chain;
  //always_comb foreach(s_debug_chain[i])
  //  s_debug_chain[i] = '{
  //    repair_en: 1'b0,
  //    repair_col: i
  //  };

  // Capture and drive repair settings shift_reg
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_repair_settings_shift_reg <= '0;
    else begin
      if(i_clear) r_repair_settings_shift_reg <= '0;
      else if(s_state_action.capture_shift) r_repair_settings_shift_reg <= s_repair_settings;//s_debug_chain
      else if(s_state_action.shift_en)
        r_repair_settings_shift_reg <= {i_imc_bisr_so, r_repair_settings_shift_reg[$bits(r_repair_settings_shift_reg)-1:1]};
    end

  // Repair attempts counter
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_num_repair_attempts <= '0;
    else begin
      if(i_clear) r_num_repair_attempts <= '0;
      else if(s_state_action.assert_ack)
        r_num_repair_attempts <= r_num_repair_attempts + 'd1;
    end

  // Shift cycles counter
  always_ff @(posedge i_clk, negedge i_rst_n)
  if (!i_rst_n) r_num_shifted_cycles <= '0;
  else begin
    if(i_clear) r_num_shifted_cycles <= '0;
    else if(s_state_action.capture_shift)
      r_num_shifted_cycles <= '0;
    else if(s_state_action.shift_en)
      r_num_shifted_cycles <= r_num_shifted_cycles + 'd1;
  end

  /// -----------------------
  /// ----- Outputs ---------
  /// -----------------------

  assign o_imc_repair_ack  = r_imc_repair_req & {2{s_state_action.assert_ack}};
  assign o_imc_repair_nack = r_imc_repair_req & {2{s_state_action.assert_nack}};

  assign o_imc_bisr_shift_en = s_state_action.shift_en;
  assign o_imc_bisr_ue       = (r_state == E_SHIFT) & (r_num_shifted_cycles == (N_SHIFT_CYCLES-1));
  assign o_imc_bisr_si       = r_repair_settings_shift_reg[0];

endmodule : imc_bisr
