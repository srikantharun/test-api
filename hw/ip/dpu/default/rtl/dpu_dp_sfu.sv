// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Special Function Unit
// See prod/europa/#788
//
// Owner: Stefan Mach <stefan.mach@axelera.ai>

module dpu_dp_sfu
  import dpu_pkg::*;
#(
  parameter sfu_func_sel_t FUNC_SEL = 7'h7F,  // all functions
  parameter int unsigned NUM_REGS = 2  // two pipe regs
) (
  input  wire        i_clk,        // Clock
  input  wire        i_rst_n,
  // Input Side
  input  pw_dpu_fp_t i_in,
  input  sfu_func_e  i_sfu_func,   // Fucntion select, only 7bits used!
  input  dst_loc_t   i_dst_loc,
  input  logic       i_valid,
  output logic       o_ready,
  // Output Side
  output pw_dpu_fp_t o_out,        // Output
  output dst_loc_t   o_dst_loc,
  output logic       o_valid,
  input  logic       i_ready,
  // Status signals
  output logic       o_busy,       // valid operation in flight, can be used for clock-gating
  // Status Flags are not synchonized with the output data, they just go high on internal status
  output logic       o_overflow,
  output logic       o_underflow,
  output logic       o_inexact,
  output logic       o_invalid,
  output logic       o_div_zero
);

  typedef enum logic {
    E_FIRST_BEAT = 1'b0,
    E_SECOND_BEAT = 1'b1
  } sfu_fsm_state_t;
  sfu_fsm_state_t sfu_in_state_d, sfu_in_state_q;
  logic sfu_require_2nd_beat;

  typedef dpu_fp_t [PW_LEN/2-1:0] half_pw_dpu_fp_t;
  half_pw_dpu_fp_t sfu_in, sfu_out, sfu_aside_q;

  // Pipeline that will have to be retimed into the DW instances
  logic [NUM_REGS:0] valid_q, ready_q;  // ready_q is not actually registered
  half_pw_dpu_fp_t [NUM_REGS:0] sfu_in_q;
  sfu_func_e       [NUM_REGS:0] sfu_func_q;
  dst_loc_t        [NUM_REGS:0] dst_loc_q;
  sfu_fsm_state_t  [NUM_REGS:0] sfu_state_q;

  assign sfu_require_2nd_beat = i_valid
                              & (i_dst_loc.vm == VM_PW64)
                              & (sfu_in_state_q == E_FIRST_BEAT);

  always_comb begin : sfu_in_state_cproc
    sfu_in_state_d = sfu_in_state_q;
    unique case (sfu_in_state_q)
      E_FIRST_BEAT:
        if(i_valid & ready_q[0] & (i_dst_loc.vm == VM_PW64)) begin
          // If processed 1st beat in PW64 mode, move to 2nd beat
          sfu_in_state_d = E_SECOND_BEAT;
        end
      E_SECOND_BEAT:
        if(i_valid & ready_q[0]) begin
          // If processed 2nd beat, move to initial state
          sfu_in_state_d = E_FIRST_BEAT;
        end
      default:
        sfu_in_state_d = E_FIRST_BEAT;
    endcase
  end : sfu_in_state_cproc

  always_ff @(posedge i_clk or negedge i_rst_n)
    if(!i_rst_n) sfu_in_state_q <= E_FIRST_BEAT;
    else         sfu_in_state_q <= sfu_in_state_d;

  for (genvar i = 0; i < PW_LEN / 2; ++i) begin : gen_input_mux
    // First beat: Take evens in lower half and odds in upper half
    // Second beat (if applicable): Take odds in the lower half and evens in the upper half
    always_comb begin : sfu_in_cproc
      if (sfu_in_state_q == E_FIRST_BEAT) begin
        sfu_in[i] = (i >= (PW_LEN/4)) ? i_in[2*i+1] : i_in[2*i];
      end else begin
        sfu_in[i] = (i <  (PW_LEN/4)) ? i_in[2*i+1] : i_in[2*i];
      end
    end : sfu_in_cproc
  end


  // Input Regs for retiming
  assign sfu_in_q[0]    = sfu_in;
  assign sfu_func_q[0]  = i_sfu_func;
  assign dst_loc_q[0]   = i_dst_loc;
  assign valid_q[0]     = i_valid;
  assign sfu_state_q[0] = sfu_in_state_q;
  assign o_ready        = ready_q[0] & ~sfu_require_2nd_beat;
  for (genvar i = 0; i < NUM_REGS; ++i) begin : gen_pipeline
    assign ready_q[i] = ready_q[i+1] | ~valid_q[i+1];

    // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)        valid_q[i+1] <= 1'b0;
      else if (ready_q[i]) valid_q[i+1] <= valid_q[i];
    end

    // DFFL: D-Flip-Flop, load enable
    always_ff @(posedge i_clk) begin
      if (valid_q[i] && ready_q[i]) begin
        sfu_in_q[i+1]    <= sfu_in_q[i];
        sfu_func_q[i+1]  <= sfu_func_q[i];
        dst_loc_q[i+1]   <= dst_loc_q[i];
        sfu_state_q[i+1] <= sfu_state_q[i];
      end
    end

  end
  // PW64 mode set-aside buffer
  // Separate process as the gating conditions are different:
  // - ignore ready when writing (not directly output-facing)
  // - only write when a follow-up beat is expected
  logic set_aside_wren, set_aside_rden;
  logic set_aside_valid_q;

  assign set_aside_wren = valid_q[NUM_REGS]
                        & (sfu_state_q[NUM_REGS] == E_FIRST_BEAT)
                        & (dst_loc_q[NUM_REGS].vm == VM_PW64);

  assign set_aside_rden = valid_q[NUM_REGS]
                        & (sfu_state_q[NUM_REGS] == E_SECOND_BEAT)
                        & i_ready;

  always_ff @(posedge i_clk or negedge i_rst_n) begin : set_aside_sproc
    if(!i_rst_n)            set_aside_valid_q <= 1'b0;
    else if(set_aside_wren) set_aside_valid_q <= 1'b1;
    else if(set_aside_rden) set_aside_valid_q <= 1'b0;
  end : set_aside_sproc

  // DFFL: D-Flip-Flop, load enable
  always_ff @(posedge i_clk) begin
    if (set_aside_wren) sfu_aside_q <= sfu_out;
  end

  // The actual DW units
  logic [PW_LEN/2-1:0] overflow, underflow, inexact, invalid, div_zero;

  for (genvar i = 0; i < PW_LEN / 2; ++i) begin : gen_sfu
    dw_status_t status;
    DW_lp_fp_multifunc #(
      .sig_width      (DPU_FPT_SIGW),
      .exp_width      (DPU_FPT_EXPW),
      .ieee_compliance(DW_IEEE_COMPL),
      .func_select    (FUNC_SEL),
      .faithful_round (0),
      .pi_multiple    (0)
    ) i_sfu (
      .a   (sfu_in_q[NUM_REGS][i]),
      .func(sfu_func_q[NUM_REGS]),
      .rnd (DW_RND_RNE),
      .z   (sfu_out[i]),
      .status // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    // split out the status flags
    assign overflow[i]  = status.infinity | status.huge;
    assign underflow[i] = status.tiny;
    assign inexact[i]   = status.inexact;
    assign invalid[i]   = status.invalid;
    assign div_zero[i]  = status.comp_specific;
  end

  // Only raise the flag when a valid operation is being processed
  assign o_overflow  = |overflow & valid_q[NUM_REGS];
  assign o_underflow = |underflow & valid_q[NUM_REGS];
  assign o_inexact   = |inexact & valid_q[NUM_REGS];
  assign o_invalid   = |invalid & valid_q[NUM_REGS];
  assign o_div_zero  = |div_zero & valid_q[NUM_REGS];

  // Outputs
  always_comb begin : global_outputs_cproc
    o_dst_loc = dst_loc_q[NUM_REGS];
    // An operation is in flight (i.e. clock must be on) if there's a valid somewhere
    o_busy    = i_valid | (|valid_q) | set_aside_valid_q;
    // TODO: unsure if set_aside_valid_q is required here,
    //   if we use busy to gate SFU only, it is NOT required
    //   if we use busy to gate higher level DPU datapath, it IS required

    if(set_aside_wren) begin
      // Set-aside handling for first beat of 2-beat burst
      // The data is not presented at the output
      o_valid           = 1'b0;
      // The SFU result is always consumed
      ready_q[NUM_REGS] = 1'b1;
    end else begin
      // Otherwise, present data immediately
      o_valid           = valid_q[NUM_REGS];
      ready_q[NUM_REGS] = i_ready;
    end
  end : global_outputs_cproc

  for (genvar i = 0; i < PW_LEN; ++i) begin : gen_pw_outputs

    localparam bit IndexIsOdd = (i % 2 == 1);

    always_comb begin
      if(sfu_state_q[NUM_REGS] == E_SECOND_BEAT) begin
        // Second beat mixes the current output data with the set-aside buffer
        // i=0 is first_beat@0 : sfu_in[0] <set_aside[0]>
        // i=1 is second_beat@0 : sfu_in[1]
        // i=2 is first_beat@1 : sfu_in[2] <set_aside[1]>
        // ...
        // i=31 is second_beat@15 : sfu_in[31]
        // i=32 is second_beat@16 : sfu_in[32]
        // i=33 is first_beat@16 : sfu_in[33] <set_aside[16]>
        // ...
        if(i >= PW_LEN/2) begin
          // Upper half
          o_out[i] = IndexIsOdd ? sfu_aside_q[i/2] : sfu_out[i/2];
        end else begin
          // Lower half
          o_out[i] = IndexIsOdd ? sfu_out[i/2] : sfu_aside_q[i/2];
        end
      end else begin
        // Otherwise reverse gen_input_mux mapping:
        // Place lower half in the evens and upper half in the odds
        o_out[i] = sfu_out[(i%2)*(PW_LEN/4)+((i%(PW_LEN/2))/2)];
      end
    end
  end : gen_pw_outputs

endmodule
