// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: MADD block performs multiplication and addition on PWORD long vectors
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>
//        Stefan Mach <stefan.mach@axelera.ai>

module dpu_dp_madd
  import dpu_pkg::*;
(
  input  wire        clk_i,        // Clock
  input  wire        rst_ni,       // Reset active low
  // Input Side
  input  pw_dpu_fp_t x_i,          // First multiplicant
  input  pw_dpu_fp_t y_i,          // Second multiplicant
  input  pw_dpu_fp_t z_i,          // Offset
  input  dst_loc_t   dst_loc_i,
  input  logic       valid_i,
  output logic       ready_o,
  // Output Side
  output pw_dpu_fp_t out_o,        // Output
  output dst_loc_t   dst_loc_o,
  output logic       valid_o,
  input  logic       ready_i,
  // Status signals
  output logic       busy_o,       // valid operation in flight, can be used for clock-gating
  // Status Flags are not synchonized with the output data, they just go high on internal status
  output logic       overflow_o,
  output logic       underflow_o,
  output logic       inexact_o,
  output logic       invalid_o
);

  // One internal pipe stage (_q)
  pw_dpu_fp_t mout, mout_q;
  pw_dpu_fp_t z_q;
  pw_dpu_fp_t maout;
  dst_loc_t   dst_loc_q;
  logic valid_q, ready_q;  // ready_q is not actually registered
  // Status signals
  logic [PW_LEN-1:0] of_mult, uf_mult, nx_mult, nv_mult;
  logic [PW_LEN-1:0] of_add, nx_add, nv_add;
  logic of_mult_masked, uf_mult_masked, nx_mult_masked, nv_mult_masked;
  logic of_add_masked, nx_add_masked, nv_add_masked;


  // Instances of DW_fp_mult
  for (genvar i = 0; unsigned'(i) < PW_LEN; ++i) begin : gen_FMULTS
    dw_status_t status_mult;
    DW_fp_mult #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .ieee_compliance(DW_IEEE_COMPL)
    ) i_fpmul (
      .a     (x_i[i]),
      .b     (y_i[i]),
      .rnd   (DW_RND_RNE),
      .z     (mout[i]),
      .status(status_mult) // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    assign of_mult[i] = status_mult.infinity | status_mult.huge;
    assign uf_mult[i] = status_mult.tiny;
    assign nx_mult[i] = status_mult.inexact;
    assign nv_mult[i] = status_mult.invalid;
  end
  // Only raise the flag when a valid operation is being processed
  assign of_mult_masked = |of_mult & valid_i;
  assign uf_mult_masked = |uf_mult & valid_i;
  assign nx_mult_masked = |nx_mult & valid_i;
  assign nv_mult_masked = |nv_mult & valid_i;

  // Pipeline Stage 1 (same as `stream_register` but non-resettable flop for data)
  assign ready_o = ready_q | ~valid_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)      valid_q <= 1'b0;
    else if (ready_o) valid_q <= valid_i;
  end

  always_ff @(posedge clk_i) begin
    if (valid_i && ready_o) begin
      mout_q    <= mout;
      z_q       <= z_i;
      dst_loc_q <= dst_loc_i;
    end
  end

  // Instances of DW_fp_add
  for (genvar i = 0; unsigned'(i) < PW_LEN; ++i) begin : gen_FADDS
    dw_status_t status_add;
    DW_fp_add #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .ieee_compliance(DW_IEEE_COMPL)
    ) i_fpadd (
      .a     (mout_q[i]),
      .b     (z_q[i]),
      .rnd   (DW_RND_RNE),
      .z     (maout[i]),
      .status(status_add) // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    assign of_add[i] = status_add.infinity | status_add.huge;
    assign nx_add[i] = status_add.inexact;
    assign nv_add[i] = status_add.invalid;
  end
  // Only raise the flag when a valid operation is being processed
  assign of_add_masked = |of_add & valid_q;
  assign nx_add_masked = |nx_add & valid_q;
  assign nv_add_masked = |nv_add & valid_q;

  // It is unlikely we need another pipe stage here, feed to output
  assign out_o         = maout;
  assign dst_loc_o     = dst_loc_q;
  assign valid_o       = valid_q;
  assign ready_q       = ready_i;

  // An operation is in flight (i.e. clock must be on) if there's a valid somewhere
  assign busy_o        = valid_i | valid_q | valid_o;

  // Overflow in mult or add - not synch to output as we don't have 'precise' exceptions
  assign overflow_o    = of_mult_masked | of_add_masked;
  assign underflow_o   = uf_mult_masked;
  assign inexact_o     = nx_mult_masked | nx_add_masked;
  assign invalid_o     = nv_mult_masked | nv_add_masked;

endmodule
