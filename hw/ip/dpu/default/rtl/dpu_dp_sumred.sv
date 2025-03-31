// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Performas sum reduction on PWORD long vector and
// broadcases the result back to the whole vector.
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

module dpu_dp_sumred
  import dpu_pkg::*;
(
  input  wire        clk_i,       // Clock
  input  wire        rst_ni,      // Reset active low
  // Input Side
  input  pw_dpu_fp_t x_i,         // Input
  input  dst_loc_t   dst_loc_i,
  input  logic       valid_i,
  output logic       ready_o,
  // Output Side
  output pw_dpu_fp_t out_o,       // Output
  output dst_loc_t   dst_loc_o,
  output logic       valid_o,
  input  logic       ready_i,
  // Status Signals
  output logic       busy_o,      // valid operation in flight, can be used for clock-gating
  // Status flags are not synchonized with the output data, they just go high on internal status
  output logic       overflow_o,
  output logic       inexact_o,
  output logic       invalid_o
);

  // Five internal pipe stages (_q to _q5)
  dpu_fp_t [PW_LEN/2-1:0] out1, out_q;
  dpu_fp_t [PW_LEN/4-1:0] out2, out_q2;
  dpu_fp_t [PW_LEN/8-1:0] out3, out_q3;
  dpu_fp_t [3:0] out4, out_q4;
  dpu_fp_t [1:0] out5, out_q5;
  dpu_fp_t out6, out6_o;
  dst_loc_t dst_loc_q, dst_loc_q2, dst_loc_q3, dst_loc_q4, dst_loc_q5;
  logic valid_q, valid_q2, valid_q3, valid_q4, valid_q5;
  logic ready_q, ready_q2, ready_q3, ready_q4, ready_q5;  // ready_q* is not actually registered
  // Status signals
  logic [PW_LEN/2-1:0] of1, nx1, nv1;
  logic [PW_LEN/4-1:0] of2, nx2, nv2;
  logic [PW_LEN/8-1:0] of3, nx3, nv3;
  logic [PW_LEN/16-1:0] of4, nx4, nv4;
  logic [PW_LEN/32-1:0] of5, nx5, nv5;
  logic [PW_LEN/64-1:0] of6, nx6, nv6;
  logic of1_masked, nx1_masked, nv1_masked;
  logic of2_masked, nx2_masked, nv2_masked;
  logic of3_masked, nx3_masked, nv3_masked;
  logic of4_masked, nx4_masked, nv4_masked;
  logic of5_masked, nx5_masked, nv5_masked;
  logic of6_masked, nx6_masked, nv6_masked;

  for (genvar i = 0; unsigned'(i) < PW_LEN / 2; ++i) begin : gen_FMAX2_ST1
    dw_status_t status;
    DW_fp_add #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .ieee_compliance(DW_IEEE_COMPL)
    ) i1_fpadd (
      .a  (x_i[2*i]),
      .b  (x_i[2*i+1]),
      .rnd(DW_RND_RNE),
      .z  (out1[i]),
      .status // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    assign of1[i] = status.infinity | status.huge;
    assign nx1[i] = status.inexact;
    assign nv1[i] = status.invalid;
  end
  // Only raise the flag when a valid operation is being processed
  assign of1_masked = |of1 & valid_i;
  assign nx1_masked = |nx1 & valid_i;
  assign nv1_masked = |nv1 & valid_i;

  // Pipeline Stage 1 (same as `stream_register` but non-resettable flop for data)
  assign ready_o = ready_q | ~valid_q;
  //`FFL(valid_q, valid_i, ready_o, 1'b0, clk_i, rst_ni)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q <= (1'b0);
    end else begin
      if (ready_o) begin
        valid_q <= (valid_i);
      end
    end
  end
  //`FFLNR(out_q, out1, valid_i && ready_o, clk_i)
  //`FFLNR(dst_loc_q, dst_loc_i, valid_i && ready_o, clk_i)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_q     <= '0;
      dst_loc_q <= '0;
    end else begin
      if (valid_i && ready_o) begin
        out_q     <= out1;
        dst_loc_q <= dst_loc_i;
      end
    end
  end

  for (genvar i = 0; unsigned'(i) < PW_LEN / 4; ++i) begin : gen_FMAX2_ST2
    dw_status_t status;
    DW_fp_add #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .ieee_compliance(DW_IEEE_COMPL)
    ) i2_fpadd (
      .a  (out_q[2*i]),
      .b  (out_q[2*i+1]),
      .rnd(DW_RND_RNE),
      .z  (out2[i]),
      .status // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    assign of2[i] = status.infinity | status.huge;
    assign nx2[i] = status.inexact;
    assign nv2[i] = status.invalid;
  end
  // Only raise the flag when a valid operation is being processed
  assign of2_masked = |of2 & valid_q;
  assign nx2_masked = |nx2 & valid_q;
  assign nv2_masked = |nv2 & valid_q;

  // Pipeline Stage 2 (same as `stream_register` but non-resettable flop for data)
  assign ready_q = ready_q2 | ~valid_q2;
  //`FFL(valid_q2, valid_q, ready_q, 1'b0, clk_i, rst_ni)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q2 <= (1'b0);
    end else begin
      if (ready_q) begin
        valid_q2 <= (valid_q);
      end
    end
  end
  //`FFLNR(out_q2, out2, valid_q && ready_q, clk_i)
  //`FFLNR(dst_loc_q2, dst_loc_q, valid_q && ready_q, clk_i)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_q2     <= '0;
      dst_loc_q2 <= '0;
    end else begin
      if (valid_q && ready_q) begin
        out_q2     <= out2;
        dst_loc_q2 <= dst_loc_q;
      end
    end
  end

  for (genvar i = 0; unsigned'(i) < PW_LEN / 8; ++i) begin : gen_FMAX2_ST3
    dw_status_t status;
    DW_fp_add #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .ieee_compliance(DW_IEEE_COMPL)
    ) i3_fpadd (
      .a  (out_q2[2*i]),
      .b  (out_q2[2*i+1]),
      .rnd(DW_RND_RNE),
      .z  (out3[i]),
      .status // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    assign of3[i] = status.infinity | status.huge;
    assign nx3[i] = status.inexact;
    assign nv3[i] = status.invalid;
  end
  // Only raise the flag when a valid operation is being processed
  assign of3_masked = |of3 & valid_q2;
  assign nx3_masked = |nx3 & valid_q2;
  assign nv3_masked = |nv3 & valid_q2;

  // Pipeline Stage 3 (same as `stream_register` but non-resettable flop for data)
  assign ready_q2   = ready_q3 | ~valid_q3;
  //`FFL(valid_q3, valid_q2, ready_q2, 1'b0, clk_i, rst_ni)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q3 <= (1'b0);
    end else begin
      if (ready_q2) begin
        valid_q3 <= (valid_q2);
      end
    end
  end
  //`FFLNR(out_q3, out3, valid_q2 && ready_q2, clk_i)
  //`FFLNR(dst_loc_q3, dst_loc_q2, valid_q2 && ready_q2, clk_i)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_q3     <= '0;
      dst_loc_q3 <= '0;
    end else begin
      if (valid_q2 && ready_q2) begin
        out_q3     <= out3;
        dst_loc_q3 <= dst_loc_q2;
      end
    end
  end

  for (genvar i = 0; i < 4; ++i) begin : gen_FMAX2_ST4
    dw_status_t status;
    DW_fp_add #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .ieee_compliance(DW_IEEE_COMPL)
    ) i4_fpadd (
      .a  (out_q3[2*i]),
      .b  (out_q3[2*i+1]),
      .rnd(DW_RND_RNE),
      .z  (out4[i]),
      .status // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    assign of4[i] = status.infinity | status.huge;
    assign nx4[i] = status.inexact;
    assign nv4[i] = status.invalid;
  end
  // Only raise the flag when a valid operation is being processed
  assign of4_masked = |of4 & valid_q3;
  assign nx4_masked = |nx4 & valid_q3;
  assign nv4_masked = |nv4 & valid_q3;

  // Pipeline Stage 4 (same as `stream_register` but non-resettable flop for data)
  assign ready_q3   = ready_q4 | ~valid_q4;
  //`FFL(valid_q4, valid_q3, ready_q3, 1'b0, clk_i, rst_ni)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q4 <= (1'b0);
    end else begin
      if (ready_q3) begin
        valid_q4 <= (valid_q3);
      end
    end
  end
  //`FFLNR(out_q4, out4, valid_q3 && ready_q3, clk_i)
  //`FFLNR(dst_loc_q4, dst_loc_q3, valid_q3 && ready_q3, clk_i)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_q4     <= '0;
      dst_loc_q4 <= '0;
    end else begin
      if (valid_q3 && ready_q3) begin
        out_q4     <= out4;
        dst_loc_q4 <= dst_loc_q3;
      end
    end
  end

  for (genvar i = 0; i < 2; ++i) begin : gen_FMAX2_ST5
    dw_status_t status;
    DW_fp_add #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .ieee_compliance(DW_IEEE_COMPL)
    ) i5_fpadd (
      .a  (out_q4[2*i]),
      .b  (out_q4[2*i+1]),
      .rnd(DW_RND_RNE),
      .z  (out5[i]),
      .status // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    assign of5[i] = status.infinity | status.huge;
    assign nx5[i] = status.inexact;
    assign nv5[i] = status.invalid;
  end
  // Only raise the flag when a valid operation is being processed
  assign of5_masked = |of5 & valid_q4;
  assign nx5_masked = |nx5 & valid_q4;
  assign nv5_masked = |nv5 & valid_q4;

  // Pipeline Stage 5 (same as `stream_register` but non-resettable flop for data)
  assign ready_q4   = ready_q5 | ~valid_q5;
  //`FFL(valid_q5, valid_q4, ready_q4, 1'b0, clk_i, rst_ni)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q5 <= (1'b0);
    end else begin
      if (ready_q4) begin
        valid_q5 <= (valid_q4);
      end
    end
  end
  //`FFLNR(out_q5, out5, valid_q4 && ready_q4, clk_i)
  //`FFLNR(dst_loc_q5, dst_loc_q4, valid_q4 && ready_q4, clk_i)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out_q5     <= '0;
      dst_loc_q5 <= '0;
    end else begin
      if (valid_q4 && ready_q4) begin
        out_q5     <= out5;
        dst_loc_q5 <= dst_loc_q4;
      end
    end
  end

  dw_status_t status;
  DW_fp_add #(
    .sig_width(DPU_FPT_SIGW),
    .exp_width(DPU_FPT_EXPW),
    .ieee_compliance(DW_IEEE_COMPL)
  ) i6_fpadd (
    .a  (out_q5[0]),
    .b  (out_q5[1]),
    .rnd(DW_RND_RNE),
    .z  (out6),
    .status // ASO-UNUSED_VARIABLE : Not all values of the status are observed
  );
  assign of6        = status.infinity | status.huge;
  assign nx6        = status.inexact;
  assign nv6        = status.invalid;
  // Only raise the flag when a valid operation is being processed
  assign of6_masked = |of6 & valid_q5;
  assign nx6_masked = |nx6 & valid_q5;
  assign nv6_masked = |nv6 & valid_q5;

  // Outputs
  assign ready_q5   = ready_i;
  assign valid_o    = valid_q5;
  assign dst_loc_o  = dst_loc_q5;
  // Broadcast result
  assign out_o      = {(PW_LEN) {dst_loc_q5.vm ? out_q5[0] : out6}};

  // An operation is in flight (i.e. clock must be on) if there's a valid somewhere
  assign busy_o     = valid_i | valid_q | valid_q2 | valid_q3 | valid_q4 | valid_q5 | valid_o;

  // Status flags - not synch to output as we don't have 'precise' exceptions
  assign overflow_o = of1_masked | of2_masked | of3_masked | of4_masked | of5_masked | of6_masked;
  assign inexact_o  = nx1_masked | nx2_masked | nx3_masked | nx4_masked | nx5_masked | nx6_masked;
  assign invalid_o  = nv1_masked | nv2_masked | nv3_masked | nv4_masked | nv5_masked | nv6_masked;

endmodule
