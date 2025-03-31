// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Performs max or min reduction on PWORD long vector and
// broadcases the result back to the whole vector.
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

module dpu_dp_maxminred
  import dpu_pkg::*;
(
  input wire clk_i,  // Clock
  input wire rst_ni, // Reset active low

  input  pw_dpu_fp_t x_i,        // Input
  input  logic       maxmin_i,   // '0'- maxred, '1'- minred
  input  dst_loc_t   dst_loc_i,
  input  logic       valid_i,
  output logic       ready_o,

  output pw_dpu_fp_t out_o,      // Output
  output dst_loc_t   dst_loc_o,
  output logic       valid_o,
  input  logic       ready_i,

  output logic busy_o  // valid operation in flight, can be used for clock-gating
);

  // One internal pipe stage (_q)
  dpu_fp_t [PW_LEN/2-1:0] out1;
  dpu_fp_t [PW_LEN/4-1:0] out2;
  dpu_fp_t [PW_LEN/8-1:0] out3;
  dpu_fp_t [PW_LEN/8-1:0] out3_q;
  dpu_fp_t [         3:0] out4;
  dpu_fp_t [         1:0] out5;
  dpu_fp_t out6, out6_o;
  dst_loc_t dst_loc_q;
  logic valid_q, ready_q;  // ready_q is not actually registered

  for (genvar i = 0; unsigned'(i) < PW_LEN / 2; ++i) begin : gen_FMAX2_ST1
    dpu_dp_fp_maxmin i1_fpmaxmin2 (
      .in1_i(x_i[2*i]),
      .in2_i(x_i[2*i+1]),
      .sel_i(maxmin_i),
      .out_o(out1[i])
    );
  end
  for (genvar i = 0; unsigned'(i) < PW_LEN / 4; ++i) begin : gen_FMAX2_ST2
    dpu_dp_fp_maxmin i2_fpmaxmin2 (
      .in1_i(out1[2*i]),
      .in2_i(out1[2*i+1]),
      .sel_i(maxmin_i),
      .out_o(out2[i])
    );
  end
  for (genvar i = 0; unsigned'(i) < PW_LEN / 8; ++i) begin : gen_FMAX2_ST3
    dpu_dp_fp_maxmin i3_fpmaxmin2 (
      .in1_i(out2[2*i]),
      .in2_i(out2[2*i+1]),
      .sel_i(maxmin_i),
      .out_o(out3[i])
    );
  end
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
  //`FFLNR(out3_q, out3, valid_i && ready_o, clk_i)
  //`FFLNR(dst_loc_q, dst_loc_i, valid_i && ready_o, clk_i)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      out3_q    <= '0;
      dst_loc_q <= '0;
    end else begin
      if (valid_i && ready_o) begin
        out3_q    <= out3;
        dst_loc_q <= dst_loc_i;
      end
    end
  end

  for (genvar i = 0; i < 4; ++i) begin : gen_FMAX2_ST4
    dpu_dp_fp_maxmin i4_fpmaxmin2 (
      .in1_i(out3_q[2*i]),
      .in2_i(out3_q[2*i+1]),
      .sel_i(maxmin_i),
      .out_o(out4[i])
    );
  end
  for (genvar i = 0; i < 2; ++i) begin : gen_FMAX2_ST5
    dpu_dp_fp_maxmin i5_fpmaxmin2 (
      .in1_i(out4[2*i]),
      .in2_i(out4[2*i+1]),
      .sel_i(maxmin_i),
      .out_o(out5[i])
    );
  end
  dpu_dp_fp_maxmin i6_fpmaxmin2 (
    .in1_i(out5[0]),
    .in2_i(out5[1]),
    .sel_i(maxmin_i),
    .out_o(out6)
  );

  // Outputs
  assign ready_q   = ready_i;
  assign valid_o   = valid_q;
  assign dst_loc_o = dst_loc_q;
  // Broadcast result
  assign out_o     = {(PW_LEN) {dst_loc_q.vm ? out5[0] : out6}};

  // An operation is in flight (i.e. clock must be on) if there's a valid somewhere
  assign busy_o    = valid_i | valid_q | valid_o;

endmodule
