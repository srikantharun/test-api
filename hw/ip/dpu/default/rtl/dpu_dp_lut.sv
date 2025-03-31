// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: LUT block computes scale and offset coefficients
// for each PWORD element based on bins determined with quaternary
// comparator tree. There are 15 bins and 16 respective scale and
// offset coefficients, which is not parametrizable. Accordingly,
// comparator tree is 2 levels deep, those 2 levels are in pipeline
// stage 1, and 16:1 MUXs are in stage 2.
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

module dpu_dp_lut
  import dpu_pkg::*;
(
  input wire clk_i,  // Clock
  input wire rst_ni, // Reset active low

  input  pw_dpu_fp_t in_i,       // Input
  input  pw_dpu_fp_t bso_i,      // Packed bin, scale and offset
  input  dst_loc_t   dst_loc_i,
  input  logic       valid_i,
  output logic       ready_o,

  output pw_dpu_fp_t in_o,       // Pipelined input
  output pw_dpu_fp_t scale_o,    // Output scale coeff
  output pw_dpu_fp_t offset_o,   // Output offset coeff
  output dst_loc_t   dst_loc_o,
  output logic       valid_o,
  input  logic       ready_i,

  output logic busy_o  // valid operation in flight, can be used for clock-gating
);

  // Input stage & inner pipeline
  dpu_fp_t [NR_LUT_BINS-1:0] bin;  // Bin boundry
  dpu_fp_t [NR_LUT_BINS-1:0] scale, scale_q;  // Scale coeff
  dpu_fp_t [NR_LUT_BINS-1:0] offset, offset_q;  // Offset coeff
  new_lut_t                  new_lut;

  logic [PW_LEN-1:0][2:0] pos1, pos2;
  logic [PW_LEN-1:0] norm_range, norm_range_q;

  logic [PW_LEN-1:0][$clog2(NR_LUT_BINS)-1:0] psum1, psum1_q;
  logic [PW_LEN-1:0][$clog2(NR_LUT_BINS)-1:0] psum2, psum2_q;

  pw_dpu_fp_t res_in, res_sel_in;
  dst_loc_t   dst_loc_q;
  logic valid_q, ready_q;  // ready is not actually registered but belongs to valid_q

  // Special case handling
  new_lut_t          new_lut_compat, new_lut_compat_q;
  logic [PW_LEN-1:0] below_lo_bnd, below_lo_bnd_q;
  logic [PW_LEN-1:0] below_hi_bnd, below_hi_bnd_q;

  assign bin[NR_LUT_BINS-1:1] = bso_i[NR_LUT_BINS-2:0];
  assign bin[0] = bso_i[NR_LUT_BINS-1];
  assign scale = bso_i[2*NR_LUT_BINS-1:NR_LUT_BINS];
  assign offset = bso_i[3*NR_LUT_BINS-1:2*NR_LUT_BINS];
  assign new_lut = new_lut_t'(bso_i[4*NR_LUT_BINS-1:3*NR_LUT_BINS]);

  // Detect if using new_lut (Europa) format or old (Omega) format
  // If not using Europa version new_lut, fill it with hardcoded values
  always_comb begin : new_lut_back_compat_cproc
    if(new_lut.version == DPU_FP_ONE)
      new_lut_compat = new_lut;
    else
      new_lut_compat = '{
        version: DPU_FP_ZERO,
        hi_off : DPU_FP_ZERO,
        hi_bnd : DPU_FP_INF,
        lo_off : DPU_FP_ZERO,
        lo_bnd : DPU_FP_NEGINF,
        off_16 : DPU_FP_ZERO,
        scl_16 : DPU_FP_ZERO,
        default: '0
      };
  end : new_lut_back_compat_cproc

  // Pipeline stage 1
  // Note: Nothing here is adhering to `NR_LUT_BINS`, it's hardcoded
  for (genvar i = 0; unsigned'(i) < PW_LEN; ++i) begin : gen_F_PWORD1

    // Compare with low bound
    dpu_dp_fp_lt u_cmp_lb (
      .i_operand_a    (in_i[i]),
      .i_operand_b    (new_lut_compat.lo_bnd),
      .o_a_less_than_b(below_lo_bnd[i])
    );
    // Compare with high bound
    dpu_dp_fp_lt u_cmp_hb (
      .i_operand_a    (in_i[i]),
      .i_operand_b    (new_lut_compat.hi_bnd),
      .o_a_less_than_b(below_hi_bnd[i])
    );

    // Compare with bins
    dpu_dp_fp_lt u_cmp_i0 (
      .i_operand_a    (in_i[i]),
      .i_operand_b    (bin[0]),
      .o_a_less_than_b(norm_range[i])
    );
    dpu_dp_fp_lt u_cmp_i1 (
      .i_operand_a    (in_i[i]),
      .i_operand_b    (bin[4]),
      .o_a_less_than_b(pos1[i][2])
    );
    dpu_dp_fp_lt u_cmp_i2 (
      .i_operand_a    (in_i[i]),
      .i_operand_b    (bin[8]),
      .o_a_less_than_b(pos1[i][1])
    );
    dpu_dp_fp_lt u_cmp_i3 (
      .i_operand_a    (in_i[i]),
      .i_operand_b    (bin[12]),
      .o_a_less_than_b(pos1[i][0])
    );

    assign psum1[i] = (pos1[i] == 3'b011) ? 'd4  :
                        (pos1[i] == 3'b001) ? 'd8  :
                        (pos1[i] == 3'b000) ? 'd12 : 'd0;

    dpu_dp_fp_lt u_cmp_i4 (
      .i_operand_a    (in_i[i]),
      .i_operand_b    (bin[4'(psum1[i]+1)]),
      .o_a_less_than_b(pos2[i][2])
    );
    dpu_dp_fp_lt u_cmp_i5 (
      .i_operand_a    (in_i[i]),
      .i_operand_b    (bin[4'(psum1[i]+2)]),
      .o_a_less_than_b(pos2[i][1])
    );
    dpu_dp_fp_lt u_cmp_i6 (
      .i_operand_a    (in_i[i]),
      .i_operand_b    (bin[4'(psum1[i]+3)]),
      .o_a_less_than_b(pos2[i][0])
    );
    assign psum2[i] = (pos2[i] == 3'b011) ? 'd1 :
                        (pos2[i] == 3'b001) ? 'd2 :
                        (pos2[i] == 3'b000) ? 'd3 : 'd0;
  end

  // Internal Pipeline Stage (same as `stream_register` but non-resettable flop for data)
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
  //`FFLNR(res_in, in_i, valid_i && ready_o, clk_i)
  //`FFLNR(scale_q, scale, valid_i && ready_o, clk_i)
  //`FFLNR(offset_q, offset, valid_i && ready_o, clk_i)
  //`FFLNR(norm_range_q, norm_range, valid_i && ready_o, clk_i)
  //`FFLNR(psum1_q, psum1, valid_i && ready_o, clk_i)
  //`FFLNR(psum2_q, psum2, valid_i && ready_o, clk_i)
  //`FFLNR(dst_loc_q, dst_loc_i, valid_i && ready_o, clk_i)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      res_in           <= '0;
      scale_q          <= '0;
      offset_q         <= '0;
      norm_range_q     <= '0;
      psum1_q          <= '0;
      psum2_q          <= '0;
      dst_loc_q        <= '0;
      below_lo_bnd_q   <= '0;
      below_hi_bnd_q   <= '0;
      new_lut_compat_q <= '0;
    end else begin
      if (valid_i && ready_o) begin
        res_in           <= in_i;
        scale_q          <= scale;
        offset_q         <= offset;
        norm_range_q     <= norm_range;
        psum1_q          <= psum1;
        psum2_q          <= psum2;
        dst_loc_q        <= dst_loc_i;
        below_lo_bnd_q   <= below_lo_bnd;
        below_hi_bnd_q   <= below_hi_bnd;
        new_lut_compat_q <= new_lut_compat;
      end
    end
  end

  // Output stage
  logic [PW_LEN-1:0][$clog2(NR_LUT_BINS)-1:0] sel;
  pw_dpu_fp_t res_scale, res_offset;

  // Pipeline stage 2
  for (genvar i = 0; unsigned'(i) < PW_LEN; ++i) begin : gen_F_PWORD
    always_comb begin : res_cproc
      sel[i] = psum1_q[i] + psum2_q[i];

      if(below_lo_bnd_q[i]) begin
        res_sel_in[i] = DPU_FP_ZERO;
        res_scale[i]  = DPU_FP_ZERO;
        res_offset[i] = new_lut_compat_q.lo_off;
      end else if(~below_hi_bnd_q[i]) begin
        res_sel_in[i] = DPU_FP_ZERO;
        res_scale[i]  = DPU_FP_ZERO;
        res_offset[i] = new_lut_compat_q.hi_off;
      end else begin
        res_sel_in[i] = res_in[i];
        res_scale[i]  = (norm_range_q[i]) ? scale_q[sel[i]]  : new_lut_compat_q.scl_16;
        res_offset[i] = (norm_range_q[i]) ? offset_q[sel[i]] : new_lut_compat_q.off_16;
      end
    end : res_cproc
  end

  // Output pipe to cut path to MADD (same as `stream_register` but non-resettable flop for data)
  assign ready_q = ready_i | ~valid_o;
  //`FFL(valid_o, valid_q, ready_q, 1'b0, clk_i, rst_ni)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_o <= (1'b0);
    end else begin
      if (ready_q) begin
        valid_o <= (valid_q);
      end
    end
  end
  //`FFLNR(in_o, res_in, valid_q & ready_q, clk_i)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_o <= '0;
    end else begin
      if (valid_q & ready_q) begin
        in_o <= (res_sel_in);
      end
    end
  end
  //`FFLNR(scale_o, res_scale, valid_q & ready_q, clk_i)
  //`FFLNR(offset_o, res_offset, valid_q & ready_q, clk_i)
  //`FFLNR(dst_loc_o, dst_loc_q, valid_q & ready_q, clk_i)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      scale_o   <= '0;
      offset_o  <= '0;
      dst_loc_o <= '0;
    end else begin
      if (valid_q & ready_q) begin
        scale_o   <= res_scale;
        offset_o  <= res_offset;
        dst_loc_o <= dst_loc_q;
      end
    end
  end

  // An operation is in flight (i.e. clock must be on) if there's a valid somewhere
  assign busy_o = valid_i | valid_q | valid_o;

endmodule
