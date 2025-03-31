// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Output stream (ODR) conversion block based on fmt from fp18 to int8, fp16, fp24,
// and fp32
//
// FP18 data PWORD is fed through format conversion units in parallel. The appropriate path is
// then selected to be applied to the output stream. Multi-Beat operations will only read a portion
// of the FP18 PWORD in each beat, and the transaction is considered complete once all elements of
// the PWORD have been sent.
//
// WARNING: This module is not fully parametric in `PW_LEN` and IO_W due to the addition of FP24
// which requires partial values on stream beats as 64/3 = 21.333.
// TODO(@stefan.mach): In another life, generalize this to handle other PW lengths and have a more general behavior. Many fmt + vm combinations are hardcoded and irregluar
//
// Owner: Stefan Mach <stefan.mach@axelera.ai>
module dpu_dp_out_stream
  import dpu_pkg::*;
(
  input wire clk_i,  // Clock
  input wire rst_ni, // Reset active low

  // Input data
  input pw_dpu_fp_t in_data_i,  // Input

  // Output stream
  output logic [PW_LEN-1:0][IO_W-1:0] out_data_o,  // Output
  output logic                        out_vld_o,
  output logic                        out_lst_o,
  input  logic                        out_rdy_i,

  // Conversion request
  input  stream_fmt_e  fmt_i,         // Format
  input  vector_mode_e operand_vm_i,  // Vector mode of the data we produce [e.g. pword64]
  input  logic         fmt_vld_i,
  input  logic         fmt_last_i,
  output logic         fmt_rdy_o,

  // CSR configuration
  input logic cfg_int_signed_i,

  // IRQs
  output logic overflow_o,
  output logic underflow_o,
  output logic inexact_o
);
  // ===========
  // Parameters
  // ===========
  // These are not required as the output looks the same in both modes..
  // TODO(@stefan.mach): Generalize but why?
  localparam int unsigned PW64_BYP_W = IO_W;
  localparam int unsigned PW32_BYP_W = 2 * IO_W;
  typedef logic signed [IO_W:0] int_word_t;
  typedef logic signed [2*IO_W:0] intw_word_t;
  // Union for the two vector mode views of the stream
  typedef union packed {
    logic [PW_LEN-1:0][IO_W-1:0]   as_pw64;
    logic [HW_LEN-1:0][2*IO_W-1:0] as_pw32;  // stream pword32 by definition 2x wide elements
  } stream_data_t;

  // Constants for integer clipping (all signed because of comparison of unsigned output)
  localparam int signed MAX_VAL_INT8   =    127;
  localparam int signed MIN_VAL_INT8   =   -128;
  localparam int signed MAX_VAL_UINT8  =    255;
  localparam int signed MIN_VAL_UINT8  =      0;

  localparam int signed MAX_VAL_INT16  =  32767;
  localparam int signed MIN_VAL_INT16  = -32768;
  localparam int signed MIN_VAL_UINT16 =      0;

  // ==================
  // Beat Counting FSM
  // ==================
  // FSM state
  logic beat_cntr_ena;
  logic [1:0] beat_cntr_q, beat_cntr_d;

  always_comb begin : comb_main_fsm
    // Default assignments
    fmt_rdy_o     = 1'b0;
    out_lst_o     = 1'b0;
    beat_cntr_ena = 1'b0;
    beat_cntr_d   = beat_cntr_q;
    // Wait for successful handshake
    if (out_vld_o && out_rdy_i) begin
      beat_cntr_ena = 1'b1;
      // According to format and state, decide when to ack request, update state
      unique case (fmt_i)
        FMT_INT, FMT_BYP:  fmt_rdy_o = 1'b1;  // 1 beat
        FMT_INTW, FMT_F16: fmt_rdy_o = beat_cntr_q == (operand_vm_i ? 0 : 1);  // 2/1 beats
        FMT_F24:           fmt_rdy_o = beat_cntr_q == 2;  // 3 beats
        FMT_F32:           fmt_rdy_o = beat_cntr_q == (operand_vm_i ? 1 : 3);  // 4/2 beats
        default:           fmt_rdy_o = 1'b1;  // default ready
      endcase
      out_lst_o   = fmt_rdy_o & fmt_last_i;  // Set last flag only on last beat
      beat_cntr_d = fmt_rdy_o ? 0 : beat_cntr_q + 1;  // reset beat counter after last beat
    end
  end
  // FSM and data regs
  //`FFL(beat_cntr_q, beat_cntr_d, beat_cntr_ena, '0, clk_i, rst_ni)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      beat_cntr_q <= '0;
    end else begin
      if (beat_cntr_ena) begin
        beat_cntr_q <= beat_cntr_d;
      end
    end
  end

  // ===================
  // Input Preparation
  // ==================
  // FP24 beats don't line up with the PWORD boundaries, some elements are partially transmitted
  // over two consecutive beats, so the same element needs to be computed twice
  // TODO(@stefan.mach): Generalize to other PW_LEN and ratios

  // Shorthand control to enable conversion paths, gate data off otherwise to save on switching
  logic fp18_int_ena, fp18_intw_ena, fp18_fp16_ena, fp18_fp24_ena, fp18_fp32_ena, fp18_byp_ena;
  assign fp18_int_ena  = fmt_vld_i & (fmt_i == FMT_INT);
  assign fp18_intw_ena = fmt_vld_i & (fmt_i == FMT_INTW);
  assign fp18_fp16_ena = fmt_vld_i & (fmt_i == FMT_F16);
  assign fp18_fp24_ena = fmt_vld_i & (fmt_i == FMT_F24);
  assign fp18_fp32_ena = fmt_vld_i & (fmt_i == FMT_F32);
  assign fp18_byp_ena  = fmt_vld_i & (fmt_i == FMT_BYP);
  // Conversion data path inputs
  pw_dpu_fp_t in_data, in_fp18_int;
  hw_dpu_fp_t in_data_half, in_fp18_intw, in_fp18_fp16;
  tw_dpu_fp_t in_data_third, in_fp18_fp24;
  qw_dpu_fp_t in_data_quarter, in_fp18_fp32;
  stream_data_t byp_out;  // vm-dependent!

  // Select input data to conversions according to current beat and format
  always_comb begin : prepare_conv_inputs
    // Default assignment: silence conv input data
    // FP24 has 22 conversion units, but addresses them as if there were 21 to convert the element
    // which needs to be split across 2 beats twice (once as topmost, once as bottommost).
    in_data = in_data_i;
    foreach (in_data_half[i]) in_data_half[i] = in_data_i[HW_LEN*(beat_cntr_q%2)+i];
    foreach (in_data_third[i]) in_data_third[i] = in_data_i[(PW_LEN/3)*(beat_cntr_q%3)+i];
    foreach (in_data_quarter[i]) in_data_quarter[i] = in_data_i[QW_LEN*beat_cntr_q+i];
    // Inputs to conversion blocks
    in_fp18_int  = '0;
    in_fp18_intw = '0;
    in_fp18_fp16 = '0;
    in_fp18_fp24 = '0;
    in_fp18_fp32 = '0;
    byp_out      = '0;  // direcly compute output

    // Assign conv datapath inputs if active - one-hot!
    unique case (1'b1)  // will raise sim error if not one-hot!
      fp18_int_ena: begin
        in_fp18_int = in_data;
        // INTW units used as well to convert INT, INTW is INT with sign-extension
        foreach (in_fp18_intw[i]) in_fp18_intw[i] = in_fp18_int[i];
      end
      fp18_intw_ena: in_fp18_intw = in_data_half;
      fp18_fp16_ena: in_fp18_fp16 = in_data_half;
      fp18_fp24_ena: begin
        in_fp18_fp24 = in_data_third;
        // FP32 units used as well to convert FP24, FP24 is FP32 without the lowest byte
        foreach (in_fp18_fp32[i]) in_fp18_fp32[i] = in_fp18_fp24[i];
      end
      fp18_fp32_ena: in_fp18_fp32 = in_data_quarter;
      // The only place where VM matters at the output?
      fp18_byp_ena: begin
        if (operand_vm_i) foreach (byp_out.as_pw32[i]) byp_out.as_pw32[i] = in_data[i];
        else foreach (byp_out.as_pw64[i]) byp_out.as_pw64[i] = in_data[i];
      end
      default: ;  // use defaults
    endcase
  end


  // ======================
  // Input Data Conversion
  // ======================
  // Conversion data path outputs
  beat_fp16_t   fp18_fp16_out;
  beat_fp24_t   fp18_fp24_out;
  beat_fp32_t   fp18_fp32_out;
  // We don't care about the stream layout, hardcoded output width of 8 densely packed!
  stream_data_t int_out;   // only in pw64 mode - no check here but decoder swaps pw32 int to intw
  stream_data_t intw_out;  // only happens as pw32 - decoder swaps pw to pw32 for intw
  stream_data_t fp16_out;  // as pw64 equivalent to pw32 as IO_W is fully used
  stream_data_t fp24_out;  // as pw64 equivalent to pw32 as IO_W is fully used
  stream_data_t fp32_out;  // as pw64 equivalent to pw32 as IO_W is fully used

  // Conversion status flags
  logic [PW_LEN-1:0] int_of, int_uf, int_nx;
  logic [HW_LEN-1:0] intw_of, intw_uf, intw_nx;
  logic [HW_LEN-1:0] fp16_of, fp16_uf, fp16_nx;
  logic [TW_LEN-1:0] fp24_of, fp24_uf, fp24_nx;
  logic [QW_LEN-1:0] fp32_of, fp32_uf, fp32_nx;
  logic int_of_masked, int_uf_masked, int_nx_masked;
  logic intw_of_masked, intw_uf_masked, intw_nx_masked;
  logic fp16_of_masked, fp16_uf_masked, fp16_nx_masked;
  logic fp24_of_masked, fp24_uf_masked, fp24_nx_masked;
  logic fp32_of_masked, fp32_uf_masked, fp32_nx_masked;

  // FP18 -> INT, along with the INTW units, used for the remaining FP18 -> INT casts
  for (genvar i = HW_LEN; unsigned'(i) < PW_LEN; ++i) begin : gen_FP_INT
    int_word_t  int_sgn;
    dw_status_t dw_status;
    logic int_clip_p, int_clip_n;
    DW_fp_flt2i #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .isize(IO_W + 1),
      .ieee_compliance(DW_IEEE_COMPL)
    ) i_flt2i (
      .a     (in_fp18_int[i]),
      .rnd   (DW_RND_RNE),
      .z     (int_sgn),
      .status(dw_status) // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );

    // Take care of signed/unsigned switching clipping
    always_comb begin : proc_int_clipping
      int_out.as_pw64[i] = IO_W'(int_sgn);
      int_clip_p         = 1'b0;
      int_clip_n         = 1'b0;

      if (cfg_int_signed_i && (int_sgn > int_word_t'(MAX_VAL_INT8))) begin
        // Largest int8
        int_out.as_pw64[i] = IO_W'(MAX_VAL_INT8);
        int_clip_p         = 1'b1;
      end else if (cfg_int_signed_i && (int_sgn < int_word_t'(MIN_VAL_INT8))) begin
        // Smallest int8
        int_out.as_pw64[i] = IO_W'(MIN_VAL_INT8);
        int_clip_n         = 1'b1;
      end else if (!cfg_int_signed_i && (int_sgn < int_word_t'(MIN_VAL_UINT8))) begin
        // Smallest uint8
        int_out.as_pw64[i] = IO_W'(MIN_VAL_UINT8);
        int_clip_n         = 1'b1;
      end
    end

    always_comb int_of[i] = dw_status.huge_int | int_clip_p | int_clip_n;
    always_comb int_uf[i] = dw_status.tiny | (dw_status.zero & dw_status.inexact);
    always_comb int_nx[i] = dw_status.inexact | int_clip_n | int_clip_p;
  end
  // Also for the ones driven from INTW
  always_comb int_of_masked = |int_of & fp18_int_ena;
  always_comb int_uf_masked = |int_uf & fp18_int_ena;
  always_comb int_nx_masked = |int_nx & fp18_int_ena;

  // FP18 -> INTW, also used for the lower 32 FP18 -> INT casts
  for (genvar i = 0; unsigned'(i) < HW_LEN; ++i) begin : gen_FP_INTW
    intw_word_t intw_sgn;
    dw_status_t dw_status;
    logic intw_clip_p, intw_clip_n;
    logic int_clip_p, int_clip_n;
    DW_fp_flt2i #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .isize(2 * IO_W + 1),
      .ieee_compliance(DW_IEEE_COMPL)
    ) i_flt2i (
      .a     (in_fp18_intw[i]),
      .rnd   (DW_RND_RNE),
      .z     (intw_sgn),
      .status(dw_status) // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );

    // Take care of signed/unsigned clipping
    always_comb begin : proc_intw_clip
      intw_out.as_pw32[i] = (2*IO_W)'(intw_sgn);
      intw_clip_p         = 1'b0;
      intw_clip_n         = 1'b0;

      if (cfg_int_signed_i && (intw_sgn > intw_word_t'(MAX_VAL_INT16))) begin
        // Largest int16
        intw_out.as_pw32[i] = (2*IO_W)'(MAX_VAL_INT16);
        intw_clip_p         = 1'b1;
      end else if (cfg_int_signed_i && (intw_sgn < intw_word_t'(MIN_VAL_INT16))) begin
        // Smallest int16
        intw_out.as_pw32[i] = (2*IO_W)'(MIN_VAL_INT16);
        intw_clip_n         = 1'b1;
      end else if (!cfg_int_signed_i && (intw_sgn < intw_word_t'(MIN_VAL_UINT16))) begin
        // Smallest uint16
        intw_out.as_pw32[i] = (2*IO_W)'(MIN_VAL_UINT16);
        intw_clip_n         = 1'b1;
      end
    end

    assign intw_of[i] = dw_status.huge_int | intw_clip_p | intw_clip_n;
    assign intw_uf[i] = dw_status.tiny | (dw_status.zero & dw_status.inexact);
    assign intw_nx[i] = dw_status.inexact | intw_clip_n | intw_clip_p;
    // Pack back the INT results
    always_comb begin : proc_int_clip
      int_out.as_pw64[i] = IO_W'(intw_sgn);
      int_clip_p         = 1'b0;
      int_clip_n         = 1'b0;

      if (cfg_int_signed_i && (intw_sgn > intw_word_t'(MAX_VAL_INT8))) begin
        // Largest int8
        int_out.as_pw64[i] = IO_W'(MAX_VAL_INT8);
        int_clip_p         = 1'b1;
      end else if (cfg_int_signed_i && (intw_sgn < intw_word_t'(MIN_VAL_INT8))) begin
        // Smallest int8
        int_out.as_pw64[i] = IO_W'(MIN_VAL_INT8);
        int_clip_n         = 1'b1;
      end else if (!cfg_int_signed_i && (intw_sgn > intw_word_t'(MAX_VAL_UINT8))) begin
        // Largest uint8
        int_out.as_pw64[i] = IO_W'(MAX_VAL_UINT8);
        int_clip_p         = 1'b1;
      end else if (!cfg_int_signed_i && (intw_sgn < intw_word_t'(MIN_VAL_UINT8))) begin
        // Smallest uint8
        int_out.as_pw64[i] = IO_W'(MIN_VAL_UINT8);
        int_clip_n         = 1'b1;
      end
    end

    assign int_of[i] = intw_of[i] | int_clip_p | int_clip_n;
    assign int_uf[i] = intw_uf[i];
    assign int_nx[i] = intw_nx[i] | int_clip_n | int_clip_p;
  end
  assign intw_of_masked = |intw_of & fp18_intw_ena;
  assign intw_uf_masked = |intw_uf & fp18_intw_ena;
  assign intw_nx_masked = |intw_nx & fp18_intw_ena;

  // FP18 -> FP16
  for (genvar i = 0; unsigned'(i) < HW_LEN; ++i) begin : gen_FP_F16
    dpu_dp_f2f_cast #(
      .src_fp_t(dpu_fp_t),
      .dst_fp_t(fp16_t)
    ) i_fp18_fp16 (
      .src_i      (in_fp18_fp16[i]),
      .dst_o      (fp18_fp16_out[i]),
      .overflow_o (fp16_of[i]),
      .underflow_o(fp16_uf[i]),
      .inexact_o  (fp16_nx[i])
    );
  end
  assign fp16_out       = fp18_fp16_out;  // same for both vm
  assign fp16_of_masked = |fp16_of & fp18_fp16_ena;
  assign fp16_uf_masked = |fp16_uf & fp18_fp16_ena;
  assign fp16_nx_masked = |fp16_nx & fp18_fp16_ena;

  // FP18 -> FP24, along with the FP32 units, used for the remaining FP18 -> FP24 casts
  dpu_dp_f2f_cast #(
    .src_fp_t(dpu_fp_t),
    .dst_fp_t(fp24_t)
  ) i_fp18_fp24[TW_LEN-1:QW_LEN] (
    .src_i      (in_fp18_fp24[TW_LEN-1:QW_LEN]),
    .dst_o      (fp18_fp24_out[TW_LEN-1:QW_LEN]),
    .overflow_o (fp24_of[TW_LEN-1:QW_LEN]),
    .underflow_o(fp24_uf[TW_LEN-1:QW_LEN]),
    .inexact_o  (fp24_nx[TW_LEN-1:QW_LEN])
  );
  // There is one more FP24 value than fit into the output stream, and the bottommost FP24 value is
  // the previous topmost value. The topmost elements that don't fit are just clipped off, and the
  // remainder topmost elements from the previous beat are sent as the lowest: b0: 0, b1: 2, b2: 1
  // TODO(@stefan.mach): Hardcoded. --> explicit 3:1 MUX and generic in IO_W?
  assign fp24_out       = (PW_LEN*IO_W)'(fp18_fp24_out >> 8 * ((beat_cntr_q) % 3));  // >>0, >>1, >>2
  assign fp24_of_masked = |fp24_of & fp18_fp24_ena;  // TODO(@stefan.mach): no IRQ
  assign fp24_uf_masked = |fp24_uf & fp18_fp24_ena;  // TODO(@stefan.mach): no IRQ
  assign fp24_nx_masked = |fp24_nx & fp18_fp24_ena;  // TODO(@stefan.mach): no IRQ

  // FP18 -> FP32, also used for the lower 16 FP18 -> FP24
  for (genvar i = 0; unsigned'(i) < QW_LEN; ++i) begin : gen_FP_F32
    dpu_dp_f2f_cast #(
      .src_fp_t(dpu_fp_t),
      .dst_fp_t(fp32_t)
    ) i_fp18_fp32 (
      .src_i      (in_fp18_fp32[i]),
      .dst_o      (fp18_fp32_out[i]),
      .overflow_o (fp32_of[i]),        // TODO(@stefan.mach): Remove IRQ, never set in upcast
      .underflow_o(fp32_uf[i]),        // TODO(@stefan.mach): Remove IRQ, never set in upcast
      .inexact_o  (fp32_nx[i])         // TODO(@stefan.mach): Remove IRQ, never set in upcast
    );
    // Pack back the FP24 results, FP24 is just FP32 missing the lowest byte
    assign fp18_fp24_out[i] = fp24_t'(fp18_fp32_out[i] >> 8);
    assign fp24_of[i]       = fp32_of[i];
    assign fp24_uf[i]       = fp32_uf[i];
    assign fp24_nx[i]       = fp32_nx[i];
  end
  assign fp32_out       = fp18_fp32_out;
  assign fp32_of_masked = |fp32_of & fp18_fp32_ena;
  assign fp32_uf_masked = |fp32_uf & fp18_fp32_ena;
  assign fp32_nx_masked = |fp32_nx & fp18_fp32_ena;


  // ============================
  // Conversion Result Selection
  // ============================
  // Select conversion result according to format,
  always_comb begin : result_sel_mux
    unique case (fmt_i)
      FMT_INT:  out_data_o = int_out;
      FMT_F16:  out_data_o = fp16_out;
      FMT_F24:  out_data_o = fp24_out;
      FMT_F32:  out_data_o = fp32_out;
      FMT_INTW: out_data_o = intw_out;
      FMT_BYP:  out_data_o = byp_out;
      default:  out_data_o = byp_out;
    endcase
  end
  assign out_vld_o = fmt_vld_i;

  // Status outputs
  assign overflow_o  = int_of_masked | intw_of_masked | fp16_of_masked | fp24_of_masked | fp32_of_masked;
  assign underflow_o = int_uf_masked | intw_uf_masked | fp16_uf_masked | fp24_uf_masked | fp32_uf_masked;
  assign inexact_o   = int_nx_masked | intw_nx_masked | fp16_nx_masked | fp24_nx_masked | fp32_nx_masked;

endmodule
