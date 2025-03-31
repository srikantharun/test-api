// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Input streams (IAU and IFD1) conversion block based on fmt
// from int8/int32, fp16, fp24, and fp32 to fp18
//
// Input data beat is fed through format conversion units in parallel. The appropriate path is
// then selected to be applied to the ID/ISS interface (spill register). Multi-Beat operations
// will only write a portion of the spill registers in each beat, and the transaction is
// considered complete once all spill registers have been filled.
//
// The width of the spill register slices are such that 1/2, 1/3, and 1/4 of the entire DPU-facing
// PWORD can be filled at one time to sink each converted stream beat. In case PW_LEN is not
// divisible by the number of elements in a higher-precision value (e.g. FP24 needs 3 beats, and
// 64/3 = 21.333), a register for the remainder number of elements is required to store them until
// the value can be assembled from the next beat. The spill register slices thus look as follows:
// 63                                                                    0  PW element index
// |       16       |   6  |    10    |     11    |  5  |       16       |
//        sl5         sl4      sl3         sl2     sl1         sl0
// And the respective formats enable the slices as follows during their processing beats:
// INT8/32: sl0-5                         (64 elements each)
//    FP16: sl0-2 | sl3-5                 (32 elements each)
//    FP24: sl0-1 | sl2-3 | sl4-5         (21|21|22 elements)
//    FP32: sl0   | sl1-2 | sl3-4 | sl5   (16 elements each)
//
// As the DPU can serve as a cross-over point between vector modes, vector mode switching requires
// two vm annotations: one for the stream data (pw64/32 packing = using 1 or 2 elements), and one
// for the DPU-internal data (pw64/32 packing = using 64 or 32 FP18 values).
//
// WARNING: This module is not fully parametric in `PW_LEN` due to the addition of FP24 which
// requires partial values on stream beats as 64/3 = 21.333.
// TODO(@stefan.mach): In another life, generalize this to handle other PW lengths and have a more general behavior. Many fmt + vm combinations are hardcoded and irregluar
//
// Owner: Stefan Mach <stefan.mach@axelera.ai>

module dpu_dp_in_stream
  import dpu_pkg::*;
#(
  parameter int unsigned WordWidth    = 32,
  // TODO(@stefan.mach): PW32 ints are not always 2x WordWidth. Find unified approach across AIC
  parameter int unsigned WideIntWidth = 48
) (
  input wire clk_i,  // Clock
  input wire rst_ni, // Reset active low

  // Input Stream
  input  logic [PW_LEN-1:0][WordWidth-1:0] in_data_i,  // Input
  input  logic                             in_vld_i,
  input  logic                             in_last_i,
  output logic                             in_rdy_o,

  // Output Data
  output pw_dpu_fp_t out_data_o,  // Output
  output logic       out_vld_o,
  input  logic       out_rdy_i,

  // Conversion request
  input  stream_fmt_e  fmt_i,             // Format
  input  vector_mode_e stream_vm_i,       // Vector mode used for stream layout [e.g. @8/32, @16/64]
  input  vector_mode_e operand_vm_i,      // Vector mode of the data we produce [e.g. pword64]
  input  logic         peek_i,            // Only peek the input - next read will see the same data
  input  logic         fmt_vld_i,
  output logic         fmt_rdy_o,
  output logic         last_o,            // asserted with fmt_rdy_o
  output logic         illegal_vm_fmt_o,  // illegal format for stream layout VM
  output logic         stream_error_o,    // asserted whenever the error occurs
  output logic         stream_stalled_o,  // asserted when we want to read but there's no valid data

  // CSR configuration
  input logic cfg_int_signed_i,

  // Conversion Status for IRQ - not synchonized with the output data, goes high on internal status
  output logic overflow_o,
  output logic underflow_o,
  output logic inexact_o
);
  // ===========
  // Parameters
  // ===========
  localparam int unsigned PW64_BYP_W = IO_W;
  localparam int unsigned PW32_BYP_W = 2 * IO_W;
  typedef logic signed [WordWidth:0] int_word_t;
  typedef logic signed [WideIntWidth:0] intw_word_t;
  // Union for the two vector mode views of the stream
  typedef union packed {
    logic [PW_LEN-1:0][WordWidth-1:0]   as_pw64;
    logic [HW_LEN-1:0][2*WordWidth-1:0] as_pw32;  // stream pword32 by definition 2x wide elements
  } stream_data_t;


  // ==================
  // Beat Counting FSM
  // ==================
  // Conversion only happens the first time a DPU-facing PWORD needs to be produced. If a peek
  // happens, subsequent accesses (peeks or pops) don't trigger the conversion again and the output
  // data stays in the ID/ISS pipe register.
  logic use_prev_data;
  // A sticky flop is set once a peek operation is completed, and cleared when a pop occurs.
  // FFL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) use_prev_data <= 1'b0;
    else if (fmt_vld_i & fmt_rdy_o) use_prev_data <= peek_i;
  end

  // Handshakes with downstream spill registers, and format-dependent mask for which to use. The
  // hold-over register is required for formats that don't cleanly divide the PWORD length.
  logic conv_ena, hold_reg_ena;
  logic [5:0] conv_vld, conv_rdy, conv_mask;
  // FSM state
  logic beat_cntr_ena;
  logic [1:0] beat_cntr_q, beat_cntr_d;

  always_comb begin : comb_main_fsm
    // Default assignments
    in_rdy_o       = 1'b0;
    fmt_rdy_o      = 1'b0;
    conv_ena       = 1'b0;
    hold_reg_ena   = 1'b0;
    conv_vld       = 6'b000000;
    last_o         = 1'b0;
    stream_error_o = 1'b0;
    beat_cntr_ena  = 1'b0;
    beat_cntr_d    = beat_cntr_q;
    // Set appropriate spill reg handshake mask according to format and beat #
    unique case (fmt_i)
      FMT_INT, FMT_BYP: conv_mask = 6'b111111;
      FMT_INTW, FMT_F16: conv_mask = 6'b000_111 << 3 * beat_cntr_q;
      FMT_F24: conv_mask = 6'b00_00_11 << 2 * beat_cntr_q;
      FMT_F32: conv_mask = (7'b0_00_00_1_1 << 2 * beat_cntr_q) >> 1;  // 0, 1&2, 3&4, 5
      default: conv_mask = 6'b000000;
    endcase
    // Limit to half of the datapath if pword32 requested
    if (operand_vm_i) conv_mask &= 6'b000111;
    // Wait for conversion request
    if (fmt_vld_i) begin
      // If possible, serve the request using the result from a previous peek
      if (use_prev_data) fmt_rdy_o = 1'b1;
      // Otherwise: Wait for valid input stream
      else if (in_vld_i) begin
        // Enable data paths to appropriate conversion units - gated off otherwise
        conv_ena = 1'b1;
        // Wait for all required slots to be ready to accept new data. Thanks to default-ready
        // behavior of spill_register, we can check for needed readies here
        if (&(conv_rdy | ~conv_mask)) begin
          // Accept the beat and push the conversion result into the appropriate spill regs
          in_rdy_o      = 1'b1;
          conv_vld      = conv_mask;
          beat_cntr_ena = 1'b1;
          // According to format, operand vector mode, and state, decide when to ack request, update
          // state and catch errors. The last to the ID stage is masked for stream errors, as such
          // it will seem as if TLAST has never occured and the block will stall until sufficient
          // stream beats are provided to complete the operation (e.g. from a subsequent stream).
          // This keeps the ID and the stream converters in synch as we can't flush half-executed
          // operations for now, and RFS won't terminate in the middle of an incomplete transfer.
          // TODO(@stefan.mach): Rethink whether we can now propagate last on errors
          unique case (fmt_i)
            FMT_INT, FMT_BYP:  fmt_rdy_o = 1'b1;  // 1 beat
            FMT_INTW, FMT_F16: fmt_rdy_o = beat_cntr_q == (operand_vm_i ? 0 : 1);  // 2/1 beats
            FMT_F24:           fmt_rdy_o = beat_cntr_q == 2;  // 3 beats
            FMT_F32:           fmt_rdy_o = beat_cntr_q == (operand_vm_i ? 1 : 3);  // 4/2 beats
            default:           fmt_rdy_o = 1'b1;  // default ready
          endcase
          last_o         = fmt_rdy_o & in_last_i;
          beat_cntr_d    = fmt_rdy_o ? 0 : beat_cntr_q + 1;  // reset beat counter after last beat
          hold_reg_ena   = (fmt_i == FMT_F24) && ~fmt_rdy_o;  // hold register first two F24 beats
          stream_error_o = in_last_i & ~fmt_rdy_o;
        end
      end
    end
  end
  // FSM regs
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

  // Stream is considered stalled if we want to read data (and are NOT backpressured), but there is
  // no valid data available
  assign stream_stalled_o = fmt_vld_i & ~use_prev_data & (&(conv_rdy | ~conv_mask)) & ~in_vld_i;


  // =============================
  // Input Preparation & Holdover
  // =============================
  // Shorthand control to enable conversion paths, gate data off otherwise to save on switching
  logic int_fp18_ena, intw_fp18_ena, fp16_fp18_ena, fp24_fp18_ena, fp32_fp18_ena, byp_fp18_ena, sgn;
  assign int_fp18_ena = conv_ena & (fmt_i == FMT_INT);
  assign intw_fp18_ena = conv_ena & (fmt_i == FMT_INTW);
  assign fp16_fp18_ena = conv_ena & (fmt_i == FMT_F16);
  assign fp24_fp18_ena = conv_ena & (fmt_i == FMT_F24);
  assign fp32_fp18_ena = conv_ena & (fmt_i == FMT_F32);
  assign byp_fp18_ena = conv_ena & (fmt_i == FMT_BYP);
  assign sgn = cfg_int_signed_i;  // short hand signedness config

  // Conversion data path inputs - beats are just [partial] PWORDs
  stream_data_t in_data;  // Input data after modifications if needed
  int_word_t [PW_LEN-1:0] in_int, in_int_vm64;  // i8@8 / i32@32 - only defined for one stream vm
  intw_word_t [HW_LEN-1:0] in_intw, in_intw_vm32;  // pword32i16/48 - dito
  beat_fp16_t in_fp16;  // pword32fp16
  beat_fp24_t in_fp24;  // pword22fp24
  beat_fp32_t in_fp32;  // pword16fp32
  // TODO(@stefan.mach): typedef these in pkg
  logic [PW_LEN-1:0][PW64_BYP_W-1:0] in_byp, in_byp_vm64;  // pword64b8
  logic [HW_LEN-1:0][PW32_BYP_W-1:0] in_byp_vm32;  // pword32b16
  pw_dpu_fp_t byp_fp18_out;  // pw64 - NOTE: bypass with changing vm is not supported, only use 64

  // FP24 beats don't line up with the PWORD boundaries, and up to two top i8 elements at the input
  // must be held to contribute to the next beat's conversion.
  // TODO(@stefan.mach): Generalize to other PW_LEN and ratios - but this should work for what we do
  logic [1:0][PW64_BYP_W-1:0] held_in_data;
  // FFLNR: D-Flip-Flop, load enable, no reset
  always_ff @(posedge clk_i) begin
    if (hold_reg_ena) begin
      held_in_data <= stream_vm_i ? in_byp_vm32[HW_LEN-1-:1] : in_byp_vm64[PW_LEN-1-:2];
    end
  end

  // Unpack stream according to stream VM (the @xx), combine input data with held data if necessary
  always_comb begin : prepare_conv_inputs
    // Default assignment: silence conv input data
    in_data          = in_data_i;
    // Inputs to conversion blocks
    in_int           = '0;
    in_intw          = '0;
    in_fp16          = '0;
    in_fp24          = '0;
    in_fp32          = '0;
    byp_fp18_out     = '0;  // direcly compute output
    // This feature is a bit of a mess, some combinations don't work - just throw an error, but it
    // should actually be caught in decode already.
    illegal_vm_fmt_o = 1'b0;

    // Unpack as int and bypass formats for further use
    // PW64 vector mode layout with @WordWidth aligned elements
    for (int unsigned i = 0; i < PW_LEN; ++i) begin
      // pword64i8@8 / pword64i32@32
      in_int_vm64[i] = signed'({sgn & in_data.as_pw64[i][WordWidth-1], in_data.as_pw64[i]});
      // pword64b8@8 / pword64b8@32 - Bypass-packed formats all unpack the same data structure
      in_byp_vm64[i] = in_data.as_pw64[i][PW64_BYP_W-1:0];
    end
    // PW32 vector mode layout with @2*WordWidth aligned elements
    for (int unsigned i = 0; i < HW_LEN; ++i) begin
      // pword32i8@16 / pword32i32@64
      in_intw_vm32[i] = signed'({
        sgn & in_data.as_pw32[i][WideIntWidth-1], in_data.as_pw32[i][WideIntWidth-1:0]
      });
      // pword32b8@16 / pword32b8@64 - Bypass-packed formats all unpack the same data structure
      in_byp_vm32[i] = in_data.as_pw32[i][PW32_BYP_W-1:0];
    end

    // Actually ungate the individual conv paths if needed
    // TODO(@stefan.mach): This could be a single case, but it is hard enough to understand as-is without ternary vm switches in every item
    if (stream_vm_i) begin
      // PW32 vector mode layout with @2*WordWidth aligned elements
      // Assign conv datapath inputs if active - one-hot!
      unique case (1'b1)  // will raise sim error if not one-hot!
        // pword64i8@16 & pword64i32@64
        int_fp18_ena: illegal_vm_fmt_o = 1'b1;  // packing i8/16 in pw32 layout not defined
        // pword32i16[@16] & pword32i48@64
        intw_fp18_ena: in_intw = in_intw_vm32;
        // pword32fp16@16 - bypass packed
        fp16_fp18_ena: in_fp16 = in_byp_vm32;
        // pword22fp24@16 - bypass packed
        // FP24 draws N topmost bytes from the previous input as its lowest: b0: 0, b1: 2, b2: 1
        fp24_fp18_ena: begin
          // in_fp24 = {in_byp_vm32, held_in_data} >> PW64_BYP_W * ((3'(beat_cntr_q) + 2) % 3);  // >>2, >>0, >>1
          unique case (1'b1)  // should give sim error if fp24_fp18_ena && beat_cntr_q > 2, and opt.
            (beat_cntr_q == 0): in_fp24 = in_byp_vm32;
            (beat_cntr_q == 1): in_fp24 = {in_byp_vm32, held_in_data};
            (beat_cntr_q == 2): in_fp24 = {in_byp_vm32, held_in_data[1]};
            default: ;
          endcase
          // FP32 units used as well to convert FP24, FP24 is FP32 without the lowest byte
          foreach (in_fp32[i]) in_fp32[i] = {in_fp24[i], 8'h0};
        end
        // pword16fp32@16 - bypass packed
        fp32_fp18_ena: in_fp32 = in_byp_vm32;
        // pword16fp32@16 - bypass packed, upper half of PW remains 0 (we never switch VM in bypass)
        byp_fp18_ena: foreach (in_byp_vm32[i]) byp_fp18_out[i] = dpu_fp_t'(in_byp_vm32[i]);
        // Silence all by default
        default: ;
      endcase
    end else begin
      // PW64 vector mode layout with @WordWidth aligned elements
      // Assign conv datapath inputs if active - one-hot!
      unique case (1'b1)  // will raise sim error if not one-hot!
        // pword64i8[@8] & pword64i32[@32]
        int_fp18_ena: begin
          in_int = in_int_vm64;
          // INTW units used as well to convert INT, INTW is INT with sign-extension
          foreach (in_intw[i]) in_intw[i] = signed'(in_int[i]);  // should already be signed!
        end
        // pword32i16@8 & pword32i48@32
        intw_fp18_ena: illegal_vm_fmt_o = 1'b1;  // packing i16/48 in pw64 layout not defined
        // pword32fp16@8 - bypass packed
        fp16_fp18_ena: in_fp16 = in_byp_vm64;
        // pword22fp24@8 - bypass packed
        // FP24 draws N topmost bytes from the previous input as its lowest: b0: 0, b1: 2, b2: 1
        fp24_fp18_ena: begin
          // in_fp24 = {in_byp_vm64, held_in_data} >> PW64_BYP_W * ((3'(beat_cntr_q) + 2) % 3);  // >>2, >>0, >>1
          unique case (1'b1)  // should give sim error if fp24_fp18_ena && beat_cntr_q > 2, and opt.
            (beat_cntr_q == 0): in_fp24 = in_byp_vm32;
            (beat_cntr_q == 1): in_fp24 = {in_byp_vm32, held_in_data};
            (beat_cntr_q == 2): in_fp24 = {in_byp_vm32, held_in_data[1]};
            default: ;
          endcase
          // FP32 units used as well to convert FP24, FP24 is FP32 without the lowest byte
          foreach (in_fp32[i]) in_fp32[i] = {in_fp24[i], 8'h0};
        end
        // pword16fp32@8 - bypass packed
        fp32_fp18_ena: in_fp32 = in_byp_vm64;
        // pword16fp32@8 - bypass packed
        byp_fp18_ena: foreach (in_byp_vm64[i]) byp_fp18_out[i] = dpu_fp_t'(in_byp_vm64[i]);
        // Silence all by default
        default: ;
      endcase
    end
  end


  // ======================
  // Input Data Conversion
  // ======================
  // Conversion data path outputs
  pw_dpu_fp_t int_fp18_out;  //pw64
  hw_dpu_fp_t intw_fp18_out;  // pw32
  hw_dpu_fp_t fp16_fp18_out;  // pw32
  tw_dpu_fp_t fp24_fp18_out;  // pw22
  qw_dpu_fp_t fp32_fp18_out;  // pw16
  // Conversion status flags
  logic [PW_LEN-1:0] int_fp18_of, int_fp18_nx;
  logic [HW_LEN-1:0] intw_fp18_of, intw_fp18_nx;
  logic [QW_LEN-1:0] fp32_fp18_of, fp32_fp18_uf, fp32_fp18_nx;
  logic [TW_LEN-1:0] fp24_fp18_of, fp24_fp18_uf, fp24_fp18_nx;
  logic [HW_LEN-1:0] fp16_fp18_of, fp16_fp18_uf, fp16_fp18_nx;  // TODO(@stefan.mach): no irq
  logic int_fp18_of_masked, int_fp18_nx_masked;
  logic intw_fp18_of_masked, intw_fp18_nx_masked;
  logic fp32_fp18_of_masked, fp32_fp18_uf_masked, fp32_fp18_nx_masked;
  logic fp24_fp18_of_masked, fp24_fp18_uf_masked, fp24_fp18_nx_masked;
  logic fp16_fp18_of_masked, fp16_fp18_uf_masked, fp16_fp18_nx_masked;

  // INT -> FP18, along with the INTW units, used for the remaining INT -> FP18 casts
  for (genvar i = HW_LEN; unsigned'(i) < PW_LEN; ++i) begin : gen_INT_FP
    dw_status_t int_fp18_status;
    DW_fp_i2flt #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .isize    (WordWidth + 1),
      .isign    (1)
    ) i_i2flt (
      .a     (in_int[i]),
      .rnd   (DW_RND_RNE),
      .z     (int_fp18_out[i]),
      .status(int_fp18_status) // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    assign int_fp18_of[i] = int_fp18_status.huge | int_fp18_status.infinity;
    assign int_fp18_nx[i] = int_fp18_status.inexact;
  end
  // Also for the ones driven from INTW
  assign int_fp18_of_masked = |int_fp18_of & int_fp18_ena;
  assign int_fp18_nx_masked = |int_fp18_nx & int_fp18_ena;

  // INTW -> FP18, also used for the lower 32 INT -> FP18 casts
  for (genvar i = 0; unsigned'(i) < HW_LEN; ++i) begin : gen_INTW_FP
    dw_status_t intw_fp18_status;
    DW_fp_i2flt #(
      .sig_width(DPU_FPT_SIGW),
      .exp_width(DPU_FPT_EXPW),
      .isize    (WideIntWidth + 1),
      .isign    (1)
    ) i_i2flt (
      .a     (in_intw[i]),
      .rnd   (DW_RND_RNE),
      .z     (intw_fp18_out[i]),
      .status(intw_fp18_status) // ASO-UNUSED_VARIABLE : Not all values of the status are observed
    );
    assign intw_fp18_of[i] = intw_fp18_status.huge | intw_fp18_status.infinity;
    assign intw_fp18_nx[i] = intw_fp18_status.inexact;
    // Pack back the INT results
    assign int_fp18_out[i] = intw_fp18_out[i];
    assign int_fp18_of[i]  = intw_fp18_of[i];
    assign int_fp18_nx[i]  = intw_fp18_nx[i];
  end
  assign intw_fp18_of_masked = |intw_fp18_of & intw_fp18_ena;
  assign intw_fp18_nx_masked = |intw_fp18_nx & intw_fp18_ena;

  // FP16 -> FP18
  dpu_dp_f2f_cast #(
    .src_fp_t(fp16_t),
    .dst_fp_t(dpu_fp_t)
  ) i_fp16_fp18[HW_LEN-1:0] (
    .src_i      (in_fp16),
    .dst_o      (fp16_fp18_out),
    .overflow_o (fp16_fp18_of),   // TODO(@stefan.mach): Remove IRQ, never set in upcast
    .underflow_o(fp16_fp18_uf),   // TODO(@stefan.mach): Remove IRQ, never set in upcast
    .inexact_o  (fp16_fp18_nx)    // TODO(@stefan.mach): Remove IRQ, never set in upcast
  );
  assign fp16_fp18_of_masked = |fp16_fp18_of & fp16_fp18_ena;
  assign fp16_fp18_uf_masked = |fp16_fp18_uf & fp16_fp18_ena;
  assign fp16_fp18_nx_masked = |fp16_fp18_nx & fp16_fp18_ena;

  // FP24 -> FP18, along with the FP32 units, used for the remaining FP24 -> FP18 casts
  dpu_dp_f2f_cast #(
    .src_fp_t(fp24_t),
    .dst_fp_t(dpu_fp_t)
  ) i_fp24_fp18[TW_LEN-1:QW_LEN] (
    .src_i      (in_fp24[TW_LEN-1:QW_LEN]),
    .dst_o      (fp24_fp18_out[TW_LEN-1:QW_LEN]),
    .overflow_o (fp24_fp18_of[TW_LEN-1:QW_LEN]),
    .underflow_o(fp24_fp18_uf[TW_LEN-1:QW_LEN]),
    .inexact_o  (fp24_fp18_nx[TW_LEN-1:QW_LEN])
  );
  // Also for the ones driven by FP32
  assign fp24_fp18_of_masked = |fp24_fp18_of & fp24_fp18_ena;  // TODO(@stefan.mach): mask unused 22
  assign fp24_fp18_uf_masked = |fp24_fp18_uf & fp24_fp18_ena;  // TODO(@stefan.mach): mask unused 22
  assign fp24_fp18_nx_masked = |fp24_fp18_nx & fp24_fp18_ena;  // TODO(@stefan.mach): mask unused 22

  // FP32 -> FP18, also used for the lower 16 FP24 -> FP18
  for (genvar i = 0; unsigned'(i) < QW_LEN; ++i) begin : gen_F32_FP
    dpu_dp_f2f_cast #(
      .src_fp_t(fp32_t),
      .dst_fp_t(dpu_fp_t)
    ) i_fp32_fp18 (
      .src_i      (in_fp32[i]),
      .dst_o      (fp32_fp18_out[i]),
      .overflow_o (fp32_fp18_of[i]),
      .underflow_o(fp32_fp18_uf[i]),
      .inexact_o  (fp32_fp18_nx[i])
    );
    // Pack back the FP24 results
    assign fp24_fp18_out[i] = fp32_fp18_out[i];
    assign fp24_fp18_of[i]  = fp32_fp18_of[i];
    assign fp24_fp18_uf[i]  = fp32_fp18_uf[i];
    assign fp24_fp18_nx[i]  = fp32_fp18_nx[i];
  end
  assign fp32_fp18_of_masked = |fp32_fp18_of & fp32_fp18_ena;
  assign fp32_fp18_uf_masked = |fp32_fp18_uf & fp32_fp18_ena;
  assign fp32_fp18_nx_masked = |fp32_fp18_nx & fp32_fp18_ena;


  // ============================
  // Conversion Result Selection
  // ============================
  pw_dpu_fp_t conv_data;
  // Select conversion result according to format, extend narrow ones
  always_comb begin : result_sel_mux
    unique case (fmt_i)
      FMT_INT:  conv_data = int_fp18_out;
      FMT_INTW: conv_data = {2{intw_fp18_out}};
      FMT_F16:  conv_data = {2{fp16_fp18_out}};
      FMT_F24:  conv_data = {fp24_fp18_out, fp24_fp18_out[20:0], fp24_fp18_out[20:0]};
      FMT_F32:  conv_data = {4{fp32_fp18_out}};
      FMT_BYP:  conv_data = byp_fp18_out;
      default:  conv_data = byp_fp18_out;
    endcase
  end


  // ================
  // Spill registers
  // ================
  logic [PW_LEN-1:0] spill_in_vld, spill_in_rdy;
  logic [PW_LEN-1:0] spill_out_vld;
  logic              spill_out_rdy;
  typedef struct packed {
    vector_mode_e vm;
    logic         peek;
  } info_t;
  info_t info_out;
  logic  info_out_rdy;
  // Six spill registers for the DPU-facing beat in parallel, slicing according to comment at the
  // top of this file.
  // TODO(@stefan.mach): hardcoded, use math and some brains to make it parametric
  // TODO(@stefan.mach): revert to just 6 instances with wider data
  assign spill_in_vld = {
    {16{conv_vld[5]}},
    {6{conv_vld[4]}},
    {10{conv_vld[3]}},
    {11{conv_vld[2]}},
    {5{conv_vld[1]}},
    {16{conv_vld[0]}}
  };
  // Default ready, thus we don't touch it with VM switching
  assign conv_rdy = {
    &spill_in_rdy[48+:16],
    &spill_in_rdy[42+:6],
    &spill_in_rdy[32+:10],
    &spill_in_rdy[21+:11],
    &spill_in_rdy[16+:5],
    &spill_in_rdy[0+:16]
  };

  // TODO(@stefan.mach): Shoudln't a regular stream reg be sufficient?
  // TODO(@stefan.mach): revert to just 6 instances with wider data?
  cc_stream_spill_reg #(
    .data_t(dpu_fp_t)
  ) u_spill_regs[PW_LEN-1:0] (
    .i_clk  (clk_i),
    .i_rst_n(rst_ni),
    .i_flush(1'b0),
    .i_valid(spill_in_vld),
    .o_ready(spill_in_rdy),
    .i_data (conv_data),
    .o_valid(spill_out_vld),
    .i_ready(spill_out_rdy),
    .o_data (out_data_o)
  );
  // Match the data buffering to transfer peeking decision & vector mode to the output side
  cc_stream_spill_reg #(
    .data_t(info_t)  // result VM, peek
  ) u_info_spill_reg (
    .i_clk  (clk_i),
    .i_rst_n(rst_ni),
    .i_flush(1'b0),
    .i_valid(fmt_vld_i && fmt_rdy_o),
    .o_ready(), // ASO-UNUSED_OUTPUT : Signal handled externally.
    .i_data ({operand_vm_i, peek_i}),
    .o_valid(), // ASO-UNUSED_OUTPUT : Signal handled externally.
    .i_ready(info_out_rdy),
    .o_data (info_out)
  );
  // ISS must consume the entire PWORD from all spill registers concurrently
  assign out_vld_o = &(spill_out_vld[HW_LEN-1:0]) & (&(spill_out_vld[PW_LEN-1:HW_LEN]) | info_out.vm);
  // Gate spill reg ready to only consume data on pops, keep it on peeks
  assign spill_out_rdy = ~info_out.peek & out_vld_o & out_rdy_i;
  // Peek information is consumed upon read from downstream
  assign info_out_rdy = out_vld_o & out_rdy_i;

  // Status outputs
  // TODO(@stefan.mach): Not all conversions raise flags
  assign overflow_o = fp32_fp18_of_masked | fp24_fp18_of_masked | fp16_fp18_of_masked | int_fp18_of_masked | intw_fp18_of_masked;
  assign underflow_o = fp32_fp18_uf_masked | fp24_fp18_uf_masked | fp16_fp18_uf_masked;
  assign inexact_o = fp32_fp18_nx_masked | fp24_fp18_nx_masked | fp16_fp18_nx_masked | int_fp18_nx_masked | intw_fp18_nx_masked;

  // Assertions
  // ===========
  // synopsys translate_off
`ifdef ASSERTIONS_ON
  `include "prim_assert.sv"
  // VM - FMT mismatches TODO(@stefan.mach): add more
  `ASSERT_IF(int8_data_in_pw32_mode, fmt_i != FMT_INT, fmt_vld_i && operand_vm_i, clk_i, !rst_ni)
`endif  // ASSERTIONS_ON
  // synopsys translate_on

endmodule
