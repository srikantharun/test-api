// (C) Copyright 2022 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner:       Stefan Mach <stefan.mach@axelera.ai>
//              Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Implements the data path of the DWPU. Handels the data and command stream handshaking as well as the computation.
///
module dwpu_dp #(
  /// Number of total channels
  parameter int unsigned NumChannels = dwpu_pkg::NUM_CHANNELS,
  /// Data type for the input data
  parameter type data_inp_t = dwpu_pkg::input_t,
  /// Data type for the computed output data
  parameter type data_oup_t = dwpu_pkg::output_t,
  /// Number of scratchpad registers per channel
  parameter int unsigned NumSpRegs = dwpu_pkg::NUM_SP_REGS,
  /// Number of weight buffer registers per channel
  parameter int unsigned NumWbRegs = dwpu_pkg::NUM_WB_REGS,
  /// Number of compute tree operands
  parameter int unsigned NumOperands = dwpu_pkg::NUM_OPERANDS,
  /// Number of pipeline stages
  parameter int unsigned NumPipeStages = dwpu_pkg::NUM_PIPELINE_STAGES
)(
  /// Clock, positive edge triggered
  input wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input wire  i_rst_n,
  // doc sync i_clk
  /// Configuration from the CSRs
  input dwpu_pkg::config_t i_config,

  /// DPcmd stream tdata
  input dwpu_pkg::dp_instruction_t i_dp_instruction_tdata,
  /// DPcmd stream tlast flag
  input logic                      i_dp_instruction_tlast,
  /// DPcmd stream tvalid flag
  input logic                      i_dp_instruction_tvalid,
  /// DPcmd stream tready flag
  output logic                     o_dp_instruction_tready,
  /// Datapath is done flag. Set if the output stream tlast flag is transmitted.
  output logic                     o_dp_done,

  /// IFD0 AXI stream tdata
  input  data_inp_t [NumChannels-1:0] i_inp_tdata,
  /// IFD0 AXI stream tlast flag
  input  logic                        i_inp_tlast,
  /// IFD0 AXI stream tvalid flag
  input  logic                        i_inp_tvalid,
  /// IFD0 AXI stream treadz flag
  output logic                        o_inp_tready,

  /// IAU AXI stream tdata
  output data_oup_t [NumChannels-1:0] o_out_tdata,
  /// IAU AXI stream tlast flag
  output logic                        o_out_tlast,
  /// IAU AXI stream tvalid flag
  output logic                        o_out_tvalid,
  /// IAU AXI stream tready flag
  input  logic                        i_out_tready,

  /// Status observation signals to the CSRs
  output dwpu_csr_reg_pkg::dwpu_csr_hw2reg_dp_status_reg_t o_dp_status,
  /// Error flag input stream is active on last operation (0 in bypass mode)
  output logic o_err_act_inp_stream,
  /// Error flag output stream is active when datapath is done (0 in bypass mode)
  output logic o_err_act_oup_stream
);

  /////////////////////
  // Input Data FIFO //
  /////////////////////
  // Consider all data as 'in our unit' after the FIFO
  data_inp_t [NumChannels-1:0] inp_pword;
  logic inp_last, inp_valid, inp_ready;

  // Note: fifo_v3 does not properly degenerate at 0
  if (dwpu_pkg::INPUT_FIFO_DEPTH > 0) begin : gen_inp_fifo
    cc_stream_fifo #(
      .Depth      (dwpu_pkg::INPUT_FIFO_DEPTH),
      .DataWidth  ($bits(data_inp_t)*NumChannels + 1),
      .FallThrough(1'b0)
    ) u_input_fifo (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data ({i_inp_tlast, i_inp_tdata}),
      .i_valid(i_inp_tvalid),
      .o_ready(o_inp_tready),
      .o_data ({inp_last, inp_pword}),
      .o_valid(inp_valid),
      .i_ready(inp_ready),
      .o_usage(/*open*/),
      .o_full (/*open*/),
      .o_empty(/*open*/)
    );
  end else begin : gen_no_inp_fifo
    always_comb inp_pword    = i_inp_tdata;
    always_comb inp_last     = i_inp_tlast;
    always_comb inp_valid    = i_inp_tvalid;
    always_comb o_inp_tready = inp_ready;
  end

  // Unpack DPcmd
  // Keep the instruction available for each pipeline stage
  // Mask the last_push with command stream tlast
  dwpu_pkg::dp_instruction_t [NumPipeStages:0] dp_instruction_q;
  assign dp_instruction_q[0] = i_dp_instruction_tdata;

  logic last_op;
  assign last_op = i_dp_instruction_tlast;

  // Bypass control:
  // - Normal mode takes DPcmd for execution on the channels - 1 DPcmd per cycle
  // - Bypass mode blocks DPcmd reading until entire stream is processed - 1 DPcmd per stream
  typedef enum logic [1:0] {
    NORMAL  = 2'd0,
    CLEANUP = 2'd1,
    BYPASS  = 2'd2
  } op_mode_e;

  op_mode_e op_mode_q, op_mode_d;
  logic op_mode_load;
  logic dp_in_bypass;
  assign dp_in_bypass = op_mode_q == BYPASS;

  // Pipe states & back-pressure
  logic dp_cmd_valid, dp_cmd_ready;
  logic ch_inp_ready, ch_inp_valid;
  logic ch_out_ready, ch_out_valid;
  logic bypass_ready, bypass_valid;
  // Output handshaking
  logic out_ready, out_valid, out_last;
  logic reading_input, reading_cmd, writing_output;
  // Indicate state of channel pipeline
  logic pipe_flushed;

  // AXI-style rdy/vld: No 'vld' signal must depend on it's own ready! -> don't use for valid
  assign reading_input  = inp_valid & inp_ready;
  assign reading_cmd    = i_dp_instruction_tvalid & o_dp_instruction_tready;
  assign writing_output = out_ready & out_valid;

  // Control the operation mode
  // In bypass stall as long as needed.
  always_comb begin : op_mode_handling
    // Default values
    dp_cmd_valid            = 1'b0;
    o_dp_instruction_tready = 1'b0;
    op_mode_load            = 1'b0;
    op_mode_d               = op_mode_q;
    o_dp_done               = 1'b0;

    unique case (op_mode_q)
      // In normal operation, only switch to bypass mode if we read a DPcmd with the flag set
      NORMAL: begin
        if (i_dp_instruction_tvalid && dp_instruction_q[0].bypass) begin
          op_mode_load            = 1'b1;
          op_mode_d               = BYPASS;
          o_dp_instruction_tready = pipe_flushed;
        end else begin
          dp_cmd_valid    = i_dp_instruction_tvalid;
          o_dp_instruction_tready = dp_cmd_ready;
          if (reading_cmd && i_dp_instruction_tlast) begin
            op_mode_load = 1'b1;
            op_mode_d    = CLEANUP;
          end
        end
      end
      CLEANUP: begin
        if (pipe_flushed) begin
          o_dp_done    = 1'b1;
          op_mode_load = 1'b1;
          op_mode_d    = NORMAL;
        end
      end
      // Stay in bypass mode until data stream finishes
      BYPASS: begin
        if (writing_output && out_last) begin
          o_dp_done    = 1'b1;
          op_mode_load = 1'b1;
          op_mode_d    = NORMAL;
        end
      end
      // Unknown states drop to normal mode
      default: begin
        op_mode_load = 1'b1;
        op_mode_d    = NORMAL;
      end
    endcase
  end
  ////////////////////
  // State register //
  ////////////////////
  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          op_mode_q <= NORMAL;
    else if (op_mode_load) op_mode_q <= op_mode_d;
  end

  // Join command stream and data stream depending on module state
  logic [1:0] dispatch_select;
  logic dispatch_valid, dispatch_ready;

  // Do we need the data input stream (handshaking with dp_cmd_valid and dp_cmd_ready)
  logic [NumOperands-1:0] any_img_sel_is_one;
  for (genvar op_idx = 0; unsigned'(op_idx) < NumOperands; op_idx++) begin : gen_any_img_sel_is_one
    assign any_img_sel_is_one[op_idx] = (dp_instruction_q[0].command.i_sel[op_idx] == dwpu_pkg::i_sel_t'(1));
  end

  logic  read_from_input;
  assign read_from_input =
          dp_instruction_q[0].command.op_desc.shift_sp
      ||  dp_instruction_q[0].command.op_desc.shift_wb
      || (dp_instruction_q[0].command.op_desc.op_exe   && |any_img_sel_is_one);

  // - BYPASS: Careful with tlast flag! Should not be an issue as in bypass it is not pipelined.
  // - NORMAL: Every CMD needs DATA if needed
  assign dispatch_select[1] = (op_mode_q == BYPASS) ? 1'b1 : read_from_input;
  // Do we need the cmd input stream
  // - BYPASS: CMD stream not needed.
  // - NORMAL: Every CMD needs DATA sometimes
  assign dispatch_select[0] = (op_mode_q == BYPASS) ? 1'b0 : 1'b1;

  cc_stream_join #(
    .NumStreams(2)
  ) u_cc_stream_join_cmd_data (
    .i_select(dispatch_select),
    .i_valid ({inp_valid, dp_cmd_valid}),
    .o_ready ({inp_ready, dp_cmd_ready}),
    .o_valid (dispatch_valid),
    .i_ready (dispatch_ready)
  );

  cc_stream_demux #(
    .NumStreams (2),
    .DropOnError(0)
  ) u_cc_stream_demux (
    .i_valid (dispatch_valid),
    .o_ready (dispatch_ready),
    .i_select(dp_in_bypass),
    .o_error (/*open*/), // ASO-UNUSED_OUTPUT : Demux is power of two, can not select non existing output.
    .o_valid ({bypass_valid, ch_inp_valid}),
    .i_ready ({bypass_ready, ch_inp_ready})
  );

  //////////////
  // Channels //
  //////////////
  // Output data
  data_oup_t [NumChannels-1:0] ch_out_pword;

  // flag to see if a transaction goes into the channel
  // Any channel can take a command if there is a handshake happening at the filter input
  logic  channel_transaction;
  assign channel_transaction = ch_inp_valid && ch_inp_ready;

  // If there is no output needed, filter out the pieline handshaking here to prevent loading.
  // The shifts are enabeld directly by the instruction which is filtered here.
  logic  cmd_no_exe, ch_dropped;
  assign cmd_no_exe = ch_inp_valid && ~dp_instruction_q[0].command.op_desc.op_exe;

  logic ch_valid, ch_ready;
  cc_stream_filter i_cc_stream_filter (
    .i_drop   (cmd_no_exe),
    .o_dropped(ch_dropped),  // ASO-UNUSED_VARIABLE : Not observed that this was dropped.
    .i_valid  (ch_inp_valid),
    .o_ready  (ch_inp_ready),
    .o_valid  (ch_valid),
    .i_ready  (ch_ready)
  );

  // Channel pipelining handshake
  logic [NumPipeStages-1:0] pipe_load, pipe_state;

  cc_stream_pipe_load #(
    .NumStages(NumPipeStages)
  ) u_cc_stream_pipe_load (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),          // Pipeline not flushable
    .i_valid(ch_valid),
    .o_ready(ch_ready),
    .o_load (pipe_load),
    .o_state(pipe_state),
    .o_valid(ch_out_valid),
    .i_ready(ch_out_ready)
  );
  // The 'internal' pipeline doesn't have in-flight data when valids are low -> bypass switch safe
  assign pipe_flushed = ~(|pipe_state);

  // Keep the command synced with the amount of pipeline stages
  for (genvar i = 0; unsigned'(i) < NumPipeStages; i++) begin : gen_cmd_pipeline
    // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)          dp_instruction_q[i+1] <= '0;
      else if (pipe_load[i]) dp_instruction_q[i+1] <= dp_instruction_q[i]; // ASO-UNUSED_VARIABLE : Last pipeline stage does no need all instruction fields.
    end
  end

  //////////////
  // Channels //
  //////////////
  for (genvar i_channel = 0; unsigned'(i_channel) < NumChannels; i_channel++) begin : gen_channels
    dwpu_dp_channel #(
      .NumSpRegs        (NumSpRegs),
      .NumWbRegs        (NumWbRegs),
      .NumOperands      (NumOperands),
      .NumPipeStages    (NumPipeStages),
      .dwpu_dp_command_t(dwpu_pkg::dwpu_dp_command_t),
      .data_inp_t       (data_inp_t),
      .data_oup_t       (data_oup_t)
    ) u_dwpu_dp_channel (
      .i_clk,
      .i_rst_n,
      .i_pipe_load  (pipe_load),
      .i_command    (dp_instruction_q[0].command), // Take the non pipelined datapath command
      .i_transaction(channel_transaction),
      .i_data       (inp_pword[i_channel]),
      .o_data       (ch_out_pword[i_channel]),
      .i_signed_img (i_config.signed_img),
      .i_signed_wgt (i_config.signed_wgt)
    );
  end


  /////////////////
  // Data Output //
  /////////////////
  // Before the output buffer
  data_oup_t [NumChannels-1:0] out_pword, bypass_pword;

  // Handle bypass by properly extending inputs
  logic  signed_op;
  assign signed_op = i_config.signed_img;

  for (genvar i = 0; unsigned'(i) < NumChannels; ++i) begin : gen_extend_bypass_pword
    data_inp_t in_data;
    assign in_data = inp_pword[i];
    assign bypass_pword[i] = signed'({signed_op & in_data[dwpu_pkg::IN_PIXEL_WIDTH-1], in_data});
  end

  // Select output buffer data according to operation mode (direct or delayed path)
  assign out_last  = (op_mode_q == BYPASS) ? inp_last : dp_instruction_q[NumPipeStages].command.op_desc.last_push;

  // Feed output handshake together
  cc_stream_mux #(
    .data_t    (data_oup_t[NumChannels-1:0]),
    .NumStreams(2)
  ) u_cc_stream_mux (
    .i_data  ({bypass_pword, ch_out_pword}),
    .i_select(dp_in_bypass),
    .o_error (/*open*/), // ASO-UNUSED_OUTPUT : Mux is power of two, can not select non existing input.
    .i_valid ({bypass_valid, ch_out_valid}),
    .o_ready ({bypass_ready, ch_out_ready}),
    .o_data  (out_pword),
    .o_valid (out_valid),
    .i_ready (out_ready)
  );

  // Cycle output buffer regs only if we actually have data to push there (energy savings)
  // Valid is always clocked when the buffer becomes ready (to clear the valid again).
  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      o_out_tdata  <= '0;
      o_out_tlast  <= 1'b0;
      o_out_tvalid <= 1'b0;
    end else begin
      if (writing_output) o_out_tdata  <= out_pword;
      if (writing_output) o_out_tlast  <= out_last;
      if (out_ready)      o_out_tvalid <= out_valid;
    end
  end

  // A buffer is ready 1) if downstream is ready or 2) to pop bubbles
  assign out_ready = i_out_tready | ~o_out_tvalid;

  ////////////////////////
  // Status Observation //
  ////////////////////////
  // Input stream is stalled if we SHALL read it (and are not downstream stalled), but no valid.
  logic  inp_stream_stalled, cmd_stream_stalled;
  assign inp_stream_stalled = ~inp_valid & (dp_in_bypass ? out_ready :
      dp_cmd_valid & read_from_input & (ch_ready | ~dp_instruction_q[0].command.op_desc.op_exe));
  // There is no way to know if the missing command would have backpressure or not (due to
  // `op_exe` in the instruction), so we err on the side of raising false-positives.
  assign cmd_stream_stalled = ~i_dp_instruction_tvalid & (op_mode_q == NORMAL);

  assign o_dp_status = '{
      in0_vld:      '{d: inp_valid},
      in0_rdy:      '{d: inp_ready},
      in0_lst:      '{d: inp_last},
      in0_stl:      '{d: inp_stream_stalled},
      out_vld:      '{d: out_valid},
      out_rdy:      '{d: out_ready},
      out_lst:      '{d: out_last},
      out_stl:      '{d: out_valid & ~out_ready},
      dpcmd0_vld:   '{d: i_dp_instruction_tvalid},
      dpcmd0_rdy:   '{d: o_dp_instruction_tready},
      dpcmd0_lst:   '{d: i_dp_instruction_tlast},
      dpcmd0_stl:   '{d: cmd_stream_stalled},
      current_op:   '{d: dp_instruction_q[0].command.op_desc.opcode},
      op_mode:      '{d: op_mode_q},
      pipe_flushed: '{d: pipe_flushed},
      ch_in_lst:    '{d: last_op},
      ch_in_rdy:    '{d: ch_inp_ready},
      ch_in_vld:    '{d: ch_inp_valid},
      ch_out_lst:   '{d: dp_instruction_q[NumPipeStages].command.op_desc.last_push},
      ch_out_rdy:   '{d: ch_out_ready},
      ch_out_vld:   '{d: ch_out_valid}
  };

  ////////////////////
  // Error Checking //
  ////////////////////
  logic in_str_active_q, in_str_active_clear;
  logic out_str_active_q, out_str_active_clear;

  assign in_str_active_clear  = reading_input & inp_last;
  assign out_str_active_clear = writing_output & out_last;

  // Once we use the streams, only tlast can reset the active state
  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                  in_str_active_q <= 1'b0;
    else if (in_str_active_clear)  in_str_active_q <= 1'b0;
    else if (reading_input)        in_str_active_q <= 1'b1;
  end
  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                  out_str_active_q <= 1'b0;
    else if (out_str_active_clear) out_str_active_q <= 1'b0;
    else if (writing_output)       out_str_active_q <= 1'b1;
  end

  // Detect errors, except for bypass mode
  assign o_err_act_inp_stream = (op_mode_q != BYPASS)
                              &  reading_cmd & last_op
                              & (in_str_active_q | reading_input)
                              & ~in_str_active_clear;

  assign o_err_act_oup_stream = (op_mode_q != BYPASS)
                              &  o_dp_done
                              & (out_str_active_q | writing_output);

endmodule
