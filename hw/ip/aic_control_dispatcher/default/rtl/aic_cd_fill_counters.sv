// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Keep track of the command FIFO fill levels of the respective destination. If destination is blocked stalls the command stream.
///
/// The unit can be split up in two parts, one is an input pipeline which [calculates](#estimation-of-fill-level) how many lines
/// a particular copy command will use in the commandblock fifo of a destination.  This pipeline also acts as a buffer for outstanding
/// copy commands.  Then there is an array of [individual fill counters](#fill-counter-operation) which then keep the current fill levels
/// per destination. The overal functionality is shown in the following diagram:
///
/// ![AIC_CD_FILL_COUNTERS: Block Diagram](figures/aic_cd_fill_counters.drawio.svg)
///
/// ## Configuration
///
/// The fill counters need to know the destinations shape and size of the respective *command FIFO* to be able to perform their function.
/// For this there exist two CSRs where the *number of bytes per line* `(bytes_per_line)` and the *number of FIFO lines (depth)* `(num_fifo_lines)`.
/// The values in the CSRs for the respective *command blcok FIFO* **must be configured** for the stalling to have an effect.
///
///
/// !!! info "Disabled Counter by Default"
///
///     If any of the values `bytes_per_line` or `num_fifo_lines` is configured `0` for a particular *destination ID* the counter is considered
///     **DISABLED**. A `cmd` copy command will then be sent further without checking for the fill level.
///
///     !!! warning "Pop Errors on Disabled Counters"
///
///         The `counter pop error` irq will be raised on counters that are disabled to emphasize that the CSRs must be configured.
///
///
/// !!! danger "Configure only when IDLE"
///
///     The configuration of the `bytes_per_line` and `num_fifo_lines` **must not** be done while the `aic_cd` is performing operations.
///     Ideally have the firmware set up the configuration at boot once and then leave it alone!
///
///
/// ## Estimation of Fill Level
///
/// Each command that needs to be copied only knows the number of bytes that will be copied.  As the number of bytes per `cmdblock_fifo`
/// line at a destination can be configured through a CSR, we need to calculate this value for each command that flows through this unit.
/// A command will enter through two pipeline stages.  These are primarily there to limit the impact the *ceiling division* used to
/// calculate the used number of fifo lines per command.  The calculation is as follows:
///
/// $$
/// \text{num_fifo_lines} = \frac{\text{num_bytes}_\text{command} + \text{bytes_per_line}_\text{csr} + 1}{\text{bytes_per_line}_\text{csr}}
/// $$
///
///
/// ## Fill Counter Operation
///
/// Once the number of used FIFO lines is calculated the copy command arrives at a `stream_fork`.  It connects to each of the counter FIFOs
/// as well as to the downstream.  On the downstream we fins a `stream_disconnect`.  It is active the moment the respective counter indicates
/// that a new copied *command* to a destination would cause the *command FIFO* to overflow.  The moment the counter is sufficiently decremented
/// the command is let through.  On the counter side we find a FIFO to hold the number of lines a command occupies.  The counter is incremented
/// when the number of lines is deposited in the FIFO.  And decremented if a `done` signal pops the respective oldest entry.  The `steram_fork`
/// ensures correct stalling behaviour in case of internal FIFOs reaching capacity.
///
///
/// ## Errors
///
/// As this unit has to rely on the destinations to send one done pulse per copied command.  Therefore if the destination sends too may *done's* or
/// the counters were not set up correctly the counters will report the counter on `o_error_done_pop`.  This is asserted when there was a pop on a
/// counter which currently is not tracking any outstanding commands.  Thew other error which should *never* be asserted is the `o_error_overflow`.
///
module aic_cd_fill_counters #(
  /// The number of destinations the unit interacts with
  parameter int unsigned NumDestinations = 17,
  /// The depth of the respective fill counter FIFOs
  parameter int unsigned FifoDepth = 16,
  /// The type describing the overall parameterization of the command block FIFOs
  parameter type dst_cmdblock_params_t = aic_cd_csr_reg_pkg::aic_cd_csr_reg2hw_dst_cmdblock_params_mreg_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  //////////////////////////////
  // Subordinate Copy Command //
  //////////////////////////////
  /// The copy command
  input  aic_cd_pkg::copy_command_t i_copy_command,
  /// The copy command is valid
  input  logic                      i_copy_command_valid,
  /// Module consumes copy command
  output logic                      o_copy_command_ready,

  //////////////////////////
  // Manager Copy Command //
  //////////////////////////
  /// The copy command
  output aic_cd_pkg::copy_command_t o_copy_command,
  /// The copy command is valid
  output logic                      o_copy_command_valid,
  /// Dowstream consumes copy command
  input  logic                      i_copy_command_ready,

  ///////////////////
  // Configuration //
  ///////////////////
  /// The CSRs containing the parameterization of the commandblock
  ///
  /// These must be stable during operation
  input  dst_cmdblock_params_t [NumDestinations-1:0] i_destination_cmdblock_params,

  /////////////////////////////
  // Destination Done Pulses //
  /////////////////////////////
  // Each destination must raise a done pulse
  input  logic [NumDestinations-1:0] i_destination_done,

  ///////////////////////
  // Errors and Status //
  ///////////////////////
  /// This unit is busy by either having values in the FIFO, or something being calculated.
  output logic                             o_busy,
  /// The unit is actively stalling because the respective counter said so
  output logic                             o_command_stalled,
  /// The respective fill counter is at capacity
  output logic                             o_must_be_stalled[NumDestinations],
  /// The respective fill counter value
  output aic_cd_pkg::command_byte_length_t o_fill_count[NumDestinations],
  /// A destination signaled a done pulse with the respective FIFO being empty.
  output logic [NumDestinations-1:0]       o_error_done_pop,
  /// A Counter over or undeflowed
  output logic [NumDestinations-1:0]       o_error_overflow
);
  ///////////////////////////////
  // Parameters and Sanitation //
  ///////////////////////////////

  if (aic_cd_pkg::COMMAND_BYTE_LENGTH_WIDTH < $bits(i_destination_cmdblock_params[0].num_fifo_lines.q))
      $fatal(1, "Constant: 'aic_cd_pkg::COMMAND_BYTE_LENGTH_WIDTH(%d)' must not be smaller than width of CSR 'DST_CMDBLOCK_PARAMS.NUM_FIFO_LINES(%d)';",
      aic_cd_pkg::COMMAND_BYTE_LENGTH_WIDTH, $bits(i_destination_cmdblock_params[0].num_fifo_lines.q));
  if (aic_cd_pkg::COMMAND_BYTE_LENGTH_WIDTH < $bits(i_destination_cmdblock_params[0].bytes_per_line.q))
      $fatal(1, "Constant: 'aic_cd_pkg::COMMAND_BYTE_LENGTH_WIDTH(%d)' must not be smaller than width of CSR 'DST_CMDBLOCK_PARAMS.BYTES_PER_LINE(%d)';",
      aic_cd_pkg::COMMAND_BYTE_LENGTH_WIDTH, $bits(i_destination_cmdblock_params[0].bytes_per_line.q));

  /// The destination maximum FIFO size is the binary product
  localparam int unsigned CmdblockFifoUsageWidth = aic_cd_pkg::COMMAND_BYTE_LENGTH_WIDTH + 1;
  /// The size of the respective destination command FIFO
  typedef logic [CmdblockFifoUsageWidth-1:0] cmdblock_fifo_usage_t;

  ///////////////////////////////////////////
  // Pipeline to Calculate number of lines //
  ///////////////////////////////////////////
  localparam int unsigned NUM_STAGES = 2;

  logic [NUM_STAGES-1:0] load_stage;
  logic [NUM_STAGES-1:0] pipeline_state;

  logic copy_command_valid;
  logic copy_command_ready;

  cc_stream_pipe_load #(
    .NumStages(NUM_STAGES)
  ) u_cc_stream_pipe_load (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_valid(i_copy_command_valid),
    .o_ready(o_copy_command_ready),
    .o_load (load_stage),
    .o_state(pipeline_state),
    .o_valid(copy_command_valid),
    .i_ready(copy_command_ready)
  );

  //////////////////////////
  // Stage 0              //
  // Select relevant info //
  //////////////////////////
  aic_cd_pkg::copy_command_t        input_command_q;
  aic_cd_pkg::command_byte_length_t selected_bytes_per_line_q;

  logic       load_selected_bytes;
  always_comb load_selected_bytes =
      (i_copy_command.opcode inside {aic_cd_pkg::OpcodeCommand})
    & (|i_destination_cmdblock_params[i_copy_command.destination_id].bytes_per_line.q);

  // DFFL: D-Flip-Flop, load enable
  always_ff @(posedge i_clk) begin
    if (load_stage[0]) begin
      input_command_q <= i_copy_command;

      if (load_selected_bytes)
          selected_bytes_per_line_q <= aic_cd_pkg::command_byte_length_t'(i_destination_cmdblock_params[i_copy_command.destination_id].bytes_per_line.q);
    end
  end

  /////////////////////////
  // Stage 1             //
  // Calculate FIFO Size //
  /////////////////////////
  aic_cd_pkg::copy_command_t copy_command_q;
  cmdblock_fifo_usage_t      copy_num_fifo_lines_q;
  cmdblock_fifo_usage_t      cmdblock_num_fifo_lines_q;
  cmdblock_fifo_usage_t      cmdblock_num_fifo_lines_d;

  // THIS IS A COMBINATIONAL CEILING DIVISION!
  // FULL PIPELINE TO CONTAIN CYCLE TIME IMPACT!
  always_comb begin : proc_ceil_div
    cmdblock_num_fifo_lines_d = cmdblock_fifo_usage_t'((
        aic_cd_pkg::command_byte_length_t'(input_command_q.num_bytes)
      + selected_bytes_per_line_q
      - aic_cd_pkg::command_byte_length_t'(1)
    ) / selected_bytes_per_line_q);
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      copy_command_q        <= aic_cd_pkg::copy_command_t'(0);
      copy_num_fifo_lines_q <= cmdblock_fifo_usage_t'(0);
    end else if (load_stage[1]) begin
      copy_command_q        <= input_command_q;
      copy_num_fifo_lines_q <= cmdblock_num_fifo_lines_d;
    end
  end

  logic respect_fill_counter;
  always_comb respect_fill_counter =
       copy_command_valid
    & (copy_command_q.opcode inside {aic_cd_pkg::OpcodeCommand})
    & (|i_destination_cmdblock_params[copy_command_q.destination_id].num_fifo_lines.q)
    & (|i_destination_cmdblock_params[copy_command_q.destination_id].bytes_per_line.q);


  ///////////////////////////////////////////////////////////////////
  // Stream fork to connect the handshaking to the respective FIFO //
  ///////////////////////////////////////////////////////////////////

  logic [NumDestinations:0] fill_counter_select;
  logic [NumDestinations:0] fill_counter_valid;
  logic [NumDestinations:0] fill_counter_ready;

  always_comb begin
    fill_counter_select[NumDestinations-1:0] = NumDestinations'(respect_fill_counter) << copy_command_q.destination_id;
    fill_counter_select[NumDestinations]     = 1'b1; // Always have the output stream on
  end

  cc_stream_fork #(
    .NumStreams(NumDestinations+1)
  ) u_stream_fork_fifo_distribution (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select(fill_counter_select),
    .i_valid (copy_command_valid),
    .o_ready (copy_command_ready),
    .o_valid (fill_counter_valid),
    .i_ready (fill_counter_ready)
  );

  //////////////////
  // The Counters //
  //////////////////
  logic [NumDestinations-1:0] counter_contains_value;

  for (genvar destination_index = 0; unsigned'(destination_index) < NumDestinations; destination_index++) begin : gen_counters
    logic       counter_is_selected;
    always_comb counter_is_selected = fill_counter_select[destination_index];

    cmdblock_fifo_usage_t cmdblock_used_lines_q;

    cmdblock_fifo_usage_t increment_value;
    always_comb           increment_value = counter_is_selected ? copy_num_fifo_lines_q : cmdblock_fifo_usage_t'(0);
    logic                 increment_push; // Push when the actual copy command handshake happens
    always_comb           increment_push  = counter_is_selected & copy_command_valid & copy_command_ready;

    cmdblock_fifo_usage_t decrement_value;
    logic                 decrement_valid;
    logic                 decrement_ready;
    always_comb           decrement_ready = i_destination_done[destination_index];
    logic                 decrement_pop;
    always_comb           decrement_pop  = decrement_valid & decrement_ready;

    always_comb o_error_done_pop[destination_index] = ~decrement_valid & decrement_ready;

    cc_stream_fifo #(
      .Depth (FifoDepth),
      .data_t(cmdblock_fifo_usage_t)
    ) u_fifo_bytes_used (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data (increment_value),
      .i_valid(fill_counter_valid[destination_index]),
      .o_ready(fill_counter_ready[destination_index]),
      .o_data (decrement_value),
      .o_valid(decrement_valid),
      .i_ready(decrement_ready),
      .o_usage(/* not used */),
      .o_full (/* not used */),
      .o_empty(/* not used */)
    );

    logic                 counter_enable;
    logic                 counter_down;
    cmdblock_fifo_usage_t counter_delta;
    always_comb begin
      counter_enable = 1'b0;
      counter_down   = 1'b0;
      counter_delta  = cmdblock_fifo_usage_t'(0);

      unique case ({increment_push, decrement_pop})
        2'b10: begin
          counter_enable = 1'b1;
          counter_down   = 1'b0;
          counter_delta  = increment_value;
        end
        2'b01: begin
          counter_enable = 1'b1;
          counter_down   = 1'b1;
          counter_delta  = decrement_value;
        end
        2'b11: begin
          counter_enable = 1'b1;
          if (increment_value >= decrement_value) begin
            counter_down   = 1'b0;
            counter_delta  = increment_value - decrement_value;
          end else begin
            counter_down   = 1'b1;
            counter_delta  = decrement_value - increment_value;
          end
        end
        default: /* do nothing */;
      endcase
    end

    logic overflow;
    cc_cnt_delta #(
      .Width         (CmdblockFifoUsageWidth),
      .StickyOverflow(1'b0)
    ) u_cc_cnt_delta (
      .i_clk,
      .i_rst_n,
      .i_flush   (1'b0),
      .i_cnt_en  (counter_enable),
      .i_cnt_down(counter_down),
      .i_delta   (counter_delta),
      .o_q       (cmdblock_used_lines_q),
      .i_d       (cmdblock_fifo_usage_t'(0)),
      .i_d_load  (1'b0),
      .o_overflow(o_error_overflow[destination_index]) // Should never happen
    );
    always_comb counter_contains_value[destination_index] = o_error_overflow[destination_index] | (|cmdblock_used_lines_q);


    /////////////////////////////////
    // Decide if nee need to stall //
    /////////////////////////////////
    always_comb o_must_be_stalled[destination_index] =
        (cmdblock_used_lines_q + copy_num_fifo_lines_q) > cmdblock_fifo_usage_t'(i_destination_cmdblock_params[destination_index].num_fifo_lines.q);

    always_comb o_fill_count[destination_index] = aic_cd_pkg::command_byte_length_t'(cmdblock_used_lines_q);
  end

  ///////////////////////
  // Stream Disconnect //
  ///////////////////////
  always_comb o_command_stalled = respect_fill_counter & o_must_be_stalled[copy_command_q.destination_id];

  cc_stream_disconnect #(
    .data_t(aic_cd_pkg::copy_command_t)
  ) u_cc_stream_disconnect (
    .i_disconnect (o_command_stalled),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(/* not used */),
    .i_data       (copy_command_q),
    .i_valid      (fill_counter_valid[NumDestinations]),
    .o_ready      (fill_counter_ready[NumDestinations]),
    .o_data       (o_copy_command),
    .o_valid      (o_copy_command_valid),
    .i_ready      (i_copy_command_ready)
  );

  ////////////
  // Status //
  ////////////
  always_comb o_busy = (|counter_contains_value) | (|pipeline_state);
endmodule
