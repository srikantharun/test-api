// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Decoding Stage of the AI-Core Datapath Command Generator.
///
/// This is the gate keeper for executing a command. It performs the validation so that only sane
/// commands are exectued.  If the validation stage passes it distributes the metadata as well as
/// the loop descriptors into their respective queues to be further processed.  It further
/// keeps track of the amount of oustanding commends which are processed to peroperly form
/// the `o_cmdb_done` flag for the `comand block`.
///
/// ## Command Processing
///
/// First a command is taken and put into a register to be further processed.  Depending on the
/// commend `format` and `nested_mapping` each main loop is analyzed for its [loop flags](./aic_cd_dp_gen_loop_flags).
/// These are then used to determine if the command contains any errors.
///
/// If the validation passes the `FSM` then proceeds to generate for each `main` loop a `loop_descriptor`.
///
/// !!! note
///
///     This happens independent of the `format` and is solely dependent on the values contained
///     in the respective *expanded* full command!
///
///
/// ## FSM States and Transitions
///
/// The FSm goes through different states to proerly handle handshakes and generation of loop descriptors.
///
/// - `IDLE`: Accept a newcommand from the `cmdblock`. If unsupported `format` go to error, else proceed with `BYPASS` or `VALIDATION`.
/// - `VALIDATION`: Check command for errors and go to `ERROR` if so. If command is good proceed to next existing `MAIN_*` loop.
/// - `BYPASS_LOOP`: Send out dummy loop descriptor, proceed to `BYPASS_LOOP`.
/// - `BYPASS_META`: Send out Metadata for Bypass, then go to `IDLE`.
/// - `ERROR`: Wait for all outstanding good commands to complete. Signal done flag and go to `IDLE`.
/// - `MAIN_0`: Generate a loop descriptor, then go to next existing `MAIN_*` loop.
/// - `MAIN_1`: Generate a loop descriptor, then go to next existing `MAIN_*` loop.
/// - `MAIN_2`: Generate a loop descriptor, then go to next existing `MAIN_*` loop.
///
/// ```mermaid
/// stateDiagram-v2
///     IDLE
///     VALIDATION
///     BYPASS_LOOP
///     BYPASS_META
///     ERROR
///     MAIN_0
///     MAIN_1
///     MAIN_2
///
///     [*] --> IDLE
///     IDLE --> ERROR: unsupported format
///     ERROR --> IDLE: no more outstanding commands
///
///     IDLE --> VALIDATION
///     IDLE --> BYPASS_LOOP
///
///     VALIDATION --> ERROR: any error detected
///
///     MAIN_0 --> MAIN_1: main_1 exists
///     MAIN_0 --> MAIN_2: main_2 exists
///     MAIN_0 --> IDLE
///
///     MAIN_1 --> IDLE
///     MAIN_1 --> MAIN_2: main_2 exists
///
///     MAIN_2 --> IDLE
///
///     VALIDATION --> MAIN_0: main_0 exists
///     VALIDATION --> MAIN_1: main_1 exists
///     VALIDATION --> MAIN_2: main_2 exists
///
///     BYPASS_LOOP --> BYPASS_META
///     BYPASS_META --> IDLE
/// ```
///
module aic_dp_cmd_gen_decode #(
  /// Depth of the datapath command memory
  parameter int unsigned DpCommandMemoryDepth = 0,
  /// Number of outstanding commands
  parameter int unsigned MaxOutstanding = 2
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  /// Purge everything and force the FSM to IDLE
  input  logic i_flush,

  /////////////////////////////
  // CMD Block Command Input //
  /////////////////////////////
  /// Full command
  input  aic_dp_cmd_gen_pkg::cmdb_cmd_t   i_cmdb_command,
  /// The command format encoding
  input  aic_dp_cmd_gen_pkg::cmd_format_e i_cmdb_format,
  /// The config field from the command header
  input  aic_dp_cmd_gen_pkg::cmd_config_t i_cmdb_config,
  /// Command is valid
  input  logic                            i_cmdb_valid,
  /// Command is ready
  output logic                            o_cmdb_ready,

  ////////////////////////
  // Command done Flags //
  ////////////////////////
  /// Command is Done
  output logic o_cmdb_done,
  /// Datapath is done
  input  logic i_dp_done,

  ////////////////////////////////////
  // Decoded Main Loop Descriptors //
  ////////////////////////////////////
  /// Loop Descriptor payload
  output aic_dp_cmd_gen_pkg::loop_descriptor_t o_loop_descriptor,
  /// Loop descriptor os valid
  output logic                                 o_loop_descriptor_valid,
  /// Loop descriptor ready
  input  logic                                 i_loop_descriptor_ready,

  ///////////////////////////////////////////
  // Metadata, handshaked once per command //
  ///////////////////////////////////////////
  /// Metadata
  output aic_dp_cmd_gen_pkg::metadata_t o_metadata,
  /// Metadata is valid
  output logic                          o_metadata_valid,
  /// Metadata is ready
  input  logic                          i_metadata_ready,

  //////////////////////////////
  // Observability and Errors //
  //////////////////////////////
  /// Error conditions for the loops
  output aic_dp_cmd_gen_pkg::loop_errors_t o_errors
);
  /////////////////////////////////
  // Type and Signal Definitions //
  /////////////////////////////////
  typedef enum logic [2:0] {
    IDLE,
    VALIDATION,
    MAIN_0,
    MAIN_1,
    MAIN_2,
    BYPASS_LOOP,
    BYPASS_META,
    ERROR
  } state_e;
  state_e state_q, state_d;

  /////////////////////////////////////////////////////////////////
  // Have a copy of the command here as local copy to operate on //
  /////////////////////////////////////////////////////////////////
  aic_dp_cmd_gen_pkg::cmdb_cmd_t   command_q;
  aic_dp_cmd_gen_pkg::cmd_format_e format_q;
  aic_dp_cmd_gen_pkg::cmd_config_t config_q;
  logic                            command_load;

  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      command_q <= '0;
      format_q  <= aic_dp_cmd_gen_pkg::LoopsM1N0;
      config_q  <= aic_dp_cmd_gen_pkg::cmd_config_t'(0);
    end else if (i_flush) begin
      command_q <= '0;
      format_q  <= aic_dp_cmd_gen_pkg::LoopsM1N0;
      config_q  <= aic_dp_cmd_gen_pkg::cmd_config_t'(0);
    end else if (command_load) begin
      command_q <= i_cmdb_command; // ASO-UNUSED_VARIABLE : Reserved fields are loaded but never read from flop.
      format_q  <= i_cmdb_format;
      config_q  <= i_cmdb_config;
    end
  end

  //////////////////////////////////////////////////////
  // Keep track of the amount of outstanding commands //
  //////////////////////////////////////////////////////
  localparam int unsigned OutstandingWidth = cc_math_pkg::index_width(MaxOutstanding + 1);
  typedef logic [OutstandingWidth-1:0] outstanding_t;

  outstanding_t outstanding_commands;
  logic         outstanding_increment;
  logic         outstanding_decrement;
  logic         at_max_outstanding;
  always_comb   at_max_outstanding = outstanding_commands >= outstanding_t'(MaxOutstanding);
  logic         zero_outstanding;
  always_comb   zero_outstanding = outstanding_commands == outstanding_t'(0);

  cc_cnt_delta #(
    .Width         (OutstandingWidth),
    .StickyOverflow(1'b0)
  ) u_counter_outstanding (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_cnt_en  (outstanding_increment ^ outstanding_decrement),
    .i_cnt_down(outstanding_decrement),
    .i_delta   (outstanding_t'(1)),
    .o_q       (outstanding_commands),
    .i_d       (outstanding_t'(0)),
    .i_d_load  (1'b0),
    .o_overflow(/* not used */) // ASO-UNUSED_OUTPUT : Not possible to overflow due to check and then stall if full.
  );

  ///////////
  // Flags //
  ///////////
  aic_dp_cmd_gen_pkg::loop_description_t mapped_nested_0[aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS];
  aic_dp_cmd_gen_pkg::loop_description_t mapped_nested_1[aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS];
  aic_dp_cmd_gen_pkg::loop_errors_t      detected_errors;

  //////////////////////////////////
  // Mapping Nested to Main Loops //
  //////////////////////////////////
  logic       main_mapping_is_equal;
  always_comb main_mapping_is_equal = command_q.view_struct.nested_0_map_main == command_q.view_struct.nested_1_map_main;

  logic [aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS-1:0] nested_1_mapped_to_0;

  // Remap the nested to the correct main loop (plus sanitation if the mapping is wrong)
  always_comb foreach (mapped_nested_0[loop_index]) begin
    if (aic_dp_cmd_gen_pkg::loop_index_t'(loop_index) == command_q.view_struct.nested_0_map_main) begin
      mapped_nested_0[loop_index]      = detected_errors.nested_0_mapping ? '{default: '0} : command_q.view_struct.nested_0;
      nested_1_mapped_to_0[loop_index] = 1'b0;
    end else if (!main_mapping_is_equal && aic_dp_cmd_gen_pkg::loop_index_t'(loop_index) == command_q.view_struct.nested_1_map_main) begin
      mapped_nested_0[loop_index]      = detected_errors.nested_1_mapping ? '{default: '0} : command_q.view_struct.nested_1;
      nested_1_mapped_to_0[loop_index] = 1'b1;
    end else begin
      mapped_nested_0[loop_index]      = '{default: '0};
      nested_1_mapped_to_0[loop_index] = 1'b0;
    end
  end

  always_comb foreach (mapped_nested_1[loop_index]) begin
    if (main_mapping_is_equal && aic_dp_cmd_gen_pkg::loop_index_t'(loop_index) == command_q.view_struct.nested_1_map_main)
      mapped_nested_1[loop_index] = detected_errors.nested_1_mapping ? '{default: '0} : command_q.view_struct.nested_1;
    else
      mapped_nested_1[loop_index] = '{default: '0};
  end

  logic                             main_exists[aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS];
  logic                             nested_0_exists[aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS];
  logic                             nested_1_exists[aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS];
  aic_dp_cmd_gen_pkg::loop_errors_t loop_errors[aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS];
  aic_dp_cmd_gen_pkg::loop_errors_t remapped_errors[aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS];

  aic_dp_cmd_gen_loop_flags #(
    .DpCommandMemoryDepth(DpCommandMemoryDepth)
  ) u_aic_dp_cmd_gen_loop_flags_main_0 (
    .i_main                      (command_q.view_struct.main_0),
    .i_nested_0                  (mapped_nested_0[0]),
    .i_nested_1                  (mapped_nested_1[0]),
    .o_main_exists               (main_exists[0]),
    .o_nested_0_exists           (nested_0_exists[0]),
    .o_nested_1_exists           (nested_1_exists[0]),
    .o_main_end                  (/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_nested_0_end              (/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_nested_1_end              (/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_nested_0_contains_nested_1(/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_loop_errors               (loop_errors[0])
  );

   aic_dp_cmd_gen_loop_flags #(
    .DpCommandMemoryDepth(DpCommandMemoryDepth)
  ) u_aic_dp_cmd_gen_loop_flags_main_1 (
    .i_main                      (command_q.view_struct.main_1),
    .i_nested_0                  (mapped_nested_0[1]),
    .i_nested_1                  (mapped_nested_1[1]),
    .o_main_exists               (main_exists[1]),
    .o_nested_0_exists           (nested_0_exists[1]),
    .o_nested_1_exists           (nested_1_exists[1]),
    .o_main_end                  (/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_nested_0_end              (/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_nested_1_end              (/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_nested_0_contains_nested_1(/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_loop_errors               (loop_errors[1])
  );

  aic_dp_cmd_gen_loop_flags #(
    .DpCommandMemoryDepth(DpCommandMemoryDepth)
  ) u_aic_dp_cmd_gen_loop_flags_main_2 (
    .i_main                      (command_q.view_struct.main_2),
    .i_nested_0                  (mapped_nested_0[2]),
    .i_nested_1                  (mapped_nested_1[2]),
    .o_main_exists               (main_exists[2]),
    .o_nested_0_exists           (nested_0_exists[2]),
    .o_nested_1_exists           (nested_1_exists[2]),
    .o_main_end                  (/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_nested_0_end              (/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_nested_1_end              (/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_nested_0_contains_nested_1(/* not used here */), // ASO-UNUSED_OUTPUT : Value not needed in decode.
    .o_loop_errors               (loop_errors[2])       // ASO-UNUSED_VARIABLE : Error signal intended to be merged with others, not all fields used.
  );

  // Because nested 1 can be executed as a nested 0, we need to remap some of the detected errors
  for (genvar loop_index = 0; unsigned'(loop_index) < aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS; loop_index++) begin : gen_error_remapping
    always_comb remapped_errors[loop_index] = '{ // ASO-UNUSED_VARIABLE : Error signal for merging.
      nested_0_length:   nested_1_mapped_to_0[loop_index] ? 1'b0 : loop_errors[loop_index].nested_0_length, // ASO-UNUSED_VARIABLE : Error signal for merging.
      nested_0_segfault: nested_1_mapped_to_0[loop_index] ? 1'b0 : loop_errors[loop_index].nested_0_segfault,
      nested_1_length:   nested_1_mapped_to_0[loop_index] ? loop_errors[loop_index].nested_0_length   : loop_errors[loop_index].nested_1_length,
      nested_1_segfault: nested_1_mapped_to_0[loop_index] ? loop_errors[loop_index].nested_0_segfault : loop_errors[loop_index].nested_1_segfault,
      default: 1'b0
    };
  end

  logic error_illegal_format_q;
  logic error_illegal_format;
  logic error_clear;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                  error_illegal_format_q <= '0;
    else if (error_illegal_format) error_illegal_format_q <= 1'b1;
    else if (error_clear)          error_illegal_format_q <= 1'b0;
  end

  // Accumulate the actual error conditions we know off, propagation is handled in FSM
  always_comb detected_errors = '{
    illegal_format:      error_illegal_format_q,
    empty_program:       aic_dp_cmd_gen_pkg::error_empty_program(main_exists),
    main_0_length:       loop_errors[0].main_0_length,
    main_1_length:       loop_errors[1].main_0_length,
    main_2_length:       loop_errors[2].main_0_length,
    nested_0_length:     remapped_errors[0].nested_0_length
                       | remapped_errors[1].nested_0_length
                       | remapped_errors[2].nested_0_length,
    nested_1_length:     remapped_errors[0].nested_1_length
                       | remapped_errors[1].nested_1_length
                       | remapped_errors[2].nested_1_length,
    nested_0_mapping:    aic_dp_cmd_gen_pkg::error_nested_mapping(command_q.view_struct.nested_0_map_main, main_exists),
    nested_1_mapping:    aic_dp_cmd_gen_pkg::error_nested_mapping(command_q.view_struct.nested_1_map_main, main_exists),
    nested_0_segfault:   remapped_errors[0].nested_0_segfault
                       | remapped_errors[1].nested_0_segfault
                       | remapped_errors[2].nested_0_segfault,
    nested_1_segfault:   remapped_errors[0].nested_1_segfault
                       | remapped_errors[1].nested_1_segfault
                       | remapped_errors[2].nested_1_segfault,
    nested_order:        loop_errors[0].nested_order
                       | loop_errors[1].nested_order
                       | loop_errors[2].nested_order,
    nested_nesting:      loop_errors[0].nested_nesting
                       | loop_errors[1].nested_nesting
                       | loop_errors[2].nested_nesting,
    nested_overlap:      loop_errors[0].nested_overlap
                       | loop_errors[1].nested_overlap
                       | loop_errors[2].nested_overlap,
    default: 1'b0
  };

  /////////////////////////////////////////
  // Decoding Stage Finite State Machine //
  /////////////////////////////////////////
  always_comb o_metadata = '{
    format: format_q,
    cfg:    config_q,
    extra:  command_q.view_struct.extra
  };

  // This is just to find out what the last existing loop is as we can not rely on the format to tell us:
  logic [aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS-1:0] main_is_last;

  // Note: This only works with hardcoded NUM_MAIN_LOOPS!
  if (aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS != 3) $fatal(1, "aic_dp_cmd_gen_pkg::NUM_MAIN_LOOPS must be 3 for priority decoder to determine last flag!");

  always_comb begin
    if      (main_exists[2]) main_is_last = 3'b100;
    else if (main_exists[1]) main_is_last = 3'b010;
    else if (main_exists[0]) main_is_last = 3'b001;
    else                     main_is_last = 3'b000;
  end

  always_comb begin
    // Defaults
    state_d = state_q;

    // Comand block stream
    o_cmdb_ready = 1'b0;
    command_load = 1'b0;

    // Loop descriptor stream
    o_loop_descriptor       = '0;
    o_loop_descriptor_valid = 1'b0;

    // Track number of outstanding
    outstanding_increment = 1'b0;
    outstanding_decrement = 1'b0;

    // Metadata
    o_metadata_valid = 1'b0;

    // Error flags
    o_errors             = '{default: '0};
    error_illegal_format = 1'b0;
    error_clear          = 1'b0;

    // Done fleg
    o_cmdb_done = 1'b0;

    if (i_dp_done) begin
      outstanding_decrement = 1'b1;
      o_cmdb_done           = 1'b1;
    end

    unique case (state_q)
      //////////////////////////////////////////////////////////////////////////////////////////////
      IDLE: begin
        o_cmdb_ready = ~at_max_outstanding;
        if (i_cmdb_valid && !at_max_outstanding) begin
          // Load new command regardless
          command_load = 1'b1;
          unique case (i_cmdb_format)
            aic_dp_cmd_gen_pkg::LoopsM1N0,
            aic_dp_cmd_gen_pkg::LoopsM1N1,
            aic_dp_cmd_gen_pkg::LoopsM1N2,
            aic_dp_cmd_gen_pkg::LoopsM2N0,
            aic_dp_cmd_gen_pkg::LoopsM2N1,
            aic_dp_cmd_gen_pkg::LoopsM2N2,
            aic_dp_cmd_gen_pkg::LoopsM3N0,
            aic_dp_cmd_gen_pkg::LoopsM3N1,
            aic_dp_cmd_gen_pkg::LoopsM3N2: begin
              state_d = VALIDATION;
            end
            aic_dp_cmd_gen_pkg::Bypass: begin
              state_d = BYPASS_LOOP;
            end
            default: begin
              error_illegal_format = 1'b1;
              state_d              = ERROR;
            end
          endcase
        end
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      VALIDATION: begin
        if (|detected_errors) state_d = ERROR;
        else begin
          o_metadata_valid = 1'b1;
          if (i_metadata_ready) begin
            // There might be some emtpy loops, jump to the first existing one
            if      (main_exists[0]) state_d = MAIN_0;
            else if (main_exists[1]) state_d = MAIN_1;
            else                     state_d = MAIN_2;
            outstanding_increment = 1'b1;
          end
        end
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      MAIN_0: begin
        o_loop_descriptor_valid = 1'b1;
        o_loop_descriptor.index = aic_dp_cmd_gen_pkg::loop_index_t'(0);
        o_loop_descriptor.main  = command_q.view_struct.main_0;
        if (nested_0_exists[0]) o_loop_descriptor.nested_0 = mapped_nested_0[0];
        if (nested_1_exists[0]) o_loop_descriptor.nested_1 = mapped_nested_1[0];
        o_loop_descriptor.nested_1_mapped_to_0 = nested_1_mapped_to_0[0];
        o_loop_descriptor.last = main_is_last[0];
        // Decide for next state
        if (i_loop_descriptor_ready)
            if      (main_exists[1]) state_d = MAIN_1;
            else if (main_exists[2]) state_d = MAIN_2;
            else                     state_d = IDLE;
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      MAIN_1: begin
        o_loop_descriptor_valid = 1'b1;
        o_loop_descriptor.index = aic_dp_cmd_gen_pkg::loop_index_t'(1);
        o_loop_descriptor.main  = command_q.view_struct.main_1;
        if (nested_0_exists[1]) o_loop_descriptor.nested_0 = mapped_nested_0[1];
        if (nested_1_exists[1]) o_loop_descriptor.nested_1 = mapped_nested_1[1];
        o_loop_descriptor.nested_1_mapped_to_0 = nested_1_mapped_to_0[1];
        o_loop_descriptor.last = main_is_last[1];
        // Decide for next state
        if (i_loop_descriptor_ready)
            if      (main_exists[2]) state_d = MAIN_2;
            else                     state_d = IDLE;
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      MAIN_2: begin
        o_loop_descriptor_valid = 1'b1;
        o_loop_descriptor.index = aic_dp_cmd_gen_pkg::loop_index_t'(2);
        o_loop_descriptor.main  = command_q.view_struct.main_2;
        if (nested_0_exists[2]) o_loop_descriptor.nested_0 = mapped_nested_0[2];
        if (nested_1_exists[2]) o_loop_descriptor.nested_1 = mapped_nested_1[2];
        o_loop_descriptor.nested_1_mapped_to_0 = nested_1_mapped_to_0[2];
        o_loop_descriptor.last = 1'b1; //  main_is_last[2];
        // Decide for next state
        if (i_loop_descriptor_ready)
          state_d = IDLE;
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      BYPASS_LOOP: begin
        o_loop_descriptor_valid  = 1'b1;
        o_loop_descriptor.bypass = 1'b1;
        o_loop_descriptor.last   = 1'b1;
        if (i_loop_descriptor_ready) state_d = BYPASS_META;
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      BYPASS_META: begin
        o_metadata_valid = 1'b1;
        if (i_metadata_ready) begin
          outstanding_increment = 1'b1;
          state_d               = IDLE;
        end
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      ERROR: begin
        if (zero_outstanding) begin
          o_cmdb_done = 1'b1;
          error_clear = 1'b1;
          state_d     = IDLE;
          o_errors    = detected_errors;
        end
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      default: state_d = IDLE;
    endcase
  end

  // DFFRC: D-Flip-Flop, asynchronous reset, synchronous clear
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)     state_q <= IDLE;
    else if (i_flush) state_q <= IDLE;
    else              state_q <= state_d;
  end
endmodule
