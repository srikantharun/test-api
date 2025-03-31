// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Looping generator to translate a loop descriptor into a stream of addresses.
///
/// This module contains 4 counters to keep state of the current address as well as the iteration
/// number of the loops being executed.  To update the counters there is an FSM wich heavily relies
/// on priority of flags to determine where is should update the pointers next.
///
/// Pepending on the counter state varous flags are genreated to deptermine where in the loop
/// execution we currently are.
///
/// !!! note "Loop Descriptor"
///
///    This unit only is concerned of executing a *single* `main` loop with eventual mapped
///    `nested` loops.  It relyes that the loop descriptor contains *sane* values.
///
/// This unit is also responsible for generating the `iteratin flags` which then are tagged
/// along the respective generated `o_address_pointer`.
///
/// The generated output stream is expected to be feed into the program memory to fetch
/// the respective instruction.
///
module aic_dp_cmd_gen_loops #(
  /// Depth of the datapath command memory
  parameter int unsigned DpCommandMemoryDepth = 0
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  /// Purge everything and force the FSM to IDLE
  input  logic i_flush,

  //////////////////////
  // Loop Descriptors //
  //////////////////////
  /// Loop Descriptor payload
  input  aic_dp_cmd_gen_pkg::loop_descriptor_t i_loop_descriptor,
  /// Loop descriptor os valid
  input  logic                                 i_loop_descriptor_valid,
  /// Loop descriptor ready
  output logic                                 o_loop_descriptor_ready,

  ////////////////////
  // Address Stream //
  ////////////////////
  /// Program address pointer
  output aic_dp_cmd_gen_pkg::loop_pointer_t    o_address_pointer,
  /// Iteration status sent alongside the address
  aic_dp_cmd_gen_pkg::loop_iterations_t        o_address_iterations,
  /// This is the last address of the overall loop
  output logic                                 o_address_last,
  /// This is a bypass command
  output logic                                 o_address_bypass,
  /// Address is valid
  output logic                                 o_address_valid,
  /// Address ready
  input  logic                                 i_address_ready,

  //////////////////////////////
  // Observability and Errors //
  //////////////////////////////
  /// Error conditions for the loops
  output aic_dp_cmd_gen_pkg::loop_errors_t     o_loop_errors
);
  /////////////////////////////////
  // Type and Signal Definitions //
  /////////////////////////////////
  typedef enum logic [1:0] {
    IDLE,
    BYPASS,
    LOOPS
  } state_e;
  state_e state_q, state_d;

  // Counters
  logic                                address_pointer_increment;
  aic_dp_cmd_gen_pkg::loop_pointer_t   address_pointer_q;
  aic_dp_cmd_gen_pkg::loop_pointer_t   address_pointer_d;
  logic                                address_pointer_overwrite;

  aic_dp_cmd_gen_pkg::loop_iteration_t main_iteration_q;
  aic_dp_cmd_gen_pkg::loop_iteration_t nested_0_iteration_q;
  aic_dp_cmd_gen_pkg::loop_iteration_t nested_1_iteration_q;

  logic                                main_iteration_increment;
  logic                                nested_1_iteration_increment;
  logic                                nested_0_iteration_increment;

  logic                                main_iteration_clear;
  logic                                nested_1_iteration_clear;
  logic                                nested_0_iteration_clear;

  ///////////
  // Flags //
  ///////////
  // Determine if the loops actually exist
  logic main_exists;
  logic nested_0_exists;
  logic nested_1_exists;

  // End addresses of the loops
  aic_dp_cmd_gen_pkg::loop_pointer_t main_end;
  aic_dp_cmd_gen_pkg::loop_pointer_t nested_0_end;
  aic_dp_cmd_gen_pkg::loop_pointer_t nested_1_end;

  // Are we containing another loop?
  logic       nested_0_contains_nested_1;

  aic_dp_cmd_gen_loop_flags #(
    .DpCommandMemoryDepth(DpCommandMemoryDepth)
  ) u_aic_dp_cmd_gen_loop_flags (
    .i_main                      (i_loop_descriptor.main),
    .i_nested_0                  (i_loop_descriptor.nested_0),
    .i_nested_1                  (i_loop_descriptor.nested_1),
    .o_main_exists               (main_exists),
    .o_nested_0_exists           (nested_0_exists),
    .o_nested_1_exists           (nested_1_exists),
    .o_main_end                  (main_end),
    .o_nested_0_end              (nested_0_end),
    .o_nested_1_end              (nested_1_end),
    .o_nested_0_contains_nested_1(nested_0_contains_nested_1),
    // There should be no errors any more at this stage
    .o_loop_errors
  );

  // Have flags to tell us where we are in our programm
  logic at_end_of_main;
  logic at_end_of_nested_0;
  logic at_end_of_nested_1;

  always_comb at_end_of_main     = main_exists     & (o_address_pointer == main_end);
  always_comb at_end_of_nested_0 = nested_0_exists & (o_address_pointer == nested_0_end);
  always_comb at_end_of_nested_1 = nested_1_exists & (o_address_pointer == nested_1_end);

  logic inside_of_nested_0;
  logic inside_of_nested_1;

  always_comb inside_of_nested_0 = nested_0_exists & (o_address_pointer inside {[i_loop_descriptor.nested_0.start:nested_0_end]});
  always_comb inside_of_nested_1 = nested_1_exists & (o_address_pointer inside {[i_loop_descriptor.nested_1.start:nested_1_end]});

  // Flags to tell that the counters are done
  logic  last_iteration_main;
  logic  last_iteration_nested_0;
  logic  last_iteration_nested_1;

  always_comb last_iteration_main     = main_exists     & (main_iteration_q     >= (i_loop_descriptor.main.iteration     - 1));
  always_comb last_iteration_nested_0 = nested_0_exists & (nested_0_iteration_q >= (i_loop_descriptor.nested_0.iteration - 1));
  always_comb last_iteration_nested_1 = nested_1_exists & (nested_1_iteration_q >= (i_loop_descriptor.nested_1.iteration - 1));

  // When are we at the last iteration?
  logic last_overall_iteration;
  always_comb begin
    if      (inside_of_nested_0 & inside_of_nested_1) last_overall_iteration = last_iteration_main & last_iteration_nested_0 & last_iteration_nested_1;
    else if (inside_of_nested_1)                      last_overall_iteration = last_iteration_main & last_iteration_nested_1;
    else if (inside_of_nested_0)                      last_overall_iteration = last_iteration_main & last_iteration_nested_0;
    else                                              last_overall_iteration = last_iteration_main;
  end
  always_comb o_address_last       = (at_end_of_main & last_overall_iteration & i_loop_descriptor.last) | o_address_bypass;

  aic_dp_cmd_gen_pkg::loop_iterations_t address_iterations;
  always_comb address_iterations = '{
    overall_last: (last_overall_iteration & i_loop_descriptor.last) | o_address_bypass,
    nested_1:     inside_of_nested_1 ? nested_1_iteration_q : aic_dp_cmd_gen_pkg::loop_iteration_t'(0),
    nested_0:     inside_of_nested_0 ? nested_0_iteration_q : aic_dp_cmd_gen_pkg::loop_iteration_t'(0),
    main:         main_iteration_q,
    main_index:   i_loop_descriptor.index,
    default:      '0
  };

  // Remap to nested 1, in the case a command nested 1 was remapped for execution in nested 0
  always_comb o_address_iterations = '{
    overall_last: address_iterations.overall_last,
    nested_1:     i_loop_descriptor.nested_1_mapped_to_0 ? address_iterations.nested_0              : address_iterations.nested_1,
    nested_0:     i_loop_descriptor.nested_1_mapped_to_0 ? aic_dp_cmd_gen_pkg::loop_iteration_t'(0) : address_iterations.nested_0,
    main:         address_iterations.main,
    main_index:   address_iterations.main_index,
    default:      '0
  };

  //////////////////////////
  // Finite State Machine //
  //////////////////////////

  always_comb begin
    // Defaults
    state_d = state_q;

    // Input handshake
    o_loop_descriptor_ready = 1'b0;

    // Outputs
    o_address_pointer = address_pointer_q;
    o_address_valid   = 1'b0;
    o_address_bypass  = 1'b0;

    // Counter controls
    address_pointer_increment    = 1'b0;
    main_iteration_increment     = 1'b0;
    nested_0_iteration_increment = 1'b0;
    nested_1_iteration_increment = 1'b0;

    address_pointer_d    = i_loop_descriptor.main.start;

    address_pointer_overwrite = 1'b0;
    main_iteration_clear      = 1'b0;
    nested_0_iteration_clear  = 1'b0;
    nested_1_iteration_clear  = 1'b0;

    unique case (state_q)
      //////////////////////////////////////////////////////////////////////////////////////////////
      // Wait and sanity cech a new loop command
      IDLE: begin
        if (i_loop_descriptor_valid) begin
          // Decide where to go using lengths/iterations (skip 0-len/0-iter sections)
          address_pointer_overwrite = 1'b1;
          main_iteration_clear      = 1'b1;
          nested_0_iteration_clear  = 1'b1;
          nested_1_iteration_clear  = 1'b1;

          // It is a bypass command if main does not exist
          if (i_loop_descriptor.bypass) begin
            state_d = BYPASS;
          end else if (main_exists) begin
            state_d = LOOPS;
            // Note: Could emit the first address while we are changing state to get rid of the stall cycle
          end else begin
            // Just pop the empty loop
            o_loop_descriptor_ready = 1'b1;
          end
        end
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      // Just genreate an output pulse
      BYPASS: begin
        o_address_bypass = 1'b1;
        o_address_valid  = 1'b1;

        if (i_address_ready) begin
          state_d                 = IDLE;
          o_loop_descriptor_ready = 1'b1;
        end
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      // Generate addresses
      LOOPS: begin
        o_address_valid = 1'b1;
        // The datapath command memory acepts the command, we can update
        if (i_address_ready) begin
          // Advance programm counter
          address_pointer_increment = 1'b1;

          if (at_end_of_main) begin
            if (last_overall_iteration) begin
              // Note: More preformance could be implemented here
              state_d                 = IDLE;
              o_loop_descriptor_ready = 1'b1;
              // We are at the end flush the iterators
              address_pointer_d         = aic_dp_cmd_gen_pkg::loop_pointer_t'(0);
              address_pointer_overwrite = 1'b1;
              main_iteration_clear      = 1'b1;
              nested_0_iteration_clear  = 1'b1;
              nested_1_iteration_clear  = 1'b1;
            end
            else if (
                 (!nested_0_exists || last_iteration_nested_0)
              && (!nested_1_exists || last_iteration_nested_1)
            ) begin
              // Jump to the main section if we have both nested loops not present, or are in the last iteration of the respective one
              address_pointer_d         = i_loop_descriptor.main.start;
              address_pointer_overwrite = 1'b1;
              main_iteration_increment  = 1'b1;
              // Reset nested counters
              nested_0_iteration_clear  = nested_0_exists;
              // Set nested 1 to one only in the nested loop case, in parallel to 0
              // See exception below, to prevent triggering of tlast too early in parallel case
              nested_1_iteration_clear  = nested_1_exists;
            end
          end

          if (at_end_of_nested_0 && !last_iteration_nested_0) begin
            address_pointer_d            = i_loop_descriptor.nested_0.start; // ASO-MULTI_ASSIGN : Edge case that jumps somewhere else with priority.
            address_pointer_overwrite    = 1'b1;
            nested_0_iteration_increment = 1'b1;

            // Do not increment if in the nested case nested1 has not finished yet
            if (nested_0_contains_nested_1) begin
              if (last_iteration_nested_1) begin
                nested_1_iteration_clear = 1'b1; // ASO-MULTI_ASSIGN : This edge case forces the clear of the counter.
              end else begin
                nested_0_iteration_increment = 1'b0;
              end
            end
          end

          // Special case for the parallel nested loops, set the counter of nested1 when at the end of nested0
          if (at_end_of_nested_0 && last_iteration_nested_0 && nested_1_exists && !nested_0_contains_nested_1) begin
            nested_1_iteration_clear = 1'b1; // ASO-MULTI_ASSIGN : This edge case forces the clear of the counter.
          end

          if (at_end_of_nested_1 && !last_iteration_nested_1) begin
            address_pointer_d            = i_loop_descriptor.nested_1.start; // ASO-MULTI_ASSIGN : Edge case that jumps somewhere else with priority.
            address_pointer_overwrite    = 1'b1;
            nested_1_iteration_increment = 1'b1;
          end
        end
      end
      //////////////////////////////////////////////////////////////////////////////////////////////
      // Revert to Idles
      default: state_d = IDLE;
    endcase
  end

  ////////////////////////
  // Counters and State //
  ////////////////////////

  // DFFRC: D-Flip-Flop, asynchronous reset, synchronous clear
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)     state_q <= IDLE;
    else if (i_flush) state_q <= IDLE;
    else              state_q <= state_d;
  end

  cc_cnt_delta #(
    .Width         (aic_dp_cmd_gen_pkg::LOOP_POINTER_WIDTH),
    .StickyOverflow(1'b0)
  ) u_counter_address (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_cnt_en  (address_pointer_increment),
    .i_cnt_down(1'b0),
    .i_delta   (aic_dp_cmd_gen_pkg::loop_pointer_t'(1)),
    .o_q       (address_pointer_q),
    .i_d       (address_pointer_d),
    .i_d_load  (address_pointer_overwrite),
    .o_overflow(/* open */) // ASO-UNUSED_OUTPUT : No overflow check done.
  );

  cc_cnt_delta #(
    .Width         (aic_dp_cmd_gen_pkg::LOOP_ITERATION_WIDTH),
    .StickyOverflow(1'b0)
  ) u_counter_iteration_main (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_cnt_en  (main_iteration_increment),
    .i_cnt_down(1'b0),
    .i_delta   (aic_dp_cmd_gen_pkg::loop_iteration_t'(1)),
    .o_q       (main_iteration_q),
    .i_d       (aic_dp_cmd_gen_pkg::loop_iteration_t'(0)),
    .i_d_load  (main_iteration_clear),
    .o_overflow(/* open */) // ASO-UNUSED_OUTPUT : No overflow check done.
  );

  cc_cnt_delta #(
    .Width         (aic_dp_cmd_gen_pkg::LOOP_ITERATION_WIDTH),
    .StickyOverflow(1'b0)
  ) u_counter_iteration_nested_0 (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_cnt_en  (nested_0_iteration_increment),
    .i_cnt_down(1'b0),
    .i_delta   (aic_dp_cmd_gen_pkg::loop_iteration_t'(1)),
    .o_q       (nested_0_iteration_q),
    .i_d       (aic_dp_cmd_gen_pkg::loop_iteration_t'(0)),
    .i_d_load  (nested_0_iteration_clear),
    .o_overflow(/* open */) // ASO-UNUSED_OUTPUT : No overflow check done.
  );

  cc_cnt_delta #(
    .Width         (aic_dp_cmd_gen_pkg::LOOP_ITERATION_WIDTH),
    .StickyOverflow(1'b0)
  ) u_counter_iteration_nested_1 (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_cnt_en  (nested_1_iteration_increment),
    .i_cnt_down(1'b0),
    .i_delta   (aic_dp_cmd_gen_pkg::loop_iteration_t'(1)),
    .o_q       (nested_1_iteration_q),
    .i_d       (aic_dp_cmd_gen_pkg::loop_iteration_t'(0)),
    .i_d_load  (nested_1_iteration_clear),
    .o_overflow(/* open */) // ASO-UNUSED_OUTPUT : No overflow check done.
  );
endmodule
