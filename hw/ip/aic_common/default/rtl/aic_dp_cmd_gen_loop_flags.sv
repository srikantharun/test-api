// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Calculates different flags and error conditions for a single loop description.
///
module aic_dp_cmd_gen_loop_flags #(
  /// Depth of the datapath command memory
  parameter int unsigned DpCommandMemoryDepth = 0
)(
  /// The loop description for the main loop
  input  aic_dp_cmd_gen_pkg::loop_description_t i_main,
  /// The loop description for the nested 0 loop
  input  aic_dp_cmd_gen_pkg::loop_description_t i_nested_0,
  /// The loop description for the nested 1 loop
  input  aic_dp_cmd_gen_pkg::loop_description_t i_nested_1,

  /// The main loop exists
  output logic                                  o_main_exists,
  /// The nested 0 loop exists
  output logic                                  o_nested_0_exists,
  /// The nested 1 loop exists
  output logic                                  o_nested_1_exists,

  /// End pointer of the main loop
  output aic_dp_cmd_gen_pkg::loop_pointer_t     o_main_end,
  /// End pointer of the nested 0 loop
  output aic_dp_cmd_gen_pkg::loop_pointer_t     o_nested_0_end,
  /// End pointer of the nested 1 loop
  output aic_dp_cmd_gen_pkg::loop_pointer_t     o_nested_1_end,

  /// The nested 0 loop contains the nested 1 loop
  output logic                                  o_nested_0_contains_nested_1,

  /// The errors that can happen
  output aic_dp_cmd_gen_pkg::loop_errors_t      o_loop_errors
);

  /////////////////////
  // Existance Flags //
  /////////////////////
  always_comb o_main_exists = aic_dp_cmd_gen_pkg::loop_exists(
    .length    (i_main.length),
    .iterations(i_main.iteration)
  );
  always_comb o_nested_0_exists = aic_dp_cmd_gen_pkg::loop_exists(
    .length    (i_nested_0.length),
    .iterations(i_nested_0.iteration)
  );
  always_comb o_nested_1_exists = aic_dp_cmd_gen_pkg::loop_exists(
    .length    (i_nested_1.length),
    .iterations(i_nested_1.iteration)
  );

  logic       both_nested_exist;
  always_comb both_nested_exist = o_nested_0_exists & o_nested_1_exists;

  ////////////////////////////
  // Program Ending Pointer //
  ////////////////////////////
  aic_dp_cmd_gen_pkg::_loop_pointer_t main_end;
  always_comb o_main_end = aic_dp_cmd_gen_pkg::loop_pointer_t'(main_end);
  always_comb   main_end = aic_dp_cmd_gen_pkg::loop_end_pointer(
    .start (i_main.start),
    .length(i_main.length)
  );

  aic_dp_cmd_gen_pkg::_loop_pointer_t nested_0_end;
  always_comb o_nested_0_end = aic_dp_cmd_gen_pkg::loop_pointer_t'(nested_0_end);
  always_comb   nested_0_end = aic_dp_cmd_gen_pkg::loop_end_pointer(
    .start (i_nested_0.start),
    .length(i_nested_0.length)
  );

  aic_dp_cmd_gen_pkg::_loop_pointer_t nested_1_end;
  always_comb o_nested_1_end = aic_dp_cmd_gen_pkg::loop_pointer_t'(nested_1_end);
  always_comb   nested_1_end = aic_dp_cmd_gen_pkg::loop_end_pointer(
    .start (i_nested_1.start),
    .length(i_nested_1.length)
  );

  /////////////////////////////////////
  // Are we containing another loop? //
  /////////////////////////////////////
  always_comb o_nested_0_contains_nested_1 =
      both_nested_exist
    & (i_nested_0.start <= i_nested_1.start)
    & (o_nested_0_end   >= i_nested_1.start);

  ////////////////////////////
  // Errors: Memory Mapping //
  ////////////////////////////
  logic error_main_maps_outside_memory;
  logic error_nested_0_maps_outside_memory;
  logic error_nested_1_maps_outside_memory;

  always_comb error_main_maps_outside_memory =
      o_main_exists
    & aic_dp_cmd_gen_pkg::loop_maps_outside_memory(
        .start       (i_main.start),
        .length      (i_main.length),
        .memory_depth(DpCommandMemoryDepth)
      );
  always_comb error_nested_0_maps_outside_memory =
      o_nested_0_exists
    & aic_dp_cmd_gen_pkg::loop_maps_outside_memory(
        .start       (i_nested_0.start),
        .length      (i_nested_0.length),
        .memory_depth(DpCommandMemoryDepth)
      );
  always_comb error_nested_1_maps_outside_memory =
      o_nested_1_exists
    & aic_dp_cmd_gen_pkg::loop_maps_outside_memory(
        .start       (i_nested_1.start),
        .length      (i_nested_1.length),
        .memory_depth(DpCommandMemoryDepth)
      );

  //////////////////////////////////
  // Errors: Program Segmentation //
  //////////////////////////////////
  // Pre-caclulate some additional pointers for the ranges
  aic_dp_cmd_gen_pkg::_loop_pointer_t nested_0_start_plus_one;
  aic_dp_cmd_gen_pkg::_loop_pointer_t nested_0_end_minus_one;

  aic_dp_cmd_gen_pkg::_loop_pointer_t nested_1_start_plus_one;

  // Caclulate some flags for the range comaprisons, the conditional is to avoid over or underflows at the extremes.
  always_comb nested_0_start_plus_one = i_nested_0.start + aic_dp_cmd_gen_pkg::loop_pointer_t'(~&i_nested_0.start);
  always_comb nested_0_end_minus_one  =   nested_0_end   - aic_dp_cmd_gen_pkg::_loop_pointer_t'(|nested_0_end);

  always_comb nested_1_start_plus_one = i_nested_1.start + aic_dp_cmd_gen_pkg::loop_pointer_t'(~&i_nested_1.start);

  logic error_nested_0_segfault;
  logic error_nested_1_segfault;
  logic error_nested_order;
  logic error_nested_nesting;
  logic error_nested_overlap;

  always_comb error_nested_0_segfault =
      o_nested_0_exists
    & aic_dp_cmd_gen_pkg::nested_loop_has_segmentation_fault(
        .main_start   (i_main.start),
        .main_length  (i_main.length),
        .nested_start (i_nested_0.start),
        .nested_length(i_nested_0.length)
      );

  always_comb error_nested_1_segfault =
      o_nested_1_exists
    & aic_dp_cmd_gen_pkg::nested_loop_has_segmentation_fault(
        .main_start   (i_main.start),
        .main_length  (i_main.length),
        .nested_start (i_nested_1.start),
        .nested_length(i_nested_1.length)
      );

  always_comb error_nested_order =
       both_nested_exist
    & (i_nested_1.start < i_nested_0.start);

  always_comb error_nested_nesting =
       both_nested_exist
    &  (
        (   aic_dp_cmd_gen_pkg::_loop_pointer_t'(i_nested_0.start) inside {[nested_1_start_plus_one:nested_1_end]}
          & nested_0_end inside {[nested_1_start_plus_one:nested_1_end]}
        )
      | ((i_nested_0.start == i_nested_1.start) & (i_nested_0.length < i_nested_1.length))
    );

  // Overlap only makes sense if both loops have ranges
  always_comb error_nested_overlap =
       both_nested_exist
    & (
        (aic_dp_cmd_gen_pkg::_loop_pointer_t'(i_nested_1.start) inside {[nested_0_start_plus_one:nested_0_end]} & (nested_1_end > nested_0_end))
      | (nested_1_end inside {[aic_dp_cmd_gen_pkg::_loop_pointer_t'(i_nested_0.start):nested_0_end_minus_one]} & (i_nested_1.start < i_nested_0.start))
    )
    &  i_nested_0.length > aic_dp_cmd_gen_pkg::loop_length_t'(1)
    &  i_nested_1.length > aic_dp_cmd_gen_pkg::loop_length_t'(1);

  ///////////////////
  // Error Packing //
  ///////////////////
  // We are not using all fields here deliberately
  always_comb o_loop_errors = '{
    main_0_length:     error_main_maps_outside_memory,
    nested_0_length:   error_nested_0_maps_outside_memory,
    nested_1_length:   error_nested_1_maps_outside_memory,
    nested_0_segfault: error_nested_0_segfault,
    nested_1_segfault: error_nested_1_segfault,
    nested_order:      error_nested_order,
    nested_nesting:    error_nested_nesting,
    nested_overlap:    error_nested_overlap,
    default: 1'b0
  };

endmodule
