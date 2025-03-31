// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Helper functions for the Clock Crossing Modules
///
package axe_ccl_cdc_pkg;

  /// The phases a CDC goes through when the state is reset from either side.
  typedef enum logic [1:0] {
    FLUSH_PHASE_IDLE,
    FLUSH_PHASE_ISOLATE,
    FLUSH_PHASE_FLUSH,
    FLUSH_PHASE_POST_FLUSH
  } flush_phase_e;

  /// Calculate the reset index for the pointer to reset to.
  function automatic int unsigned get_rst_bin_index(
    /// The FIFO Depth
    int unsigned depth
  );
    int unsigned distance_to_next_lower_power_of_2;
    distance_to_next_lower_power_of_2 = depth - cc_math_pkg::next_power_of_2(depth, 1'b1);
    return depth / 2 - distance_to_next_lower_power_of_2;
  endfunction

  /// Calculate at elaboration time a graycode conversion
  function automatic int unsigned bin_to_gray(
    /// Binary representation
    int unsigned binary
  );
    return binary ^ (binary >> 1);
  endfunction

endpackage
