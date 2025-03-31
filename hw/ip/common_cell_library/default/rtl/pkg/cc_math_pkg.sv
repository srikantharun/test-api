// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Common package containing synthesizable constant math functions.
///
/// !!! tip
///
///     The functions in this package can be called as part of parameter declarations during elaboration.
///
package cc_math_pkg;

  /// Ceiled division of two natural integers. The result is rounded towards infinity.
  ///
  function automatic int unsigned ceil_div(
    /// the dividend
    int unsigned dividend,
    /// the divisor
    int unsigned divisor
  );
    `ifndef SYNTHESIS
    if (divisor == 0) begin : div_by_zero_fatal
      $fatal(1, "Division by zero in ceil_div");
    end
    `endif

    return (dividend + divisor - 1) / divisor;
  endfunction

  /// Return the number of bits required to represent the given number of indexes
  ///
  /// Index width required to be able to represent up to `num_idx` indices as a binary
  /// encoded signal.
  /// Ensures that the minimum width if an index signal is `1`, regardless of parametrization.
  ///
  /// !!! tip "Example Usage"
  ///
  ///     === "As parameter"
  ///
  ///         ```verilog
  ///         parameter type idx_t = logic[cc_math_pkg::index_width(NumIdx)-1:0]
  ///         ```
  ///
  ///     === "As typedef"
  ///
  ///          ```verilog
  ///          typedef logic [cc_math_pkg::index_width(NumIdx)-1:0] idx_t
  ///          ```
  ///
  function automatic int unsigned index_width(
    /// number of indexes to represent
    int unsigned num_indexes
  );
    return (num_indexes > 1) ? unsigned'($clog2(num_indexes)) : 1;
  endfunction

  /// Return the next power of 2 for the given number. If number is already a power of to it is returned.
  ///
  function automatic int unsigned next_power_of_2(
    /// number to find the next power of 2 for
    int unsigned number,
    /// - `0`: the next higher power of 2 is returned
    /// - `1`: the next lower  power of 2 is returned
    bit          lower
  );
    int unsigned log_value;
    log_value = unsigned'($clog2(number));

    if (unsigned'(2**log_value) == number) return number;
    else                                   return unsigned'(2**(log_value - unsigned'(int'(lower))));
  endfunction

endpackage
