// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Common package containing synthesizable constant math functions.
///
package cc_math_pkg;

  /// Ceiled division of two natural integers.
  ///
  /// Args:
  /// - dividend (int unsigned): dividend
  /// - divisor (int unsigned): divisor
  ///
  /// Returns:
  /// - (int unsigned): result of the division rounded towards infinity
  ///
  /// Raises:
  /// - $fatal if divisor is 0
  function automatic int unsigned ceil_div(
    int unsigned dividend,
    int unsigned divisor
  );
    if (divisor == 0) begin : div_by_zero_fatal
      $fatal(1, "Division by zero in ceil_div");
    end

    return (dividend + divisor - 1) / divisor;
  endfunction

  /// Return the number of bits required to represent the given number of indexes
  ///
  /// Index width required to be able to represent up to `num_idx` indices as a binary
  /// encoded signal.
  /// Ensures that the minimum width if an index signal is `1`, regardless of parametrization.
  ///
  /// Sample usage in type definition:
  /// As parameter:
  ///   `parameter type idx_t = logic[cc_math_pkg::index_width(NumIdx)-1:0]`
  /// As typedef:
  ///   `typedef logic [cc_math_pkg::index_width(NumIdx)-1:0] idx_t`
  ///
  /// Args:
  /// - num_indexes (int unsigned): number of indexes to represent
  ///
  /// Returns:
  /// - (int unsigned): number of bits required to represent the given number of indexes
  function automatic int unsigned index_width(
    int unsigned num_indexes
  );
    return (num_indexes > 1) ? unsigned'($clog2(num_indexes)) : 1;
  endfunction

  /// Return the next power of 2 for the given number.
  ///
  /// If number is already a power of to it is returned.
  ///
  /// Args:
  /// - number (int unsigned): number to find the next power of 2 for
  /// - higher (bit)
  ///     - `0`: the next lower power of 2 is returned
  ///     - `1`: the next higher power of 2 is returned
  /// Returns:
  /// - (int unsigned): next power of 2
  function automatic int unsigned next_power_of_2(
    int unsigned number,
    bit          higher
  );
    automatic int unsigned log_value;
    log_value = unsigned'($clog2(number));

    if (unsigned'(2**log_value) == number) return number;
    else                                   return unsigned'(2**(log_value+unsigned'(int'(higher))));
  endfunction

endpackage
