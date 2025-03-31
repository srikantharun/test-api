// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// Common package containing utility functions.
///
package cc_utils_pkg;

  typedef enum bit[1:0] {
    B,
    KiB,
    MiB
  } mem_units_e;

  /// Memory Capacity in bytes.
  ///
  /// Args:
  /// - size (int unsigned): size
  /// - base_unit (mem_units): base unit
  ///
  /// Returns:
  /// - (int unsigned): Return the capacity of memory in bytes
  ///
  function automatic int unsigned mem_capacity(
    int unsigned size,
    mem_units_e base_unit
  );
    unique case (base_unit)
      // verilog_lint: waive case-missing-default
      B: return size;
      KiB: return size*1024;
      MiB: return size*1024*1024;
    endcase
  endfunction

endpackage
