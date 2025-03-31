// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>
//        Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Package containing pre-defined LFSR taps for different lengths
package cc_cnt_lfsr_pkg;

  /// Taps for length 16 as used in the MVM bist
  // verilog_lint: waive-start line-length
  parameter logic [15:0] AX_LFSR_TAPS_016 = (16)'(1'b1 << 0) | (16)'(1'b1 << 1) | (16)'(1'b1 << 3) | (16)'(1'b1 << 12);
  // verilog_lint: waive-stop line-length
endpackage
