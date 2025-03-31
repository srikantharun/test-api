// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: {{ cookiecutter.author_full_name }} <{{ cookiecutter.author_email }}>

/// SVA of {{ cookiecutter.design_name }}
///

`ifndef {{ cookiecutter.design_name.upper() }}_SVA_SV
`define {{ cookiecutter.design_name.upper() }}_SVA_SV

module {{ cookiecutter.design_name }}_sva #(
  /// TODO:description_of_parameter
  parameter int unsigned __parameter
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Asynchronous reset, active low
  input  wire i_rst_n,


);
  // =====================================================
  // Local parameters
  // =====================================================

  // =====================================================
  // Type definition
  // =====================================================

  // =====================================================
  // Signal declarations
  // =====================================================

  // =====================================================
  // Bind signals
  // =====================================================

  // =====================================================
  // Properties
  // =====================================================

  // =====================================================
  // Assumes
  // =====================================================

  // =====================================================
  // Assertions
  // =====================================================

  // =====================================================
  // Covers
  // =====================================================

endmodule

`endif // {{ cookiecutter.design_name.upper() }}_SVA_SV
