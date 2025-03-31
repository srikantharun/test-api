// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Population decoder (Number of asserted 1 bits in a vector)
///
module cc_decode_population #(
  /// The input data width
  parameter int unsigned  DataWidth = 5,
  /// Derived parameter: The Binary Width
  localparam int unsigned PopCntWidth = cc_math_pkg::index_width(DataWidth),
  /// Derived parameter: The type of the input vector
  localparam type data_t  = logic[DataWidth-1:0],
  /// Derived parameter: The type of the count representation, Not one bit wider!
  localparam type count_t = logic[PopCntWidth:0]
)(
  /// Input data to count the bits in
  input  data_t  i_data,
  /// Decoded number of set bits
  ///
  /// Note: The width is one bit wider to acount for power of 2 widths.
  output count_t o_count
);
  ////////////////
  // Sanitation //
  ////////////////
  if (DataWidth == 0) $fatal(1, "Parameter: 'DataWidth' Must not be 0;");

  //////////////
  // Addition //
  //////////////

  always_comb begin
    o_count = count_t'(0);
    foreach (i_data[i]) o_count += count_t'(i_data[i]);
  end
endmodule
