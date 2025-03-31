// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Convert from Binary to Graycode or vice versa.
///
module axe_ccl_decode_gray #(
  /// The conversion mode:
  ///
  /// - `0`: Binary Representation to Gray Code
  /// - `1`: Gray Code to Binary Representation
  parameter bit          Mode = 0,
  /// The width of the data (optional if data_t is given)
  parameter int unsigned DataWidth = 16,
  /// The concrete data type used
  parameter type         data_t = logic[DataWidth-1:0]
)(
  /// Input data to be converted
  input  data_t i_data,
  /// Conversion Result Output
  output data_t o_data
);
  localparam int ResolvedDataWidth = $bits(i_data);

  if (Mode) begin : gen_gray_to_bin
    for (genvar bit_index = 0; bit_index < ResolvedDataWidth; bit_index++) begin : gen_bits
      assign o_data[bit_index] = ^i_data[ResolvedDataWidth-1:bit_index];
    end
  end
  else begin : gen_bin_to_gray
    always_comb o_data = i_data ^ (i_data >> 1);
  end
endmodule
