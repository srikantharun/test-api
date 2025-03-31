// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Decode a onhot0 signal to a binary number
///
module cc_decode_onehot #(
  /// The Width of the Onehot signal
  parameter int unsigned  OhtWidth = 4,
  /// Derived parameter: Width of the binary signal
  localparam int unsigned BinWidth = cc_math_pkg::index_width(OhtWidth),
  /// Derived parameter: Type of the onehot signal
  localparam type onehot_t = logic[OhtWidth-1:0],
  /// Derived parameter: Type of the binary signal
  localparam type binary_t = logic[BinWidth-1:0]
)(
  /// Input onehot signal to decode
  input  onehot_t i_onehot,
  /// Decoded binary index of the onehot bit
  output binary_t o_binary,
  /// The onehot signal has nothing asserted
  output logic    o_empty,
  /// The input is not a onehot0 signal
  output logic    o_error
);
  ////////////////
  // Sanitation //
  ////////////////
  if (OhtWidth == 0) $fatal(1, "Parameter: 'OhtWidth' must not be 0;");

  /////////////////////
  // Mask Generation //
  /////////////////////

  for (genvar bin_idx = 0; unsigned'(bin_idx) < BinWidth; bin_idx++) begin : gen_bin
    onehot_t oht_mask;

    for (genvar oht_idx = 0; unsigned'(oht_idx) < OhtWidth; oht_idx++) begin : gen_mask
      binary_t temp_oht_index;
      assign   temp_oht_index    = binary_t'(oht_idx);
      assign   oht_mask[oht_idx] = temp_oht_index[bin_idx];
    end

    assign o_binary[bin_idx] = ~o_error & |(oht_mask & i_onehot);
  end

  /////////////////////
  // Flag Generation //
  /////////////////////
  always_comb o_empty = ~|i_onehot;

  typedef logic [BinWidth:0] popcount_t;
  popcount_t popcount;

  cc_decode_population #(
    .DataWidth(OhtWidth)
  ) u_popcount (
    .i_data (i_onehot),
    .o_count(popcount)
  );

  always_comb o_error = popcount > popcount_t'(1);
endmodule
