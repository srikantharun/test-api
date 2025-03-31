/// Multiplexer using a onehot0 select line
///
module axe_ccl_mux_onehot #(
  /// The data width if the default parameter `data_t logic[DataWidth-1:0]` is used.
  /// Not needed if `data_t` is specified.
  parameter int unsigned DataWidth = 0,
  /// The actual data type used, only use of parameter `DataWidth`
  parameter type data_t = logic[DataWidth-1:0],
  /// The number of inputs
  parameter int unsigned NumInputs = 5
) (
  /// Input data
  input  data_t [NumInputs-1:0] i_data,
  /// Onehot0 select line
  input  logic  [NumInputs-1:0] i_select,
  /// Muxed data
  output data_t                 o_data
);

  localparam int unsigned ActualDataWidth = $bits(o_data);

  logic [NumInputs-1:0] mux_data[ActualDataWidth];

  for (genvar data_idx = 0; unsigned'(data_idx) < ActualDataWidth; data_idx++) begin : gen_outer
    for (genvar input_idx = 0; unsigned'(input_idx) < NumInputs; input_idx++) begin : gen_inner
      always_comb mux_data[data_idx][input_idx] = i_data[input_idx][data_idx];
    end

    always_comb o_data[data_idx] = |(i_select & mux_data[data_idx]);
  end

`ifndef SYNTHESIS
`ifdef AXE_CCL_ASSERT_ON
  a_hot_one : assert property(
    @(i_sel) $onehot0(i_sel))
      else $error("`i_select` signal must be hot1 or zero.");
`endif
`endif

endmodule
