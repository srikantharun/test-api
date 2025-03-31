// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// A clock or tree implementation comprised of axe_tcl_clk_or2 cells.
/// Output has a buffer to increase strength.
///
module axe_ccl_clk_or_tree #(
  /// The number of input clocks
  parameter int unsigned NumClocks = 2
)(
  /// Clock inputs
  input  wire i_clk[NumClocks],
  /// Clock outputs
  output wire o_clk
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if (NumClocks == 0) $fatal(1, "Parameter: 'NumClocks' Bust be larger than 0;");

  /////////////////////////
  // Derived Localparams //
  /////////////////////////
  localparam int unsigned NumWires = 2*NumClocks - 1;
  // We rely on integer rounding down division here
  localparam int unsigned NumNodes = NumWires / 2;

  wire clk[NumWires];

  ////////////////////
  // Connect inputs //
  ////////////////////
  for (genvar inp_idx = 0; inp_idx < NumClocks; inp_idx++) begin : gen_inp
    assign clk[2*NumClocks - 2 - inp_idx] = i_clk[inp_idx];
  end

  ///////////////////
  // Generate tree //
  ///////////////////
  for (genvar node_idx = 0; unsigned'(node_idx) < NumNodes; node_idx++) begin : gen_node
    axe_tcl_clk_or2 u_clk_or (
      .i_clk0(clk[node_idx*2+2]),
      .i_clk1(clk[node_idx*2+1]),
      .o_clk (clk[node_idx])
    );
  end

  ///////////////////////
  // Output clk buffer //
  ///////////////////////
  axe_tcl_clk_buffer u_clk_buffer (
    .i_clk(clk[0]),
    .o_clk
  );
endmodule
