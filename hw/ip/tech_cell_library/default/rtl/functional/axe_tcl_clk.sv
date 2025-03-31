// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Description: Wrappers for balances tech_cells to be used in clocking and reset networks

/// Clock buffer/repeater
///
module axe_tcl_clk_buffer (
  /// Input clock
  input  wire i_clk,
  /// Output clock
  output wire o_clk
);

  assign o_clk = i_clk;
endmodule


/// Clock inverter
///
module axe_tcl_clk_inverter (
  /// Input clock
  input  wire i_clk,
  /// Output clock, negated
  output wire o_clk
);

  assign o_clk = ~i_clk;
endmodule


/// Clock balanced AND
///
module axe_tcl_clk_and2 (
  /// Input clock 0
  input  wire i_clk0,
  /// Input clock 1
  input  wire i_clk1,
  /// Output clock
  output wire o_clk
);

  assign o_clk = i_clk0 & i_clk1;
endmodule


/// Clock balanced OR
///
module axe_tcl_clk_or2 (
  /// Input clock 0
  input  wire i_clk0,
  /// Input clock 1
  input  wire i_clk1,
  /// Output clock
  output wire o_clk
);

  assign o_clk = i_clk0 | i_clk1;
endmodule


/// Clock balanced XOR
///
module axe_tcl_clk_xor2 (
  /// Input clock 0
  input  wire i_clk0,
  /// Input clock 1
  input  wire i_clk1,
  /// Output clock
  output wire o_clk
);

  assign o_clk = i_clk0 ^ i_clk1;
endmodule


/// Clock balanced multiplexer
///
module axe_tcl_clk_mux2 (
  /// Input clock 0
  input  wire i_clk0,
  /// Input clock 1
  input  wire i_clk1,
  // doc sync i_clk
  /// Select input clock
  /// `0`: Select index 0
  /// `1`: Select index 1
  input  logic i_sel,
  // doc async
  /// Output clock
  output wire  o_clk
);

  assign o_clk = i_sel ? i_clk1 : i_clk0;
endmodule


/// Integrated clock gating cell
///
module axe_tcl_clk_gating (
  /// Clock, positive edge triggered
  input  wire  i_clk,
  // doc sync i_clk
  /// Enable the clock downstream
  input  logic i_en,
  /// Test mode bypass, when 1 the downstream clock is alwways enabled
  input  logic i_test_en,
  // doc async
  /// Output clock
  output wire  o_clk
);

  logic enable;

  always_latch begin : latch_low
    if (!i_clk) enable <= i_en | i_test_en;
  end

  assign o_clk = i_clk & enable;
endmodule
