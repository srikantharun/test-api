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
  // sf5a does not contain a clock buffer, so back to back inverters
  wire clk;

  CLKINV_D4_N_S6TL_C54L08 u_tc_lib_clk_inv0 (
    .Y(clk),
    .A(i_clk)
  );

  CLKINV_D8_N_S6TL_C54L08 u_tc_lib_clk_inv1 (
    .Y(o_clk),
    .A(clk)
  );
endmodule


/// Clock inverter
///
module axe_tcl_clk_inverter (
  /// Input clock
  input  wire i_clk,
  /// Output clock, negated
  output wire o_clk
);
  CLKINV_D8_N_S6TL_C54L08 u_tc_lib_clk_inv (
    .Y(o_clk),
    .A(i_clk)
  );
endmodule


/// Clock balanced AND
///
module axe_tcl_clk_and2 (
  /// Input clock 0
  input  wire i_clk0,
  /// Input clock 0
  input  wire i_clk1,
  /// Output clock
  output wire o_clk
);
  wire clk;

  NAND2_D4_N_S6TL_C54L08 u_tc_lib_clk_nand (
    .Y(clk),
    .A(i_clk0),
    .B(i_clk1)
  );

  CLKINV_D8_N_S6TL_C54L08 u_tc_lib_clk_inv (
    .Y(o_clk),
    .A(clk)
  );
endmodule


/// Clock balanced OR
///
module axe_tcl_clk_or2 (
  /// Input clock 0
  input  wire i_clk0,
  /// Input clock 0
  input  wire i_clk1,
  /// Output clock
  output wire o_clk
);
  wire clk;

  NOR2_D4_N_S6TL_C54L08 u_tc_lib_clk_nor (
    .Y(clk),
    .A(i_clk0),
    .B(i_clk1)
  );

  CLKINV_D8_N_S6TL_C54L08 u_tc_lib_clk_inv (
    .Y(o_clk),
    .A(clk)
  );
endmodule


/// Clock balanced XOR
///
module axe_tcl_clk_xor2 (
  /// Input clock 0
  input  wire i_clk0,
  /// Input clock 0
  input  wire i_clk1,
  /// Output clock
  output wire o_clk
);
  wire clk;

  XNOR2_D4_N_S6TL_C54L08 u_tc_lib_clk_xnor (
    .Y(clk),
    .A(i_clk0),
    .B(i_clk1)
  );

  CLKINV_D8_N_S6TL_C54L08 u_tc_lib_clk_inv (
    .Y(o_clk),
    .A(clk)
  );
endmodule


/// Clock balanced multiplexer
///
module axe_tcl_clk_mux2 (
  /// Input clock 0
  input  wire i_clk0,
  /// Input clock 0
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
  MXT2_D6_N_S6TL_C54L08 u_tc_lib_clk_mux (
    .Y (o_clk),
    .A (i_clk0),
    .B (i_clk1),
    .S0(i_sel)
  );
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
  PREICG_D8_N_S6TL_C54L08 u_tc_lib_clk_en (
    .ECK(o_clk),
    .CK (i_clk),
    .E  (i_en),
    .SE (i_test_en)
  );
endmodule
