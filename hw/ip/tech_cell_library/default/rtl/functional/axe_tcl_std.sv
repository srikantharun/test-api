// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Combinatorial Buffer
///
module axe_tcl_std_buffer (
  input  logic i_a,
  output logic o_z
);

  assign o_z = i_a;
endmodule


/// Combinational Inverter
///
module axe_tcl_std_inverter (
  input  logic i_a,
  output logic o_z
);

  assign o_z = ~i_a;
endmodule


/// Combinatorial 2 input AND gate
///
module axe_tcl_std_and2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);

  assign o_z = &{i_a, i_b};
endmodule


/// Combinatorial 3 input AND gate
///
module axe_tcl_std_and3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);

  assign o_z = &{i_a, i_b, i_c};
endmodule


/// Combinatorial 2 input NAND gate
///
module axe_tcl_std_nand2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);

  assign o_z = ~&{i_a, i_b};
endmodule


/// Combinatorial 3 input NAND gate
///
module axe_tcl_std_nand3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);

  assign o_z = ~&{i_a, i_b, i_c};
endmodule


/// Combinatorial 2 input OR gate
///
module axe_tcl_std_or2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);

  assign o_z = |{i_a, i_b};
endmodule


/// Combinatorial 3 input OR gate
///
module axe_tcl_std_or3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);

  assign o_z = |{i_a, i_b, i_c};
endmodule


/// Combinatorial 2 input NOR gate
///
module axe_tcl_std_nor2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);

  assign o_z = ~|{i_a, i_b};
endmodule


/// Combinatorial 3 input NOR gate
///
module axe_tcl_std_nor3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);

  assign o_z = ~|{i_a, i_b, i_c};
endmodule


/// Combinatorial 2 input XOR gate
///
module axe_tcl_std_xor2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);

  assign o_z = ^{i_a, i_b};
endmodule


/// Combinatorial 3 input XOR gate
///
module axe_tcl_std_xor3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);

  assign o_z = ^{i_a, i_b, i_c};
endmodule


/// Combinatorial 2 input XNOR gate
///
module axe_tcl_std_xnor2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);

  assign o_z = ~^{i_a, i_b};
endmodule


/// Combinatorial 3 input XNOR gate
///
module axe_tcl_std_xnor3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);

  assign o_z = ~^{i_a, i_b, i_c};
endmodule


/// Combinational 2 port Multiplexer
///
/// **Do not use for CLOCKS or RESETS!**
module axe_tcl_std_mux2 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_sel,
  output logic o_z
);

  assign o_z = i_sel ? i_b : i_a;
endmodule
