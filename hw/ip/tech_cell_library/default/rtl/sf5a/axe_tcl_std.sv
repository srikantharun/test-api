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
  BUF_D4_N_S6TR_C54L08 u_tc_lib_std_buf (
    .Y(o_z),
    .A(i_a)
  );
endmodule


/// Combinational Inverter
///
module axe_tcl_std_inverter (
  input  logic i_a,
  output logic o_z
);
  INV_D4_N_S6TR_C54L08 u_tc_lib_std_inv (
    .Y(o_z),
    .A(i_a)
  );
endmodule


/// Combinatorial 2 input AND gate
///
module axe_tcl_std_and2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);
  wire internal_nand;

  NAND2_D2_N_S6TR_C54L08 u_tc_lib_std_nand (
    .Y(internal_nand),
    .A(i_a),
    .B(i_b)
  );

  INV_D4_N_S6TR_C54L08 u_tc_lib_std_inv (
    .Y(o_z),
    .A(internal_nand)
  );
endmodule


/// Combinatorial 3 input AND gate
///
module axe_tcl_std_and3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);
  wire internal_nand;

  NAND3_D2_N_S6TR_C54L08 u_tc_lib_std_nand (
    .Y(internal_nand),
    .A(i_a),
    .B(i_b),
    .C(i_c)
  );

  INV_D4_N_S6TR_C54L08 u_tc_lib_std_inv (
    .Y(o_z),
    .A(internal_nand)
  );
endmodule


/// Combinatorial 2 input NAND gate
///
module axe_tcl_std_nand2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);
  NAND2_D2_N_S6TR_C54L08 u_tc_lib_std_nand (
    .Y(o_z),
    .A(i_a),
    .B(i_b)
  );
endmodule


/// Combinatorial 3 input NAND gate
///
module axe_tcl_std_nand3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);
  NAND3_D2_N_S6TR_C54L08 u_tc_lib_std_nand (
    .Y(o_z),
    .A(i_a),
    .B(i_b),
    .C(i_c)
  );
endmodule


/// Combinatorial 2 input OR gate
///
module axe_tcl_std_or2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);
  wire internal_nor;

  NOR2_D2_N_S6TR_C54L08 u_tc_lib_std_nor (
    .Y(internal_nor),
    .A(i_a),
    .B(i_b)
  );

  INV_D4_N_S6TR_C54L08 u_tc_lib_std_inv (
    .Y(o_z),
    .A(internal_nor)
  );
endmodule


/// Combinatorial 3 input OR gate
///
module axe_tcl_std_or3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);
  wire internal_nor;

  NOR3_D2_N_S6TR_C54L08 u_tc_lib_std_nor (
    .Y(internal_nor),
    .A(i_a),
    .B(i_b),
    .C(i_c)
  );

  INV_D4_N_S6TR_C54L08 u_tc_lib_std_inv (
    .Y(o_z),
    .A(internal_nor)
  );
endmodule


/// Combinatorial 2 input NOR gate
///
module axe_tcl_std_nor2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);
  NOR2_D2_N_S6TR_C54L08 u_tc_lib_std_nor (
    .Y(o_z),
    .A(i_a),
    .B(i_b)
  );
endmodule


/// Combinatorial 3 input NOR gate
///
module axe_tcl_std_nor3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);
  NOR3_D2_N_S6TR_C54L08 u_tc_lib_std_nor (
    .Y(o_z),
    .A(i_a),
    .B(i_b),
    .C(i_c)
  );
endmodule


/// Combinatorial 2 input XOR gate
///
module axe_tcl_std_xor2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);
  XOR2_D2_N_S6TR_C54L08 u_tc_lib_std_xor (
    .Y(o_z),
    .A(i_a),
    .B(i_b)
  );
endmodule


/// Combinatorial 3 input XOR gate
///
module axe_tcl_std_xor3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);
  XOR3_D2_N_S6TR_C54L08 u_tc_lib_std_xor (
    .Y(o_z),
    .A(i_a),
    .B(i_b),
    .C(i_c)
  );
endmodule


/// Combinatorial 2 input XNOR gate
///
module axe_tcl_std_xnor2 (
  input  logic i_a,
  input  logic i_b,
  output logic o_z
);
  XNOR2_D2_N_S6TR_C54L08 u_tc_lib_std_xnor (
    .Y(o_z),
    .A(i_a),
    .B(i_b)
  );
endmodule


/// Combinatorial 3 input XNOR gate
///
module axe_tcl_std_xnor3 (
  input  logic i_a,
  input  logic i_b,
  input  logic i_c,
  output logic o_z
);
  XNOR3_D2_N_S6TR_C54L08 u_tc_lib_std_xnor (
    .Y(o_z),
    .A(i_a),
    .B(i_b),
    .C(i_c)
  );
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
  MXT2_D2_N_S6TR_C54L08 u_tc_lib_std_mux (
    .Y (o_z),
    .A (i_a),
    .B (i_b),
    .S0(i_sel)
  );
endmodule
