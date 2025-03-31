// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owners: Tasos Psarras <anastasios.psarras@axelera.ai>
//         Joao Martins <joao.martins@axelera.ai>
//
// Description: This is the Customer Cell that's instantiated by FlexNoC
//              in place of a Clock Gater. This does *not* comply with
//              Europa I/O naming requirements. We *cannot* fix this
//              because FlexNoC does not allow us to modify the pin names

module noc_common_clk_gater
(
    input  wire  CLKIN,
    output wire  CLKOUT,
    input  logic EN,
    input  wire  RSTN, // unconnected!
    input  logic TE
);

  axe_tcl_clk_gating i_clk_gater(
      .i_clk     (CLKIN),
      .i_en      (EN),
      .i_test_en (TE),
      .o_clk     (CLKOUT)
  );
endmodule
