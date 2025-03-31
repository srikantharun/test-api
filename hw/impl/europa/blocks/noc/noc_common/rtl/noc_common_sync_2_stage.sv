// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owners: Tasos Psarras <anastasios.psarras@axelera.ai>
//         Joao Martins <joao.martins@axelera.ai>
//
// Description: This is the Customer Cell that's instantiated by FlexNoC
//              in place of a 2-stage synchronizer. This does *not* comply with
//              Europa I/O naming requirements. We *cannot* fix this
//              because FlexNoC does not allow us to modify the pin names

module noc_common_sync_2_stage
(
    input  wire  CLK,
    input  logic I,
    output logic O,
    input  wire  RSTN
);

  axe_tcl_seq_sync #(
    .SyncStages(2),
    .ResetValue(0),
    .Ratio(0)
  ) i_sync_2dff(
    .i_clk  (CLK),
    .i_rst_n(RSTN),
    .i_d    (I),
    .o_q    (O)
  );

endmodule
