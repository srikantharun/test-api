// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Array of synchronizer cells for slow sideband signals.
///
module cc_cdc_sync_array #(
  /// The number of synchronization stages for all synchronizers
  parameter int unsigned SyncStages = 1,
  /// The array width
  parameter int unsigned Width = 1,
  /// The reset state for the sync cells
  parameter logic[Width-1:0] ResetValues = '0
)(
  /// Clock, positive edge triggered
  input  wire             i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire             i_rst_n,
  /// Asynchronous data to be synched to 'i_clk'
  input  logic[Width-1:0] i_data,
  /// Synchronized data
  output logic[Width-1:0] o_data
);
  // Parameter checks
  if (Width == 0) $fatal(1, "Parameter: 'Width' must be greater than 0;");

  for (genvar i = 0; unsigned'(i) < Width; i++) begin : gen_syncs
    axe_tcl_seq_sync #(
      .SyncStages(SyncStages),
      .ResetValue(ResetValues[i])
    ) u_axe_tcl_seq_sync (
      .i_clk,
      .i_rst_n,
      .i_d    (i_data[i]),
      .o_q    (o_data[i])
    );
  end
endmodule
