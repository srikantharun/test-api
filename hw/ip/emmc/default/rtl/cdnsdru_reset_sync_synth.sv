// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Bond <andrew.bond@axelera.ai>

/// Axelera technology specific cell
/// Required for synthesis of CDNS SDHC

module cdnsdru_reset_sync_synth
#(
    parameter int unsigned NUM_FLOPS = 3
)(
  input  wire  sync_clock_in,
  input  wire  reset_in_n,
  input  logic upstream_reset_in_n,
  output logic reset_n_synced
);

    // TODO - check
    // using standard reset - do we need a reset resync?
    axe_tcl_seq_sync #(.SyncStages(NUM_FLOPS)) u_axe_tcl_seq_sync (
        .i_clk(sync_clock_in),
        .i_rst_n(reset_in_n),
        .i_d(upstream_reset_in_n),
        .o_q(reset_n_synced)
    );

endmodule
