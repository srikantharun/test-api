// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Bond <andrew.bond@axelera.ai>

/// Axelera technology specific cell
/// Required for synthesis of CDNS SDHC

module cdnsdru_scan_mux_synth
(
      input  wire   scan_mode_en_in,
      input  wire   scan_signal_in,
      input  wire   fcn_signal_in,
      output logic  fcn_signal_out
);

    // TODO - replace with std cell
    always_comb fcn_signal_out = (scan_mode_en_in) ? scan_signal_in : fcn_signal_in;
endmodule
