// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

/// Generic PVT Probe Wrapper IP containing the instance of the PVT Probe
/// Samsung Foundry PVT - LN05LPE

`ifndef PVT_PROBE_WRAPPER_SV
`define PVT_PROBE_WRAPPER_SV
module pvt_probe_wrapper #(
)
(
`ifdef POWER_PINS
  // Probe supply
  inout wire io_avss_ts  ,
  // Probe ground
  inout wire io_avss_gd  ,
  // Probe ibias
`endif
  inout wire io_ibias_ts ,
  // Probe vsense
  inout wire io_vsense_ts
);

  tu_tem0501ar01_ln05lpe_4007002 #(
  ) u_tu_tem0501ar01_ln05lpe_4007002 (
`ifdef POWER_PINS
    .AVSS_TS   ( io_avss_ts   ),
    .AVSS_GD   ( io_avss_gd   ),
`endif
    .IBIAS_TS  ( io_ibias_ts  ),
    .VSENSE_TS ( io_vsense_ts )
);


endmodule

`endif // PVT_PROBE_WRAPPER_SV
