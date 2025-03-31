// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// Grouping the config signals

module axe_tcl_sram_cfg #(
    parameter int unsigned NUM_SRAMS = 1,
    /// parameterized type for implementation specific inputs
    localparam type impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
    /// parameterized type for implementation specific outputs
    localparam type impl_oup_t = axe_tcl_sram_pkg::impl_oup_t
  ) (
    /// implementation specific inputs
    input  impl_inp_t                 i_s,
    /// implementation specific outputs
    output impl_oup_t                 o_s,
    /// implementation specific outputs
    output impl_inp_t [NUM_SRAMS-1:0] o_m,
    /// implementation specific inputs
    input  impl_oup_t [NUM_SRAMS-1:0] i_m
  );

  logic [NUM_SRAMS-1:0] prn;
  logic [NUM_SRAMS-1:0] pde;

  always_comb begin
    foreach (prn[sram]) begin
      prn[sram] = i_m[sram].prn;
    end
  end

  always_comb begin
    foreach (o_m[sram]) begin
      o_m[sram].pde    = pde[sram];
      o_m[sram].mcs    = i_s.mcs;
      o_m[sram].mcsw   = i_s.mcsw;
      o_m[sram].ret    = i_s.ret;
      o_m[sram].se     = i_s.se;
      o_m[sram].adme   = i_s.adme;
    end
  end

  always_comb {o_s.prn, pde} = {prn, i_s.pde};

endmodule
