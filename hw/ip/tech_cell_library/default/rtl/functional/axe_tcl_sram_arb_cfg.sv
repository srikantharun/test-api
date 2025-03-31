// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Emre Kirkaya <emre.kirkaya@axelera.ai>

/// Connecting the config signals arbitrarily

module axe_tcl_sram_arb_cfg #(
    parameter int unsigned NUM_BANKS = 1,
    parameter int unsigned NUM_RAMS  = 1,
    parameter int unsigned NUM_SRAMS = 1,
    parameter int unsigned ARB_CHAIN_ARR [NUM_BANKS][NUM_RAMS][NUM_SRAMS] = '{default:0},
    /// parameterized type for implementation specific inputs
    localparam type impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
    /// parameterized type for implementation specific outputs
    localparam type impl_oup_t = axe_tcl_sram_pkg::impl_oup_t
  ) (
    /// implementation specific inputs
    input  impl_inp_t                                               i_s,
    /// implementation specific outputs
    output impl_oup_t                                               o_s,
    /// implementation specific outputs
    output impl_inp_t [NUM_BANKS-1:0][NUM_RAMS-1:0][NUM_SRAMS-1:0]  o_m,
    /// implementation specific inputs
    input  impl_oup_t [NUM_BANKS-1:0][NUM_RAMS-1:0][NUM_SRAMS-1:0]  i_m
  );

  logic [NUM_BANKS * NUM_RAMS * NUM_SRAMS-1:0]  prn;
  logic [NUM_BANKS * NUM_RAMS * NUM_SRAMS-1:0]  pde;

  always_comb foreach (i_m[bank, ram, sram]) prn[ARB_CHAIN_ARR[bank][ram][sram]] = i_m[bank][ram][sram].prn;

  always_comb begin
    foreach (o_m[bank, ram, sram]) begin
      o_m[bank][ram][sram].pde    = pde[ARB_CHAIN_ARR[bank][ram][sram]];
      o_m[bank][ram][sram].mcs    = i_s.mcs;
      o_m[bank][ram][sram].mcsw   = i_s.mcsw;
      o_m[bank][ram][sram].ret    = i_s.ret;
      o_m[bank][ram][sram].se     = i_s.se;
      o_m[bank][ram][sram].adme   = i_s.adme;
    end
  end

  always_comb {o_s.prn, pde} = {prn, i_s.pde};

endmodule
