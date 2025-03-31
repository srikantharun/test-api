// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>
//
// Description: DFT Pad Mux for axe_tcl_pad_input pads


///
///
module axe_ccl_dft_pad_mux_input #(
  /// Implemetation specific input signals to the pad from the core.
  /// This can be drive strength, schmitt-trigger, etc.
  parameter type impl_inp_t = logic,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = logic
)(
  ////////////////////////
  // Core side selector //
  ////////////////////////
  input  logic      i_dft_enable,

  ///////////////////////////////////////
  // Core side functional connectivity //
  ///////////////////////////////////////
  /// Core side output signal from the pad, received
  output logic      o_func_inp,
  /// Core side enable to gate the received input
  input  logic      i_func_inp_en,
  /// Pull type: `0`: pull-down, `1`: pull-up
  input  logic      i_func_pull_type,
  /// Pull enable
  input  logic      i_func_pull_en,
  /// Implemetation specific signals to the pad
  input  impl_inp_t i_func_impl_inp,
  /// Implemetation specific signals from the pad
  output impl_oup_t o_func_impl_oup,

  ////////////////////////////////
  // Core side dft connectivity //
  ////////////////////////////////
  /// Core side output signal from the pad, received
  output logic      o_dft_inp,
  /// Core side enable to gate the received input
  input  logic      i_dft_inp_en,
  /// Pull type: `0`: pull-down, `1`: pull-up
  input  logic      i_dft_pull_type,
  /// Pull enable
  input  logic      i_dft_pull_en,
  /// Implemetation specific signals to the pad
  input  impl_inp_t i_dft_impl_inp,
  /// Implemetation specific signals from the pad
  output impl_oup_t o_dft_impl_oup,

  ////////////////////////////
  // Pad side connecitivity //
  ////////////////////////////
  /// Core side output signal from the pad, received
  input  logic      i_padside_inp,
  /// Core side enable to gate the received input
  output logic      o_padside_inp_en,
  /// Pull type: `0`: pull-down, `1`: pull-up
  output logic      o_padside_pull_type,
  /// Pull enable
  output logic      o_padside_pull_en,
  /// Implemetation specific signals to the pad
  output impl_inp_t o_padside_impl_inp,
  /// Implemetation specific signals from the pad
  input  impl_oup_t i_padside_impl_oup
);

  typedef struct packed {
    logic inp_en;
    logic pull_type;
    logic pull_en;
    impl_inp_t impl_inp;
  } core_to_pad_t;

  typedef struct packed {
    logic inp;
    impl_oup_t impl_oup;
  } pad_to_core_t;

  core_to_pad_t [1:0] from_core_to_mux;
  pad_to_core_t [1:0] from_mux_to_core;

  core_to_pad_t       from_mux_to_pad;
  pad_to_core_t       from_pad_to_mux;

  always_comb begin
    from_core_to_mux[0] = '{
      inp_en   : i_func_inp_en,
      pull_type: i_func_pull_type,
      pull_en  : i_func_pull_en,
      impl_inp : i_func_impl_inp
    };
    from_core_to_mux[1] = '{
      inp_en   : i_dft_inp_en,
      pull_type: i_dft_pull_type,
      pull_en  : i_dft_pull_en,
      impl_inp : i_dft_impl_inp
    };
  end

  always_comb from_pad_to_mux = '{
    inp     : i_padside_inp,
    impl_oup: i_padside_impl_oup
  };

  axe_ccl_dft_pad_mux_core #(
    .core_to_pad_t(core_to_pad_t),
    .pad_to_core_t(pad_to_core_t)
  ) u_core (
    .i_dft_enable,
    .i_from_core_to_mux(from_core_to_mux),
    .o_from_mux_to_core(from_mux_to_core),
    .o_from_mux_to_pad (from_mux_to_pad),
    .i_from_pad_to_mux (from_pad_to_mux)
  );

  // Core-to-pad outputs
  always_comb o_padside_inp_en    = from_mux_to_pad.inp_en;
  always_comb o_padside_pull_type = from_mux_to_pad.pull_type;
  always_comb o_padside_pull_en   = from_mux_to_pad.pull_en;
  always_comb o_padside_impl_inp  = from_mux_to_pad.impl_inp;

  // Pad-to-core outputs
  always_comb o_func_inp      = from_mux_to_core[0].inp;
  always_comb o_func_impl_oup = from_mux_to_core[0].impl_oup;

  always_comb o_dft_inp       = from_mux_to_core[1].inp;
  always_comb o_dft_impl_oup  = from_mux_to_core[1].impl_oup;

endmodule : axe_ccl_dft_pad_mux_input
