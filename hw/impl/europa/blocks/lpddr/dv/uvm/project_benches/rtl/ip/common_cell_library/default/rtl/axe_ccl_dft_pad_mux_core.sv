// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>
//
// Description:
// DFT Pad Mux Core
// Should not be instantiated standalone
// Instantiate instead:
// - axe_ccl_dft_pad_mux_input
// - axe_ccl_dft_pad_mux_inout
// - axe_ccl_dft_pad_mux_output


///
///
module axe_ccl_dft_pad_mux_core #(
  parameter type core_to_pad_t = logic,
  parameter type pad_to_core_t = logic
)(
  /// Core side master selector
  input  logic               i_dft_enable,

  /// Coreside signals
  input  core_to_pad_t [1:0] i_from_core_to_mux,
  output pad_to_core_t [1:0] o_from_mux_to_core,

  /// Padside signals
  output core_to_pad_t       o_from_mux_to_pad,
  input  pad_to_core_t       i_from_pad_to_mux
);

  typedef union packed {
    core_to_pad_t s;
    logic [$bits(core_to_pad_t)-1:0] b;
  } core_to_pad_u_t;

  typedef union packed {
    pad_to_core_t s;
    logic [$bits(pad_to_core_t)-1:0] b;
  } pad_to_core_u_t;

  core_to_pad_u_t [1:0] from_core_to_mux;
  core_to_pad_u_t       from_mux_to_pad;
  pad_to_core_u_t       from_pad_to_mux;
  pad_to_core_u_t [1:0] from_mux_to_core;

  always_comb from_core_to_mux = i_from_core_to_mux;
  always_comb from_pad_to_mux  = i_from_pad_to_mux;

  for (genvar g = 0; unsigned'(g) < $bits(core_to_pad_u_t); g++) begin : gen_core_to_pad_muxes
    axe_tcl_std_mux2 u_mux (
      .i_a  (from_core_to_mux[0].b[g]),
      .i_b  (from_core_to_mux[1].b[g]),
      .i_sel(i_dft_enable),
      .o_z  (from_mux_to_pad.b[g])
    );
  end

  for (genvar g = 0; unsigned'(g) < $bits(pad_to_core_u_t); g++) begin : gen_pad_to_core_demuxes_func
    // Silence functional output in dft mode
    axe_tcl_std_mux2 u_mux (
      .i_a  (from_pad_to_mux.b[g]),
      .i_b  (1'b0),
      .i_sel(i_dft_enable),
      .o_z  (from_mux_to_core[0].b[g])
    );
  end

  for (genvar g = 0; unsigned'(g) < $bits(pad_to_core_u_t); g++) begin : gen_pad_to_core_demuxes_dft
    // Silence DFT output to core in functional mode
    axe_tcl_std_mux2 u_mux (
      .i_a  (1'b0),
      .i_b  (from_pad_to_mux.b[g]),
      .i_sel(i_dft_enable),
      .o_z  (from_mux_to_core[1].b[g])
    );
  end

  always_comb o_from_mux_to_core = from_mux_to_core;
  always_comb o_from_mux_to_pad  = from_mux_to_pad;

endmodule : axe_ccl_dft_pad_mux_core
