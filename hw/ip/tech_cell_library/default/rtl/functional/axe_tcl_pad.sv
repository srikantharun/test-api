// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Description: Models for chip pad technology cells


/// Model of a bidirectional pad instance
///
module axe_tcl_pad_inout #(
  /// Implementation key to select different flavours of the same cell
  parameter ImplementationKey = "horizontal",
  /// Implemetation specific input signals to the pad from the core.
  /// This can be drive strength, schmitt-trigger, etc.
  parameter type impl_inp_t = logic,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = logic,
  /// Implemetation specific power signals
  /// They usually run in parallel to the pads and are managed by `axe_tcl_pad_power`
  parameter type impl_pwr_t = logic
)(
  /// Core side input signal to the pad, to be transmitted
  input  logic i_oup,
  /// Core side enable the pad as an output
  input  logic i_oup_en,
  /// Core side output signal from the pad, received
  output logic o_inp,
  /// Core side enable to gate the received input
  input  logic i_inp_en,
  /// Pull type: `0`: pull-down, `1`: pull-up
  input  logic i_pull_type,
  /// Pull enable
  input  logic i_pull_en,
  /// Implemetation specific signals to the pad
  input  impl_inp_t i_impl,
  /// Implemetation specific signals from the pad
  output impl_oup_t o_impl,
  /// Implemetation specific signals for power management
  input  impl_pwr_t i_impl_pwr,
  /// The pad wire
  inout  wire io_pad
);

  // Model the pull-up/down behaviour
  assign (weak0, weak1) io_pad = i_pull_en ? i_pull_type : 1'bz;

  // Model the output driving of the pad, if not enabled have the pull drive the logic
  assign io_pad = i_oup_en ? i_oup : 1'bz;

  // The core side receiver output
  assign o_inp = i_inp_en & io_pad;

  // Outputs have some values always
  assign o_impl = '0;
endmodule


/// Model of a pure output pad instance
///
module axe_tcl_pad_output #(
  /// Implementation key to select different flavours of the same cell
  parameter ImplementationKey = "horizontal",
  /// Implemetation specific input signals to the pad from the core.
  /// This can be drive strength, schmitt-trigger, etc.
  parameter type impl_inp_t = logic,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = logic,
  /// Implemetation specific power signals
  /// They usually run in parallel to the pads and are managed by `axe_tcl_pad_power`
  parameter type impl_pwr_t = logic
)(
  /// Core side input signal to the pad, to be transmitted
  input  logic i_oup,
  /// Core side enable the pad as an output
  input  logic i_oup_en,
  /// Pull type: `0`: pull-down, `1`: pull-up
  input  logic i_pull_type,
  /// Pull enable
  input  logic i_pull_en,
  /// Implemetation specific signals to the pad
  input  impl_inp_t i_impl,
  /// Implemetation specific signals from the pad
  output impl_oup_t o_impl,
  /// Implemetation specific signals for power management
  input  impl_pwr_t i_impl_pwr,
  /// The pad wire
  output wire o_pad
);

  // Model the pull-up/down behaviour
  assign (weak0, weak1) o_pad = i_pull_en ? i_pull_type : 1'bz;

  // Model the output driving of the pad, if not enabled have the pull drive the logic
  assign o_pad = i_oup_en ? i_oup : 1'bz;

  // Outputs have some values always
  assign o_impl = '0;
endmodule


/// Model of a pure input pad instance
///
module axe_tcl_pad_input #(
  /// Implementation key to select different flavours of the same cell
  parameter ImplementationKey = "horizontal",
  /// Implemetation specific input signals to the pad from the core.
  /// This can be drive strength, schmitt-trigger, etc.
  parameter type impl_inp_t = logic,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = logic,
  /// Implemetation specific power signals
  /// They usually run in parallel to the pads and are managed by `axe_tcl_pad_power`
  parameter type impl_pwr_t = logic
)(
  /// Core side output signal from the pad
  output logic o_inp,
  /// Core side output enable
  input  logic i_inp_en,
  /// Pull type: `0`: pull-down, `1`: pull-up
  input  logic i_pull_type,
  /// Pull enable
  input  logic i_pull_en,
  /// Implemetation specific signals to the pad
  input  impl_inp_t i_impl,
  /// Implemetation specific signals from the pad
  output impl_oup_t o_impl,
  /// Implemetation specific signals for power management
  input  impl_pwr_t i_impl_pwr,
  /// The pad wire
  input  wire  i_pad
);

  // Model the pull-up/down behaviour
  assign (weak0, weak1) i_pad = i_pull_en ? i_pull_type : 1'bz;

  // The core side receiver output
  assign o_inp = i_inp_en & i_pad;

  // Outputs have some values always
  assign o_impl = '0;
endmodule


/// Model of a crystal oscillator pad instance
///
module axe_tcl_pad_oscillator #(
  /// Implementation key to select different flavours of the same cell
  parameter ImplementationKey = "horizontal",
  /// Implemetation specific input signals to the pad from the core.
  parameter type impl_inp_t = logic,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = logic,
  /// Implemetation specific power signals
  /// They usually run in parallel to the pads and are managed by `axe_tcl_pad_power`
  parameter type impl_pwr_t = logic
)(
  /// Clock towards the core
  output wire       o_clk,
  /// Crystal oscillation mode enable
  input  logic      i_enable,
  /// External clock recieve enable
  input  logic      i_test_en,
  /// Implemetation specific signals to the pad
  input  impl_inp_t i_impl,
  /// Implemetation specific signals from the pad
  output impl_oup_t o_impl,
  /// Implemetation specific signals for power management
  input  impl_pwr_t i_impl_pwr,
  /// Output pad wire
  output wire       o_pad,
  /// Input pad wire
  input  wire       i_pad
);
  assign o_pad  = ~i_pad;
  assign o_clk  = (i_enable || i_test_en) ? i_pad : 1'b0;
  assign o_impl = '0;
endmodule


/// Model of a power management cell
///
module axe_tcl_pad_power #(
  /// Implementation key to select different flavours of the same cell
  parameter ImplementationKey = "horizontal",
  /// Implemetation specific input signals to the pad from the core.
  parameter type impl_inp_t = logic,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = logic
)(
  /// Implemetation specific signals to the pad
  input  impl_inp_t i_impl,
  /// Implemetation specific signals from the pad
  output impl_oup_t o_impl
);

  assign o_impl = i_impl;
endmodule
