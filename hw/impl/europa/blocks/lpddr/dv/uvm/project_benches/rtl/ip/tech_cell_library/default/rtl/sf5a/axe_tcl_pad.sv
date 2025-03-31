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
  parameter ImplementationKey = "slow_horizontal",
  /// Implemetation specific input signals to the pad from the core.
  /// This can be drive strength, schmitt-trigger, etc.
  parameter type impl_inp_t = axe_tcl_pad_pkg::impl_pad_slow_inp_t,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = axe_tcl_pad_pkg::impl_pad_slow_oup_t,
  /// Implemetation specific power signals
  /// They usually run in parallel to the pads and are managed by `axe_tcl_pad_power`
  parameter type impl_pwr_t = axe_tcl_pad_pkg::impl_pwr_t
)(
  /// Core side input signal to the pad, to be transmitted
  input  logic i_oup,
  /// Core side enable the pad as an output
  input  logic i_oup_en,
  /// Core side output signal from the pad, received
  output logic o_inp,
  /// Core side enable to get the received input
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
  case (ImplementationKey)
    "slow_horizontal": begin : gen_slow_horizontal
      if ($bits(i_impl.ds) != 2) $fatal(1, "Drive strength does not have width of 2!");

      PBNT_18_H u_tc_lib_pad_inout (
        .PAD   (io_pad),
        .OE    (i_oup_en),
        .A     (i_oup),
        .IE    (i_inp_en),
        .IS    (i_impl.is),
        .Y     (o_inp),
        .PE    (i_pull_en),
        .PS    (i_pull_type),
        .DS    (i_impl.ds),
        .PO    (o_impl.po),
        .POE   (i_impl.poe),
        .SPS   (i_impl_pwr.sps),
        .RTN   (i_impl_pwr.rtn),
        .LSBIAS(i_impl_pwr.lsbias)
      );
    end
    "slow_vertical": begin : gen_slow_vertical
      if ($bits(i_impl.ds) != 2) $fatal(1, "Drive strength does not have width of 2!");

      PBNT_18_V u_tc_lib_pad_inout (
        .PAD   (io_pad),
        .OE    (i_oup_en),
        .A     (i_oup),
        .IE    (i_inp_en),
        .IS    (i_impl.is),
        .Y     (o_inp),
        .PE    (i_pull_en),
        .PS    (i_pull_type),
        .DS    (i_impl.ds),
        .PO    (o_impl.po),
        .POE   (i_impl.poe),
        .SPS   (i_impl_pwr.sps),
        .RTN   (i_impl_pwr.rtn),
        .LSBIAS(i_impl_pwr.lsbias)
      );
    end
    "fast_horizontal": begin : gen_fast_horizontal
      if ($bits(i_impl.ds) != 3) $fatal(1, "Drive strength does not have width of 3!");

      PBHSNT_18_H u_tc_lib_pad_inout (
        .PAD   (io_pad),
        .OE    (i_oup_en),
        .A     (i_oup),
        .IE    (i_inp_en),
        .IS    (i_impl.is),
        .Y     (o_inp),
        .PE    (i_pull_en),
        .PS    (i_pull_type),
        .DS    (i_impl.ds),
        .PO    (o_impl.po),
        .POE   (i_impl.poe),
        .SPS   (i_impl_pwr.sps),
        .RTN   (i_impl_pwr.rtn),
        .LSBIAS(i_impl_pwr.lsbias)
      );
    end
    "fast_vertical": begin : gen_fast_vertical
      if ($bits(i_impl.ds) != 3) $fatal(1, "Drive strength does not have width of 3!");

      PBHSNT_18_V u_tc_lib_pad_inout (
        .PAD   (io_pad),
        .OE    (i_oup_en),
        .A     (i_oup),
        .IE    (i_inp_en),
        .IS    (i_impl.is),
        .Y     (o_inp),
        .PE    (i_pull_en),
        .PS    (i_pull_type),
        .DS    (i_impl.ds),
        .PO    (o_impl.po),
        .POE   (i_impl.poe),
        .SPS   (i_impl_pwr.sps),
        .RTN   (i_impl_pwr.rtn),
        .LSBIAS(i_impl_pwr.lsbias)
      );
    end
    default: begin : gen_fatal
      $fatal(1, "Not supported implemetation key, supported: 'slow_horizontal', 'slow_vertical', 'fast_horizontal', 'fast_vertical'");
    end
  endcase
endmodule


/// Model of a pure output pad instance
///
module axe_tcl_pad_output #(
  /// Implementation key to select different flavours of the same cell
  parameter ImplementationKey = "slow_horizontal",
  /// Implemetation specific input signals to the pad from the core.
  /// This can be drive strength, schmitt-trigger, etc.
  parameter type impl_inp_t = axe_tcl_pad_pkg::impl_pad_slow_inp_t,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = axe_tcl_pad_pkg::impl_pad_slow_oup_t,
  /// Implemetation specific power signals
  /// They usually run in parallel to the pads and are managed by `axe_tcl_pad_power`
  parameter type impl_pwr_t = axe_tcl_pad_pkg::impl_pwr_t
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
  axe_tcl_pad_inout #(
    .ImplementationKey(ImplementationKey),
    .impl_inp_t       (impl_inp_t),
    .impl_oup_t       (impl_oup_t)
  ) u_axe_tcl_pad_inout (
    .i_oup,
    .i_oup_en,
    .o_inp      (/*open*/),
    .i_inp_en   (1'b0),
    .i_pull_type,
    .i_pull_en,
    .i_impl,
    .o_impl,
    .i_impl_pwr,
    .io_pad     (o_pad)
  );
endmodule


/// Model of a pure input pad instance
///
module axe_tcl_pad_input #(
  /// Implementation key to select different flavours of the same cell
  parameter ImplementationKey = "slow_horizontal",
  /// Implemetation specific input signals to the pad from the core.
  /// This can be drive strength, schmitt-trigger, etc.
  parameter type impl_inp_t = axe_tcl_pad_pkg::impl_pad_slow_inp_t,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = axe_tcl_pad_pkg::impl_pad_slow_oup_t,
  /// Implemetation specific power signals
  /// They usually run in parallel to the pads and are managed by `axe_tcl_pad_power`
  parameter type impl_pwr_t = axe_tcl_pad_pkg::impl_pwr_t
)(
  /// Core side receive signal from the pad
  output logic o_inp,
  /// Core side receive enable
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
  axe_tcl_pad_inout #(
    .ImplementationKey(ImplementationKey),
    .impl_inp_t       (impl_inp_t),
    .impl_oup_t       (impl_oup_t)
  ) u_axe_tcl_pad_inout (
    .i_oup      (1'b0),
    .i_oup_en   (1'b0),
    .o_inp,
    .i_inp_en,
    .i_pull_type,
    .i_pull_en,
    .i_impl,
    .o_impl,
    .i_impl_pwr,
    .io_pad     (i_pad)
  );
endmodule


/// Model of a crystal oscillator pad instance
///
module axe_tcl_pad_oscillator #(
  /// Implementation key to select different flavours of the same cell
  parameter ImplementationKey = "fast_horizontal",
  /// Implemetation specific input signals to the pad from the core.
  parameter type impl_inp_t = axe_tcl_pad_pkg::impl_oscillator_fast_inp_t,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = axe_tcl_pad_pkg::impl_oscillator_fast_oup_t,
  /// Implemetation specific power signals
  /// They usually run in parallel to the pads and are managed by `axe_tcl_pad_power`
  parameter type impl_pwr_t = axe_tcl_pad_pkg::impl_pwr_t
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
  case (ImplementationKey)
    "slow_horizontal": begin : gen_slow_horizontal
      POSCK_18_H u_tc_lib_pad_oscillator (
        .CK    (o_clk),
        .CK_IOV(o_impl.ck_iov),
        .PADO  (o_pad),
        .PO    (o_impl.po),
        .E0    (i_enable),
        .PADI  (i_pad),
        .POE   (i_impl.poe),
        .RTN   (i_impl_pwr.rtn),
        .SPS   (i_impl_pwr.sps),
        .TE    (i_test_en),
        .LSBIAS(i_impl_pwr.lsbias)
      );
    end
    "slow_vertical": begin : gen_slow_vertical
      POSCK_18_V u_tc_lib_pad_oscillator (
        .CK    (o_clk),
        .CK_IOV(o_impl.ck_iov),
        .PADO  (o_pad),
        .PO    (o_impl.po),
        .E0    (i_enable),
        .PADI  (i_pad),
        .POE   (i_impl.poe),
        .RTN   (i_impl_pwr.rtn),
        .SPS   (i_impl_pwr.sps),
        .TE    (i_test_en),
        .LSBIAS(i_impl_pwr.lsbias)
      );
    end
    "fast_horizontal": begin : gen_fast_horizontal
      POSCM_18_H u_tc_lib_pad_oscillator (
        .CK    (o_clk),
        .CK_IOV(o_impl.ck_iov),
        .PADO  (o_pad),
        .PO    (o_impl.po),
        .E0    (i_enable),
        .PADI  (i_pad),
        .POE   (i_impl.poe),
        .RTN   (i_impl_pwr.rtn),
        .SPS   (i_impl_pwr.sps),
        .TE    (i_test_en),
        .SF    (i_impl.sf),
        .LSBIAS(i_impl_pwr.lsbias)
      );
    end
    "fast_vertical": begin : gen_fast_vertical
      POSCM_18_V u_tc_lib_pad_oscillator (
        .CK    (o_clk),
        .CK_IOV(o_impl.ck_iov),
        .PADO  (o_pad),
        .PO    (o_impl.po),
        .E0    (i_enable),
        .PADI  (i_pad),
        .POE   (i_impl.poe),
        .RTN   (i_impl_pwr.rtn),
        .SPS   (i_impl_pwr.sps),
        .TE    (i_test_en),
        .SF    (i_impl.sf),
        .LSBIAS(i_impl_pwr.lsbias)
      );
    end
    default: begin : gen_fatal
      $fatal(1, "Not supported implemetation key, supported: 'slow_horizontal', 'slow_vertical', 'fast_horizontal', 'fast_vertical'");
    end
  endcase
endmodule


/// Model of a retention pad instance
///
module axe_tcl_pad_power #(
  /// Implementation key to select different flavours of the same cell
  parameter ImplementationKey = "horizontal",
  /// Implemetation specific input signals to the pad from the core.
  parameter type impl_inp_t = logic,
  /// Implemetation specific output signals from the pad to the core.
  parameter type impl_oup_t = axe_tcl_pad_pkg::impl_pwr_t
)(
  /// Implemetation specific signals to the pad
  input  impl_inp_t i_impl,
  /// Implemetation specific signals from the pad
  output impl_oup_t o_impl
);
  case (ImplementationKey)
    "horizontal": begin : gen_horizontal
      POCTIE_18_H u_tc_lib_pad_power (
        .RTN   (o_impl.sps),
        .SPS   (o_impl.rtn),
        .LSBIAS(o_impl.lsbias)
      );
    end
    "vertical": begin : gen_vertical
      POCTIE_18_V u_tc_lib_pad_power (
        .RTN   (o_impl.sps),
        .SPS   (o_impl.rtn),
        .LSBIAS(o_impl.lsbias)
      );
    end
    default: begin : gen_fatal
      $fatal(1, "Not supported implemetation key, supported: 'horizontal', 'vertical'");
    end
  endcase
endmodule
