// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

/// Generic OTP Wrapper IP containing the instance of the OTP
/// Samsung Foundry OTP - LN05LPE
/// Size = 16Kb

`ifndef SF_OTP_WRAPPER_SV
`define SF_OTP_WRAPPER_SV

module sf_otp_wrapper #(
  parameter int unsigned OTP_ADDR_W = 14,
  parameter int unsigned OTP_DATA_W = 32,
  parameter int unsigned OTP_LOCK_DEPTH = 8
)
(
  /// i_otp_clk/CLK signal enables chopper to compensate the mismatch of differential amplifier
  /// in reference voltage generator. It should be connected to chip clock.
  input  wire  i_otp_clk,
  /// i_otp_rstb/RSTB resets all test command registers and data input buffer. It must be toggled before
  /// going into a new test mode or program mode or read mode to clear away the old settings and data.
  input  wire  i_otp_rstb,
  /// i_otp_addr/ADD[MSB:0] are used to address the location to be programmed or read during program or
  /// read mode respectively.
  input  logic [OTP_ADDR_W-1:0] i_otp_addr,
  /// i_otp_ceb/CEB activates OTP. When CEB is set to low, OTP can run program or read operation.
  /// When CEB is set to high, OTP is deactivated and set on standby mode.
  input  logic i_otp_ceb,
  /// i_otp_cle/CLE enables test mode command entry. You can run various test modes using CLE
  /// combined with WEB and ADD[MSB:0].
  input  logic i_otp_cle,
  /// i_otp_cpumpen/CPUMPEN enables the charge pump in program mode with internal charge pump and
  /// it allows external VPP to pass through the switch in the program mode with external VPP.
  /// CPUMPEN must be set to low in read mode.
  input  logic i_otp_cpumpen,
  /// i_otp_pgmen/PGMEN activates all circuits for program operation and must be set to low in read mode.
  input  logic i_otp_pgmen,
  /// i_otp_dle/DLE enables data input buffer in program operation combined with DIN and WEB and it makes
  /// various test modes combined with CLE, WEB, and ADD[MSB:0].
  input  logic i_otp_dle,
  /// i_otp_din/DIN sets 1-bit program data input. When DIN and DLE are set to high and latched with WEB, data '1'
  /// is written to a selected bitcell by following program sequence. DIN must be set to low in read mode.
  input  logic i_otp_din,
  /// i_otp_readen/READEN activates all circuits for read or verify operation.
  input  logic i_otp_readen,
  /// i_otp_web/WEBenables data input buffer in program operation combined with DIN and DLE and it makes
  /// various test modes combined with CLE, DLE, and ADD[MSB:0]. In addition, WEB low pulse width sets the
  // real program time within high pulse of PGMEN and CPUMPEN.
  input  logic i_otp_web,
  /// i_otp_vddrdy/VDDRDY is a test input and must be set to low during normal operation.
  input  logic i_otp_vddrdy,
  /// i_otp_clken/CLKEN is an input to decide the use of chopper in reference voltage genertor.
  input  logic i_otp_clken,
  /// o_otp_dout/DOUT[31:0] are 32-bit read data bus outputs selected by address.
  output logic [OTP_DATA_W-1:0] o_otp_dout,
  /// o_otp_lock/LOCK[7:0] are test outputs, so you don't need to connect it.
  output logic [OTP_LOCK_DEPTH-1:0] o_otp_lock,
  /// io_otp_vtdo/VTDO pin is an analog test signal for measuring OTP cell current on test mode and must be
  /// connected to the probing pad directly without buffers. When packaging after wafer sorting, it should be
  /// set to VSS or floating.
  inout  wire  io_otp_vtdo,
  /// io_otp_vrefm/VREFM pin is an analog test signal for measuring reference voltage or internal bias level
  /// on test mode and must be connected to the probing pad directly without buffers. When packaging after
  /// wafer sorting, it should be set to VSS or floating.
  inout  wire  io_otp_vrefm,
  /// io_vpp/VPP pin is an analog signal for high voltage input or output. (4.3 +/- 0.2V)
  /// When it is used as an input pin, high voltage is forced through this pin during program mode and should be
  /// discharged after program mode. When it is used as an output pin, the output of internal charge pump is monitored
  /// through this pin during test mode. When packaging after wafer sorting, it should be set to VDDHOTP or floating.
  inout  wire  io_otp_vpp
);
  ////////////////////////////////////////////////////
  // Instantiate the analog SF5A pads directly here //
  ////////////////////////////////////////////////////

  // Spec on what pads must be used can be found here:
  // `/data/foundry/samsung/sf5a/ip/samsung/DOC-Common_sec240719_0012/UserGuide/samsung_foundry_otp_cp_a100_ln05lpe_v1.02_userguide_rev1.02.pdf`

  `ifdef TARGET_SF5A
  wire axe_tcl_pad_pkg::impl_pwr_t impl_power;

  wire otp_vtdo;
  wire otp_vrefm;
  wire otp_vpp;

  PANANT_18_V u_pad_analog_vtdo (
    .PAD   (io_otp_vtdo),
    .AY    (otp_vtdo),
    .AY50  (/* floating */), // ASO-UNUSED_OUTPUT : 50ohm output left floating
    .AY500 (/* floating */), // ASO-UNUSED_OUTPUT : 500ohm output left floating
    .RTN   (impl_power.rtn), // ASO-UNDRIVEN_INPUT : Will not be connected by PD
    .SPS   (impl_power.sps), // ASO-UNDRIVEN_INPUT : Will not be connected by PD
    .LSBIAS(impl_power.lsbias) // ASO-UNDRIVEN_INPUT : Will not be connected by PD
    `ifdef POWER_PINS
    ,
    .DVDD  (),
    .DVSS  (),
    .VDD   (),
    .VSS   ()
    `endif
  );

  PANANT_18_V u_pad_analog_vrefm (
    .PAD   (io_otp_vrefm),
    .AY    (otp_vrefm),
    .AY50  (/* floating */), // ASO-UNUSED_OUTPUT : 50ohm output left floating
    .AY500 (/* floating */), // ASO-UNUSED_OUTPUT : 500ohm output left floating
    .RTN   (impl_power.rtn), // ASO-UNDRIVEN_INPUT : Will not be connected by PD
    .SPS   (impl_power.sps), // ASO-UNDRIVEN_INPUT : Will not be connected by PD
    .LSBIAS(impl_power.lsbias) // ASO-UNDRIVEN_INPUT : Will not be connected by PD
    `ifdef POWER_PINS
    ,
    .DVDD  (),
    .DVSS  (),
    .VDD   (),
    .VSS   ()
    `endif
  );

  PANAFS_18_V u_pad_analog_vpp (
    .PAD   (io_otp_vpp),
    .AY    (otp_vpp),
    .AY500 (/* floating */), // ASO-UNUSED_OUTPUT : 500ohm output left floating
    .RTN   (impl_power.rtn), // ASO-UNDRIVEN_INPUT : Will not be connected by PD
    .SPS   (impl_power.sps), // ASO-UNDRIVEN_INPUT : Will not be connected by PD
    .LSBIAS(impl_power.lsbias) // ASO-UNDRIVEN_INPUT : Will not be connected by PD
    `ifdef POWER_PINS
    ,
    .DVDD  (),
    .DVSS  (),
    .VDD   (),
    .VSS   ()
    `endif
  );
  `endif

  sf_otp16kb_cp_a100_ln05lpe_4006000 #(
    .ADDR_WIDTH (OTP_ADDR_W),
    .DOUT_WIDTH (OTP_DATA_W),
    .LOCK_DEPTH (OTP_LOCK_DEPTH)
  ) u_sf_otp16kb_cp_a100_ln05lpe_4006000 (
    .ADD     (i_otp_addr),
    .CEB     (i_otp_ceb),
    .CLE     (i_otp_cle),
    .CPUMPEN (i_otp_cpumpen),
    .PGMEN   (i_otp_pgmen),
    .DLE     (i_otp_dle),
    .DIN     (i_otp_din),
    .READEN  (i_otp_readen),
    .RSTB    (i_otp_rstb),
    .WEB     (i_otp_web),
    .VDDRDY  (i_otp_vddrdy),
    .CLK     (i_otp_clk),
    .CLKEN   (i_otp_clken),
    .DOUT    (o_otp_dout),
    .LOCK    (o_otp_lock),

    `ifdef POWER_PINS
    //.VDDOTP   (),
    //.VDDHOTP  (),
    //.VSSOTP   (),
    //.VSSL     (),
    `endif
    `ifdef TARGET_SF5A
    .VTDO    (otp_vtdo),
    .VREFM   (otp_vrefm),
    .VPP     (otp_vpp)
    `else
    .VTDO    (io_otp_vtdo),
    .VREFM   (io_otp_vrefm),
    .VPP     (io_otp_vpp)
    `endif
  );

endmodule

`endif // OTP_WRAPPER_SV
