// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Abhishek Maringanti <abhishek.maringanti@axelera.ai>

/// Generic eFUSE Wrapper IP containing the instance of the eFUSE Module
/// Samsung Foundry eFUSE - LN05LPE
/// Size = 10kx40b

`ifndef EFUSE_WRAPPER_SV
`define EFUSE_WRAPPER_SV

module efuse_wrapper #(
  parameter int unsigned EFUSE_ADDR_W = 14
)
(
  /// Chip select enable signal
  input  i_efuse_csb,
  /// Signal to enable the access to the array for read or program
  input  i_efuse_strobe,
  /// Signal to select read or program operation (H: Read, L:Program)
  input  i_efuse_load,
  /// Signal to select read or program operation (H: Read, L:Program)
  input  i_efuse_pgenb,
  /// Signal(0.75V) to control power switch of VQPS and VDDWL
  input  i_efuse_psm,
  /// Address input bus (A[13:0] @10Kb and 7.5Kb, A[12:0] @5Kb, A[11:0] @2.5Kb)
  input  [EFUSE_ADDR_W-1:0] i_efuse_a,
  /// Signal to enable test mode to access additional test array(default '0')
  input  i_efuse_te,
  /// Signal to select a specific test row or column
  input  [2:0] i_efuse_ts,
  /// Signal to select a reference resistance value for margin read which is necessary to verify
  /// programmed and un-programmed cells(default '0')
  input  [1:0] i_efuse_pmr,
  /// VDDRDY is a reserved input for test(default '0')
  input  i_efuse_vddrdy,
  /// High voltage supply power for fuse programming (1.8V)
  inout  io_efuse_vqps,
  /// High voltage supply power for fuse programming (1.8V)
  inout  io_efuse_vddwl,
  /// Test data output bus for test column cells
  output [1:0] o_efuse_qt,
  /// Data output bus which is valid after rising edge of STROBE in read mode
  output [39:0] o_efuse_q

);

  // Instantiation of the 10k * 40bit eFUSE module.
  sf_efuse10kbx40_a100_ln05lpe_4006000 #(
  ) u_sf_efuse10kbx40_a100_ln05lpe_4006000 (
    .CSB        (i_efuse_csb),
    .STROBE     (i_efuse_strobe),
    .LOAD       (i_efuse_load),
    .PGENB      (i_efuse_pgenb),
    .PSM        (i_efuse_psm),
    .A          (i_efuse_a),
    .Q          (o_efuse_q),
    .TE         (i_efuse_te),
    .TS         (i_efuse_ts),
    .QT         (o_efuse_qt),
    .PMR        (i_efuse_pmr),
    .VDDRDY     (i_efuse_vddrdy),
    `ifdef POWER_PINS
    //.VDD        (),
    //.VSS        (),
    `endif
    .VQPS       (io_efuse_vqps),
    .VDDWL      (io_efuse_vddwl)
  );


endmodule

`endif // EFUSE_WRAPPER_SV

