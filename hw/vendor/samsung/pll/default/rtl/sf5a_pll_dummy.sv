// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***

/// Dummy PLL model IP. Blank RTL with no functionality.
/// Used for compilation only.

module tu_pll0519a01_ln05lpe_4007002 #(
)
(
  /// Monitoring pin. Output code of AFC (5 bits).
  output logic [4:0]       AFC_CODE,
  /// Monitoring pin. FREF or FEED can be observed.
  output logic             FEED_OUT,
  /// PLL clock output.
  output logic             FOUT,
  /// If PLL is unlocked, LOCK=0. If PLL is locked, LOCK = 1.
  output logic             LOCK,
  `ifdef POWER_PINS
  ///
  input  logic             AVDD18,
  ///
  input  logic             AVSS,
  ///
  input  logic             DVDD075,
  ///
  input  logic             DVSS,
  `endif
  /// Monitoring pin. If AFC_ENB=0, AFC is enabled and VCO is calibrated automatically.
  /// If AFC_ENB=1, AFC is disabled and VCO is calibrated manually by EXTAFC[4:0] for the test of VCO range.
  /// Default value : 1'b0
  input  logic             AFC_ENB,
  /// If BYPASS = 1, bypass mode is enabled. (FOUT = FIN) If BYPASS = 0, PLL operates normally.
  input  logic             BYPASS,
  ///Monitoring pin. If AFC_ENB=1, AFC is disabled and VCO is calibrated manually by EXTAFC[4:0] for the
  /// test of VCO range. Default value : 5'b0_0000
  input  logic [4:0]       EXTAFC,
  /// Monitoring pin. If FEED_EN=1, FEED_OUT is enabled. Default value : 1'b0
  input  logic             FEED_EN,
  ///PLL clock input. PLL has to be reset if FIN is changed.
  input  logic             FIN,
  /// Scaler's re-initialization time control pin. Default value : 1'b0
  input  logic             FOUT_MASK,
  /// Monitoring pin. If FSEL = 0, FEED_OUT = FREF. If FSEL = 1, FEED_OUT = FEED. Default value : 1'b0
  input  logic             FSEL,
  ///Controls the charge-pump current. Default value : 2'b01
  input  logic [1:0]       ICP,
  /// Lock detector setting of the detection resolution. Default value : 2'b11
  input  logic [1:0]       LOCK_CON_DLY,
  /// Lock detector setting of the input margin. Default value : 2'b11
  input  logic [1:0]       LOCK_CON_IN,
  /// Lock detector setting of the output margin. Default value : 2'b11
  input  logic [1:0]       LOCK_CON_OUT,
  ///Division value of the 10-bit programmable main-divider. PLL has to be reset if M value is changed.
  input  logic [9:0]       M,
  /// Division value of the 6-bit programmable pre-divider. PLL has to be reset if P value is changed.
  input  logic [5:0]       P,
  /// RESETB signal is used for power down control.
  /// If RESETB = 0, power down mode is enabled and all digital blocks are reset.
  /// If RESETB = 1 from 0, PLL starts its normal operation after lock time.
  input  logic             RESETB,
  /// Reserved pin. Default value : 4'b1000
  input  logic [3:0]       RSEL,
  /// Division value of the 3-bit programmable scaler.
  input  logic [2:0]       S
);

endmodule
