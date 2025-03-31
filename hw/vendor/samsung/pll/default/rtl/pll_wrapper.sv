// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Abhishek Maringanti <abhishek.maringanti@axelera.ai>

/// Generic PLL Wrapper IP containing the instance of the PLL
/// Samsung Foundry PLL - LN05LPE

`ifndef PLL_WRAPPER_SV
`define PLL_WRAPPER_SV

module pll_wrapper #(
)
(
  /// Monitoring pin. Output code of AFC (5 bits).
  output logic [4:0]       o_pll_afc_code,
  /// Monitoring pin. FREF or FEED can be observed.
  output logic             o_pll_feed_out,
  /// PLL clock output.
  output logic             o_pll_fout,
  /// If PLL is unlocked, LOCK=0. If PLL is locked, LOCK = 1.
  output logic             o_pll_lock,
  `ifdef POWER_PINS
  ///
  input  logic             i_pll_avdd18,
  ///
  input  logic             i_pll_avss,
  ///
  input  logic             i_pll_dvdd075,
  ///
  input  logic             i_pll_dvss,
  `endif
  /// Monitoring pin. If AFC_ENB=0, AFC is enabled and VCO is calibrated automatically.
  /// If AFC_ENB=1, AFC is disabled and VCO is calibrated manually by EXTAFC[4:0] for the test of VCO range.
  /// Default value : 1'b0
  input  logic             i_pll_afc_enb,
  /// If BYPASS = 1, bypass mode is enabled. (FOUT = FIN) If BYPASS = 0, PLL operates normally.
  input  logic             i_pll_bypass,
  ///Monitoring pin. If AFC_ENB=1, AFC is disabled and VCO is calibrated manually by EXTAFC[4:0] for the
  /// test of VCO range. Default value : 5'b0_0000
  input  logic [4:0]       i_pll_extafc,
  /// Monitoring pin. If FEED_EN=1, FEED_OUT is enabled. Default value : 1'b0
  input  logic             i_pll_feed_en,
  ///PLL clock input. PLL has to be reset if FIN is changed.
  input  logic             i_pll_fin,
  /// Scaler's re-initialization time control pin. Default value : 1'b0
  input  logic             i_pll_fout_mask,
  /// Monitoring pin. If FSEL = 0, FEED_OUT = FREF. If FSEL = 1, FEED_OUT = FEED. Default value : 1'b0
  input  logic             i_pll_fsel,
  ///Controls the charge-pump current. Default value : 2'b01
  input  logic [1:0]       i_pll_icp,
  /// Lock detector setting of the detection resolution. Default value : 2'b11
  input  logic [1:0]       i_pll_lock_con_dly,
  /// Lock detector setting of the input margin. Default value : 2'b11
  input  logic [1:0]       i_pll_lock_con_in,
  /// Lock detector setting of the output margin. Default value : 2'b11
  input  logic [1:0]       i_pll_lock_con_out,
  ///Division value of the 10-bit programmable main-divider. PLL has to be reset if M value is changed.
  input  logic [9:0]       i_pll_m,
  /// Division value of the 6-bit programmable pre-divider. PLL has to be reset if P value is changed.
  input  logic [5:0]       i_pll_p,
  /// RESETB signal is used for power down control.
  /// If RESETB = 0, power down mode is enabled and all digital blocks are reset.
  /// If RESETB = 1 from 0, PLL starts its normal operation after lock time.
  input  logic             i_pll_resetb,
  /// Reserved pin. Default value : 4'b1000
  input  logic [3:0]       i_pll_rsel,
  /// Division value of the 3-bit programmable scaler.
  input  logic [2:0]       i_pll_s
);

  tu_pll0519a01_ln05lpe_4007002 #(
  ) u_tu_pll0519a01_ln05lpe_4007002 (
    .AFC_CODE(o_pll_afc_code),
    .FEED_OUT(o_pll_feed_out),
    .FOUT(o_pll_fout),
    .LOCK(o_pll_lock),
    `ifdef POWER_PINS
    .AVDD18(i_pll_avdd18),
    .AVSS(i_pll_avss),
    .DVDD075(i_pll_dvdd075),
    .DVSS(i_pll_dvss),
    `endif
    .AFC_ENB(i_pll_afc_enb),
    .BYPASS(i_pll_bypass),
    .EXTAFC(i_pll_extafc),
    .FEED_EN(i_pll_feed_en),
    .FIN(i_pll_fin),
    .FOUT_MASK(i_pll_fout_mask),
    .FSEL(i_pll_fsel),
    .ICP(i_pll_icp),
    .LOCK_CON_DLY(i_pll_lock_con_dly),
    .LOCK_CON_IN(i_pll_lock_con_in),
    .LOCK_CON_OUT(i_pll_lock_con_out),
    .M(i_pll_m),
    .P(i_pll_p),
    .RESETB(i_pll_resetb),
    .RSEL(i_pll_rsel),
    .S(i_pll_s)
  );


endmodule

`endif // PLL_WRAPPER_SV

