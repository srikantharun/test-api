// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Abhishek Maringanti <abhishek.maringanti@axelera.ai>

/// Generic Dummy PVT model IP. Blank RTL with no functionality.
/// Used for compilation only.

module tu_pvt0501a01_ln05lpe_4007002 #(
)
(
  /// Temperature sensor and voltage sensor enable signal 1'b1 = Enable (default) 1'b0 = Disable.
  input  logic        EN_TS,
  /// ADC enable signal
  input  logic        EN_ADC_TS,
  /// Main clock input Default: 4MHz for the voltage sensor and temperature sensor Default: 8MHz for the process sensor
  input  wire         CLK_TS,
  /// Input signal that starts the conversion process of temperature sensor and voltage sensor
  input  logic        SOC_TS,
  /// Remote probe selection signal 6'b00_0000: Main probe inside PVT sensor 6'b00_0001 to 6'b11_1111:
  /// Remote probe 0(IBIAS_TS[0], VSENSE_TS[0]) to 62(IBIAS_TS[62], VSENSE_TS[62])
  input  logic [5:0]  BJT_SEL_TS,
  /// ADC input control signal Temperature sensor mode: 4'b0000 Voltage sensor mode: 4'b0001 ~ 4'b1110 ADC test mode: 4'b1111
  input  logic [3:0]  SEL_TS,
  /// Slope control for temperature output code Default: 5'b0_0001
  input  logic [4:0]  BUF_SLOPE_SEL_TS,
  /// Offset control for temperature output code Default: 5'b0_0001
  input  logic [4:0]  BUF_VREF_SEL_TS,
  /// BGR trim control signal Default: 4'b0000
  input  logic [3:0]  BGR_TRIM_TS,
  /// VREF trim control signal Default: 4'b0000
  input  logic [3:0]  VREF_TRIM_TS,
  /// VBE trim control signal Default: 4'b0000
  input  logic [3:0]  VBE_TRIM_TS,
  /// ADC cap control signal Default: 3'b100
  input  logic [2:0]  ADC_CCTRL_TS,
  /// ADC current trimming signal Default: 3'b011
  input  logic [2:0]  ADC_ICTRL_TS,
  /// MUX control signal for test mode Default: 3'b000 VREF monitoring: 3'b001
  /// VPTAT monitoring: 3'b010 VBE monitoring: 3'b011 DAC Test: 3'b101 ADC Test: 3'b111
  input  logic [2:0]  MUX_ADDR_TS,
  /// Average mode control input signals for digital offset cancellation function 2-sample average: 2'b01
  /// 4-sample average: 2'b10 8-sample average: 2'b11 Default: 2'b11
  input  logic [1:0]  AVG_MODE_TS,
  /// Clock input signal for HTOL test mode(Same as scan test clock) Default: 1'b0 HTOL test: 50MHz
  input  wire         SCAN_TEST_CLK,
  /// HTOL test mode selection control signal HTOL test mode enable: 1'b1, HTOL test mode disable: 1'b0, Default value: 1'b0
  input  logic        SCAN_TEST_MODE,
  /// Start of conversion signal for process sensor
  input  logic        SOC_PS,
  /// Process sensor enable signal Default value: 3'b000 Process of LVT NMOS and PMOS: 3'b001 Process of LVT NMOS: 3'b010
  /// Process of LVT PMOS: 3'b011 Process of RVT NMOS and PMOS: 3'b101 Process of RVT NMOS: 3'b110 Process of RVT PMOS: 3'b111
  input  logic [2:0]  EN_PS,
  /// 12bit temperature and voltage sensor output signal
  output logic [11:0] OUT_12BIT_TS,
  /// A signal that notifies the end of conversion of process sensor
  output logic        EOC_PS,
  /// The frequency output of process sensor
  output logic        PS_FREQ_OUT,
  /// A signal that notifies the end of conversion of temperature and voltage sensor
  output logic        EOC_TS,
  /// 12bit process sensor output signal
  output logic [11:0] OUT_12BIT_PS,
  /// Temperature sensor signals for providing bias current to IBIAS_TS of remote probes (tu_tem0501ar01_ln05lpe_4007002).
  /// It must be connected with IBIAS_TS in each remote probe if you want to use remote probes. For unused signals, leave as floating
  inout  wire  [62:0] IBIAS_TS,
  /// Temperature sensor signals for voltage sensing from VSENSE_TS of remote probes (tu_tem0501ar01_ln05lpe_4007002).
  /// It must be connected with VSENSE_TS in each remote probe if you want to use remote probes. For unused signals, leave as floating
  inout  wire  [62:0] VSENSE_TS,
  /// Analog monitoring signal for test purposes: refer to test MUX control guide in DataSheet
  /// MUX_ADDR_TS can select internal analog voltage. Connect with AY500 (500ohm) port
  inout  wire         TEST_OUT_TS,
  /// Voltage input signal for voltage sensor When SEL_TS[3:0]=4'b0001, VOL_TS[0] is measured.
  inout  wire  [13:0] VOL_TS
`ifdef POWER_PINS
  ,
  inout  wire  DVDD075A_TS,
  inout  wire  DVSS0A_TS,
  inout  wire  AVDD18A_TS,
  inout  wire  AVSS0A_TS,
  inout  wire  AVSS_GD
`endif

);


endmodule


