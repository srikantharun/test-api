// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Abhishek Maringanti <abhishek.maringanti@axelera.ai>

/// Generic PVT Wrapper IP containing the instance of the PVT
/// Samsung Foundry PVT - LN05LPE

`ifndef TMS_PVT_WRAPPER_SV
`define TMS_PVT_WRAPPER_SV

module tms_pvt_wrapper #(
)
(
  /// Temperature sensor and voltage sensor enable signal 1'b1 = Enable (default) 1'b0 = Disable.
  input  logic        i_pvt_en_ts,
  /// ADC enable signal
  input  logic        i_pvt_en_adc_ts,
  /// Main clock input Default: 4MHz for the voltage sensor and temperature sensor Default: 8MHz for the process sensor
  input  wire         i_pvt_clk_ts,
  /// Input signal that starts the conversion process of temperature sensor and voltage sensor
  input  logic        i_pvt_soc_ts,
  /// Remote probe selection signal 6'b00_0000: Main probe inside PVT sensor 6'b00_0001 to 6'b11_1111:
  /// Remote probe 0(IBIAS_TS[0], VSENSE_TS[0]) to 62(IBIAS_TS[62], VSENSE_TS[62])
  input  logic [5:0]  i_pvt_bjt_sel_ts,
  /// ADC input control signal Temperature sensor mode: 4'b0000 Voltage sensor mode: 4'b0001 ~ 4'b1110 ADC test mode: 4'b1111
  input  logic [3:0]  i_pvt_sel_ts,
  /// Slope control for temperature output code Default: 5'b0_0001
  input  logic [4:0]  i_pvt_buf_slope_sel_ts,
  /// Offset control for temperature output code Default: 5'b0_0001
  input  logic [4:0]  i_pvt_buf_vref_sel_ts,
  /// BGR trim control signal Default: 4'b0000
  input  logic [3:0]  i_pvt_bgr_trim_ts,
  /// VREF trim control signal Default: 4'b0000
  input  logic [3:0]  i_pvt_vref_trim_ts,
  /// VBE trim control signal Default: 4'b0000
  input  logic [3:0]  i_pvt_vbe_trim_ts,
  /// ADC cap control signal Default: 3'b100
  input  logic [2:0]  i_pvt_adc_cctrl_ts,
  /// ADC current trimming signal Default: 3'b011
  input  logic [2:0]  i_pvt_adc_ictrl_ts,
  /// MUX control signal for test mode Default: 3'b000 VREF monitoring: 3'b001
  /// VPTAT monitoring: 3'b010 VBE monitoring: 3'b011 DAC Test: 3'b101 ADC Test: 3'b111
  input  logic [2:0]  i_pvt_mux_addr_ts,
  /// Average mode control input signals for digital offset cancellation function 2-sample average: 2'b01
  /// 4-sample average: 2'b10 8-sample average: 2'b11 Default: 2'b11
  input  logic [1:0]  i_pvt_avg_mode_ts,
  /// Clock input signal for HTOL test mode(Same as scan test clock) Default: 1'b0 HTOL test: 50MHz
  input  wire         i_pvt_scan_test_clk,
  /// HTOL test mode selection control signal HTOL test mode enable: 1'b1, HTOL test mode disable: 1'b0, Default value: 1'b0
  input  logic        i_pvt_scan_test_mode,
  /// Start of conversion signal for process sensor
  input  logic        i_pvt_soc_ps,
  /// Process sensor enable signal Default value: 3'b000 Process of LVT NMOS and PMOS: 3'b001 Process of LVT NMOS: 3'b010
  /// Process of LVT PMOS: 3'b011 Process of RVT NMOS and PMOS: 3'b101 Process of RVT NMOS: 3'b110 Process of RVT PMOS: 3'b111
  input  logic [2:0]  i_pvt_en_ps,
  /// 12bit temperature and voltage sensor output signal
  output logic [11:0] o_pvt_out_12bit_ts,
  /// A signal that notifies the end of conversion of process sensor
  output logic        o_pvt_eoc_ps,
  /// The frequency output of process sensor
  output logic        o_pvt_ps_freq_out,
  /// A signal that notifies the end of conversion of temperature and voltage sensor
  output logic        o_pvt_eoc_ts,
  /// 12bit process sensor output signal
  output logic [11:0] o_pvt_out_12bit_ps,
  /// Temperature sensor signals for providing bias current to IBIAS_TS of remote probes (tu_tem0501ar01_ln05lpe_4007002).
  /// It must be connected with IBIAS_TS in each remote probe if you want to use remote probes. For unused signals, leave as floating
  inout  wire  [62:0] io_pvt_ibias_ts,
  /// Temperature sensor signals for voltage sensing from VSENSE_TS of remote probes (tu_tem0501ar01_ln05lpe_4007002).
  /// It must be connected with VSENSE_TS in each remote probe if you want to use remote probes. For unused signals, leave as floating
  inout  wire  [62:0] io_pvt_vsense_ts,
  /// Analog monitoring signal for test purposes: refer to test MUX control guide in DataSheet
  /// MUX_ADDR_TS can select internal analog voltage. Connect with AY500 (500ohm) port
  inout  wire         io_pvt_test_out_ts,
  /// Voltage input signal for voltage sensor When SEL_TS[3:0]=4'b0001, VOL_TS[0] is measured.
  inout  wire  [13:0] io_pvt_vol_ts
`ifdef POWER_PINS
  ,
  inout  wire  io_pvt_dvdd075a_ts,
  inout  wire  io_pvt_dvss0a_ts,
  inout  wire  io_pvt_avdd18a_ts,
  inout  wire  io_pvt_avss0a_ts,
  inout  wire  io_pvt_avss_gd
`endif

);

  // ---------------------------------------
  // PVT Wrapper instantiation
  // ---------------------------------------
  pvt_wrapper #(
  ) u_pvt_wrapper (
    .i_pvt_en_ts                  (i_pvt_en_ts           ),
    .i_pvt_en_adc_ts              (i_pvt_en_adc_ts       ),
    .i_pvt_clk_ts                 (i_pvt_clk_ts          ),
    .i_pvt_soc_ts                 (i_pvt_soc_ts          ),
    .i_pvt_bjt_sel_ts             (i_pvt_bjt_sel_ts      ),
    .i_pvt_sel_ts                 (i_pvt_sel_ts          ),
    .i_pvt_buf_slope_sel_ts       (i_pvt_buf_slope_sel_ts),
    .i_pvt_buf_vref_sel_ts        (i_pvt_buf_vref_sel_ts ),
    .i_pvt_bgr_trim_ts            (i_pvt_bgr_trim_ts     ),
    .i_pvt_vref_trim_ts           (i_pvt_vref_trim_ts    ),
    .i_pvt_vbe_trim_ts            (i_pvt_vbe_trim_ts     ),
    .i_pvt_adc_cctrl_ts           (i_pvt_adc_cctrl_ts    ),
    .i_pvt_adc_ictrl_ts           (i_pvt_adc_ictrl_ts    ),
    .i_pvt_mux_addr_ts            (i_pvt_mux_addr_ts     ),
    .i_pvt_avg_mode_ts            (i_pvt_avg_mode_ts     ),
    .i_pvt_scan_test_clk          (i_pvt_scan_test_clk   ),
    .i_pvt_scan_test_mode         (i_pvt_scan_test_mode  ),
    .o_pvt_out_12bit_ts           (o_pvt_out_12bit_ts    ),
    .o_pvt_eoc_ts                 (o_pvt_eoc_ts          ),
    .io_pvt_ibias_ts              (io_pvt_ibias_ts       ),
    .io_pvt_vsense_ts             (io_pvt_vsense_ts      ),
    .io_pvt_test_out_ts           (io_pvt_test_out_ts    ),
    .i_pvt_soc_ps                 (i_pvt_soc_ps          ),
    .io_pvt_vol_ts                (io_pvt_vol_ts         ),
    .o_pvt_out_12bit_ps           (o_pvt_out_12bit_ps    ),
    .i_pvt_en_ps                  (i_pvt_en_ps           ),
    .o_pvt_eoc_ps                 (o_pvt_eoc_ps          ),
    .o_pvt_ps_freq_out            (o_pvt_ps_freq_out     )
    `ifdef POWER_PINS
    ,
    .io_pvt_dvdd075a_ts           (io_pvt_dvdd075a_ts    ),
    .io_pvt_dvss0a_ts             (io_pvt_dvss0a_ts      ),
    .io_pvt_avdd18a_ts            (io_pvt_avdd18a_ts     ),
    .io_pvt_avss0a_ts             (io_pvt_avss0a_ts      ),
    .io_pvt_avss_gd               (io_pvt_avss_gd        )
    `endif
);


endmodule

`endif // TMS_PVT_WRAPPER_SV

