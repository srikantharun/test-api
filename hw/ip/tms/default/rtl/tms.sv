// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

// Thermal  Management Supervisor (TMS). Top level
//
`ifndef TMS_SV
`define TMS_SV

module tms #(
  // Number of temperature sensors
  parameter int  unsigned NB_EXT_TEMP_SENSE = 11                                              ,
  // Number of temp sensors in rms
  parameter int  unsigned NB_INT_TEMP_SENSE = 1                                               ,
  // width definition for APB address bus
  parameter int  unsigned PAW               = 16                                              ,
  // width definition for APB data bus
  parameter int  unsigned PDW               = 32                                              ,
  // width definition for APB strobe bus
  parameter int  unsigned PSTRBW            = 4                                               ,
  // width definition for APB pprobe bus
  parameter int  unsigned PPROTW            = 3                                               ,
  // Width of the PVT data
  parameter int  unsigned PVT_TW            = 12                                              ,
  // Width of PVT I/Os signals to the remove probes
  parameter int  unsigned PVT_PROBEW        = 63                                              ,
  // Width of the PVT voltage i/o
  parameter int  unsigned PVT_VOLW          = 14                                              ,
  // width of interrupr outputs
  parameter int  unsigned IRQW              =  3                                              ,
  // type for temper#oature outputs
  parameter type          tms_temp_t        = logic [NB_EXT_TEMP_SENSE+NB_INT_TEMP_SENSE-1:0] ,

  // APB types
  parameter type          tms_paddr_t       = logic [PAW              -1:0]                   ,
  parameter type          tms_pdata_t       = logic [PDW              -1:0]                   ,
  parameter type          tms_pstrb_t       = logic [PSTRBW           -1:0]                   ,
  parameter type          tms_pprot_t       = logic [PPROTW           -1:0]                   ,
  parameter type          tms_irq_t         = logic [IRQW             -1:0]
)(
  // Clock, positive edge triggered
  input  wire                         i_clk                      ,
  // Asynchronous reset, active low
  input  wire                         i_rst_n                    ,
  // Asynchronous always-on reset, active low
  input  wire                         i_ao_rst_n                 ,
  // PVT Clock
  input  wire                         i_pvt_clk                  ,
  // PVT Reset
  input  wire                         i_pvt_rst_n                ,

  // APB bus
  input  tms_paddr_t                  i_cfg_apb4_s_paddr         ,
  input  tms_pdata_t                  i_cfg_apb4_s_pwdata        ,
  input  logic                        i_cfg_apb4_s_pwrite        ,
  input  logic                        i_cfg_apb4_s_psel          ,
  input  logic                        i_cfg_apb4_s_penable       ,
  input  tms_pstrb_t                  i_cfg_apb4_s_pstrb         ,
  input  tms_pprot_t                  i_cfg_apb4_s_pprot         ,
  output logic                        o_cfg_apb4_s_pready        ,
  output tms_pdata_t                  o_cfg_apb4_s_prdata        ,
  output logic                        o_cfg_apb4_s_pslverr       ,

  // JTAG interface
  input  wire                         i_jtag_tck                  ,
  input  wire                         i_jtag_rst_n                ,

  // thermal control signals
  // thermal throttle override
  input  logic                        i_thermal_throttle          ,
  // thermal throttle output to AI cores
  output tms_temp_t                   o_thermal_throttle          ,
  // thrermnal warning. From thermal throttle. Overheating warning to boardsystem
  output logic                        o_thermal_throttle_warning  ,
  // thermal warning. To partition AI cores
  output tms_temp_t                   o_thermal_warning           ,
  // thermal shutdown. Will reset the chip via pcb controller
  output logic                        o_thermal_shutdown          ,
  // irq for dml changes.
  output tms_irq_t                    o_irq                       ,

  // Connections to PVT probes.
  // inout need to be type wire for vcs compailation. code did not compile
  // with type defined.
  inout  wire [PVT_PROBEW       -1:0] io_pvt_ibias_ts             ,
  inout  wire [PVT_PROBEW       -1:0] io_pvt_vsense_ts            ,
  inout  wire                         io_pvt_test_out_ts          ,
  // PVT monitor voltage tot remove PVT probes
  inout  wire [PVT_VOLW         -1:0] io_pvt_vol_ts
`ifdef POWER_PINS
                                                                  ,
  inout  wire                         io_pvt_dvdd075a_ts          ,
  inout  wire                         io_pvt_dvss0a_ts            ,
  inout  wire                         io_pvt_avdd18a_ts           ,
  inout  wire                         io_pvt_avss0a_ts            ,
  inout  wire                         io_pvt_avss_gd
`endif
);

//==============================================================================
// Local parameters
// total number of temperature sensor probes.
localparam int  unsigned NB_TEMP_SENSE      = NB_EXT_TEMP_SENSE + NB_INT_TEMP_SENSE;
// number of APB masters at APB mux
localparam int unsigned NB_APBMUXIN         = 2                                    ;
localparam int unsigned APB_CFG_IDX         = 0                                    ;
localparam int unsigned APB_JTAG_IDX        = 1                                    ;

// numer of signals to be synced to i_clk
localparam int unsigned NB_EOC              = 2                                    ;

// PVT BJT SEL TS WIDTH
localparam int unsigned BJT_SELTS_W         = 6                                    ;
// PVT SEL TS WIDTH
localparam int unsigned PVT_SELTS_W         = 4                                    ;

//==============================================================================
// types
// APB
typedef logic [PAW        -1:0] tms_apb_mux_addr_t [NB_APBMUXIN]                  ;
typedef logic [PDW        -1:0] tms_apb_mux_data_t [NB_APBMUXIN]                  ;
typedef logic [PSTRBW     -1:0] tms_apb_mux_pstrb_t[NB_APBMUXIN]                  ;
typedef logic [PPROTW     -1:0] tms_apb_mux_pprot_t[NB_APBMUXIN]                  ;
typedef logic                   tms_apb_mux_logic_t[NB_APBMUXIN]                  ;

typedef logic [BJT_SELTS_W-1:0]tms_bjt_sel_t                                      ;
typedef logic [PVT_SELTS_W-1:0]tms_sel_t                                          ;

// Synchronizer
localparam int unsigned NB_SYNC_STAGES   = 2                                      ;
localparam logic        SYNC_RESET_VALUE = 1'h0                                   ;

// temperature array type. 2-D -> one for each CTM + width to match temperature data
// width.
typedef logic [PVT_TW-1:0] tms_temp_reg_t[NB_TEMP_SENSE]                          ;
// pvt output temp
typedef logic [PVT_TW-1:0] tms_pvt_res_t                                          ;

//==============================================================================
// signal declarations
// APB type declaration
tms_csr_reg_pkg::apb_h2d_t            reg_apb_req                   ;
tms_csr_reg_pkg::apb_d2h_t            reg_apb_rsp                   ;

// register interface type declaration
tms_csr_reg_pkg::tms_csr_reg2hw_t     reg2hw                        ;
tms_csr_reg_pkg::tms_csr_hw2reg_t     hw2reg                        ;

// pvt raw temperature value to registers
tms_temp_reg_t                        pvt_raw_value                 ;

tms_paddr_t                           jtag_to_apb4_s_paddr          ;
tms_pdata_t                           jtag_to_apb4_s_pwdata         ;
logic                                 jtag_to_apb4_s_pwrite         ;
logic                                 jtag_to_apb4_s_psel           ;
logic                                 jtag_to_apb4_s_penable        ;
tms_pstrb_t                           jtag_to_apb4_s_pstrb          ;
tms_pprot_t                           jtag_to_apb4_s_pprot          ;
logic                                 jtag_to_apb4_s_pready         ;
tms_pdata_t                           jtag_to_apb4_s_prdata         ;
logic                                 jtag_to_apb4_s_pslverr        ;

tms_apb_mux_addr_t                    apb4_mux_in_s_paddr           ;
tms_apb_mux_data_t                    apb4_mux_in_s_pwdata          ;
tms_apb_mux_logic_t                   apb4_mux_in_s_pwrite          ;
tms_apb_mux_logic_t                   apb4_mux_in_s_psel            ;
tms_apb_mux_logic_t                   apb4_mux_in_s_penable         ;
tms_apb_mux_pstrb_t                   apb4_mux_in_s_pstrb           ;
tms_apb_mux_pprot_t                   apb4_mux_in_s_pprot           ;
tms_apb_mux_logic_t                   apb4_mux_out_s_pready         ;
tms_apb_mux_data_t                    apb4_mux_out_s_prdata         ;
tms_apb_mux_logic_t                   apb4_mux_out_s_pslverr        ;

tms_paddr_t                           apb4_mux_slave_paddr          ;
tms_pstrb_t                           apb4_mux_slave_pstrb          ;

// pvt outputs
// pvt temp/voltage sensor data
tms_pvt_res_t                         pvt_ts_out                    ;
tms_pvt_res_t                         pvt_ps_out                    ;
// registered pvt sensor data
tms_pvt_res_t                         pvt_ts_out_del                ;
tms_pvt_res_t                         pvt_ps_out_del                ;

// pvt end of conversion
logic                                 pvt_eoc_ts                    ;
logic                                 pvt_eoc_ts_sync               ;
logic                                 pvt_eoc_ps                    ;
logic                                 pvt_eoc_ps_sync               ;
// Edge detected ts eoc signal to enable register updates
logic                                 eoc_ts_reg_ena                ;
logic                                 eoc_ts_clr_ena                ;
logic                                 eoc_ts_reg_ena_del            ;
logic                                 eoc_ps_reg_ena                ;
logic                                 eoc_ps_clr_ena                ;
logic                                 eoc_ps_reg_ena_del            ;

logic                                 pvt_auto_soc_ts               ;
logic                                 pvt_auto_en_ts                ;
logic                                 pvt_auto_en_adc_ts            ;
tms_sel_t                             pvt_auto_sel_ts               ;
tms_bjt_sel_t                         pvt_auto_bjt_sel_ts           ;

logic                                 sel_pvt_en_ts                 ;
logic                                 sel_pvt_en_adc_ts             ;
logic                                 sel_pvt_soc_ts                ;
tms_bjt_sel_t                         sel_pvt_bjt_sel_ts            ;
tms_sel_t                             sel_pvt_sel_ts                ;
// CTM results to CSR register ena
tms_temp_t                            ctm_reg_ena                   ;

// thermal stats outputs from CTM
tms_temp_t                            ctm_thermal_shutdown          ;
tms_temp_t                            ctm_thermal_warning           ;
tms_temp_t                            ctm_thermal_throttle          ;
tms_temp_reg_t                        ctm_min_temp                  ;
tms_temp_reg_t                        ctm_max_temp                  ;
tms_temp_reg_t                        ctm_cur_temp                  ;
logic                                 thermal_throttle_sync         ;

//==============================================================================
// RTL
// TODO:Connect when sources are defined
always_comb begin
  o_irq = {IRQW{1'h0}};
end
//

// PVT Wrapper
pvt_wrapper u_pvt_wrapper (
  .i_pvt_en_ts            ( sel_pvt_en_ts                        ), // MUXED Signal from SW or Auto
  .i_pvt_en_adc_ts        ( sel_pvt_en_adc_ts                    ), // MUXED Signal from SW or Auto
  .i_pvt_clk_ts           ( i_pvt_clk                            ), // MUXED Signal from SW or Auto
  .i_pvt_soc_ts           ( sel_pvt_soc_ts                       ), // MUXED Signal from SW or Auto
  .i_pvt_bjt_sel_ts       ( sel_pvt_bjt_sel_ts                   ), // MUXED Signal from SW or Auto
  .i_pvt_sel_ts           ( sel_pvt_sel_ts                       ), // MUXED Signal from SW or Auto
  .i_pvt_buf_slope_sel_ts ( reg2hw.pvt_ctrl.pvt_buf_slope_sel_ts ),
  .i_pvt_buf_vref_sel_ts  ( reg2hw.pvt_ctrl.pvt_buf_vref_sel_ts  ),
  .i_pvt_bgr_trim_ts      ( reg2hw.pvt_ctrl.pvt_bgr_trim_ts      ),
  .i_pvt_vref_trim_ts     ( reg2hw.pvt_ctrl.pvt_vref_trim_ts     ),
  .i_pvt_vbe_trim_ts      ( reg2hw.pvt_ctrl.pvt_vbe_trim_ts      ),
  .i_pvt_adc_cctrl_ts     ( reg2hw.pvt_ctrl.pvt_adc_cctrl_ts     ),
  .i_pvt_adc_ictrl_ts     ( reg2hw.pvt_ctrl.pvt_adc_ictrl_ts     ),
  .i_pvt_mux_addr_ts      ( reg2hw.pvt_mode_ctrl.pvt_mux_addr_ts ),
  .i_pvt_avg_mode_ts      ( reg2hw.pvt_mode_ctrl.pvt_avg_mode_ts ),
  .i_pvt_scan_test_clk    (                                      ), // ASO-UNDRIVEN_INPUT : To be connected by DFT
  .i_pvt_scan_test_mode   (                                      ), // ASO-UNDRIVEN_INPUT : To be connected by DFT
  .i_pvt_soc_ps           ( reg2hw.pvt_mode_ctrl.pvt_soc_ps      ),
  .i_pvt_en_ps            ( reg2hw.pvt_mode_ctrl.pvt_en_ps       ),
  .o_pvt_out_12bit_ts     ( pvt_ts_out                           ),
  .o_pvt_eoc_ps           ( pvt_eoc_ps                           ),
  .o_pvt_ps_freq_out      (                                      ), // NOT USED
  .o_pvt_eoc_ts           ( pvt_eoc_ts                           ),
  .o_pvt_out_12bit_ps     ( pvt_ps_out                           ),
  .io_pvt_ibias_ts        ( io_pvt_ibias_ts                      ),
  .io_pvt_vsense_ts       ( io_pvt_vsense_ts                     ),
  .io_pvt_test_out_ts     ( io_pvt_test_out_ts                   ),
  .io_pvt_vol_ts          ( io_pvt_vol_ts                        )
`ifdef POWER_PINS
                                                                  ,
  .io_pvt_dvdd075a_ts     ( io_pvt_dvdd075a_ts                   ),
  .io_pvt_dvss0a_ts       ( io_pvt_dvss0a_ts                     ),
  .io_pvt_avdd18a_ts      ( io_pvt_avdd18a_ts                    ),
  .io_pvt_avss0a_ts       ( io_pvt_avss0a_ts                     ),
  .io_pvt_avss_gd         ( io_pvt_avss_gd                       )
`endif
);

always_comb begin
  sel_pvt_en_ts       = reg2hw.pvt_mode_ctrl.pvt_mode ? reg2hw.pvt_mode_ctrl.pvt_en_ts      : pvt_auto_en_ts     ;
  sel_pvt_en_adc_ts   = reg2hw.pvt_mode_ctrl.pvt_mode ? reg2hw.pvt_mode_ctrl.pvt_en_adc_ts  : pvt_auto_en_adc_ts ;
  sel_pvt_soc_ts      = reg2hw.pvt_mode_ctrl.pvt_mode ? reg2hw.pvt_mode_ctrl.pvt_soc_ts     : pvt_auto_soc_ts    ;
  sel_pvt_bjt_sel_ts  = reg2hw.pvt_mode_ctrl.pvt_mode ? reg2hw.pvt_mode_ctrl.pvt_bjt_sel_ts : pvt_auto_bjt_sel_ts;
  sel_pvt_sel_ts      = reg2hw.pvt_mode_ctrl.pvt_mode ? reg2hw.pvt_mode_ctrl.pvt_sel_ts     : pvt_auto_sel_ts    ;
end

//==============================================================================
// Synchronize EOC outputs from PVT to i_clk
// ECO ts measurement
axe_tcl_seq_sync #(
  .SyncStages ( NB_SYNC_STAGES   ),
  .ResetValue ( SYNC_RESET_VALUE )
) u_axe_tcl_eoc_ts_sync (
  .i_clk      ( i_clk            ),
  .i_rst_n    ( i_rst_n          ),
  .i_d        ( pvt_eoc_ts       ),
  .o_q        ( pvt_eoc_ts_sync  )
);

// EOC processs sensor
axe_tcl_seq_sync #(
  .SyncStages ( NB_SYNC_STAGES   ),
  .ResetValue ( SYNC_RESET_VALUE )
) u_axe_tcl_eoc_ps_sync (
  .i_clk      ( i_clk            ),
  .i_rst_n    ( i_rst_n          ),
  .i_d        ( pvt_eoc_ps       ),
  .o_q        ( pvt_eoc_ps_sync  )
);

// Thermal throttle synchronizer. This is an asynchronous signal from top-level PAD.
axe_tcl_seq_sync #(
  .SyncStages ( NB_SYNC_STAGES        ),
  .ResetValue ( SYNC_RESET_VALUE      )
) u_axe_tcl_thermal_throttle_sync (
  .i_clk      ( i_clk                 ),
  .i_rst_n    ( i_rst_n               ),
  .i_d        ( i_thermal_throttle    ),
  .o_q        ( thermal_throttle_sync )
);

// rising edge detect sync to generate enable for storing pvt data
tms_edge_detect u_tms_ts_data_valid_edge_detect (
  .i_clk   ( i_clk           ),
  .i_rst_n ( i_rst_n         ),
  .din     ( pvt_eoc_ts_sync ),
  .redge   ( eoc_ts_reg_ena  ),
  .fedge   ( eoc_ts_clr_ena  ),
  .aedge   (                 )  // not used
);

tms_edge_detect u_tms_ps_data_valid_edge_detect (
  .i_clk   ( i_clk           ),
  .i_rst_n ( i_rst_n         ),
  .din     ( pvt_eoc_ps_sync ),
  .redge   ( eoc_ps_reg_ena  ),
  .fedge   ( eoc_ps_clr_ena  ),
  .aedge   (                 )  // not used
);

// register pvt temp_ts outputs
always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    pvt_ts_out_del     <=   '0;
    eoc_ts_reg_ena_del <= 1'h0;
    pvt_ps_out_del     <=   '0;
    eoc_ps_reg_ena_del <= 1'h0;
  end else begin
    // Delay register enable so that timing matches delayfor data
    eoc_ts_reg_ena_del <= eoc_ts_reg_ena;
    eoc_ps_reg_ena_del <= eoc_ps_reg_ena;
    if (eoc_ts_reg_ena) begin
      pvt_ts_out_del <= pvt_ts_out;
    end
    if (eoc_ps_reg_ena) begin
      pvt_ps_out_del <= pvt_ps_out;
    end
  end
end

// connect pvt output to data register input
always_comb begin
  // PVT TS Data register
  hw2reg.pvt_data.pvt_out_12bit_ts.d  = pvt_ts_out_del    ;
  hw2reg.pvt_data.pvt_out_12bit_ts.de = eoc_ts_reg_ena_del;
  // TS EOC register
  hw2reg.pvt_data.pvt_eoc_ts.d        = pvt_eoc_ts_sync   ;
  hw2reg.pvt_data.pvt_eoc_ts.de       = eoc_ts_reg_ena_del | eoc_ts_clr_ena;
  // PVT PS Data register
  hw2reg.pvt_data.pvt_out_12bit_ps.d  = pvt_ps_out_del    ;
  hw2reg.pvt_data.pvt_out_12bit_ps.de = eoc_ps_reg_ena_del;
  // PSEOC register
  hw2reg.pvt_data.pvt_eoc_ps.d        = pvt_eoc_ps_sync   ;
  hw2reg.pvt_data.pvt_eoc_ps.de       = eoc_ps_reg_ena_del | eoc_ps_clr_ena;
end

tms_ctm_ctrl #(
  .NB_TEMP_SENSE ( NB_TEMP_SENSE  )
) u_tms_ctm_ctrl (
  .i_clk           ( i_clk                         ),
  .i_rst_n         ( i_rst_n                       ),
  .i_pvt_clk       ( i_pvt_clk                     ),
  .i_pvt_rst_n     ( i_pvt_rst_n                   ),
  .i_ctm_mode_ena  (~reg2hw.pvt_mode_ctrl.pvt_mode ),
  .o_en_ts         ( pvt_auto_en_ts                ),
  .o_en_adc_ts     ( pvt_auto_en_adc_ts            ),
  .o_sel_ts        ( pvt_auto_sel_ts               ),
  .o_bjt_sel_ts    ( pvt_auto_bjt_sel_ts           ),
  .o_soc_ts        ( pvt_auto_soc_ts               ),
  .i_eoc_ts        ( pvt_eoc_ts_sync               )
);

//==============================================================================
// CSR
// aPB connnects to reg_apb_req/reg_apb_rsp. Connections are made at the APB
// mux
// Write registers are output on reg2hw
// Read  registers are input  on hw2reg

tms_csr_reg_top u_tms_csr_reg_top (
  .clk_i     ( i_clk       ),
  .rst_ni    ( i_rst_n     ),
  .apb_i     ( reg_apb_req ),
  .apb_o     ( reg_apb_rsp ),
  .reg2hw    ( reg2hw      ), // Write
  .hw2reg    ( hw2reg      ), // Read
  .devmode_i ( 1'h1        )  // If 1, explicit error return for unmapped register access
);

//==============================================================================
// JTAG 2 APB Bridge
axe_jtag_to_apb #(
  .PAW                   ( PAW                     ),
  .PDW                   ( PDW                     ),
  .PSTRBW                ( PSTRBW                  ),
  .SyncStages            ( NB_SYNC_STAGES          )
) u_tms_jtag_to_apb (
  .i_clk                 ( i_clk                   ),
  .i_rst_n               ( i_rst_n                 ),
  .i_ao_rst_n            ( i_ao_rst_n              ),
  .tcki                  ( i_jtag_tck              ),
  .trsti                 ( i_jtag_rst_n            ),
  .o_apb_m_paddr         ( jtag_to_apb4_s_paddr    ),
  .o_apb_m_pwdata        ( jtag_to_apb4_s_pwdata   ),
  .o_apb_m_pwrite        ( jtag_to_apb4_s_pwrite   ),
  .o_apb_m_psel          ( jtag_to_apb4_s_psel     ),
  .o_apb_m_penable       ( jtag_to_apb4_s_penable  ),
  .o_apb_m_pstrb         ( jtag_to_apb4_s_pstrb    ),
  .o_apb_m_pprot         ( jtag_to_apb4_s_pprot    ),
  .i_apb_m_pready        ( jtag_to_apb4_s_pready   ),
  .i_apb_m_prdata        ( jtag_to_apb4_s_prdata   ),
  .i_apb_m_pslverr       ( jtag_to_apb4_s_pslverr  )
);

//==============================================================================
// APB bus managers to mux connections
always_comb apb4_mux_in_s_paddr   [APB_CFG_IDX]  = i_cfg_apb4_s_paddr;
always_comb apb4_mux_in_s_pwdata  [APB_CFG_IDX]  = i_cfg_apb4_s_pwdata;
always_comb apb4_mux_in_s_pwrite  [APB_CFG_IDX]  = i_cfg_apb4_s_pwrite;
always_comb apb4_mux_in_s_psel    [APB_CFG_IDX]  = i_cfg_apb4_s_psel;
always_comb apb4_mux_in_s_penable [APB_CFG_IDX]  = i_cfg_apb4_s_penable;
always_comb apb4_mux_in_s_pstrb   [APB_CFG_IDX]  = i_cfg_apb4_s_pstrb;
always_comb apb4_mux_in_s_pprot   [APB_CFG_IDX]  = i_cfg_apb4_s_pprot;
always_comb o_cfg_apb4_s_pready                  = apb4_mux_out_s_pready [APB_CFG_IDX];
always_comb o_cfg_apb4_s_prdata                  = apb4_mux_out_s_prdata [APB_CFG_IDX];
always_comb o_cfg_apb4_s_pslverr                 = apb4_mux_out_s_pslverr[APB_CFG_IDX];

always_comb apb4_mux_in_s_paddr   [APB_JTAG_IDX] = jtag_to_apb4_s_paddr;
always_comb apb4_mux_in_s_pwdata  [APB_JTAG_IDX] = jtag_to_apb4_s_pwdata;
always_comb apb4_mux_in_s_pwrite  [APB_JTAG_IDX] = jtag_to_apb4_s_pwrite;
always_comb apb4_mux_in_s_psel    [APB_JTAG_IDX] = jtag_to_apb4_s_psel;
always_comb apb4_mux_in_s_penable [APB_JTAG_IDX] = jtag_to_apb4_s_penable;
always_comb apb4_mux_in_s_pstrb   [APB_JTAG_IDX] = jtag_to_apb4_s_pstrb;
always_comb apb4_mux_in_s_pprot   [APB_JTAG_IDX] = jtag_to_apb4_s_pprot;
always_comb jtag_to_apb4_s_pready                = apb4_mux_out_s_pready [APB_JTAG_IDX];
always_comb jtag_to_apb4_s_prdata                = apb4_mux_out_s_prdata [APB_JTAG_IDX];
always_comb jtag_to_apb4_s_pslverr               = apb4_mux_out_s_pslverr[APB_JTAG_IDX];

// APB mux and arbitration
// multi master -> single slave
axe_apb_mux #(
  .NB_APBIN ( NB_APBMUXIN ),
  .PAW      ( PAW         ),
  .PDW      ( PDW         ),
  .PSTRBW   ( PSTRBW      )
) u_tmp_apbmux (
  .i_clk                    ( i_clk                  ),
  .i_rst_n                  ( i_rst_n                ),
  // APB input interface
  .i_apb_s_paddr            ( apb4_mux_in_s_paddr    ),
  .i_apb_s_pwdata           ( apb4_mux_in_s_pwdata   ),
  .i_apb_s_pwrite           ( apb4_mux_in_s_pwrite   ),
  .i_apb_s_psel             ( apb4_mux_in_s_psel     ),
  .i_apb_s_penable          ( apb4_mux_in_s_penable  ),
  .i_apb_s_pstrb            ( apb4_mux_in_s_pstrb    ),
  .i_apb_s_pprot            ( apb4_mux_in_s_pprot    ),
  .o_apb_s_pready           ( apb4_mux_out_s_pready  ),
  .o_apb_s_prdata           ( apb4_mux_out_s_prdata  ),
  .o_apb_s_pslverr          ( apb4_mux_out_s_pslverr ),
  // APB output interface
  .o_apb_m_paddr            ( apb4_mux_slave_paddr   ),
  .o_apb_m_pwdata           ( reg_apb_req.pwdata     ),
  .o_apb_m_pwrite           ( reg_apb_req.pwrite     ),
  .o_apb_m_psel             ( reg_apb_req.psel       ),
  .o_apb_m_penable          ( reg_apb_req.penable    ),
  .o_apb_m_pstrb            ( reg_apb_req.pstrb      ),
  .o_apb_m_pprot            ( reg_apb_req.pprot      ),
  .i_apb_m_pready           ( reg_apb_rsp.pready     ),
  .i_apb_m_prdata           ( reg_apb_rsp.prdata     ),
  .i_apb_m_pslverr          ( reg_apb_rsp.pslverr    )
);

// connect mismatched bus width from mux to registers
always_comb begin
 reg_apb_req.paddr = {{32-PAW{1'h0}}, apb4_mux_slave_paddr    };
end

//==============================================================================
// CTM
// for generate
for (genvar i=0; i<NB_TEMP_SENSE; i++) begin : gen_tms_ctm
  tms_ctm #(
    .CH_NUM                           ( i + 1                                       ),
    .PVT_TW                           ( PVT_TW                                      )
  ) u_tms_ctm (
    .i_clk                            ( i_clk                                       ),
    .i_rst_n                          ( i_rst_n                                     ),
    .i_pvt_temp_value                 ( pvt_ts_out_del                              ),
    .i_pvt_eoc_ts                     ( eoc_ts_reg_ena                              ), // Temp/Voltage End of conversion
    .i_pvt_bjt_sel_ts                 ( sel_pvt_bjt_sel_ts                          ),
    .i_csr_offset_comp                ( reg2hw.ctm_offset_comp       [i]            ),
    .i_csr_thermal_shutdown_threshold ( reg2hw.ctm_thrm_shtdwn_thresh[i]            ),
    .i_csr_thermal_warning_threshold  ( reg2hw.ctm_thrm_warn_thresh  [i]            ),
    .i_csr_throttle_on_temp           ( reg2hw.ctm_thrtl_on_temp     [i]            ),
    .i_csr_throttle_off_temp          ( reg2hw.ctm_thrtl_off_temp    [i]            ),
    .i_thermal_throttle               ( thermal_throttle_sync                       ),
    .o_thermal_shutdown               ( ctm_thermal_shutdown         [i]            ),
    .o_thermal_warning                ( ctm_thermal_warning          [i]            ),
    .o_thermal_throttle               ( ctm_thermal_throttle         [i]            ),
    .o_csr_min_temp_value             ( ctm_min_temp                 [i]            ),
    .o_csr_max_temp_value             ( ctm_max_temp                 [i]            ),
    .o_csr_cur_temp_value             ( ctm_cur_temp                 [i]            ),
    .i_csr_shtdwn_ena                 ( reg2hw.ctm_thermal_ctrl      [i].shtdwn_ena ),
    .i_csr_warn_ena                   ( reg2hw.ctm_thermal_ctrl      [i].warn_ena   ),
    .i_csr_throttle_ena               ( reg2hw.ctm_thermal_ctrl      [i].thrtl_ena  ),
    .o_ctm_reg_ena                    ( ctm_reg_ena                  [i]            )
  );
end

//==============================================================================
// thermal output controls
always_comb begin
  o_thermal_shutdown         = |ctm_thermal_shutdown  ; // 1-bit

  o_thermal_warning          =  ctm_thermal_warning   ; // 12-bit
  o_thermal_throttle         =  ctm_thermal_throttle  ; // 12-bit

  // mux thermal throttle/warnign signals to generate the output
  if (reg2hw.thermal_warning_ctrl) begin
    o_thermal_throttle_warning = |ctm_thermal_throttle; // 1 bit
  end else begin
    o_thermal_throttle_warning = |ctm_thermal_warning ; // 1 bit
  end
end

// connect thermal status registers plus temperature result CSR
for (genvar i=0; i<NB_TEMP_SENSE; i++) begin : gen_connect_thermal_status_reg
  always_comb begin
    // thermal status
    hw2reg.ctm_thermal_status[i].shtdwn_status.d  = ctm_thermal_shutdown[i];
    hw2reg.ctm_thermal_status[i].shtdwn_status.de = ctm_reg_ena         [i];
    hw2reg.ctm_thermal_status[i].warn_status  .d  = ctm_thermal_warning [i];
    hw2reg.ctm_thermal_status[i].warn_status  .de = ctm_reg_ena         [i];
    hw2reg.ctm_thermal_status[i].thrtl_status .d  = ctm_thermal_throttle[i];
    hw2reg.ctm_thermal_status[i].thrtl_status .de = ctm_reg_ena         [i];

    // temp result
    hw2reg.ctm_min_temp      [i]              .d  = ctm_min_temp        [i];
    hw2reg.ctm_min_temp      [i]              .de = ctm_reg_ena         [i];
    hw2reg.ctm_max_temp      [i]              .d  = ctm_max_temp        [i];
    hw2reg.ctm_max_temp      [i]              .de = ctm_reg_ena         [i];
    hw2reg.ctm_cur_temp      [i]              .d  = ctm_cur_temp        [i];
    hw2reg.ctm_cur_temp      [i]              .de = ctm_reg_ena         [i];
  end
end

endmodule

`endif // TMS_SV
