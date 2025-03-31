// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>


/// Description: Europa SoC Management Block Package file
///
package soc_mgmt_pkg;
  import chip_pkg    ::*;

  /// AXI Manager parameters
  /// AXI ID Width
  parameter int unsigned SOC_MGMT_LT_AXI_M_ID_W = 4;
  typedef logic [SOC_MGMT_LT_AXI_M_ID_W-1:0] soc_mgmt_lt_axi_m_id_t;

  /// AXI Subordinate parameters
  /// AXI ID Width
  parameter int unsigned SOC_MGMT_LT_AXI_S_ID_W = 4;
  typedef logic [SOC_MGMT_LT_AXI_S_ID_W-1:0] soc_mgmt_lt_axi_s_id_t;

  parameter int unsigned OBS_IP_BUS_W      = 352;
  parameter int unsigned OBS_OP_BUS_W      = 16;

  typedef logic [OBS_IP_BUS_W-1:0] obs_in_t;
  typedef logic [OBS_OP_BUS_W-1:0] obs_out_t;

  //============================================================================
  // TMS Parameters
  parameter int unsigned TMS_NB_EXT_TSENSE = 11;
  // Number of temp sensors in tms
  parameter int unsigned TMS_NB_INT_TSENSE =  1;
  // Number of total temp sensors
  parameter int unsigned TMS_NB_TSENSE = TMS_NB_EXT_TSENSE + TMS_NB_INT_TSENSE;
  // Width of the PVT data
  parameter int unsigned TMS_TW            = 12;
  // Width of PVT I/Os signals to the remove probes
  parameter int unsigned TMS_PROBEW        = 63;
  // Width of the PVT voltage i/o
  parameter int unsigned TMS_VOLW          = 14;

  /// TMS inrterrupt
  parameter int unsigned TMS_IRQW           =  3;

  // type for temperature outputs
  typedef logic [TMS_NB_TSENSE-1:0] tms_temp_t;

  // type for tms irq
  typedef logic [TMS_IRQW     -1:0] tms_irq_t ;

  // TMS apb address bus width
  parameter int  unsigned TMS_PAW          = 16;
  // TMS apb data bus width
  parameter int  unsigned TMS_PDW          = 32;
  // width definition for APB strobe bus
  parameter int  unsigned PSTRBW           = 4;
  // width definition for APB pprot bus
  parameter int  unsigned PPROTW           = 3;

  // APB type declarations
  typedef logic [PSTRBW-1:0] soc_mgmt_pstrb_t;
  typedef logic [PPROTW-1:0] soc_mgmt_pprot_t;

  // pprot value will be constant as follows:
  // +-----+--------+-------------------+
  // | BIT |  Value | Description       |
  // +-----+--------+-------------------+
  // |  0  |    0   | Normal access     |
  // |  1  |    1   | non-secure access |
  // |  2  |    0   | Data access       |
  // +-----+--------+-------------------+
  parameter soc_mgmt_pprot_t PPROT_VAL     = 3'h2;

  // pstrb value will be constant
  // Set write strobe for all byte lanes
  parameter soc_mgmt_pstrb_t PSTRB_VAL     = '1;

  //============================================================================
  // ppmu
  parameter int unsigned PPMU_COUNTW       = 8;
  parameter int unsigned PPMU_STATEW       = 4;

  typedef logic [PPMU_COUNTW-1:0] ppmu_t;
  typedef logic [PPMU_STATEW-1:0] ppmu_state_t;

  //////////////////////
  // Clock Generation //
  //////////////////////

  /// The number of coices of a single CLK mux
  parameter int unsigned CLK_MUX_CHOICES   = 2;
  /// The Select width fot the sys clk mux
  parameter int unsigned ClkMuxSelectWidth = cc_math_pkg::index_width(CLK_MUX_CHOICES);
  typedef logic [ClkMuxSelectWidth-1:0] clk_mux_select_t;
  typedef enum clk_mux_select_t {
    PLL_SYS_0_CLK = clk_mux_select_t'(0),
    PLL_SYS_1_CLK = clk_mux_select_t'(1)
  } clk_pll_mux_select_e;

  typedef enum clk_mux_select_t {
    REF_CLK = clk_mux_select_t'(0),
    DIV_CLK = clk_mux_select_t'(1)
  } clk_div_mux_select_e;

  /// Clock mux has an active clock during reset
  parameter bit CLK_ACTIVE_RESET  = 1'b1;

  /// The number of System PLLs are generated
  typedef enum int unsigned {
    PLL_SYS_0 = 0,
    PLL_SYS_1 = 1,
    PLL_DDR   = 2
  } pll_index_e;
  parameter int unsigned NUM_PLL = 3;

  /// The number of system clocks that are generated
  typedef enum int unsigned {
    CLK_FAST   = 0,
    CLK_APU    = 1,
    CLK_CODEC  = 2,
    CLK_EMMC   = 3,
    CLK_PERIPH = 4,
    CLK_PVT    = 5
  } clk_index_e;
  parameter int unsigned NUM_SYS_CLK = 6;

  /// The maximum integer division each system clock can be divided by
  parameter int unsigned CLK_MAX_INT_DIVISION = 25;
  /// The derived width of the division factor
  parameter int unsigned ClkMaxIntDivisorWidth = cc_math_pkg::index_width(CLK_MAX_INT_DIVISION) + 1;
  typedef logic [ClkMaxIntDivisorWidth-1:0] clk_int_divisor_t;

  /// The PLL configuration, should be set from CSR
  typedef struct packed {
    /// Monitoring pin. If AFC_ENB=0, AFC is enabled and VCO is calibrated automatically.
    /// If AFC_ENB=1, AFC is disabled and VCO is calibrated manually by EXTAFC[4:0] for the test of VCO range.
    /// Default value : 1'
    logic       afc_enb;
    /// If BYPASS = 1, bypass mode is enabled. (FOUT = FIN) If BYPASS = 0, PLL operates normally.
    logic       bypass;
    /// Monitoring pin. If AFC_ENB=1, AFC is disabled and VCO is calibrated manually by EXTAFC[4:0] for the
    /// test of VCO range. Default value : 5'b0_0000
    logic [4:0] extafc;
    /// Monitoring pin. If FEED_EN=1, FEED_OUT is enabled. Default value : 1'b0
    logic       feed_en;
    /// Scaler's re-initialization time control pin. Default value : 1'b0
    logic       fout_mask;
    /// Monitoring pin. If FSEL = 0, FEED_OUT = FREF. If FSEL = 1, FEED_OUT = FEED. Default value : 1'b0
    logic       fsel;
    /// Controls the charge-pump current. Default value : 2'b01
    logic [1:0] icp;
    /// Lock detector setting of the detection resolution. Default value : 2'b11
    logic [1:0] lock_con_dly;
    /// Lock detector setting of the input margin. Default value : 2'b11
    logic [1:0] lock_con_in;
    /// Lock detector setting of the output margin. Default value : 2'b11
    logic [1:0] lock_con_out;
    /// Division value of the 10-bit programmable main-divider. PLL has to be reset if M value is changed.
    logic [9:0] div_main;
    /// Division value of the 6-bit programmable pre-divider. PLL has to be reset if P value is changed.
    logic [5:0] div_pre;
    /// RESETB signal is used for power down control.
    /// If RESETB = 0, power down mode is enabled and all digital blocks are reset.
    /// If RESETB = 1 from 0, PLL starts its normal operation after lock time.
    logic       resetb;
    /// Reserved pin. Default value : 4'b1000
    logic [3:0] rsel;
    /// Division value of the 3-bit programmable scaler.
    logic [2:0] div_scalar;
  } pll_config_t;
  parameter int unsigned PllConfigWidth = unsigned'($bits(pll_config_t));

  /// The PLL observable status
  typedef struct packed {
    /// Monitoring pin. Output code of AFC (5 bits).
    logic [4:0] afc_code;
    /// Monitoring pin. FREF or FEED can be observed.
    logic       feed_out;
    /// If PLL is unlocked, LOCK=0. If PLL is locked, LOCK = 1.
    logic       lock;
  } pll_status_t;

  /// The Clock Mux and Divisor configuration
  typedef struct packed {
    /// The divisor has been updated (needed for CDC)
    logic                updated;
    /// Divisor for the initeger clock divider (`0` turns clock off)
    clk_int_divisor_t    divisor;
    /// Index of the pll clock the mux should select.
    clk_pll_mux_select_e pll_mux_select;
    /// The multiplexer for selecting the PLL is enabled
    logic                pll_mux_enable;
    /// Index of the pll clock the mux should select.
    clk_div_mux_select_e div_mux_select;
    /// The multiplexer for selecting the PLL is enabled
    logic                div_mux_enable;
  } mux_div_config_t;
  parameter int unsigned MuxDivConfigWidth = unsigned'($bits(mux_div_config_t));

  typedef struct packed {
    /// The onehot index of the exact clock that is active
    logic [CLK_MUX_CHOICES-1:0] pll_mux_active;
    /// A clock on the mux is currently active
    logic                       pll_mux_is_on;
    /// The onehot index of the exact clock that is active
    logic [CLK_MUX_CHOICES-1:0] div_mux_active;
    /// A clock on the mux is currently active
    logic                       div_mux_is_on;
  } mux_div_status_t;

  /// The Clock Mux and Divisor configuration
  typedef struct packed {
    /// Index of the clock the mux should select.
    logic mux_select;
    /// The multiplexer is enabled
    logic mux_enable;
  } mux_ddr_config_t;
  parameter int unsigned MuxDdrConfigWidth = unsigned'($bits(mux_ddr_config_t));

  typedef struct packed {
    /// The onehot index of the exact clock that is active
    logic [1:0] mux_active;
    /// A clock on the mux is currently active
    logic       mux_is_on;
  } mux_ddr_status_t;

  //============================================================================
  // debugger interface
  parameter int unsigned NHART                     = 30    ;

  typedef logic [NHART         -1:0] dbg_hart_t            ;

  parameter int unsigned NB_TRIG                  = 1      ;

  typedef logic [NB_TRIG      -1:0] dbg_trigger_t          ;

  parameter int unsigned DTM_ADDR_WIDTH            = 10    ;

  parameter int unsigned SERIAL_COUNT              = 0     ;
  parameter int unsigned SERIAL0                   = 0     ;
  parameter int unsigned PROGBUF_SIZE              = 2     ;
  parameter int unsigned HALTGROUP_COUNT           = 0     ;
  parameter int unsigned DMXTRIGGER_COUNT          = 0     ;
  parameter int unsigned NEXTDM_ADDR               = 0     ;
  parameter int unsigned SYSTEM_BUS_ACCESS_SUPPORT = 1     ;
  parameter int unsigned HASEL_SUPPORT             = 1     ;

  //============================================================================
  // AHB
  parameter int unsigned  AHB_HADDRW  = 32                 ;
  parameter int unsigned  AHB_HTRANSW = 2                  ;
  parameter int unsigned  AHB_HSIZEW  = 3                  ;
  parameter int unsigned  AHB_HBURSTW = 3                  ;
  parameter int unsigned  AHB_HPROTW  = 4                  ;
  parameter int unsigned  AHB_HDATAW  = 32                 ;
  parameter int unsigned  AHB_HRESPW  = 2                  ;

  typedef logic [AHB_HADDRW -1:0] ahb_haddr_t              ;
  typedef logic [AHB_HTRANSW-1:0] ahb_htrans_t             ;
  typedef logic [AHB_HSIZEW -1:0] ahb_hsize_t              ;
  typedef logic [AHB_HBURSTW-1:0] ahb_hburst_t             ;
  typedef logic [AHB_HPROTW -1:0] ahb_hprot_t              ;
  typedef logic [AHB_HDATAW -1:0] ahb_hdata_t              ;
  typedef logic [AHB_HRESPW -1:0] ahb_hresp_t              ;

  //============================================================================
  // SYSCFG APB DEMUX
  parameter int unsigned SYSCFG_NB_APBOUT     = 5                      ;
  parameter int unsigned SYSCFG_APB_DEMUX_PAW = CHIP_SYSCFG_ADDR_W     ;
  parameter int unsigned SYSCFG_APB_DEMUX_PDW = CHIP_APB_SYSCFG_DATA_W ;
  parameter int unsigned SYSCFG_APB_IDXW      = 3                      ;

  typedef logic [SYSCFG_APB_IDXW -1:0]  syscfg_apb_mux_idx_t           ;

  //============================================================================
  // DLM
  parameter int unsigned                DLM_THRTLW     =  8;
  parameter int unsigned                DLM_CLK_THRTLW = 15;
  parameter int unsigned                AIC_BOOSTW     =  8;
  parameter int unsigned                DLM_INTW       =  2;
  parameter int unsigned                TMS_INTW       =  3;

  typedef logic [DLM_THRTLW    -1:0]    aic_thrtl_t        ;
  typedef logic [DLM_CLK_THRTLW-1:0]    dlm_clk_thrtl_t    ;
  typedef logic [AIC_BOOSTW    -1:0]    aic_boost_t        ;
  typedef logic [DLM_INTW      -1:0]    dlm_int_t          ;
  typedef logic [TMS_INTW      -1:0]    tms_int_t          ;

endpackage
