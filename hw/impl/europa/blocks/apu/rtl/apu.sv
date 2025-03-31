/// Description: Application Processor Unit containing AX65 Cluster
///
module apu
  import apu_pkg::*;
  import apu_interrupt_map_pkg::*;
(
  /// Clock, positive edge triggered
  /// Slow ref clock
  input wire i_mtime_clk,
  input wire i_por_rst_n,
  /// Fast core clocks
  input wire [CORE_WIDTH - 1:0] i_cores_clk,
  input wire [CORE_WIDTH - 1:0] i_cores_rst_n,
  /// Fast AXI clock
  input wire i_aclk,
  input wire i_free_run_aclk,
  input wire i_arst_n,
  /// Fast l2 clock
  input wire i_l2c_clk,
  input wire i_l2c_rst_n,

  /// Core NMI IRQs
  input  logic [CORE_WIDTH - 1:0] i_cores_nmi,
  /// External IRQs from AIC to APU
  output logic [APU_AIC_WIDTH - 1:0] o_aic_msip,
  output logic [APU_AIC_WIDTH - 1:0] o_aic_mtip,
  input  logic [APU_AIC_WIDTH - 1:0] i_aic_stoptime,
  /// External IRQs to APU
  input  apu_external_irqs_t i_external_irqs,

  /// Debug sigs
  input logic [CORE_WIDTH - 1:0] i_cores_debugint,
  input logic [CORE_WIDTH - 1:0] i_cores_resethaltreq,
  output logic [CORE_WIDTH - 1:0] o_cores_hart_unavail,
  output logic [CORE_WIDTH - 1:0] o_cores_hart_under_reset,

  /// NoC AXI Connections LP Init Port
  // AXI write address channel
  output apu_axi_lt_s_aw_t              o_apu_init_lt_axi_m_aw,
  input  logic                          i_apu_init_lt_axi_m_awready,
  output logic                          o_apu_init_lt_axi_m_awvalid,
  // AXI write data channel
  output apu_axi_lt_w_t                 o_apu_init_lt_axi_m_w,
  input  logic                          i_apu_init_lt_axi_m_wready,
  output logic                          o_apu_init_lt_axi_m_wvalid,
  // AXI write response channel
  input  apu_axi_lt_s_b_t               i_apu_init_lt_axi_m_b,
  output logic                          o_apu_init_lt_axi_m_bready,
  input  logic                          i_apu_init_lt_axi_m_bvalid,
  // AXI read address channel
  output apu_axi_lt_s_ar_t              o_apu_init_lt_axi_m_ar,
  input  logic                          i_apu_init_lt_axi_m_arready,
  output logic                          o_apu_init_lt_axi_m_arvalid,
  // AXI read data/response channel
  input  apu_axi_lt_s_r_t               i_apu_init_lt_axi_m_r,
  output logic                          o_apu_init_lt_axi_m_rready,
  input  logic                          i_apu_init_lt_axi_m_rvalid,

  /// NoC AXI Connections LP Target Port
  // AXI write address channel
  input  apu_axi_lt_m_aw_t              i_apu_targ_lt_axi_s_aw,
  output logic                          o_apu_targ_lt_axi_s_awready,
  input  logic                          i_apu_targ_lt_axi_s_awvalid,
  // AXI write data channel
  input  apu_axi_lt_w_t                 i_apu_targ_lt_axi_s_w,
  output logic                          o_apu_targ_lt_axi_s_wready,
  input  logic                          i_apu_targ_lt_axi_s_wvalid,
  // AXI write response channel
  output apu_axi_lt_m_b_t               o_apu_targ_lt_axi_s_b,
  input  logic                          i_apu_targ_lt_axi_s_bready,
  output logic                          o_apu_targ_lt_axi_s_bvalid,
  // AXI read address channel
  input  apu_axi_lt_m_ar_t              i_apu_targ_lt_axi_s_ar,
  output logic                          o_apu_targ_lt_axi_s_arready,
  input  logic                          i_apu_targ_lt_axi_s_arvalid,
  // AXI read data/response channel
  output apu_axi_lt_m_r_t               o_apu_targ_lt_axi_s_r,
  input  logic                          i_apu_targ_lt_axi_s_rready,
  output logic                          o_apu_targ_lt_axi_s_rvalid,

  /// NoC Connections HP AXI Init Interface
  // AXI write address channel
  output apu_axi_mt_m_aw_t              o_apu_init_mt_axi_m_aw,
  input  logic                          i_apu_init_mt_axi_m_awready,
  output logic                          o_apu_init_mt_axi_m_awvalid,
  // AXI write data channel
  output apu_axi_mt_w_t                 o_apu_init_mt_axi_m_w,
  input  logic                          i_apu_init_mt_axi_m_wready,
  output logic                          o_apu_init_mt_axi_m_wvalid,
  // AXI write response channel
  input  apu_axi_mt_m_b_t               i_apu_init_mt_axi_m_b,
  output logic                          o_apu_init_mt_axi_m_bready,
  input  logic                          i_apu_init_mt_axi_m_bvalid,
  // AXI read address channel
  output apu_axi_mt_m_ar_t              o_apu_init_mt_axi_m_ar,
  input  logic                          i_apu_init_mt_axi_m_arready,
  output logic                          o_apu_init_mt_axi_m_arvalid,
  // AXI read data/response channel
  input  apu_axi_mt_m_r_t               i_apu_init_mt_axi_m_r,
  output logic                          o_apu_init_mt_axi_m_rready,
  input  logic                          i_apu_init_mt_axi_m_rvalid,

  // TODO - Placeholder signals for skeleton. To be reviewed and finalized in Bronze.

  // Disable init
  input logic [CORE_WIDTH - 1:0] i_cores_disable_init,
  input logic i_l2c_disable_init,

  /// CORES configuration
  input logic [CORE_WIDTH - 1:0][47:0] i_cores_reset_vector,

  /// SRAM impl signals
  input  axe_tcl_sram_pkg::impl_inp_t [CORE_WIDTH - 1:0] i_cores_ctrl,
  output axe_tcl_sram_pkg::impl_oup_t [CORE_WIDTH - 1:0] o_cores_ctrl,
  input  axe_tcl_sram_pkg::impl_inp_t i_l2c_ctrl,
  output axe_tcl_sram_pkg::impl_oup_t o_l2c_ctrl,
  input  axe_tcl_sram_pkg::impl_inp_t i_dma_ctrl,
  output axe_tcl_sram_pkg::impl_oup_t o_dma_ctrl,
  input  axe_tcl_sram_pkg::impl_inp_rom_t i_rom_ctrl,
  output axe_tcl_sram_pkg::impl_oup_rom_t o_rom_ctrl,

  // Token network
  output chip_pkg::chip_ocpl_token_addr_t o_tok_prod_ocpl_m_maddr,
  output chip_pkg::chip_ocpl_token_data_t o_tok_prod_ocpl_m_mdata,
  output logic                            o_tok_prod_ocpl_m_mcmd,
  input  logic                            i_tok_prod_ocpl_m_scmdaccept,
  input  chip_pkg::chip_ocpl_token_addr_t i_tok_cons_ocpl_s_maddr,
  input  chip_pkg::chip_ocpl_token_data_t i_tok_cons_ocpl_s_mdata,
  input  logic                            i_tok_cons_ocpl_s_mcmd,
  output logic                            o_tok_cons_ocpl_s_scmdaccept,

  // Fabric low Power control sigs
  input  logic                                   i_fabric_low_power_en,
  input  logic [APU_FABRIC_IDLE_DELAY_WIDTH-1:0] i_fabric_low_power_idle_delay,

  /// DFT reset override signals
  input  logic i_test_mode
);

  // AXI clk gating
  wire aclk_gated;
  logic [1:0] axi_qreq_n;
  logic [1:0] axi_qdeny;
  logic [1:0] axi_qaccept_n;
  logic [1:0] axi_qactive;

  apu_axi_power_management_unit #(
    .DEVICE_WIDTH(2),
    .IDLE_DELAY_WIDTH(APU_FABRIC_IDLE_DELAY_WIDTH)
  ) u_apu_axi_pmu (
    /// Fast bus clock
    .i_clk(i_aclk),
    .i_rst_n(i_arst_n),
    .o_clk(aclk_gated),
    /// DFT
    .i_test_en('0),
    /// CSR status
    .i_low_power_en(i_fabric_low_power_en),
    .i_low_power_idle_delay(i_fabric_low_power_idle_delay),
    /// Low Power Interface
    .o_devices_qreq_n(axi_qreq_n),
    .i_devices_qdeny(axi_qdeny),
    .i_devices_qaccept_n(axi_qaccept_n),
    .i_devices_qactive(axi_qactive)
  );

  // HART ID
  logic [CORE_WIDTH - 1:0][63:0] cores_hart_id;
  for (genvar i = 0; unsigned'(i) < CORE_WIDTH; i++) begin : g_cores_hart_id
    always_comb cores_hart_id[i] = i + APU_HART_ID_OFFSET;
  end

  // CORES misc
  logic [CORE_WIDTH - 1:0] cores_meip;
  logic [CORE_WIDTH - 1:0] cores_msip;
  logic [CORE_WIDTH - 1:0] cores_seip;
  logic [CORE_WIDTH - 1:0] cores_wfi_mode;

  // misc
  logic l2c_err_int;

  // AXI
  // LT Xbar
  apu_axi_lt_m_aw_t lt_axi_m_aw[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_awready[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_awvalid[APU_XBAR_LT_S_PORTS];
  apu_axi_lt_w_t lt_axi_m_w[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_wready[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_wvalid[APU_XBAR_LT_S_PORTS];
  apu_axi_lt_m_b_t lt_axi_m_b[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_bready[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_bvalid[APU_XBAR_LT_S_PORTS];
  apu_axi_lt_m_ar_t lt_axi_m_ar[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_arready[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_arvalid[APU_XBAR_LT_S_PORTS];
  apu_axi_lt_m_r_t lt_axi_m_r[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_rready[APU_XBAR_LT_S_PORTS];
  logic lt_axi_m_rvalid[APU_XBAR_LT_S_PORTS];

  apu_axi_isolate #(
    .AxiIdWidth(APU_AXI_LT_M_ID_W),
    .AxiDataWidth(chip_pkg::CHIP_AXI_LT_DATA_W),
    .MaxTxn(2**APU_AXI_LT_M_ID_W),
    .SupportAtops(APU_SUPPORT_ATOPS),
    .axi_aw_t(apu_axi_lt_m_aw_t),
    .axi_w_t(apu_axi_lt_w_t),
    .axi_b_t(apu_axi_lt_m_b_t),
    .axi_ar_t(apu_axi_lt_m_ar_t),
    .axi_r_t(apu_axi_lt_m_r_t)
  ) u_lt_axi_isolate_noc (
    /// Rising-edge clock of all ports
    .i_clk(i_aclk),
    /// Asynchronous reset, active low
    .i_rst_n(i_arst_n),

    /// Low Power Interface
    .i_qreq_n(axi_qreq_n[0]),
    .o_qdeny(axi_qdeny[0]),
    .o_qaccept_n(axi_qaccept_n[0]),
    .o_qactive(axi_qactive[0]),

    //////////////////////
    // Subordinate Port //
    //////////////////////
    .i_axi_s_aw(i_apu_targ_lt_axi_s_aw),
    .i_axi_s_aw_valid(i_apu_targ_lt_axi_s_awvalid),
    .o_axi_s_aw_ready(o_apu_targ_lt_axi_s_awready),
    .i_axi_s_w(i_apu_targ_lt_axi_s_w),
    .i_axi_s_w_valid(i_apu_targ_lt_axi_s_wvalid),
    .o_axi_s_w_ready(o_apu_targ_lt_axi_s_wready),
    .o_axi_s_b(o_apu_targ_lt_axi_s_b),
    .o_axi_s_b_valid(o_apu_targ_lt_axi_s_bvalid),
    .i_axi_s_b_ready(i_apu_targ_lt_axi_s_bready),
    .i_axi_s_ar(i_apu_targ_lt_axi_s_ar),
    .i_axi_s_ar_valid(i_apu_targ_lt_axi_s_arvalid),
    .o_axi_s_ar_ready(o_apu_targ_lt_axi_s_arready),
    .o_axi_s_r(o_apu_targ_lt_axi_s_r),
    .o_axi_s_r_valid(o_apu_targ_lt_axi_s_rvalid),
    .i_axi_s_r_ready(i_apu_targ_lt_axi_s_rready),

    //////////////////
    // Manager port //
    //////////////////
    .o_axi_m_aw(lt_axi_m_aw[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .o_axi_m_aw_valid(lt_axi_m_awvalid[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .i_axi_m_aw_ready(lt_axi_m_awready[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .o_axi_m_w(lt_axi_m_w[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .o_axi_m_w_valid(lt_axi_m_wvalid[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .i_axi_m_w_ready(lt_axi_m_wready[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .i_axi_m_b(lt_axi_m_b[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .i_axi_m_b_valid(lt_axi_m_bvalid[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .o_axi_m_b_ready(lt_axi_m_bready[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .o_axi_m_ar(lt_axi_m_ar[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .o_axi_m_ar_valid(lt_axi_m_arvalid[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .i_axi_m_ar_ready(lt_axi_m_arready[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .i_axi_m_r(lt_axi_m_r[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .i_axi_m_r_valid(lt_axi_m_rvalid[APU_XBAR_LT_S_PORT_IDX_EXT]),
    .o_axi_m_r_ready(lt_axi_m_rready[APU_XBAR_LT_S_PORT_IDX_EXT])
  );

  // Unused trace
  always_comb lt_axi_m_aw[APU_XBAR_LT_S_PORT_IDX_TRACE] = 'b0;
  always_comb lt_axi_m_awvalid[APU_XBAR_LT_S_PORT_IDX_TRACE] = 'b0;
  always_comb lt_axi_m_w[APU_XBAR_LT_S_PORT_IDX_TRACE] = 'b0;
  always_comb lt_axi_m_wvalid[APU_XBAR_LT_S_PORT_IDX_TRACE] = 'b0;
  always_comb lt_axi_m_bready[APU_XBAR_LT_S_PORT_IDX_TRACE] = 'b0;
  always_comb lt_axi_m_ar[APU_XBAR_LT_S_PORT_IDX_TRACE] = 'b0;
  always_comb lt_axi_m_arvalid[APU_XBAR_LT_S_PORT_IDX_TRACE] = 'b0;
  always_comb lt_axi_m_rready[APU_XBAR_LT_S_PORT_IDX_TRACE] = 'b0;

  apu_axi_lt_s_aw_t lt_axi_s_aw[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_awready[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_awvalid[APU_XBAR_LT_M_PORTS];
  apu_axi_lt_w_t lt_axi_s_w[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_wready[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_wvalid[APU_XBAR_LT_M_PORTS];
  apu_axi_lt_s_b_t lt_axi_s_b[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_bready[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_bvalid[APU_XBAR_LT_M_PORTS];
  apu_axi_lt_s_ar_t lt_axi_s_ar[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_arready[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_arvalid[APU_XBAR_LT_M_PORTS];
  apu_axi_lt_s_r_t lt_axi_s_r[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_rready[APU_XBAR_LT_M_PORTS];
  logic lt_axi_s_rvalid[APU_XBAR_LT_M_PORTS];

  apu_axi_lt_s_aw_t lt_atu_axi_s_aw[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_awready[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_awvalid[APU_XBAR_LT_M_PORTS];
  apu_axi_lt_w_t lt_atu_axi_s_w[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_wready[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_wvalid[APU_XBAR_LT_M_PORTS];
  apu_axi_lt_s_b_t lt_atu_axi_s_b[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_bready[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_bvalid[APU_XBAR_LT_M_PORTS];
  apu_axi_lt_s_ar_t lt_atu_axi_s_ar[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_arready[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_arvalid[APU_XBAR_LT_M_PORTS];
  apu_axi_lt_s_r_t lt_atu_axi_s_r[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_rready[APU_XBAR_LT_M_PORTS];
  logic lt_atu_axi_s_rvalid[APU_XBAR_LT_M_PORTS];

  always_comb o_apu_init_lt_axi_m_aw = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_EXT];
  always_comb lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_EXT] = i_apu_init_lt_axi_m_awready;
  always_comb o_apu_init_lt_axi_m_awvalid = lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_EXT];
  always_comb o_apu_init_lt_axi_m_w = lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_EXT];
  always_comb lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_EXT] = i_apu_init_lt_axi_m_wready;
  always_comb o_apu_init_lt_axi_m_wvalid = lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_EXT];
  always_comb lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_EXT] = i_apu_init_lt_axi_m_b;
  always_comb o_apu_init_lt_axi_m_bready = lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_EXT];
  always_comb lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_EXT] = i_apu_init_lt_axi_m_bvalid;
  always_comb o_apu_init_lt_axi_m_ar = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_EXT];
  always_comb lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_EXT] = i_apu_init_lt_axi_m_arready;
  always_comb o_apu_init_lt_axi_m_arvalid = lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_EXT];
  always_comb lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_EXT] = i_apu_init_lt_axi_m_r;
  always_comb o_apu_init_lt_axi_m_rready = lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_EXT];
  always_comb lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_EXT] = i_apu_init_lt_axi_m_rvalid;

  apu_xbar_lt_rule_t apu_xbar_lt_rules [APU_XBAR_LT_NB_ADDR_RULES];
  always_comb apu_xbar_lt_rules[0] = APU_XBAR_LT_RULE_BOOT;
  always_comb apu_xbar_lt_rules[1] = APU_XBAR_LT_RULE_CSRS;
  always_comb apu_xbar_lt_rules[2] = APU_XBAR_LT_RULE_DMA;
  always_comb apu_xbar_lt_rules[3] = APU_XBAR_LT_RULE_MAIL;
  always_comb apu_xbar_lt_rules[4] = APU_XBAR_LT_RULE_PLMT;
  always_comb apu_xbar_lt_rules[5] = APU_XBAR_LT_RULE_L2C_REGISTER;
  always_comb apu_xbar_lt_rules[6] = APU_XBAR_LT_RULE_PLIC;
  always_comb apu_xbar_lt_rules[7] = APU_XBAR_LT_RULE_SWPLIC;
  always_comb apu_xbar_lt_rules[8] = APU_XBAR_LT_RULE_TOKEN;
  always_comb apu_xbar_lt_rules[9] = APU_XBAR_LT_RULE_ERR;
  always_comb apu_xbar_lt_rules[10] = APU_XBAR_LT_RULE_EXT;

  logic default_m_port_en[APU_XBAR_LT_S_PORTS];
  logic [APU_XBAR_LT_M_PORT_IDX_W - 1:0] default_m_port[APU_XBAR_LT_S_PORTS];
  for (genvar i = 0; unsigned'(i) < APU_XBAR_LT_S_PORTS; i++) begin : g_xbar_default_port
    always_comb default_m_port_en[i] = '1;
    always_comb default_m_port[i] = APU_XBAR_LT_M_PORT_IDX_EXT;
  end

  axe_axi_xbar #(
    .NumSubPorts  (APU_XBAR_LT_S_PORTS),
    .NumManPorts  (APU_XBAR_LT_M_PORTS),
    .SubAxiIdWidth(APU_AXI_LT_M_ID_W),
    .UniqueIds    (1'b0),

    .AxiIdUsedWidth(APU_AXI_LT_S_ID_W - APU_AXI_LT_M_ID_W),
    .AxiAddrWidth  (chip_pkg::CHIP_AXI_ADDR_W),
    .NumAddrRules  (APU_XBAR_LT_NB_ADDR_RULES),
    .SupportAtops  (APU_SUPPORT_ATOPS),
    .Connectivity  (APU_XBAR_LT_CONNECTIVITY),

    .addr_rule_t(apu_xbar_lt_rule_t),
    .axi_s_aw_t (apu_axi_lt_m_aw_t),
    .axi_m_aw_t (apu_axi_lt_s_aw_t),
    .axi_w_t    (apu_axi_lt_w_t),
    .axi_s_b_t  (apu_axi_lt_m_b_t),
    .axi_m_b_t  (apu_axi_lt_s_b_t),
    .axi_s_ar_t (apu_axi_lt_m_ar_t),
    .axi_m_ar_t (apu_axi_lt_s_ar_t),
    .axi_s_r_t  (apu_axi_lt_m_r_t),
    .axi_m_r_t  (apu_axi_lt_s_r_t)
  ) u_lt_xbar (
    .i_clk(aclk_gated),
    .i_rst_n(i_arst_n),

    // Subordinate Port
    .i_axi_s_aw      (lt_axi_m_aw),
    .i_axi_s_aw_valid(lt_axi_m_awvalid),
    .o_axi_s_aw_ready(lt_axi_m_awready),
    .i_axi_s_w       (lt_axi_m_w),
    .i_axi_s_w_valid (lt_axi_m_wvalid),
    .o_axi_s_w_ready (lt_axi_m_wready),
    .o_axi_s_b       (lt_axi_m_b),
    .o_axi_s_b_valid (lt_axi_m_bvalid),
    .i_axi_s_b_ready (lt_axi_m_bready),
    .i_axi_s_ar      (lt_axi_m_ar),
    .i_axi_s_ar_valid(lt_axi_m_arvalid),
    .o_axi_s_ar_ready(lt_axi_m_arready),
    .o_axi_s_r       (lt_axi_m_r),
    .o_axi_s_r_valid (lt_axi_m_rvalid),
    .i_axi_s_r_ready (lt_axi_m_rready),

    // Manager Port
    .o_axi_m_aw      (lt_atu_axi_s_aw),
    .o_axi_m_aw_valid(lt_atu_axi_s_awvalid),
    .i_axi_m_aw_ready(lt_atu_axi_s_awready),
    .o_axi_m_w       (lt_atu_axi_s_w),
    .o_axi_m_w_valid (lt_atu_axi_s_wvalid),
    .i_axi_m_w_ready (lt_atu_axi_s_wready),
    .i_axi_m_b       (lt_atu_axi_s_b),
    .i_axi_m_b_valid (lt_atu_axi_s_bvalid),
    .o_axi_m_b_ready (lt_atu_axi_s_bready),
    .o_axi_m_ar      (lt_atu_axi_s_ar),
    .o_axi_m_ar_valid(lt_atu_axi_s_arvalid),
    .i_axi_m_ar_ready(lt_atu_axi_s_arready),
    .i_axi_m_r       (lt_atu_axi_s_r),
    .i_axi_m_r_valid (lt_atu_axi_s_rvalid),
    .o_axi_m_r_ready (lt_atu_axi_s_rready),

    /// The address map, replicated on all subordinate ports
    .i_addr_map(apu_xbar_lt_rules),
    /// Enable default routing on decode errors
    .i_default_m_port_en(default_m_port_en),
    /// Default routing mapping per subordinate port
    .i_default_m_port(default_m_port)
  );

  // LT ATUs
  apu_atu_entry_t apu_atu_entries [APU_XBAR_LT_M_PORTS][APU_ATU_MAX_NUM_ENTRIES];
  always_comb apu_atu_entries[1][0] = APU_ATU_ENTRY_BOOT;
  always_comb apu_atu_entries[2][0] = APU_ATU_ENTRY_CSRS;
  always_comb apu_atu_entries[3][0] = APU_ATU_ENTRY_DMA;
  always_comb apu_atu_entries[4][0] = APU_ATU_ENTRY_MAIL;
  always_comb apu_atu_entries[5][0] = APU_ATU_ENTRY_PLIC;
  always_comb apu_atu_entries[6][0] = APU_ATU_ENTRY_SWPLIC;
  always_comb apu_atu_entries[7][0] = APU_ATU_ENTRY_TOKEN;
  always_comb apu_atu_entries[8][0] = APU_ATU_ENTRY_SWPLIC;

  for (genvar i = 0; unsigned'(i) < APU_XBAR_LT_M_PORTS; i++) begin: g_atu
    if (APU_ATU_NUM_ENTRIES[i] == 0) begin: g_bypass
      always_comb lt_axi_s_ar[i] = lt_atu_axi_s_ar[i];
      always_comb lt_atu_axi_s_arready[i] = lt_axi_s_arready[i];
      always_comb lt_axi_s_arvalid[i] = lt_atu_axi_s_arvalid[i];
      always_comb lt_axi_s_aw[i] = lt_atu_axi_s_aw[i];
      always_comb lt_atu_axi_s_awready[i] = lt_axi_s_awready[i];
      always_comb lt_axi_s_awvalid[i] = lt_atu_axi_s_awvalid[i];
      always_comb lt_atu_axi_s_b[i] = lt_axi_s_b[i];
      always_comb lt_axi_s_bready[i] = lt_atu_axi_s_bready[i];
      always_comb lt_atu_axi_s_bvalid[i] = lt_axi_s_bvalid[i];
      always_comb lt_atu_axi_s_r[i] = lt_axi_s_r[i];
      always_comb lt_axi_s_rready[i] = lt_atu_axi_s_rready[i];
      always_comb lt_atu_axi_s_rvalid[i] = lt_axi_s_rvalid[i];
      always_comb lt_axi_s_w[i] = lt_atu_axi_s_w[i];
      always_comb lt_atu_axi_s_wready[i] = lt_axi_s_wready[i];
      always_comb lt_axi_s_wvalid[i] = lt_atu_axi_s_wvalid[i];
    end
    else begin: g_real_atu
      axe_axi_atu #(
        .AxiIdWidth(APU_AXI_LT_S_ID_W),
        .AxiSubPortAddrWidth(chip_pkg::CHIP_AXI_ADDR_W),
        .AxiManPortAddrWidth(chip_pkg::CHIP_AXI_ADDR_W),
        .AxiSubPortMaxTxns(4),
        .SupportAtops(APU_SUPPORT_ATOPS),
        .L1PageOffsetSize(APU_ATU_PAGE_OFFSET_W),
        .L1NumEntries(APU_ATU_NUM_ENTRIES[i]),
        .axi_s_aw_t  (apu_axi_lt_s_aw_t),
        .axi_m_aw_t  (apu_axi_lt_s_aw_t),
        .axi_w_t     (apu_axi_lt_w_t),
        .axi_b_t     (apu_axi_lt_s_b_t),
        .axi_s_ar_t  (apu_axi_lt_s_ar_t),
        .axi_m_ar_t  (apu_axi_lt_s_ar_t),
        .axi_r_t     (apu_axi_lt_s_r_t),
        .entry_t     (apu_atu_entry_t)
      ) u_atu (
        .i_clk(aclk_gated),
        .i_rst_n(i_arst_n),

        .i_axi_s_aw      (lt_atu_axi_s_aw[i]),
        .i_axi_s_aw_valid(lt_atu_axi_s_awvalid[i]),
        .o_axi_s_aw_ready(lt_atu_axi_s_awready[i]),
        .i_axi_s_w       (lt_atu_axi_s_w[i]),
        .i_axi_s_w_valid (lt_atu_axi_s_wvalid[i]),
        .o_axi_s_w_ready (lt_atu_axi_s_wready[i]),
        .o_axi_s_b       (lt_atu_axi_s_b[i]),
        .o_axi_s_b_valid (lt_atu_axi_s_bvalid[i]),
        .i_axi_s_b_ready (lt_atu_axi_s_bready[i]),
        .i_axi_s_ar      (lt_atu_axi_s_ar[i]),
        .i_axi_s_ar_valid(lt_atu_axi_s_arvalid[i]),
        .o_axi_s_ar_ready(lt_atu_axi_s_arready[i]),
        .o_axi_s_r       (lt_atu_axi_s_r[i]),
        .o_axi_s_r_valid (lt_atu_axi_s_rvalid[i]),
        .i_axi_s_r_ready (lt_atu_axi_s_rready[i]),

        .o_axi_m_aw      (lt_axi_s_aw[i]),
        .o_axi_m_aw_valid(lt_axi_s_awvalid[i]),
        .i_axi_m_aw_ready(lt_axi_s_awready[i]),
        .o_axi_m_w       (lt_axi_s_w[i]),
        .o_axi_m_w_valid (lt_axi_s_wvalid[i]),
        .i_axi_m_w_ready (lt_axi_s_wready[i]),
        .i_axi_m_b       (lt_axi_s_b[i]),
        .i_axi_m_b_valid (lt_axi_s_bvalid[i]),
        .o_axi_m_b_ready (lt_axi_s_bready[i]),
        .o_axi_m_ar      (lt_axi_s_ar[i]),
        .o_axi_m_ar_valid(lt_axi_s_arvalid[i]),
        .i_axi_m_ar_ready(lt_axi_s_arready[i]),
        .i_axi_m_r       (lt_axi_s_r[i]),
        .i_axi_m_r_valid (lt_axi_s_rvalid[i]),
        .o_axi_m_r_ready (lt_axi_s_rready[i]),

        .i_entries(apu_atu_entries[i]),
        .i_bypass(1'b0)
      );
    end
  end

  // LT sub
  ax65_axi_lt_s_aw_t iocp_axi_s_aw;
  logic iocp_axi_s_awready;
  logic iocp_axi_s_awvalid;
  ax65_axi_lt_w_t iocp_axi_s_w;
  logic iocp_axi_s_wready;
  logic iocp_axi_s_wvalid;
  ax65_axi_lt_s_b_t iocp_axi_s_b;
  logic iocp_axi_s_bready;
  logic iocp_axi_s_bvalid;
  ax65_axi_lt_s_ar_t iocp_axi_s_ar;
  logic iocp_axi_s_arready;
  logic iocp_axi_s_arvalid;
  ax65_axi_lt_s_r_t iocp_axi_s_r;
  logic iocp_axi_s_rready;
  logic iocp_axi_s_rvalid;

  apu_axi_lt_s_aw_t iocp_prepend_axi_s_aw;
  logic iocp_prepend_axi_s_awready;
  logic iocp_prepend_axi_s_awvalid;
  ax65_axi_lt_w_t iocp_prepend_axi_s_w;
  logic iocp_prepend_axi_s_wready;
  logic iocp_prepend_axi_s_wvalid;
  apu_axi_lt_s_b_t iocp_prepend_axi_s_b;
  logic iocp_prepend_axi_s_bready;
  logic iocp_prepend_axi_s_bvalid;
  apu_axi_lt_s_ar_t iocp_prepend_axi_s_ar;
  logic iocp_prepend_axi_s_arready;
  logic iocp_prepend_axi_s_arvalid;
  apu_ax65_axi_lt_s_r_t iocp_prepend_axi_s_r;
  logic iocp_prepend_axi_s_rready;
  logic iocp_prepend_axi_s_rvalid;

  axe_axi_id_prepend #(
    .IdWidthDifference(AX65_AXI_LT_S_ID_W - APU_AXI_LT_S_ID_W),

    .axi_s_aw_t(apu_axi_lt_s_aw_t),
    .axi_s_w_t (ax65_axi_lt_w_t),
    .axi_s_b_t (apu_axi_lt_s_b_t),
    .axi_s_ar_t(apu_axi_lt_s_ar_t),
    .axi_s_r_t (apu_ax65_axi_lt_s_r_t),
    .axi_m_aw_t(ax65_axi_lt_s_aw_t),
    .axi_m_w_t (ax65_axi_lt_w_t),
    .axi_m_b_t (ax65_axi_lt_s_b_t),
    .axi_m_ar_t(ax65_axi_lt_s_ar_t),
    .axi_m_r_t (ax65_axi_lt_s_r_t)
  ) u_iocp_id_prepend (
    // Subordinate Port
    .i_axi_s_aw(iocp_prepend_axi_s_aw),
    .i_axi_s_aw_valid(iocp_prepend_axi_s_awvalid),
    .o_axi_s_aw_ready(iocp_prepend_axi_s_awready),
    .i_axi_s_w(iocp_prepend_axi_s_w),
    .i_axi_s_w_valid(iocp_prepend_axi_s_wvalid),
    .o_axi_s_w_ready(iocp_prepend_axi_s_wready),
    .o_axi_s_b(iocp_prepend_axi_s_b),
    .o_axi_s_b_valid(iocp_prepend_axi_s_bvalid),
    .i_axi_s_b_ready(iocp_prepend_axi_s_bready),
    .i_axi_s_ar(iocp_prepend_axi_s_ar),
    .i_axi_s_ar_valid(iocp_prepend_axi_s_arvalid),
    .o_axi_s_ar_ready(iocp_prepend_axi_s_arready),
    .o_axi_s_r(iocp_prepend_axi_s_r),
    .o_axi_s_r_valid(iocp_prepend_axi_s_rvalid),
    .i_axi_s_r_ready(iocp_prepend_axi_s_rready),

    // Manager port
    .o_axi_m_aw(iocp_axi_s_aw),
    .o_axi_m_aw_valid(iocp_axi_s_awvalid),
    .i_axi_m_aw_ready(iocp_axi_s_awready),
    .o_axi_m_w(iocp_axi_s_w),
    .o_axi_m_w_valid(iocp_axi_s_wvalid),
    .i_axi_m_w_ready(iocp_axi_s_wready),
    .i_axi_m_b(iocp_axi_s_b),
    .i_axi_m_b_valid(iocp_axi_s_bvalid),
    .o_axi_m_b_ready(iocp_axi_s_bready),
    .o_axi_m_ar(iocp_axi_s_ar),
    .o_axi_m_ar_valid(iocp_axi_s_arvalid),
    .i_axi_m_ar_ready(iocp_axi_s_arready),
    .i_axi_m_r(iocp_axi_s_r),
    .i_axi_m_r_valid(iocp_axi_s_rvalid),
    .o_axi_m_r_ready(iocp_axi_s_rready)
  );

  axe_axi_dw_upsizer #(
    .AxiIdWidth         (APU_AXI_LT_S_ID_W),
    .AxiAddrWidth       (chip_pkg::CHIP_AXI_ADDR_W),
    .AxiSubPortDataWidth(chip_pkg::CHIP_AXI_LT_DATA_W),
    .AxiManPortDataWidth(AX65_AXI_LT_DATA_W),

    .axi_aw_t (apu_axi_lt_s_aw_t),
    .axi_s_w_t(apu_axi_lt_w_t),
    .axi_m_w_t(ax65_axi_lt_w_t),
    .axi_b_t  (apu_axi_lt_s_b_t),
    .axi_ar_t (apu_axi_lt_s_ar_t),
    .axi_s_r_t(apu_axi_lt_s_r_t),
    .axi_m_r_t(apu_ax65_axi_lt_s_r_t)
  ) u_iocp_upsizer (
    /// Clock, positive edge triggered
    .i_clk(aclk_gated),
    /// Asynchronous reset, active low
    .i_rst_n(i_arst_n),

    // Subordinate Port
    .i_axi_s_aw(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .i_axi_s_aw_valid(lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .o_axi_s_aw_ready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .i_axi_s_w(lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .i_axi_s_w_valid(lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .o_axi_s_w_ready(lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .o_axi_s_b(lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .o_axi_s_b_valid(lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .i_axi_s_b_ready(lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .i_axi_s_ar(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .i_axi_s_ar_valid(lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .o_axi_s_ar_ready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .o_axi_s_r(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .o_axi_s_r_valid(lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_AX65]),
    .i_axi_s_r_ready(lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_AX65]),

    // Manager port
    .o_axi_m_aw(iocp_prepend_axi_s_aw),
    .o_axi_m_aw_valid(iocp_prepend_axi_s_awvalid),
    .i_axi_m_aw_ready(iocp_prepend_axi_s_awready),
    .o_axi_m_w(iocp_prepend_axi_s_w),
    .o_axi_m_w_valid(iocp_prepend_axi_s_wvalid),
    .i_axi_m_w_ready(iocp_prepend_axi_s_wready),
    .i_axi_m_b(iocp_prepend_axi_s_b),
    .i_axi_m_b_valid(iocp_prepend_axi_s_bvalid),
    .o_axi_m_b_ready(iocp_prepend_axi_s_bready),
    .o_axi_m_ar(iocp_prepend_axi_s_ar),
    .o_axi_m_ar_valid(iocp_prepend_axi_s_arvalid),
    .i_axi_m_ar_ready(iocp_prepend_axi_s_arready),
    .i_axi_m_r(iocp_prepend_axi_s_r),
    .i_axi_m_r_valid(iocp_prepend_axi_s_rvalid),
    .o_axi_m_r_ready(iocp_prepend_axi_s_rready)
  );

  // MT manager
  ax65_axi_mt_m_aw_t mem_dma_axi_m_aw[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_awready[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_awvalid[APU_MUX_MT_NB_PORTS];
  apu_axi_mt_w_t mem_dma_axi_m_w[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_wready[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_wvalid[APU_MUX_MT_NB_PORTS];
  ax65_axi_mt_m_b_t mem_dma_axi_m_b[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_bready[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_bvalid[APU_MUX_MT_NB_PORTS];
  ax65_axi_mt_m_ar_t mem_dma_axi_m_ar[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_arready[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_arvalid[APU_MUX_MT_NB_PORTS];
  ax65_axi_mt_m_r_t mem_dma_axi_m_r[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_rready[APU_MUX_MT_NB_PORTS];
  logic mem_dma_axi_m_rvalid[APU_MUX_MT_NB_PORTS];

  apu_axi_mt_m_aw_t mt_axi_m_aw;
  logic mt_axi_m_awready;
  logic mt_axi_m_awvalid;
  apu_axi_mt_w_t mt_axi_m_w;
  logic mt_axi_m_wready;
  logic mt_axi_m_wvalid;
  apu_axi_mt_m_b_t mt_axi_m_b;
  logic mt_axi_m_bready;
  logic mt_axi_m_bvalid;
  apu_axi_mt_m_ar_t mt_axi_m_ar;
  logic mt_axi_m_arready;
  logic mt_axi_m_arvalid;
  apu_axi_mt_m_r_t mt_axi_m_r;
  logic mt_axi_m_rready;
  logic mt_axi_m_rvalid;

  always_comb o_apu_init_mt_axi_m_aw = mt_axi_m_aw;
  always_comb mt_axi_m_awready = i_apu_init_mt_axi_m_awready;
  always_comb o_apu_init_mt_axi_m_awvalid = mt_axi_m_awvalid;
  always_comb o_apu_init_mt_axi_m_w = mt_axi_m_w;
  always_comb mt_axi_m_wready = i_apu_init_mt_axi_m_wready;
  always_comb o_apu_init_mt_axi_m_wvalid = mt_axi_m_wvalid;
  always_comb mt_axi_m_b = i_apu_init_mt_axi_m_b;
  always_comb o_apu_init_mt_axi_m_bready = mt_axi_m_bready;
  always_comb mt_axi_m_bvalid = i_apu_init_mt_axi_m_bvalid;
  always_comb o_apu_init_mt_axi_m_ar = mt_axi_m_ar;
  always_comb mt_axi_m_arready = i_apu_init_mt_axi_m_arready;
  always_comb o_apu_init_mt_axi_m_arvalid = mt_axi_m_arvalid;
  always_comb mt_axi_m_r = i_apu_init_mt_axi_m_r;
  always_comb o_apu_init_mt_axi_m_rready = mt_axi_m_rready;
  always_comb mt_axi_m_rvalid = i_apu_init_mt_axi_m_rvalid;

  logic dma_channel1_irq;
  logic dma_channel2_irq;
  logic dma_common_irq;

  // DMA
  snps_dma_axe_axi #(
    .DMA_VERSION("apu"),

    .AXI_S_ADDR_W(chip_pkg::CHIP_AXI_ADDR_W),
    .AXI_S_DATA_W(chip_pkg::CHIP_AXI_LT_DATA_W),
    .AXI_S_ID_W(APU_AXI_LT_S_ID_W),
    .AXI_S_LEN_W(axi_pkg::AXI_LEN_WIDTH),

    // AXI channels for sub port
    .axi_s_aw_t(apu_axi_lt_s_aw_t),
    .axi_s_w_t (apu_axi_lt_w_t),
    .axi_s_b_t (apu_axi_lt_s_b_t),
    .axi_s_ar_t(apu_axi_lt_s_ar_t),
    .axi_s_r_t (apu_axi_lt_s_r_t),

    // AXI channels for manager port(s)
    .axi_m_aw_t(ax65_axi_mt_m_aw_t),
    .axi_m_w_t (apu_axi_mt_w_t),
    .axi_m_b_t (ax65_axi_mt_m_b_t),
    .axi_m_ar_t(ax65_axi_mt_m_ar_t),
    .axi_m_r_t (ax65_axi_mt_m_r_t)
  ) u_dma_mt (
    // Clock and reset signals
    .i_clk(i_aclk),
    .i_rst_n(i_arst_n),
    .i_test_mode(i_test_mode),

    // Subordinate Port
    .i_axi_s_aw(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .i_axi_s_aw_valid(lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .o_axi_s_aw_ready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .i_axi_s_w(lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .i_axi_s_w_valid(lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .o_axi_s_w_ready(lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .o_axi_s_b(lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .o_axi_s_b_valid(lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .i_axi_s_b_ready(lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .i_axi_s_ar(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .i_axi_s_ar_valid(lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .o_axi_s_ar_ready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .o_axi_s_r(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .o_axi_s_r_valid(lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_DMA]),
    .i_axi_s_r_ready(lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_DMA]),

    // Manager Port(s)
    .o_axi_m_aw(mem_dma_axi_m_aw[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .o_axi_m_aw_valid(mem_dma_axi_m_awvalid[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .i_axi_m_aw_ready(mem_dma_axi_m_awready[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .o_axi_m_w(mem_dma_axi_m_w[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .o_axi_m_w_valid(mem_dma_axi_m_wvalid[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .i_axi_m_w_ready(mem_dma_axi_m_wready[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .i_axi_m_b(mem_dma_axi_m_b[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .i_axi_m_b_valid(mem_dma_axi_m_bvalid[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .o_axi_m_b_ready(mem_dma_axi_m_bready[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .o_axi_m_ar(mem_dma_axi_m_ar[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .o_axi_m_ar_valid(mem_dma_axi_m_arvalid[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .i_axi_m_ar_ready(mem_dma_axi_m_arready[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .i_axi_m_r(mem_dma_axi_m_r[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .i_axi_m_r_valid(mem_dma_axi_m_rvalid[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),
    .o_axi_m_r_ready(mem_dma_axi_m_rready[APU_MUX_MT_PORT_IDX_DMA:APU_MUX_MT_PORT_IDX_DMA]),

    // Interrupts
    .o_irq_ch({dma_channel2_irq, dma_channel1_irq}),
    .o_irq_cmn(dma_common_irq),

     // SRAM config registers
    .i_impl_inp(i_dma_ctrl),
    .o_impl_oup(o_dma_ctrl),

    // Debug signals
    .i_debug_ch_num('0), // TODO(@vincent.morillon) to connect?
    .o_dma_debug()
  );

  axe_axi_mux #(
    .NumPorts(APU_MUX_MT_NB_PORTS),
    .SubAxiIdWidth(AX65_AXI_MT_M_ID_W),

    .axi_s_aw_t(ax65_axi_mt_m_aw_t),
    .axi_m_aw_t(apu_axi_mt_m_aw_t),
    .axi_w_t   (apu_axi_mt_w_t),
    .axi_s_b_t (ax65_axi_mt_m_b_t),
    .axi_m_b_t (apu_axi_mt_m_b_t),
    .axi_s_ar_t(ax65_axi_mt_m_ar_t),
    .axi_m_ar_t(apu_axi_mt_m_ar_t),
    .axi_s_r_t (ax65_axi_mt_m_r_t),
    .axi_m_r_t (apu_axi_mt_m_r_t)
  ) u_mem_dma_mux (
    /// Clock, positive edge triggered
    .i_clk(i_aclk),
    /// Aysnchronous reset, active low.
    .i_rst_n(i_arst_n),

    // Subordinate Ports
    .i_axi_s_aw(mem_dma_axi_m_aw),
    .i_axi_s_aw_valid(mem_dma_axi_m_awvalid),
    .o_axi_s_aw_ready(mem_dma_axi_m_awready),
    .i_axi_s_w(mem_dma_axi_m_w),
    .i_axi_s_w_valid(mem_dma_axi_m_wvalid),
    .o_axi_s_w_ready(mem_dma_axi_m_wready),
    .o_axi_s_b(mem_dma_axi_m_b),
    .o_axi_s_b_valid(mem_dma_axi_m_bvalid),
    .i_axi_s_b_ready(mem_dma_axi_m_bready),
    .i_axi_s_ar(mem_dma_axi_m_ar),
    .i_axi_s_ar_valid(mem_dma_axi_m_arvalid),
    .o_axi_s_ar_ready(mem_dma_axi_m_arready),
    .o_axi_s_r(mem_dma_axi_m_r),
    .o_axi_s_r_valid(mem_dma_axi_m_rvalid),
    .i_axi_s_r_ready(mem_dma_axi_m_rready),

    // Manager Port
    .o_axi_m_aw(mt_axi_m_aw),
    .o_axi_m_aw_valid(mt_axi_m_awvalid),
    .i_axi_m_aw_ready(mt_axi_m_awready),
    .o_axi_m_w(mt_axi_m_w),
    .o_axi_m_w_valid(mt_axi_m_wvalid),
    .i_axi_m_w_ready(mt_axi_m_wready),
    .i_axi_m_b(mt_axi_m_b),
    .i_axi_m_b_valid(mt_axi_m_bvalid),
    .o_axi_m_b_ready(mt_axi_m_bready),
    .o_axi_m_ar(mt_axi_m_ar),
    .o_axi_m_ar_valid(mt_axi_m_arvalid),
    .i_axi_m_ar_ready(mt_axi_m_arready),
    .i_axi_m_r(mt_axi_m_r),
    .i_axi_m_r_valid(mt_axi_m_rvalid),
    .o_axi_m_r_ready(mt_axi_m_rready)
  );

  // BootROM
  apu_bootrom #(
    /// AXI ID width
    .AxiIdWidth  (APU_AXI_LT_S_ID_W),
    /// AXI Address width
    .AxiAddrWidth(chip_pkg::CHIP_AXI_ADDR_W),
    /// The number of parallel outstanding reads the boot ROM can do at a given time.
    .AxiMaxReads (4),
    .axi_aw_t    (apu_axi_lt_s_aw_t),
    .axi_w_t     (apu_axi_lt_w_t),
    .axi_b_t     (apu_axi_lt_s_b_t),
    .axi_ar_t    (apu_axi_lt_s_ar_t),
    .axi_r_t     (apu_axi_lt_s_r_t),

    .ImplKey("HD_LVT"),
    .impl_inp_t(axe_tcl_sram_pkg::impl_inp_rom_t),
    .impl_oup_t(axe_tcl_sram_pkg::impl_oup_rom_t)
  ) u_bootrom (
    .i_clk(aclk_gated),
    .i_free_run_clk(i_free_run_aclk),
    .i_rst_n(i_arst_n),

    .i_axi_s_aw      (lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .i_axi_s_aw_valid(lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .o_axi_s_aw_ready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .i_axi_s_w       (lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .i_axi_s_w_valid (lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .o_axi_s_w_ready (lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .o_axi_s_b       (lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .o_axi_s_b_valid (lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .i_axi_s_b_ready (lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .i_axi_s_ar      (lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .i_axi_s_ar_valid(lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .o_axi_s_ar_ready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .o_axi_s_r       (lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .o_axi_s_r_valid (lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_BOOT]),
    .i_axi_s_r_ready (lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_BOOT]),

    .i_impl(i_rom_ctrl),
    .o_impl(o_rom_ctrl)
  );

  // CSR
  // TODO (@vincent.morillon) move to real CSR
  axe_axi_err_sub #(
    .AxiIdWidth  (APU_AXI_LT_S_ID_W),
    .Resp        (axi_pkg::RespDecErr),
    // litt "!CSR...." as ASCII
    .ReadData    (64'h214353522E2E2E2E),
    .MaxTxn      (4), // Minimize ressource consumption
    .SupportAtops(APU_SUPPORT_ATOPS),
    .axi_aw_t    (apu_axi_lt_s_aw_t),
    .axi_w_t     (apu_axi_lt_w_t),
    .axi_b_t     (apu_axi_lt_s_b_t),
    .axi_ar_t    (apu_axi_lt_s_ar_t),
    .axi_r_t     (apu_axi_lt_s_r_t)
  ) u_csr (
    .i_clk(aclk_gated),
    .i_rst_n(i_arst_n),

    .i_axi_s_aw      (lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .i_axi_s_aw_valid(lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .o_axi_s_aw_ready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .i_axi_s_w       (lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .i_axi_s_w_valid (lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .o_axi_s_w_ready (lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .o_axi_s_b       (lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .o_axi_s_b_valid (lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .i_axi_s_b_ready (lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .i_axi_s_ar      (lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .i_axi_s_ar_valid(lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .o_axi_s_ar_ready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .o_axi_s_r       (lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .o_axi_s_r_valid (lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_CSRS]),
    .i_axi_s_r_ready (lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_CSRS])
  );

  // Mailbox
  axi_mailbox_csr_reg_pkg::axi_a_ch_h2d_t axi_lt_mailbox_aw;
  axi_mailbox_csr_reg_pkg::axi_w_ch_h2d_t axi_lt_mailbox_w;
  axi_mailbox_csr_reg_pkg::axi_b_ch_d2h_t axi_lt_mailbox_b;
  axi_mailbox_csr_reg_pkg::axi_a_ch_h2d_t axi_lt_mailbox_ar;
  axi_mailbox_csr_reg_pkg::axi_r_ch_d2h_t axi_lt_mailbox_r;

  always_comb axi_lt_mailbox_aw.id    = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_MAIL].id;
  always_comb axi_lt_mailbox_aw.addr  = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_MAIL].addr;
  always_comb axi_lt_mailbox_aw.len   = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_MAIL].len;
  always_comb axi_lt_mailbox_aw.size  = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_MAIL].size;
  always_comb axi_lt_mailbox_aw.burst = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_MAIL].burst;
  always_comb axi_lt_mailbox_aw.valid = lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_MAIL];

  always_comb axi_lt_mailbox_w.data  = lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_MAIL].data;
  always_comb axi_lt_mailbox_w.strb  = lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_MAIL].strb;
  always_comb axi_lt_mailbox_w.last  = lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_MAIL].last;
  always_comb axi_lt_mailbox_w.valid = lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_MAIL];

  always_comb lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_MAIL].id   = axi_lt_mailbox_b.id;
  always_comb lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_MAIL].resp = axi_pkg::axi_resp_e'(axi_lt_mailbox_b.resp);
  always_comb lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_MAIL].user = 'b0;
  always_comb lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_MAIL] = axi_lt_mailbox_b.valid;

  always_comb axi_lt_mailbox_ar.id    = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_MAIL].id;
  always_comb axi_lt_mailbox_ar.addr  = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_MAIL].addr;
  always_comb axi_lt_mailbox_ar.len   = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_MAIL].len;
  always_comb axi_lt_mailbox_ar.size  = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_MAIL].size;
  always_comb axi_lt_mailbox_ar.burst = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_MAIL].burst;
  always_comb axi_lt_mailbox_ar.valid = lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_MAIL];

  always_comb lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_MAIL].id   = axi_lt_mailbox_r.id;
  always_comb lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_MAIL].data = axi_lt_mailbox_r.data;
  always_comb lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_MAIL].resp = axi_pkg::axi_resp_e'(axi_lt_mailbox_r.resp);
  always_comb lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_MAIL].last = axi_lt_mailbox_r.last;
  always_comb lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_MAIL].user = 'b0;
  always_comb lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_MAIL] = axi_lt_mailbox_r.valid;

  logic mailbox_irq;

  axi_mailbox #(
    .MailboxDepth(APU_MAILBOX_DEPTH)
  ) u_axi_mailbox (
    .i_clk(aclk_gated),
    .i_rst_n(i_arst_n),
    .i_axi_s_aw      (axi_lt_mailbox_aw),
    .o_axi_s_aw_ready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_MAIL]),
    .i_axi_s_w       (axi_lt_mailbox_w),
    .o_axi_s_w_ready (lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_MAIL]),
    .o_axi_s_b       (axi_lt_mailbox_b),
    .i_axi_s_b_ready (lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_MAIL]),
    .i_axi_s_ar      (axi_lt_mailbox_ar),
    .o_axi_s_ar_ready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_MAIL]),
    .o_axi_s_r       (axi_lt_mailbox_r),
    .i_axi_s_r_ready (lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_MAIL]),

    .o_irq           (mailbox_irq)
  );

  // PLICs
  logic token_manager_irq;
  apu_all_irqs_t all_irqs;

  apu_interrupt_connectivity_internal u_apu_irqs_connect_int (
    .i_irq__apu__l2c_err(l2c_err_int),
    .i_irq__apu__dma_channel_1(dma_channel1_irq),
    .i_irq__apu__dma_channel_2(dma_channel2_irq),
    .i_irq__apu__dma_common(dma_common_irq),
    .i_irq__apu__mailbox(mailbox_irq),
    .i_irq__apu__token_manager(token_manager_irq),
    .i_external_irqs,
    .o_all_irqs(all_irqs)
  );

  nds_plic_wrapper #(
    .INTERRUPT_WIDTH(APU_INTERRUPT_WIDTH),
    .TARGET_WIDTH(CORE_WIDTH*2),
    .MAX_PRIORITY(APU_INTERRUPT_MAX_PRIORITY),
    .EDGE_TRIGGER(APU_IRQS_EDGE_TRIGGER),
    .ASYNC_INTERRUPT(APU_IRQS_ASYNC),
    .PROGRAMMABLE_TRIGGER(0),
    .AXI_DATA_WIDTH(chip_pkg::CHIP_AXI_LT_DATA_W),
    .AXI_ADDR_WIDTH(chip_pkg::CHIP_AXI_ADDR_W),
    .AXI_ID_WIDTH(APU_AXI_LT_S_ID_W)
  ) u_plic (
    .i_clk(i_aclk),
    .i_rst_n(i_arst_n),

    .i_interrupt_src(all_irqs),
    .o_targets_eip({cores_seip, cores_meip}),

    .i_axi_s_araddr(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_PLIC].addr),
    .i_axi_s_arburst(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_PLIC].burst),
    .i_axi_s_arcache(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_PLIC].cache),
    .i_axi_s_arid(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_PLIC].id),
    .i_axi_s_arlen(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_PLIC].len),
    .i_axi_s_arlock(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_PLIC].lock),
    .i_axi_s_arprot(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_PLIC].prot),
    .i_axi_s_arsize(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_PLIC].size),
    .o_axi_s_arready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_PLIC]),
    .i_axi_s_arvalid(lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_PLIC]),
    .i_axi_s_awaddr(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_PLIC].addr),
    .i_axi_s_awburst(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_PLIC].burst),
    .i_axi_s_awcache(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_PLIC].cache),
    .i_axi_s_awid(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_PLIC].id),
    .i_axi_s_awlen(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_PLIC].len),
    .i_axi_s_awlock(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_PLIC].lock),
    .i_axi_s_awprot(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_PLIC].prot),
    .i_axi_s_awsize(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_PLIC].size),
    .o_axi_s_awready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_PLIC]),
    .i_axi_s_awvalid(lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_PLIC]),
    .o_axi_s_bid(lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_PLIC].id),
    .o_axi_s_bresp(lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_PLIC].resp),
    .i_axi_s_bready(lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_PLIC]),
    .o_axi_s_bvalid(lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_PLIC]),
    .o_axi_s_rdata(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_PLIC].data),
    .o_axi_s_rid(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_PLIC].id),
    .o_axi_s_rlast(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_PLIC].last),
    .o_axi_s_rresp(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_PLIC].resp),
    .i_axi_s_rready(lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_PLIC]),
    .o_axi_s_rvalid(lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_PLIC]),
    .i_axi_s_wdata(lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_PLIC].data),
    .i_axi_s_wlast(lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_PLIC].last),
    .i_axi_s_wstrb(lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_PLIC].strb),
    .o_axi_s_wready(lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_PLIC]),
    .i_axi_s_wvalid(lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_PLIC])
  );

  always_comb lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_PLIC].user = 'b0;
  always_comb lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_PLIC].user = 'b0;

  nds_plic_wrapper #(
    .INTERRUPT_WIDTH(APU_SW_INTERRUPT_WIDTH),
    .TARGET_WIDTH(CORE_WIDTH + APU_AIC_WIDTH),
    .MAX_PRIORITY(APU_SW_INTERRUPT_MAX_PRIORITY),
    .PROGRAMMABLE_TRIGGER(1),
    .AXI_DATA_WIDTH(chip_pkg::CHIP_AXI_LT_DATA_W),
    .AXI_ADDR_WIDTH(chip_pkg::CHIP_AXI_ADDR_W),
    .AXI_ID_WIDTH(APU_AXI_LT_S_ID_W)
  ) u_sw_plic (
    .i_clk(aclk_gated),
    .i_rst_n(i_arst_n),

    .i_interrupt_src('0),
    .o_targets_eip({o_aic_msip, cores_msip}),

    .i_axi_s_araddr(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_SWPLIC].addr),
    .i_axi_s_arburst(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_SWPLIC].burst),
    .i_axi_s_arcache(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_SWPLIC].cache),
    .i_axi_s_arid(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_SWPLIC].id),
    .i_axi_s_arlen(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_SWPLIC].len),
    .i_axi_s_arlock(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_SWPLIC].lock),
    .i_axi_s_arprot(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_SWPLIC].prot),
    .i_axi_s_arsize(lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_SWPLIC].size),
    .o_axi_s_arready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_SWPLIC]),
    .i_axi_s_arvalid(lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_SWPLIC]),
    .i_axi_s_awaddr(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_SWPLIC].addr),
    .i_axi_s_awburst(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_SWPLIC].burst),
    .i_axi_s_awcache(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_SWPLIC].cache),
    .i_axi_s_awid(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_SWPLIC].id),
    .i_axi_s_awlen(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_SWPLIC].len),
    .i_axi_s_awlock(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_SWPLIC].lock),
    .i_axi_s_awprot(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_SWPLIC].prot),
    .i_axi_s_awsize(lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_SWPLIC].size),
    .o_axi_s_awready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_SWPLIC]),
    .i_axi_s_awvalid(lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_SWPLIC]),
    .o_axi_s_bid(lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_SWPLIC].id),
    .o_axi_s_bresp(lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_SWPLIC].resp),
    .i_axi_s_bready(lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_SWPLIC]),
    .o_axi_s_bvalid(lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_SWPLIC]),
    .o_axi_s_rdata(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_SWPLIC].data),
    .o_axi_s_rid(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_SWPLIC].id),
    .o_axi_s_rlast(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_SWPLIC].last),
    .o_axi_s_rresp(lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_SWPLIC].resp),
    .i_axi_s_rready(lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_SWPLIC]),
    .o_axi_s_rvalid(lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_SWPLIC]),
    .i_axi_s_wdata(lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_SWPLIC].data),
    .i_axi_s_wlast(lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_SWPLIC].last),
    .i_axi_s_wstrb(lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_SWPLIC].strb),
    .o_axi_s_wready(lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_SWPLIC]),
    .i_axi_s_wvalid(lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_SWPLIC])
  );

  always_comb lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_SWPLIC].user = 'b0;
  always_comb lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_SWPLIC].user = 'b0;

  // Token Manager
  token_manager_apu_csr_reg_pkg::axi_a_ch_h2d_t token_manager_axi_s_aw;
  token_manager_apu_csr_reg_pkg::axi_w_ch_h2d_t token_manager_axi_s_w;
  token_manager_apu_csr_reg_pkg::axi_b_ch_d2h_t token_manager_axi_s_b;
  token_manager_apu_csr_reg_pkg::axi_a_ch_h2d_t token_manager_axi_s_ar;
  token_manager_apu_csr_reg_pkg::axi_r_ch_d2h_t token_manager_axi_s_r;

  always_comb begin
    token_manager_axi_s_aw.id    = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_TOKEN].id;
    token_manager_axi_s_aw.addr  = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_TOKEN].addr;
    token_manager_axi_s_aw.len   = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_TOKEN].len;
    token_manager_axi_s_aw.size  = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_TOKEN].size;
    token_manager_axi_s_aw.burst = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_TOKEN].burst;
    // token_manager_axi_s_aw.lock  = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_TOKEN].lock;
    // token_manager_axi_s_aw.cache = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_TOKEN].cache;
    // token_manager_axi_s_aw.prot  = lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_TOKEN].prot;
    token_manager_axi_s_aw.valid = lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_TOKEN];
  end
  always_comb begin
    token_manager_axi_s_w.data  = lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_TOKEN].data;
    token_manager_axi_s_w.strb  = lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_TOKEN].strb;
    token_manager_axi_s_w.last  = lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_TOKEN].last;
    token_manager_axi_s_w.valid = lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_TOKEN];
  end
  always_comb begin
    lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_TOKEN].id   = token_manager_axi_s_b.id;
    lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_TOKEN].resp = axi_pkg::axi_resp_e'(token_manager_axi_s_b.resp);
    lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_TOKEN] = token_manager_axi_s_b.valid;
  end
  always_comb begin
    token_manager_axi_s_ar.id    = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_TOKEN].id;
    token_manager_axi_s_ar.addr  = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_TOKEN].addr;
    token_manager_axi_s_ar.len   = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_TOKEN].len;
    token_manager_axi_s_ar.size  = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_TOKEN].size;
    token_manager_axi_s_ar.burst = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_TOKEN].burst;
    // token_manager_axi_s_ar.lock  = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_TOKEN].lock;
    // token_manager_axi_s_ar.cache = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_TOKEN].cache;
    // token_manager_axi_s_ar.prot  = lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_TOKEN].prot;
    token_manager_axi_s_ar.valid = lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_TOKEN];
  end
  always_comb begin
    lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_TOKEN].id   = token_manager_axi_s_r.id;
    lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_TOKEN].data = token_manager_axi_s_r.data;
    lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_TOKEN].resp = axi_pkg::axi_resp_e'(token_manager_axi_s_r.resp);
    lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_TOKEN].last = token_manager_axi_s_r.last;
    lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_TOKEN] = token_manager_axi_s_r.valid;
  end

  token_manager_apu u_token_manager (
    .i_clk(i_aclk),
    .i_rst_n(i_arst_n),

    // Top connection via OCPL:
    .o_tok_prod_ocpl_m_maddr(o_tok_prod_ocpl_m_maddr),
    .o_tok_prod_ocpl_m_mcmd(o_tok_prod_ocpl_m_mcmd),
    .i_tok_prod_ocpl_m_scmdaccept(i_tok_prod_ocpl_m_scmdaccept),
    .o_tok_prod_ocpl_m_mdata(o_tok_prod_ocpl_m_mdata),

    .i_tok_cons_ocpl_s_maddr(i_tok_cons_ocpl_s_maddr),
    .i_tok_cons_ocpl_s_mcmd(i_tok_cons_ocpl_s_mcmd),
    .o_tok_cons_ocpl_s_scmdaccept(o_tok_cons_ocpl_s_scmdaccept),
    .i_tok_cons_ocpl_s_mdata(i_tok_cons_ocpl_s_mdata),

    // Write Address Channel
    .i_axi_s_aw(token_manager_axi_s_aw),
    .o_axi_s_aw_ready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_TOKEN]),
    // Write  Data Channel
    .i_axi_s_w(token_manager_axi_s_w),
    .o_axi_s_w_ready(lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_TOKEN]),
    // Write Response Channel
    .o_axi_s_b(token_manager_axi_s_b),
    .i_axi_s_b_ready(lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_TOKEN]),
    // Read Address Channel
    .i_axi_s_ar(token_manager_axi_s_ar),
    .o_axi_s_ar_ready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_TOKEN]),
    // Read Data Channel
    .o_axi_s_r(token_manager_axi_s_r),
    .i_axi_s_r_ready(lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_TOKEN]),

    // interrupt:
    .o_irq(token_manager_irq)
  );

  always_comb lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_TOKEN].user = 'b0;
  always_comb lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_TOKEN].user = 'b0;

  // Trace
  // No real trace
  axe_axi_err_sub #(
    .AxiIdWidth  (APU_AXI_LT_S_ID_W),
    .Resp        (axi_pkg::RespDecErr),
    // litt "!Trace.." as ASCII
    .ReadData    (64'h2154726163652E2E),
    .MaxTxn      (4), // Minimize ressource consumption
    .SupportAtops(APU_SUPPORT_ATOPS),
    .axi_aw_t    (apu_axi_lt_s_aw_t),
    .axi_w_t     (apu_axi_lt_w_t),
    .axi_b_t     (apu_axi_lt_s_b_t),
    .axi_ar_t    (apu_axi_lt_s_ar_t),
    .axi_r_t     (apu_axi_lt_s_r_t)
  ) u_trace (
    .i_clk(aclk_gated),
    .i_rst_n(i_arst_n),

    .i_axi_s_aw      (lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .i_axi_s_aw_valid(lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .o_axi_s_aw_ready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .i_axi_s_w       (lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .i_axi_s_w_valid (lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .o_axi_s_w_ready (lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .o_axi_s_b       (lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .o_axi_s_b_valid (lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .i_axi_s_b_ready (lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .i_axi_s_ar      (lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .i_axi_s_ar_valid(lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .o_axi_s_ar_ready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .o_axi_s_r       (lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .o_axi_s_r_valid (lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_TRACE]),
    .i_axi_s_r_ready (lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_TRACE])
  );

  // Reserved / Err sub
  axe_axi_err_sub #(
    .AxiIdWidth  (APU_AXI_LT_S_ID_W),
    .Resp        (axi_pkg::RespDecErr),
    // litt "/KonKon\" as ASCII
    .ReadData    (64'h2F4B6F6E4B6F6E5C),
    .MaxTxn      (4), // Minimize ressource consumption
    .SupportAtops(APU_SUPPORT_ATOPS),
    .axi_aw_t    (apu_axi_lt_s_aw_t),
    .axi_w_t     (apu_axi_lt_w_t),
    .axi_b_t     (apu_axi_lt_s_b_t),
    .axi_ar_t    (apu_axi_lt_s_ar_t),
    .axi_r_t     (apu_axi_lt_s_r_t)
  ) u_reserved_err_sub (
    .i_clk(aclk_gated),
    .i_rst_n(i_arst_n),

    .i_axi_s_aw      (lt_axi_s_aw[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .i_axi_s_aw_valid(lt_axi_s_awvalid[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .o_axi_s_aw_ready(lt_axi_s_awready[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .i_axi_s_w       (lt_axi_s_w[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .i_axi_s_w_valid (lt_axi_s_wvalid[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .o_axi_s_w_ready (lt_axi_s_wready[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .o_axi_s_b       (lt_axi_s_b[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .o_axi_s_b_valid (lt_axi_s_bvalid[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .i_axi_s_b_ready (lt_axi_s_bready[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .i_axi_s_ar      (lt_axi_s_ar[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .i_axi_s_ar_valid(lt_axi_s_arvalid[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .o_axi_s_ar_ready(lt_axi_s_arready[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .o_axi_s_r       (lt_axi_s_r[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .o_axi_s_r_valid (lt_axi_s_rvalid[APU_XBAR_LT_M_PORT_IDX_ERR]),
    .i_axi_s_r_ready (lt_axi_s_rready[APU_XBAR_LT_M_PORT_IDX_ERR])
  );

  apu_axi_lt_m_aw_t mmio_axi_m_aw;
  logic mmio_axi_m_awready;
  logic mmio_axi_m_awvalid;
  apu_axi_lt_w_t mmio_axi_m_w;
  logic mmio_axi_m_wready;
  logic mmio_axi_m_wvalid;
  apu_axi_lt_m_b_t mmio_axi_m_b;
  logic mmio_axi_m_bready;
  logic mmio_axi_m_bvalid;
  apu_axi_lt_m_ar_t mmio_axi_m_ar;
  logic mmio_axi_m_arready;
  logic mmio_axi_m_arvalid;
  apu_axi_lt_m_r_t mmio_axi_m_r;
  logic mmio_axi_m_rready;
  logic mmio_axi_m_rvalid;

  apu_axi_isolate #(
    .AxiIdWidth(APU_AXI_LT_M_ID_W),
    .AxiDataWidth(chip_pkg::CHIP_AXI_LT_DATA_W),
    .MaxTxn(2**APU_AXI_LT_M_ID_W),
    .SupportAtops(APU_SUPPORT_ATOPS),
    .axi_aw_t(apu_axi_lt_m_aw_t),
    .axi_w_t(apu_axi_lt_w_t),
    .axi_b_t(apu_axi_lt_m_b_t),
    .axi_ar_t(apu_axi_lt_m_ar_t),
    .axi_r_t(apu_axi_lt_m_r_t)
  ) u_lt_axi_isolate_ax65 (
    /// Rising-edge clock of all ports
    .i_clk(i_aclk),
    /// Asynchronous reset, active low
    .i_rst_n(i_arst_n),

    /// Low Power Interface
    .i_qreq_n(axi_qreq_n[1]),
    .o_qdeny(axi_qdeny[1]),
    .o_qaccept_n(axi_qaccept_n[1]),
    .o_qactive(axi_qactive[1]),

    //////////////////////
    // Subordinate Port //
    //////////////////////
    .i_axi_s_aw(mmio_axi_m_aw),
    .i_axi_s_aw_valid(mmio_axi_m_awvalid),
    .o_axi_s_aw_ready(mmio_axi_m_awready),
    .i_axi_s_w(mmio_axi_m_w),
    .i_axi_s_w_valid(mmio_axi_m_wvalid),
    .o_axi_s_w_ready(mmio_axi_m_wready),
    .o_axi_s_b(mmio_axi_m_b),
    .o_axi_s_b_valid(mmio_axi_m_bvalid),
    .i_axi_s_b_ready(mmio_axi_m_bready),
    .i_axi_s_ar(mmio_axi_m_ar),
    .i_axi_s_ar_valid(mmio_axi_m_arvalid),
    .o_axi_s_ar_ready(mmio_axi_m_arready),
    .o_axi_s_r(mmio_axi_m_r),
    .o_axi_s_r_valid(mmio_axi_m_rvalid),
    .i_axi_s_r_ready(mmio_axi_m_rready),

    //////////////////
    // Manager port //
    //////////////////
    .o_axi_m_aw(lt_axi_m_aw[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .o_axi_m_aw_valid(lt_axi_m_awvalid[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .i_axi_m_aw_ready(lt_axi_m_awready[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .o_axi_m_w(lt_axi_m_w[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .o_axi_m_w_valid(lt_axi_m_wvalid[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .i_axi_m_w_ready(lt_axi_m_wready[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .i_axi_m_b(lt_axi_m_b[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .i_axi_m_b_valid(lt_axi_m_bvalid[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .o_axi_m_b_ready(lt_axi_m_bready[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .o_axi_m_ar(lt_axi_m_ar[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .o_axi_m_ar_valid(lt_axi_m_arvalid[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .i_axi_m_ar_ready(lt_axi_m_arready[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .i_axi_m_r(lt_axi_m_r[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .i_axi_m_r_valid(lt_axi_m_rvalid[APU_XBAR_LT_S_PORT_IDX_AX65]),
    .o_axi_m_r_ready(lt_axi_m_rready[APU_XBAR_LT_S_PORT_IDX_AX65])
  );

  axe_ax65_cluster #(
    .CORE_WIDTH(CORE_WIDTH),
    .MAX_CORE_WIDTH(AX65_MAX_CORE_WIDTH),
    .BHT_WIDTH(AX65_BHT_WIDTH),
    .DCACHE_WIDTH(AX65_DCACHE_WIDTH),
    .ICACHE_WIDTH(AX65_ICACHE_WIDTH),
    .L2_WIDTH(AX65_L2_WIDTH),
    .L2C_BANK_WIDTH(AX65_L2C_BANK_WIDTH),
    .L2C_BANK_DATA_WIDTH(AX65_L2C_BANK_DATA_WIDTH),
    .L2C_BANK_TAG_WIDTH(AX65_L2C_BANK_TAG_WIDTH),
    .SINK_WIDTH(AX65_SINK_WIDTH),
    .SOURCE_WIDTH(AX65_SOURCE_WIDTH),
    .CTRL_IN_WIDTH(AX65_CTRL_IN_WIDTH),
    .CTRL_OUT_WIDTH(AX65_CTRL_OUT_WIDTH)
  ) u_axe_ax65_cluster (
    /// Slow ref clock
    .i_mtime_clk,
    .i_por_rst_n,
    /// Fast core clocks
    .i_cores_clk,
    .i_cores_rst_n,
    /// Fast AXI clock
    .i_aclk,
    .i_arst_n,
    /// Fast l2 clock
    .i_l2c_clk,
    .i_l2c_rst_n,
    //////////////////////////////////////////////
    /// COREs sigs
    //////////////////////////////////////////////
    .i_cores_ctrl,
    .o_cores_ctrl,
    .i_cores_disable_init,
    .i_cores_hart_id(cores_hart_id),
    .i_cores_meip(cores_meip),
    .i_cores_msip(cores_msip),
    .i_cores_nmi,
    .i_cores_reset_vector,
    .i_cores_seip(cores_seip),
    .o_cores_wfi_mode(cores_wfi_mode),
    /// Debug sigs
    .i_cores_debugint,
    .i_cores_resethaltreq,
    .o_cores_hart_unavail,
    .o_cores_hart_under_reset,

    //////////////////////////////////////////////
    /// AXIs sigs
    //////////////////////////////////////////////
    // IOCP
    .i_iocp_axi_s_aw(iocp_axi_s_aw),
    .o_iocp_axi_s_awready(iocp_axi_s_awready),
    .i_iocp_axi_s_awvalid(iocp_axi_s_awvalid),
    .i_iocp_axi_s_w(iocp_axi_s_w),
    .o_iocp_axi_s_wready(iocp_axi_s_wready),
    .i_iocp_axi_s_wvalid(iocp_axi_s_wvalid),
    .o_iocp_axi_s_b(iocp_axi_s_b),
    .i_iocp_axi_s_bready(iocp_axi_s_bready),
    .o_iocp_axi_s_bvalid(iocp_axi_s_bvalid),
    .i_iocp_axi_s_ar(iocp_axi_s_ar),
    .o_iocp_axi_s_arready(iocp_axi_s_arready),
    .i_iocp_axi_s_arvalid(iocp_axi_s_arvalid),
    .o_iocp_axi_s_r(iocp_axi_s_r),
    .i_iocp_axi_s_rready(iocp_axi_s_rready),
    .o_iocp_axi_s_rvalid(iocp_axi_s_rvalid),
    // MEM
    .o_mem_axi_m_aw(mem_dma_axi_m_aw[APU_MUX_MT_PORT_IDX_AX65]),
    .i_mem_axi_m_awready(mem_dma_axi_m_awready[APU_MUX_MT_PORT_IDX_AX65]),
    .o_mem_axi_m_awvalid(mem_dma_axi_m_awvalid[APU_MUX_MT_PORT_IDX_AX65]),
    .o_mem_axi_m_w(mem_dma_axi_m_w[APU_MUX_MT_PORT_IDX_AX65]),
    .i_mem_axi_m_wready(mem_dma_axi_m_wready[APU_MUX_MT_PORT_IDX_AX65]),
    .o_mem_axi_m_wvalid(mem_dma_axi_m_wvalid[APU_MUX_MT_PORT_IDX_AX65]),
    .i_mem_axi_m_b(mem_dma_axi_m_b[APU_MUX_MT_PORT_IDX_AX65]),
    .o_mem_axi_m_bready(mem_dma_axi_m_bready[APU_MUX_MT_PORT_IDX_AX65]),
    .i_mem_axi_m_bvalid(mem_dma_axi_m_bvalid[APU_MUX_MT_PORT_IDX_AX65]),
    .o_mem_axi_m_ar(mem_dma_axi_m_ar[APU_MUX_MT_PORT_IDX_AX65]),
    .i_mem_axi_m_arready(mem_dma_axi_m_arready[APU_MUX_MT_PORT_IDX_AX65]),
    .o_mem_axi_m_arvalid(mem_dma_axi_m_arvalid[APU_MUX_MT_PORT_IDX_AX65]),
    .i_mem_axi_m_r(mem_dma_axi_m_r[APU_MUX_MT_PORT_IDX_AX65]),
    .o_mem_axi_m_rready(mem_dma_axi_m_rready[APU_MUX_MT_PORT_IDX_AX65]),
    .i_mem_axi_m_rvalid(mem_dma_axi_m_rvalid[APU_MUX_MT_PORT_IDX_AX65]),
    // MMIO
    .o_mmio_axi_m_aw(mmio_axi_m_aw),
    .i_mmio_axi_m_awready(mmio_axi_m_awready),
    .o_mmio_axi_m_awvalid(mmio_axi_m_awvalid),
    .o_mmio_axi_m_w(mmio_axi_m_w),
    .i_mmio_axi_m_wready(mmio_axi_m_wready),
    .o_mmio_axi_m_wvalid(mmio_axi_m_wvalid),
    .i_mmio_axi_m_b(mmio_axi_m_b),
    .o_mmio_axi_m_bready(mmio_axi_m_bready),
    .i_mmio_axi_m_bvalid(mmio_axi_m_bvalid),
    .o_mmio_axi_m_ar(mmio_axi_m_ar),
    .i_mmio_axi_m_arready(mmio_axi_m_arready),
    .o_mmio_axi_m_arvalid(mmio_axi_m_arvalid),
    .i_mmio_axi_m_r(mmio_axi_m_r),
    .o_mmio_axi_m_rready(mmio_axi_m_rready),
    .i_mmio_axi_m_rvalid(mmio_axi_m_rvalid),

    //////////////////////////////////////////////
    /// L2 sigs
    //////////////////////////////////////////////
    .i_l2c_ctrl,
    .o_l2c_ctrl,
    .i_l2c_disable_init,
    .o_l2c_err_int(l2c_err_int),

    //////////////////////////////////////////////
    /// Misc sigs
    //////////////////////////////////////////////
    .o_aic_mtip,
    .i_aic_stoptime,
    .i_test_mode
  );

endmodule
