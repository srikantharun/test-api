
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//

module lpddr_p
  import chip_pkg::*;
  import axi_pkg::*;
  import lpddr_pkg::*;
  (
  // Clocks
  input  wire   i_ao_clk,
  input  wire   i_lpddr_clk,

  //-------------------------------
  // Partition Controller Interface
  //-------------------------------
  input  wire                         i_ao_rst_n          ,
  input  wire                         i_global_rst_n      ,
  output wire                         o_ao_rst_sync_n     ,
  output logic          [1:0]         o_noc_async_idle_req, // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  input  logic          [1:0]         i_noc_async_idle_ack, // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  input  logic          [1:0]         i_noc_async_idle_val, // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  output logic                        o_noc_clken         ,
  output wire                         o_noc_rst_n         ,

  //-------------------------------
  // AXI4 lpddr_axi
  //-------------------------------
  input  logic [39:0]  i_lpddr_axi_m_araddr  ,
  input  logic [1:0]   i_lpddr_axi_m_arburst ,
  input  logic [3:0]   i_lpddr_axi_m_arcache ,
  input  logic [7:0]   i_lpddr_axi_m_arid    ,
  input  logic [7:0]   i_lpddr_axi_m_arlen   ,
  input  logic i_lpddr_axi_m_arlock  ,
  input  logic [2:0]   i_lpddr_axi_m_arprot  ,
  input  logic [3:0]   i_lpddr_axi_m_arqos   ,
  input  logic [3:0]   i_lpddr_axi_m_arregion,
  input  logic         i_lpddr_axi_m_aruser  ,
  input  logic [2:0]   i_lpddr_axi_m_arsize  ,
  input  logic i_lpddr_axi_m_arvalid ,
  input  logic i_lpddr_axi_m_rready  ,
  input  logic [39:0]  i_lpddr_axi_m_awaddr  ,
  input  logic [1:0]   i_lpddr_axi_m_awburst ,
  input  logic [3:0]   i_lpddr_axi_m_awcache ,
  input  logic [7:0]   i_lpddr_axi_m_awid    ,
  input  logic [7:0]   i_lpddr_axi_m_awlen   ,
  input  logic i_lpddr_axi_m_awlock  ,
  input  logic [2:0]   i_lpddr_axi_m_awprot  ,
  input  logic [3:0]   i_lpddr_axi_m_awqos   ,
  input  logic [3:0]   i_lpddr_axi_m_awregion,
  input  logic         i_lpddr_axi_m_awuser  ,
  input  logic [2:0]   i_lpddr_axi_m_awsize  ,
  input  logic i_lpddr_axi_m_awvalid ,
  input  logic [255:0] i_lpddr_axi_m_wdata   ,
  input  logic i_lpddr_axi_m_wlast   ,
  input  logic [31:0]  i_lpddr_axi_m_wstrb   ,
  input  logic i_lpddr_axi_m_wvalid  ,
  input  logic i_lpddr_axi_m_wuser  ,
  input  logic i_lpddr_axi_m_bready  ,
  output logic o_lpddr_axi_m_arready,
  output logic [255:0] o_lpddr_axi_m_rdata  ,
  output logic [7:0]   o_lpddr_axi_m_rid    ,
  output logic o_lpddr_axi_m_rlast  ,
  output logic o_lpddr_axi_m_ruser ,
  output logic [1:0]   o_lpddr_axi_m_rresp  ,
  output logic o_lpddr_axi_m_rvalid ,
  output logic o_lpddr_axi_m_awready,
  output logic o_lpddr_axi_m_wready ,
  output logic [7:0]   o_lpddr_axi_m_bid    ,
  output logic [1:0]   o_lpddr_axi_m_bresp  ,
  output logic o_lpddr_axi_m_bvalid ,
  output logic o_lpddr_axi_m_buser ,

  //-------------------------------
  // APB4 lpddr_cfg_apb (sync to i_lpddr_clk)
  //-------------------------------
  input  logic [31:0] i_lpddr_cfg_apb4_s_paddr,
  input  logic        i_lpddr_cfg_apb4_s_penable,
  input  logic [2:0]  i_lpddr_cfg_apb4_s_pprot,
  input  logic        i_lpddr_cfg_apb4_s_psel,
  input  logic [3:0]  i_lpddr_cfg_apb4_s_pstrb,
  input  logic [31:0] i_lpddr_cfg_apb4_s_pwdata,
  input  logic        i_lpddr_cfg_apb4_s_pwrite,
  output logic [31:0] o_lpddr_cfg_apb4_s_prdata,
  output logic        o_lpddr_cfg_apb4_s_pready,
  output logic        o_lpddr_cfg_apb4_s_pslverr,
  //-------------------------------
  // APB4 lpddr_syscfg_apb (sync to i_ao_clk)
  //-------------------------------
  input  chip_syscfg_addr_t           i_lpddr_syscfg_apb4_s_paddr  ,
  input  chip_apb_syscfg_data_t       i_lpddr_syscfg_apb4_s_pwdata ,
  input  logic                        i_lpddr_syscfg_apb4_s_pwrite ,
  input  logic                        i_lpddr_syscfg_apb4_s_psel   ,
  input  logic                        i_lpddr_syscfg_apb4_s_penable,
  input  chip_apb_syscfg_strb_t       i_lpddr_syscfg_apb4_s_pstrb  ,
  input  logic                  [2:0] i_lpddr_syscfg_apb4_s_pprot  ,
  output logic                        o_lpddr_syscfg_apb4_s_pready ,
  output chip_apb_syscfg_data_t       o_lpddr_syscfg_apb4_s_prdata ,
  output logic                        o_lpddr_syscfg_apb4_s_pslverr,

  // CTRL Interrupts
  output logic  o_ctrl_sbr_done_intr,
  output logic  o_ctrl_derate_temp_limit_intr,
  output logic  o_ctrl_ecc_ap_err_intr,
  output logic  o_ctrl_ecc_corrected_err_intr,
  output logic  o_ctrl_ecc_uncorrected_err_intr,
  output logic  o_ctrl_rd_linkecc_corr_err_intr,
  output logic  o_ctrl_rd_linkecc_uncorr_err_intr,

  // PHY interrupts
  output logic  o_phy_pie_prog_err_intr,
  output logic  o_phy_ecc_err_intr,
  output logic  o_phy_rdfptrchk_err_intr,
  output logic  o_phy_pie_parity_err_intr,
  output logic  o_phy_acsm_parity_err_intr,
  output logic  o_phy_trng_fail_intr,
  output logic  o_phy_init_cmplt_intr,
  output logic  o_phy_trng_cmplt_intr,

  //-------------------------------
  // DFT Interface add by axelera
  //-------------------------------
  input wire  tck,
  input wire  trst,
  input logic tms,
  input logic tdi,
  output logic tdo_en,
  output logic tdo,

  input wire  ssn_bus_clk,
  input logic [24 -1: 0] ssn_bus_data_in,
  output logic [24 -1: 0] ssn_bus_data_out,

  input wire  bisr_clk,
  input wire  bisr_reset,
  input logic  bisr_shift_en,
  input logic  bisr_si,
  output logic  bisr_so,

  // Observability signals for lpddr
  output logic [15:0] o_lpddr_obs,

  //-----------
  // PHY Bump signals
  //-----------
  output wire  BP_MEMRESET_L, //DRAM reset
  inout wire [19:0] BP_A,     //DRAM address and command bits
  inout wire  BP_ATO,         //Analog test output (debug pin, functionality selectable through PHY csrs)
  inout wire  BP_ATO_PLL,     //Analog test output from PLL (debug pin, functionality selectable through PHY csrs)
  inout wire [12:0] BP_B0_D,  //DRAM data bits and strobes
  inout wire [12:0] BP_B1_D,  //DRAM data bits and strobes
  inout wire [12:0] BP_B2_D,  //DRAM data bits and strobes
  inout wire [12:0] BP_B3_D,  //DRAM data bits and strobes
  inout wire  BP_CK0_C,       //DRAM clock (complement)
  inout wire  BP_CK0_T,       //DRAM clock
  inout wire  BP_CK1_C,       //DRAM clock (complement)
  inout wire  BP_CK1_T,       //DRAM clock
  inout wire  BP_ZN           //calibration external reference resistor -> An external precision resistor (RZN), connected between BP_ZN port and VSS, is required and used as areference by the impedance calibration circuit. By default, a 120 Ohm, 1% tolerance, resistor is required.
);

  //-------------------------------
  // Partition controller Instance
  //-------------------------------
  logic test_mode = 1'b0;

  // Clocks
  wire lpddr_clk;
  wire lpddr_pll_ref_clk;
  wire [1:0] lpddr_clks, lpddr_clkens;
  assign lpddr_clk = lpddr_clks[0];
  assign lpddr_pll_ref_clk = lpddr_clks[1];
  assign o_noc_clken = lpddr_clkens[0];

  // Resets
  wire  cfg_rst_n;
  wire  ctrl_rst_n;
  wire  phy_rst;
  wire [2:0] lpddr_rsts_n;
  assign cfg_rst_n = lpddr_rsts_n[0];
  assign ctrl_rst_n = lpddr_rsts_n[1];
  assign phy_rst = ~lpddr_rsts_n[2]; // Inverted as PHY resets are active high.

  // MEM PG control signals
  logic [1:0] ret;
  logic [1:0] pde;
  logic [1:0] prn;
  logic lpddr_ctrl_pde, lpddr_ctrl_ret, lpddr_ctrl_prn;
  logic lpddr_phy_pde, lpddr_phy_ret, lpddr_phy_prn;
  assign lpddr_ctrl_ret= ret[0];
  assign lpddr_ctrl_pde= pde[0];
  assign prn[0] = lpddr_ctrl_prn;
  assign lpddr_phy_ret = ret[1];
  assign lpddr_phy_pde = pde[1];
  assign prn[1] = lpddr_phy_prn;

  // Tie off unused AXI user signals
  assign o_lpddr_axi_m_ruser = '0;
  assign o_lpddr_axi_m_buser = '0;

  //-------------------------------
  // AO Reg
  //-------------------------------
  lpddr_csr_reg_pkg::lpddr_csr_reg2hw_t             reg2hw;
  lpddr_csr_reg_pkg::lpddr_csr_hw2reg_t             hw2reg;
  pctl_ao_csr_reg_pkg::apb_h2d_t ao_csr_apb_req;
  pctl_ao_csr_reg_pkg::apb_d2h_t ao_csr_apb_rsp;

  //-------------------------------
  // PCTL setup
  //-------------------------------
  // CLOCKS and RESET
  // LPDDR has two incoming clocks. The ao_clk that drives all the always-on logic in the wrapper, and the i_lpddr_clk that drives the SNPS IP through the pctlP
  // The pctl needs 2 dividers on i_lpddr_clk to split it in a normal lpddr-clk and a lpddr_pll_ref_clk clock.
  // The first is used to drive all subsys clocks related to interfaces, ctrl, and dfi.
  // The second is used to drive the PHYs internal pll_ref_clk and the pll_bypass_clk. In a normal use-case (i.e. as pll_ref_clk), the PHYs pll will multiply it with 4x to obtain a 3.2GHz clock
  // Further, the lpddr has 3 resets, cfg, ctrl and phy. When any of them is deasserted, only the lpddr_clk is stopped. The lpddr_pll_ref_clk is never stopped for a reset deassert to avoid losing pll lock.
  // The noc signals should be driven based on the 'normal' lpddr_clk, and the `cfg` reset.
  // FENCES
  // LPDDR needs to have its apb cfg interface up and running to start the IP configuration and link training.
  // During this period the AXI interface will not respond since the remainder of the CTRL is still in reset.
  // To keep the AXI still fenced during this time, the APB CFG interface and AXI interface each needs an individual fence
  // APB takes fence 0, AXI takes fence 1.
  pctl #(
    .N_FAST_CLKS (2),
    .N_RESETS (3),
    .N_MEM_PG(2),
    .N_FENCES(2),
    .N_THROTTLE_PINS(0),
    .CLKRST_MATRIX ({
      3'b000,     // clock index 1 -> lpddr_pll_ref_clk -> No reset de-assertion causes a gating of lpddr_pll_ref_clk, it should never be stopped.
      3'b111}),   // clock index 0 -> lpddr_clk ->Any reset de-assertion causes a gating of lpddr_clk
    .PLL_CLK_IS_I_CLK ({1'b0, 1'b0}),
    .NOC_RST_IDX (0),
    .AUTO_RESET_REMOVE (1'b0),
    .paddr_t (chip_syscfg_addr_t),
    .pdata_t (chip_apb_syscfg_data_t),
    .pstrb_t (chip_apb_syscfg_strb_t)
  ) u_pctl (
    .i_clk(i_ao_clk),
    .i_ao_rst_n(i_ao_rst_n),
    .i_global_rst_n(i_global_rst_n),
    .i_test_mode(test_mode),
    .i_pll_clk({i_lpddr_clk,i_lpddr_clk}),
    .o_partition_clk(lpddr_clks),
    .o_partition_rst_n(lpddr_rsts_n),
    .o_ao_rst_sync_n(o_ao_rst_sync_n),
    .o_noc_async_idle_req(o_noc_async_idle_req),
    .i_noc_async_idle_ack(i_noc_async_idle_ack),
    .i_noc_async_idle_val(i_noc_async_idle_val),
    .o_noc_clken(lpddr_clkens),
    .o_noc_rst_n(o_noc_rst_n),
    .o_int_shutdown_req  (),// ASO-UNUSED_OUTPUT: LPDDR doesn't request shutdown
    .i_int_shutdown_ack  (1'b1),
    .o_ret(ret),
    .o_pde(pde),
    .i_prn(prn),
    .i_global_sync_async('0), // LPDDR does not have a global sync feature
    .o_global_sync(), // ASO-UNUSED_OUTPUT: LPDDR does not have a global sync feature
    .i_cfg_apb4_s_paddr(i_lpddr_syscfg_apb4_s_paddr),
    .i_cfg_apb4_s_pwdata(i_lpddr_syscfg_apb4_s_pwdata),
    .i_cfg_apb4_s_pwrite(i_lpddr_syscfg_apb4_s_pwrite),
    .i_cfg_apb4_s_psel(i_lpddr_syscfg_apb4_s_psel),
    .i_cfg_apb4_s_penable(i_lpddr_syscfg_apb4_s_penable),
    .i_cfg_apb4_s_pstrb(i_lpddr_syscfg_apb4_s_pstrb),
    .i_cfg_apb4_s_pprot(i_lpddr_syscfg_apb4_s_pprot),
    .o_cfg_apb4_s_pready(o_lpddr_syscfg_apb4_s_pready),
    .o_cfg_apb4_s_prdata(o_lpddr_syscfg_apb4_s_prdata),
    .o_cfg_apb4_s_pslverr(o_lpddr_syscfg_apb4_s_pslverr),
    .o_ao_csr_apb_req(ao_csr_apb_req),
    .i_ao_csr_apb_rsp(ao_csr_apb_rsp),
    .i_throttle(1'b0) // LPDDR does not support throttling.
  );

  wire pclk_clk_buf_out;
  wire pclk_apbrw_clk_buf_out;
  wire aclk_clk_buf_out;
  wire core_ddrc_core_clk_clk_buf_out;
  wire core_ddrc_core_clk_apbrw_clk_buf_out;
  wire dficlk_clk_buf_out;
  wire sbr_clk_clk_buf_out;
  wire pllbypclk_clk_buf_out;
  wire pllrefclk_clk_buf_out;

  // Clock buffer for clock definition of pclk
  axe_tcl_clk_buffer i_pclk_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (pclk_clk_buf_out)
  );
  // Clock buffer for clock definition of pclk_apbrw
  axe_tcl_clk_buffer i_pclk_apbrw_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (pclk_apbrw_clk_buf_out)
  );
  // // Clock buffer for clock definition of aclk
  // axe_tcl_clk_buffer i_aclk_clk_buf (
  //   .i_clk (lpddr_clk),
  //   .o_clk (aclk_clk_buf_out)
  // );
  // Clock buffer for clock definition of core_ddrc_core_clk
  // axe_tcl_clk_buffer i_core_ddrc_core_clk_clk_buf (
  //   .i_clk (lpddr_clk),
  //   .o_clk (core_ddrc_core_clk_clk_buf_out)
  // );
  // Clock buffer for clock definition of core_ddrc_core_clk_apbrw
  axe_tcl_clk_buffer i_core_ddrc_core_clk_apbrw_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (core_ddrc_core_clk_apbrw_clk_buf_out)
  );
  // Clock buffer for clock definition of dficlk
  axe_tcl_clk_buffer i_dficlk_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (dficlk_clk_buf_out)
  );
  // Clock buffer for clock definition of sbr_clk
  axe_tcl_clk_buffer i_sbr_clk_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (sbr_clk_clk_buf_out)
  );
  // Clock buffer for clock definition of pllbypclk
  axe_tcl_clk_buffer i_pllbypclk_clk_buf (
    .i_clk (lpddr_pll_ref_clk),
    .o_clk (pllbypclk_clk_buf_out)
  );
  // Clock buffer for clock definition of pllrefclk
  axe_tcl_clk_buffer i_pllrefclk_clk_buf (
    .i_clk (lpddr_pll_ref_clk),
    .o_clk (pllrefclk_clk_buf_out)
  );


  //-------------------------------
  // AO CSR
  //-------------------------------
  lpddr_csr_reg_top u_lpddr_ao_csr (
    .clk_i    (i_ao_clk),
    .rst_ni   (o_ao_rst_sync_n),
    .apb_i    (ao_csr_apb_req),
    .apb_o    (ao_csr_apb_rsp),
    .reg2hw,
    .hw2reg,
    .devmode_i(1'b1)
  );

  //-------------------------------
  // SRAM implementation signals
  //-------------------------------
  logic  acsm_pde;
  logic  acsm_ret;
  logic  acsm_prn;
  logic  bc_pde;
  logic  bc_ret;
  logic  bc_prn;
  logic  dccm_pde;
  logic  dccm_ret;
  logic  dccm_prn;
  logic  gs_pde;
  logic  gs_ret;
  logic  gs_prn;
  logic  iccm_pde;
  logic  iccm_ret;
  logic  iccm_prn;
  logic  pie_pde;
  logic  pie_ret;
  logic  pie_prn;
  logic  wdata_pde;
  logic  wdata_ret;
  logic  wdata_prn;
  // CTRL memory control signal connections
  assign wdata_pde = lpddr_ctrl_pde;
  assign wdata_ret = lpddr_ctrl_ret;
  assign lpddr_ctrl_prn = wdata_prn;

  // PHY memory control signal connections
  // Power down enable daisy chain
  assign acsm_pde = lpddr_phy_pde;
  assign bc_pde = acsm_prn;
  assign dccm_pde = bc_prn;
  assign gs_pde = dccm_prn;
  assign iccm_pde = gs_prn;
  assign pie_pde = iccm_prn;
  assign lpddr_phy_prn = pie_prn;
  // Retention setting is broadcasted
  assign acsm_ret = lpddr_phy_ret;
  assign bc_ret = lpddr_phy_ret;
  assign dccm_ret = lpddr_phy_ret;
  assign gs_ret = lpddr_phy_ret;
  assign iccm_ret = lpddr_phy_ret;
  assign pie_ret = lpddr_phy_ret;

  // PLL debug signals, linked to csr with sync stage
  logic dwc_lpddr5xphy_pll_lock, dwc_lpddr5xphy_pll_lock_ao_synced;
  logic dwc_lpddr5xphy_pmu_busy, dwc_lpddr5xphy_pmu_busy_ao_synced;
  assign hw2reg.debug_phy_status.pll_lock.d = dwc_lpddr5xphy_pll_lock_ao_synced;
  assign hw2reg.debug_phy_status.pmu_busy.d = dwc_lpddr5xphy_pmu_busy_ao_synced;
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) dwc_lpddr5xphy_pll_lock_sync_inst (
    .i_clk (i_ao_clk),
    .i_rst_n (i_ao_rst_n),
    .i_d (dwc_lpddr5xphy_pll_lock),
    .o_q (dwc_lpddr5xphy_pll_lock_ao_synced)
  );
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) dwc_lpddr5xphy_pmu_busy_sync_inst (
    .i_clk (i_ao_clk),
    .i_rst_n (i_ao_rst_n),
    .i_d (dwc_lpddr5xphy_pmu_busy),
    .o_q (dwc_lpddr5xphy_pmu_busy_ao_synced)
  );

  //-------------------------------
  // APB Spill lpddr_cfg_apb
  //-------------------------------
  logic [31:0] piped_lpddr_cfg_apb4_s_paddr;
  logic        piped_lpddr_cfg_apb4_s_penable;
  logic [2:0]  piped_lpddr_cfg_apb4_s_pprot;
  logic        piped_lpddr_cfg_apb4_s_psel;
  logic [3:0]  piped_lpddr_cfg_apb4_s_pstrb;
  logic [31:0] piped_lpddr_cfg_apb4_s_pwdata;
  logic        piped_lpddr_cfg_apb4_s_pwrite;
  logic [31:0] piped_lpddr_cfg_apb4_s_prdata;
  logic        piped_lpddr_cfg_apb4_s_pready;
  logic        piped_lpddr_cfg_apb4_s_pslverr;

  axe_apb_cut #(
    /// Width of the APB address (only used for typedef)
    .ApbAddrWidth(32),
    /// Width of the APB data (only used for typedef)
    .ApbDataWidth(32)
  ) lpddr_cfg_apb_cut_inst (
    /// Clock, positive edge triggered
    .i_clk              (lpddr_clk),
    /// Asynchronous reset, active low
    .i_rst_n            (cfg_rst_n),
    /////////////////
    // Subordinate //
    /////////////////
    .i_apb_s_paddr      (i_lpddr_cfg_apb4_s_paddr),
    .i_apb_s_pwdata     (i_lpddr_cfg_apb4_s_pwdata),
    .i_apb_s_pwrite     (i_lpddr_cfg_apb4_s_pwrite),
    .i_apb_s_psel       (i_lpddr_cfg_apb4_s_psel),
    .i_apb_s_penable    (i_lpddr_cfg_apb4_s_penable),
    .i_apb_s_pstrb      (i_lpddr_cfg_apb4_s_pstrb),
    .i_apb_s_pprot      (i_lpddr_cfg_apb4_s_pprot),
    .o_apb_s_pready     (o_lpddr_cfg_apb4_s_pready),
    .o_apb_s_prdata     (o_lpddr_cfg_apb4_s_prdata),
    .o_apb_s_pslverr    (o_lpddr_cfg_apb4_s_pslverr),
    /////////////
    // Manager //
    /////////////
    .o_apb_m_paddr      (piped_lpddr_cfg_apb4_s_paddr),
    .o_apb_m_pwdata     (piped_lpddr_cfg_apb4_s_pwdata),
    .o_apb_m_pwrite     (piped_lpddr_cfg_apb4_s_pwrite),
    .o_apb_m_psel       (piped_lpddr_cfg_apb4_s_psel),
    .o_apb_m_penable    (piped_lpddr_cfg_apb4_s_penable),
    .o_apb_m_pstrb      (piped_lpddr_cfg_apb4_s_pstrb),
    .o_apb_m_pprot      (piped_lpddr_cfg_apb4_s_pprot),
    .i_apb_m_pready     (piped_lpddr_cfg_apb4_s_pready),
    .i_apb_m_prdata     (piped_lpddr_cfg_apb4_s_prdata),
    .i_apb_m_pslverr    (piped_lpddr_cfg_apb4_s_pslverr)
  );

  //-------------------------------
  // AXI SPILL lpddr_axi
  //-------------------------------
  logic [7:0] i_lpddr_axi_m_subip_awid   ;
  logic [32:0] i_lpddr_axi_m_subip_awaddr ;
  logic [7:0] i_lpddr_axi_m_subip_awlen  ;
  logic [2:0] i_lpddr_axi_m_subip_awsize ;
  logic [1:0] i_lpddr_axi_m_subip_awburst;
  logic i_lpddr_axi_m_subip_awlock ;
  logic [3:0] i_lpddr_axi_m_subip_awcache;
  logic [2:0] i_lpddr_axi_m_subip_awprot ;
  logic [3:0] i_lpddr_axi_m_subip_awqos  ;
  logic [3:0] i_lpddr_axi_m_subip_awregion;
  logic i_lpddr_axi_m_subip_awvalid;
  logic [255:0] i_lpddr_axi_m_subip_wdata  ;
  logic [31:0] i_lpddr_axi_m_subip_wstrb  ;
  logic i_lpddr_axi_m_subip_wlast  ;
  logic i_lpddr_axi_m_subip_wvalid ;
  logic i_lpddr_axi_m_subip_bready ;
  logic [7:0] i_lpddr_axi_m_subip_arid   ;
  logic [32:0] i_lpddr_axi_m_subip_araddr ;
  logic [7:0] i_lpddr_axi_m_subip_arlen  ;
  logic [2:0] i_lpddr_axi_m_subip_arsize ;
  logic [1:0] i_lpddr_axi_m_subip_arburst;
  logic i_lpddr_axi_m_subip_arlock ;
  logic [3:0] i_lpddr_axi_m_subip_arcache;
  logic [2:0] i_lpddr_axi_m_subip_arprot ;
  logic [3:0] i_lpddr_axi_m_subip_arqos  ;
  logic [3:0] i_lpddr_axi_m_subip_arregion;
  logic i_lpddr_axi_m_subip_arvalid;
  logic i_lpddr_axi_m_subip_rready ;
  logic o_lpddr_axi_m_subip_awready;
  logic o_lpddr_axi_m_subip_wready ;
  logic [7:0] o_lpddr_axi_m_subip_bid    ;
  logic [1:0] o_lpddr_axi_m_subip_bresp  ;
  logic o_lpddr_axi_m_subip_bvalid ;
  logic o_lpddr_axi_m_subip_arready;
  logic [7:0] o_lpddr_axi_m_subip_rid    ;
  logic [255:0] o_lpddr_axi_m_subip_rdata  ;
  logic [1:0] o_lpddr_axi_m_subip_rresp  ;
  logic o_lpddr_axi_m_subip_rlast  ;
  logic o_lpddr_axi_m_subip_rvalid ;
  logic axi_hw_lp_gates_clock;

  axe_axi_multicut_flat #(
    .AxiAddrWidth (33),
    .AxiIdWidth (8),
    .AxiDataWidth (256),
    .NumCuts(1)
  ) o_lpddr_axi_m_spill_flat (
    .i_clk(lpddr_clk),
    .i_rst_n(ctrl_rst_n),
    .i_axi_s_aw_id(i_lpddr_axi_m_awid),
    .i_axi_s_aw_addr(i_lpddr_axi_m_awaddr[32:0]),  // LPDDR is only 33b, NoC internally uses 33b as well, but top-level integration pads to 40b using 0-ties
    .i_axi_s_aw_len(i_lpddr_axi_m_awlen),
    .i_axi_s_aw_size(i_lpddr_axi_m_awsize),
    .i_axi_s_aw_burst(i_lpddr_axi_m_awburst),
    .i_axi_s_aw_lock(i_lpddr_axi_m_awlock),
    .i_axi_s_aw_cache(i_lpddr_axi_m_awcache),
    .i_axi_s_aw_prot(i_lpddr_axi_m_awprot),
    .i_axi_s_aw_qos(i_lpddr_axi_m_awqos),
    .i_axi_s_aw_region(i_lpddr_axi_m_awregion),
    .i_axi_s_aw_user('0),
    .i_axi_s_aw_valid(i_lpddr_axi_m_awvalid),
    .o_axi_s_aw_ready(o_lpddr_axi_m_awready),
    .i_axi_s_w_data(i_lpddr_axi_m_wdata),
    .i_axi_s_w_strb(i_lpddr_axi_m_wstrb),
    .i_axi_s_w_last(i_lpddr_axi_m_wlast),
    .i_axi_s_w_user('0),
    .i_axi_s_w_valid(i_lpddr_axi_m_wvalid),
    .o_axi_s_w_ready(o_lpddr_axi_m_wready),
    .o_axi_s_b_id(o_lpddr_axi_m_bid),
    .o_axi_s_b_resp(o_lpddr_axi_m_bresp),
    .o_axi_s_b_user(),
    .o_axi_s_b_valid(o_lpddr_axi_m_bvalid),
    .i_axi_s_b_ready(i_lpddr_axi_m_bready),
    .i_axi_s_ar_id(i_lpddr_axi_m_arid),
    .i_axi_s_ar_addr(i_lpddr_axi_m_araddr[32:0]), // LPDDR is only 33b, NoC internally uses 33b as well, but top-level integration pads to 40b using 0-ties
    .i_axi_s_ar_len(i_lpddr_axi_m_arlen),
    .i_axi_s_ar_size(i_lpddr_axi_m_arsize),
    .i_axi_s_ar_burst(i_lpddr_axi_m_arburst),
    .i_axi_s_ar_lock(i_lpddr_axi_m_arlock),
    .i_axi_s_ar_cache(i_lpddr_axi_m_arcache),
    .i_axi_s_ar_prot(i_lpddr_axi_m_arprot),
    .i_axi_s_ar_qos(i_lpddr_axi_m_arqos),
    .i_axi_s_ar_region(i_lpddr_axi_m_arregion),
    .i_axi_s_ar_user('0),
    .i_axi_s_ar_valid(i_lpddr_axi_m_arvalid),
    .o_axi_s_ar_ready(o_lpddr_axi_m_arready),
    .o_axi_s_r_id(o_lpddr_axi_m_rid),
    .o_axi_s_r_data(o_lpddr_axi_m_rdata),
    .o_axi_s_r_resp(o_lpddr_axi_m_rresp),
    .o_axi_s_r_last(o_lpddr_axi_m_rlast),
    .o_axi_s_r_user(),
    .o_axi_s_r_valid(o_lpddr_axi_m_rvalid),
    .i_axi_s_r_ready(i_lpddr_axi_m_rready),
    .o_axi_m_aw_id(i_lpddr_axi_m_subip_awid),
    .o_axi_m_aw_addr(i_lpddr_axi_m_subip_awaddr),
    .o_axi_m_aw_len(i_lpddr_axi_m_subip_awlen),
    .o_axi_m_aw_size(i_lpddr_axi_m_subip_awsize),
    .o_axi_m_aw_burst(i_lpddr_axi_m_subip_awburst),
    .o_axi_m_aw_lock(i_lpddr_axi_m_subip_awlock),
    .o_axi_m_aw_cache(i_lpddr_axi_m_subip_awcache),
    .o_axi_m_aw_prot(i_lpddr_axi_m_subip_awprot),
    .o_axi_m_aw_qos(i_lpddr_axi_m_subip_awqos),
    .o_axi_m_aw_region(i_lpddr_axi_m_subip_awregion),
    .o_axi_m_aw_valid(i_lpddr_axi_m_subip_awvalid),
    .o_axi_m_aw_user(),
    .i_axi_m_aw_ready(o_lpddr_axi_m_subip_awready & (~axi_hw_lp_gates_clock)), // SNPS recommend to pull the ready of the axi signal low when disabling the clock using the AXI LP interface
    .o_axi_m_w_data(i_lpddr_axi_m_subip_wdata),
    .o_axi_m_w_strb(i_lpddr_axi_m_subip_wstrb),
    .o_axi_m_w_last(i_lpddr_axi_m_subip_wlast),
    .o_axi_m_w_user(),
    .o_axi_m_w_valid(i_lpddr_axi_m_subip_wvalid),
    .i_axi_m_w_ready(o_lpddr_axi_m_subip_wready & (~axi_hw_lp_gates_clock)), // SNPS recommend to pull the ready of the axi signal low when disabling the clock using the AXI LP interface
    .i_axi_m_b_id(o_lpddr_axi_m_subip_bid),
    .i_axi_m_b_resp(o_lpddr_axi_m_subip_bresp),
    .i_axi_m_b_user('0),
    .i_axi_m_b_valid(o_lpddr_axi_m_subip_bvalid),
    .o_axi_m_b_ready(i_lpddr_axi_m_subip_bready),
    .o_axi_m_ar_id(i_lpddr_axi_m_subip_arid),
    .o_axi_m_ar_addr(i_lpddr_axi_m_subip_araddr),
    .o_axi_m_ar_len(i_lpddr_axi_m_subip_arlen),
    .o_axi_m_ar_size(i_lpddr_axi_m_subip_arsize),
    .o_axi_m_ar_burst(i_lpddr_axi_m_subip_arburst),
    .o_axi_m_ar_lock(i_lpddr_axi_m_subip_arlock),
    .o_axi_m_ar_cache(i_lpddr_axi_m_subip_arcache),
    .o_axi_m_ar_prot(i_lpddr_axi_m_subip_arprot),
    .o_axi_m_ar_qos(i_lpddr_axi_m_subip_arqos),
    .o_axi_m_ar_region(i_lpddr_axi_m_subip_arregion),
    .o_axi_m_ar_user(),
    .o_axi_m_ar_valid(i_lpddr_axi_m_subip_arvalid),
    .i_axi_m_ar_ready(o_lpddr_axi_m_subip_arready & (~axi_hw_lp_gates_clock)), // SNPS recommend to pull the ready of the axi signal low when disabling the clock using the AXI LP interface
    .i_axi_m_r_id(o_lpddr_axi_m_subip_rid),
    .i_axi_m_r_data(o_lpddr_axi_m_subip_rdata),
    .i_axi_m_r_resp(o_lpddr_axi_m_subip_rresp),
    .i_axi_m_r_last(o_lpddr_axi_m_subip_rlast),
    .i_axi_m_r_user('0),
    .i_axi_m_r_valid(o_lpddr_axi_m_subip_rvalid),
    .o_axi_m_r_ready(i_lpddr_axi_m_subip_rready)
  );

  //-------------------------------
  // AXI low power interface
  //-------------------------------
  logic csysreq, cactive, csysack;
  logic axi_lp_en_sync;
  logic [LPDDR_HW_LP_IDLE_DELAYW-1:0] axi_lp_idle_delay_sync;

  // SYNC AXI LP_EN from ao clock domain to lpddr clock domain
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) axi_lp_en_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (ctrl_rst_n),
    .i_d (reg2hw.axi_low_power_control.lp_en.q),
    .o_q (axi_lp_en_sync)
  );

  // SYNC AXI LP idle delay from ao clock domain to lpddr clock domain
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [LPDDR_HW_LP_IDLE_DELAYW-1:0])
  ) axi_lp_idle_delay_sync_inst (
    /// Source domain clock, positive edge triggered
    .i_src_clk (i_ao_clk),
    /// Source domain asynchronous reset, active low
    .i_src_rst_n (i_ao_rst_n),
    /// Source domain input enable (sync this data)
    .i_src_en (reg2hw.axi_low_power_control.lp_en.q),
    /// Source data input
    .i_src_data (reg2hw.axi_low_power_control.idle_delay.q),
    /// Source domain busy flag, new data sync requests are ignored while high
    .o_src_busy (),

    /// Destination domain clock, positive edge triggered
    .i_dst_clk (lpddr_clk),
    /// Destination domain asynchronous reset, active low
    .i_dst_rst_n (ctrl_rst_n),
    /// Destination domain data
    .o_dst_data (axi_lp_idle_delay_sync),
    /// Destination domain update pulse (new data this cycle)
    .o_dst_update ()
  );

  // SNPS advices to use synchroniser on cactive
  logic cactive_sync;
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) axi_lp_cactive_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (ctrl_rst_n),
    .i_d (cactive),
    .o_q (cactive_sync)
  );

  axe_ccl_clk_lp_control #(
    .IdleDelayW (LPDDR_HW_LP_IDLE_DELAYW)
  ) i_axi_low_power_interface (
    .i_clk (lpddr_clk),
    .i_rst_n (ctrl_rst_n),
    /// Clock_gate bypass enable
    .i_scan_en (1'b0),
    /// Low Power enable
    .i_low_power_en (axi_lp_en_sync),
    /// Low Power active, clock is gated when set
    .o_low_power_active (axi_hw_lp_gates_clock),
    /// Low Power idle delay, wait this amount of cycles before going into low power state
    .i_low_power_idle_delay (axi_lp_idle_delay_sync),

    /////////////////////////
    // Low Power Interface //
    /////////////////////////
    /// QREQn
    .o_qreq_n (csysreq),
    /// QDENY
    .i_qdeny (1'b0),
    /// QACCEPTn
    .i_qaccept_n (csysack),
    /// QACTIVE
    .i_qactive (cactive_sync),

    /// Output gated clock
    .o_clk (aclk_clk_buf_out)
  );

  //-------------------------------
  // Additional AXI interface signal (non-std). given csr control.
  //-------------------------------
  logic  arurgent_ao_sync, arurgent;
  logic  awurgent_ao_sync, awurgent;
  assign arurgent_ao_sync = reg2hw.config_lpddr.arurgent.q;
  assign awurgent_ao_sync = reg2hw.config_lpddr.awurgent.q;
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) arurgent_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (cfg_rst_n),
    .i_d (arurgent_ao_sync),
    .o_q (arurgent)
  );
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) awurgent_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (cfg_rst_n),
    .i_d (awurgent_ao_sync),
    .o_q (awurgent)
  );

  // Flags about evens in the read and write address queues. Connected to csrs counter for debug, otherwise not used
  logic raq_split;
  logic raqb_pop;
  logic raqb_push;
  logic raqr_pop;
  logic raqr_push;
  logic waq_pop;
  logic waq_push;
  logic waq_split;

  // ADDRESS FIFO position indicators, connected to csrs for debug, otherwise not used.
  logic [5:0] raqb_wcount, raqb_wcount_ao_sync;
  logic [5:0] raqr_wcount, raqr_wcount_ao_sync;
  logic [5:0] waq_wcount, waq_wcount_ao_sync;
  assign hw2reg.debug_address_fifos_lpddr.raqb_wcount.d = raqb_wcount_ao_sync;
  assign hw2reg.debug_address_fifos_lpddr.raqr_wcount.d = raqr_wcount_ao_sync;
  assign hw2reg.debug_address_fifos_lpddr.waq_wcount.d = waq_wcount_ao_sync;
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [5:0])
  ) raqb_wcount_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (raqb_wcount),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (raqb_wcount_ao_sync),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [5:0])
  ) raqr_wcount_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (raqr_wcount),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (raqr_wcount_ao_sync),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [5:0])
  ) waq_wcount_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (waq_wcount),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (waq_wcount_ao_sync),
    .o_dst_update ()
  );

  //--------------------------------
  // DDRC Low power interface
  //--------------------------------
  logic csysreq_ddrc, cactive_ddrc, csysack_ddrc;
  logic ddrc_lp_en_sync;
  logic [LPDDR_HW_LP_IDLE_DELAYW-1:0] ddrc_lp_idle_delay_sync;
  logic ddrc_hw_lp_gates_clock;

  // SYNC AXI LP_EN from ao clock domain to lpddr clock domain
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) ddrc_lp_en_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (ctrl_rst_n),
    .i_d (reg2hw.ddrc_low_power_control.lp_en.q),
    .o_q (ddrc_lp_en_sync)
  );

  // SYNC AXI LP idle delay from ao clock domain to lpddr clock domain
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [LPDDR_HW_LP_IDLE_DELAYW-1:0])
  ) ddrc_lp_idle_delay_sync_inst (
    /// Source domain clock, positive edge triggered
    .i_src_clk (i_ao_clk),
    /// Source domain asynchronous reset, active low
    .i_src_rst_n (i_ao_rst_n),
    /// Source domain input enable (sync this data)
    .i_src_en (reg2hw.ddrc_low_power_control.lp_en.q),
    /// Source data input
    .i_src_data (reg2hw.ddrc_low_power_control.idle_delay.q),
    /// Source domain busy flag, new data sync requests are ignored while high
    .o_src_busy (),

    /// Destination domain clock, positive edge triggered
    .i_dst_clk (lpddr_clk),
    /// Destination domain asynchronous reset, active low
    .i_dst_rst_n (ctrl_rst_n),
    /// Destination domain data
    .o_dst_data (ddrc_lp_idle_delay_sync),
    /// Destination domain update pulse (new data this cycle)
    .o_dst_update ()
  );

  // SNPS advices to use synchroniser on csysack
  logic cactive_ddrc_sync;
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) ddrc_lp_cactive_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (ctrl_rst_n),
    .i_d (cactive_ddrc),
    .o_q (cactive_ddrc_sync)
  );

  axe_ccl_clk_lp_control #(
    .IdleDelayW (LPDDR_HW_LP_IDLE_DELAYW)
  ) i_ddrc_low_power_interface (
    .i_clk (lpddr_clk),
    .i_rst_n (ctrl_rst_n),
    /// Clock_gate bypass enable
    .i_scan_en (1'b0),
    /// Low Power enable
    .i_low_power_en (ddrc_lp_en_sync),
    /// Low Power active, clock is gated when set
    .o_low_power_active (ddrc_hw_lp_gates_clock),
    /// Low Power idle delay, wait this amount of cycles before going into low power state
    .i_low_power_idle_delay (ddrc_lp_idle_delay_sync),

    /////////////////////////
    // Low Power Interface //
    /////////////////////////
    /// QREQn
    .o_qreq_n (csysreq_ddrc),
    /// QDENY
    .i_qdeny (1'b0),
    /// QACCEPTn
    .i_qaccept_n (csysack_ddrc),
    /// QACTIVE
    .i_qactive (cactive_ddrc_sync),

    /// Output gated clock
    .o_clk (core_ddrc_core_clk_clk_buf_out)
  );

  // Tie the csysmode to always select HW low power signaling and not HW fast frequency signaling which we do not support.
  // FROM SNPS DATABOOK
  // A hardware low-power entry request and a HWFFC request cannot be accepted simulta-
  // neously. The signal csysmode_ddrc indicates which action to take place. When the 
  // signal csysreq_ddrc is de-asserted, ‘0’ on csysmode_ddrc indicates that a hardware 
  // low-power entry request is required and the DDRCTL attempts to enter the self-refresh 
  // operating mode. See the section “DDRC Hardware Low-Power Interface” on page 270. 
  // Clocks may then be removed but HWFFC is not executed and the signal 
  // csysfrequency_ddrc is ignored.
  logic csysmode_ddrc;
  assign csysmode_ddrc = '0;

  // Tie off signals related to HW fast frequency change. We do not support this.
  logic csysdiscamdrain_ddrc;
  assign csysdiscamdrain_ddrc = '0;
  logic [4:0] csysfrequency_ddrc;
  assign csysfrequency_ddrc = '0;
  logic csysfsp_ddrc;
  assign csysfsp_ddrc = '0;

  //-----------------
  // APB security
  //-----------------
  // 7.3.1.2 PPROT_PIN Configuration and Purpose
  // -  Typically tied off to a particular value, sometimes fuse programmed, or in some highly secure environments this is randomized by a different security engine.
  // -  The PHY only responds to APB requests where PPROT_APB matches the value of PPROT_PIN.
  // This functionality prevents unauthorized accesses to the registers. A hardware configurable port for comparison against the value on PPROT during activity PPROT_PIN[2:0] is a static value provided by the SOC.
  logic [2:0] pprot_pin;
  // Solution used in Omega, just use apb pprot signal on pprot pin as well.
  assign pprot_pin = piped_lpddr_cfg_apb4_s_pprot;

  //-----------------
  // ECC related signals
  //------------------
  logic dis_regs_ecc_syndrome, dis_regs_ecc_syndrome_ao_sync;
  assign dis_regs_ecc_syndrome_ao_sync = reg2hw.config_lpddr.dis_regs_ecc_syndrome.q;
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) dis_regs_ecc_syndrome_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (ctrl_rst_n),
    .i_d (dis_regs_ecc_syndrome_ao_sync),
    .o_q (dis_regs_ecc_syndrome)
  );

  //-----------------
  // CAM credit counters
  //-----------------
  logic [6:0] hpr_credit_cnt, hpr_credit_cnt_ao_synced;
  logic [6:0] lpr_credit_cnt, lpr_credit_cnt_ao_synced;
  logic [6:0] wr_credit_cnt, wr_credit_cnt_ao_synced;
  logic [6:0] wrecc_credit_cnt, wrecc_credit_cnt_ao_synced;
  assign hw2reg.debug_cam_credit_count_lpddr.hpr_credit_cnt.d = hpr_credit_cnt_ao_synced;
  assign hw2reg.debug_cam_credit_count_lpddr.lpr_credit_cnt.d = lpr_credit_cnt_ao_synced;
  assign hw2reg.debug_cam_credit_count_lpddr.wr_credit_cnt.d = wr_credit_cnt_ao_synced;
  assign hw2reg.debug_cam_credit_count_lpddr.wrecc_credit_cnt.d = wrecc_credit_cnt_ao_synced;
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [6:0])
  ) hpr_credit_cnt_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (hpr_credit_cnt),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (hpr_credit_cnt_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [6:0])
  ) lpr_credit_cnt_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (lpr_credit_cnt),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (lpr_credit_cnt_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [6:0])
  ) wr_credit_cnt_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (wr_credit_cnt),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (wr_credit_cnt_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [6:0])
  ) wrecc_credit_cnt_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (wrecc_credit_cnt),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (wrecc_credit_cnt_ao_synced),
    .o_dst_update ()
  );

  //-------------------
  // Mode register read
  //-----------------
  logic [31:0] hif_mrr_data, hif_mrr_data_ao_synced;
  logic hif_mrr_data_valid;
  assign hw2reg.hif_mode_read.d = hif_mrr_data_ao_synced;
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [31:0])
  ) hif_mrr_data_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en (hif_mrr_data_valid),
    .i_src_data (hif_mrr_data),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (hif_mrr_data_ao_synced),
    .o_dst_update ()
  );

  //-----------------
  // Performance counters
  //-----------------
  logic  perf_dfi_rd_data_cycles;
  logic  perf_dfi_wr_data_cycles;
  logic  perf_hif_hi_pri_rd;
  logic  perf_hif_rd;
  logic  perf_hif_rd_or_wr;
  logic  perf_hif_rmw;
  logic  perf_hif_wr;
  logic  perf_hpr_req_with_nocredit;
  logic  perf_hpr_xact_when_critical;
  logic  perf_ie_blk_hazard;
  logic  perf_lpr_req_with_nocredit;
  logic  perf_lpr_xact_when_critical;
  logic  perf_op_is_activate;
  logic  perf_op_is_cas;
  logic  perf_op_is_cas_wck_sus;
  logic  perf_op_is_cas_ws;
  logic  perf_op_is_cas_ws_off;
  logic  perf_op_is_crit_ref;
  logic  perf_op_is_dqsosc_mpc;
  logic  perf_op_is_dqsosc_mrr;
  logic  perf_op_is_enter_dsm;
  logic  perf_op_is_load_mode;
  logic  perf_op_is_mwr;
  logic  perf_op_is_precharge;
  logic  perf_op_is_rd;
  logic  perf_op_is_rd_activate;
  logic  perf_op_is_rd_or_wr;
  logic  perf_op_is_refresh;
  logic  perf_op_is_rfm;
  logic  perf_op_is_spec_ref;
  logic  perf_op_is_tcr_mrr;
  logic  perf_op_is_wr;
  logic  perf_op_is_zqlatch;
  logic  perf_op_is_zqstart;
  logic  perf_precharge_for_other;
  logic  perf_precharge_for_rdwr;
  logic  perf_raw_hazard;
  logic  perf_rdwr_transitions;
  logic  perf_visible_window_limit_reached_rd;
  logic  perf_visible_window_limit_reached_wr;
  logic  perf_war_hazard;
  logic  perf_waw_hazard;
  logic  perf_wr_xact_when_critical;
  logic  perf_write_combine;
  logic  perf_write_combine_noecc;
  logic  perf_write_combine_wrecc;
  // Multi-bit counter increment signals per rank split in separate signals.
  logic perf_selfref_mode_rank_0;
  logic perf_selfref_mode_rank_1;
  logic perf_op_is_enter_powerdown_rank_0;
  logic perf_op_is_enter_powerdown_rank_1;
  logic perf_op_is_enter_selfref_rank_0;
  logic perf_op_is_enter_selfref_rank_1;

  // Debug signals, no counter signals
  logic       perf_rank, perf_rank_ao_synced;
  logic [2:0] perf_bank, perf_bank_ao_synced;
  logic [1:0] perf_bg, perf_bg_ao_synced;
  logic debug_cam_valid;
  assign debug_cam_valid = perf_op_is_rd_or_wr | perf_op_is_rd | perf_op_is_wr;
  assign hw2reg.debug_cam_schedule_lpddr.perf_rank.d = perf_rank_ao_synced;
  assign hw2reg.debug_cam_schedule_lpddr.perf_bank.d = perf_bank_ao_synced;
  assign hw2reg.debug_cam_schedule_lpddr.perf_bank_group.d = perf_bg_ao_synced;
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic)
  ) perf_rank_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en (debug_cam_valid),
    .i_src_data (perf_rank),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (perf_rank_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [2:0])
  ) perf_bank_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en (debug_cam_valid),
    .i_src_data (perf_bank),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (perf_bank_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [1:0])
  ) perf_bg_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en (debug_cam_valid),
    .i_src_data (perf_bg),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (perf_bg_ao_synced),
    .o_dst_update ()
  );

  // Digital test output signal (PHY signals for debug)
  logic [1:0] dwc_lpddr5xphy_dto;

  // PHY interrupts come out of a single bundle that is active low.
  // See section 7.5 of PUB databook
  // Assign to individual interrupt signals here, and invert to active high for PLIC handling
  // Not all 16 bits are actually used. Mapping taken from PhyInterruptStatus register in the PUB databook
  logic [15:0] phyint_n;
  assign o_phy_pie_prog_err_intr = ~phyint_n[12];
  assign o_phy_ecc_err_intr = ~phyint_n[11];
  assign o_phy_rdfptrchk_err_intr = ~phyint_n[10];
  assign o_phy_pie_parity_err_intr = ~phyint_n[9];
  assign o_phy_acsm_parity_err_intr = ~phyint_n[8];
  assign o_phy_trng_fail_intr = ~phyint_n[2];
  assign o_phy_init_cmplt_intr = ~phyint_n[1];
  assign o_phy_trng_cmplt_intr = ~phyint_n[0];

  // Observability connections
  assign o_lpddr_obs[0] = dwc_lpddr5xphy_pll_lock;
  assign o_lpddr_obs[1] = dwc_lpddr5xphy_pmu_busy;
  assign o_lpddr_obs[2] = o_phy_pie_prog_err_intr;
  assign o_lpddr_obs[3] = o_phy_rdfptrchk_err_intr;
  assign o_lpddr_obs[4] = o_phy_trng_fail_intr;
  assign o_lpddr_obs[5] = o_phy_init_cmplt_intr;
  assign o_lpddr_obs[6] = o_phy_trng_cmplt_intr;
  assign o_lpddr_obs[8:7] = dwc_lpddr5xphy_dto;
  assign o_lpddr_obs[9] = o_ctrl_sbr_done_intr;
  assign o_lpddr_obs[10] = o_ctrl_derate_temp_limit_intr;
  assign o_lpddr_obs[11] = o_ctrl_ecc_ap_err_intr;
  assign o_lpddr_obs[12] = o_ctrl_ecc_corrected_err_intr;
  assign o_lpddr_obs[13] = o_ctrl_ecc_uncorrected_err_intr;
  assign o_lpddr_obs[14] = axi_hw_lp_gates_clock;
  assign o_lpddr_obs[15] = ddrc_hw_lp_gates_clock;


  //-------------------------------
  // JTAG TDR integration of snps TDR
  //-------------------------------

wire to_DdrPhyCsrCmdTdrCaptureEn,to_DdrPhyCsrCmdTdrShiftEn,to_DdrPhyCsrCmdTdrUpdateEn;
wire to_DdrPhyCsrRdDataTdrCaptureEn,to_DdrPhyCsrRdDataTdrShiftEn,to_DdrPhyCsrRdDataTdrUpdateEn;
wire to_WSI,from_DdrPhyCsrCmdTdr_Tdo,from_DdrPhyCsrRdDataTdr_Tdo;

dwc_ddrphy_jtag_dfttdrs_cmd dwc_ddrphy_jtag_dfttdrs_Cmd_inst (
        .ijtag_sel            (),
        .tck               (),
        .scan_in           (),
        .scan_out          (),
        .reset             (),
        .shift_en          (),
        .capture_en        (),
        .update_en         (),
        .to_DdrPhyCsrCmdTdrCaptureEn(to_DdrPhyCsrCmdTdrCaptureEn),
        .to_DdrPhyCsrCmdTdrShiftEn(to_DdrPhyCsrCmdTdrShiftEn),
        .to_DdrPhyCsrCmdTdrUpdateEn(to_DdrPhyCsrCmdTdrUpdateEn),
        .to_WSI(),
	.from_DdrPhyCsrCmdTdr_Tdo(from_DdrPhyCsrCmdTdr_Tdo)
);

dwc_ddrphy_jtag_dfttdrs_RdData dwc_ddrphy_jtag_dfttdrs_RdData_inst (
        .ijtag_sel         (),
        .tck               (),
        .scan_in           (),
        .scan_out          (),
        .reset             (),
        .shift_en          (),
        .capture_en        (),
        .update_en         (),
        .to_DdrPhyCsrRdDataTdrCaptureEn(to_DdrPhyCsrRdDataTdrCaptureEn),
        .to_DdrPhyCsrRdDataTdrShiftEn(to_DdrPhyCsrRdDataTdrShiftEn),
        .to_DdrPhyCsrRdDataTdrUpdateEn(to_DdrPhyCsrRdDataTdrUpdateEn),
        .to_WSI(to_WSI),
        .from_DdrPhyCsrRdDataTdr_Tdo(from_DdrPhyCsrRdDataTdr_Tdo)
);


  //-------------------------------
  // Wrapped module instantiation
  //-------------------------------
  lpddr_subsys_wrapper u_lpddr_subsys_wrapper (
    // Clocks
    .i_pclk (pclk_clk_buf_out),
    .i_pclk_apbrw (pclk_apbrw_clk_buf_out),
    .i_aclk (aclk_clk_buf_out),
    .i_core_ddrc_core_clk (core_ddrc_core_clk_clk_buf_out),
    .i_core_ddrc_core_clk_apbrw (core_ddrc_core_clk_apbrw_clk_buf_out),
    .i_dficlk (dficlk_clk_buf_out),
    .i_sbr_clk (sbr_clk_clk_buf_out),
    .i_pllbypclk (pllbypclk_clk_buf_out),
    .i_pllrefclk (pllrefclk_clk_buf_out),
    // Resets
    .i_cfg_rst_n(cfg_rst_n),
    .i_ctrl_rst_n(ctrl_rst_n),
    .i_phy_rst(phy_rst),
    // DDRC low power interface
    .i_csysreq_ddrc(csysreq_ddrc),
    .i_csysdiscamdrain_ddrc(csysdiscamdrain_ddrc),
    .i_csysfrequency_ddrc(csysfrequency_ddrc),
    .i_csysfsp_ddrc(csysfsp_ddrc),
    .i_csysmode_ddrc(csysmode_ddrc),
    .o_cactive_ddrc(cactive_ddrc),
    .o_csysack_ddrc(csysack_ddrc),
    // AXI low power interface
    .i_csysreq(csysreq),
    .o_cactive(cactive),
    .o_csysack(csysack),
    // AXI interface
    .i_lpddr_axi_m_araddr(i_lpddr_axi_m_subip_araddr),
    .i_lpddr_axi_m_arburst(i_lpddr_axi_m_subip_arburst),
    .i_lpddr_axi_m_arcache(i_lpddr_axi_m_subip_arcache),
    .i_lpddr_axi_m_arid(i_lpddr_axi_m_subip_arid),
    .i_lpddr_axi_m_arlen(i_lpddr_axi_m_subip_arlen),
    .i_lpddr_axi_m_arlock(i_lpddr_axi_m_subip_arlock),
    .i_lpddr_axi_m_arprot(i_lpddr_axi_m_subip_arprot),
    .i_lpddr_axi_m_arqos(i_lpddr_axi_m_subip_arqos),
    .i_lpddr_axi_m_arregion(i_lpddr_axi_m_subip_arregion),
    .i_lpddr_axi_m_arsize(i_lpddr_axi_m_subip_arsize),
    .i_lpddr_axi_m_arvalid(i_lpddr_axi_m_subip_arvalid),
    .i_lpddr_axi_m_rready(i_lpddr_axi_m_subip_rready),
    .i_lpddr_axi_m_awaddr(i_lpddr_axi_m_subip_awaddr),
    .i_lpddr_axi_m_awburst(i_lpddr_axi_m_subip_awburst),
    .i_lpddr_axi_m_awcache(i_lpddr_axi_m_subip_awcache),
    .i_lpddr_axi_m_awid(i_lpddr_axi_m_subip_awid),
    .i_lpddr_axi_m_awlen(i_lpddr_axi_m_subip_awlen),
    .i_lpddr_axi_m_awlock(i_lpddr_axi_m_subip_awlock),
    .i_lpddr_axi_m_awprot(i_lpddr_axi_m_subip_awprot),
    .i_lpddr_axi_m_awqos(i_lpddr_axi_m_subip_awqos),
    .i_lpddr_axi_m_awregion(i_lpddr_axi_m_subip_awregion),
    .i_lpddr_axi_m_awsize(i_lpddr_axi_m_subip_awsize),
    .i_lpddr_axi_m_awvalid(i_lpddr_axi_m_subip_awvalid),
    .i_lpddr_axi_m_wdata(i_lpddr_axi_m_subip_wdata),
    .i_lpddr_axi_m_wlast(i_lpddr_axi_m_subip_wlast),
    .i_lpddr_axi_m_wstrb(i_lpddr_axi_m_subip_wstrb),
    .i_lpddr_axi_m_wvalid(i_lpddr_axi_m_subip_wvalid),
    .i_lpddr_axi_m_bready(i_lpddr_axi_m_subip_bready),
    .o_lpddr_axi_m_arready(o_lpddr_axi_m_subip_arready),
    .o_lpddr_axi_m_rdata(o_lpddr_axi_m_subip_rdata),
    .o_lpddr_axi_m_rid(o_lpddr_axi_m_subip_rid),
    .o_lpddr_axi_m_rlast(o_lpddr_axi_m_subip_rlast),
    .o_lpddr_axi_m_rresp(o_lpddr_axi_m_subip_rresp),
    .o_lpddr_axi_m_rvalid(o_lpddr_axi_m_subip_rvalid),
    .o_lpddr_axi_m_awready(o_lpddr_axi_m_subip_awready),
    .o_lpddr_axi_m_wready(o_lpddr_axi_m_subip_wready),
    .o_lpddr_axi_m_bid(o_lpddr_axi_m_subip_bid),
    .o_lpddr_axi_m_bresp(o_lpddr_axi_m_subip_bresp),
    .o_lpddr_axi_m_bvalid(o_lpddr_axi_m_subip_bvalid),
    .i_awurgent(awurgent),
    .i_arurgentb(arurgent),  // There is no difference in this signal between read or blue queue
    .i_arurgentr(arurgent),  // in both cases the rd_port_urgent_en register is set (see ref manual)
    .o_raq_split(raq_split),
    .o_raqb_pop(raqb_pop),
    .o_raqb_push(raqb_push),
    .o_raqb_wcount(raqb_wcount),
    .o_raqr_pop(raqr_pop),
    .o_raqr_push(raqr_push),
    .o_raqr_wcount(raqr_wcount),
    .o_waq_pop(waq_pop),
    .o_waq_push(waq_push),
    .o_waq_split(waq_split),
    .o_waq_wcount(waq_wcount),
    // APB interface
    .i_lpddr_cfg_apb_m_pprot(piped_lpddr_cfg_apb4_s_pprot),
    .i_lpddr_cfg_apb_m_paddr(piped_lpddr_cfg_apb4_s_paddr),
    .i_lpddr_cfg_apb_m_penable(piped_lpddr_cfg_apb4_s_penable),
    .i_lpddr_cfg_apb_m_psel(piped_lpddr_cfg_apb4_s_psel),
    .i_lpddr_cfg_apb_m_pstrb(piped_lpddr_cfg_apb4_s_pstrb),
    .i_lpddr_cfg_apb_m_pwdata(piped_lpddr_cfg_apb4_s_pwdata),
    .i_lpddr_cfg_apb_m_pwrite(piped_lpddr_cfg_apb4_s_pwrite),
    .o_lpddr_cfg_apb_m_prdata(piped_lpddr_cfg_apb4_s_prdata),
    .o_lpddr_cfg_apb_m_pready(piped_lpddr_cfg_apb4_s_pready),
    .o_lpddr_cfg_apb_m_pslverr(piped_lpddr_cfg_apb4_s_pslverr),
    .i_pprot_pin(pprot_pin),
    // ECC security signal
    .i_dis_regs_ecc_syndrome(dis_regs_ecc_syndrome),
    // Credit counters
    .o_hpr_credit_cnt(hpr_credit_cnt),
    .o_lpr_credit_cnt(lpr_credit_cnt),
    .o_wr_credit_cnt(wr_credit_cnt),
    .o_wrecc_credit_cnt(wrecc_credit_cnt),
    // CTRL interupts
    .o_sbr_done_intr(o_ctrl_sbr_done_intr),
    .o_derate_temp_limit_intr(o_ctrl_derate_temp_limit_intr),
    .o_ecc_ap_err_intr(o_ctrl_ecc_ap_err_intr),
    .o_ecc_corrected_err_intr(o_ctrl_ecc_corrected_err_intr),
    .o_ecc_uncorrected_err_intr(o_ctrl_ecc_uncorrected_err_intr),
    .o_rd_linkecc_corr_err_intr(o_ctrl_rd_linkecc_corr_err_intr),
    .o_rd_linkecc_uncorr_err_intr(o_ctrl_rd_linkecc_uncorr_err_intr),
    // PHY interrupts
    .o_phyint_n(phyint_n),
    // PHY PLL status
    .o_dwc_lpddr5xphy_pll_lock(dwc_lpddr5xphy_pll_lock),
    .o_dwc_lpddr5xphy_pmu_busy(dwc_lpddr5xphy_pmu_busy),
    // Mode register read output
    .o_hif_mrr_data(hif_mrr_data),
    .o_hif_mrr_data_valid(hif_mrr_data_valid),
    // Perf counter increment flags
    .o_perf_bank(perf_bank),
    .o_perf_bg(perf_bg),
    .o_perf_dfi_rd_data_cycles(perf_dfi_rd_data_cycles),
    .o_perf_dfi_wr_data_cycles(perf_dfi_wr_data_cycles),
    .o_perf_hif_hi_pri_rd(perf_hif_hi_pri_rd),
    .o_perf_hif_rd(perf_hif_rd),
    .o_perf_hif_rd_or_wr(perf_hif_rd_or_wr),
    .o_perf_hif_rmw(perf_hif_rmw),
    .o_perf_hif_wr(perf_hif_wr),
    .o_perf_hpr_req_with_nocredit(perf_hpr_req_with_nocredit),
    .o_perf_hpr_xact_when_critical(perf_hpr_xact_when_critical),
    .o_perf_ie_blk_hazard(perf_ie_blk_hazard),
    .o_perf_lpr_req_with_nocredit(perf_lpr_req_with_nocredit),
    .o_perf_lpr_xact_when_critical(perf_lpr_xact_when_critical),
    .o_perf_op_is_activate(perf_op_is_activate),
    .o_perf_op_is_cas(perf_op_is_cas),
    .o_perf_op_is_cas_wck_sus(perf_op_is_cas_wck_sus),
    .o_perf_op_is_cas_ws(perf_op_is_cas_ws),
    .o_perf_op_is_cas_ws_off(perf_op_is_cas_ws_off),
    .o_perf_op_is_crit_ref(perf_op_is_crit_ref),
    .o_perf_op_is_dqsosc_mpc(perf_op_is_dqsosc_mpc),
    .o_perf_op_is_dqsosc_mrr(perf_op_is_dqsosc_mrr),
    .o_perf_op_is_enter_dsm(perf_op_is_enter_dsm),
    .o_perf_op_is_enter_powerdown({perf_op_is_enter_powerdown_rank_1, perf_op_is_enter_powerdown_rank_0}),
    .o_perf_op_is_enter_selfref({perf_op_is_enter_selfref_rank_1,perf_op_is_enter_selfref_rank_0}),
    .o_perf_op_is_load_mode(perf_op_is_load_mode),
    .o_perf_op_is_mwr(perf_op_is_mwr),
    .o_perf_op_is_precharge(perf_op_is_precharge),
    .o_perf_op_is_rd(perf_op_is_rd),
    .o_perf_op_is_rd_activate(perf_op_is_rd_activate),
    .o_perf_op_is_rd_or_wr(perf_op_is_rd_or_wr),
    .o_perf_op_is_refresh(perf_op_is_refresh),
    .o_perf_op_is_rfm(perf_op_is_rfm),
    .o_perf_op_is_spec_ref(perf_op_is_spec_ref),
    .o_perf_op_is_tcr_mrr(perf_op_is_tcr_mrr),
    .o_perf_op_is_wr(perf_op_is_wr),
    .o_perf_op_is_zqlatch(perf_op_is_zqlatch),
    .o_perf_op_is_zqstart(perf_op_is_zqstart),
    .o_perf_precharge_for_other(perf_precharge_for_other),
    .o_perf_precharge_for_rdwr(perf_precharge_for_rdwr),
    .o_perf_rank(perf_rank),
    .o_perf_raw_hazard(perf_raw_hazard),
    .o_perf_rdwr_transitions(perf_rdwr_transitions),
    .o_perf_selfref_mode({perf_selfref_mode_rank_1, perf_selfref_mode_rank_0}),     // Increment signal per rank, split in two counters
    .o_perf_visible_window_limit_reached_rd(perf_visible_window_limit_reached_rd),
    .o_perf_visible_window_limit_reached_wr(perf_visible_window_limit_reached_wr),
    .o_perf_war_hazard(perf_war_hazard),
    .o_perf_waw_hazard(perf_waw_hazard),
    .o_perf_wr_xact_when_critical(perf_wr_xact_when_critical),
    .o_perf_write_combine(perf_write_combine),
    .o_perf_write_combine_noecc(perf_write_combine_noecc),
    .o_perf_write_combine_wrecc(perf_write_combine_wrecc),
    // SRAM control signals
    .i_acsm_pde(acsm_pde),
    .i_acsm_ret(acsm_ret),
    .i_bc_pde(bc_pde),
    .i_bc_ret(bc_ret),
    .i_dccm_pde(dccm_pde),
    .i_dccm_ret(dccm_ret),
    .i_gs_pde(gs_pde),
    .i_gs_ret(gs_ret),
    .i_iccm_pde(iccm_pde),
    .i_iccm_ret(iccm_ret),
    .i_pie_pde(pie_pde),
    .i_pie_ret(pie_ret),
    .i_wdata_pde(wdata_pde),
    .i_wdata_ret(wdata_ret),
    .o_acsm_prn(acsm_prn),
    .o_bc_prn(bc_prn),
    .o_dccm_prn(dccm_prn),
    .o_gs_prn(gs_prn),
    .o_iccm_prn(iccm_prn),
    .o_pie_prn(pie_prn),
    .o_wdata_prn(wdata_prn),
    // PHY debug signal
    .o_dwc_lpddr5xphy_dto(dwc_lpddr5xphy_dto),
    // PHY BUMPS
    .BP_MEMRESET_L(BP_MEMRESET_L),
    .BP_A (BP_A),
    .BP_ATO (BP_ATO),
    .BP_ATO_PLL (BP_ATO_PLL),
    .BP_B0_D (BP_B0_D),
    .BP_B1_D (BP_B1_D),
    .BP_B2_D (BP_B2_D),
    .BP_B3_D (BP_B3_D),
    .BP_CK0_C (BP_CK0_C),
    .BP_CK0_T (BP_CK0_T),
    .BP_CK1_C (BP_CK1_C),
    .BP_CK1_T (BP_CK1_T),
    .BP_ZN (BP_ZN)
  );

  //-------------------------
  // Performance counters
  //-------------------------
  logic flush_perf_dfi_rd_data_cycles;
  assign flush_perf_dfi_rd_data_cycles = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_dfi_rd_data_cycles_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_dfi_rd_data_cycles_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_dfi_rd_data_cycles),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_dfi_rd_data_cycles.q),
    .i_ctrl_cnt_flush   (flush_perf_dfi_rd_data_cycles),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_dfi_rd_data_cycles_count.d)
  );

  logic flush_perf_counter_dfi_wr_data_cycles;
  assign flush_perf_counter_dfi_wr_data_cycles = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_dfi_wr_data_cycles_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_dfi_wr_data_cycles_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_dfi_wr_data_cycles),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_dfi_wr_data_cycles.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_dfi_wr_data_cycles),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_dfi_wr_data_cycles_count.d)
  );

  logic flush_perf_counter_hif_hi_pri_rd;
  assign flush_perf_counter_hif_hi_pri_rd = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_hi_pri_rd_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_hi_pri_rd_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_hi_pri_rd),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_hi_pri_rd.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_hi_pri_rd),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_hi_pri_rd_count.d)
  );

  logic flush_perf_counter_hif_rd;
  assign flush_perf_counter_hif_rd = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_rd_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_rd_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_rd),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_rd.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_rd),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_rd_count.d)
  );

  logic flush_perf_counter_hif_rd_or_wr;
  assign flush_perf_counter_hif_rd_or_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_rd_or_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_rd_or_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_rd_or_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_rd_or_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_rd_or_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_rd_or_wr_count.d)
  );

  logic flush_perf_counter_hif_rmw;
  assign flush_perf_counter_hif_rmw = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_rmw_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_rmw_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_rmw),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_rmw.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_rmw),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_rmw_count.d)
  );

  logic flush_perf_counter_hif_wr;
  assign flush_perf_counter_hif_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_wr_count.d)
  );

  logic flush_perf_counter_hpr_req_with_nocredit;
  assign flush_perf_counter_hpr_req_with_nocredit = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hpr_req_with_nocredit_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hpr_req_with_nocredit_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hpr_req_with_nocredit),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hpr_req_with_nocredit.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hpr_req_with_nocredit),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hpr_req_with_nocredit_count.d)
  );

  logic flush_perf_counter_hpr_xact_when_critical;
  assign flush_perf_counter_hpr_xact_when_critical = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hpr_xact_when_critical_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hpr_xact_when_critical_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hpr_xact_when_critical),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hpr_xact_when_critical.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hpr_xact_when_critical),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hpr_xact_when_critical_count.d)
  );

  logic flush_perf_counter_ie_blk_hazard;
  assign flush_perf_counter_ie_blk_hazard = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_ie_blk_hazard_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_ie_blk_hazard_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_ie_blk_hazard),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_ie_blk_hazard.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_ie_blk_hazard),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_ie_blk_hazard_count.d)
  );

  logic flush_perf_counter_lpr_req_with_nocredit;
  assign flush_perf_counter_lpr_req_with_nocredit = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_lpr_req_with_nocredit_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_lpr_req_with_nocredit_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_lpr_req_with_nocredit),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_lpr_req_with_nocredit.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_lpr_req_with_nocredit),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_lpr_req_with_nocredit_count.d)
  );

  logic flush_perf_counter_lpr_xact_when_critical;
  assign flush_perf_counter_lpr_xact_when_critical = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_lpr_xact_when_critical_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_lpr_xact_when_critical_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_lpr_xact_when_critical),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_lpr_xact_when_critical.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_lpr_xact_when_critical),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_lpr_xact_when_critical_count.d)
  );

  logic flush_perf_counter_op_is_activate;
  assign flush_perf_counter_op_is_activate = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_activate_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_activate_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_activate),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_activate.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_activate),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_activate_count.d)
  );

  logic flush_perf_counter_op_is_cas;
  assign flush_perf_counter_op_is_cas = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_cas_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_cas_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_cas),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_cas.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_cas),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_cas_count.d)
  );

  logic flush_perf_counter_op_is_cas_wck_sus;
  assign flush_perf_counter_op_is_cas_wck_sus = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_cas_wck_sus_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_cas_wck_sus_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_cas_wck_sus),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_cas_wck_sus.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_cas_wck_sus),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_cas_wck_sus_count.d)
  );

  logic flush_perf_counter_op_is_cas_ws;
  assign flush_perf_counter_op_is_cas_ws = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_cas_ws_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_cas_ws_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_cas_ws),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_cas_ws.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_cas_ws),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_cas_ws_count.d)
  );

  logic flush_perf_counter_op_is_cas_ws_off;
  assign flush_perf_counter_op_is_cas_ws_off = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_cas_ws_off_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_cas_ws_off_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_cas_ws_off),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_cas_ws_off.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_cas_ws_off),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_cas_ws_off_count.d)
  );

  logic flush_perf_counter_op_is_crit_ref;
  assign flush_perf_counter_op_is_crit_ref = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_crit_ref_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_crit_ref_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_crit_ref),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_crit_ref.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_crit_ref),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_crit_ref_count.d)
  );

  logic flush_perf_counter_op_is_dqsosc_mpc;
  assign flush_perf_counter_op_is_dqsosc_mpc = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_dqsosc_mpc_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_dqsosc_mpc_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_dqsosc_mpc),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_dqsosc_mpc.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_dqsosc_mpc),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_dqsosc_mpc_count.d)
  );

  logic flush_perf_counter_op_is_dqsosc_mrr;
  assign flush_perf_counter_op_is_dqsosc_mrr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_dqsosc_mrr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_dqsosc_mrr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_dqsosc_mrr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_dqsosc_mrr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_dqsosc_mrr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_dqsosc_mrr_count.d)
  );

  logic flush_perf_counter_op_is_enter_dsm;
  assign flush_perf_counter_op_is_enter_dsm = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_dsm_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_dsm_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_dsm),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_dsm.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_dsm),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_dsm_count.d)
  );

  logic flush_perf_counter_op_is_enter_powerdown_rank_0;
  assign flush_perf_counter_op_is_enter_powerdown_rank_0 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_powerdown_rank_0_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_powerdown_rank_0_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_powerdown_rank_0),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_powerdown_rank_0.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_powerdown_rank_0),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_powerdown_rank_0_count.d)
  );

  logic flush_perf_counter_op_is_enter_powerdown_rank_1;
  assign flush_perf_counter_op_is_enter_powerdown_rank_1 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_powerdown_rank_1_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_powerdown_rank_1_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_powerdown_rank_1),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_powerdown_rank_1.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_powerdown_rank_1),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_powerdown_rank_1_count.d)
  );

  logic flush_perf_counter_op_is_enter_selfref_rank_0;
  assign flush_perf_counter_op_is_enter_selfref_rank_0 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_selfref_rank_0_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_selfref_rank_0_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_selfref_rank_0),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_selfref_rank_0.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_selfref_rank_0),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_selfref_rank_0_count.d)
  );

  logic flush_perf_counter_op_is_enter_selfref_rank_1;
  assign flush_perf_counter_op_is_enter_selfref_rank_1 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_selfref_rank_1_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_selfref_rank_1_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_selfref_rank_1),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_selfref_rank_1.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_selfref_rank_1),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_selfref_rank_1_count.d)
  );

  logic flush_perf_counter_op_is_load_mode;
  assign flush_perf_counter_op_is_load_mode = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_load_mode_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_load_mode_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_load_mode),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_load_mode.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_load_mode),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_load_mode_count.d)
  );

  logic flush_perf_counter_op_is_mwr;
  assign flush_perf_counter_op_is_mwr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_mwr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_mwr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_mwr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_mwr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_mwr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_mwr_count.d)
  );

  logic flush_perf_counter_op_is_precharge;
  assign flush_perf_counter_op_is_precharge = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_precharge_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_precharge_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_precharge),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_precharge.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_precharge),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_precharge_count.d)
  );

  logic flush_perf_counter_op_is_rd;
  assign flush_perf_counter_op_is_rd = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_rd_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_rd_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_rd),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_rd.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_rd),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_rd_count.d)
  );

  logic flush_perf_counter_op_is_rd_activate;
  assign flush_perf_counter_op_is_rd_activate = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_rd_activate_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_rd_activate_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_rd_activate),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_rd_activate.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_rd_activate),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_rd_activate_count.d)
  );

  logic flush_perf_counter_op_is_rd_or_wr;
  assign flush_perf_counter_op_is_rd_or_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_rd_or_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_rd_or_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_rd_or_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_rd_or_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_rd_or_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_rd_or_wr_count.d)
  );

  logic flush_perf_counter_op_is_refresh;
  assign flush_perf_counter_op_is_refresh = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_refresh_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_refresh_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_refresh),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_refresh.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_refresh),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_refresh_count.d)
  );

  logic flush_perf_counter_op_is_rfm;
  assign flush_perf_counter_op_is_rfm = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_rfm_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_rfm_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_rfm),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_rfm.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_rfm),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_rfm_count.d)
  );

  logic flush_perf_counter_op_is_spec_ref;
  assign flush_perf_counter_op_is_spec_ref = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_spec_ref_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_spec_ref_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_spec_ref),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_spec_ref.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_spec_ref),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_spec_ref_count.d)
  );

  logic flush_perf_counter_op_is_tcr_mrr;
  assign flush_perf_counter_op_is_tcr_mrr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_tcr_mrr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_tcr_mrr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_tcr_mrr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_tcr_mrr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_tcr_mrr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_tcr_mrr_count.d)
  );

  logic flush_perf_counter_op_is_wr;
  assign flush_perf_counter_op_is_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_wr_count.d)
  );

  logic flush_perf_counter_op_is_zqlatch;
  assign flush_perf_counter_op_is_zqlatch = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_zqlatch_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_zqlatch_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_zqlatch),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_zqlatch.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_zqlatch),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_zqlatch_count.d)
  );

  logic flush_perf_counter_op_is_zqstart;
  assign flush_perf_counter_op_is_zqstart = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_zqstart_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_zqstart_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_zqstart),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_zqstart.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_zqstart),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_zqstart_count.d)
  );

  logic flush_perf_counter_precharge_for_other;
  assign flush_perf_counter_precharge_for_other = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_precharge_for_other_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_precharge_for_other_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_precharge_for_other),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_precharge_for_other.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_precharge_for_other),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_precharge_for_other_count.d)
  );

  logic flush_perf_counter_precharge_for_rdwr;
  assign flush_perf_counter_precharge_for_rdwr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_precharge_for_rdwr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_precharge_for_rdwr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_precharge_for_rdwr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_precharge_for_rdwr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_precharge_for_rdwr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_precharge_for_rdwr_count.d)
  );

  logic flush_perf_counter_raw_hazard;
  assign flush_perf_counter_raw_hazard = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_raw_hazard_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raw_hazard_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_raw_hazard),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_raw_hazard.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raw_hazard),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_raw_hazard_count.d)
  );

  logic flush_perf_counter_rdwr_transitions;
  assign flush_perf_counter_rdwr_transitions = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_rdwr_transitions_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_rdwr_transitions_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_rdwr_transitions),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_rdwr_transitions.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_rdwr_transitions),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_rdwr_transitions_count.d)
  );

  logic flush_perf_counter_selfref_mode_rank_0;
  assign flush_perf_counter_selfref_mode_rank_0 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_selfref_mode_rank_0_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_selfref_mode_rank_0_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_selfref_mode_rank_0),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_selfref_mode_rank_0.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_selfref_mode_rank_0),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_selfref_mode_rank_0_count.d)
  );

  logic flush_perf_counter_selfref_mode_rank_1;
  assign flush_perf_counter_selfref_mode_rank_1 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_selfref_mode_rank_1_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_selfref_mode_rank_1_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_selfref_mode_rank_1),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_selfref_mode_rank_1.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_selfref_mode_rank_1),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_selfref_mode_rank_1_count.d)
  );

  logic flush_perf_counter_visible_window_limit_reached_rd;
  assign flush_perf_counter_visible_window_limit_reached_rd = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_visible_window_limit_reached_rd_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_visible_window_limit_reached_rd_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_visible_window_limit_reached_rd),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_visible_window_limit_reached_rd.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_visible_window_limit_reached_rd),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_visible_window_limit_reached_rd_count.d)
  );

  logic flush_perf_counter_visible_window_limit_reached_wr;
  assign flush_perf_counter_visible_window_limit_reached_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_visible_window_limit_reached_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_visible_window_limit_reached_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_visible_window_limit_reached_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_visible_window_limit_reached_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_visible_window_limit_reached_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_visible_window_limit_reached_wr_count.d)
  );

  logic flush_perf_counter_war_hazard;
  assign flush_perf_counter_war_hazard = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_war_hazard_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_war_hazard_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_war_hazard),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_war_hazard.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_war_hazard),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_war_hazard_count.d)
  );

  logic flush_perf_counter_waw_hazard;
  assign flush_perf_counter_waw_hazard = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_waw_hazard_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_waw_hazard_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_waw_hazard),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_waw_hazard.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_waw_hazard),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_waw_hazard_count.d)
  );

  logic flush_perf_counter_wr_xact_when_critical;
  assign flush_perf_counter_wr_xact_when_critical = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_wr_xact_when_critical_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_wr_xact_when_critical_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_wr_xact_when_critical),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_wr_xact_when_critical.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_wr_xact_when_critical),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_wr_xact_when_critical_count.d)
  );

  logic flush_perf_counter_write_combine;
  assign flush_perf_counter_write_combine = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_write_combine_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_write_combine_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_write_combine),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_write_combine.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_write_combine),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_write_combine_count.d)
  );

  logic flush_perf_counter_write_combine_noecc;
  assign flush_perf_counter_write_combine_noecc = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_write_combine_noecc_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_write_combine_noecc_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_write_combine_noecc),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_write_combine_noecc.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_write_combine_noecc),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_write_combine_noecc_count.d)
  );

  logic flush_perf_counter_write_combine_wrecc;
  assign flush_perf_counter_write_combine_wrecc = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_write_combine_wrecc_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_write_combine_wrecc_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_write_combine_wrecc),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_write_combine_wrecc.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_write_combine_wrecc),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_write_combine_wrecc_count.d)
  );

  logic flush_perf_counter_raq_split;
  assign flush_perf_counter_raq_split = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raq_split_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raq_split_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raq_split),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raq_split.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raq_split),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raq_split_count.d)
  );

  logic flush_perf_counter_raqb_pop;
  assign flush_perf_counter_raqb_pop = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raqb_pop_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raqb_pop_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raqb_pop),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raqb_pop.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raqb_pop),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raqb_pop_count.d)
  );

  logic flush_perf_counter_raqb_push;
  assign flush_perf_counter_raqb_push = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raqb_push_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raqb_push_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raqb_push),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raqb_push.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raqb_push),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raqb_push_count.d)
  );

  logic flush_perf_counter_raqr_pop;
  assign flush_perf_counter_raqr_pop = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raqr_pop_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raqr_pop_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raqr_pop),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raqr_pop.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raqr_pop),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raqr_pop_count.d)
  );

  logic flush_perf_counter_raqr_push;
  assign flush_perf_counter_raqr_push = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raqr_push_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raqr_push_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raqr_push),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raqr_push.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raqr_push),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raqr_push_count.d)
  );

  logic flush_perf_counter_waq_pop;
  assign flush_perf_counter_waq_pop = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_waq_pop_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_waq_pop_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (waq_pop),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.waq_pop.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_waq_pop),
    .o_ctrl_cnt_value   (hw2reg.lpddr_waq_pop_count.d)
  );

  logic flush_perf_counter_waq_push;
  assign flush_perf_counter_waq_push = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_waq_push_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_waq_push_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (waq_push),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.waq_push.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_waq_push),
    .o_ctrl_cnt_value   (hw2reg.lpddr_waq_push_count.d)
  );

  logic flush_perf_counter_waq_split;
  assign flush_perf_counter_waq_split = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_waq_split_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_waq_split_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (waq_split),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.waq_split.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_waq_split),
    .o_ctrl_cnt_value   (hw2reg.lpddr_waq_split_count.d)
  );

endmodule
