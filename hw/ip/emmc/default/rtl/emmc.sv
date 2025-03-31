// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Bond <andrew.bond@axelera.ai>

/// Axelera wrapper around Cadence eMMC

module emmc
  import axi_pkg::*;
  import emmc_pkg::*;
  import axe_tcl_sram_pkg::*;
#(
  parameter type emmc_axi_addr_t  = logic [39:0],
  parameter type emmc_axi_data_t  = logic [63:0],
  parameter type emmc_axi_wstrb_t = logic  [7:0],
  parameter type emmc_axi_id_t    = logic  [3:0],
  parameter type emmc_axi_user_t  = logic  [0:0]
)
(
  /// emmc capability register struct for inputs to emmc
  input emmc_outreg_cfg_t emmc_outreg_cfg,

  /// emmc register struct for ports driving from emmc
  output emmc_inreg_cfg_t emmc_inreg_cfg,

  /// Peripheral Clock, positive edge triggered
  input  wire i_pclk,

  /// Asynchronous reset, active low
  input  wire i_preset_n,

  input  wire i_emmc_clk,

  input  wire i_emmc_rst_n,

  //--------------------------------------------------------------------
  // SD host events
  //--------------------------------------------------------------------
  output logic           o_interrupt,

  //--------------------------------------------------------------------
  // APB slave interface
  //--------------------------------------------------------------------
  input  logic [31:0]            i_s_paddr,
  input  logic                   i_s_psel,
  input  logic                   i_s_penable,
  input  logic                   i_s_pwrite,
  input  logic [31:0]            i_s_pwdata,
  output logic                   o_s_pready,
  output logic [31:0]            o_s_prdata,
  output logic                   o_s_pslverr,

  //--------------------------------------------------------------------
  // AXI master interface
  //--------------------------------------------------------------------
  // AXI Write Address Channel
  input  logic                        i_m_awready,
  output emmc_axi_addr_t              o_m_awaddr,
  output emmc_axi_id_t                o_m_awid,
  output axi_len_t                    o_m_awlen,
  output axi_size_e                   o_m_awsize,
  output axi_burst_e                  o_m_awburst,
  output logic                        o_m_awlock,
  output axi_cache_t                  o_m_awcache,
  output axi_prot_t                   o_m_awprot,
  output axi_qos_t                    o_m_awqos,
  output axi_region_t                 o_m_awregion,
  output emmc_axi_user_t              o_m_awuser,
  output logic                        o_m_awvalid,
  // AXI Write Data Channel
  input  logic                        i_m_wready,
  output emmc_axi_data_t              o_m_wdata,
  output emmc_axi_wstrb_t             o_m_wstrb,
  output logic                        o_m_wlast,
  output emmc_axi_user_t              o_m_wuser,
  output logic                        o_m_wvalid,
  // AXI Write Response Channel
  input  axi_resp_t                   i_m_bresp,
  input  logic                        i_m_bvalid,
  input  emmc_axi_id_t                i_m_bid,
  input  emmc_axi_user_t              i_m_buser,
  output logic                        o_m_bready,
  // AXI Read Address Channel
  input  logic                        i_m_arready,
  output emmc_axi_id_t                o_m_arid,
  output emmc_axi_addr_t              o_m_araddr,
  output axi_len_t                    o_m_arlen,
  output axi_size_e                   o_m_arsize,
  output axi_burst_e                  o_m_arburst,
  output logic                        o_m_arlock,
  output axi_cache_t                  o_m_arcache,
  output axi_prot_t                   o_m_arprot,
  output axi_qos_t                    o_m_arqos,
  output axi_region_t                 o_m_arregion,
  output emmc_axi_user_t              o_m_aruser,
  output logic                        o_m_arvalid,
  // AXI Read Data Channel
  input  emmc_axi_data_t              i_m_rdata,
  input  axi_resp_t                   i_m_rresp,
  input  logic                        i_m_rlast,
  input  logic                        i_m_rvalid,
  output logic                        o_m_rready,

  // SRAM config registers
  input axe_tcl_sram_pkg::impl_inp_t  [3:0]  i_impl_inp,
  output axe_tcl_sram_pkg::impl_oup_t [3:0]  o_impl_oup,

  //--------------------------------------------------------------------
  // Pad Interface
  //--------------------------------------------------------------------
  output                              o_mem_ale_oepad,
  output                              o_mem_ale_iepad,
  output                              o_mem_ale_opad,
  input                               i_mem_cmd_ipad,
  output                              o_mem_cmd_oepad,
  output                              o_mem_cmd_iepad,
  output                              o_mem_cmd_opad,
  output                              o_mem_ctrl_0_oepad,
  output                              o_mem_ctrl_0_iepad,
  input                               i_mem_ctrl_0_ipad,
  output                              o_mem_ctrl_1_oepad,
  output                              o_mem_ctrl_1_iepad,
  output                              o_mem_ctrl_1_opad,
  output                              o_mem_rstbar_oepad,
  output                              o_mem_rstbar_iepad,
  output                              o_mem_rstbar_opad,
  input                               i_mem_lpbk_dqs_ipad,
  output                              o_mem_lpbk_dqs_oepad,
  output                              o_mem_lpbk_dqs_iepad,
  input                               i_mem_dqs_ipad,
  output                              o_mem_dqs_oepad,
  output                              o_mem_dqs_iepad,
  output                              o_mem_rebar_oepad,
  output                              o_mem_rebar_iepad,
  output                              o_mem_rebar_opad,
  input                               i_mem_rebar_ipad,
  input  [7:0]                        i_mem_data_ipad,
  output [7:0]                        o_mem_data_oepad,
  output [7:0]                        o_mem_data_iepad,
  output [7:0]                        o_mem_data_opad,
  output                              o_mem_webar_oepad,
  output                              o_mem_webar_iepad,
  output                              o_mem_webar_opad,
  output                              o_mem_wpbar_oepad,
  output                              o_mem_wpbar_iepad,
  input                               i_mem_wpbar_ipad,
  output                              o_tsel_dqs_0_opad,
  output                              o_tsel_dqs_1_opad,
  output                              o_tsel_dqs_2_opad,
  output                              o_tsel_dqs_3_opad,
  output [7:0]                        o_tsel_data_0_opad,
  output [7:0]                        o_tsel_data_1_opad,
  output [7:0]                        o_tsel_data_2_opad,
  output [7:0]                        o_tsel_data_3_opad,
  output                              o_v18,
  output [31:0]                       o_phy_gpio_reg_ctrl_0,
  input  [31:0]                       i_phy_gpio_reg_status_0,
  output [31:0]                       o_phy_gpio_reg_ctrl_1,
  input  [31:0]                       i_phy_gpio_reg_status_1,
  // DFT
  input logic                         test_mode,
  input logic                         scan_en
);

  //--------------------------------------------------------------------
  // scan interface - Not Used in this design
  //--------------------------------------------------------------------
  logic iddq_en;
  logic scanmode;
  logic scan_atspeed_tmode;
  logic slice0_dll_scan_in;
  logic slice0_scan_in;
  logic adrctl_scan_in;
  logic slice0_dll_scan_out;
  logic slice0_scan_out;
  logic adrctl_scan_out;

  always_comb iddq_en            = 1'b0;
  always_comb scanmode           = 1'b0;
  always_comb scan_atspeed_tmode = 1'b0;
  always_comb slice0_dll_scan_in = 1'b0;
  always_comb slice0_scan_in     = 1'b0;
  always_comb adrctl_scan_in     = 1'b0;

  always_comb o_m_awid           = '0;
  always_comb o_m_arid           = '0;

  //--------------------------------------------------------------------
  // Internal clock assignments
  //--------------------------------------------------------------------
  logic s_pclk;
  logic clk;
  logic sdphy_reg_pclk;

  always_comb s_pclk         = i_pclk;
  always_comb clk            = i_pclk;
  always_comb sdphy_reg_pclk = i_pclk;

  logic sdmclk;
  always_comb sdmclk         = i_emmc_clk;

  //--------------------------------------------------------------------
  // Internal reset assignments
  //--------------------------------------------------------------------
  logic s_presetn;
  logic rstclk_n;
  logic sdphy_reg_presetn;

  // No need to re-synchronize resets as done outside this module
  always_comb s_presetn         = i_preset_n;
  always_comb rstclk_n          = i_preset_n;
  always_comb sdphy_reg_presetn = i_preset_n;

  logic rstsdmclk_n;

  // No need to re-synchronize resets as done outside this module
  always_comb rstsdmclk_n       = i_emmc_rst_n;

  //--------------------------------------------------------------------
  // SD host events
  //--------------------------------------------------------------------
  logic interrupt;
  logic wakeup;   // Not required - only used for hot insert / removal

  always_comb o_interrupt = interrupt;

  //--------------------------------------------------------------------
  // AXI slave interface
  //--------------------------------------------------------------------
  logic [CDNS_EMMC_S_AWIDTH-1:0]  s_awaddr;
  logic                           s_awvalid;
  logic                           s_awready;
  logic [CDNS_EMMC_S_DWIDTH-1:0]  s_wdata;
  logic [CDNS_EMMC_S_BEWIDTH-1:0] s_wstrb;
  logic                           s_wvalid;
  logic                           s_wready;
  logic                           s_bready;
  logic [1:0]                     s_bresp;
  logic                           s_bvalid;
  logic [CDNS_EMMC_S_AWIDTH-1:0]  s_araddr;
  logic                           s_arvalid;
  logic                           s_arready;
  logic                           s_rready;
  logic [CDNS_EMMC_S_DWIDTH-1:0]  s_rdata;
  logic [1:0]                     s_rresp;
  logic                           s_rvalid;

  // Tie off and leave outputs floating
  always_comb s_awaddr   = {CDNS_EMMC_S_AWIDTH{1'b0}};
  always_comb s_awvalid  = 1'b0;
  always_comb s_wdata    = {CDNS_EMMC_S_DWIDTH{1'b0}};
  always_comb s_wstrb    = {CDNS_EMMC_S_BEWIDTH{1'b0}};
  always_comb s_wvalid   = 1'b0;
  always_comb s_bready   = 1'b0;
  always_comb s_araddr   = {CDNS_EMMC_S_AWIDTH{1'b0}};
  always_comb s_arvalid  = 1'b0;
  always_comb s_rready   = 1'b0;

  //--------------------------------------------------------------------
  // APB slave interface
  //--------------------------------------------------------------------
  logic [CDNS_EMMC_S_AWIDTH-1:0]      s_paddr;
  logic [2:0]                         s_pprot;
  logic                               s_psel;
  logic                               s_penable;
  logic                               s_pwrite;
  logic [CDNS_EMMC_S_DWIDTH-1:0]      s_pwdata;
  logic [CDNS_EMMC_S_BEWIDTH-1:0]     s_pstrb;
  logic                               s_pready;
  logic [CDNS_EMMC_S_DWIDTH-1:0]      s_prdata;
  logic                               s_pslverr;

  if (CDNS_EMMC_S_AWIDTH > 32) begin : g_awidth_gt32
    $error("COMPILE_ERROR: Cadence SHDC APB Address Bus is too wide");
  end : g_awidth_gt32
  else begin : g_awidth_lte32
    always_comb s_paddr   = i_s_paddr[CDNS_EMMC_S_AWIDTH-1:0];
  end : g_awidth_lte32

  if (CDNS_EMMC_S_DWIDTH > 32) begin : g_dwidth_gt32
    $error("COMPILE_ERROR: Cadence SHDC APB Data Bus is too wide");
  end: g_dwidth_gt32
  else begin : g_dwidth_lte32
    always_comb s_pwdata    = i_s_pwdata[CDNS_EMMC_S_DWIDTH-1:0];
    always_comb o_s_prdata  = { {32-CDNS_EMMC_S_DWIDTH{1'b0}}, s_prdata};
  end: g_dwidth_lte32

  always_comb   s_pprot   = 3'b0;
  always_comb   s_psel    = i_s_psel;
  always_comb   s_penable = i_s_penable;
  always_comb   s_pwrite  = i_s_pwrite;
  // NOTE:: s_pstrb is an Optional signal: tied to write signal from Master as MUST not be active during reads
  always_comb   s_pstrb   = {CDNS_EMMC_S_BEWIDTH{i_s_pwrite}};
  always_comb o_s_pready  = s_pready;
  always_comb o_s_pslverr = s_pslverr;

  //--------------------------------------------------------------------
  // master (dma) interface
  //--------------------------------------------------------------------
  logic m_desc;             // TODO: descriptor transfer flag - do we need this?
  logic master_if;

  // Tie off to indicate AXI Master
  always_comb master_if = 1'b0;

  //--------------------------------------------------------------------
  // AXI master interface
  //--------------------------------------------------------------------
  // AXI Write Address Channel
  logic                            m_awready;
  logic [CDNS_EMMC_M_AWIDTH-1:0]   m_awaddr;
  logic [3:0]                      m_awlen;
  logic [2:0]                      m_awsize;
  logic [1:0]                      m_awburst;
  logic [1:0]                      m_awlock;
  logic [3:0]                      m_awcache;
  logic [2:0]                      m_awprot;
  logic                            m_awvalid;

  // AXI Write Data Channel
  logic                            m_wready;
  logic [CDNS_EMMC_M_DWIDTH-1:0]   m_wdata;
  logic [CDNS_EMMC_M_DWIDTH/8-1:0] m_wstrb;
  logic                            m_wlast;
  logic                            m_wvalid;

  // AXI Write Response Channel
  logic [1:0]                      m_bresp;
  logic                            m_bvalid;
  logic                            m_bready;

  // AXI Read Address Channel
  logic                            m_arready;
  logic [CDNS_EMMC_M_AWIDTH-1:0]   m_araddr;
  logic [3:0]                      m_arlen;
  logic [2:0]                      m_arsize;
  logic [1:0]                      m_arburst;
  logic [1:0]                      m_arlock;
  logic [3:0]                      m_arcache;
  logic [2:0]                      m_arprot;
  logic                            m_arvalid;

  // AXI Read Data Channel
  logic [CDNS_EMMC_M_DWIDTH-1:0]   m_rdata;
  logic [1:0]                      m_rresp;
  logic                            m_rlast;
  logic                            m_rvalid;
  logic                            m_rready;

  // Write and Read Address Channels
  always_comb o_m_awvalid = m_awvalid;
  always_comb o_m_arvalid = m_arvalid;

  always_comb   m_awready = i_m_awready;
  always_comb   m_arready = i_m_arready;

  if (CDNS_EMMC_M_AWIDTH > $bits(emmc_axi_addr_t)) begin : g_addr_emmc_gt_noc
    always_comb o_m_awaddr  = emmc_axi_addr_t'(m_awaddr[$bits(emmc_axi_addr_t)-1:0]);
    always_comb o_m_araddr  = emmc_axi_addr_t'(m_araddr[$bits(emmc_axi_addr_t)-1:0]);
  end : g_addr_emmc_gt_noc
  else begin : g_addr_emmc_lte_noc
    always_comb o_m_awaddr  = emmc_axi_addr_t'({ {$bits(emmc_axi_addr_t)-CDNS_EMMC_M_AWIDTH{1'b0}}, m_awaddr });
    always_comb o_m_araddr  = emmc_axi_addr_t'({ {$bits(emmc_axi_addr_t)-CDNS_EMMC_M_AWIDTH{1'b0}}, m_araddr });
  end : g_addr_emmc_lte_noc

  if (3 > AXI_SIZE_WIDTH) begin: g_size_lt_3
    $error("COMPILE_ERROR: Cadence SHDC AXI-M Size is too wide");
  end: g_size_lt_3
  else begin : g_size_gte_3
    always_comb o_m_awsize  = axi_size_e'({ {AXI_SIZE_WIDTH-3{1'b0}}, m_awsize });
    always_comb o_m_arsize  = axi_size_e'({ {AXI_SIZE_WIDTH-3{1'b0}}, m_arsize });
  end : g_size_gte_3

  if (2 > AXI_BURST_WIDTH) begin : g_burst_lt_2
    $error("COMPILE_ERROR: Cadence SHDC AXI-M Burst is too wide");
  end : g_burst_lt_2
  else begin : g_burst_gte_2
    always_comb o_m_awburst = axi_burst_e'({ {AXI_BURST_WIDTH-2{1'b0}}, m_awburst });
    always_comb o_m_arburst = axi_burst_e'({ {AXI_BURST_WIDTH-2{1'b0}}, m_arburst });
  end : g_burst_gte_2

  if (4 > AXI_CACHE_WIDTH) begin : g_cache_lt_4
    $error("COMPILE_ERROR: Cadence SHDC AXI-M Cache is too wide");
  end : g_cache_lt_4
  else begin : g_cache_gte_4
    always_comb o_m_awcache = axi_cache_t'({ {AXI_CACHE_WIDTH-4{1'b0}}, m_awcache });
    always_comb o_m_arcache = axi_cache_t'({ {AXI_CACHE_WIDTH-4{1'b0}}, m_arcache });
  end : g_cache_gte_4

 if (3 > AXI_PROT_WIDTH) begin : g_prot_lt_3
    $error("COMPILE_ERROR: Cadence SHDC AXI-M Prot is too wide");
 end: g_prot_lt_3
  else begin : g_prot_gte_3
    always_comb o_m_awprot = axi_prot_t'({ {AXI_PROT_WIDTH-3{1'b0}}, m_awprot });
    always_comb o_m_arprot = axi_prot_t'({ {AXI_PROT_WIDTH-3{1'b0}}, m_arprot });
  end : g_prot_gte_3

  if (4 > AXI_LEN_WIDTH) begin : g_len_lt_4
    $error("COMPILE_ERROR: Cadence SHDC AXI-M Len is too wide");
  end : g_len_lt_4
  else begin : g_len_gte_4
    always_comb o_m_awlen   = axi_len_t'({ {AXI_LEN_WIDTH-4{1'b0}}, m_awlen });
    always_comb o_m_arlen   = axi_len_t'({ {AXI_LEN_WIDTH-4{1'b0}}, m_arlen });
  end : g_len_gte_4

  always_comb o_m_awlock  = (m_awlock == 2'b01);
  always_comb o_m_arlock  = (m_arlock == 2'b01);

  always_comb o_m_awqos    = '0;
  always_comb o_m_arqos    = '0;

  always_comb o_m_awregion = '0;
  always_comb o_m_arregion = '0;

  always_comb o_m_awuser   = '0;
  always_comb o_m_aruser   = '0;

  // Write / Read Data Channels
  always_comb o_m_wvalid  = m_wvalid;
  always_comb   m_rvalid  = i_m_rvalid;

  always_comb   m_wready  = i_m_wready;
  always_comb o_m_rready  = m_rready;

  always_comb o_m_wlast   = m_wlast;
  always_comb   m_rlast   = i_m_rlast;

  if (CDNS_EMMC_M_DWIDTH > $bits(emmc_axi_data_t)) begin : g_md_gt_noc
    $error("COMPILE_ERROR: Cadence SHDC AXI-M Data is too wide");
  end: g_md_gt_noc
  else begin : g_md_lte_noc
    always_comb o_m_wdata   = emmc_axi_data_t'({ {$bits(emmc_axi_data_t)-CDNS_EMMC_M_DWIDTH{1'b0}}, m_wdata });
    always_comb m_rdata     = i_m_rdata[CDNS_EMMC_M_DWIDTH-1:0];
  end : g_md_lte_noc

  if (CDNS_EMMC_M_BEWIDTH > $bits(emmc_axi_wstrb_t)) begin: g_mbe_gt_noc
    $error("COMPILE_ERROR: Cadence SHDC AXI-M Strobe is too wide");
  end: g_mbe_gt_noc
  else begin : g_mbe_lte_noc
    always_comb o_m_wstrb = emmc_axi_wstrb_t'({ {$bits(emmc_axi_wstrb_t)-CDNS_EMMC_M_BEWIDTH{1'b0}}, m_wstrb });
  end: g_mbe_lte_noc

  always_comb o_m_wuser    = '0;

  if (2 > AXI_RESP_WIDTH) begin : g_resp_lt_2
    $error("COMPILE_ERROR: Cadence SHDC AXI-M RResp is too wide");
    $error("COMPILE_ERROR: Cadence SHDC AXI-M BResp is too wide");
  end: g_resp_lt_2
  else begin : g_resp_gte_2
    always_comb m_rresp   = i_m_rresp[1:0];
    always_comb m_bresp   = axi_resp_t'(i_m_bresp[1:0]);
  end : g_resp_gte_2

  // Write Response Channel
  // i_m_bid - discarded
  // i_m_buser - discarded
  always_comb   m_bvalid  = i_m_bvalid;
  always_comb o_m_bready  = m_bready;


  //--------------------------------------------------------------------
  // AHB-Lite master interface - Tied off as we use the AXI bus
  //--------------------------------------------------------------------
  logic [CDNS_EMMC_M_DWIDTH-1:0] m_hrdata;
  logic                m_hready;
  logic                m_hresp;
  logic [CDNS_EMMC_M_AWIDTH-1:0] m_haddr;
  logic [1:0]          m_htrans;
  logic [2:0]          m_hburst;
  logic [2:0]          m_hsize;
  logic                m_hmastlock;
  logic [3:0]          m_hprot;
  logic                m_hwrite;
  logic [CDNS_EMMC_M_DWIDTH-1:0] m_hwdata;

  always_comb m_hrdata = {CDNS_EMMC_M_DWIDTH{1'b0}};
  always_comb m_hready = 1'b0;
  always_comb m_hresp  = 1'b0;

  //--------------------------------------------------------------------
  // dma sideband signals
  //--------------------------------------------------------------------
  logic dma_rd_ack;
  logic dma_wr_ack;
  logic dma_rd_req;
  logic dma_wr_req;

  // Assume using internal emmc DMAs- tie off
  always_comb dma_rd_ack = 1'b0;
  always_comb dma_wr_ack = 1'b0;

  //--------------------------------------------------------------------
  // eMMC Boot - tied off : Not used in this design
  //--------------------------------------------------------------------
  logic             boot_en;
  logic             boot_ack_en;
  logic             boot_method;
  logic [1:0]       boot_buswidth;
  logic [9:0]       boot_sdclkdiv;
  logic             boot_addrwidth;
  logic [63:0]      boot_addr;
  logic [31:0]      boot_blockcnt;
  logic [11:0]      boot_blocksize;
  logic [2:0]       boot_bvs;
  logic [1:0]       boot_speedmode;
  logic [31:0]      boot_pow_clk_dly;
  logic [31:0]      boot_clk_cmd_dly;
  logic [3:0]       boot_timeout_ack;
  logic [3:0]       boot_timeout_dat;
  logic             boot_ack;
  logic             boot_done;
  logic             boot_err;

  logic [31:0]      boot_wr_dly;
  logic [9:0]       boot_io_dly;
  logic [3:0]       boot_exten;
  logic [3:0]       boot_clkadj;

  logic [3:0]        boot_phy_dqstm;
  logic [9:0]        boot_phy_dqtm;
  logic [8:0]        boot_phy_glpbk;
  logic              boot_phy_dllmst;
  logic [15:0]       boot_phy_dllslv;

  logic              boot_setup_mode;
  logic [63:0]       boot_desc_addr;
  logic              desc_mech_error;
  logic              desc_mech_active;

  always_comb boot_en           = 1'b0;
  always_comb boot_ack_en       = 1'b0;
  always_comb boot_method       = 1'b0;
  always_comb boot_buswidth     = 2'b0;
  always_comb boot_sdclkdiv     = 10'b0;
  always_comb boot_addrwidth    = 1'b0;
  always_comb boot_addr         = 64'b0;
  always_comb boot_blockcnt     = 32'b0;
  always_comb boot_blocksize    = 12'b0;
  always_comb boot_bvs          = 3'b0;
  always_comb boot_speedmode    = 2'b0;
  always_comb boot_pow_clk_dly  = 32'b0;
  always_comb boot_clk_cmd_dly  = 32'b0;
  always_comb boot_timeout_ack  = 4'b0;
  always_comb boot_timeout_dat  = 4'b0;
  always_comb boot_wr_dly       = 32'b0;
  always_comb boot_io_dly       = 10'b0;
  always_comb boot_exten        = 4'b0;
  always_comb boot_clkadj       = 4'b0;
  always_comb boot_phy_dqstm    = 4'b0;
  always_comb boot_phy_dqtm     = 10'b0;
  always_comb boot_phy_glpbk    = 9'b0;
  always_comb boot_phy_dllmst   = 1'b0;
  always_comb boot_phy_dllslv   = 16'b0;
  always_comb boot_setup_mode   = 64'b0;
  always_comb boot_desc_addr    = 4'b0;


  //--------------------------------------------------------------------
  // RAM interface
  //--------------------------------------------------------------------
  // biu side
  logic [CDNS_EMMC_RAM_DWIDTH-1:0] biu0_datar;
  logic                            biu0_we;
  logic                            biu0_re;
  logic [CDNS_EMMC_RAM_DWIDTH-1:0] biu0_dataw;
  logic [CDNS_EMMC_FIFODEPTH-1:0]  biu0_addr;
  logic [CDNS_EMMC_RAM_DWIDTH-1:0] biu1_datar;
  logic                            biu1_we;
  logic                            biu1_re;
  logic [CDNS_EMMC_RAM_DWIDTH-1:0] biu1_dataw;
  logic [CDNS_EMMC_FIFODEPTH-1:0]  biu1_addr;

  // ciu side
  logic [CDNS_EMMC_RAM_DWIDTH-1:0] ciu0_datar;
  logic                            ciu0_we;
  logic                            ciu0_re;
  logic [CDNS_EMMC_RAM_DWIDTH-1:0] ciu0_dataw;
  logic [CDNS_EMMC_FIFODEPTH-1:0]  ciu0_addr;
  logic [CDNS_EMMC_RAM_DWIDTH-1:0] ciu1_datar;
  logic                            ciu1_we;
  logic                            ciu1_re;
  logic [CDNS_EMMC_RAM_DWIDTH-1:0] ciu1_dataw;
  logic [CDNS_EMMC_FIFODEPTH-1:0]  ciu1_addr;


  //--------------------------------------------------------------------
  logic [2:0] pad_bv; // power voltage
  logic       pad_cle; // current limit error (active high)
  logic       pad_led; // led on (active high)

  always_comb pad_cle = 1'b0;
  //--------------------------------------------------------------------
  // Instance underlying Cadence IP
  // Although parameterised docs indicate only single configuration
  //--------------------------------------------------------------------
  cdns_sdhc_top#(
    .S_AWIDTH(CDNS_EMMC_S_AWIDTH),
    .S_DWIDTH(CDNS_EMMC_S_DWIDTH),
    .M_AWIDTH(CDNS_EMMC_M_AWIDTH),
    .M_DWIDTH(CDNS_EMMC_M_DWIDTH),
    .FIFODEPTH(CDNS_EMMC_FIFODEPTH), // 2048 bytes
    .RAM_DWIDTH(CDNS_EMMC_RAM_DWIDTH)
  ) u_cdns_sdhc_top(
    //--------------------------------------------------------------------
    // scan interface
    //--------------------------------------------------------------------
    .iddq_en(iddq_en),
    .scanmode(test_mode),
    .scan_en(scan_en),
    .scan_atspeed_tmode(scan_atspeed_tmode),
    .slice0_dll_scan_in(slice0_dll_scan_in),
    .slice0_scan_in(slice0_scan_in),
    .adrctl_scan_in(adrctl_scan_in),
    .slice0_dll_scan_out(slice0_dll_scan_out),
    .slice0_scan_out(slice0_scan_out),
    .adrctl_scan_out(adrctl_scan_out),
    // Clocks
    .s_pclk(s_pclk),
    .clk   (clk),
    .sdmclk(sdmclk),
    .sdphy_reg_pclk(sdphy_reg_pclk),
    // Resets
    .s_presetn(s_presetn),               // hardware reset (slave interface)
    .rstclk_n(rstclk_n),                  // asyn. reset in clk clock domain
    .rstsdmclk_n(rstsdmclk_n),            // asyn. reset in sdmclk clock domain
    .sdphy_reg_presetn(sdphy_reg_presetn),

    // Clock enable / stable
    .ics(emmc_outreg_cfg.ics),
    .ice(emmc_inreg_cfg.ice),

    // Interrupt
    .interrupt(interrupt),
    .wakeup(),

    // AXI slave interface
    .s_awaddr   ( s_awaddr  ),  // Write address
    .s_awvalid  ( s_awvalid ),  // Write address valid
    .s_awready  ( s_awready ),  // Write address ready
    .s_wdata    ( s_wdata   ),  // Write data
    .s_wstrb    ( s_wstrb   ),  // Write strobe
    .s_wvalid   ( s_wvalid  ),  // Write data valid
    .s_wready   ( s_wready  ),  // Write ready
    .s_bready   ( s_bready  ),  // Response ready
    .s_bresp    ( s_bresp   ),  // Write response
    .s_bvalid   ( s_bvalid  ),  // Write response valid
    .s_araddr   ( s_araddr  ),  // Read address
    .s_arvalid  ( s_arvalid ),  // Read address valid
    .s_arready  ( s_arready ),  // Read address ready
    .s_rready   ( s_rready  ),  // Read data ready
    .s_rdata    ( s_rdata   ),  // Read data
    .s_rresp    ( s_rresp   ),  // Read response
    .s_rvalid   ( s_rvalid  ),  // Read data valid

    // APB subordinate interface
    .s_paddr   ( s_paddr   ),
    .s_pprot   ( s_pprot   ),
    .s_psel    ( s_psel    ),
    .s_penable ( s_penable ),
    .s_pwrite  ( s_pwrite  ),
    .s_pwdata  ( s_pwdata  ),
    .s_pready  ( s_pready  ),
    .s_prdata  ( s_prdata  ),
    .s_pslverr ( s_pslverr ),
    .s_pstrb   ( s_pstrb   ),

     //--------------------------------------------------------------------
     // master (dma) interface
     //--------------------------------------------------------------------
     .master_if(master_if),    // master interface select
     .m_desc(m_desc),          // descriptor transfer flag

    // AXI manager interface
    .m_awready(m_awready),
    .m_awaddr(m_awaddr),
    .m_awlen(m_awlen),
    .m_awsize(m_awsize),
    .m_awburst(m_awburst),
    .m_awlock(m_awlock),
    .m_awcache(m_awcache),
    .m_awprot(m_awprot),
    .m_awvalid(m_awvalid),

    .m_wready(m_wready),
    .m_wdata(m_wdata),
    .m_wstrb(m_wstrb),
    .m_wlast(m_wlast),
    .m_wvalid(m_wvalid),
    .m_bresp(m_bresp),
    .m_bvalid(m_bvalid),
    .m_bready(m_bready),

    .m_arready(m_arready),
    .m_araddr(m_araddr),
    .m_arlen(m_arlen),
    .m_arsize(m_arsize),
    .m_arburst(m_arburst),
    .m_arlock(m_arlock),
    .m_arcache(m_arcache),
    .m_arprot(m_arprot),
    .m_arvalid(m_arvalid),
    .m_rdata(m_rdata),
    .m_rresp(m_rresp),
    .m_rlast(m_rlast),
    .m_rvalid(m_rvalid),
    .m_rready(m_rready),

    // AHB-Lite master interface
    .m_hrdata      ( m_hrdata    ),
    .m_hready      ( m_hready    ),
    .m_hresp       ( m_hresp     ),
    .m_haddr       ( m_haddr     ),
    .m_htrans      ( m_htrans    ),
    .m_hburst      ( m_hburst    ),
    .m_hsize       ( m_hsize     ),
    .m_hmastlock   ( m_hmastlock ),
    .m_hprot       ( m_hprot     ),
    .m_hwrite      ( m_hwrite    ),
    .m_hwdata      ( m_hwdata    ),

    // dma sideband signals
    .dma_rd_ack ( dma_rd_ack ),
    .dma_wr_ack ( dma_wr_ack ),
    .dma_rd_req ( dma_rd_req ),
    .dma_wr_req ( dma_wr_req ),

    // I/O Pads
    .o_mem_ale_oepad(o_mem_ale_oepad),
    .o_mem_ale_iepad(o_mem_ale_iepad),
    .o_mem_ale_opad(o_mem_ale_opad),
    .i_mem_cmd_ipad(i_mem_cmd_ipad),
    .o_mem_cmd_oepad(o_mem_cmd_oepad),
    .o_mem_cmd_iepad(o_mem_cmd_iepad),
    .o_mem_cmd_opad(o_mem_cmd_opad),
    .o_mem_ctrl_0_oepad(o_mem_ctrl_0_oepad),
    .o_mem_ctrl_0_iepad(o_mem_ctrl_0_iepad),
    .i_mem_ctrl_0_ipad(i_mem_ctrl_0_ipad),
    .o_mem_ctrl_1_oepad(o_mem_ctrl_1_oepad),
    .o_mem_ctrl_1_iepad(o_mem_ctrl_1_iepad),
    .o_mem_ctrl_1_opad(o_mem_ctrl_1_opad),
    .o_mem_rstbar_oepad(o_mem_rstbar_oepad),
    .o_mem_rstbar_iepad(o_mem_rstbar_iepad),
    .o_mem_rstbar_opad(o_mem_rstbar_opad),
    .i_mem_lpbk_dqs_ipad(i_mem_lpbk_dqs_ipad),
    .o_mem_lpbk_dqs_oepad(o_mem_lpbk_dqs_oepad),
    .o_mem_lpbk_dqs_iepad(o_mem_lpbk_dqs_iepad),
    .i_mem_dqs_ipad(i_mem_dqs_ipad),
    .o_mem_dqs_oepad(o_mem_dqs_oepad),
    .o_mem_dqs_iepad(o_mem_dqs_iepad),
    .o_mem_rebar_oepad(o_mem_rebar_oepad),
    .o_mem_rebar_iepad(o_mem_rebar_iepad),
    .o_mem_rebar_opad(o_mem_rebar_opad),
    .i_mem_rebar_ipad(i_mem_rebar_ipad),
    .i_mem_data_ipad(i_mem_data_ipad),
    .o_mem_data_oepad(o_mem_data_oepad),
    .o_mem_data_iepad(o_mem_data_iepad),
    .o_mem_data_opad(o_mem_data_opad),
    .o_mem_webar_oepad(o_mem_webar_oepad),
    .o_mem_webar_iepad(o_mem_webar_iepad),
    .o_mem_webar_opad(o_mem_webar_opad),
    .o_mem_wpbar_oepad(o_mem_wpbar_oepad),
    .o_mem_wpbar_iepad(o_mem_wpbar_iepad),
    .i_mem_wpbar_ipad(i_mem_wpbar_ipad),
    // Config registers
    .o_tsel_dqs_0_opad(o_tsel_dqs_0_opad),
    .o_tsel_dqs_1_opad(o_tsel_dqs_1_opad),
    .o_tsel_dqs_2_opad(o_tsel_dqs_2_opad),
    .o_tsel_dqs_3_opad(o_tsel_dqs_3_opad),
    .o_tsel_data_0_opad(o_tsel_data_0_opad),
    .o_tsel_data_1_opad(o_tsel_data_1_opad),
    .o_tsel_data_2_opad(o_tsel_data_2_opad),
    .o_tsel_data_3_opad(o_tsel_data_3_opad),
    .o_v18(o_v18),
    .o_phy_gpio_reg_ctrl_0(o_phy_gpio_reg_ctrl_0),
    .i_phy_gpio_reg_status_0(i_phy_gpio_reg_status_0),
    .o_phy_gpio_reg_ctrl_1(o_phy_gpio_reg_ctrl_1),
    .i_phy_gpio_reg_status_1(i_phy_gpio_reg_status_1),
     //--------------------------------------------------------------------
    .pad_bv(pad_bv), // power voltage
    .pad_cle(pad_cle), // current limit error (active high)
    .pad_led(pad_led), // led on (active high)
    //--------------------------------------------------------------------
    // eMMC Boot
    //--------------------------------------------------------------------
    .boot_en(boot_en),                  // Boot operation enable
    .boot_ack_en(boot_ack_en),          // Boot Acknowledge Pattern enable
    .boot_method(boot_method),          // Boot method select
    .boot_buswidth(boot_buswidth),      // Boot width mode select
    .boot_sdclkdiv(boot_sdclkdiv),      // SD clock divider select
    .boot_addrwidth(boot_addrwidth),    // System address bus width
    .boot_addr(boot_addr),              // System address
    .boot_blockcnt(boot_blockcnt),      // Block count
    .boot_blocksize(boot_blocksize),    // Block size
    .boot_bvs(boot_bvs),                // Bus voltage select
    .boot_speedmode(boot_speedmode),    // Speed mode select
    .boot_pow_clk_dly(boot_pow_clk_dly),// Power to Clock delay
    .boot_clk_cmd_dly(boot_clk_cmd_dly),// Clock to Command delay
    .boot_timeout_ack(boot_timeout_ack),// Boot Acknowledge Timeout
    .boot_timeout_dat(boot_timeout_dat),// Boot Data Transfer Timeout
    .boot_ack(boot_ack),                // Boot Acknowledge Status Received
    .boot_done(boot_done),              // Boot acknowledge
    .boot_err(boot_err),                // Boot error
    .boot_wr_dly(boot_wr_dly),          // Boot HRS16 value
    .boot_io_dly(boot_io_dly),          // Boot HRS07 value, idelay + rw_compensate
    .boot_exten(boot_exten),            // Boot HRS09 value
    .boot_clkadj(boot_clkadj),          // Boot HRS10 value
    .boot_phy_dqstm(boot_phy_dqstm),    //
    .boot_phy_dqtm(boot_phy_dqtm),      //
    .boot_phy_glpbk(boot_phy_glpbk),    //
    .boot_phy_dllmst(boot_phy_dllmst),  //
    .boot_phy_dllslv(boot_phy_dllslv),  //
    .boot_setup_mode(boot_setup_mode),
    .boot_desc_addr(boot_desc_addr),
    .desc_mech_error(desc_mech_error),   // error detected during descriptor mechanism
    .desc_mech_active(desc_mech_active), // descriptor mechanism in progress
  //--------------------------------------------------------------------
  // RAM interface
  //--------------------------------------------------------------------
  // biu side
  .biu0_datar(biu0_datar),      // mem read data
  .biu0_we(biu0_we),            // mem write enable
  .biu0_re(biu0_re),            // mem read enable
  .biu0_dataw(biu0_dataw),      // mem write data
  .biu0_addr(biu0_addr),        // mem address
  .biu1_datar(biu1_datar),      // mem read data
  .biu1_we(biu1_we),            // mem write enable
  .biu1_re(biu1_re),            // mem read enable
  .biu1_dataw(biu1_dataw),      // mem write data
  .biu1_addr(biu1_addr),        // mem address
  // ciu side
  .ciu0_datar(ciu0_datar),      // mem read data
  .ciu0_we(ciu0_we),            // mem write enable
  .ciu0_re(ciu0_re),            // mem read enable
  .ciu0_dataw(ciu0_dataw),      // mem write data
  .ciu0_addr(ciu0_addr),        // mem address
  .ciu1_datar(ciu1_datar),      // mem read data
  .ciu1_we(ciu1_we),            // mem write enable
  .ciu1_re(ciu1_re),            // mem read enable
  .ciu1_dataw(ciu1_dataw),      // mem write data
  .ciu1_addr(ciu1_addr),        // mem address
  //--------------------------------------------------------------------
  // Host Settings (Hardware Initialized Registers)
  //--------------------------------------------------------------------
  // Default values for SRS
  .s0_hwinit_srs16(emmc_outreg_cfg.s0_hwinit_srs16),    // hwinit for srs16
  .s0_hwinit_srs17(emmc_outreg_cfg.s0_hwinit_srs17),    // hwinit for srs17
  .s0_hwinit_srs18(emmc_outreg_cfg.s0_hwinit_srs18),    // hwinit for srs18
  .s0_hwinit_srs19(emmc_outreg_cfg.s0_hwinit_srs19),    // hwinit for srs19
  .s0_hwinit_srs24(emmc_outreg_cfg.s0_hwinit_srs24),    // hwinit for srs24
  .s0_hwinit_srs25(emmc_outreg_cfg.s0_hwinit_srs25),    // hwinit for srs25
  .s0_hwinit_srs26(emmc_outreg_cfg.s0_hwinit_srs26),    // hwinit for srs26
  .s0_hwinit_srs27(emmc_outreg_cfg.s0_hwinit_srs27),    // hwinit for srs27
  .hwinit_itcfmul(emmc_outreg_cfg.hwinit_itcfmul),
  .hwinit_itcfval(emmc_outreg_cfg.hwinit_itcfval),
  .hwinit_itcfsel(emmc_outreg_cfg.hwinit_itcfsel)
  );

  //--------------------------------------------------------------------
  // Instance SRAMs
  //--------------------------------------------------------------------
  localparam int unsigned SRAM_NUM_WORDS  = 256;
  localparam int unsigned SRAM_DATA_WIDTH = 64;
  localparam int unsigned SRAM_BYTE_WIDTH = 64;
  localparam int unsigned SRAM_LATENCY    = 1;

  axe_tcl_ram_1rwp #(
    .NumWords    (SRAM_NUM_WORDS),
    .DataWidth   (SRAM_DATA_WIDTH),
    .ByteWidth   (SRAM_BYTE_WIDTH),
    .ReadLatency (SRAM_LATENCY),
    .ImplKey     ("HS_RVT")
  ) u_biu0_sram (
    .i_clk       (i_pclk),
    .i_rst_n     (i_preset_n),
    .i_req       (biu0_we|biu0_re),
    .i_addr      (biu0_addr),
    .i_wr_enable (biu0_we),
    .i_wr_data   (biu0_dataw),
    .i_wr_mask   (1'b1),
    .o_rd_data   (biu0_datar),
    .i_impl      (i_impl_inp[0]),
    .o_impl      (o_impl_oup[0])
  );

  axe_tcl_ram_1rwp #(
    .NumWords    (SRAM_NUM_WORDS),
    .DataWidth   (SRAM_DATA_WIDTH),
    .ByteWidth   (SRAM_BYTE_WIDTH),
    .ReadLatency (SRAM_LATENCY),
    .ImplKey     ("HS_RVT")
  ) u_biu1_sram (
    .i_clk       (i_pclk),
    .i_rst_n     (i_preset_n),
    .i_req       (biu1_we|biu1_re),
    .i_addr      (biu1_addr),
    .i_wr_enable (biu1_we),
    .i_wr_data   (biu1_dataw),
    .i_wr_mask   (1'b1),
    .o_rd_data   (biu1_datar),
    .i_impl      (i_impl_inp[1]),
    .o_impl      (o_impl_oup[1])
  );

  axe_tcl_ram_1rwp #(
    .NumWords    (SRAM_NUM_WORDS),
    .DataWidth   (SRAM_DATA_WIDTH),
    .ByteWidth   (SRAM_BYTE_WIDTH),
    .ReadLatency (SRAM_LATENCY),
    .ImplKey     ("HS_RVT")
  ) u_ciu0_sram (
    .i_clk       (i_emmc_clk),
    .i_rst_n     (i_preset_n),
    .i_req       (ciu0_we|ciu0_re),
    .i_addr      (ciu0_addr),
    .i_wr_enable (ciu0_we),
    .i_wr_data   (ciu0_dataw),
    .i_wr_mask   (1'b1),
    .o_rd_data   (ciu0_datar),
    .i_impl      (i_impl_inp[2]),
    .o_impl      (o_impl_oup[2])
  );

  axe_tcl_ram_1rwp #(
    .NumWords    (SRAM_NUM_WORDS),
    .DataWidth   (SRAM_DATA_WIDTH),
    .ByteWidth   (SRAM_BYTE_WIDTH),
    .ReadLatency (SRAM_LATENCY),
    .ImplKey     ("HS_RVT")
  ) u_ciu1_sram (
    .i_clk       (i_emmc_clk),
    .i_rst_n     (i_preset_n),
    .i_req       (ciu1_we|ciu1_re),
    .i_addr      (ciu1_addr),
    .i_wr_enable (ciu1_we),
    .i_wr_data   (ciu1_dataw),
    .i_wr_mask   (1'b1),
    .o_rd_data   (ciu1_datar),
    .i_impl      (i_impl_inp[3]),
    .o_impl      (o_impl_oup[3])
  );
endmodule
