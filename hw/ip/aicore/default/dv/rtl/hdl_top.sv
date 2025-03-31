//Description: This is the top module for aicore top tb
//Owner      : Roswin Benny<roswin.benny@axelera.ai>
`define DUT dut
`define LS_DUT_PATH hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls

`include "uvm_macros.svh"

module hdl_top;
  // Time unit and precision
  timeunit 1ns; timeprecision 1ps;

  // Packages import
  import uvm_pkg::*;
  import ai_core_pkg::*;
  import ai_core_top_test_pkg::*;

  // VIP packages import
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;
  import dmc_pkg::*, mmio_pkg::*;

  //`include "axi4pc/bind_ai_core_p.svh" //TODO
  //Include files for LS
  `include "aic_ls_mmio_connections.svh"
  //`include "aic_ls_rvv_connections.svh"


  // Clock and reset signals
  logic clk_en;
  logic clk;
  logic ref_clk_en;
  logic ref_clk;
  logic axi_rst;
  logic apb_rst;

  int aicore_freq_mhz = 1200;   //1.2GHz //give value in MHz
  int ref_freq_mhz = 50;        //50MHz //give value in MHz
  time aicore_tol_ps = 10;

  svt_apb_if apb_if ();  // VIP Interface instance representing the APB system
  svt_axi_if axi_if ();  // VIP Interface instance representing the AXI system
  svt_axi_if axi_ls_if ();

  ai_core_top_if tb_cfg_if ();  // aicore tb interface
  aic_ls_if if_aic_ls();
  axi_reset_if axi_reset_if ();  // AXI reset interface
  apb_reset_if apb_reset_if ();  // APB reset interface

  dmc_addr_gen_if if_m_ifd0(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_m_ifd1(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_m_ifd2(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_m_ifdw(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_m_odr(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_d_ifd0(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_d_ifd1(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_d_odr(`LS_DUT_PATH.i_clk);


  // =============================================================================================================
  // CLK RST Generation
  // =============================================================================================================
  axe_clk_generator u_axe_clk_generator (
      .i_enable(clk_en),
      .o_clk(clk)
  );
  assign tb_cfg_if.clk = clk;

  axe_clk_generator u_axe_ref_clk_generator (
      .i_enable(ref_clk_en),
      .o_clk(ref_clk)
  );
  assign tb_cfg_if.ref_clk = ref_clk;

  axe_rst_generator u_apb_rst_generator (
      .i_clk(ref_clk),
      .o_rst(apb_rst)
  );
  assign tb_cfg_if.apb_rst = apb_rst;

  axe_rst_generator u_axi_rst_generator (
      .i_clk(clk),
      .o_rst(axi_rst)
  );
  assign tb_cfg_if.axi_rst = axi_rst;

  //axe_clk_assert u_axe_clk_assert (
  //    .clk(clk),
  //    .rst_n(~rst),
  //    .freq_mhz(aicore_freq_mhz),
  //    .tol_ps(aicore_tol_ps)
  //);

  assign axi_if.common_aclk          = clk;
  assign axi_if.master_if[0].aclk    = clk;
  assign axi_if.slave_if[0].aclk     = clk;

  assign axi_reset_if.clk            = clk;
  assign axi_reset_if.reset          = axi_rst;
  assign axi_if.master_if[0].aresetn = ~axi_reset_if.reset;
  assign axi_if.slave_if[0].aresetn  = ~axi_reset_if.reset;
  assign apb_reset_if.pclk           = ref_clk;
  assign apb_reset_if.presetn        = ~apb_rst;
  assign apb_if.pclk                 = ref_clk;
  assign apb_if.presetn              = apb_reset_if.presetn;


//==============================================================
//
// UVM_SW_IPC connection
//
//==============================================================
  import aic_common_pkg::*;

  wire[39:0]                            o_noc_lt_axi_m_awaddr;
  wire[8:0]                             o_noc_lt_axi_m_awid;
  wire[7:0]                             o_noc_lt_axi_m_awlen;
  wire[AIC_LT_AXI_SIZE_WIDTH-1:0]       o_noc_lt_axi_m_awsize;
  wire[AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_awburst;
  wire[AIC_LT_AXI_CACHE_WIDTH-1:0]      o_noc_lt_axi_m_awcache;
  wire[AIC_LT_AXI_PROT_WIDTH-1:0]       o_noc_lt_axi_m_awprot;
  wire                                  o_noc_lt_axi_m_awlock;
  wire                                  o_noc_lt_axi_m_awvalid;
  wire                                  i_noc_lt_axi_m_awready;
  wire[63:0]                            o_noc_lt_axi_m_wdata;
  wire[7:0]                             o_noc_lt_axi_m_wstrb;
  wire                                  o_noc_lt_axi_m_wlast;
  wire                                  o_noc_lt_axi_m_wvalid;
  wire                                  i_noc_lt_axi_m_wready;
  wire                                  i_noc_lt_axi_m_bvalid;
  wire[8:0]                             i_noc_lt_axi_m_bid;
  wire[AIC_LT_AXI_RESP_WIDTH-1:0]       i_noc_lt_axi_m_bresp;
  wire                                  o_noc_lt_axi_m_bready;
  wire[39:0]                            o_noc_lt_axi_m_araddr;
  wire[8:0]                             o_noc_lt_axi_m_arid;
  wire[7:0]                             o_noc_lt_axi_m_arlen;
  wire[AIC_LT_AXI_SIZE_WIDTH-1:0]       o_noc_lt_axi_m_arsize;
  wire[AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_arburst;
  wire[AIC_LT_AXI_CACHE_WIDTH-1:0]      o_noc_lt_axi_m_arcache;
  wire[AIC_LT_AXI_PROT_WIDTH-1:0]       o_noc_lt_axi_m_arprot;
  wire                                  o_noc_lt_axi_m_arlock;
  wire                                  o_noc_lt_axi_m_arvalid;
  wire                                  i_noc_lt_axi_m_arready;
  wire                                  i_noc_lt_axi_m_rvalid;
  wire                                  i_noc_lt_axi_m_rlast;
  wire[8:0]                             i_noc_lt_axi_m_rid;
  wire[63:0]                            i_noc_lt_axi_m_rdata;
  wire[AIC_LT_AXI_RESP_WIDTH-1:0]       i_noc_lt_axi_m_rresp;
  wire                                  o_noc_lt_axi_m_rready;

  `include "uvm_sw_ipc_connections.sv";

  // Only outside accesses to the SYS_SPM are authorized TODO-when compilation support is added uncomment this
  // `ifdef DMA_TESTS
  //always @(posedge clk) begin
  //  if (((i_noc_lt_axi_m_awready & o_noc_lt_axi_m_awvalid) === 1) &&
  //      ((o_noc_lt_axi_m_awaddr < aipu_addr_map_pkg::SYS_SPM_ST_ADDR) ||
  //       (o_noc_lt_axi_m_awaddr > aipu_addr_map_pkg::SYS_SPM_END_ADDR))) begin
  //    `uvm_fatal("hdl_top", $sformatf("Unauthorized write address: %0h", o_noc_lt_axi_m_awaddr))
  //  end
  //  if (((i_noc_lt_axi_m_arready & o_noc_lt_axi_m_arvalid) === 1) &&
  //      ((o_noc_lt_axi_m_araddr < aipu_addr_map_pkg::SYS_SPM_ST_ADDR) ||
  //       (o_noc_lt_axi_m_araddr > aipu_addr_map_pkg::SYS_SPM_END_ADDR))) begin
  //    `uvm_fatal("hdl_top", $sformatf("Unauthorized read address: %0h", o_noc_lt_axi_m_araddr))
  //  end
  //end
  //`endif

  dv_axi_ram #(
      .ADDR_WIDTH(40),
      .DATA_WIDTH(64),
      .ID_WIDTH  (9)
  ) i_fake_sys_spm (
      .clk          (clk),
      .rst          (axi_reset_if.reset),
      .s_axi_awid   (o_noc_lt_axi_m_awid),
      .s_axi_awaddr (o_noc_lt_axi_m_awaddr),
      .s_axi_awlen  (o_noc_lt_axi_m_awlen),
      .s_axi_awsize (o_noc_lt_axi_m_awsize),
      .s_axi_awburst(o_noc_lt_axi_m_awburst),
      .s_axi_awlock (o_noc_lt_axi_m_awlock),
      .s_axi_awcache(o_noc_lt_axi_m_awcache),
      .s_axi_awprot (o_noc_lt_axi_m_awprot),
      .s_axi_awvalid(o_noc_lt_axi_m_awvalid),
      .s_axi_awready(i_noc_lt_axi_m_awready),
      .s_axi_wdata  (o_noc_lt_axi_m_wdata),
      .s_axi_wstrb  (o_noc_lt_axi_m_wstrb),
      .s_axi_wlast  (o_noc_lt_axi_m_wlast),
      .s_axi_wvalid (o_noc_lt_axi_m_wvalid),
      .s_axi_wready (i_noc_lt_axi_m_wready),
      .s_axi_bid    (i_noc_lt_axi_m_bid),
      .s_axi_bresp  (i_noc_lt_axi_m_bresp),
      .s_axi_bvalid (i_noc_lt_axi_m_bvalid),
      .s_axi_bready (o_noc_lt_axi_m_bready),
      .s_axi_arid   (o_noc_lt_axi_m_arid),
      .s_axi_araddr (o_noc_lt_axi_m_araddr),
      .s_axi_arlen  (o_noc_lt_axi_m_arlen),
      .s_axi_arsize (o_noc_lt_axi_m_arsize),
      .s_axi_arburst(o_noc_lt_axi_m_arburst),
      .s_axi_arlock (o_noc_lt_axi_m_arlock),
      .s_axi_arcache(o_noc_lt_axi_m_arcache),
      .s_axi_arprot (o_noc_lt_axi_m_arprot),
      .s_axi_arvalid(o_noc_lt_axi_m_arvalid),
      .s_axi_arready(i_noc_lt_axi_m_arready),
      .s_axi_rid    (i_noc_lt_axi_m_rid),
      .s_axi_rdata  (i_noc_lt_axi_m_rdata),
      .s_axi_rresp  (i_noc_lt_axi_m_rresp),
      .s_axi_rlast  (i_noc_lt_axi_m_rlast),
      .s_axi_rvalid (i_noc_lt_axi_m_rvalid),
      .s_axi_rready (o_noc_lt_axi_m_rready)
  );


  // =============================================================================================================
  // Instantiate DUT
  // =============================================================================================================
  ai_core_p dut (
      .i_clk(clk),                           /// Fast Clock, positive edge triggered
      .i_ref_clk(ref_clk),                   /// Slow Ref Clock, positive edge triggered
      .i_ao_rst_n(apb_reset_if.presetn),     /// Asynchronous POR, always On reset, active low
      .i_global_rst_n(~axi_reset_if.reset),  /// Asynchronous global reset, active low
      .i_cid('h1),
      .i_inter_core_sync('0),
      .i_thermal_throttle_async('0),
      .i_clock_throttle_async('0),
      .i_aic_throttle_async('0),
      .i_thermal_warning_async('0),
      .i_aic_boost_ack_async('0),
      .o_aic_boost_req_async(),
      .o_tok_prod_ocpl_m_maddr(),
      .o_tok_prod_ocpl_m_mcmd(),
      .o_tok_prod_ocpl_m_mdata(),
      .o_tok_cons_ocpl_s_scmdaccept(),
      .o_irq(),
      .i_msip_async(0),
      .i_mtip_async(0),
      .i_debug_int_async(0),
      .i_resethaltreq_async(0),
      .o_hart_unavail_async(),
      .o_hart_under_reset_async(),
      .o_stoptime_async(),
      .io_ibias_ts(),
      .io_vsense_ts(),
      .o_aic_obs(),
      .i_reserved(),
      .o_reserved(),
      //noc ht master //ht slave 0
      .o_noc_ht_axi_m_awaddr(axi_if.slave_if[0].awaddr),
      .o_noc_ht_axi_m_awid(axi_if.slave_if[0].awid),
      .o_noc_ht_axi_m_awlen(axi_if.slave_if[0].awlen),
      .o_noc_ht_axi_m_awsize(axi_if.slave_if[0].awsize[2:0]),
      .o_noc_ht_axi_m_awburst(axi_if.slave_if[0].awburst),
      .o_noc_ht_axi_m_awcache(axi_if.slave_if[0].awcache),
      .o_noc_ht_axi_m_awprot(axi_if.slave_if[0].awprot),
      .o_noc_ht_axi_m_awlock(axi_if.slave_if[0].awlock),
      .o_noc_ht_axi_m_awvalid(axi_if.slave_if[0].awvalid),
      .i_noc_ht_axi_m_awready(axi_if.slave_if[0].awready),
      .o_noc_ht_axi_m_wdata(axi_if.slave_if[0].wdata),
      .o_noc_ht_axi_m_wstrb(axi_if.slave_if[0].wstrb),
      .o_noc_ht_axi_m_wlast(axi_if.slave_if[0].wlast),
      .o_noc_ht_axi_m_wvalid(axi_if.slave_if[0].wvalid),
      .i_noc_ht_axi_m_wready(axi_if.slave_if[0].wready),
      .i_noc_ht_axi_m_bvalid(axi_if.slave_if[0].bvalid),
      .i_noc_ht_axi_m_bid(axi_if.slave_if[0].bid),
      .i_noc_ht_axi_m_bresp(axi_if.slave_if[0].bresp),
      .o_noc_ht_axi_m_bready(axi_if.slave_if[0].bready),
      .o_noc_ht_axi_m_araddr(axi_if.slave_if[0].araddr),
      .o_noc_ht_axi_m_arid(axi_if.slave_if[0].arid),
      .o_noc_ht_axi_m_arlen(axi_if.slave_if[0].arlen),
      .o_noc_ht_axi_m_arsize(axi_if.slave_if[0].arsize[2:0]),
      .o_noc_ht_axi_m_arburst(axi_if.slave_if[0].arburst),
      .o_noc_ht_axi_m_arcache(axi_if.slave_if[0].arcache),
      .o_noc_ht_axi_m_arprot(axi_if.slave_if[0].arprot),
      .o_noc_ht_axi_m_arlock(axi_if.slave_if[0].arlock),
      .o_noc_ht_axi_m_arvalid(axi_if.slave_if[0].arvalid),
      .i_noc_ht_axi_m_arready(axi_if.slave_if[0].arready),
      .i_noc_ht_axi_m_rvalid(axi_if.slave_if[0].rvalid),
      .i_noc_ht_axi_m_rlast(axi_if.slave_if[0].rlast),
      .i_noc_ht_axi_m_rid(axi_if.slave_if[0].rid),
      .i_noc_ht_axi_m_rdata(axi_if.slave_if[0].rdata),
      .i_noc_ht_axi_m_rresp(axi_if.slave_if[0].rresp),
      .o_noc_ht_axi_m_rready(axi_if.slave_if[0].rready),

      //noc lt master //lt slave 1
      .o_noc_lt_axi_m_awaddr (o_noc_lt_axi_m_awaddr),
      .o_noc_lt_axi_m_awid   (o_noc_lt_axi_m_awid),
      .o_noc_lt_axi_m_awlen  (o_noc_lt_axi_m_awlen),
      .o_noc_lt_axi_m_awsize (o_noc_lt_axi_m_awsize),
      .o_noc_lt_axi_m_awburst(o_noc_lt_axi_m_awburst),
      .o_noc_lt_axi_m_awcache(o_noc_lt_axi_m_awcache),
      .o_noc_lt_axi_m_awprot (o_noc_lt_axi_m_awprot),
      .o_noc_lt_axi_m_awlock (o_noc_lt_axi_m_awlock),
      .o_noc_lt_axi_m_awvalid(o_noc_lt_axi_m_awvalid),
      .i_noc_lt_axi_m_awready(i_noc_lt_axi_m_awready),
      .o_noc_lt_axi_m_wdata  (o_noc_lt_axi_m_wdata),
      .o_noc_lt_axi_m_wstrb  (o_noc_lt_axi_m_wstrb),
      .o_noc_lt_axi_m_wlast  (o_noc_lt_axi_m_wlast),
      .o_noc_lt_axi_m_wvalid (o_noc_lt_axi_m_wvalid),
      .i_noc_lt_axi_m_wready (i_noc_lt_axi_m_wready),
      .i_noc_lt_axi_m_bvalid (i_noc_lt_axi_m_bvalid),
      .i_noc_lt_axi_m_bid    (i_noc_lt_axi_m_bid),
      .i_noc_lt_axi_m_bresp  (i_noc_lt_axi_m_bresp),
      .o_noc_lt_axi_m_bready (o_noc_lt_axi_m_bready),
      .o_noc_lt_axi_m_araddr (o_noc_lt_axi_m_araddr),
      .o_noc_lt_axi_m_arid   (o_noc_lt_axi_m_arid),
      .o_noc_lt_axi_m_arlen  (o_noc_lt_axi_m_arlen),
      .o_noc_lt_axi_m_arsize (o_noc_lt_axi_m_arsize),
      .o_noc_lt_axi_m_arburst(o_noc_lt_axi_m_arburst),
      .o_noc_lt_axi_m_arcache(o_noc_lt_axi_m_arcache),
      .o_noc_lt_axi_m_arprot (o_noc_lt_axi_m_arprot),
      .o_noc_lt_axi_m_arlock (o_noc_lt_axi_m_arlock),
      .o_noc_lt_axi_m_arvalid(o_noc_lt_axi_m_arvalid),
      .i_noc_lt_axi_m_arready(i_noc_lt_axi_m_arready),
      .i_noc_lt_axi_m_rvalid (i_noc_lt_axi_m_rvalid),
      .i_noc_lt_axi_m_rlast  (i_noc_lt_axi_m_rlast),
      .i_noc_lt_axi_m_rid    (i_noc_lt_axi_m_rid),
      .i_noc_lt_axi_m_rdata  (i_noc_lt_axi_m_rdata),
      .i_noc_lt_axi_m_rresp  (i_noc_lt_axi_m_rresp),
      .o_noc_lt_axi_m_rready (o_noc_lt_axi_m_rready),

      //noc lt slave //lt master 0
      .i_noc_lt_axi_s_awaddr (axi_if.master_if[0].awaddr),
      .i_noc_lt_axi_s_awid   (axi_if.master_if[0].awid),
      .i_noc_lt_axi_s_awlen  (axi_if.master_if[0].awlen),
      .i_noc_lt_axi_s_awsize (axi_if.master_if[0].awsize[2:0]),
      .i_noc_lt_axi_s_awburst(axi_if.master_if[0].awburst),
      .i_noc_lt_axi_s_awcache(axi_if.master_if[0].awcache),
      .i_noc_lt_axi_s_awprot (axi_if.master_if[0].awprot),
      .i_noc_lt_axi_s_awlock (axi_if.master_if[0].awlock),
      .i_noc_lt_axi_s_awvalid(axi_if.master_if[0].awvalid),
      .o_noc_lt_axi_s_awready(axi_if.master_if[0].awready),
      .i_noc_lt_axi_s_wdata  (axi_if.master_if[0].wdata),
      .i_noc_lt_axi_s_wstrb  (axi_if.master_if[0].wstrb),
      .i_noc_lt_axi_s_wlast  (axi_if.master_if[0].wlast),
      .i_noc_lt_axi_s_wvalid (axi_if.master_if[0].wvalid),
      .o_noc_lt_axi_s_wready (axi_if.master_if[0].wready),
      .o_noc_lt_axi_s_bvalid (axi_if.master_if[0].bvalid),
      .o_noc_lt_axi_s_bid    (axi_if.master_if[0].bid),
      .o_noc_lt_axi_s_bresp  (axi_if.master_if[0].bresp),
      .i_noc_lt_axi_s_bready (axi_if.master_if[0].bready),
      .i_noc_lt_axi_s_araddr (axi_if.master_if[0].araddr),
      .i_noc_lt_axi_s_arid   (axi_if.master_if[0].arid),
      .i_noc_lt_axi_s_arlen  (axi_if.master_if[0].arlen),
      .i_noc_lt_axi_s_arsize (axi_if.master_if[0].arsize[2:0]),
      .i_noc_lt_axi_s_arburst(axi_if.master_if[0].arburst),
      .i_noc_lt_axi_s_arcache(axi_if.master_if[0].arcache),
      .i_noc_lt_axi_s_arprot (axi_if.master_if[0].arprot),
      .i_noc_lt_axi_s_arlock (axi_if.master_if[0].arlock),
      .i_noc_lt_axi_s_arvalid(axi_if.master_if[0].arvalid),
      .o_noc_lt_axi_s_arready(axi_if.master_if[0].arready),
      .o_noc_lt_axi_s_rvalid (axi_if.master_if[0].rvalid),
      .o_noc_lt_axi_s_rlast  (axi_if.master_if[0].rlast),
      .o_noc_lt_axi_s_rid    (axi_if.master_if[0].rid),
      .o_noc_lt_axi_s_rdata  (axi_if.master_if[0].rdata),
      .o_noc_lt_axi_s_rresp  (axi_if.master_if[0].rresp),
      .i_noc_lt_axi_s_rready (axi_if.master_if[0].rready),

      // APB
      .i_cfg_apb4_s_paddr  (apb_if.paddr),
      .i_cfg_apb4_s_pwdata (apb_if.pwdata),
      .i_cfg_apb4_s_pwrite (apb_if.pwrite),
      .i_cfg_apb4_s_psel   (apb_if.psel[0]),
      .i_cfg_apb4_s_penable(apb_if.penable),
      .i_cfg_apb4_s_pstrb  (apb_if.pstrb),
      .i_cfg_apb4_s_pprot  (apb_if.pprot),
      .o_cfg_apb4_s_pready (apb_if.pready[0]),
      .o_cfg_apb4_s_prdata (apb_if.prdata[0]),
      .o_cfg_apb4_s_pslverr(apb_if.pslverr[0]),

      .o_noc_async_idle_req(),
      .i_noc_async_idle_ack(),
      .i_noc_async_idle_val(),
      .o_noc_ocpl_tok_async_idle_req(),
      .i_noc_ocpl_tok_async_idle_ack(),
      .i_noc_ocpl_tok_async_idle_val(),
      .o_noc_clken(),
      .o_noc_rst_n(),

      .tck(1'b0),
      .trst(1'b0),
      .tms(1'b1),
      .tdi(1'b0),
      .tdo_en(),
      .tdo(),

      .test_mode(1'b0),

      .ssn_bus_clk(1'b0),
      .ssn_bus_data_in('d0),
      .ssn_bus_data_out(),
      .bisr_clk(1'b0),
      .bisr_reset(1'b1),
      .bisr_shift_en(1'b0),
      .bisr_si(1'b0),
      .bisr_so()
  );


  `include "memory_preloading_macros.svh"
  import memory_preloading_pkg::*;


  `include "spm_utils.svh"

  //preloading aicore spm
  task automatic preload_aicore_spm();
    string hex_path;
    $display("Init AICORE SPM to 0 (avoid X when prefetching nullptr)");
    preload_spm_single_value(0);
    if ($value$plusargs("HEX_PATH=%s", hex_path)) begin
      preload_spm_file(hex_path);
      return;
    end
    $error("Not preloading anything to AICORE SPM");
  endtask

  task automatic preload_sys_spm();
    string mem_file;
    string hex_path;
    if ($value$plusargs("HEX_PATH=%s", hex_path)) begin
      `MEMORY_PRELOADING_FAKE_SYS_SPM_FILE(i_fake_sys_spm.mem, hex_path, ~axi_rst, aipu_addr_map_pkg::SYS_SPM_ST_ADDR>>3)
      return;
    end
    $error("Not preloading anything to SYS SPM");
  endtask

  `include "l1_utils.svh"

  //preloading aicore l1
  task automatic preload_aicore_l1();
    string hex_path;
    $display("Init AICORE L1 to 0 (avoid X when prefetching nullptr)");
    preload_l1_single_value(0);
    if ($value$plusargs("HEX_PATH=%s", hex_path)) begin
      preload_l1_file(hex_path);
      return;
    end
    $error("Not preloading anything to AICORE L1");
  endtask

  `define CVA6_PATH hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_ai_core_cva6v

  function static void cva6v_assertoff();
    // from Raymonds's hw/vendor/axelera/cva6v/default/dv/rtl/uvm_top.sv
    // TODO: known failure in PMP https://github.com/axelera-ai/hw.riscv/issues/542
    $assertoff(
        0, `CVA6_PATH.u_cva6v.u_cva6v_top.i_cva6.ex_stage_i.lsu_i.gen_mmu_sv39.i_cva6_mmu.i_pmp_if);
    // TODO: known failure in PMP https://github.com/axelera-ai/hw.riscv/issues/542
    $assertoff(
        0,
        `CVA6_PATH.u_cva6v.u_cva6v_top.i_cva6.ex_stage_i.lsu_i.gen_mmu_sv39.i_cva6_mmu.i_pmp_data);
    // TODO: to be debuuged
    $assertoff(0, `CVA6_PATH.u_cva6v.u_cva6v_top.i_cva6.gen_cache_wb.i_cache_subsystem);
  endfunction

  initial begin
    u_axe_clk_generator.set_clock(.freq_mhz(aicore_freq_mhz), .duty(50));
    u_axe_ref_clk_generator.set_clock(.freq_mhz(ref_freq_mhz), .duty(50));
    clk_en = 1'b1;
    ref_clk_en = 1'b1;
    u_apb_rst_generator.async_rst(.duration_ns(100));
    u_axi_rst_generator.async_rst(.duration_ns(50));
  end

  initial begin
    cva6v_assertoff();
    //TODO-Rafael will give issue number from LS
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[0].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[1].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[2].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[3].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[4].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[5].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_odr[6].u_odr.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_odr[7].u_odr.u_defmem.chk_mem_rdata_not_all_x);

    @(posedge ref_clk);
    wait (axi_rst === 0);
    preload_aicore_spm();
    preload_sys_spm();
    preload_aicore_l1();
  end

  `define AICORE_L1_PATH hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem

  // =============================================================================================================
  // Configuration database settings
  // =============================================================================================================
  initial begin
    import uvm_pkg::uvm_config_db;
    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.sequencer", "reset_mp",axi_reset_if.axi_reset_modport);  // Set the reset interface on the virtual sequencer

    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.env.m_axi_system_env", "vif",axi_if);  //Provide the AXI SV interface to the AXI System ENV. This step establishes the connection between the AXI System ENV and the DUT through the AXI interface.

    uvm_config_db#(virtual apb_reset_if.apb_reset_modport)::set(uvm_root::get(), "uvm_test_top.env.apb_sequencer", "reset_mp",apb_reset_if.apb_reset_modport);
    uvm_config_db#(svt_apb_vif)::set(uvm_root::get(), "uvm_test_top.env.m_apb_system_env", "vif",apb_if);

    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set( uvm_root::get(), "uvm_test_top.env.m_ls_env.m_axi_virt_sqr", "reset_mp", axi_reset_if.axi_reset_modport);
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.env.m_ls_env.m_axi_system_env", "vif", axi_ls_if);

    uvm_config_db#(virtual aic_ls_if)::set(null, "uvm_test_top.env.m_ls_env.m_aic_ls_agt", "vif", if_aic_ls);
    uvm_config_db#(virtual ai_core_top_if)::set(uvm_root::get(), "*", "tb_cfg_if", tb_cfg_if);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.env.m_ls_env.m_m_ifd0_agt", "vif", if_m_ifd0);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.env.m_ls_env.m_m_ifd1_agt", "vif", if_m_ifd1);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.env.m_ls_env.m_m_ifd2_agt", "vif", if_m_ifd2);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.env.m_ls_env.m_m_ifdw_agt", "vif", if_m_ifdw);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.env.m_ls_env.m_m_odr_agt", "vif", if_m_odr);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.env.m_ls_env.m_d_ifd0_agt", "vif", if_d_ifd0);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.env.m_ls_env.m_d_ifd1_agt", "vif", if_d_ifd1);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.env.m_ls_env.m_d_odr_agt", "vif", if_d_odr);
  end


  initial begin
    run_test();
  end

endmodule : hdl_top
