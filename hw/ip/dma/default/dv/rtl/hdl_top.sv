// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Top-level TestBench instancing and connecting the DUT with the AXI Master and Slave Interfaces
// Owner: Sultan.Khan
// --------------------------------------------------

// This introduces the AXI Master and Slave VIP Interfaces 
`define AXI_VIP


module hdl_top;
  // Time unit and precision
  timeunit 1ns; 
  timeprecision 1ps;

  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import dma_pkg::*;
  import dma_ip_common_pkg::*;
  import dma_ip_test_pkg::*;
//  import aic_common_pkg::*;
//  import imc_bank_pkg::*;

`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif

  // Include BIND files for axi4PC (AXI PROTCOL CHECKER) and axi_perf_tracker
  `include "axi4pc/bind_dma.svh"
  `include "axi_perf_tracker/bind_axi_tracker_dma.svh"
  
  // DMA Assertions
  `include "dma_assertions/bind_dma_assertions.svh"

  realtime  C_MAX_SIMTIME = 200us;
  realtime  current_simtime;
  
  logic clk_en;   
  logic reset;
  logic sys_clk;
  logic sys_rst_n;

  //--------------------------------------------------
  // DUT Port Signals 
  //--------------------------------------------------

  // AXI Slave I/F of DUT
  // --------------------
  logic                 dut_axi_s_awvalid;            
  logic [ 40-1:0]       dut_axi_s_awaddr;
  logic [  4-1:0]       dut_axi_s_awid;
  axi_pkg::axi_len_t    dut_axi_s_awlen;
  axi_pkg::axi_size_e   dut_axi_s_awsize;
  axi_pkg::axi_burst_e  dut_axi_s_awburst;
  logic                 dut_axi_s_awlock;
  axi_pkg::axi_cache_e  dut_axi_s_awcache;
  axi_pkg::axi_prot_t   dut_axi_s_awprot;
  logic                 dut_axi_s_awready;
  // AXI write data channel
  logic                 dut_axi_s_wvalid;
  logic                 dut_axi_s_wlast;
  logic [64-1:0]        dut_axi_s_wdata;
  logic [ 8-1:0]        dut_axi_s_wstrb;
  logic                 dut_axi_s_wready;
  // AXI write response channel
  logic                 dut_axi_s_bvalid;
  logic [  4-1:0]       dut_axi_s_bid;
  axi_pkg::axi_resp_e   dut_axi_s_bresp;
  logic                 dut_axi_s_bready;
  // AXI read address channel
  logic                 dut_axi_s_arvalid;
  logic [ 40-1:0]       dut_axi_s_araddr;
  logic [  4-1:0]       dut_axi_s_arid;
  axi_pkg::axi_len_t    dut_axi_s_arlen;
  axi_pkg::axi_size_e   dut_axi_s_arsize;
  axi_pkg::axi_burst_e  dut_axi_s_arburst;
  logic                 dut_axi_s_arlock;
  axi_pkg::axi_cache_e  dut_axi_s_arcache;
  axi_pkg::axi_prot_t   dut_axi_s_arprot;
  logic                 dut_axi_s_arready;
  // AXI read data/response channel
  logic                 dut_axi_s_rvalid;
  logic                 dut_axi_s_rlast;
  logic [  4-1:0]       dut_axi_s_rid;
  logic [64-1:0]        dut_axi_s_rdata;
  axi_pkg::axi_resp_t   dut_axi_s_rresp;
  logic                 dut_axi_s_rready;

  // AXI Master I/F of DUT (Data Ports)
  // ----------------------------------
  // AXI 4 Data Ports
  // AXI write address channel
  logic                 dut_axi_m_awvalid [NUM_PORTS];
  logic [ 40-1:0]       dut_axi_m_awaddr  [NUM_PORTS];
  logic [  9-1:0]       dut_axi_m_awid    [NUM_PORTS];
  axi_pkg::axi_len_t    dut_axi_m_awlen   [NUM_PORTS];
  axi_pkg::axi_size_e   dut_axi_m_awsize  [NUM_PORTS];
  axi_pkg::axi_burst_e  dut_axi_m_awburst [NUM_PORTS];
  logic                 dut_axi_m_awlock  [NUM_PORTS];
  axi_pkg::axi_cache_e  dut_axi_m_awcache [NUM_PORTS];
  axi_pkg::axi_prot_t   dut_axi_m_awprot  [NUM_PORTS];
  logic                 dut_axi_m_awready [NUM_PORTS];
  // AXI write data channel
  logic                 dut_axi_m_wvalid  [NUM_PORTS];
  logic                 dut_axi_m_wlast   [NUM_PORTS];
  logic [512-1:0]       dut_axi_m_wdata   [NUM_PORTS];
  logic [ 64-1:0]       dut_axi_m_wstrb   [NUM_PORTS];
  logic                 dut_axi_m_wready  [NUM_PORTS];
  // AXI write resp     dutnsechannel
  logic                 dut_axi_m_bvalid  [NUM_PORTS];
  logic [  9-1:0]       dut_axi_m_bid     [NUM_PORTS];
  axi_pkg::axi_resp_e   dut_axi_m_bresp   [NUM_PORTS];
  logic                 dut_axi_m_bready  [NUM_PORTS];
  // AXI read address channel
  logic                 dut_axi_m_arvalid [NUM_PORTS];
  logic [ 40-1:0]       dut_axi_m_araddr  [NUM_PORTS];
  logic [  9-1:0]       dut_axi_m_arid    [NUM_PORTS];
  axi_pkg::axi_len_t    dut_axi_m_arlen   [NUM_PORTS];
  axi_pkg::axi_size_e   dut_axi_m_arsize  [NUM_PORTS];
  axi_pkg::axi_burst_e  dut_axi_m_arburst [NUM_PORTS];
  logic                 dut_axi_m_arlock  [NUM_PORTS];
  axi_pkg::axi_cache_e  dut_axi_m_arcache [NUM_PORTS];
  axi_pkg::axi_prot_t   dut_axi_m_arprot  [NUM_PORTS];
  logic                 dut_axi_m_arready [NUM_PORTS];
  // AXI read data/responsechannel
  logic                 dut_axi_m_rvalid  [NUM_PORTS];
  logic                 dut_axi_m_rlast   [NUM_PORTS];
  logic [  9-1:0]       dut_axi_m_rid     [NUM_PORTS];
  logic [512-1:0]       dut_axi_m_rdata   [NUM_PORTS];
  axi_pkg::axi_resp_e   dut_axi_m_rresp   [NUM_PORTS];
  logic                 dut_axi_m_rready  [NUM_PORTS];
  
  // DUT IRQ lines - 1 per channel
  logic [dma_ip_common_pkg::NUM_CHANNELS-1:0]   dut_channel_irqs;
  
  logic [5:0]           dut_tok_prod_vld[dma_ip_common_pkg::NUM_CHANNELS];
  logic [5:0]           dut_tok_prod_rdy[dma_ip_common_pkg::NUM_CHANNELS];
  logic [5:0]           dut_tok_cons_vld[dma_ip_common_pkg::NUM_CHANNELS];
  logic [5:0]           dut_tok_cons_rdy[dma_ip_common_pkg::NUM_CHANNELS];

  logic [dma_ip_common_pkg::NUM_CHANNELS-1:0]   dut_ts_start;
  logic [dma_ip_common_pkg::NUM_CHANNELS-1:0]   dut_ts_end;
  logic [dma_ip_common_pkg::NUM_CHANNELS-1:0]   dut_acd_sync;

  dma_pkg::dma_dev_obs_t [dma_ip_common_pkg::NUM_CHANNELS-1:0] dut_o_obs;             


  // DFT signals
  // Observation signals

  int   dma_clk_freq_mhz = 800;
  time  dma_clk_tol_ps   = 10;
      
  // =============================================================================================================
  // Instantiate interfaces and BFMs and assignments
  // =============================================================================================================

`ifdef AXI_VIP
  
  // VIP Interface instance representing the AXI system
  // Number of AXI Master and Slave VIPs defined by uvm/env/axi_vip_config.sv 
  //   - 1 AXI MASTER VIP
  //   - 2 AXI SLAVE VIPs
  //
  // Connect up the clks and resets to the VIPs
  
  svt_axi_if axi_if ();
  assign axi_if.common_aclk        = sys_clk;
  assign axi_if.master_if[0].aclk  = sys_clk;
  assign axi_if.slave_if[0].aclk   = sys_clk;
  assign axi_if.slave_if[1].aclk   = sys_clk;
  
  assign axi_if.master_if[0].aresetn =  sys_rst_n;
  assign axi_if.slave_if[0].aresetn  =  sys_rst_n;
  assign axi_if.slave_if[1].aresetn  =  sys_rst_n;

`endif

  irq_if  dma_irq_if();
  assign dma_irq_if.clk = sys_clk;
  
  clk_if  dma_clk_if();
  assign  dma_clk_if.clk = sys_clk;

// =============================================================================================================
// Assign the DUT Ports to various interfaces.
// =============================================================================================================
// By default, DUT (DMA IP RTL) is connected to the AXI_MASTER VIP and 2 AXI_SLAVE VIPs.
//
// However, by defining particular defines on the command line, we can bypass the DUT for standalone AXI VIP Testing too 
// This is to allow pipecleaning of axi-transactions and check operation of the AXI MASTER and SLAVE VIPs prior to DMA testing
// And even to assist in the debug of AXI SLAVE VIP behaviour when it doesnt operate accordingly
//
//   AXI_VIP_MSTR_2_SLV_DIRECT  Connects AXI Master VIP directly to 1 of the AXI SLAVE VIPs
//   AXI_VIP_USE_SLAVE_1        Connects the AXI MASTER VIP to the AXI_SLAVE_1_VIP (else connect to the AXI SLAVE_0 VIP)

`ifndef AXI_VIP_MSTR_2_SLV_DIRECT

  // ------------------------------------------------------------------
  // Connect AXI Master and Slave VIPs to the DUT AXI lines (default connections)

  // AXI Master VIP to DUT AXI Slave (Register) Interface
  assign  dut_axi_s_awvalid = axi_if.master_if[0].awvalid;
  assign  dut_axi_s_awaddr  = axi_if.master_if[0].awaddr;
  assign  dut_axi_s_awid    = axi_if.master_if[0].awid;
  assign  dut_axi_s_awlen   = axi_if.master_if[0].awlen;
  assign  dut_axi_s_awsize  = axi_if.master_if[0].awsize;
  assign  dut_axi_s_awburst = axi_if.master_if[0].awburst;
  assign  dut_axi_s_awlock  = axi_if.master_if[0].awlock;
  assign  dut_axi_s_awcache = axi_if.master_if[0].awcache;
  assign  dut_axi_s_awprot  = axi_if.master_if[0].awprot;
  assign  axi_if.master_if[0].awready = dut_axi_s_awready;

  assign  dut_axi_s_wvalid  = axi_if.master_if[0].wvalid;
  assign  dut_axi_s_wlast   = axi_if.master_if[0].wlast;
  assign  dut_axi_s_wdata   = axi_if.master_if[0].wdata;
  assign  dut_axi_s_wstrb   = axi_if.master_if[0].wstrb;
  assign  axi_if.master_if[0].wready = dut_axi_s_wready; 

  assign  axi_if.master_if[0].bvalid = dut_axi_s_bvalid;
  assign  axi_if.master_if[0].bid    = dut_axi_s_bid;   
  assign  axi_if.master_if[0].bresp  = dut_axi_s_bresp; 
  assign  dut_axi_s_bready  = axi_if.master_if[0].bready;

  assign  dut_axi_s_arvalid = axi_if.master_if[0].arvalid;
  assign  dut_axi_s_araddr  = axi_if.master_if[0].araddr;
  assign  dut_axi_s_arid    = axi_if.master_if[0].arid;
  assign  dut_axi_s_arlen   = axi_if.master_if[0].arlen;
  assign  dut_axi_s_arsize  = axi_if.master_if[0].arsize;
  assign  dut_axi_s_arburst = axi_if.master_if[0].arburst;
  assign  dut_axi_s_arlock  = axi_if.master_if[0].arlock;
  assign  dut_axi_s_arcache = axi_if.master_if[0].arcache;
  assign  dut_axi_s_arprot  = axi_if.master_if[0].arprot;
  assign  axi_if.master_if[0].arready = dut_axi_s_arready;

  assign  axi_if.master_if[0].rvalid = dut_axi_s_rvalid;
  assign  axi_if.master_if[0].rlast  = dut_axi_s_rlast; 
  assign  axi_if.master_if[0].rid    = dut_axi_s_rid;   
  assign  axi_if.master_if[0].rdata  = dut_axi_s_rdata; 
  assign  axi_if.master_if[0].rresp  = dut_axi_s_rresp; 
  assign  dut_axi_s_rready = axi_if.master_if[0].rready;

  // DUT AXI Master (Data Port) Interfaces, to AXI SLAVE VIPs
  // To AXI SLAVE 0 VIP
   
  assign axi_if.slave_if[0].awvalid   = dut_axi_m_awvalid[0];
  assign axi_if.slave_if[0].awaddr    = dut_axi_m_awaddr[0];
  assign axi_if.slave_if[0].awid      = dut_axi_m_awid[0];
  assign axi_if.slave_if[0].awlen     = dut_axi_m_awlen[0];
  assign axi_if.slave_if[0].awsize    = dut_axi_m_awsize[0];
  assign axi_if.slave_if[0].awburst   = dut_axi_m_awburst[0];
  assign axi_if.slave_if[0].awlock    = dut_axi_m_awlock[0];
  assign axi_if.slave_if[0].awcache   = dut_axi_m_awcache[0];
  assign axi_if.slave_if[0].awprot    = dut_axi_m_awprot[0];
  assign dut_axi_m_awready[0]         = axi_if.slave_if[0].awready;
  
  assign axi_if.slave_if[0].wvalid    = dut_axi_m_wvalid[0];
  assign axi_if.slave_if[0].wlast     = dut_axi_m_wlast[0];
  assign axi_if.slave_if[0].wdata     = dut_axi_m_wdata[0];
  assign axi_if.slave_if[0].wstrb     = dut_axi_m_wstrb[0];
  assign dut_axi_m_wready[0]          = axi_if.slave_if[0].wready;

  assign dut_axi_m_bvalid[0]          = axi_if.slave_if[0].bvalid;
  assign dut_axi_m_bid[0]             = axi_if.slave_if[0].bid;
  assign dut_axi_m_bresp[0]           = axi_pkg::axi_resp_e'(axi_if.slave_if[0].bresp);
  assign axi_if.slave_if[0].bready    = dut_axi_m_bready[0];
  
  assign axi_if.slave_if[0].arvalid   = dut_axi_m_arvalid[0];
  assign axi_if.slave_if[0].araddr    = dut_axi_m_araddr[0];
  assign axi_if.slave_if[0].arid      = dut_axi_m_arid[0];
  assign axi_if.slave_if[0].arlen     = dut_axi_m_arlen[0];
  assign axi_if.slave_if[0].arsize    = dut_axi_m_arsize[0];
  assign axi_if.slave_if[0].arburst   = dut_axi_m_arburst[0];
  assign axi_if.slave_if[0].arlock    = dut_axi_m_arlock[0];
  assign axi_if.slave_if[0].arcache   = dut_axi_m_arcache[0];
  assign axi_if.slave_if[0].arprot    = dut_axi_m_arprot[0];
  assign dut_axi_m_arready[0]         = axi_if.slave_if[0].arready;

  assign dut_axi_m_rvalid[0]          = axi_if.slave_if[0].rvalid;
  assign dut_axi_m_rlast[0]           = axi_if.slave_if[0].rlast;
  assign dut_axi_m_rid[0]             = axi_if.slave_if[0].rid;
  assign dut_axi_m_rdata[0]           = axi_if.slave_if[0].rdata;
  assign dut_axi_m_rresp[0]           = axi_pkg::axi_resp_e'(axi_if.slave_if[0].rresp);
  assign axi_if.slave_if[0].rready    = dut_axi_m_rready[0];

  // To AXI SLAVE 1 VIP
  assign axi_if.slave_if[1].awvalid   = dut_axi_m_awvalid[1];
  assign axi_if.slave_if[1].awaddr    = dut_axi_m_awaddr[1];
  assign axi_if.slave_if[1].awid      = dut_axi_m_awid[1];
  assign axi_if.slave_if[1].awlen     = dut_axi_m_awlen[1];
  assign axi_if.slave_if[1].awsize    = dut_axi_m_awsize[1];
  assign axi_if.slave_if[1].awburst   = dut_axi_m_awburst[1];
  assign axi_if.slave_if[1].awlock    = dut_axi_m_awlock[1];
  assign axi_if.slave_if[1].awcache   = dut_axi_m_awcache[1];
  assign axi_if.slave_if[1].awprot    = dut_axi_m_awprot[1];
  assign dut_axi_m_awready[1]         = axi_if.slave_if[1].awready;
  
  assign axi_if.slave_if[1].wvalid    = dut_axi_m_wvalid[1];
  assign axi_if.slave_if[1].wlast     = dut_axi_m_wlast[1];
  assign axi_if.slave_if[1].wdata     = dut_axi_m_wdata[1];
  assign axi_if.slave_if[1].wstrb     = dut_axi_m_wstrb[1];
  assign dut_axi_m_wready[1]          = axi_if.slave_if[1].wready;

  assign dut_axi_m_bvalid[1]          = axi_if.slave_if[1].bvalid;
  assign dut_axi_m_bid[1]             = axi_if.slave_if[1].bid;
  assign dut_axi_m_bresp[1]           = axi_pkg::axi_resp_e'(axi_if.slave_if[1].bresp);
  assign axi_if.slave_if[1].bready    = dut_axi_m_bready[1];
  
  assign axi_if.slave_if[1].arvalid   = dut_axi_m_arvalid[1];
  assign axi_if.slave_if[1].araddr    = dut_axi_m_araddr[1];
  assign axi_if.slave_if[1].arid      = dut_axi_m_arid[1];
  assign axi_if.slave_if[1].arlen     = dut_axi_m_arlen[1];
  assign axi_if.slave_if[1].arsize    = dut_axi_m_arsize[1];
  assign axi_if.slave_if[1].arburst   = dut_axi_m_arburst[1];
  assign axi_if.slave_if[1].arlock    = dut_axi_m_arlock[1];
  assign axi_if.slave_if[1].arcache   = dut_axi_m_arcache[1];
  assign axi_if.slave_if[1].arprot    = dut_axi_m_arprot[1];
  assign dut_axi_m_arready[1]         = axi_if.slave_if[1].arready;

  assign dut_axi_m_rvalid[1]          = axi_if.slave_if[1].rvalid;
  assign dut_axi_m_rlast[1]           = axi_if.slave_if[1].rlast;
  assign dut_axi_m_rid[1]             = axi_if.slave_if[1].rid;
  assign dut_axi_m_rdata[1]           = axi_if.slave_if[1].rdata;
  assign dut_axi_m_rresp[1]           = axi_pkg::axi_resp_e'(axi_if.slave_if[1].rresp);
  assign axi_if.slave_if[1].rready    = dut_axi_m_rready[1];

  // Assign the IRQ Lines Individually to the irq agent
  assign dma_irq_if.irq               = dut_channel_irqs;
 
  // TBD _ Assign the token signals
  // dut_tok_prod_vld  // output
  // dut_tok_cons_rdy  // output

  // TBD - Assign the TS signals
  // dut_ts_start  // output
  // dut_ts_end    // output
  // dut_acd_sync  // output
  // dut_o_obs     // output

  initial begin
    for (int i=0; i < dma_ip_common_pkg::NUM_CHANNELS; i++) begin
      dut_tok_prod_rdy[i] = '1;  // TBD
      dut_tok_cons_vld[i] = '1;  // TBD
    end
  end
  
`else

`ifndef AXI_VIP_USE_SLAVE_1

  // ------------------------------------------------------------------
  // Connect AXI_MASTER VIP to AXI_SLAVE_VIP[0]
 
  assign axi_if.slave_if[0].awvalid   = axi_if.master_if[0].awvalid;
  assign axi_if.slave_if[0].awaddr    = axi_if.master_if[0].awaddr;
  assign axi_if.slave_if[0].awid      = axi_if.master_if[0].awid;
  assign axi_if.slave_if[0].awlen     = axi_if.master_if[0].awlen;
  assign axi_if.slave_if[0].awsize    = axi_if.master_if[0].awsize;
  assign axi_if.slave_if[0].awburst   = axi_if.master_if[0].awburst;
  assign axi_if.slave_if[0].awlock    = axi_if.master_if[0].awlock;
  assign axi_if.slave_if[0].awcache   = axi_if.master_if[0].awcache;
  assign axi_if.slave_if[0].awprot    = axi_if.master_if[0].awprot;
  assign axi_if.master_if[0].awready  = axi_if.slave_if[0].awready;
  assign axi_if.slave_if[0].wvalid    = axi_if.master_if[0].wvalid;
  assign axi_if.slave_if[0].wlast     = axi_if.master_if[0].wlast;
  assign axi_if.slave_if[0].wdata     = axi_if.master_if[0].wdata;
  assign axi_if.slave_if[0].wstrb     = axi_if.master_if[0].wstrb;
  assign axi_if.master_if[0].wready   = axi_if.slave_if[0].wready;
  assign axi_if.master_if[0].bvalid   = axi_if.slave_if[0].bvalid;
  assign axi_if.master_if[0].bid      = axi_if.slave_if[0].bid;
  assign axi_if.master_if[0].bresp    = axi_if.slave_if[0].bresp;
  assign axi_if.slave_if[0].bready    = axi_if.master_if[0].bready;
  assign axi_if.slave_if[0].arvalid   = axi_if.master_if[0].arvalid;
  assign axi_if.slave_if[0].araddr    = axi_if.master_if[0].araddr;
  assign axi_if.slave_if[0].arid      = axi_if.master_if[0].arid;
  assign axi_if.slave_if[0].arlen     = axi_if.master_if[0].arlen;
  assign axi_if.slave_if[0].arsize    = axi_if.master_if[0].arsize;
  assign axi_if.slave_if[0].arburst   = axi_if.master_if[0].arburst;
  assign axi_if.slave_if[0].arlock    = axi_if.master_if[0].arlock;
  assign axi_if.slave_if[0].arcache   = axi_if.master_if[0].arcache;
  assign axi_if.slave_if[0].arprot    = axi_if.master_if[0].arprot;
  assign axi_if.master_if[0].arready  = axi_if.slave_if[0].arready;
  assign axi_if.master_if[0].rvalid   = axi_if.slave_if[0].rvalid;
  assign axi_if.master_if[0].rlast    = axi_if.slave_if[0].rlast;
  assign axi_if.master_if[0].rid      = axi_if.slave_if[0].rid;
  assign axi_if.master_if[0].rdata    = axi_if.slave_if[0].rdata;
  assign axi_if.master_if[0].rresp    = axi_if.slave_if[0].rresp;
  assign axi_if.slave_if[0].rready    = axi_if.master_if[0].rready;

`else

  // ------------------------------------------------------------------
  // Connect AXI_MASTER VIP to AXI_SLAVE_VIP[1]
 
  assign axi_if.slave_if[1].awvalid   = axi_if.master_if[0].awvalid;
  assign axi_if.slave_if[1].awaddr    = axi_if.master_if[0].awaddr;
  assign axi_if.slave_if[1].awid      = axi_if.master_if[0].awid;
  assign axi_if.slave_if[1].awlen     = axi_if.master_if[0].awlen;
  assign axi_if.slave_if[1].awsize    = axi_if.master_if[0].awsize;
  assign axi_if.slave_if[1].awburst   = axi_if.master_if[0].awburst;
  assign axi_if.slave_if[1].awlock    = axi_if.master_if[0].awlock;
  assign axi_if.slave_if[1].awcache   = axi_if.master_if[0].awcache;
  assign axi_if.slave_if[1].awprot    = axi_if.master_if[0].awprot;
  assign axi_if.master_if[0].awready  = axi_if.slave_if[1].awready;
  assign axi_if.slave_if[1].wvalid    = axi_if.master_if[0].wvalid;
  assign axi_if.slave_if[1].wlast     = axi_if.master_if[0].wlast;
  assign axi_if.slave_if[1].wdata     = axi_if.master_if[0].wdata;
  assign axi_if.slave_if[1].wstrb     = axi_if.master_if[0].wstrb;
  assign axi_if.master_if[0].wready   = axi_if.slave_if[1].wready;
  assign axi_if.master_if[0].bvalid   = axi_if.slave_if[1].bvalid;
  assign axi_if.master_if[0].bid      = axi_if.slave_if[1].bid;
  assign axi_if.master_if[0].bresp    = axi_if.slave_if[1].bresp;
  assign axi_if.slave_if[1].bready    = axi_if.master_if[0].bready;
  assign axi_if.slave_if[1].arvalid   = axi_if.master_if[0].arvalid;
  assign axi_if.slave_if[1].araddr    = axi_if.master_if[0].araddr;
  assign axi_if.slave_if[1].arid      = axi_if.master_if[0].arid;
  assign axi_if.slave_if[1].arlen     = axi_if.master_if[0].arlen;
  assign axi_if.slave_if[1].arsize    = axi_if.master_if[0].arsize;
  assign axi_if.slave_if[1].arburst   = axi_if.master_if[0].arburst;
  assign axi_if.slave_if[1].arlock    = axi_if.master_if[0].arlock;
  assign axi_if.slave_if[1].arcache   = axi_if.master_if[0].arcache;
  assign axi_if.slave_if[1].arprot    = axi_if.master_if[0].arprot;
  assign axi_if.master_if[0].arready  = axi_if.slave_if[1].arready;
  assign axi_if.master_if[0].rvalid   = axi_if.slave_if[1].rvalid;
  assign axi_if.master_if[0].rlast    = axi_if.slave_if[1].rlast;
  assign axi_if.master_if[0].rid      = axi_if.slave_if[1].rid;
  assign axi_if.master_if[0].rdata    = axi_if.slave_if[1].rdata;
  assign axi_if.master_if[0].rresp    = axi_if.slave_if[1].rresp;
  assign axi_if.slave_if[1].rready    = axi_if.master_if[0].rready;

`endif
`endif
  


// =============================================================================================================
// CLOCK and RESET Generators
// =============================================================================================================

  axe_clk_generator u_dma_clk_generator(
    .i_enable(clk_en),
    .o_clk(sys_clk)
    );
 
  axe_clk_assert u_axe_clk_assert(.clk(sys_clk),
    .rst_n(sys_rst_n),
    .freq_mhz(dma_clk_freq_mhz),
    .tol_ps(dma_clk_tol_ps)
    );
  
  axe_rst_generator u_dma_rst_generator(
    .i_clk(clk),
    .o_rst(reset)
    );

  assign sys_rst_n = ~reset;
  

  // =============================================================================================================
  // Assign the reset pin from the reset interface to the reset pins from the VIP interface.
  // =============================================================================================================

  
  // =============================================================================================================
  // DUT and TB INTERFACE Declarations and Assignments
  // =============================================================================================================

  // =============================================================================================================
  // Instantiate test harness/DUT
  // =============================================================================================================
  // TBD to be wired
  
  dma dut (
    // Clock and reset signals
    .i_clk                                  (sys_clk),
    .i_rst_n                                (sys_rst_n),

    // SRAM Sidebands
    .i_impl                                 ('0),
    .o_impl                                 (),

    // Control
    .o_int                                  (dut_channel_irqs),

    .o_tok_prod_vld                         (dut_tok_prod_vld),
    .i_tok_prod_rdy                         (dut_tok_prod_rdy),
    .i_tok_cons_vld                         (dut_tok_cons_vld),
    .o_tok_cons_rdy                         (dut_tok_cons_rdy),

    .o_ts_start                             (dut_ts_start),
    .o_ts_end                               (dut_ts_end),
    .o_acd_sync                             (dut_acd_sync),
    .o_obs                                  (dut_o_obs),

    // AXI 4 Configuration Interface
    // AXI write address channel
    .i_axi_s_awvalid                        (dut_axi_s_awvalid),
    .i_axi_s_awaddr                         (dut_axi_s_awaddr),
    .i_axi_s_awid                           (dut_axi_s_awid),
    .i_axi_s_awlen                          (dut_axi_s_awlen),
    .i_axi_s_awsize                         (dut_axi_s_awsize),
    .i_axi_s_awburst                        (dut_axi_s_awburst),
    .i_axi_s_awlock                         (dut_axi_s_awlock),
    .i_axi_s_awcache                        (dut_axi_s_awcache),
    .i_axi_s_awprot                         (dut_axi_s_awprot),
    .o_axi_s_awready                        (dut_axi_s_awready),
    // AXI write data channel 
    .i_axi_s_wvalid                         (dut_axi_s_wvalid),
    .i_axi_s_wlast                          (dut_axi_s_wlast),
    .i_axi_s_wdata                          (dut_axi_s_wdata),
    .i_axi_s_wstrb                          (dut_axi_s_wstrb),
    .o_axi_s_wready                         (dut_axi_s_wready),
    // AXI write response channel 
    .o_axi_s_bvalid                         (dut_axi_s_bvalid),
    .o_axi_s_bid                            (dut_axi_s_bid),
    .o_axi_s_bresp                          (dut_axi_s_bresp),
    .i_axi_s_bready                         (dut_axi_s_bready),
    // AXI read address channel 
    .i_axi_s_arvalid                        (dut_axi_s_arvalid),
    .i_axi_s_araddr                         (dut_axi_s_araddr),
    .i_axi_s_arid                           (dut_axi_s_arid),
    .i_axi_s_arlen                          (dut_axi_s_arlen),
    .i_axi_s_arsize                         (dut_axi_s_arsize),
    .i_axi_s_arburst                        (dut_axi_s_arburst),
    .i_axi_s_arlock                         (dut_axi_s_arlock),
    .i_axi_s_arcache                        (dut_axi_s_arcache),
    .i_axi_s_arprot                         (dut_axi_s_arprot),
    .o_axi_s_arready                        (dut_axi_s_arready),
    // AXI read data/response channel 
    .o_axi_s_rvalid                         (dut_axi_s_rvalid),
    .o_axi_s_rlast                          (dut_axi_s_rlast),
    .o_axi_s_rid                            (dut_axi_s_rid),
    .o_axi_s_rdata                          (dut_axi_s_rdata),
    .o_axi_s_rresp                          (dut_axi_s_rresp),
    .i_axi_s_rready                         (dut_axi_s_rready),

    // AXI 4 Data Ports (n-Number of them)
    // AXI write address channel
    .o_axi_m_awvalid                        (dut_axi_m_awvalid),           
    .o_axi_m_awaddr                         (dut_axi_m_awaddr),
    .o_axi_m_awid                           (dut_axi_m_awid),
    .o_axi_m_awlen                          (dut_axi_m_awlen),
    .o_axi_m_awsize                         (dut_axi_m_awsize),
    .o_axi_m_awburst                        (dut_axi_m_awburst),
    .o_axi_m_awlock                         (dut_axi_m_awlock),
    .o_axi_m_awcache                        (dut_axi_m_awcache),
    .o_axi_m_awprot                         (dut_axi_m_awprot),
    .i_axi_m_awready                        (dut_axi_m_awready),
    // AXI write data channel               
    .o_axi_m_wvalid                         (dut_axi_m_wvalid),
    .o_axi_m_wlast                          (dut_axi_m_wlast),
    .o_axi_m_wdata                          (dut_axi_m_wdata),
    .o_axi_m_wstrb                          (dut_axi_m_wstrb),
    .i_axi_m_wready                         (dut_axi_m_wready),
    // AXI write response channel           
    .i_axi_m_bvalid                         (dut_axi_m_bvalid),
    .i_axi_m_bid                            (dut_axi_m_bid),
    .i_axi_m_bresp                          (dut_axi_m_bresp),
    .o_axi_m_bready                         (dut_axi_m_bready),
    // AXI read address channel             
    .o_axi_m_arvalid                        (dut_axi_m_arvalid),
    .o_axi_m_araddr                         (dut_axi_m_araddr),
    .o_axi_m_arid                           (dut_axi_m_arid),
    .o_axi_m_arlen                          (dut_axi_m_arlen),
    .o_axi_m_arsize                         (dut_axi_m_arsize),
    .o_axi_m_arburst                        (dut_axi_m_arburst),
    .o_axi_m_arlock                         (dut_axi_m_arlock),
    .o_axi_m_arcache                        (dut_axi_m_arcache),
    .o_axi_m_arprot                         (dut_axi_m_arprot),
    .i_axi_m_arready                        (dut_axi_m_arready),
    // AXI read data/response channel       
    .i_axi_m_rvalid                         (dut_axi_m_rvalid),
    .i_axi_m_rlast                          (dut_axi_m_rlast),
    .i_axi_m_rid                            (dut_axi_m_rid),
    .i_axi_m_rdata                          (dut_axi_m_rdata),
    .i_axi_m_rresp                          (dut_axi_m_rresp),
    .o_axi_m_rready                         (dut_axi_m_rready)
    
    // TBD Wire up IRQ line to IRQ IF
    // o_irq (dut_irq)
    
  );

  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================
  // Generate the clock
  initial begin
    u_dma_rst_generator.async_rst(.duration_ns(10));
    u_dma_clk_generator.set_clock(.freq_mhz(dma_clk_freq_mhz), .duty(50));
    clk_en = 1'b1;     
  end

  // =============================================================================================================
  initial begin
    import uvm_pkg::uvm_config_db;
    `ifdef AXI_VIP

    // Set the reset interface on the virtual sequencer
    //    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(
    //        uvm_root::get(), "uvm_test_top.env.sequencer", "reset_mp", axi_reset_if.axi_reset_modport);

    // =============================================================================================================
    // Provide the AXI SV interface to the AXI System ENV. This step establishes the connection between the AXI
    // System ENV and the DUT through the AXI interface.
    // =============================================================================================================
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.env.axi_system_env", "vif", axi_if);
    `endif

    uvm_config_db#(virtual irq_if)::set(null,"*env.m_dma_irq_agent","dma_irq_vif", dma_irq_if);
    uvm_config_db#(virtual clk_if)::set(null,"*","dma_clk_vif", dma_clk_if);

  end 


  // =============================================================================================================
  // Initialize all statis DUT input signals and memories
  // =============================================================================================================
  initial begin   
    // Input ports initializations
    dma_inp_ports_init();
  end

  // Initializing all input masters
  task dma_inp_ports_init;
    // TBD
  endtask:dma_inp_ports_init

// ----------------------------------------------------------------------------------------------------------------
// TBD - Add
//     -  axe_clk_generator.sv
//     -  axe_rst_generator.sv
//     -  axe_timeout.sv
//     -  axe_clk_assert.sv
//
//     - check if AXI VIPs have the protocol checkers in place
// ----------------------------------------------------------------------------------------------------------------

// TestBench MAX SIM Timeout
   initial begin
     current_simtime = $realtime();
     while (current_simtime < C_MAX_SIMTIME) begin
       @(posedge sys_clk);
       current_simtime = $realtime();
     end
     
     `uvm_fatal("dv/rtl/hdl_top", $sformatf("Local Simulation TIMEOUT [C_MAX_SIMTIME]"))
   end


// ----------------------------------------------------------------------------------------------------------------
  
  // Run test
  initial begin
    run_test();
  end
endmodule : hdl_top
