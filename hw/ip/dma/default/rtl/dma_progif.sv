// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA
// Owner: Matt Morris <matt.morris@axelera.ai>

`ifndef DMAPROGIF_SV
`define DMAPROGIF_SV

module dma_progif
  import dma_reg_pkg::*;
  import dma_pkg::*;
  import axi_pkg::*;
  #(
    parameter int  NUM_PORTS       = 2,
    parameter int  NUM_CHNLS       = 4,
    parameter type dma_axi_s_data_t  = logic [64-1:0],
    parameter type dma_axi_s_strb_t  = logic [ 8-1:0],
    parameter type dma_axi_s_addr_t  = logic [ 36-1:0],
    parameter type dma_axi_s_id_t    = logic [  4-1:0],

    localparam int unsigned NumRegions = 1 + 3*NUM_CHNLS,
    parameter longint  RegionStAddr[NumRegions] = DmaDefaultRegionStAddr[0+:NumRegions],
    parameter longint RegionEndAddr[NumRegions] = DmaDefaultRegionEndAddr[0+:NumRegions]
  ) (
    // Clock and reset signals
    input  wire            i_clk,
    input  wire            i_rst_n,

    // AXI 4 Configuration Interface
    // AXI write address channel
    input  logic            i_axi_s_awvalid,
    input  dma_axi_s_addr_t i_axi_s_awaddr,
    input  dma_axi_s_id_t   i_axi_s_awid,
    input  axi_len_t        i_axi_s_awlen,
    input  axi_size_e       i_axi_s_awsize,
    input  axi_burst_e      i_axi_s_awburst,
    input  logic            i_axi_s_awlock,
    input  axi_cache_e      i_axi_s_awcache,
    input  axi_prot_t       i_axi_s_awprot,
    output logic            o_axi_s_awready,
    // AXI write data channel
    input  logic            i_axi_s_wvalid,
    input  logic            i_axi_s_wlast,
    input  dma_axi_s_data_t i_axi_s_wdata,
    input  dma_axi_s_strb_t i_axi_s_wstrb,
    output logic            o_axi_s_wready,
    // AXI write response channel
    output logic            o_axi_s_bvalid,
    output dma_axi_s_id_t   o_axi_s_bid,
    output axi_resp_e       o_axi_s_bresp,
    input  logic            i_axi_s_bready,
    // AXI read address channel
    input  logic            i_axi_s_arvalid,
    input  dma_axi_s_addr_t i_axi_s_araddr,
    input  dma_axi_s_id_t   i_axi_s_arid,
    input  axi_len_t        i_axi_s_arlen,
    input  axi_size_e       i_axi_s_arsize,
    input  axi_burst_e      i_axi_s_arburst,
    input  logic            i_axi_s_arlock,
    input  axi_cache_e      i_axi_s_arcache,
    input  axi_prot_t       i_axi_s_arprot,
    output logic            o_axi_s_arready,
    // AXI read data/response channel
    output logic            o_axi_s_rvalid,
    output logic            o_axi_s_rlast,
    output dma_axi_s_id_t   o_axi_s_rid,
    output dma_axi_s_data_t o_axi_s_rdata,
    output axi_resp_e       o_axi_s_rresp,
    input  logic            i_axi_s_rready,

    //output logic  [NUM_PORTS-1:0] o_ll_xfer_req,
    //input  logic  [NUM_PORTS-1:0] i_ll_xfer_gnt,
    //output dma_rd_xfer_t   o_ll_xfer,

    //input  logic  [NUM_PORTS-1:0] i_ll_resp_req,
    //output logic  [NUM_PORTS-1:0] o_ll_resp_gnt,
    //input  dma_rd_resp_t   i_ll_resp     [NUM_PORTS],


    output dma_global_cfg_t o_global_cfg [NUM_CHNLS],
    input  dma_global_sts_t i_global_sts [NUM_CHNLS],

    output axi_a_ch_h2d_t o_chnl_mmu_axi_aw     [NUM_CHNLS],
    input  logic          i_chnl_mmu_axi_awready[NUM_CHNLS],
    output axi_a_ch_h2d_t o_chnl_mmu_axi_ar     [NUM_CHNLS],
    input  logic          i_chnl_mmu_axi_arready[NUM_CHNLS],
    output axi_w_ch_h2d_t o_chnl_mmu_axi_w      [NUM_CHNLS],
    input  logic          i_chnl_mmu_axi_wready [NUM_CHNLS],
    input  axi_r_ch_d2h_t i_chnl_mmu_axi_r      [NUM_CHNLS],
    output logic          o_chnl_mmu_axi_rready [NUM_CHNLS],
    input  axi_b_ch_d2h_t i_chnl_mmu_axi_b      [NUM_CHNLS],
    output logic          o_chnl_mmu_axi_bready [NUM_CHNLS],
    output axi_a_ch_h2d_t o_chnl_csr_axi_aw     [NUM_CHNLS],
    input  logic          i_chnl_csr_axi_awready[NUM_CHNLS],
    output axi_a_ch_h2d_t o_chnl_csr_axi_ar     [NUM_CHNLS],
    input  logic          i_chnl_csr_axi_arready[NUM_CHNLS],
    output axi_w_ch_h2d_t o_chnl_csr_axi_w      [NUM_CHNLS],
    input  logic          i_chnl_csr_axi_wready [NUM_CHNLS],
    input  axi_r_ch_d2h_t i_chnl_csr_axi_r      [NUM_CHNLS],
    output logic          o_chnl_csr_axi_rready [NUM_CHNLS],
    input  axi_b_ch_d2h_t i_chnl_csr_axi_b      [NUM_CHNLS],
    output logic          o_chnl_csr_axi_bready [NUM_CHNLS],
    output axi_a_ch_h2d_t o_chnl_cmd_axi_aw     [NUM_CHNLS],
    input  logic          i_chnl_cmd_axi_awready[NUM_CHNLS],
    output axi_a_ch_h2d_t o_chnl_cmd_axi_ar     [NUM_CHNLS],
    input  logic          i_chnl_cmd_axi_arready[NUM_CHNLS],
    output axi_w_ch_h2d_t o_chnl_cmd_axi_w      [NUM_CHNLS],
    input  logic          i_chnl_cmd_axi_wready [NUM_CHNLS],
    input  axi_r_ch_d2h_t i_chnl_cmd_axi_r      [NUM_CHNLS],
    output logic          o_chnl_cmd_axi_rready [NUM_CHNLS],
    input  axi_b_ch_d2h_t i_chnl_cmd_axi_b      [NUM_CHNLS],
    output logic          o_chnl_cmd_axi_bready [NUM_CHNLS]

  );

  localparam int unsigned NR_MASTERS = 1 + (3 * NUM_CHNLS);
  localparam int unsigned BW = $bits(axi_len_t);
  localparam int unsigned IDW = $bits(dma_axi_s_id_t);
  localparam int unsigned AW = $bits(dma_axi_s_addr_t);
  localparam int unsigned DW = $bits(dma_axi_s_data_t);

  logic [NR_MASTERS-1:0][IDW-1:0] m_awid   ;
  logic [NR_MASTERS-1:0][ BW-1:0] m_awlen  ;
  logic [NR_MASTERS-1:0][ AW-1:0] m_awaddr ;
  logic [NR_MASTERS-1:0][    2:0] m_awsize ;
  logic [NR_MASTERS-1:0][    1:0] m_awburst;
  logic [NR_MASTERS-1:0]          m_awlock ;
  logic [NR_MASTERS-1:0][    2:0] m_awprot ;
  logic [NR_MASTERS-1:0][    3:0] m_awcache;
  logic [NR_MASTERS-1:0]          m_awvalid;
  logic [NR_MASTERS-1:0]          m_awready;

  // Read Address Channel
  logic [NR_MASTERS-1:0][IDW-1:0] m_arid   ;
  logic [NR_MASTERS-1:0][ BW-1:0] m_arlen  ;
  logic [NR_MASTERS-1:0][ AW-1:0] m_araddr ;
  logic [NR_MASTERS-1:0][    2:0] m_arsize ;
  logic [NR_MASTERS-1:0][    1:0] m_arburst;
  logic [NR_MASTERS-1:0]          m_arlock ;
  logic [NR_MASTERS-1:0][    2:0] m_arprot ;
  logic [NR_MASTERS-1:0][    3:0] m_arcache;
  logic [NR_MASTERS-1:0]          m_arvalid;
  logic [NR_MASTERS-1:0]          m_arready;

  // Read Resp Channel
  logic [NR_MASTERS-1:0][IDW-1:0] m_rid   ;
  logic [NR_MASTERS-1:0][ DW-1:0] m_rdata ;
  logic [NR_MASTERS-1:0][    1:0] m_rresp ;
  logic [NR_MASTERS-1:0]          m_rlast ;
  logic [NR_MASTERS-1:0]          m_rvalid;
  logic [NR_MASTERS-1:0]          m_rready;

  // Write  Data Channel
  logic [NR_MASTERS-1:0][  DW-1:0] m_wdata ;
  logic [NR_MASTERS-1:0][DW/8-1:0] m_wstrb ;
  logic [NR_MASTERS-1:0]           m_wlast ;
  logic [NR_MASTERS-1:0]           m_wvalid;
  logic [NR_MASTERS-1:0]           m_wready;

  // Write Resp Channel
  logic [NR_MASTERS-1:0][IDW-1:0] m_bid   ;
  logic [NR_MASTERS-1:0][    1:0] m_bresp ;
  logic [NR_MASTERS-1:0]          m_bvalid;
  logic [NR_MASTERS-1:0]          m_bready;

  logic [$bits(axi_resp_e)-1:0] axi_s_rresp;
  logic [$bits(axi_resp_e)-1:0] axi_s_bresp;

  always_comb o_axi_s_rresp = axi_resp_e'(axi_s_rresp);
  always_comb o_axi_s_bresp = axi_resp_e'(axi_s_bresp);

  logic [$clog2(NR_MASTERS+1)-1:0] bus_sel_rd;
  logic [$clog2(NR_MASTERS+1)-1:0] bus_sel_wr;

  typedef int dev_ep_idx_t[NR_MASTERS];
  function automatic dev_ep_idx_t get_dev_ep_idx();
    for (int i=0; i<NR_MASTERS; i++)
      get_dev_ep_idx[i] = i;
  endfunction
  localparam dev_ep_idx_t DevEpIdx = get_dev_ep_idx();

  aic_fabric_addr_decoder #(
    .AW(AW+1),
    .CORE_ID_LSB(AW), // make use of core detection for prot checking
    .NR_CORE_IDS(1),
    .CORE_IDS({1}), // prot[0] (privileged) set
    .DEFAULT_SLAVE('1), // '1 is the error endpoint
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(NR_MASTERS),
    .NR_REGIONS(NR_MASTERS),
    .REGION_IS_CORE(DmaDefaultRegionPrivileged[0+:NumRegions]),
    .SKIP_CORE_CHECK_IF_NOT_CORE(1'b1), // don't check prot bit in address for non 'core'/prot regions
    .REGION_ST_ADDR(RegionStAddr),
    .REGION_END_ADDR(RegionEndAddr),
    .REGION_SLAVE_ID(DevEpIdx)
  ) u_ext_decode_wr (
    .addr_in({i_axi_s_awprot[0],i_axi_s_awaddr}),
    .core_id(1'b1), // check for privileged bit set in case of protected region ('core')

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AW+1),
    .CORE_ID_LSB(AW), // make use of core detection for prot checking
    .NR_CORE_IDS(1),
    .CORE_IDS({1}), // prot[0] (privileged) set
    .DEFAULT_SLAVE('1), // '1 is the error endpoint
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(NR_MASTERS),
    .NR_REGIONS(NR_MASTERS),
    .REGION_IS_CORE(DmaDefaultRegionPrivileged[0+:NumRegions]),
    .SKIP_CORE_CHECK_IF_NOT_CORE(1'b1), // don't check prot bit in address for non 'core'/prot regions
    .REGION_ST_ADDR(RegionStAddr),
    .REGION_END_ADDR(RegionEndAddr),
    .REGION_SLAVE_ID(DevEpIdx)
  ) u_ext_decode_rd (
    .addr_in({i_axi_s_arprot[0],i_axi_s_araddr}),
    .core_id(1'b1), // check for privileged bit set in case of protected region ('core')

    .sl_select(bus_sel_rd)
  );

  simple_axi_demux #(
    .NR_MASTERS(NR_MASTERS),
    .IDW ( IDW ),
    .AW ( AW ),
    .DW ( DW ),
    .BW ( BW ),
    .SL_WREQ_SHIELD ( 0 ),
    .SL_RREQ_SHIELD ( 0 ),
    .SL_WDATA_SHIELD ( 0 ),
    .SL_WRESP_SHIELD ( 0 ),
    .SL_RRESP_SHIELD ( 0 ),
    .OSR     ( 2 ),
    .EXT_SEL ( 1 )
  ) u_axi_demux (
    .i_clk,
    .i_rst_n,

    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),

  ///// AXI slave:
  // Write Address Channel
    .s_awid               (i_axi_s_awid),
    .s_awaddr             (i_axi_s_awaddr),
    .s_awlen              (i_axi_s_awlen),
    .s_awsize             (i_axi_s_awsize),
    .s_awburst            (i_axi_s_awburst),
    .s_awlock             (i_axi_s_awlock),
    .s_awprot             (i_axi_s_awprot),
    .s_awcache            (i_axi_s_awcache),
    .s_awvalid            (i_axi_s_awvalid),
    .s_awready            (o_axi_s_awready),
  // Read Address Channel
    .s_arid               (i_axi_s_arid),
    .s_araddr             (i_axi_s_araddr),
    .s_arlen              (i_axi_s_arlen),
    .s_arsize             (i_axi_s_arsize),
    .s_arburst            (i_axi_s_arburst),
    .s_arlock             (i_axi_s_arlock),
    .s_arprot             (i_axi_s_arprot),
    .s_arcache            (i_axi_s_arcache),
    .s_arvalid            (i_axi_s_arvalid),
    .s_arready            (o_axi_s_arready),
  // Write  Data Channel
    .s_wdata              (i_axi_s_wdata),
    .s_wstrb              (i_axi_s_wstrb),
    .s_wlast              (i_axi_s_wlast),
    .s_wvalid             (i_axi_s_wvalid),
    .s_wready             (o_axi_s_wready),
  // Read Data Channel
    .s_rid                (o_axi_s_rid),
    .s_rdata              (o_axi_s_rdata),
    .s_rresp              (axi_s_rresp),
    .s_rlast              (o_axi_s_rlast),
    .s_rvalid             (o_axi_s_rvalid),
    .s_rready             (i_axi_s_rready),
  // Write Response Channel
    .s_bid                (o_axi_s_bid),
    .s_bresp              (axi_s_bresp),
    .s_bvalid             (o_axi_s_bvalid),
    .s_bready             (i_axi_s_bready),

  ///// AXI Master:
  // Write Address Channel
  .m_awid   ,
  .m_awlen  ,
  .m_awaddr ,
  .m_awsize ,
  .m_awburst,
  .m_awlock ,
  .m_awprot ,
  .m_awcache,
  .m_awvalid,
  .m_awready,

  // Read Address Channel
  .m_arid   ,
  .m_arlen  ,
  .m_araddr ,
  .m_arsize ,
  .m_arburst,
  .m_arlock ,
  .m_arprot ,
  .m_arcache,
  .m_arvalid,
  .m_arready,

  // Read Resp Channel
  .m_rid   ,
  .m_rdata ,
  .m_rresp ,
  .m_rlast ,
  .m_rvalid,
  .m_rready,

  // Write  Data Channel
  .m_wdata ,
  .m_wstrb ,
  .m_wlast ,
  .m_wvalid,
  .m_wready,

  // Write Resp Channel
  .m_bid   ,
  .m_bresp ,
  .m_bvalid,
  .m_bready
);

  axi_a_ch_h2d_t global_csr_axi_aw ;
  logic          global_csr_axi_awready;
  axi_a_ch_h2d_t global_csr_axi_ar;
  logic          global_csr_axi_arready;
  axi_w_ch_h2d_t global_csr_axi_w;
  logic          global_csr_axi_wready;
  axi_r_ch_d2h_t global_csr_axi_r;
  logic          global_csr_axi_rready;
  axi_b_ch_d2h_t global_csr_axi_b;
  logic          global_csr_axi_bready;

  dma_reg2hw_t   reg2hw;
  dma_hw2reg_t   hw2reg;

  always_comb global_csr_axi_aw      = '{ id    : dma_reg_pkg::AXI_IDW'(m_awid[common_csr_idx]),
                                          addr  : dma_reg_pkg::AXI_AW'(m_awaddr[common_csr_idx]),
                                          len   : m_awlen[common_csr_idx],
                                          size  : m_awsize[common_csr_idx],
                                          burst : m_awburst[common_csr_idx],
                                          valid : m_awvalid[common_csr_idx] };
  always_comb m_awready[common_csr_idx]   = global_csr_axi_awready;

  always_comb global_csr_axi_ar      = '{ id    : dma_reg_pkg::AXI_IDW'(m_arid[common_csr_idx]),
                                          addr  : dma_reg_pkg::AXI_AW'(m_araddr[common_csr_idx]),
                                          len   : m_arlen[common_csr_idx],
                                          size  : m_arsize[common_csr_idx],
                                          burst : m_arburst[common_csr_idx],
                                          valid : m_arvalid[common_csr_idx]};
  always_comb m_arready[common_csr_idx]   = global_csr_axi_arready;

  always_comb global_csr_axi_w       = '{ data  : m_wdata[common_csr_idx],
                                          strb  : m_wstrb[common_csr_idx],
                                          last  : m_wlast[common_csr_idx],
                                          valid : m_wvalid[common_csr_idx]};
  always_comb m_wready[common_csr_idx]    = global_csr_axi_wready;

  always_comb m_bid[common_csr_idx]       = dma_axi_s_id_t'(global_csr_axi_b.id);
  always_comb m_bresp[common_csr_idx]     = axi_resp_e'(global_csr_axi_b.resp);
  always_comb m_bvalid[common_csr_idx]    = global_csr_axi_b.valid;
  always_comb global_csr_axi_bready  = m_bready[common_csr_idx];

  always_comb m_rid[common_csr_idx]       = dma_axi_s_id_t'(global_csr_axi_r.id);
  always_comb m_rdata[common_csr_idx]     = global_csr_axi_r.data;
  always_comb m_rresp[common_csr_idx]     = axi_resp_e'(global_csr_axi_r.resp);
  always_comb m_rlast[common_csr_idx]     = global_csr_axi_r.last;
  always_comb m_rvalid[common_csr_idx]    = global_csr_axi_r.valid;
  always_comb global_csr_axi_rready  = m_rready[common_csr_idx];

  for (genvar C=0; C< NUM_CHNLS; C++) begin: g_chnl_csr

    // DMA Command Block Channel Registers
    always_comb o_chnl_mmu_axi_aw[C]  = '{ id    : dma_reg_pkg::AXI_IDW'(m_awid[mmu_base_idx+C*3]),
                                           addr  : dma_reg_pkg::AXI_AW'(m_awaddr[mmu_base_idx+C*3] & DMA_MMU_ADDR_MASK),
                                           len   : m_awlen[mmu_base_idx+C*3],
                                           size  : m_awsize[mmu_base_idx+C*3],
                                           burst : m_awburst[mmu_base_idx+C*3],
                                           valid : m_awvalid[mmu_base_idx+C*3] };
    always_comb m_awready[mmu_base_idx+C*3]          = i_chnl_mmu_axi_awready[C];

    always_comb o_chnl_mmu_axi_ar[C]  = '{ id    : dma_reg_pkg::AXI_IDW'(m_arid[mmu_base_idx+C*3]),
                                           addr  : dma_reg_pkg::AXI_AW'(m_araddr[mmu_base_idx+C*3] & DMA_MMU_ADDR_MASK),
                                           len   : m_arlen[mmu_base_idx+C*3],
                                           size  : m_arsize[mmu_base_idx+C*3],
                                           burst : m_arburst[mmu_base_idx+C*3],
                                           valid : m_arvalid[mmu_base_idx+C*3]};
    always_comb m_arready[mmu_base_idx+C*3]          = i_chnl_mmu_axi_arready[C];

    always_comb o_chnl_mmu_axi_w[C]   = '{ data  : m_wdata[mmu_base_idx+C*3],
                                           strb  : m_wstrb[mmu_base_idx+C*3],
                                           last  : m_wlast[mmu_base_idx+C*3],
                                           valid : m_wvalid[mmu_base_idx+C*3]};
    always_comb m_wready[mmu_base_idx+C*3]           = i_chnl_mmu_axi_wready[C];

    always_comb m_bid[mmu_base_idx+C*3]               = dma_axi_s_id_t'(i_chnl_mmu_axi_b[C].id);
    always_comb m_bresp[mmu_base_idx+C*3]             = axi_resp_e'(i_chnl_mmu_axi_b[C].resp);
    always_comb m_bvalid[mmu_base_idx+C*3]            = i_chnl_mmu_axi_b[C].valid;
    always_comb o_chnl_mmu_axi_bready[C] = m_bready[mmu_base_idx+C*3];

    always_comb m_rid[mmu_base_idx+C*3]               = dma_axi_s_id_t'(i_chnl_mmu_axi_r[C].id);
    always_comb m_rdata[mmu_base_idx+C*3]             = i_chnl_mmu_axi_r[C].data;
    always_comb m_rresp[mmu_base_idx+C*3]             = axi_resp_e'(i_chnl_mmu_axi_r[C].resp);
    always_comb m_rlast[mmu_base_idx+C*3]             = i_chnl_mmu_axi_r[C].last;
    always_comb m_rvalid[mmu_base_idx+C*3]            = i_chnl_mmu_axi_r[C].valid;
    always_comb o_chnl_mmu_axi_rready[C] = m_rready[mmu_base_idx+C*3];

    // DMA Command Block Channel Registers
    always_comb o_chnl_cmd_axi_aw[C]  = '{ id    : dma_reg_pkg::AXI_IDW'(m_awid[ch_cmdb_base_idx+C*3]),
                                           addr  : dma_reg_pkg::AXI_AW'(m_awaddr[ch_cmdb_base_idx+C*3] & DMA_CMD_ADDR_MASK),
                                           len   : m_awlen[ch_cmdb_base_idx+C*3],
                                           size  : m_awsize[ch_cmdb_base_idx+C*3],
                                           burst : m_awburst[ch_cmdb_base_idx+C*3],
                                           valid : m_awvalid[ch_cmdb_base_idx+C*3] };
    always_comb m_awready[ch_cmdb_base_idx+C*3]    = i_chnl_cmd_axi_awready[C];

    always_comb o_chnl_cmd_axi_ar[C]  = '{ id    : dma_reg_pkg::AXI_IDW'(m_arid[ch_cmdb_base_idx+C*3]),
                                           addr  : dma_reg_pkg::AXI_AW'(m_araddr[ch_cmdb_base_idx+C*3] & DMA_CMD_ADDR_MASK),
                                           len   : m_arlen[ch_cmdb_base_idx+C*3],
                                           size  : m_arsize[ch_cmdb_base_idx+C*3],
                                           burst : m_arburst[ch_cmdb_base_idx+C*3],
                                           valid : m_arvalid[ch_cmdb_base_idx+C*3]};
    always_comb m_arready[ch_cmdb_base_idx+C*3]    = i_chnl_cmd_axi_arready[C];

    always_comb o_chnl_cmd_axi_w[C]   = '{ data  : m_wdata[ch_cmdb_base_idx+C*3],
                                           strb  : m_wstrb[ch_cmdb_base_idx+C*3],
                                           last  : m_wlast[ch_cmdb_base_idx+C*3],
                                           valid : m_wvalid[ch_cmdb_base_idx+C*3]};
    always_comb m_wready[ch_cmdb_base_idx+C*3]     = i_chnl_cmd_axi_wready[C];

    always_comb m_bid[ch_cmdb_base_idx+C*3]         = dma_axi_s_id_t'(i_chnl_cmd_axi_b[C].id);
    always_comb m_bresp[ch_cmdb_base_idx+C*3]       = axi_resp_e'(i_chnl_cmd_axi_b[C].resp);
    always_comb m_bvalid[ch_cmdb_base_idx+C*3]      = i_chnl_cmd_axi_b[C].valid;
    always_comb o_chnl_cmd_axi_bready[C] = m_bready[ch_cmdb_base_idx+C*3];

    always_comb m_rid[ch_cmdb_base_idx+C*3]         = dma_axi_s_id_t'(i_chnl_cmd_axi_r[C].id);
    always_comb m_rdata[ch_cmdb_base_idx+C*3]       = i_chnl_cmd_axi_r[C].data;
    always_comb m_rresp[ch_cmdb_base_idx+C*3]       = axi_resp_e'(i_chnl_cmd_axi_r[C].resp);
    always_comb m_rlast[ch_cmdb_base_idx+C*3]       = i_chnl_cmd_axi_r[C].last;
    always_comb m_rvalid[ch_cmdb_base_idx+C*3]      = i_chnl_cmd_axi_r[C].valid;
    always_comb o_chnl_cmd_axi_rready[C] = m_rready[ch_cmdb_base_idx+C*3];

    // DMA Channel Registers
    always_comb o_chnl_csr_axi_aw[C]  = '{ id    : dma_reg_pkg::AXI_IDW'(m_awid[ch_csr_base_idx+C*3]),
                                           addr  : dma_reg_pkg::AXI_AW'(m_awaddr[ch_csr_base_idx+C*3] & DMA_CSR_ADDR_MASK),
                                           len   : m_awlen[ch_csr_base_idx+C*3],
                                           size  : m_awsize[ch_csr_base_idx+C*3],
                                           burst : m_awburst[ch_csr_base_idx+C*3],
                                           valid : m_awvalid[ch_csr_base_idx+C*3] };
    always_comb m_awready[ch_csr_base_idx+C*3]  = i_chnl_csr_axi_awready[C];

    always_comb o_chnl_csr_axi_ar[C]  = '{ id    : dma_reg_pkg::AXI_IDW'(m_arid[ch_csr_base_idx+C*3]),
                                           addr  : dma_reg_pkg::AXI_AW'(m_araddr[ch_csr_base_idx+C*3] & DMA_CSR_ADDR_MASK),
                                           len   : m_arlen[ch_csr_base_idx+C*3],
                                           size  : m_arsize[ch_csr_base_idx+C*3],
                                           burst : m_arburst[ch_csr_base_idx+C*3],
                                           valid : m_arvalid[ch_csr_base_idx+C*3]};
    always_comb m_arready[ch_csr_base_idx+C*3]  = i_chnl_csr_axi_arready[C];

    always_comb o_chnl_csr_axi_w[C]   = '{ data  : m_wdata[ch_csr_base_idx+C*3],
                                           strb  : m_wstrb[ch_csr_base_idx+C*3],
                                           last  : m_wlast[ch_csr_base_idx+C*3],
                                           valid : m_wvalid[ch_csr_base_idx+C*3]};
    always_comb m_wready[ch_csr_base_idx+C*3]   = i_chnl_csr_axi_wready[C];

    always_comb m_bid[ch_csr_base_idx+C*3]         = dma_axi_s_id_t'(i_chnl_csr_axi_b[C].id);
    always_comb m_bresp[ch_csr_base_idx+C*3]       = axi_resp_e'(i_chnl_csr_axi_b[C].resp);
    always_comb m_bvalid[ch_csr_base_idx+C*3]      = i_chnl_csr_axi_b[C].valid;
    always_comb o_chnl_csr_axi_bready[C] = m_bready[ch_csr_base_idx+C*3];

    always_comb m_rid[ch_csr_base_idx+C*3]         = dma_axi_s_id_t'(i_chnl_csr_axi_r[C].id);
    always_comb m_rdata[ch_csr_base_idx+C*3]       = i_chnl_csr_axi_r[C].data;
    always_comb m_rresp[ch_csr_base_idx+C*3]       = axi_resp_e'(i_chnl_csr_axi_r[C].resp);
    always_comb m_rlast[ch_csr_base_idx+C*3]       = i_chnl_csr_axi_r[C].last;
    always_comb m_rvalid[ch_csr_base_idx+C*3]      = i_chnl_csr_axi_r[C].valid;
    always_comb o_chnl_csr_axi_rready[C] = m_rready[ch_csr_base_idx+C*3];

  end: g_chnl_csr

  always_comb o_global_cfg[0].mode = reg2hw.ch_mode.ch0_mode;
  always_comb o_global_cfg[1].mode = reg2hw.ch_mode.ch1_mode;
  always_comb hw2reg.ch_status.ch0_busy.d = i_global_sts[0].busy;
  always_comb hw2reg.ch_status.ch1_busy.d = i_global_sts[1].busy;
  if (NUM_CHNLS == 4) begin : g_regif_4chnl
    always_comb o_global_cfg[2].mode = reg2hw.ch_mode.ch2_mode;
    always_comb o_global_cfg[3].mode = reg2hw.ch_mode.ch3_mode;
    always_comb hw2reg.ch_status.ch2_busy.d = i_global_sts[2].busy;
    always_comb hw2reg.ch_status.ch3_busy.d = i_global_sts[3].busy;
  end : g_regif_4chnl
  else if (NUM_CHNLS == 2) begin : g_regif_2chnl
    always_comb hw2reg.ch_status.ch2_busy.d = 1'b0;
    always_comb hw2reg.ch_status.ch3_busy.d = 1'b0;
  end : g_regif_2chnl



  dma_reg_top #(
    .StageNum ( 3 )
  ) u_csr (

    .clk_i        (i_clk),
    .rst_ni       (i_rst_n),
    .axi_aw_i     (global_csr_axi_aw),
    .axi_awready  (global_csr_axi_awready),
    .axi_ar_i     (global_csr_axi_ar),
    .axi_arready  (global_csr_axi_arready),
    .axi_w_i      (global_csr_axi_w),
    .axi_wready   (global_csr_axi_wready),
    .axi_b_o      (global_csr_axi_b),
    .axi_bready   (global_csr_axi_bready),
    .axi_r_o      (global_csr_axi_r),
    .axi_rready   (global_csr_axi_rready),
  // To HW
    .reg2hw       (reg2hw), // Write
    .hw2reg       (hw2reg), // Read
  // Config
    .devmode_i   (1'b1)
);

endmodule

`endif
