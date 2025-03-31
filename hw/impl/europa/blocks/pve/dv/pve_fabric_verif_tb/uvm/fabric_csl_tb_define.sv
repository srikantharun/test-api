// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : ana.stoisavljevic@axelera.ai  *** //

//Defines///////////////////////////

  `define AXI_HP_ADDR_WIDTH            40
  // PVE_0
  `define PVE_0_BASE 40'h9000_0000
  `define PVE_0_EA   40'h9FFF_FFFF
  // PVE_1
  `define PVE_1_BASE 40'hA000_0000
  `define PVE_1_EA   40'hAFFF_FFFF

  // Set PVE_BASE/EA to either PVE_0 or PVE_1
  `define PVE_BASE 40'h9000_0000
  `define PVE_EA   40'h9FFF_FFFF
  // DMA0
  `define DMA0_SA 40'h0_0000
  `define DMA0_EA 40'h0_FFFF
  // DMA1
  `define DMA1_SA 40'h1_0000
  `define DMA1_EA 40'h1_FFFF
  // CLINT
  `define CLINT_SA 40'h2_0000
  `define CLINT_EA 40'h2_FFFF
  // PERF_COUNTERS
  `define PERF_COUNTERS_SA 40'h3_0000
  `define PERF_COUNTERS_EA 40'h3_FFFF
  // TRACE_IP
  `define TRACE_IP_SA 40'h4_0000
  `define TRACE_IP_EA 40'h4_FFFF
  // external to NoC 0
  `define EXT_0_SA 40'h005_0000
  `define EXT_0_EA 40'h3FF_FFFF
  // SPM
  `define SPM_SA 40'h400_0000
  `define SPM_EA 40'h400_3FFF
  // external to NoC 1
  `define EXT_1_SA 40'h404_0000
  `define EXT_1_EA 40'h7FF_FFFF
  // L1_0
  `define L1_0_SA 40'h800_0000
  `define L1_0_EA 40'h83F_FFFF
  // L1_1
  `define L1_1_SA 40'h840_0000
  `define L1_1_EA 40'h87F_FFFF
  // L1_2
  `define L1_2_SA 40'h880_0000
  `define L1_2_EA 40'h8BF_FFFF
  // L1_3
  `define L1_3_SA 40'h8C0_0000
  `define L1_3_EA 40'h8FF_FFFF
  // external to NoC 2
  `define EXT_2_SA 40'h900_0000
  `define EXT_2_EA 40'hFFF_FFFF

// =============================================================================================================
// macros that create the signals of AXI and assign them to the VIPs interface
// =============================================================================================================

`define create_axi_mst(mst_num, w_name, addr_w, data_w, id_w, len_w) \
  logic  [addr_w-1:0]   o_``w_name``_awaddr[mst_num]; \
  logic  [  1:0]        o_``w_name``_awburst[mst_num]; \
  logic  [  3:0]        o_``w_name``_awcache[mst_num]; \
  logic  [id_w-1:0]     o_``w_name``_awid[mst_num]; \
  logic  [len_w-1:0]    o_``w_name``_awlen[mst_num]; \
  logic                 o_``w_name``_awlock[mst_num]; \
  logic  [  2:0]        o_``w_name``_awprot[mst_num]; \
  logic  [  2:0]        o_``w_name``_awsize[mst_num]; \
  logic                 o_``w_name``_awvalid[mst_num]; \
  logic                 i_``w_name``_awready[mst_num]; \
  logic                 o_``w_name``_bready[mst_num]; \
  logic  [id_w-1:0]     i_``w_name``_bid[mst_num]; \
  logic  [  1:0]        i_``w_name``_bresp[mst_num]; \
  logic                 i_``w_name``_bvalid[mst_num]; \
  logic  [data_w-1:0]   o_``w_name``_wdata[mst_num]; \
  logic                 o_``w_name``_wlast[mst_num]; \
  logic  [data_w/8-1:0] o_``w_name``_wstrb[mst_num]; \
  logic                 o_``w_name``_wvalid[mst_num]; \
  logic                 i_``w_name``_wready[mst_num]; \
  logic  [ addr_w-1:0]  o_``w_name``_araddr[mst_num]; \
  logic  [  1:0]        o_``w_name``_arburst[mst_num]; \
  logic  [  3:0]        o_``w_name``_arcache[mst_num]; \
  logic  [id_w-1:0]     o_``w_name``_arid[mst_num]; \
  logic  [len_w-1:0]    o_``w_name``_arlen[mst_num]; \
  logic                 o_``w_name``_arlock[mst_num]; \
  logic  [  2:0]        o_``w_name``_arprot[mst_num]; \
  logic  [  2:0]        o_``w_name``_arsize[mst_num]; \
  logic                 o_``w_name``_arvalid[mst_num]; \
  logic                 i_``w_name``_arready[mst_num]; \
  logic  [data_w-1:0]   i_``w_name``_rdata[mst_num]; \
  logic  [id_w-1:0]     i_``w_name``_rid[mst_num]; \
  logic                 i_``w_name``_rlast[mst_num]; \
  logic  [  1:0]        i_``w_name``_rresp[mst_num]; \
  logic                 i_``w_name``_rvalid[mst_num]; \
  logic                 o_``w_name``_rready[mst_num]; \
  logic  [  5:0]        o_``w_name``_awatop[mst_num];

`define interface_connect_axi_read_mst(mst_num, w_name, intf) \
  assign intf.araddr  = o_``w_name``_araddr[mst_num]; \
  assign intf.arburst = o_``w_name``_arburst[mst_num]; \
  assign intf.arcache = o_``w_name``_arcache[mst_num]; \
  assign intf.arid    = o_``w_name``_arid[mst_num]; \
  assign intf.arlen   = o_``w_name``_arlen[mst_num]; \
  assign intf.arlock  = o_``w_name``_arlock[mst_num]; \
  assign intf.arprot  = o_``w_name``_arprot[mst_num]; \
  assign intf.arsize  = o_``w_name``_arsize[mst_num]; \
  assign intf.arvalid = o_``w_name``_arvalid[mst_num]; \
  assign i_``w_name``_arready[mst_num] = intf.arready; \
  assign i_``w_name``_rdata[mst_num] = intf.rdata; \
  assign i_``w_name``_rid[mst_num] = intf.rid; \
  assign i_``w_name``_rlast[mst_num] = intf.rlast; \
  assign i_``w_name``_rresp[mst_num] = intf.rresp; \
  assign i_``w_name``_rvalid[mst_num] = intf.rvalid; \
  assign intf.rready = o_``w_name``_rready[mst_num];

`define interface_connect_axi_write_mst(mst_num, w_name, intf) \
  assign  intf.awaddr  = o_``w_name``_awaddr[mst_num]; \
  assign  intf.awburst = o_``w_name``_awburst[mst_num]; \
  assign  intf.awcache = o_``w_name``_awcache[mst_num]; \
  assign  intf.awid    = o_``w_name``_awid[mst_num]; \
  assign  intf.awlen   = o_``w_name``_awlen[mst_num]; \
  assign  intf.awlock  = o_``w_name``_awlock[mst_num]; \
  assign  intf.awprot  = o_``w_name``_awprot[mst_num]; \
  assign  intf.awsize  = o_``w_name``_awsize[mst_num]; \
  assign  intf.awvalid = o_``w_name``_awvalid[mst_num]; \
  assign  i_``w_name``_awready[mst_num] = intf.awready; \
  assign  intf.bready = o_``w_name``_bready[mst_num]; \
  assign  i_``w_name``_bid[mst_num] = intf.bid; \
  assign  i_``w_name``_bresp[mst_num] = intf.bresp; \
  assign  i_``w_name``_bvalid[mst_num] = intf.bvalid; \
  assign  intf.wdata  = o_``w_name``_wdata[mst_num]; \
  assign  intf.wlast  = o_``w_name``_wlast[mst_num]; \
  assign  intf.wstrb  = o_``w_name``_wstrb[mst_num]; \
  assign  intf.wvalid = o_``w_name``_wvalid[mst_num]; \
  assign  i_``w_name``_wready[mst_num] = intf.wready;

`define create_axi_slv(slv_num, w_name, addr_w, data_w, id_w, len_w) \
  logic  [addr_w-1:0]   i_``w_name``_awaddr[slv_num]; \
  logic  [  1:0]        i_``w_name``_awburst[slv_num]; \
  logic  [  3:0]        i_``w_name``_awcache[slv_num]; \
  logic  [id_w-1:0]     i_``w_name``_awid[slv_num]; \
  logic  [len_w-1:0]    i_``w_name``_awlen[slv_num]; \
  logic                 i_``w_name``_awlock[slv_num]; \
  logic  [  2:0]        i_``w_name``_awprot[slv_num]; \
  logic  [  2:0]        i_``w_name``_awsize[slv_num]; \
  logic                 i_``w_name``_awvalid[slv_num]; \
  logic                 o_``w_name``_awready[slv_num]; \
  logic                 i_``w_name``_bready[slv_num]; \
  logic  [id_w-1:0]     o_``w_name``_bid[slv_num]; \
  logic  [  1:0]        o_``w_name``_bresp[slv_num]; \
  logic                 o_``w_name``_bvalid[slv_num]; \
  logic  [data_w-1:0]   i_``w_name``_wdata[slv_num]; \
  logic                 i_``w_name``_wlast[slv_num]; \
  logic  [data_w/8-1:0] i_``w_name``_wstrb[slv_num]; \
  logic                 i_``w_name``_wvalid[slv_num]; \
  logic                 o_``w_name``_wready[slv_num]; \
  logic  [ addr_w-1:0]  i_``w_name``_araddr[slv_num]; \
  logic  [  1:0]        i_``w_name``_arburst[slv_num]; \
  logic  [  3:0]        i_``w_name``_arcache[slv_num]; \
  logic  [id_w-1:0]     i_``w_name``_arid[slv_num]; \
  logic  [len_w-1:0]    i_``w_name``_arlen[slv_num]; \
  logic                 i_``w_name``_arlock[slv_num]; \
  logic  [  2:0]        i_``w_name``_arprot[slv_num]; \
  logic  [  2:0]        i_``w_name``_arsize[slv_num]; \
  logic                 i_``w_name``_arvalid[slv_num]; \
  logic                 o_``w_name``_arready[slv_num]; \
  logic  [data_w-1:0]   o_``w_name``_rdata[slv_num]; \
  logic  [id_w-1:0]     o_``w_name``_rid[slv_num]; \
  logic                 o_``w_name``_rlast[slv_num]; \
  logic  [  1:0]        o_``w_name``_rresp[slv_num]; \
  logic                 o_``w_name``_rvalid[slv_num]; \
  logic                 i_``w_name``_rready[slv_num]; \
  logic  [  5:0]        i_``w_name``_awatop[slv_num];

`define interface_connect_axi_write_slv(slv_num, w_name, intf) \
  assign i_``w_name``_awaddr[slv_num] = intf.awaddr; \
  assign i_``w_name``_awburst[slv_num] = intf.awburst; \
  assign i_``w_name``_awcache[slv_num] = intf.awcache; \
  assign i_``w_name``_awid[slv_num] = intf.awid; \
  assign i_``w_name``_awlen[slv_num] = intf.awlen; \
  assign i_``w_name``_awlock[slv_num] = intf.awlock; \
  assign i_``w_name``_awprot[slv_num] = intf.awprot; \
  assign i_``w_name``_awsize[slv_num] = intf.awsize; \
  assign i_``w_name``_awvalid[slv_num] = intf.awvalid; \
  assign intf.awready   = o_``w_name``_awready[slv_num]; \
  assign i_``w_name``_bready[slv_num] = intf.bready; \
  assign intf.bid       = o_``w_name``_bid[slv_num]; \
  assign intf.bresp     = o_``w_name``_bresp[slv_num]; \
  assign intf.bvalid    = o_``w_name``_bvalid[slv_num]; \
  assign i_``w_name``_wdata[slv_num] = intf.wdata; \
  assign i_``w_name``_wlast[slv_num] = intf.wlast; \
  assign i_``w_name``_wstrb[slv_num] = intf.wstrb; \
  assign i_``w_name``_wvalid[slv_num] = intf.wvalid; \
  assign intf.wready    = o_``w_name``_wready[slv_num];

`define interface_connect_axi_read_slv(slv_num, w_name, intf) \
  assign i_``w_name``_araddr[slv_num]  = intf.araddr; \
  assign i_``w_name``_arburst[slv_num] = intf.arburst; \
  assign i_``w_name``_arcache[slv_num] = intf.arcache; \
  assign i_``w_name``_arid[slv_num] = intf.arid; \
  assign i_``w_name``_arlen[slv_num] = intf.arlen; \
  assign i_``w_name``_arlock[slv_num] = intf.arlock; \
  assign i_``w_name``_arprot[slv_num] = intf.arprot; \
  assign i_``w_name``_arsize[slv_num] = intf.arsize; \
  assign i_``w_name``_arvalid[slv_num] = intf.arvalid; \
  assign intf.arready   = o_``w_name``_arready[slv_num]; \
  assign intf.rdata     = o_``w_name``_rdata[slv_num]; \
  assign intf.rid       = o_``w_name``_rid[slv_num]; \
  assign intf.rlast     = o_``w_name``_rlast[slv_num]; \
  assign intf.rresp     = o_``w_name``_rresp[slv_num]; \
  assign intf.rvalid    = o_``w_name``_rvalid[slv_num]; \
  assign i_``w_name``_rready[slv_num]  = intf.rready;

`define interface_connect_axi_mst(mst_num, w_name, intf) \
`interface_connect_axi_write_mst(mst_num, w_name, intf) \
`interface_connect_axi_read_mst(mst_num, w_name, intf)

`define interface_connect_axi_slv(slv_num, w_name, intf) \
`interface_connect_axi_write_slv(slv_num, w_name, intf) \
`interface_connect_axi_read_slv(slv_num, w_name, intf)

  typedef int unsigned uint32_t;

  //TODO: define custom parameters for each Initiator&Target
  `define AXI_LP_ADDR_WIDTH              40
  `define AXI_LP_DATA_WIDTH              64
  `define AXI_HP_DATA_WIDTH              512
  `define AXI_TRANSACTION_BURST_SIZE_8   0
  `define AXI_TRANSACTION_BURST_SIZE_16  1
  `define AXI_TRANSACTION_BURST_SIZE_32  2
  `define AXI_TRANSACTION_BURST_SIZE_64  3
  `define AXI_TRANSACTION_BURST_SIZE_128 4
  `define AXI_TRANSACTION_BURST_SIZE_256 5
  `define AXI_TRANSACTION_BURST_SIZE_512 6
  `define AXI_TRANSACTION_BURST_FIXED    0
  `define AXI_TRANSACTION_BURST_INCR     1
  `define AXI_TRANSACTION_BURST_WRAP     2
  `define AXI_OKAY_RESPONSE              0
  `define AXI_EXOKAY_RESPONSE            1
  `define AXI_SLVERR_RESPONSE            2
  `define AXI_DECERR_RESPONSE            3
  `define AXI_MAX_DELAY                 16

  //TODO: define custom parameters for each Initiator&Target
  `define P_APB_ADDR_WIDTH                  64
  `define P_APB_DATA_WIDTH                  32
  `define P_APB_BE_WIDTH                    (`SVT_APB_MAX_DATA_WIDTH / 8)
  `define P_MST_TO_SLV_CNTRL_WIDTH          `P_APB_DATA_WIDTH + `P_APB_ADDR_WIDTH + `P_APB_BE_WIDTH + 1
  `define P_SLV_TO_MST_CNTRL_WIDTH          `P_APB_DATA_WIDTH + 1

  `define P_APB_TRANSACTION_MAX    2048
  `define P_APB_READY_TIMEOUT_MAX  8
  `define P_MST_RST_ACKN_BIT       uint32_t'(0)
   
  `define HP_STRB_WIDTH   64 
  `define MP_STRB_WIDTH   16 
  `define LP_STRB_WIDTH   8 
  
  `define MIN_DELAY 500
  `define MED_DELAY 2500
  `define MAX_DELAY 5000
 
  // HP Crossbar S3
  `define DDR_0_SA 40'h2000000000
  `define DDR_0_EA 40'h27FFFFFFFF
  `define DDR_1_SA 40'h2800000000
  `define DDR_1_EA 40'h2FFFFFFFFF
  `define L2_MODULE_0_SA 40'h08000000
  `define L2_MODULE_0_EA 40'h08FFFFFF

//  `define LPDDR_PPP_0_TARG_MT_SA  36'h200000000
//  `define LPDDR_PPP_0_TARG_MT_EA  36'h3ffffffff
//  `define LPDDR_PPP_1_TARG_MT_SA  36'h400000000
//  `define LPDDR_PPP_1_TARG_MT_EA  36'h5ffffffff
//  `define SYS_SPM_TARG_LT_SA      36'h0 
//  `define SYS_SPM_TARG_LT_EA      36'h3ffffff
//  `define L2_0_TARG_HT_SA         36'h8000000
//  `define L2_0_TARG_HT_EA         36'h8ffffff
//  `define L2_1_TARG_HT_SA         36'h9000000
//  `define L2_1_TARG_HT_EA         36'h9ffffff

  // ****************************************************************************
  // Enumerated Types
  // ****************************************************************************

  typedef enum bit [3:0] {
    BURST_SIZE_8BIT    = `AXI_TRANSACTION_BURST_SIZE_8,
    BURST_SIZE_16BIT   = `AXI_TRANSACTION_BURST_SIZE_16,
    BURST_SIZE_32BIT   = `AXI_TRANSACTION_BURST_SIZE_32,
    BURST_SIZE_64BIT   = `AXI_TRANSACTION_BURST_SIZE_64,
    BURST_SIZE_128BIT  = `AXI_TRANSACTION_BURST_SIZE_128,
    BURST_SIZE_256BIT  = `AXI_TRANSACTION_BURST_SIZE_256,
    BURST_SIZE_512BIT  = `AXI_TRANSACTION_BURST_SIZE_512
  } burst_size_t;

  typedef enum bit[1:0]{
    FIXED = `AXI_TRANSACTION_BURST_FIXED,
    INCR  = `AXI_TRANSACTION_BURST_INCR,
    WRAP  = `AXI_TRANSACTION_BURST_WRAP
  } burst_type_t;

  typedef enum bit[5:0]{
    BURST_LENGTH_1  = 1,
    BURST_LENGTH_2  = 2,
    BURST_LENGTH_4  = 4,
    BURST_LENGTH_8  = 8,
    BURST_LENGTH_16 = 16
  } burst_length_t;

  typedef enum bit [1:0] {
    OKAY    = `AXI_OKAY_RESPONSE,
    EXOKAY  = `AXI_EXOKAY_RESPONSE,
    SLVERR  = `AXI_SLVERR_RESPONSE,
    DECERR  = `AXI_DECERR_RESPONSE
  } resp_type_t;

  `define AXI_MAX_ADDR_USER_WIDTH       4
  `define AXI_MAX_DATA_USER_WIDTH       8
  `define AXI_MAX_BRESP_USER_WIDTH      4
  `define AXI_QOS_WIDTH                 4

  typedef enum bit[3:0]{
    targ_dma0   = 0,
    targ_dma1   = 1,
    targ_clint  = 2,
    targ_perfc  = 3,
    targ_trace  = 4,
    targ_spm    = 5,
    targ_lt_ext = 6,
    targ_l1_0   = 7,
    targ_l1_1   = 8,
    targ_l1_2   = 9,
    targ_l1_3   = 10,
    targ_ht_ext = 11
  } targ_t;

  typedef enum bit[3:0]{
    init_cl0cpu0 = 0,
    init_cl0cpu1 = 1,
    init_cl1cpu0 = 2,
    init_cl1cpu1 = 3,
    init_cl2cpu0 = 4,
    init_cl2cpu1 = 5,
    init_cl3cpu0 = 6,
    init_cl3cpu1 = 7,
    init_trace   = 8,
    init_lt_ext  = 9,
    init_dma0_0  = 10,
    init_dma0_1  = 11,
    init_dma1_0  = 12,
    init_dma1_1  = 13
  } init_t;
