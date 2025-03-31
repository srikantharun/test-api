// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

//Defines///////////////////////////
  typedef int unsigned uint32_t;

  //TODO: define custom parameters for each Initiator&Target
  `define AXI_LP_ADDR_WIDTH              40
  `define AXI_LP_DATA_WIDTH              64
  `define AXI_HP_ADDR_WIDTH              40
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

  `define AXI_MAX_ADDR_USER_WIDTH       4 
  `define AXI_MAX_DATA_USER_WIDTH       8
  `define AXI_MAX_BRESP_USER_WIDTH      4
  `define AXI_QOS_WIDTH                 4

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


`ifdef AXE_AXI_RISCV_AMOS
  `define DUT axe_axi_riscv_amos
`elsif AXE_AXI_RISCV_LRSC
  `define DUT axe_axi_riscv_lrsc
`elsif AXE_AXI_ATOP_FILTER
  `define DUT axe_axi_atop_filter
`elsif AXE_AXI_ATU
  `define DUT axe_axi_atu
`elsif AXE_AXI_DEMUX
  `define DUT axe_axi_demux
`elsif AXE_AXI_DW_CONVERTER
  `define DUT axe_axi_dw_converter
`elsif AXE_AXI_ERR_SUB
  `define DUT axe_axi_err_sub
`elsif AXE_AXI_ID_REMAP
  `define DUT axe_axi_id_remap
`elsif AXE_AXI_ISOLATE
  `define DUT axe_axi_isolate
`elsif AXE_AXI_MODIFY_ADDRESS
  `define DUT axe_axi_modify_address
`elsif AXE_AXI_MUX
  `define DUT axe_axi_mux
`elsif AXE_AXI_RISCV_ATOMICS
  `define DUT axe_axi_riscv_atomics
`endif

`ifdef AXE_AXI_DEMUX
  `define MST_NUM 1
  `define SLV_NUM 10
`elsif AXE_AXI_MUX
  `define MST_NUM 10
  `define SLV_NUM 1
`else
  `define MST_NUM 1
  `define SLV_NUM 1
`endif

`ifdef AXE_AXI_ATU
  `define ADDR_M_W 64
  `define ADDR_S_W 40
  `define DATA_M_W 64
  `define DATA_S_W 64
  `define ID_M_W 4
  `define ID_S_W 4
`elsif AXE_AXI_DW_CONVERTER
  `define ADDR_M_W 40
  `define ADDR_S_W 40
  `define DATA_M_W 512
  `define DATA_S_W 64
  `define ID_M_W 4
  `define ID_S_W 4
`elsif AXE_AXI_ID_REMAP
  `define ADDR_M_W 40
  `define ADDR_S_W 40
  `define DATA_M_W 64
  `define DATA_S_W 64
  `define ID_S_W 4
  `define ID_M_W 5
`elsif AXE_AXI_MODIFY_ADDRESS
  `define ADDR_M_W 64
  `define ADDR_S_W 40
  `define DATA_M_W 64
  `define DATA_S_W 64
  `define ID_S_W 4
  `define ID_M_W 4
`elsif AXE_AXI_MUX
  `define ADDR_M_W 40
  `define ADDR_S_W 40
  `define DATA_M_W 64
  `define DATA_S_W 64
  `define ID_S_W 8
  `define ID_M_W 4
`elsif DUT
  `define ADDR_M_W 40
  `define ADDR_S_W 40
  `define DATA_M_W 64
  `define DATA_S_W 64
  `define ID_S_W 4
  `define ID_M_W 4
`else
  `define ADDR_M_W 40
  `define ADDR_S_W 40
  `define DATA_M_W 512
  `define DATA_S_W 512
  `define ID_S_W 9
  `define ID_M_W 9
`endif

`define AXI_DATA_WIDTH `DATA_M_W
`define AXI_ID_WIDTH `ID_M_W

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

  typedef enum bit[3:0]{PCIE, DEC, PVE, SDMA, AIC} init_t;
  typedef enum bit[1:0]{GRAPH_LPDDR, PP_LPDDR, L2} targ_t;

  `define BASE_TEST common_seq_lib_base_test
  `define CSL_TB 

`define create_and_assign_slv_connections(id_s_w, addr_s_w, user_w, data_s_w, strb_s_w) \
  axi_aw_``id_s_w``_``addr_s_w``_``user_w``_t o_axi_m_aw; \
  axi_w_``data_s_w``_``strb_s_w``_``user_w``_t  o_axi_m_w; \
  axi_b_``id_s_w``_``user_w``_t     i_axi_m_b; \
  axi_ar_``id_s_w``_``addr_s_w``_``user_w``_t o_axi_m_ar; \
  axi_r_``id_s_w``_``data_s_w``_``user_w``_t  i_axi_m_r; \
  logic o_axi_m_aw_valid, i_axi_m_aw_ready; \
  logic o_axi_m_w_valid, i_axi_m_w_ready; \
  logic i_axi_m_b_valid, o_axi_m_b_ready; \
  logic o_axi_m_ar_valid, i_axi_m_ar_ready; \
  logic i_axi_m_r_valid, o_axi_m_r_ready; \
  assign axi_if.slave_if[0].awid     = o_axi_m_aw.id; \
  assign axi_if.slave_if[0].awaddr   = o_axi_m_aw.addr; \
  assign axi_if.slave_if[0].awlen    = o_axi_m_aw.len; \
  assign axi_if.slave_if[0].awsize   = o_axi_m_aw.size; \
  assign axi_if.slave_if[0].awburst  = o_axi_m_aw.burst; \
  assign axi_if.slave_if[0].awlock   = o_axi_m_aw.lock; \
  assign axi_if.slave_if[0].awcache  = o_axi_m_aw.cache; \
  assign axi_if.slave_if[0].awprot   = o_axi_m_aw.prot; \
  assign axi_if.slave_if[0].awqos    = o_axi_m_aw.qos; \
  assign axi_if.slave_if[0].awregion = o_axi_m_aw.region; \
  assign axi_if.slave_if[0].awatop   = o_axi_m_aw.atop; \
  assign axi_if.slave_if[0].awuser   = o_axi_m_aw.user; \
  assign axi_if.slave_if[0].awvalid = o_axi_m_aw_valid; \
  assign i_axi_m_aw_ready = axi_if.slave_if[0].awready; \
  assign axi_if.slave_if[0].wdata = o_axi_m_w.data; \
  assign axi_if.slave_if[0].wstrb = o_axi_m_w.strb; \
  assign axi_if.slave_if[0].wlast = o_axi_m_w.last; \
  assign axi_if.slave_if[0].wuser = o_axi_m_w.user; \
  assign axi_if.slave_if[0].wvalid = o_axi_m_w_valid; \
  assign i_axi_m_w_ready = axi_if.slave_if[0].wready; \
  assign i_axi_m_b.id   = axi_if.slave_if[0].bid; \
  assign i_axi_m_b.resp = axi_if.slave_if[0].bresp; \
  assign i_axi_m_b.user = axi_if.slave_if[0].buser; \
  assign i_axi_m_b_valid = axi_if.slave_if[0].bvalid; \
  assign axi_if.slave_if[0].bready = o_axi_m_b_ready; \
  assign axi_if.slave_if[0].arid     = o_axi_m_ar.id; \
  assign axi_if.slave_if[0].araddr   = o_axi_m_ar.addr; \
  assign axi_if.slave_if[0].arlen    = o_axi_m_ar.len; \
  assign axi_if.slave_if[0].arsize   = o_axi_m_ar.size; \
  assign axi_if.slave_if[0].arburst  = o_axi_m_ar.burst; \
  assign axi_if.slave_if[0].arlock   = o_axi_m_ar.lock; \
  assign axi_if.slave_if[0].arcache  = o_axi_m_ar.cache; \
  assign axi_if.slave_if[0].arprot   = o_axi_m_ar.prot; \
  assign axi_if.slave_if[0].arqos    = o_axi_m_ar.qos; \
  assign axi_if.slave_if[0].arregion = o_axi_m_ar.region; \
  assign axi_if.slave_if[0].aruser   = o_axi_m_ar.user; \
  assign axi_if.slave_if[0].arvalid = o_axi_m_ar_valid; \
  assign i_axi_m_ar_ready = axi_if.slave_if[0].arready; \
  assign i_axi_m_r.id   = axi_if.slave_if[0].rid; \
  assign i_axi_m_r.data = axi_if.slave_if[0].rdata; \
  assign i_axi_m_r.resp = axi_if.slave_if[0].rresp; \
  assign i_axi_m_r.last = axi_if.slave_if[0].rlast; \
  assign i_axi_m_r.user = axi_if.slave_if[0].ruser; \
  assign i_axi_m_r_valid = axi_if.slave_if[0].rvalid; \
  assign axi_if.slave_if[0].rready = o_axi_m_r_ready; 

`define create_and_assign_mst_connections(id_m_w, addr_m_w, user_w, data_m_w, strb_m_w) \
  axi_aw_``id_m_w``_``addr_m_w``_``user_w``_t i_axi_s_aw; \
  axi_w_``data_m_w``_``strb_m_w``_``user_w``_t  i_axi_s_w; \
  axi_b_``id_m_w``_``user_w``_t     o_axi_s_b; \
  axi_ar_``id_m_w``_``addr_m_w``_``user_w``_t i_axi_s_ar; \
  axi_r_``id_m_w``_``data_m_w``_``user_w``_t  o_axi_s_r; \
  logic i_axi_s_aw_valid, o_axi_s_aw_ready; \
  logic i_axi_s_w_valid,  o_axi_s_w_ready; \
  logic o_axi_s_b_valid,  i_axi_s_b_ready; \
  logic i_axi_s_ar_valid, o_axi_s_ar_ready; \
  logic o_axi_s_r_valid,  i_axi_s_r_ready; \
  assign i_axi_s_aw.id     = axi_if.master_if[0].awid; \
  assign i_axi_s_aw.addr   = axi_if.master_if[0].awaddr; \
  assign i_axi_s_aw.len    = axi_if.master_if[0].awlen; \
  assign i_axi_s_aw.size   = axi_if.master_if[0].awsize; \
  assign i_axi_s_aw.burst  = axi_if.master_if[0].awburst; \
  assign i_axi_s_aw.lock   = axi_if.master_if[0].awlock; \
  assign i_axi_s_aw.cache  = axi_if.master_if[0].awcache; \
  assign i_axi_s_aw.prot   = axi_if.master_if[0].awprot; \
  assign i_axi_s_aw.qos    = axi_if.master_if[0].awqos; \
  assign i_axi_s_aw.region = axi_if.master_if[0].awregion; \
  assign i_axi_s_aw.atop   = axi_if.master_if[0].awatop; \
  assign i_axi_s_aw.user   = axi_if.master_if[0].awuser; \
  assign i_axi_s_aw_valid = axi_if.master_if[0].awvalid; \
  assign axi_if.master_if[0].awready = o_axi_s_aw_ready; \
  assign i_axi_s_w.data = axi_if.master_if[0].wdata; \
  assign i_axi_s_w.strb = axi_if.master_if[0].wstrb; \
  assign i_axi_s_w.last = axi_if.master_if[0].wlast; \
  assign i_axi_s_w.user = axi_if.master_if[0].wuser; \
  assign i_axi_s_w_valid = axi_if.master_if[0].wvalid; \
  assign axi_if.master_if[0].wready = o_axi_s_w_ready; \
  assign axi_if.master_if[0].bid   = o_axi_s_b.id; \
  assign axi_if.master_if[0].bresp = o_axi_s_b.resp; \
  assign axi_if.master_if[0].buser = o_axi_s_b.user; \
  assign axi_if.master_if[0].bvalid = o_axi_s_b_valid; \
  assign i_axi_s_b_ready = axi_if.master_if[0].bready; \
  assign i_axi_s_ar.id     = axi_if.master_if[0].arid; \
  assign i_axi_s_ar.addr   = axi_if.master_if[0].araddr; \
  assign i_axi_s_ar.len    = axi_if.master_if[0].arlen; \
  assign i_axi_s_ar.size   = axi_if.master_if[0].arsize; \
  assign i_axi_s_ar.burst  = axi_if.master_if[0].arburst; \
  assign i_axi_s_ar.lock   = axi_if.master_if[0].arlock; \
  assign i_axi_s_ar.cache  = axi_if.master_if[0].arcache; \
  assign i_axi_s_ar.prot   = axi_if.master_if[0].arprot; \
  assign i_axi_s_ar.qos    = axi_if.master_if[0].arqos; \
  assign i_axi_s_ar.region = axi_if.master_if[0].arregion; \
  assign i_axi_s_ar.user   = axi_if.master_if[0].aruser; \
  assign i_axi_s_ar_valid = axi_if.master_if[0].arvalid; \
  assign axi_if.master_if[0].arready = o_axi_s_ar_ready; \
  assign axi_if.master_if[0].rid   = o_axi_s_r.id; \
  assign axi_if.master_if[0].rdata = o_axi_s_r.data; \
  assign axi_if.master_if[0].rresp = o_axi_s_r.resp; \
  assign axi_if.master_if[0].rlast = o_axi_s_r.last; \
  assign axi_if.master_if[0].ruser = o_axi_s_r.user; \
  assign axi_if.master_if[0].rvalid = o_axi_s_r_valid; \
  assign i_axi_s_r_ready = axi_if.master_if[0].rready;

`define assign_slv_mon_to_axi_err_if \
  assign axi_if.slave_if[0].awid     = dut.axi_err_aw.id; \
  assign axi_if.slave_if[0].awaddr   = dut.axi_err_aw.addr; \
  assign axi_if.slave_if[0].awlen    = dut.axi_err_aw.len; \
  assign axi_if.slave_if[0].awsize   = dut.axi_err_aw.size; \
  assign axi_if.slave_if[0].awburst  = dut.axi_err_aw.burst; \
  assign axi_if.slave_if[0].awlock   = dut.axi_err_aw.lock; \
  assign axi_if.slave_if[0].awcache  = dut.axi_err_aw.cache; \
  assign axi_if.slave_if[0].awprot   = dut.axi_err_aw.prot; \
  assign axi_if.slave_if[0].awqos    = dut.axi_err_aw.qos; \
  assign axi_if.slave_if[0].awregion = dut.axi_err_aw.region; \
  assign axi_if.slave_if[0].awatop   = dut.axi_err_aw.atop; \
  assign axi_if.slave_if[0].awuser   = dut.axi_err_aw.user; \
  assign axi_if.slave_if[0].awvalid = dut.axi_err_aw_valid; \
  assign axi_if.slave_if[0].awready = dut.axi_err_aw_ready; \
  assign axi_if.slave_if[0].wdata = dut.axi_err_w.data; \
  assign axi_if.slave_if[0].wstrb = dut.axi_err_w.strb; \
  assign axi_if.slave_if[0].wlast = dut.axi_err_w.last; \
  assign axi_if.slave_if[0].wuser = dut.axi_err_w.user; \
  assign axi_if.slave_if[0].wvalid = dut.axi_err_w_valid; \
  assign axi_if.slave_if[0].wready = dut.axi_err_w_ready; \
  assign axi_if.slave_if[0].bid = dut.axi_err_b.id; \
  assign axi_if.slave_if[0].bresp = dut.axi_err_b.resp; \
  assign axi_if.slave_if[0].buser = dut.axi_err_b.user; \
  assign axi_if.slave_if[0].bvalid = dut.axi_err_b_valid; \
  assign axi_if.slave_if[0].bready = dut.axi_err_b_ready; \
  assign axi_if.slave_if[0].arid     = dut.axi_err_ar.id; \
  assign axi_if.slave_if[0].araddr   = dut.axi_err_ar.addr; \
  assign axi_if.slave_if[0].arlen    = dut.axi_err_ar.len; \
  assign axi_if.slave_if[0].arsize   = dut.axi_err_ar.size; \
  assign axi_if.slave_if[0].arburst  = dut.axi_err_ar.burst; \
  assign axi_if.slave_if[0].arlock   = dut.axi_err_ar.lock; \
  assign axi_if.slave_if[0].arcache  = dut.axi_err_ar.cache; \
  assign axi_if.slave_if[0].arprot   = dut.axi_err_ar.prot; \
  assign axi_if.slave_if[0].arqos    = dut.axi_err_ar.qos; \
  assign axi_if.slave_if[0].arregion = dut.axi_err_ar.region; \
  assign axi_if.slave_if[0].aruser   = dut.axi_err_ar.user; \
  assign axi_if.slave_if[0].arvalid = dut.axi_err_ar_valid; \
  assign axi_if.slave_if[0].arready = dut.axi_err_ar_ready ; \
  assign axi_if.slave_if[0].rid = dut.axi_err_r.id; \
  assign axi_if.slave_if[0].rdata = dut.axi_err_r.data; \
  assign axi_if.slave_if[0].rresp = dut.axi_err_r.resp; \
  assign axi_if.slave_if[0].rlast = dut.axi_err_r.last; \
  assign axi_if.slave_if[0].ruser = dut.axi_err_r.user; \
  assign axi_if.slave_if[0].rvalid = dut.axi_err_r_valid; \
  assign axi_if.slave_if[0].rready = dut.axi_err_r_ready; 

`define create_mux_mst_conn(id_m_w, addr_m_w, user_w, data_m_w, strb_m_w) \
  axi_aw_``id_m_w``_``addr_m_w``_``user_w``_t i_axi_s_aw[`MST_NUM]; \
  axi_w_``data_m_w``_``strb_m_w``_``user_w``_t  i_axi_s_w[`MST_NUM]; \
  axi_b_``id_m_w``_``user_w``_t     o_axi_s_b[`MST_NUM]; \
  axi_ar_``id_m_w``_``addr_m_w``_``user_w``_t i_axi_s_ar[`MST_NUM]; \
  axi_r_``id_m_w``_``data_m_w``_``user_w``_t  o_axi_s_r[`MST_NUM]; \
  logic i_axi_s_aw_valid[`MST_NUM], o_axi_s_aw_ready[`MST_NUM]; \
  logic i_axi_s_w_valid[`MST_NUM],  o_axi_s_w_ready[`MST_NUM]; \
  logic o_axi_s_b_valid[`MST_NUM],  i_axi_s_b_ready[`MST_NUM]; \
  logic i_axi_s_ar_valid[`MST_NUM], o_axi_s_ar_ready[`MST_NUM]; \
  logic o_axi_s_r_valid[`MST_NUM],  i_axi_s_r_ready[`MST_NUM];

`define assign_mux_mst_conn(mst_num, id_m_w, addr_m_w, user_w, data_m_w, strb_m_w) \
  assign i_axi_s_aw[mst_num].id     = axi_if.master_if[mst_num].awid; \
  assign i_axi_s_aw[mst_num].addr   = axi_if.master_if[mst_num].awaddr; \
  assign i_axi_s_aw[mst_num].len    = axi_if.master_if[mst_num].awlen; \
  assign i_axi_s_aw[mst_num].size   = axi_if.master_if[mst_num].awsize; \
  assign i_axi_s_aw[mst_num].burst  = axi_if.master_if[mst_num].awburst; \
  assign i_axi_s_aw[mst_num].lock   = axi_if.master_if[mst_num].awlock; \
  assign i_axi_s_aw[mst_num].cache  = axi_if.master_if[mst_num].awcache; \
  assign i_axi_s_aw[mst_num].prot   = axi_if.master_if[mst_num].awprot; \
  assign i_axi_s_aw[mst_num].qos    = axi_if.master_if[mst_num].awqos; \
  assign i_axi_s_aw[mst_num].region = axi_if.master_if[mst_num].awregion; \
  assign i_axi_s_aw[mst_num].atop   = axi_if.master_if[mst_num].awatop; \
  assign i_axi_s_aw[mst_num].user   = axi_if.master_if[mst_num].awuser; \
  assign i_axi_s_aw_valid[mst_num] = axi_if.master_if[mst_num].awvalid; \
  assign axi_if.master_if[mst_num].awready = o_axi_s_aw_ready[mst_num]; \
  assign i_axi_s_w[mst_num].data = axi_if.master_if[mst_num].wdata; \
  assign i_axi_s_w[mst_num].strb = axi_if.master_if[mst_num].wstrb; \
  assign i_axi_s_w[mst_num].last = axi_if.master_if[mst_num].wlast; \
  assign i_axi_s_w[mst_num].user = axi_if.master_if[mst_num].wuser; \
  assign i_axi_s_w_valid[mst_num] = axi_if.master_if[mst_num].wvalid; \
  assign axi_if.master_if[mst_num].wready = o_axi_s_w_ready[mst_num]; \
  assign axi_if.master_if[mst_num].bid   = o_axi_s_b[mst_num].id; \
  assign axi_if.master_if[mst_num].bresp = o_axi_s_b[mst_num].resp; \
  assign axi_if.master_if[mst_num].buser = o_axi_s_b[mst_num].user; \
  assign axi_if.master_if[mst_num].bvalid = o_axi_s_b_valid[mst_num]; \
  assign i_axi_s_b_ready[mst_num] = axi_if.master_if[mst_num].bready; \
  assign i_axi_s_ar[mst_num].id     = axi_if.master_if[mst_num].arid; \
  assign i_axi_s_ar[mst_num].addr   = axi_if.master_if[mst_num].araddr; \
  assign i_axi_s_ar[mst_num].len    = axi_if.master_if[mst_num].arlen; \
  assign i_axi_s_ar[mst_num].size   = axi_if.master_if[mst_num].arsize; \
  assign i_axi_s_ar[mst_num].burst  = axi_if.master_if[mst_num].arburst; \
  assign i_axi_s_ar[mst_num].lock   = axi_if.master_if[mst_num].arlock; \
  assign i_axi_s_ar[mst_num].cache  = axi_if.master_if[mst_num].arcache; \
  assign i_axi_s_ar[mst_num].prot   = axi_if.master_if[mst_num].arprot; \
  assign i_axi_s_ar[mst_num].qos    = axi_if.master_if[mst_num].arqos; \
  assign i_axi_s_ar[mst_num].region = axi_if.master_if[mst_num].arregion; \
  assign i_axi_s_ar[mst_num].user   = axi_if.master_if[mst_num].aruser; \
  assign i_axi_s_ar_valid[mst_num] = axi_if.master_if[mst_num].arvalid; \
  assign axi_if.master_if[mst_num].arready = o_axi_s_ar_ready[mst_num]; \
  assign axi_if.master_if[mst_num].rid   = o_axi_s_r[mst_num].id; \
  assign axi_if.master_if[mst_num].rdata = o_axi_s_r[mst_num].data; \
  assign axi_if.master_if[mst_num].rresp = o_axi_s_r[mst_num].resp; \
  assign axi_if.master_if[mst_num].rlast = o_axi_s_r[mst_num].last; \
  assign axi_if.master_if[mst_num].ruser = o_axi_s_r[mst_num].user; \
  assign axi_if.master_if[mst_num].rvalid = o_axi_s_r_valid[mst_num]; \
  assign i_axi_s_r_ready[mst_num] = axi_if.master_if[mst_num].rready;


`define create_demux_slv_conn(id_s_w, addr_s_w, user_w, data_s_w, strb_s_w) \
  axi_aw_``id_s_w``_``addr_s_w``_``user_w``_t o_axi_m_aw[`SLV_NUM]; \
  axi_w_``data_s_w``_``strb_s_w``_``user_w``_t  o_axi_m_w[`SLV_NUM]; \
  axi_b_``id_s_w``_``user_w``_t     i_axi_m_b[`SLV_NUM]; \
  axi_ar_``id_s_w``_``addr_s_w``_``user_w``_t o_axi_m_ar[`SLV_NUM]; \
  axi_r_``id_s_w``_``data_s_w``_``user_w``_t  i_axi_m_r[`SLV_NUM]; \
  logic o_axi_m_aw_valid[`SLV_NUM], i_axi_m_aw_ready[`SLV_NUM]; \
  logic o_axi_m_w_valid[`SLV_NUM], i_axi_m_w_ready[`SLV_NUM]; \
  logic i_axi_m_b_valid[`SLV_NUM], o_axi_m_b_ready[`SLV_NUM]; \
  logic o_axi_m_ar_valid[`SLV_NUM], i_axi_m_ar_ready[`SLV_NUM]; \
  logic i_axi_m_r_valid[`SLV_NUM], o_axi_m_r_ready[`SLV_NUM];

`define assign_demux_slv_conn(slv_num, id_s_w, addr_s_w, user_w, data_s_w, strb_s_w) \
  assign axi_if.slave_if[slv_num].awid     = o_axi_m_aw[slv_num].id; \
  assign axi_if.slave_if[slv_num].awaddr   = o_axi_m_aw[slv_num].addr; \
  assign axi_if.slave_if[slv_num].awlen    = o_axi_m_aw[slv_num].len; \
  assign axi_if.slave_if[slv_num].awsize   = o_axi_m_aw[slv_num].size; \
  assign axi_if.slave_if[slv_num].awburst  = o_axi_m_aw[slv_num].burst; \
  assign axi_if.slave_if[slv_num].awlock   = o_axi_m_aw[slv_num].lock; \
  assign axi_if.slave_if[slv_num].awcache  = o_axi_m_aw[slv_num].cache; \
  assign axi_if.slave_if[slv_num].awprot   = o_axi_m_aw[slv_num].prot; \
  assign axi_if.slave_if[slv_num].awqos    = o_axi_m_aw[slv_num].qos; \
  assign axi_if.slave_if[slv_num].awregion = o_axi_m_aw[slv_num].region; \
  assign axi_if.slave_if[slv_num].awatop   = o_axi_m_aw[slv_num].atop; \
  assign axi_if.slave_if[slv_num].awuser   = o_axi_m_aw[slv_num].user; \
  assign axi_if.slave_if[slv_num].awvalid = o_axi_m_aw_valid[slv_num]; \
  assign i_axi_m_aw_ready[slv_num] = axi_if.slave_if[slv_num].awready; \
  assign axi_if.slave_if[slv_num].wdata = o_axi_m_w[slv_num].data; \
  assign axi_if.slave_if[slv_num].wstrb = o_axi_m_w[slv_num].strb; \
  assign axi_if.slave_if[slv_num].wlast = o_axi_m_w[slv_num].last; \
  assign axi_if.slave_if[slv_num].wuser = o_axi_m_w[slv_num].user; \
  assign axi_if.slave_if[slv_num].wvalid = o_axi_m_w_valid[slv_num]; \
  assign i_axi_m_w_ready[slv_num] = axi_if.slave_if[slv_num].wready; \
  assign i_axi_m_b[slv_num].id   = axi_if.slave_if[slv_num].bid; \
  assign i_axi_m_b[slv_num].resp = axi_if.slave_if[slv_num].bresp; \
  assign i_axi_m_b[slv_num].user = axi_if.slave_if[slv_num].buser; \
  assign i_axi_m_b_valid[slv_num] = axi_if.slave_if[slv_num].bvalid; \
  assign axi_if.slave_if[slv_num].bready = o_axi_m_b_ready[slv_num]; \
  assign axi_if.slave_if[slv_num].arid     = o_axi_m_ar[slv_num].id; \
  assign axi_if.slave_if[slv_num].araddr   = o_axi_m_ar[slv_num].addr; \
  assign axi_if.slave_if[slv_num].arlen    = o_axi_m_ar[slv_num].len; \
  assign axi_if.slave_if[slv_num].arsize   = o_axi_m_ar[slv_num].size; \
  assign axi_if.slave_if[slv_num].arburst  = o_axi_m_ar[slv_num].burst; \
  assign axi_if.slave_if[slv_num].arlock   = o_axi_m_ar[slv_num].lock; \
  assign axi_if.slave_if[slv_num].arcache  = o_axi_m_ar[slv_num].cache; \
  assign axi_if.slave_if[slv_num].arprot   = o_axi_m_ar[slv_num].prot; \
  assign axi_if.slave_if[slv_num].arqos    = o_axi_m_ar[slv_num].qos; \
  assign axi_if.slave_if[slv_num].arregion = o_axi_m_ar[slv_num].region; \
  assign axi_if.slave_if[slv_num].aruser   = o_axi_m_ar[slv_num].user; \
  assign axi_if.slave_if[slv_num].arvalid = o_axi_m_ar_valid[slv_num]; \
  assign i_axi_m_ar_ready[slv_num] = axi_if.slave_if[slv_num].arready; \
  assign i_axi_m_r[slv_num].id   = axi_if.slave_if[slv_num].rid; \
  assign i_axi_m_r[slv_num].data = axi_if.slave_if[slv_num].rdata; \
  assign i_axi_m_r[slv_num].resp = axi_if.slave_if[slv_num].rresp; \
  assign i_axi_m_r[slv_num].last = axi_if.slave_if[slv_num].rlast; \
  assign i_axi_m_r[slv_num].user = axi_if.slave_if[slv_num].ruser; \
  assign i_axi_m_r_valid[slv_num] = axi_if.slave_if[slv_num].rvalid; \
  assign axi_if.slave_if[slv_num].rready = o_axi_m_r_ready[slv_num]; 

`ifdef DUT
  typedef logic [7 : 0] axi_id_8_t;

  typedef struct packed {
    axi_id_8_t            id;
    axe_axi_default_types_pkg::axi_addr_40_t         addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_e   size;
    axi_pkg::axi_burst_e  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axi_pkg::axi_atop_t   atop;
    axe_axi_default_types_pkg::axi_user_4_t          user;
  } axi_aw_8_40_4_t;

  typedef struct packed {
    axi_id_8_t            id;
    axi_pkg::axi_resp_e   resp;
    axe_axi_default_types_pkg::axi_user_4_t          user;
  } axi_b_8_4_t;

  typedef struct packed {
    axi_id_8_t            id;
    axe_axi_default_types_pkg::axi_addr_40_t         addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_e   size;
    axi_pkg::axi_burst_e  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axe_axi_default_types_pkg::axi_user_4_t          user;
  } axi_ar_8_40_4_t;

  typedef struct packed {
    axi_id_8_t            id;
    axe_axi_default_types_pkg::axi_data_64_t         data;
    axi_pkg::axi_resp_e   resp;
    logic                 last;
    axe_axi_default_types_pkg::axi_user_4_t          user;
  } axi_r_8_64_4_t;

`endif

  `define DELAY_AFTER_INIT 5000

  `define GRAPH_DDR_BASE_ADDR 'h0000_0000
  `define GRAPH_DDR_END_ADDR  'h3FFF_FFFF
  `define PP_DDR_BASE_ADDR    'h4000_0000
  `define PP_DDR_END_ADDR     'h7FFF_FFFF
  `define L2_BASE_ADDR        'h8000_0000
  `define L2_END_ADDR         'h801F_FFFF

  typedef enum int {
    SIZE_32B   = 'h20,
    SIZE_64B   = 'h40,
    SIZE_128B  = 'h80,
    SIZE_256B  = 'h100,
    SIZE_512B  = 'h200,
    SIZE_1K    = 'h400,
    SIZE_1M    = 'h100000
  } size_t;

  typedef enum bit [5:0] {
    BW_full    = 0,
    BW_half    = 1,
    BW_quarter = 2,
    BW_8th     = 3,
    BW_16th    = 4
  } bw_t;
