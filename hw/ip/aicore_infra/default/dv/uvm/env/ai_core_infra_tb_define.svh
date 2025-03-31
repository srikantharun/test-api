  //Defines///////////////////////////
  `define AXI_STREAM_IFDW_DATA_WIDTH 512
  `define AXI_STREAM_IFD0_DATA_WIDTH 512
  `define AXI_STREAM_IAU_DATA_WIDTH 1664
  `define AXI_TRANSACTION_BURST_SIZE_8 0
  `define AXI_TRANSACTION_BURST_SIZE_16 1
  `define AXI_TRANSACTION_BURST_SIZE_32 2
  `define AXI_TRANSACTION_BURST_SIZE_64 3
  `define AXI_TRANSACTION_BURST_FIXED 0
  `define AXI_TRANSACTION_BURST_INCR 1
  `define AXI_TRANSACTION_BURST_WRAP 2
  `define AXI_OKAY_RESPONSE 0
  `define AXI_EXOKAY_RESPONSE 1
  `define AXI_SLVERR_RESPONSE 2
  `define AXI_DECERR_RESPONSE 3
  `define QCMD_DEPTH 256
  `define PWORD_SIZE 512
  `define WEIGHT_SETS 4
  `define IMC_ROWS 512
  `define IMC_COLUMN 512
  `define MATRIX 64
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

  `define connect_master_axi_interface(w_name, if_id ) \
    .i_``w_name``_axi_s_awvalid(axi_if.master_if[if_id].awvalid), \
    .i_``w_name``_axi_s_awaddr (axi_if.master_if[if_id].awaddr	), \
    .i_``w_name``_axi_s_awid   (axi_if.master_if[if_id].awid[5:0]), \
    .i_``w_name``_axi_s_awlen  (axi_if.master_if[if_id].awlen	), \
    .i_``w_name``_axi_s_awsize (axi_if.master_if[if_id].awsize[2:0]), \
    .i_``w_name``_axi_s_awburst(axi_if.master_if[if_id].awburst	), \
    .i_``w_name``_axi_s_awcache(axi_if.master_if[if_id].awcache	), \
    .i_``w_name``_axi_s_awprot (axi_if.master_if[if_id].awprot	), \
    .i_``w_name``_axi_s_awlock (axi_if.master_if[if_id].awlock	), \
    .o_``w_name``_axi_s_awready(axi_if.master_if[if_id].awready	), \
    .i_``w_name``_axi_s_wvalid (axi_if.master_if[if_id].wvalid	), \
    .i_``w_name``_axi_s_wlast  (axi_if.master_if[if_id].wlast	), \
    .i_``w_name``_axi_s_wstrb  (axi_if.master_if[if_id].wstrb[7:0]), \
    .i_``w_name``_axi_s_wdata  (axi_if.master_if[if_id].wdata[63:0]), \
    .o_``w_name``_axi_s_wready (axi_if.master_if[if_id].wready	), \
    .o_``w_name``_axi_s_bvalid (axi_if.master_if[if_id].bvalid	), \
    .o_``w_name``_axi_s_bid    (axi_if.master_if[if_id].bid[5:0]), \
    .o_``w_name``_axi_s_bresp  (axi_if.master_if[if_id].bresp	), \
    .i_``w_name``_axi_s_bready (axi_if.master_if[if_id].bready	), \
    .i_``w_name``_axi_s_arvalid(axi_if.master_if[if_id].arvalid), \
    .i_``w_name``_axi_s_araddr (axi_if.master_if[if_id].araddr	), \
    .i_``w_name``_axi_s_arid   (axi_if.master_if[if_id].arid[5:0]), \
    .i_``w_name``_axi_s_arlen  (axi_if.master_if[if_id].arlen	), \
    .i_``w_name``_axi_s_arsize (axi_if.master_if[if_id].arsize[2:0]), \
    .i_``w_name``_axi_s_arburst(axi_if.master_if[if_id].arburst), \
    .i_``w_name``_axi_s_arcache(axi_if.master_if[if_id].arcache), \
    .i_``w_name``_axi_s_arprot (axi_if.master_if[if_id].arprot	), \
    .i_``w_name``_axi_s_arlock (axi_if.master_if[if_id].arlock	), \
    .o_``w_name``_axi_s_arready(axi_if.master_if[if_id].arready), \
    .o_``w_name``_axi_s_rvalid (axi_if.master_if[if_id].rvalid	), \
    .o_``w_name``_axi_s_rlast  (axi_if.master_if[if_id].rlast	), \
    .o_``w_name``_axi_s_rid    (axi_if.master_if[if_id].rid[5:0]), \
    .o_``w_name``_axi_s_rdata  (axi_if.master_if[if_id].rdata[63:0]), \
    .o_``w_name``_axi_s_rresp  (axi_if.master_if[if_id].rresp	), \
    .i_``w_name``_axi_s_rready (axi_if.master_if[if_id].rready	),

  `define connect_slave_axi_interface(w_name, if_id ) \
    .o_``w_name``_axi_m_awvalid(axi_if.slave_if[if_id].awvalid	), \
    .o_``w_name``_axi_m_awaddr (axi_if.slave_if[if_id].awaddr	), \
    .o_``w_name``_axi_m_awid   (axi_if.slave_if[if_id].awid	    ), \
    .o_``w_name``_axi_m_awlen  (axi_if.slave_if[if_id].awlen	), \
    .o_``w_name``_axi_m_awsize (axi_if.slave_if[if_id].awsize), \
    .o_``w_name``_axi_m_awburst(axi_if.slave_if[if_id].awburst	), \
    .o_``w_name``_axi_m_awcache(axi_if.slave_if[if_id].awcache	), \
    .o_``w_name``_axi_m_awprot (axi_if.slave_if[if_id].awprot	), \
    .o_``w_name``_axi_m_awlock (axi_if.slave_if[if_id].awlock	), \
    .i_``w_name``_axi_m_awready(axi_if.slave_if[if_id].awready	), \
    .o_``w_name``_axi_m_wvalid (axi_if.slave_if[if_id].wvalid	), \
    .o_``w_name``_axi_m_wlast  (axi_if.slave_if[if_id].wlast	), \
    .o_``w_name``_axi_m_wstrb  (axi_if.slave_if[if_id].wstrb	), \
    .o_``w_name``_axi_m_wdata  (axi_if.slave_if[if_id].wdata	), \
    .i_``w_name``_axi_m_wready (axi_if.slave_if[if_id].wready	), \
    .i_``w_name``_axi_m_bvalid (axi_if.slave_if[if_id].bvalid	), \
    .i_``w_name``_axi_m_bid    (axi_if.slave_if[if_id].bid	), \
    .i_``w_name``_axi_m_bresp  (axi_if.slave_if[if_id].bresp	), \
    .o_``w_name``_axi_m_bready (axi_if.slave_if[if_id].bready	), \
    .o_``w_name``_axi_m_arvalid(axi_if.slave_if[if_id].arvalid	), \
    .o_``w_name``_axi_m_araddr (axi_if.slave_if[if_id].araddr	), \
    .o_``w_name``_axi_m_arid   (axi_if.slave_if[if_id].arid	), \
    .o_``w_name``_axi_m_arlen  (axi_if.slave_if[if_id].arlen	), \
    .o_``w_name``_axi_m_arsize (axi_if.slave_if[if_id].arsize), \
    .o_``w_name``_axi_m_arburst(axi_if.slave_if[if_id].arburst	), \
    .o_``w_name``_axi_m_arcache(axi_if.slave_if[if_id].arcache	), \
    .o_``w_name``_axi_m_arprot (axi_if.slave_if[if_id].arprot	), \
    .o_``w_name``_axi_m_arlock (axi_if.slave_if[if_id].arlock	), \
    .i_``w_name``_axi_m_arready(axi_if.slave_if[if_id].arready	), \
    .i_``w_name``_axi_m_rvalid (axi_if.slave_if[if_id].rvalid	), \
    .i_``w_name``_axi_m_rlast  (axi_if.slave_if[if_id].rlast	), \
    .i_``w_name``_axi_m_rid    (axi_if.slave_if[if_id].rid	), \
    .i_``w_name``_axi_m_rdata  (axi_if.slave_if[if_id].rdata	), \
    .i_``w_name``_axi_m_rresp  (axi_if.slave_if[if_id].rresp	), \
    .o_``w_name``_axi_m_rready (axi_if.slave_if[if_id].rready	),

  `define connect_slave_axi_interface_slim(w_name, if_id ) \
    .o_``w_name``_axi_m_awvalid(axi_if.slave_if[if_id].awvalid	), \
    .o_``w_name``_axi_m_awaddr (axi_if.slave_if[if_id].awaddr	), \
    .o_``w_name``_axi_m_awid   (axi_if.slave_if[if_id].awid	    ), \
    .o_``w_name``_axi_m_awlen  (axi_if.slave_if[if_id].awlen	), \
    .o_``w_name``_axi_m_awsize (axi_if.slave_if[if_id].awsize), \
    .o_``w_name``_axi_m_awburst(axi_if.slave_if[if_id].awburst	), \
    .i_``w_name``_axi_m_awready(axi_if.slave_if[if_id].awready	), \
    .o_``w_name``_axi_m_wvalid (axi_if.slave_if[if_id].wvalid	), \
    .o_``w_name``_axi_m_wlast  (axi_if.slave_if[if_id].wlast	), \
    .o_``w_name``_axi_m_wstrb  (axi_if.slave_if[if_id].wstrb	), \
    .o_``w_name``_axi_m_wdata  (axi_if.slave_if[if_id].wdata	), \
    .i_``w_name``_axi_m_wready (axi_if.slave_if[if_id].wready	), \
    .i_``w_name``_axi_m_bvalid (axi_if.slave_if[if_id].bvalid	), \
    .i_``w_name``_axi_m_bid    (axi_if.slave_if[if_id].bid	), \
    .i_``w_name``_axi_m_bresp  (axi_if.slave_if[if_id].bresp	), \
    .o_``w_name``_axi_m_bready (axi_if.slave_if[if_id].bready	), \
    .o_``w_name``_axi_m_arvalid(axi_if.slave_if[if_id].arvalid	), \
    .o_``w_name``_axi_m_araddr (axi_if.slave_if[if_id].araddr	), \
    .o_``w_name``_axi_m_arid   (axi_if.slave_if[if_id].arid	), \
    .o_``w_name``_axi_m_arlen  (axi_if.slave_if[if_id].arlen	), \
    .o_``w_name``_axi_m_arsize (axi_if.slave_if[if_id].arsize), \
    .o_``w_name``_axi_m_arburst(axi_if.slave_if[if_id].arburst	), \
    .i_``w_name``_axi_m_arready(axi_if.slave_if[if_id].arready	), \
    .i_``w_name``_axi_m_rvalid (axi_if.slave_if[if_id].rvalid	), \
    .i_``w_name``_axi_m_rlast  (axi_if.slave_if[if_id].rlast	), \
    .i_``w_name``_axi_m_rid    (axi_if.slave_if[if_id].rid	), \
    .i_``w_name``_axi_m_rdata  (axi_if.slave_if[if_id].rdata	), \
    .i_``w_name``_axi_m_rresp  (axi_if.slave_if[if_id].rresp	), \
    .o_``w_name``_axi_m_rready (axi_if.slave_if[if_id].rready	),


  typedef enum bit [3:0] {
    noc_lt_s,
    u_ai_core_cva6v
  } masters_t;

  typedef enum bit [4:0] {
     noc_ht,
     dmc_l1_ht,
     noc_lt,
     dmc_l1_lt,
     u_aic_csr_reg_top,
     u_aic_rv_plic,
     u_aic_spm,
     u_axi_mailbox,
     u_token_manager,
     u_timestamp_logger,
     u_ht_aic_dma,
     u_lt_aic_dma
  } slaves_t;

  masters_t mst_e;
  slaves_t  slv_e;
  `define MST_NUM mst_e.num
  `define SLV_NUM slv_e.num


  typedef struct packed {
    bit is_active;
    int data_width;
    int addr_width;
    int id_width;
  } slave_cfg_t;

  slave_cfg_t slaves_cfg[slaves_t] = '{
    noc_ht              : {1'b1 , 32'd512 , 32'd40 , 32'd9} ,
    dmc_l1_ht           : {1'b1 , 32'd512 , 32'd40 , 32'd9} ,
    noc_lt              : {1'b1 , 32'd64  , 32'd40 , 32'd9} ,
    dmc_l1_lt           : {1'b1 , 32'd64  , 32'd40 , 32'd9} ,
    //passive internal slaves
    u_aic_csr_reg_top   : {1'b0 , 32'd64  , 32'd40 , 32'd7} ,
    u_aic_rv_plic       : {1'b0 , 32'd64  , 32'd40 , 32'd7} ,
    u_aic_spm           : {1'b0 , 32'd64  , 32'd40 , 32'd9} ,
    u_axi_mailbox       : {1'b0 , 32'd64  , 32'd40 , 32'd9} ,
    u_ht_aic_dma        : {1'b0 , 32'd64  , 32'd40 , 32'd8} ,
    u_lt_aic_dma        : {1'b0 , 32'd64  , 32'd40 , 32'd7} ,
    u_timestamp_logger  : {1'b0 , 32'd64  , 32'd40 , 32'd7} ,
    u_token_manager     : {1'b0 , 32'd64  , 32'd40 , 32'd7}
  };


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

  `define uvm_numbered_analysis_imp_decl(SFX) \
  class uvm_analysis_imp``SFX #(type T=int, type IMP=int) \
    extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
    int imp_id = -1; \
    `UVM_IMP_COMMON(`UVM_TLM_ANALYSIS_MASK,`"uvm_analysis_imp``SFX`",IMP) \
    function void write( input T t); \
      if (imp_id < 0) begin \
        uvm_top.uvm_report_fatal(get_type_name(), "imp_id has not been initialized!", UVM_NONE, `uvm_file, `uvm_line); \
      end \
      m_imp.write``SFX( t, imp_id); \
    endfunction \
    \
  endclass


  //AICORE 0 to 7 addr: just add core_id +1 to the MSB addr bit
  //e.g. AICORE_0_CONFIGURATION_PERIPHERALS_MAILBOX addr: {'4h1,ai_core_in_memory_map["AICORE_CONFIGURATION_PERIPHERALS_MAILBOX"][0][27:0]}
  bit [39:0] ai_core_in_memory_map [string] [2] = '{
    "AICORE_CONFIGURATION_PERIPHERALS_MAILBOX"            : { 28'h0000000 , 28'h000FFFF } ,
    "AICORE_CONFIGURATION_PERIPHERALS_TOKEN_MANAGER"      : { 28'h0010000 , 28'h001FFFF } ,
    "AICORE_CONFIGURATION_PERIPHERALS_CSR_INFRA"          : { 28'h0020000 , 28'h002FFFF } ,
    "AICORE_CONFIGURATION_PERIPHERALS_CSR_MID"            : { 28'h0030000 , 28'h003FFFF } ,
    "AICORE_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR" : { 28'h0040000 , 28'h004FFFF } ,
    "AICORE_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM" : { 28'h0050000 , 28'h005FFFF } ,
    "AICORE_CONFIGURATION_PERIPHERALS_PLIC"               : { 28'h0060000 , 28'h006FFFF } ,
    "AICORE_CONFIGURATION_PERIPHERALS_RESERVED"           : { 28'h0070000 , 28'h0FFFFFF } ,
    "AICORE_CONFIGURATION_CONTROL_ACD_CSR"                : { 28'h1000000 , 28'h100FFFF } ,
    "AICORE_CONFIGURATION_CONTROL_ACD_COMMAND"            : { 28'h1010000 , 28'h101FFFF } ,
    "AICORE_CONFIGURATION_CONTROL_LP_DMA"                 : { 28'h1020000 , 28'h102FFFF } ,
    "AICORE_CONFIGURATION_CONTROL_RESERVED"               : { 28'h1030000 , 28'h1FFFFFF } ,
    "AICORE_DATAPATH_CSR_LS_M_IFD_0"                      : { 28'h2000000 , 28'h200FFFF } ,
    "AICORE_DATAPATH_CSR_LS_M_IFD_1"                      : { 28'h2010000 , 28'h201FFFF } ,
    "AICORE_DATAPATH_CSR_LS_M_IFD_2"                      : { 28'h2020000 , 28'h202FFFF } ,
    "AICORE_DATAPATH_CSR_LS_M_IFD_W"                      : { 28'h2030000 , 28'h203FFFF } ,
    "AICORE_DATAPATH_CSR_LS_M_ODR"                        : { 28'h2040000 , 28'h204FFFF } ,
    "AICORE_DATAPATH_CSR_LS_D_IFD_0"                      : { 28'h2050000 , 28'h205FFFF } ,
    "AICORE_DATAPATH_CSR_LS_D_IFD_1"                      : { 28'h2060000 , 28'h206FFFF } ,
    "AICORE_DATAPATH_CSR_LS_D_ODR"                        : { 28'h2070000 , 28'h207FFFF } ,
    "AICORE_DATAPATH_CSR_LS_RESERVED"                     : { 28'h2080000 , 28'h21FFFFF } ,
    "AICORE_DATAPATH_CSR_MID_M_MVMEXE"                    : { 28'h2200000 , 28'h220FFFF } ,
    "AICORE_DATAPATH_CSR_MID_M_MVMPRG"                    : { 28'h2210000 , 28'h221FFFF } ,
    "AICORE_DATAPATH_CSR_MID_M_IAU"                       : { 28'h2220000 , 28'h222FFFF } ,
    "AICORE_DATAPATH_CSR_MID_M_DPU"                       : { 28'h2230000 , 28'h223FFFF } ,
    "AICORE_DATAPATH_CSR_MID_RESERVED"                    : { 28'h2240000 , 28'h23FFFFF } ,
    "AICORE_DATAPATH_CSR_DID_D_DWPU"                      : { 28'h2400000 , 28'h240FFFF } ,
    "AICORE_DATAPATH_CSR_DID_D_IAU"                       : { 28'h2410000 , 28'h241FFFF } ,
    "AICORE_DATAPATH_CSR_DID_D_DPU"                       : { 28'h2420000 , 28'h242FFFF } ,
    "AICORE_DATAPATH_CSR_DID_RESERVED"                    : { 28'h2430000 , 28'h25FFFFF } ,
    "AICORE_DATAPATH_CSR_DMA_HP_DMA_0"                    : { 28'h2600000 , 28'h260FFFF } ,
    "AICORE_DATAPATH_CSR_DMA_HP_DMA_1"                    : { 28'h2610000 , 28'h261FFFF } ,
    "AICORE_DATAPATH_CSR_DMA_MMU"                         : { 28'h2620000 , 28'h262FFFF } ,
    "AICORE_DATAPATH_CSR_DMA_COMMON"                      : { 28'h2630000 , 28'h263FFFF } ,
    "AICORE_DATAPATH_CSR_DMA_RESERVED"                    : { 28'h2640000 , 28'h27FFFFF } ,
    "AICORE_DATAPATH_COMMAND_LS_M_IFD_0"                  : { 28'h2800000 , 28'h280FFFF } ,
    "AICORE_DATAPATH_COMMAND_LS_M_IFD_1"                  : { 28'h2810000 , 28'h281FFFF } ,
    "AICORE_DATAPATH_COMMAND_LS_M_IFD_2"                  : { 28'h2820000 , 28'h282FFFF } ,
    "AICORE_DATAPATH_COMMAND_LS_M_IFD_W"                  : { 28'h2830000 , 28'h283FFFF } ,
    "AICORE_DATAPATH_COMMAND_LS_M_ODR"                    : { 28'h2840000 , 28'h284FFFF } ,
    "AICORE_DATAPATH_COMMAND_LS_D_IFD_0"                  : { 28'h2850000 , 28'h285FFFF } ,
    "AICORE_DATAPATH_COMMAND_LS_D_IFD_1"                  : { 28'h2860000 , 28'h286FFFF } ,
    "AICORE_DATAPATH_COMMAND_LS_D_ODR"                    : { 28'h2870000 , 28'h287FFFF } ,
    "AICORE_DATAPATH_COMMAND_LS_RESERVED"                 : { 28'h2880000 , 28'h29FFFFF } ,
    "AICORE_DATAPATH_COMMAND_MID_M_MVMEXE"                : { 28'h2A00000 , 28'h2A0FFFF } ,
    "AICORE_DATAPATH_COMMAND_MID_M_MVMPRG"                : { 28'h2A10000 , 28'h2A1FFFF } ,
    "AICORE_DATAPATH_COMMAND_MID_M_IAU"                   : { 28'h2A20000 , 28'h2A2FFFF } ,
    "AICORE_DATAPATH_COMMAND_MID_M_DPU"                   : { 28'h2A30000 , 28'h2A3FFFF } ,
    "AICORE_DATAPATH_COMMAND_MID_RESERVED"                : { 28'h2A40000 , 28'h2BFFFFF } ,
    "AICORE_DATAPATH_COMMAND_DID_D_DWPU"                  : { 28'h2C00000 , 28'h2C0FFFF } ,
    "AICORE_DATAPATH_COMMAND_DID_D_IAU"                   : { 28'h2C10000 , 28'h2C1FFFF } ,
    "AICORE_DATAPATH_COMMAND_DID_D_DPU"                   : { 28'h2C20000 , 28'h2C2FFFF } ,
    "AICORE_DATAPATH_COMMAND_DID_RESERVED"                : { 28'h2C30000 , 28'h2DFFFFF } ,
//    "AICORE_DATAPATH_COMMAND_DMA_HP_DMA_0"                  : { 28'h2E00000   , 28'h2E0FFFF   } , //#1986: read from cmd_fifo is not supported
//    "AICORE_DATAPATH_COMMAND_DMA_HP_DMA_1"                  : { 28'h2E10000   , 28'h2E1FFFF   } , //#1986: read from cmd_fifo is not supported
    "AICORE_DATAPATH_COMMAND_DMA_MMU"                     : { 28'h2E20000 , 28'h2E2FFFF } ,
    "AICORE_DATAPATH_COMMAND_DMA_COMMON"                  : { 28'h2E30000 , 28'h2E3FFFF } ,
    "AICORE_DATAPATH_COMMAND_DMA_RESERVED"                : { 28'h2E40000 , 28'h2FFFFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_LS_M_IFD_0"             : { 28'h3000000 , 28'h300FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_LS_M_IFD_1"             : { 28'h3010000 , 28'h301FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_LS_M_IFD_2"             : { 28'h3020000 , 28'h302FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_LS_M_IFD_W"             : { 28'h3030000 , 28'h303FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_LS_M_ODR"               : { 28'h3040000 , 28'h304FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_LS_D_IFD_0"             : { 28'h3050000 , 28'h305FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_LS_D_IFD_1"             : { 28'h3060000 , 28'h306FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_LS_D_ODR"               : { 28'h3070000 , 28'h307FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_LS_RESERVED"            : { 28'h3080000 , 28'h31FFFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_MID_M_MVMEXE"           : { 28'h3200000 , 28'h320FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_MID_M_MVMPRG"           : { 28'h3210000 , 28'h321FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_MID_M_IAU"              : { 28'h3220000 , 28'h322FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_MID_M_DPU"              : { 28'h3230000 , 28'h323FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_MID_RESERVED"           : { 28'h3240000 , 28'h33FFFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_DID_D_DWPU"             : { 28'h3400000 , 28'h340FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_DID_D_IAU"              : { 28'h3410000 , 28'h341FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_DID_D_DPU"              : { 28'h3420000 , 28'h342FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_DID_RESERVED"           : { 28'h3430000 , 28'h35FFFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_0"           : { 28'h3600000 , 28'h360FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_1"           : { 28'h3610000 , 28'h361FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_DMA_MMU"                : { 28'h3620000 , 28'h362FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_DMA_COMMON"             : { 28'h3630000 , 28'h363FFFF } ,
    "AICORE_DATAPATH_INSTRUCTIONS_DMA_RESERVED"           : { 28'h3640000 , 28'h37FFFFF } ,
    "AICORE_DATAPATH_RESERVED"                            : { 28'h3800000 , 28'h3FFFFFF } ,
    "AICORE_SPM"                                          : { 28'h4000000 , 28'h407FFFF } ,
    "AICORE_RESERVED_0"                                   : { 28'h4080000 , 28'h7FFFFFF } ,
    "AICORE_L1"                                           : { 28'h8000000 , 28'h83FFFFF } ,
    "AICORE_RESERVED_1"                                   : { 28'h8400000 , 28'hFFFFFFF }
  };


  bit [39:0] ai_core_out_memory_map [string] [2] = '{
    "APU_RESERVED_0"                        : { 40'h00000000   , 40'h0000FFFF }   ,
    "APU_BOOTROM"                           : { 40'h00010000   , 40'h0001FFFF }   ,
    "APU_CSRS"                              : { 40'h00020000   , 40'h0002FFFF }   ,
    "APU_DMA"                               : { 40'h00030000   , 40'h0003FFFF }   ,
    "APU_MAILBOX"                           : { 40'h00040000   , 40'h0004FFFF }   ,
    "APU_TOKEN_MANAGER"                     : { 40'h00050000   , 40'h0005FFFF }   ,
    "APU_PLMT"                              : { 40'h00060000   , 40'h0006FFFF }   ,
    "APU_RESERVED_1"                        : { 40'h00070000   , 40'h003FFFFF }   ,
    "APU_PLIC"                              : { 40'h00400000   , 40'h007FFFFF }   ,
    "APU_SW_PLIC"                           : { 40'h00800000   , 40'h00BFFFFF }   ,
    "APU_RESERVED_2"                        : { 40'h00C00000   , 40'h01FFFFFF }   ,
    "SOC_MGMT_ROT_ROT_KSE"                  : { 40'h02000000   , 40'h0202FFFF }   ,
    "SOC_MGMT_ROT_ROT_AO"                   : { 40'h02030000   , 40'h0203FFFF }   ,
    "SOC_MGMT_OTP_HOST"                     : { 40'h02040000   , 40'h0204FFFF }   ,
    "SOC_MGMT_TMS"                          : { 40'h02050000   , 40'h0205FFFF }   ,
    "SOC_MGMT_RTC"                          : { 40'h02060000   , 40'h0206FFFF }   ,
    "SOC_MGMT_WATCHDOG"                     : { 40'h02070000   , 40'h0207FFFF }   ,
    "SOC_MGMT_DEBUG"                        : { 40'h02080000   , 40'h0208FFFF }   ,
    "SOC_MGMT_MBIST"                        : { 40'h02090000   , 40'h0209FFFF }   ,
    "SOC_MGMT_RESERVED_0"                   : { 40'h020A0000   , 40'h02FFFFFF }   ,
    "SOC_PERIPH_TIMER"                      : { 40'h03000000   , 40'h0300FFFF }   ,
    "SOC_PERIPH_I2C_0"                      : { 40'h03010000   , 40'h0301FFFF }   ,
    "SOC_PERIPH_I2C_1"                      : { 40'h03020000   , 40'h0302FFFF }   ,
    "SOC_PERIPH_GPIO"                       : { 40'h03030000   , 40'h0303FFFF }   ,
    "SOC_PERIPH_SPI"                        : { 40'h03040000   , 40'h0304FFFF }   ,
    "SOC_PERIPH_EMMC"                       : { 40'h03050000   , 40'h0305FFFF }   ,
    "SOC_PERIPH_UART"                       : { 40'h03060000   , 40'h0306FFFF }   ,
    "SOC_PERIPH_RESERVED_0"                 : { 40'h03070000   , 40'h03FFFFFF }   ,
    "PCIE_DBI_SLAVE"                        : { 40'h04000000   , 40'h043FFFFF }   ,
    "PCIE_APB_CFG_PHY_INTERNAL"             : { 40'h04400000   , 40'h0443FFFF }   ,
    "PCIE_APB_CFG_GEN_CTRL"                 : { 40'h04440000   , 40'h04440FFF }   ,
    "PCIE_APB_CFG_SII_CTRL"                 : { 40'h04441000   , 40'h04441FFF }   ,
    "PCIE_APB_CFG_PHY_CTRL"                 : { 40'h04442000   , 40'h04442FFF }   ,
    "PCIE_APB_CFG_RESERVED_0"               : { 40'h04443000   , 40'h044FFFFF }   ,
    "NOC_SERVICE"                           : { 40'h04500000   , 40'h0450FFFF }   ,
    "NOC_OBSERVER"                          : { 40'h04510000   , 40'h0451FFFF }   ,
    "NOC_RESERVED_0"                        : { 40'h04520000   , 40'h04FFFFFF }   ,
    "SYS_CFG_AICORE_0_AO_CSR"               : { 40'h05000000   , 40'h0500FFFF }   ,
    "SYS_CFG_AICORE_1_AO_CSR"               : { 40'h05010000   , 40'h0501FFFF }   ,
    "SYS_CFG_AICORE_2_AO_CSR"               : { 40'h05020000   , 40'h0502FFFF }   ,
    "SYS_CFG_AICORE_3_AO_CSR"               : { 40'h05030000   , 40'h0503FFFF }   ,
    "SYS_CFG_AICORE_4_AO_CSR"               : { 40'h05040000   , 40'h0504FFFF }   ,
    "SYS_CFG_AICORE_5_AO_CSR"               : { 40'h05050000   , 40'h0505FFFF }   ,
    "SYS_CFG_AICORE_6_AO_CSR"               : { 40'h05060000   , 40'h0506FFFF }   ,
    "SYS_CFG_AICORE_7_AO_CSR"               : { 40'h05070000   , 40'h0507FFFF }   ,
    "SYS_CFG_L2_MODULE_0_AO_CSR"            : { 40'h05080000   , 40'h0508FFFF }   ,
    "SYS_CFG_L2_MODULE_1_AO_CSR"            : { 40'h05090000   , 40'h0509FFFF }   ,
    "SYS_CFG_L2_MODULE_2_AO_CSR"            : { 40'h050A0000   , 40'h050AFFFF }   ,
    "SYS_CFG_L2_MODULE_3_AO_CSR"            : { 40'h050B0000   , 40'h050BFFFF }   ,
    "SYS_CFG_L2_MODULE_4_AO_CSR"            : { 40'h050C0000   , 40'h050CFFFF }   ,
    "SYS_CFG_L2_MODULE_5_AO_CSR"            : { 40'h050D0000   , 40'h050DFFFF }   ,
    "SYS_CFG_L2_MODULE_6_AO_CSR"            : { 40'h050E0000   , 40'h050EFFFF }   ,
    "SYS_CFG_L2_MODULE_7_AO_CSR"            : { 40'h050F0000   , 40'h050FFFFF }   ,
    "SYS_CFG_DDR_0_AO_CSR"                  : { 40'h05100000   , 40'h0510FFFF }   ,
    "SYS_CFG_DDR_1_AO_CSR"                  : { 40'h05110000   , 40'h0511FFFF }   ,
    "SYS_CFG_DDR_2_AO_CSR"                  : { 40'h05120000   , 40'h0512FFFF }   ,
    "SYS_CFG_DDR_3_AO_CSR"                  : { 40'h05130000   , 40'h0513FFFF }   ,
    "SYS_CFG_DDR_4_AO_CSR"                  : { 40'h05140000   , 40'h0514FFFF }   ,
    "SYS_CFG_DDR_5_AO_CSR"                  : { 40'h05150000   , 40'h0515FFFF }   ,
    "SYS_CFG_DDR_6_AO_CSR"                  : { 40'h05160000   , 40'h0516FFFF }   ,
    "SYS_CFG_DDR_7_AO_CSR"                  : { 40'h05170000   , 40'h0517FFFF }   ,
    "SYS_CFG_SYS_SPM_AO_CSR"                : { 40'h05180000   , 40'h0518FFFF }   ,
    "SYS_CFG_APU_AO_CSR"                    : { 40'h05190000   , 40'h0519FFFF }   ,
    "SYS_CFG_DDR_WEST_PLL_AO_CSR"           : { 40'h051A0000   , 40'h051AFFFF }   ,
    "SYS_CFG_SOC_PERIPH_AO_CSR"             : { 40'h051B0000   , 40'h051BFFFF }   ,
    "SYS_CFG_SDMA_0_AO_CSR"                 : { 40'h051C0000   , 40'h051CFFFF }   ,
    "SYS_CFG_SDMA_1_AO_CSR"                 : { 40'h051D0000   , 40'h051DFFFF }   ,
    "SYS_CFG_PCIE_AO_CSR"                   : { 40'h051E0000   , 40'h051EFFFF }   ,
    "SYS_CFG_DECODER_AO_CSR"                : { 40'h051F0000   , 40'h051FFFFF }   ,
    "SYS_CFG_PVE_0_AO_CSR"                  : { 40'h05200000   , 40'h0520FFFF }   ,
    "SYS_CFG_PVE_1_AO_CSR"                  : { 40'h05210000   , 40'h0521FFFF }   ,
    "SYS_CFG_RESERVED_0"                    : { 40'h05220000   , 40'h052FFFFF }   ,
    "SYS_CFG_SOC_MGMT_AO_CSR_CLOCK_GEN_CSR" : { 40'h05300000   , 40'h0530FFFF }   ,
    "SYS_CFG_SOC_MGMT_AO_CSR_RESET_GEN_CSR" : { 40'h05310000   , 40'h0531FFFF }   ,
    "SYS_CFG_SOC_MGMT_AO_CSR_NOC_AO_CSR"    : { 40'h05320000   , 40'h0532FFFF }   ,
    "SYS_CFG_SOC_MGMT_AO_CSR_MISC_AO_CSR"   : { 40'h05330000   , 40'h0533FFFF }   ,
    "SYS_CFG_SOC_MGMT_AO_CSR_DLM_CSR"       : { 40'h05340000   , 40'h0534FFFF }   ,
    "SYS_CFG_SOC_MGMT_AO_CSR_RESERVED_0"    : { 40'h05350000   , 40'h0537FFFF }   ,
    "SYS_CFG_RESERVED_1"                    : { 40'h05380000   , 40'h05FFFFFF }   ,
    "SDMA_0_DMA_MMU"                        : { 40'h06000000   , 40'h0600FFFF }   ,
    "SDMA_0_DMA_COMMON"                     : { 40'h06010000   , 40'h0601FFFF }   ,
    "SDMA_0_DMA_CHANNELS"                   : { 40'h06020000   , 40'h0602FFFF }   ,
    "SDMA_0_DMA_RESERVED"                   : { 40'h06030000   , 40'h0603FFFF }   ,
    "SDMA_0_CSR"                            : { 40'h06040000   , 40'h0604FFFF }   ,
    "SDMA_0_TIMESTAMP_UNIT_CSR"             : { 40'h06050000   , 40'h0605FFFF }   ,
    "SDMA_0_TIMESTAMP_UNIT_MEM"             : { 40'h06060000   , 40'h0606FFFF }   ,
    "SDMA_0_TOKEN_MANAGER"                  : { 40'h06070000   , 40'h0607FFFF }   ,
    "SDMA_1_DMA_MMU"                        : { 40'h06080000   , 40'h0608FFFF }   ,
    "SDMA_1_DMA_COMMON"                     : { 40'h06090000   , 40'h0609FFFF }   ,
    "SDMA_1_DMA_CHANNELS"                   : { 40'h060A0000   , 40'h060AFFFF }   ,
    "SDMA_1_DMA_RESERVED"                   : { 40'h060B0000   , 40'h060BFFFF }   ,
    "SDMA_1_CSR"                            : { 40'h060C0000   , 40'h060CFFFF }   ,
    "SDMA_1_TIMESTAMP_UNIT_CSR"             : { 40'h060D0000   , 40'h060DFFFF }   ,
    "SDMA_1_TIMESTAMP_UNIT_MEM"             : { 40'h060E0000   , 40'h060EFFFF }   ,
    "SDMA_1_TOKEN_MANAGER"                  : { 40'h060F0000   , 40'h060FFFFF }   ,
    "RESERVED_0"                            : { 40'h06100000   , 40'h06FFFFFF }   ,
    "SYS_SPM"                               : { 40'h07000000   , 40'h077FFFFF }   ,
    "RESERVED_1"                            : { 40'h07800000   , 40'h07FFFFFF }   ,
    "L2_MODULE_0"                           : { 40'h08000000   , 40'h08FFFFFF }   ,
    "L2_MODULE_1"                           : { 40'h09000000   , 40'h09FFFFFF }   ,
    "L2_MODULE_2"                           : { 40'h0A000000   , 40'h0AFFFFFF }   ,
    "L2_MODULE_3"                           : { 40'h0B000000   , 40'h0BFFFFFF }   ,
    "L2_MODULE_4"                           : { 40'h0C000000   , 40'h0CFFFFFF }   ,
    "L2_MODULE_5"                           : { 40'h0D000000   , 40'h0DFFFFFF }   ,
    "L2_MODULE_6"                           : { 40'h0E000000   , 40'h0EFFFFFF }   ,
    "L2_MODULE_7"                           : { 40'h0F000000   , 40'h0FFFFFFF }   ,
    "PVE_0_DMA0"                            : { 40'h90000000   , 40'h9000FFFF }   ,
    "PVE_0_DMA1"                            : { 40'h90010000   , 40'h9001FFFF }   ,
    "PVE_0_CLINT"                           : { 40'h90020000   , 40'h9002FFFF }   ,
    "PVE_0_PERF_COUNTERS"                   : { 40'h90030000   , 40'h9003FFFF }   ,
    "PVE_0_TRACE_IP"                        : { 40'h90040000   , 40'h9004FFFF }   ,
    "PVE_0_RESERVED_0"                      : { 40'h90050000   , 40'h93FFFFFF }   ,
    "PVE_0_SPM"                             : { 40'h94000000   , 40'h9403FFFF }   ,
    "PVE_0_RESERVED_1"                      : { 40'h94040000   , 40'h97FFFFFF }   ,
    "PVE_0_L1_0"                            : { 40'h98000000   , 40'h983FFFFF }   ,
    "PVE_0_L1_1"                            : { 40'h98400000   , 40'h987FFFFF }   ,
    "PVE_0_L1_2"                            : { 40'h98800000   , 40'h98BFFFFF }   ,
    "PVE_0_L1_3"                            : { 40'h98C00000   , 40'h98FFFFFF }   ,
    "PVE_0_RESERVED_2"                      : { 40'h99000000   , 40'h9FFFFFFF }   ,
    "PVE_1_DMA0"                            : { 40'hA0000000   , 40'hA000FFFF }   ,
    "PVE_1_DMA1"                            : { 40'hA0010000   , 40'hA001FFFF }   ,
    "PVE_1_CLINT"                           : { 40'hA0020000   , 40'hA002FFFF }   ,
    "PVE_1_PERF_COUNTERS"                   : { 40'hA0030000   , 40'hA003FFFF }   ,
    "PVE_1_TRACE_IP"                        : { 40'hA0040000   , 40'hA004FFFF }   ,
    "PVE_1_RESERVED_0"                      : { 40'hA0050000   , 40'hA3FFFFFF }   ,
    "PVE_1_SPM"                             : { 40'hA4000000   , 40'hA403FFFF }   ,
    "PVE_1_RESERVED_1"                      : { 40'hA4040000   , 40'hA7FFFFFF }   ,
    "PVE_1_L1_0"                            : { 40'hA8000000   , 40'hA83FFFFF }   ,
    "PVE_1_L1_1"                            : { 40'hA8400000   , 40'hA87FFFFF }   ,
    "PVE_1_L1_2"                            : { 40'hA8800000   , 40'hA8BFFFFF }   ,
    "PVE_1_L1_3"                            : { 40'hA8C00000   , 40'hA8FFFFFF }   ,
    "PVE_1_RESERVED_2"                      : { 40'hA9000000   , 40'hAFFFFFFF }   ,
    "DECODER_DECODER_INTERNAL"              : { 40'hB0000000   , 40'hB00FFFFF }   ,
    "RESERVED_2"                            : { 40'hB0100000   , 40'hBFFFFFFF }   ,
    "RESERVED_3"                            : { 40'hC0000000   , 40'hFFFFFFFF }   ,
    "DDR_0_CTRL_PHY_PUB"                    : { 40'h100000000  , 40'h101FFFFFF }  ,
    "DDR_0_CTRL_UMCTL2"                     : { 40'h102000000  , 40'h1023FFFFF }  ,
    "DDR_0_CTRL_RESERVED"                   : { 40'h102400000  , 40'h1FFFFFFFF }  ,
    "DDR_1_CTRL_PHY_PUB"                    : { 40'h200000000  , 40'h201FFFFFF }  ,
    "DDR_1_CTRL_UMCTL2"                     : { 40'h202000000  , 40'h2023FFFFF }  ,
    "DDR_1_CTRL_RESERVED"                   : { 40'h202400000  , 40'h2FFFFFFFF }  ,
    "DDR_2_CTRL_PHY_PUB"                    : { 40'h300000000  , 40'h301FFFFFF }  ,
    "DDR_2_CTRL_UMCTL2"                     : { 40'h302000000  , 40'h3023FFFFF }  ,
    "DDR_2_CTRL_RESERVED"                   : { 40'h302400000  , 40'h3FFFFFFFF }  ,
    "DDR_3_CTRL_PHY_PUB"                    : { 40'h400000000  , 40'h401FFFFFF }  ,
    "DDR_3_CTRL_UMCTL2"                     : { 40'h402000000  , 40'h4023FFFFF }  ,
    "DDR_3_CTRL_RESERVED"                   : { 40'h402400000  , 40'h4FFFFFFFF }  ,
    "DDR_4_CTRL_PHY_PUB"                    : { 40'h500000000  , 40'h501FFFFFF }  ,
    "DDR_4_CTRL_UMCTL2"                     : { 40'h502000000  , 40'h5023FFFFF }  ,
    "DDR_4_CTRL_RESERVED"                   : { 40'h502400000  , 40'h5FFFFFFFF }  ,
    "DDR_5_CTRL_PHY_PUB"                    : { 40'h600000000  , 40'h601FFFFFF }  ,
    "DDR_5_CTRL_UMCTL2"                     : { 40'h602000000  , 40'h6023FFFFF }  ,
    "DDR_5_CTRL_RESERVED"                   : { 40'h602400000  , 40'h6FFFFFFFF }  ,
    "DDR_6_CTRL_PHY_PUB"                    : { 40'h700000000  , 40'h701FFFFFF }  ,
    "DDR_6_CTRL_UMCTL2"                     : { 40'h702000000  , 40'h7023FFFFF }  ,
    "DDR_6_CTRL_RESERVED"                   : { 40'h702400000  , 40'h7FFFFFFFF }  ,
    "DDR_7_CTRL_PHY_PUB"                    : { 40'h800000000  , 40'h801FFFFFF }  ,
    "DDR_7_CTRL_UMCTL2"                     : { 40'h802000000  , 40'h8023FFFFF }  ,
    "DDR_7_CTRL_RESERVED"                   : { 40'h802400000  , 40'h8FFFFFFFF }  ,
    "RESERVED_4"                            : { 40'h900000000  , 40'h1FFFFFFFFF } ,
    "DDR_0"                                 : { 40'h2000000000 , 40'h27FFFFFFFF } ,
    "DDR_1"                                 : { 40'h2800000000 , 40'h2FFFFFFFFF } ,
    "HOST"                                  : { 40'h3000000000 , 40'h3FFFFFFFFF } ,
    "RESERVED_5"                            : { 40'h4000000000 , 40'hFFFFFFFFFF }
  };




