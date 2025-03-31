
package dma_ip_common_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import dma_pkg::*;

  // Typedefs, local params, constants etc

  //Defines///////////////////////////
  
  // DUT and TB Components Sizing 
  // -------------------
  localparam NUM_PORTS                     = 2;
  localparam NUM_CHANNELS                  = 4;
  
  // AXI VIP Sizing etc 
  // -------------------
  // Define the USEABLE fields of the AXI MAster and SLAVE VIPs
  //
  // NOTE that the simulation_config.mk file defines the MAX SIZES (upper-limit) of the AXI Master and Slave Interfaces
  // via
  //    override GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=40
  //    override GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=512
  //    override GLOBAL_DEFINES += +define+SVT_AXI_MAX_ID_WIDTH=9
  //
  // So the the axi master and slave VIP interfaces will be sized as above, using the above DEFINES
  //
  // HOWEVER, the parameters below specify the usable fields of those interfaces
  //
  // So while the AXI MASTER and SLAVE interfaces are sized with (say) AxDATA WDITH as 512 Max [511:0] via above
  // AXI MASTER VIP DATA will use only 63:0  as below  (DATA WIDTH=64)
  // AXI SLAVE VIP  ADDR will use only 511:0 as below  (DATA WIDTH=512)
  

  // AXI MASTER VIP connected to DUT AXI SLAVE I/F 
  localparam AXI_M_ADDR_WIDTH              = 40;
  localparam AXI_M_DATA_WIDTH              = 64;
  localparam AXI_M_ID_WIDTH                = 4;

  // AXI SLAVE VIP connected to DUT AXI MASTER I/F (assume both DUT Master Interfaces are sized the same)
  localparam AXI_S_ADDR_WIDTH              = 40;
  localparam AXI_S_DATA_WIDTH              = 512;
  localparam AXI_S_ID_WIDTH                = 9;

  localparam AXI_TRANSACTION_BURST_SIZE_8  = 0;
  localparam AXI_TRANSACTION_BURST_SIZE_16 = 1;
  localparam AXI_TRANSACTION_BURST_SIZE_32 = 2;
  localparam AXI_TRANSACTION_BURST_SIZE_64 = 3;
  
  localparam AXI_TRANSACTION_BURST_FIXED   = 0;
  localparam AXI_TRANSACTION_BURST_INCR    = 1;
  localparam AXI_TRANSACTION_BURST_WRAP    = 2;
  
  localparam AXI_OKAY_RESPONSE             = 0;
  localparam AXI_EXOKAY_RESPONSE           = 1;
  localparam AXI_SLVERR_RESPONSE           = 2;
  localparam AXI_DECERR_RESPONSE           = 3;
  
  localparam AXI_TRANSACTION_TYPE_READ     = 0;
  localparam AXI_TRANSACTION_TYPE_WRITE    = 1;
  localparam AXI_TRANSACTION_TYPE_IDLE     = 2;  
  
  localparam AXI_TRANSACTION_PROT_UNPRIV     = 0;
  localparam AXI_TRANSACTION_PROT_PRIV       = 1;
  localparam AXI_TRANSACTION_PROT_SECURE     = 0;
  localparam AXI_TRANSACTION_PROT_NON_SECURE = 1;
  localparam AXI_TRANSACTION_PROT_DATA       = 0;
  localparam AXI_TRANSACTION_PROT_INSTR      = 1;


  // AXI VIP Delays
  // --------------
  // For AXI MASTER VIPs
  localparam AXI_ADDR_VALID_MAX_DELAY      = 20;
  localparam AXI_WVALID_MAX_DELAY          = 20;  
  localparam AXI_BREADY_MAX_DELAY          = 20;   // Cannot be more than europa/hw/dv/axi4pc/AxiPC.sv : parameter BREADY_MAXWAITS = 16;
  localparam AXI_RREADY_MAX_DELAY          = 16;   // Cannot be more than europa/hw/dv/axi4pc/AxiPC.sv : parameter RREADY_MAXWAITS = 16;

  // For AXI SLAVE VIPs
  localparam AXI_S_ADDR_READY_MAX_DELAY    = 16;   // Cannot be more than europa/hw/dv/axi4pc/AxiPC.sv : parameter AWREADY_MAXWAITS = 16; parameter ARREADY_MAXWAITS = 16;
  localparam AXI_S_WREADY_MAX_DELAY        = 16;   // Cannot be more than europa/hw/dv/axi4pc/AxiPC.sv : parameter WREADY_MAXWAITS = 16;
  localparam AXI_S_BVALID_MAX_DELAY        = 16;   // Cannot be more than europa/hw/dv/axi4pc/AxiPC.sv : parameter BREADY_MAXWAITS = 16;
  localparam AXI_S_RVALID_MAX_DELAY        = 16;   // Cannot be more than europa/hw/dv/axi4pc/AxiPC.sv : parameter RREADY_MAXWAITS = 16;
    
  // ****************************************************************************
  // Enumerated Types
  // ****************************************************************************

  /**
   * Enum to represent transfer sizes
   */
  typedef enum bit [3:0] {
    BURST_SIZE_8BIT    = AXI_TRANSACTION_BURST_SIZE_8,
    BURST_SIZE_16BIT   = AXI_TRANSACTION_BURST_SIZE_16,
    BURST_SIZE_32BIT   = AXI_TRANSACTION_BURST_SIZE_32,
    BURST_SIZE_64BIT   = AXI_TRANSACTION_BURST_SIZE_64
  } burst_size_enum;

  /**
   * Enum to represent burst type in a transaction
   */
  typedef enum bit[1:0]{
    FIXED = AXI_TRANSACTION_BURST_FIXED,
    INCR =  AXI_TRANSACTION_BURST_INCR,
    WRAP =  AXI_TRANSACTION_BURST_WRAP
  } burst_type_enum;

  /**
   * Enum to represent burst lenght in a transaction
   */
  typedef enum bit[5:0]{
    BURST_LENGTH_1 = 1,
    BURST_LENGTH_2 = 2,
    BURST_LENGTH_4 = 4,
    BURST_LENGTH_8 = 8,
    BURST_LENGTH_16 = 16
  } burst_lenght_enum;

  /**
   * Enum to represent responses in a transaction
   */
  typedef enum bit [1:0] {
    OKAY    = AXI_OKAY_RESPONSE,
    EXOKAY  = AXI_EXOKAY_RESPONSE,
    SLVERR =  AXI_SLVERR_RESPONSE,
    DECERR  = AXI_DECERR_RESPONSE
  } resp_type_enum;

  // Enum to represent transaction type
  typedef enum bit [2:0]{
    READ      = AXI_TRANSACTION_TYPE_READ,
    WRITE     = AXI_TRANSACTION_TYPE_WRITE,
    IDLE      = AXI_TRANSACTION_TYPE_IDLE
  } trans_type_enum;


  // ------------------------------------------------------------------------------------
  // Enum Types Representing DMA Regsters 
  
  typedef enum bit [7:0] {
    // GLOBAL (COMMON) REGISTERS
    DMA_CH_COMMON_MODE,
    DMA_CH_COMMON_STATUS,

    // CHANNEL CMD BLOCK
    DMA_CH_CMDBLK_FIFO,

    // CHANNEL REGISTER BLOCK
    DMA_CH_CMDBLK_CTRL,
    DMA_CH_CMDBLK_STATUS,
    DMA_CH_IRQ_EN,
    DMA_CH_IRQ_STATUS,
    DMA_CH_SWDP_CTRL,
    DMA_CH_SWDP_STATUS,
    DMA_CH_DP_CTRL,
    DMA_CH_DP_STATUS,
    DMA_CH_DBG_OBSERVE,
    DMA_CH_CMDGEN_STATUS,
    DMA_CH_DBG_SCRATCH,
    DMA_CH_DBG_ID,
    DMA_CH_HW_CAPABILITY,
    DMA_CH_PERF_CTRL,
    DMA_CH_PERF_STATE,
    DMA_CH_PERF_STALL,
    DMA_CH_PERF_STALL_IN,
    DMA_CH_PERF_STALL_OUT,
    DMA_CH_CTRL,
    DMA_CH_CFG,
    DMA_CH_SRC_ADDR,
    DMA_CH_DST_ADDR,
    DMA_CH_XBYTESIZE,
    DMA_CH_YROWSIZE,
    DMA_CH_TRAN_CFG,
    DMA_CH_XADDRINC,
    DMA_CH_YADDRSTRIDE,
    DMA_CH_LINK_DESCR,
    DMA_CH_STATUS,
    DMA_CH_ERR_INFO,
    DMA_CH_REQ_BUS_CTRL
  } dma_reg_types_enum;

  // ------------------------------------------------------------------------------------
  // Enum Types Representing Infor forwarded to SCBD
  
  // The Types of Basic Testing that take place
  typedef enum {
    // Non-DMA MODEL based testing - Pure UVM slef-contained testcases only
    REGISTER_BASED,             // Register    Based Testing
    CMDBLK_BASED,               // CMD Block   Based Testing
    LINKED_LIST_BASED,          // Linked-List Based Testing

    // DMA MODEL Fle Based Testing
    MODEL_BASED_CSR,					  // Register    Based Testing using DMA MODEL files
    MODEL_BASED_CMDBLK,  			  // CMD Block   Based Testing using DMA MODEL files
    MODEL_BASED_LL   					  // Linked-List Based Testing using DMA MODEL files
  } testing_type_t;

  // Register Setup
  typedef struct packed {
    bit [63:0] src_addr;     
    bit [63:0] dst_addr;     
    bit [3:0]  transize;     
    bit [3:0]  xtype;        
    bit [31:0] src_xbytesize;
    bit [31:0] dst_xbytesize;
    bit [31:0] src_xaddrinc;     
    bit [31:0] dst_xaddrinc;     
    bit [3:0]  ytype;        
    bit [31:0] src_yrowsize; 
    bit [31:0] dst_yrowsize; 
    bit [31:0] src_yaddrstride;  
    bit [31:0] dst_yaddrstride;  
    bit [7:0]  src_burstlen; 
    bit [7:0]  dst_burstlen; 
    bit [15:0] fillval; 
    bit        fillval_mode;   
    bit        transform_en;     
    bit [3:0]  transform_type;
    
    // Additional info based on rand members
    bit [1:0]  src_ms;
    bit [1:0]  dst_ms;
  } channel_setup_t;

  // Expected AXI-Transactions in the DMA transfers
  typedef struct packed {
    bit        W_nR;     
    bit [63:0] start_addr;     
    bit [63:0] end_addr;     
    int        burst_len;
    int        burst_size;
    int        num_data_transfers;
  } axi_transfer_makeup_t;
  
  // ------------------------------------------------------------------------------------


  `include "dma_ip_transfer_details.svh"

  endpackage : dma_ip_common_pkg

