package ai_core_dwpu_common_pkg;

  `include "uvm_macros.svh"
  import aic_common_pkg::*;
  import uvm_pkg::*;
  import dwpu_pkg::*;
  import dwpu_csr_ral_pkg::*;

  //Defines///////////////////////////
  localparam AXI_LT_ADDR_WIDTH                  = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH;
  localparam AXI_LT_DATA_WIDTH                  = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH;
  localparam AXI_STREAM_IFD0_DATA_WIDTH         = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH;
  localparam AXI_STREAM_IAU_DATA_WIDTH          = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH;
  localparam DWPU_INSTR_NUM_ROWS                = int'($ceil(real'($bits(dwpu_pkg::dwpu_dp_command_t)) / real'(AXI_LT_DATA_WIDTH)));
  localparam DWPU_INSTR_BYTES                   = DWPU_INSTR_NUM_ROWS * 8;
  localparam INSTR_MEM_DEPTH                    = 1024;
  localparam DWPU_IN_WORD_DW                    = AXI_STREAM_IFD0_DATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  localparam DWPU_OUT_WORD_DW                   = AXI_STREAM_IAU_DATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  localparam EXTEND_LEN                         = DWPU_OUT_WORD_DW - DWPU_IN_WORD_DW;
  localparam DWPU_CSR_ST_ADDR                   = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_ST_ADDR[dwpu_pkg::CSR];
  localparam DWPU_CSR_END_ADDR                  = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_END_ADDR[dwpu_pkg::CSR];
  localparam DWPU_CMD_ST_ADDR                   = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_ST_ADDR[dwpu_pkg::CMDB];
  localparam DWPU_CMD_END_ADDR                  = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_END_ADDR[dwpu_pkg::CMDB];
  localparam DWPU_IMEM_ST_ADDR                  = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_ST_ADDR[dwpu_pkg::IMEM];
  localparam DWPU_IMEM_END_ADDR                 = aic_addr_map_pkg::AIC_LOC_D_DWPU_REGION_END_ADDR[dwpu_pkg::IMEM];
  localparam DWPU_CSR_REGION_SIZE               = DWPU_CSR_END_ADDR - DWPU_CSR_ST_ADDR +1;
  localparam DWPU_CMD_REGION_SIZE               = DWPU_CMD_END_ADDR - DWPU_CMD_ST_ADDR +1;
  localparam DWPU_IMEM_REGION_SIZE              = INSTR_MEM_DEPTH * DWPU_INSTR_NUM_ROWS * 8;
  localparam DWPU_CSR_REGION_END                = DWPU_CSR_END_ADDR;
  localparam DWPU_CMD_REGION_END                = DWPU_CMD_END_ADDR;
  localparam DWPU_IMEM_REGION_END               = DWPU_IMEM_ST_ADDR+DWPU_IMEM_REGION_SIZE-1;
  localparam DWPU_CMD_MEM_WIDTH                 = $bits(aic_dp_cmd_gen_pkg::cmdb_cmd_t);
  localparam DWPU_CMD_NUM_ROWS_FULL             = DWPU_CMD_MEM_WIDTH / AXI_LT_DATA_WIDTH; //without header
  localparam DWPU_CMD_NUM_ROWS_BYPASS           = 0; //bypass command does not have payload
  localparam DWPU_CMD_NUM_ROWS_M1N0            = 1;
  localparam DWPU_CMD_NUM_ROWS_M1N1            = 2;
  localparam DWPU_CMD_NUM_ROWS_M1N2            = 3;
  localparam DWPU_CMD_NUM_ROWS_M2N0            = 2;
  localparam DWPU_CMD_NUM_ROWS_M2N1            = 3;
  localparam DWPU_CMD_NUM_ROWS_M2N2            = 4;
  localparam DWPU_CMD_NUM_ROWS_M3N0            = 3;
  localparam DWPU_CMD_NUM_ROWS_M3N1            = 4;
  localparam DWPU_CMD_NUM_ROWS_M3N2            = 5;
  localparam HEADER_CMD_TOK_PROD_WIDTH          = 16;
  localparam HEADER_CMD_TOK_CONS_WIDTH          = 16;
  localparam HEADER_CMD_RSVD_FORMAT_WIDTH       = 8-aic_dp_cmd_gen_pkg::CmdBlockFormatWidth;
  localparam HEADER_CMD_RSVD_WIDTH              = 8;
  localparam HEADER_CMD_TRIGGERS_WIDTH          = 8;
  localparam HEADER_CMD_CONFIG_WIDTH            = 8;

  // ****************************************************************************
  // Typedefs used in whole testbench
  // ****************************************************************************

  typedef dwpu_csr_reg_block DWPU_RAL;

  typedef  bit [AXI_LT_ADDR_WIDTH-1:0] axi_lp_addr_t;
  typedef  bit [AXI_LT_DATA_WIDTH-1:0] axi_lp_data_t;
  typedef  bit [8 - 1:0] axi_lp_wstrb_t;

  // ****************************************************************************
  // Enumerated Types
  // ****************************************************************************

  typedef struct packed {
    bit [HEADER_CMD_CONFIG_WIDTH-1:0]           h_config;
    bit [HEADER_CMD_RSVD_FORMAT_WIDTH-1:0]      rsvd_format;
    aic_dp_cmd_gen_pkg::cmd_format_e            format;
    bit [HEADER_CMD_TOK_CONS_WIDTH-1:0]         token_cons;
    bit [HEADER_CMD_TOK_PROD_WIDTH-1:0]         token_prod;
    bit [HEADER_CMD_RSVD_WIDTH-1:0]             rsvd;
    bit [HEADER_CMD_TRIGGERS_WIDTH-1:0]         triggers;
  } dwpu_cmd_header_t;

  typedef enum bit [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] {
    DWPU_IRQ_ERR_ACT_STREAM_IN      = 'd0,
    DWPU_IRQ_ERR_ACT_STREAM_OUT     = 'd1,
    DWPU_IRQ_ERR_ILLEGAL_FORMAT     = 'd2,
    DWPU_IRQ_ERR_EMPTY_PROGRAM      = 'd3,
    DWPU_IRQ_ERR_MAIN_0_LEN         = 'd4,
    DWPU_IRQ_ERR_MAIN_1_LEN         = 'd5,
    DWPU_IRQ_ERR_MAIN_2_LEN         = 'd6,
    DWPU_IRQ_ERR_NESTED_0_LEN       = 'd7,
    DWPU_IRQ_ERR_NESTED_1_LEN       = 'd8,
    DWPU_IRQ_ERR_NESTED_0_MAP       = 'd9,
    DWPU_IRQ_ERR_NESTED_1_MAP       = 'd10,
    DWPU_IRQ_ERR_NESTED_0_SEGFAULT  = 'd11,
    DWPU_IRQ_ERR_NESTED_1_SEGFAULT  = 'd12,
    DWPU_IRQ_ERR_NESTED_ORDER       = 'd13,
    DWPU_IRQ_ERR_NESTED_NESTING     = 'd14,
    DWPU_IRQ_ERR_NESTED_OVERLAP     = 'd15,
    DWPU_IRQ_CMDBLK_CMD_DROPPED     = 'd16,
    DWPU_IRQ_DBG_SW_INTERRUPT       = 'd32
  } dwpu_irq_t;


  `include "ai_core_dwpu_cmd_tr.sv"
  `include "ai_core_dwpu_utils.svh"
endpackage : ai_core_dwpu_common_pkg

