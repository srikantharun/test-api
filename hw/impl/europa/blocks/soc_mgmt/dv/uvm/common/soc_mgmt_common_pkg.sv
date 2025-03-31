package soc_mgmt_common_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import soc_mgmt_ral_pkg::*;

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
  

  `include "soc_mgmt_utils.svh"

  localparam SOC_MGMT_ROT_KSE_ST_ADDR   = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR;
  localparam SOC_MGMT_ROT_KSE_END_ADDR  = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_END_ADDR;
  localparam SOC_MGMT_ROT_AO_ST_ADDR    = aipu_addr_map_pkg::SOC_MGMT_ROT_AO_ST_ADDR;
  localparam SOC_MGMT_ROT_AO_END_ADDR   = aipu_addr_map_pkg::SOC_MGMT_ROT_AO_END_ADDR;
  localparam SOC_MGMT_OTP_HOST_ST_ADDR      = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR;
  localparam SOC_MGMT_OTP_HOST_END_ADDR     = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_END_ADDR;
  localparam SOC_MGMT_TMS_ST_ADDR           = aipu_addr_map_pkg::SOC_MGMT_TMS_ST_ADDR;
  localparam SOC_MGMT_TMS_END_ADDR          = aipu_addr_map_pkg::SOC_MGMT_TMS_END_ADDR;
  localparam SOC_MGMT_RTC_ST_ADDR           = aipu_addr_map_pkg::SOC_MGMT_RTC_ST_ADDR;
  localparam SOC_MGMT_RTC_END_ADDR          = aipu_addr_map_pkg::SOC_MGMT_RTC_END_ADDR;
  localparam SOC_MGMT_WATCHDOG_ST_ADDR      = aipu_addr_map_pkg::SOC_MGMT_WATCHDOG_ST_ADDR;
  localparam SOC_MGMT_WATCHDOG_END_ADDR     = aipu_addr_map_pkg::SOC_MGMT_WATCHDOG_END_ADDR;
  localparam SOC_MGMT_DEBUG_ST_ADDR         = aipu_addr_map_pkg::SOC_MGMT_DEBUG_ST_ADDR;
  localparam SOC_MGMT_DEBUG_END_ADDR        = aipu_addr_map_pkg::SOC_MGMT_DEBUG_END_ADDR;
  localparam SOC_MGMT_MBIST_ST_ADDR         = aipu_addr_map_pkg::SOC_MGMT_MBIST_ST_ADDR;
  localparam SOC_MGMT_MBIST_END_ADDR        = aipu_addr_map_pkg::SOC_MGMT_MBIST_END_ADDR;
    
  localparam SYS_CFG_SOC_MGMT_AO_CSR_CLOCK_GEN_CSR_ST_ADDR      = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_CLOCK_GEN_CSR_ST_ADDR;
  localparam SYS_CFG_SOC_MGMT_AO_CSR_CLOCK_GEN_CSR_END_ADDR     = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_CLOCK_GEN_CSR_END_ADDR;
  localparam SYS_CFG_SOC_MGMT_AO_CSR_RESET_GEN_CSR_ST_ADDR      = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_RESET_GEN_CSR_ST_ADDR;
  localparam SYS_CFG_SOC_MGMT_AO_CSR_RESET_GEN_CSR_END_ADDR     = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_RESET_GEN_CSR_END_ADDR;
  localparam SYS_CFG_SOC_MGMT_AO_CSR_NOC_AO_CSR_ST_ADDR         = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_NOC_AO_CSR_ST_ADDR;
  localparam SYS_CFG_SOC_MGMT_AO_CSR_NOC_AO_CSR_END_ADDR        = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_NOC_AO_CSR_END_ADDR;
  localparam SYS_CFG_SOC_MGMT_AO_CSR_MISC_AO_CSR_ST_ADDR        = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_MISC_AO_CSR_ST_ADDR;
  localparam SYS_CFG_SOC_MGMT_AO_CSR_MISC_AO_CSR_END_ADDR       = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_MISC_AO_CSR_END_ADDR;
  localparam SYS_CFG_SOC_MGMT_AO_CSR_DLM_CSR_ST_ADDR            = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_DLM_CSR_ST_ADDR;
  localparam SYS_CFG_SOC_MGMT_AO_CSR_DLM_CSR_END_ADDR           = aipu_addr_map_pkg::SYS_CFG_SOC_MGMT_AO_CSR_DLM_CSR_END_ADDR;
  
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_CTRL_0_OFFSET    = 16'h0000;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_CTRL_1_OFFSET    = 16'h0004;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_CTRL_2_OFFSET    = 16'h0008;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_DIV_0_OFFSET     = 16'h0100;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_DIV_1_OFFSET     = 16'h0104;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_DIV_2_OFFSET     = 16'h0108;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_STATIC_0_OFFSET  = 16'h0200;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_STATIC_1_OFFSET  = 16'h0204;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_STATIC_2_OFFSET  = 16'h0208;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_0_OFFSET         = 16'h1000;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_1_OFFSET         = 16'h1004;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_2_OFFSET         = 16'h1008;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_0_OFFSET     = 16'h2000;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_1_OFFSET     = 16'h2004;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_2_OFFSET     = 16'h2008;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_3_OFFSET     = 16'h200C;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_4_OFFSET     = 16'h2010;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_5_OFFSET     = 16'h2014;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DDR_CONFIG_OFFSET       = 16'h2018;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_STATUS_0_OFFSET     = 16'h3000;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_STATUS_1_OFFSET     = 16'h3004;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_STATUS_2_OFFSET     = 16'h3008;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_STATUS_3_OFFSET     = 16'h300C;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_STATUS_4_OFFSET     = 16'h3010;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_STATUS_5_OFFSET     = 16'h3014;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_MUX_DDR_STATUS_OFFSET       = 16'h3018;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_FREQ_COUNTER_0_OFFSET       = 16'h4000;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_FREQ_COUNTER_1_OFFSET       = 16'h4004;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_FREQ_COUNTER_2_OFFSET       = 16'h4008;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_FREQ_COUNTER_3_OFFSET       = 16'h400C;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_FREQ_COUNTER_4_OFFSET       = 16'h4010;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_FREQ_COUNTER_5_OFFSET       = 16'h4014;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_FREQ_COUNTER_6_OFFSET       = 16'h4018;
  parameter logic [15:0] SOC_MGMT_CLOCK_GEN_CSR_FREQ_COUNTER_7_OFFSET       = 16'h401C;
  
  endpackage : soc_mgmt_common_pkg

