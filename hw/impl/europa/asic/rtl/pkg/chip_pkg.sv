// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>


/// Chip Package File
///

package chip_pkg;

/// AXI parameters

// Primary Parameters
parameter int unsigned CHIP_AXI_ADDR_W        =  40;
parameter int unsigned CHIP_SYSCFG_ADDR_W     =  16;
parameter int unsigned CHIP_SOC_MGMT_SYSCFG   =  19;
parameter int unsigned CHIP_AXI_LT_DATA_W     =  64;
parameter int unsigned CHIP_AXI_HT_DATA_W     = 512;
parameter int unsigned CHIP_AXI_TRC_DATA_W    =  32;
parameter int unsigned CHIP_APB_SYSCFG_DATA_W =  32;
parameter int unsigned CHIP_OCPL_TOKEN_ADDR_W =   8;
parameter int unsigned CHIP_OCPL_TOKEN_DATA_W =   8;

parameter int unsigned CHIP_AXI_LT_AWUSER_W =   1;
parameter int unsigned CHIP_AXI_LT_WUSER_W  =   1;
parameter int unsigned CHIP_AXI_LT_BUSER_W  =   1;
parameter int unsigned CHIP_AXI_LT_ARUSER_W =   1;
parameter int unsigned CHIP_AXI_LT_RUSER_W  =   1;

parameter int unsigned CHIP_AXI_HT_AWUSER_W =   1;
parameter int unsigned CHIP_AXI_HT_WUSER_W  =   1;
parameter int unsigned CHIP_AXI_HT_BUSER_W  =   1;
parameter int unsigned CHIP_AXI_HT_ARUSER_W =   1;
parameter int unsigned CHIP_AXI_HT_RUSER_W  =   1;

parameter int unsigned CHIP_AXI_MT_AWUSER_W =   1;
parameter int unsigned CHIP_AXI_MT_WUSER_W  =   1;
parameter int unsigned CHIP_AXI_MT_BUSER_W  =   1;
parameter int unsigned CHIP_AXI_MT_ARUSER_W =   1;
parameter int unsigned CHIP_AXI_MT_RUSER_W  =   1;

parameter int unsigned CHIP_AXI_TRC_AWUSER_W =   1;
parameter int unsigned CHIP_AXI_TRC_WUSER_W  =   1;
parameter int unsigned CHIP_AXI_TRC_BUSER_W  =   1;
parameter int unsigned CHIP_AXI_TRC_ARUSER_W =   1;
parameter int unsigned CHIP_AXI_TRC_RUSER_W  =   1;

parameter int unsigned CHIP_APB_SYSCFG_USER_REQ_W = 1;
parameter int unsigned CHIP_APB_SYSCFG_USER_DATA_W = 1;
parameter int unsigned CHIP_APB_SYSCFG_USER_RESP_W = 1;

// Derived Parameters
parameter int unsigned CHIP_AXI_LT_WSTRB_W  = CHIP_AXI_LT_DATA_W/8;
parameter int unsigned CHIP_AXI_HT_WSTRB_W  = CHIP_AXI_HT_DATA_W/8;
parameter int unsigned CHIP_AXI_TRC_WSTRB_W = CHIP_AXI_TRC_DATA_W/8;
parameter int unsigned CHIP_APB_SYSCFG_STRB_W  = CHIP_APB_SYSCFG_DATA_W/8;

// TypeDefs
// Common NOC
typedef logic [CHIP_AXI_ADDR_W-1:0]       chip_axi_addr_t;
typedef logic [CHIP_SYSCFG_ADDR_W-1:0]    chip_syscfg_addr_t;
typedef logic [CHIP_SOC_MGMT_SYSCFG-1:0]  chip_soc_mgmt_syscfg_addr_t;
// Low Bandwidth NOC
typedef logic [CHIP_AXI_LT_DATA_W-1:0]    chip_axi_lt_data_t;
typedef logic [CHIP_AXI_LT_WSTRB_W-1:0]   chip_axi_lt_wstrb_t;
typedef logic [CHIP_AXI_LT_AWUSER_W-1:0]  chip_axi_lt_awuser_t;
typedef logic [CHIP_AXI_LT_WUSER_W-1:0]   chip_axi_lt_wuser_t;
typedef logic [CHIP_AXI_LT_BUSER_W-1:0]   chip_axi_lt_buser_t;
typedef logic [CHIP_AXI_LT_ARUSER_W-1:0]  chip_axi_lt_aruser_t;
typedef logic [CHIP_AXI_LT_RUSER_W-1:0]   chip_axi_lt_ruser_t;
// High Bandwidth NOC
typedef logic [CHIP_AXI_HT_DATA_W-1:0]    chip_axi_ht_data_t;
typedef logic [CHIP_AXI_HT_WSTRB_W-1:0]   chip_axi_ht_wstrb_t;
typedef logic [CHIP_AXI_HT_AWUSER_W-1:0]  chip_axi_ht_awuser_t;
typedef logic [CHIP_AXI_HT_WUSER_W-1:0]   chip_axi_ht_wuser_t;
typedef logic [CHIP_AXI_HT_BUSER_W-1:0]   chip_axi_ht_buser_t;
typedef logic [CHIP_AXI_HT_ARUSER_W-1:0]  chip_axi_ht_aruser_t;
typedef logic [CHIP_AXI_HT_RUSER_W-1:0]   chip_axi_ht_ruser_t;
// Mixed Bandwidth NOC
typedef logic [CHIP_AXI_MT_AWUSER_W-1:0]  chip_axi_mt_awuser_t;
typedef logic [CHIP_AXI_MT_WUSER_W-1:0]   chip_axi_mt_wuser_t;
typedef logic [CHIP_AXI_MT_BUSER_W-1:0]   chip_axi_mt_buser_t;
typedef logic [CHIP_AXI_MT_ARUSER_W-1:0]  chip_axi_mt_aruser_t;
typedef logic [CHIP_AXI_MT_RUSER_W-1:0]   chip_axi_mt_ruser_t;
// Trace NOC
typedef logic [CHIP_AXI_TRC_DATA_W-1:0]   chip_axi_trc_data_t;
typedef logic [CHIP_AXI_TRC_WSTRB_W-1:0]  chip_axi_trc_wstrb_t;
typedef logic [CHIP_AXI_TRC_AWUSER_W-1:0] chip_axi_trc_awuser_t;
typedef logic [CHIP_AXI_TRC_WUSER_W-1:0]  chip_axi_trc_wuser_t;
typedef logic [CHIP_AXI_TRC_BUSER_W-1:0]  chip_axi_trc_buser_t;
typedef logic [CHIP_AXI_TRC_ARUSER_W-1:0] chip_axi_trc_aruser_t;
typedef logic [CHIP_AXI_TRC_RUSER_W-1:0]  chip_axi_trc_ruser_t;
// Sys Cfg NOC
typedef logic [CHIP_APB_SYSCFG_DATA_W-1:0] chip_apb_syscfg_data_t;
typedef logic [CHIP_APB_SYSCFG_STRB_W-1:0] chip_apb_syscfg_strb_t;
typedef logic [CHIP_APB_SYSCFG_USER_REQ_W-1:0] chip_apb_syscfg_auser_t;
typedef logic [CHIP_APB_SYSCFG_USER_DATA_W-1:0] chip_apb_syscfg_wuser_t;
typedef logic [CHIP_APB_SYSCFG_USER_DATA_W-1:0] chip_apb_syscfg_ruser_t;
typedef logic [CHIP_APB_SYSCFG_USER_RESP_W-1:0] chip_apb_syscfg_buser_t;
// Token Network NOC
typedef logic [CHIP_OCPL_TOKEN_ADDR_W-1:0] chip_ocpl_token_addr_t;
typedef logic [CHIP_OCPL_TOKEN_DATA_W-1:0] chip_ocpl_token_data_t;

endpackage
