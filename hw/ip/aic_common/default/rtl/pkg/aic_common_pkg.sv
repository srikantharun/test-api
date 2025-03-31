// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>


/// Parameters, structures, and functions used by all AI IPs
///

package aic_common_pkg;

  // =========================
  // Pixels, pixel words etc.
  // =========================
  // Standard pixels/PWORD as found in memory
parameter int AIC_PWORD_SIZE = 64;  // elements per PWORD (64)
parameter int AIC_PWORD32_SIZE = 32;  // elements per PWORD (32)
parameter int AIC_PWORD64_INT_WIDTH = 8;
parameter int AIC_PWORD32_INT_WIDTH = 16;
parameter int AIC_PWORD_WIDTH = AIC_PWORD_SIZE * AIC_PWORD64_INT_WIDTH;  // DATA_WIDTH * AIC_PWORD_SIZE
parameter int AIC_PWORD_WIDTH_BYTES = (AIC_PWORD_WIDTH + 7) / 8;
// Different PWORD flavours based in element width
// PWORD int8 is interchangable with the standard PWORD
parameter int AIC_PWORD_I8_WIDTH = AIC_PWORD_WIDTH;
parameter int AIC_PWORD_I8_WIDTH_BYTES = AIC_PWORD_WIDTH_BYTES;
// PWORD int26 appears between MVM and IAU
parameter int AIC_PWORD64_MVM_IAU_INT_WIDTH = 26;
parameter int AIC_PWORD32_MVM_IAU_INT_WIDTH = 42;
parameter int AIC_PWORD_I26_WIDTH = AIC_PWORD_SIZE * AIC_PWORD64_MVM_IAU_INT_WIDTH;
parameter int AIC_PWORD_I26_WIDTH_BYTES = (AIC_PWORD_I26_WIDTH + 7) / 8;
// PWORD int32 appears between IAU and DPU
parameter int AIC_PWORD64_IAU_DPU_INT_WIDTH = 32;
parameter int AIC_PWORD32_IAU_DPU_INT_WIDTH = 48;
parameter int AIC_PWORD_I32_WIDTH = AIC_PWORD_SIZE * AIC_PWORD64_IAU_DPU_INT_WIDTH;
parameter int AIC_PWORD_I32_WIDTH_BYTES = (AIC_PWORD_I32_WIDTH + 7) / 8;
// PWORD float18 appears inside DPU
parameter int AIC_PWORD_F18_WIDTH = AIC_PWORD_SIZE * 18;
parameter int AIC_PWORD_F18_WIDTH_BYTES = (AIC_PWORD_F18_WIDTH + 7) / 8;
// PWORD float32 appears inside DPU
parameter int AIC_PWORD_F32_WIDTH = AIC_PWORD_SIZE * 32;
parameter int AIC_PWORD_F32_WIDTH_BYTES = (AIC_PWORD_F32_WIDTH + 7) / 8;


//========================
// General AXIS parameters
//========================
parameter int AIC_PWORD_I8_AXIS_TDATA_WIDTH = AIC_PWORD_I8_WIDTH;
parameter int AIC_PWORD_I8_AXIS_TSTRB_WIDTH = AIC_PWORD_SIZE;
parameter int AIC_PWORD_I8_AXIS_FIFO_DATA_WIDTH = AIC_PWORD_I8_AXIS_TDATA_WIDTH +1; // + AIC_PWORD_I8_AXIS_TSTRB_WIDTH
parameter int AIC_PWORD_I26_AXIS_TDATA_WIDTH = AIC_PWORD_I26_WIDTH;
parameter int AIC_PWORD_I26_AXIS_TSTRB_WIDTH = AIC_PWORD_SIZE;
parameter int AIC_PWORD_I26_AXIS_FIFO_DATA_WIDTH = AIC_PWORD_I26_AXIS_TDATA_WIDTH +1; // + AIC_PWORD_I26_AXIS_TSTRB_WIDTH
parameter int AIC_PWORD_I32_AXIS_TDATA_WIDTH = AIC_PWORD_I32_WIDTH;
parameter int AIC_PWORD_I32_AXIS_TSTRB_WIDTH = AIC_PWORD_SIZE;
parameter int AIC_PWORD_I32_AXIS_FIFO_DATA_WIDTH = AIC_PWORD_I32_AXIS_TDATA_WIDTH +1; // + AIC_PWORD_I32_AXIS_TSTRB_WIDTH
parameter int AIC_PWORD_F18_AXIS_TDATA_WIDTH = AIC_PWORD_F18_WIDTH;
parameter int AIC_PWORD_F18_AXIS_TSTRB_WIDTH = AIC_PWORD_SIZE;
parameter int AIC_PWORD_F18_AXIS_FIFO_DATA_WIDTH = AIC_PWORD_F18_AXIS_TDATA_WIDTH +1; // + AIC_PWORD_F18_AXIS_TSTRB_WIDTH
parameter int AIC_PWORD_F32_AXIS_TDATA_WIDTH = AIC_PWORD_F32_WIDTH;
parameter int AIC_PWORD_F32_AXIS_TSTRB_WIDTH = AIC_PWORD_SIZE;
parameter int AIC_PWORD_F32_AXIS_FIFO_DATA_WIDTH = AIC_PWORD_F32_AXIS_TDATA_WIDTH +1; // + AIC_PWORD_F32_AXIS_TSTRB_WIDTH


//========================
// Token network parameters
//========================
parameter int AIC_TOK_OCPL_ADDR_WIDTH = 8;
parameter int AIC_TOK_OCPL_DATA_WIDTH = 8;
parameter int AIC_TOK_OCPL_SRESP_WIDTH = 2;


//========================
// CID parameters
//========================
parameter int AIC_CID_LSB = 28;
parameter int AIC_CID_WIDTH = 12;  // based on 40 bit address
parameter int AIC_CID_SUB_W = 4; // 1-8, so 4 bit required

parameter int AIC_VA_BASE_LSB = 22; // 22 bits [21:0] are used to address the L1 4MB. everything above that is base addr.

//========================
// General CMDB parameters
//========================
// Use these values in your subip/subsys (pkg) to configure the CMDB and BP CMD FIFO
// If you want to deviate from these values for a specific reason, you can do so in your subip (pkg), and list your deviation below
parameter int AIC_GEN_CMDB_MAX_OUTST_CMDS = 4;
parameter int AIC_GEN_CMDB_CMD_FIFO_DEPTH = 16;
parameter int AIC_GEN_CMDB_BP_CMD_FIFO_DEPTH = 4;
parameter int AIC_GEN_DESC_MEM_ARB_SCHEME = 1;  // 1 = Round Robin, 0 = Row Access Priority
// Deviation list:
// -(example)ai_core_mvm: MVM_EXE_CMDB_MAX_OUTST_CMDS = 10


//========================
// Observation signal parameters
//========================
parameter int AIC_OBS_DW = 16;

typedef struct packed {
  logic [1:0] state;
  logic token_stall;
  logic dp_instr_stall;
  logic dp_cmd_stall;
  logic dp_in0_stall;
  logic dp_in1_stall;
  logic dp_out_stall;
} aic_dev_obs_t;
parameter int AIC_DEV_OBS_DW = $bits(aic_dev_obs_t);

typedef struct packed {
  aic_dev_obs_t m_ifd0_obs;
  aic_dev_obs_t m_ifd1_obs;
  aic_dev_obs_t m_ifd2_obs;
  aic_dev_obs_t m_ifdw_obs;
  aic_dev_obs_t m_odr_obs;
  aic_dev_obs_t d_ifd0_obs;
  aic_dev_obs_t d_ifd1_obs;
  aic_dev_obs_t d_odr_obs;
} dmc_obs_t;

parameter int AIC_DMC_OBS_DW = $bits(dmc_obs_t);

typedef struct packed {
  logic [6:0] sampled_avg_util;
  logic [6:0] util_limit;
  logic combined_throttle;
} tu_obs_t;
parameter int AIC_TU_OBS_DW = $bits(tu_obs_t);

// DMA OBS (6b)
typedef struct packed {logic [5:0] dma_chan_en_obs;} dma_obs_t;
parameter int AIC_DMA_OBS_DW = $bits(dma_obs_t);

//========================
// Block identifiers
//========================
parameter int AIC_BLOCK_ID_WIDTH = 8;

// Please keep in sync with data/ai_core_block_id.csv
parameter int unsigned AIC_BLOCK_ID_M_IFD0 = 8'h74;
parameter int unsigned AIC_BLOCK_ID_M_IFD1 = 8'hE4;
parameter int unsigned AIC_BLOCK_ID_M_IFD2 = 8'h3F;
parameter int unsigned AIC_BLOCK_ID_M_IFDW = 8'h28;
parameter int unsigned AIC_BLOCK_ID_M_ODR = 8'h30;
parameter int unsigned AIC_BLOCK_ID_D_IFD0 = 8'hBD;
parameter int unsigned AIC_BLOCK_ID_D_IFD1 = 8'h4B;
parameter int unsigned AIC_BLOCK_ID_D_ODR = 8'h71;
parameter int unsigned AIC_BLOCK_ID_M_MVM = 8'hF2;
parameter int unsigned AIC_BLOCK_ID_M_IAU = 8'h84;
parameter int unsigned AIC_BLOCK_ID_M_DPU = 8'h7D;
parameter int unsigned AIC_BLOCK_ID_D_DWPU = 8'h49;
parameter int unsigned AIC_BLOCK_ID_D_IAU = 8'hE0;
parameter int unsigned AIC_BLOCK_ID_D_DPU = 8'h3B;

// CSR Identification Register
parameter int unsigned AIC_BLOCK_ID_CSR = 8'h1F;
// AI Core Version (0.1)
parameter int unsigned AIC_HW_REVISION_MAJ = 8'h1;
parameter int unsigned AIC_HW_REVISION_MIN = 8'h0;

// AXI interface

typedef struct packed {
  logic activity;
  logic gen_call;
  logic rd_req;
  logic rx_done;
  logic rx_full;
  logic rx_over;
  logic rx_under;
  logic start_det;
  logic stop_det;
  logic tx_abrt;
  logic tx_empty;
  logic tx_over;
  logic scl_stuck_at_low;
  logic smbus_clk_mext;
  logic smbus_clk_sext;
  logic smbus_host_notify;
  logic smbus_quick_cmd_det;
} i2c_irq_t;

// HT AXI
parameter int AIC_HT_AXI_DATA_WIDTH = 512;
parameter int AIC_HT_AXI_DATA_WIDTH_B = AIC_HT_AXI_DATA_WIDTH / 8;
parameter int AIC_HT_AXI_MAX_BURST_LEN    = 4096 / AIC_HT_AXI_DATA_WIDTH_B; // 1-64 beats supported for AIC_HT_AXI_DATA_WIDTH = 512bits
parameter int AIC_HT_AXI_LEN_WIDTH = 8;  // fully AXI compliant: 8 bits
parameter int AIC_HT_NOC_AXI_LEN_WIDTH = 8;
parameter int AIC_HT_AXI_WSTRB_WIDTH = AIC_HT_AXI_DATA_WIDTH / 8;
parameter int AIC_HT_AXI_ADDR_WIDTH = 40;
parameter int AIC_HT_AXI_S_ID_WIDTH = 9;  // as spec-ed in #40
parameter int AIC_HT_AXI_M_ID_WIDTH = 6;  // as spec-ed in #40
parameter int AIC_HT_AXI_NS_ID_WIDTH = 6;  // as spec-ed in #40
parameter int AIC_HT_AXI_NM_ID_WIDTH = 9;  // as spec-ed in #40
parameter int AIC_HT_AXI_SIZE_WIDTH = axi_pkg::AXI_SIZE_WIDTH;                           // Burst size is encoded in 3-bits as per AIC_HT_AXI_burst_size_t
parameter int AIC_HT_AXI_BURST_TYPE_WIDTH = axi_pkg::AXI_BURST_WIDTH;               // Burst type is encoded in 2-bits as per AIC_HT_AXI_burst_type_t
parameter int AIC_HT_AXI_RESP_WIDTH  = axi_pkg::AXI_RESP_WIDTH;                          // Resp is encoded in 2-bits as per AIC_HT_AXI_resp_type_e
parameter int AIC_HT_AXI_CACHE_WIDTH = axi_pkg::AXI_CACHE_WIDTH;
parameter int AIC_HT_AXI_PROT_WIDTH = axi_pkg::AXI_PROT_WIDTH;

// HT AXI typedef
typedef logic [AIC_HT_AXI_M_ID_WIDTH-1:0]  aic_ht_axi_m_id_t;
typedef logic [AIC_HT_AXI_S_ID_WIDTH-1:0]  aic_ht_axi_s_id_t;
typedef logic [AIC_HT_AXI_ADDR_WIDTH-1:0]  aic_ht_axi_addr_t;
typedef logic [AIC_HT_AXI_DATA_WIDTH-1:0]  aic_ht_axi_data_t;
typedef logic [AIC_HT_AXI_WSTRB_WIDTH-1:0] aic_ht_axi_strb_t;

// LT AXI
parameter int AIC_LT_AXI_DATA_WIDTH = 64;
parameter int AIC_LT_AXI_DATA_WIDTH_B = 64 / 8;
parameter int AIC_LT_AXI_MAX_BURST_LEN = 256; // 1-256 beats supported for AIC_LT_AXI_DATA_WIDTH = 64bits
parameter int AIC_LT_AXI_LEN_WIDTH = 8;  // fully AXI compliant: 8 bits
parameter int AIC_LT_AXI_WSTRB_WIDTH = AIC_LT_AXI_DATA_WIDTH / 8;
parameter int AIC_LT_AXI_ADDR_WIDTH = 40;
parameter int AIC_LT_AXI_LOCAL_ADDR_WIDTH = 28;
parameter int AIC_LT_AXI_M_ID_WIDTH = 6;
parameter int AIC_LT_AXI_S_ID_WIDTH = 9;
parameter int AIC_LT_AXI_NM_ID_WIDTH = 9;
parameter int AIC_LT_AXI_NS_ID_WIDTH = 6;
parameter int AIC_LT_AXI_SIZE_WIDTH = axi_pkg::AXI_SIZE_WIDTH;                           // Burst size is encoded in 3-bits as per AIC_HT_AXI_burst_size_t
parameter int AIC_LT_AXI_BURST_TYPE_WIDTH = axi_pkg::AXI_BURST_WIDTH;               // Burst type is encoded in 2-bits as per AIC_HT_AXI_burst_type_t
parameter int AIC_LT_AXI_RESP_WIDTH  = axi_pkg::AXI_RESP_WIDTH;                          // Resp is encoded in 2-bits as per AIC_HT_AXI_resp_type_e
parameter int AIC_LT_AXI_CACHE_WIDTH = axi_pkg::AXI_CACHE_WIDTH;
parameter int AIC_LT_AXI_PROT_WIDTH = axi_pkg::AXI_PROT_WIDTH;

// LT AXI typedef
typedef logic [AIC_LT_AXI_DATA_WIDTH-1:0]       aic_lt_axi_data_t;
typedef logic [AIC_LT_AXI_ADDR_WIDTH-1:0]       aic_lt_axi_addr_t;
typedef logic [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] aic_lt_axi_loc_addr_t;
typedef logic [AIC_LT_AXI_WSTRB_WIDTH-1:0]      aic_lt_axi_strb_t;
typedef logic [AIC_LT_AXI_M_ID_WIDTH-1:0]       aic_lt_axi_m_id_t;
typedef logic [AIC_LT_AXI_S_ID_WIDTH-1:0]       aic_lt_axi_s_id_t;

// =========
// Clocking
// =========
parameter int unsigned AIC_PHASE_ACC_WIDTH = 4;

endpackage
