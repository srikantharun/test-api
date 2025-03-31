// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>


/// Description: Europa SoC Management root of trust Package file
///
package rot_pkg;

  // --------------------------------------------------------------------------
  // APB
  // --------------------------------------------------------------------------
  //
  // SECU ENCLAVE APB address bus width
  parameter int  unsigned                     SECU_ENCL_PAW = 32;
  // SECU ENCLAVE APB data bus width
  parameter int  unsigned                     SECU_ENCL_PDW = 32;
  parameter int  unsigned                     SECU_ENCL_PSTRBW = SECU_ENCL_PDW/8;
  typedef logic [SECU_ENCL_PAW-1:0]           soc_mgmt_secu_encl_paddr_t;
  typedef logic [SECU_ENCL_PDW-1:0]           soc_mgmt_secu_encl_pdata_t;
  typedef logic [SECU_ENCL_PSTRBW-1:0]        soc_mgmt_secu_encl_pstrb_t;
  // APB MUX
  parameter int  unsigned                     SECU_ENCL_MUX_NB_APBIN = 3;
  parameter int  unsigned                     SECU_ENCL_APB_MUX_IDXW = 2;
  parameter int  unsigned                     SECU_ENCL_APB_MUX_KSE_IDX  = 0;
  parameter int  unsigned                     SECU_ENCL_APB_MUX_HOST_IDX = 1;
  parameter int  unsigned                     SECU_ENCL_APB_MUX_JTAG_IDX = 2;
  typedef logic [SECU_ENCL_APB_MUX_IDXW-1:0]  secu_encl_apb_mux_idx_t;
  // APB DEMUX (OTP, AOR)
  parameter int  unsigned                     SECU_ENCL_DEMUX_NB_APBOUT = 3;
  parameter int  unsigned                     SECU_ENCL_APB_IDXW = 2;
  parameter int  unsigned                     APB_DEMUX_OTP_IDX = 0;
  parameter int  unsigned                     APB_DEMUX_AOR_IDX = 1;
  parameter int  unsigned                     APB_DEMUX_ERR_IDX = 2;
  typedef logic [SECU_ENCL_APB_IDXW -1:0]     secu_encl_apb_demux_idx_t;
  // OTP address zones size
  parameter int  unsigned                     OTP_SECU_SIZE_BYTES     = 256;
  parameter int  unsigned                     OTP_WR_PROT_SIZE_BYTES  = 856;
  // OTP address zone definitions
  parameter logic [SECU_ENCL_PAW-1:0]         OTP_SECU_START_ADDR     = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR;
  parameter logic [SECU_ENCL_PAW-1:0]         OTP_SECU_END_ADDR       = OTP_SECU_START_ADDR + OTP_SECU_SIZE_BYTES -1;
  parameter logic [SECU_ENCL_PAW-1:0]         OTP_WR_PROT_START_ADDR  = OTP_SECU_END_ADDR +1;
  parameter logic [SECU_ENCL_PAW-1:0]         OTP_WR_PROT_END_ADDR    = OTP_WR_PROT_START_ADDR + OTP_WR_PROT_SIZE_BYTES -1;
  parameter logic [SECU_ENCL_PAW-1:0]         OTP_PUB_START_ADDR      = OTP_WR_PROT_END_ADDR +1;
  parameter logic [SECU_ENCL_PAW-1:0]         OTP_PUB_END_ADDR        = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_END_ADDR;
  // AOR address zones size
  parameter int  unsigned                     AOR_WR_PROT_SIZE_BYTES  = 24;
  parameter int  unsigned                     AOR_SECU_SIZE_BYTES     = 40;
  // AOR address zone definitions
  parameter logic [SECU_ENCL_PAW-1:0]         AOR_WR_PROT_START_ADDR  = aipu_addr_map_pkg::SOC_MGMT_ROT_AO_ST_ADDR;
  parameter logic [SECU_ENCL_PAW-1:0]         AOR_WR_PROT_END_ADDR    = AOR_WR_PROT_START_ADDR + AOR_WR_PROT_SIZE_BYTES -1;
  parameter logic [SECU_ENCL_PAW-1:0]         AOR_SECU_START_ADDR     = AOR_WR_PROT_END_ADDR +1;
  parameter logic [SECU_ENCL_PAW-1:0]         AOR_SECU_END_ADDR       = AOR_SECU_START_ADDR + AOR_SECU_SIZE_BYTES -1;
  // AOR public, not visible by KSE3 but acccessible by APU/JTAG
  parameter logic [SECU_ENCL_PAW-1:0]         AOR_PUB_START_ADDR      = AOR_SECU_END_ADDR +1;
  parameter logic [SECU_ENCL_PAW-1:0]         AOR_PUB_END_ADDR        = aipu_addr_map_pkg::SOC_MGMT_ROT_AO_END_ADDR;
  parameter int  unsigned                     DBG_TAPS_EN_W           = 15;
  typedef logic [DBG_TAPS_EN_W-1:0]           dbg_taps_en_t;

  // --------------------------------------------------------------------------
  // AHB
  // --------------------------------------------------------------------------
  //
  // SOC MGMT AHB address bus width
  parameter int  unsigned                     SOC_MGMT_HAW    = 32;
  // SOC MGMT AHB data bus width
  parameter int  unsigned                     SOC_MGMT_HDW    = 32;
  // SOC MGMT AHB HRESP width
  parameter int  unsigned                     SOC_MGMT_HRESPW = 2;

  typedef logic [SOC_MGMT_HAW-1:0]            soc_mgmt_haddr_t;
  typedef logic [SOC_MGMT_HDW-1:0]            soc_mgmt_hdata_t;
  typedef logic [SOC_MGMT_HRESPW-1:0]         soc_mgmt_hresp_t;
  // AHB MUX
  parameter int  unsigned                     SECU_ENCL_MUX_NB_AHBIN = 2;
  parameter int  unsigned                     SECU_ENCL_AHB_MUX_JTAG_IDX = 0;
  parameter int  unsigned                     SECU_ENCL_AHB_MUX_APU_IDX = 1;
  // AHB DEMUX
  parameter int  unsigned                     SECU_ENCL_DEMUX_NB_AHBOUT = 3;
  parameter int  unsigned                     SECU_ENCL_DEMUX_IDXW = 2;
  typedef logic [SECU_ENCL_DEMUX_IDXW-1:0]    secu_encl_ahb_demux_idx_t;
  parameter secu_encl_ahb_demux_idx_t         SECU_ENCL_AHB_DEMUX_KSE3_IDX = 0;
  parameter secu_encl_ahb_demux_idx_t         SECU_ENCL_AHB_DEMUX_OTP_AON_IDX = 1;
  parameter secu_encl_ahb_demux_idx_t         SECU_ENCL_AHB_DEMUX_ERR_IDX = 2;

  // --------------------------------------------------------------------------
  // Secure enclave Test Data Registers (TDR)
  // --------------------------------------------------------------------------
  //
  parameter int  unsigned           KSE3_JTAG_HAW = 20;
  typedef logic [KSE3_JTAG_HAW-1:0] kse3_jtag_haddr_t;

  // TDR Struct definitions
  typedef struct packed {
    kse3_jtag_haddr_t ahb_haddr;
    soc_mgmt_hdata_t  ahb_hwdata;
    logic             ahb_hwrite;
    logic             ahb_valid;
    logic             enter_jtag_access_mode;
    logic             init_kse3_adac_itf;
  } kse3_jtag_req_t;

  typedef struct packed {
    soc_mgmt_hdata_t  ahb_hrdata;
    logic             kse_error;
    logic             ahb_error;
    logic             cmd_ignored;
  } kse3_jtag_resp_t;

  // --------------------------------------------------------------------------
  // Secure KSE3 JTAG FSM
  // --------------------------------------------------------------------------
  //
  // AHB manager MUX
  parameter int unsigned JTAG_FSM_AHB_MGR_SEL_N = 3;
  parameter int unsigned JTAG_FSM_AHB_MGR_SEL_W = 2;
  typedef enum logic[JTAG_FSM_AHB_MGR_SEL_W-1:0] {
    AHB_MGR_COMMAND_FSM_IDX    = 0,
    AHB_MGR_OTP_TO_KSE_FSM_IDX = 1,
    AHB_MGR_KSE_CMD_FSM_IDX    = 2
  } ahb_manager_sel_e;
  // OTP to KSE FSM
  parameter int unsigned OTP_TO_KSE_TR_SIZE_W = 8;
  typedef logic [OTP_TO_KSE_TR_SIZE_W-1:0] otp_to_kse_tr_size_t;
  typedef enum { OTP_TO_KSE_IDLE,OTP_TO_KSE_READ, OTP_TO_KSE_WRITE, OTP_TO_KSE_ADDR_EVAL } otp_to_kse_state_e;
  // KSE cmd FSM
  typedef enum { KSE_CMD_IDLE, KSE_CMD_POLL0, KSE_CMD_SEND, KSE_CMD_POLL1, KSE_CMD_ERR_CHECK } kse_cmd_state_e;
  // Main JTAG command FSM
  typedef enum {
    JTAG_CMD_IDLE,
    INIT_CMD_INITROT,
    INIT_DRAM_PERSO_LEN,
    INIT_DRAM_TRNG_CONFIG,
    INIT_DRAM_PERSO_STRING,
    INIT_CMD_INITCRYPTO,
    JTAG_CMD_FULLY_OPEN,
    JTAG_CMD_KEEP_CLOSED,
    INIT_ADAC_DRAM_CA_TYPE_ID,
    INIT_ADAC_DRAM_CA_ANCHOR_LEN,
    INIT_ADAC_DRAM_CA_ANCHOR_VAL,
    INIT_ADAC_CMD_SETOBJECT,
    INIT_ADAC_DRAM_SOC_ID,
    INIT_ADAC_DRAM_SOC_ID_INV,
    INIT_ADAC_DRAM_DBG_CNT,
    INIT_ADAC_DRAM_DBG_CNT_INV,
    INIT_ADAC_DRAM_SOC_CLASS,
    INIT_ADAC_CMD_SETSOCCONFIG,
    JTAG_CMD_ADAC_ONLY,
    JTAG_CMD_ERROR_REPORT,
    JTAG_CMD_ERROR
  } jtag_cmd_state_e;

  parameter soc_mgmt_haddr_t OTP_PERSO_STR_LEN_ADDR        = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_PERSO_STR_LEN_OFFSET;
  parameter soc_mgmt_haddr_t OTP_TRNG_CFG_ADDR             = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_TRNG_CFG_OFFSET;
  parameter soc_mgmt_haddr_t OTP_ANCHOR_VAL_LEN_ADDR       = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_ANCHOR_VAL_LEN_OFFSET;
  parameter soc_mgmt_haddr_t OTP_PERSO_STR_VAL_ADDR        = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_PERSO_STR_VAL_OFFSET;
  parameter soc_mgmt_haddr_t OTP_CA1_ANCHOR_VAL_ADDR       = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_CA1_ANCHOR_VAL_OFFSET;
  parameter soc_mgmt_haddr_t OTP_CA2_ANCHOR_VAL_ADDR       = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_CA2_ANCHOR_VAL_OFFSET;
  parameter soc_mgmt_haddr_t OTP_CHIP_ID_ADDR              = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_CHIP_ID_OFFSET;
  parameter soc_mgmt_haddr_t OTP_DBG_COUNTER_ADDR          = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_DBG_COUNTER_OFFSET;
  parameter soc_mgmt_haddr_t OTP_SOC_CLASS_ADDR            = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_SOC_CLASS_OFFSET;

  parameter soc_mgmt_haddr_t KSE3_DRAM_PERSO_STR_LEN_ADDR  = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_PERSO_STR_LEN_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_DRAM_TRNG_CFG_ADDR       = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_TRNG_CFG_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_DRAM_ANCHOR_VAL_LEN_ADDR = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_ANCHOR_VAL_LEN_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_DRAM_PERSO_STR_VAL_ADDR  = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_PERSO_STR_VAL_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_DRAM_SET_OBJ_TYPEID_ADDR = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_SET_OBJ_TYPEID_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_DRAM_SOC_ID_ADDR         = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_SOC_ID_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_DRAM_SOC_ID_INV_ADDR     = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_SOC_ID_INV_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_DRAM_DBG_COUNTER_ADDR    = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_DBG_COUNTER_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_DRAM_DBG_COUNTER_INV_ADDR= aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_DBG_COUNTER_INV_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_DRAM_SOC_CLASS_ADDR      = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_DRAM_SOC_CLASS_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_CMD_CTRL_ADDR            = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_CMD_CTRL_OFFSET;
  parameter soc_mgmt_haddr_t KSE3_CMD_STATUS_ADDR          = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR + kudelski_kse3_pkg::KSE3_CMD_STATUS_OFFSET;

  parameter kse3_jtag_haddr_t OTP_ST_ADDR      = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR  [KSE3_JTAG_HAW-1:0];
  parameter kse3_jtag_haddr_t AOR_ST_ADDR      = aipu_addr_map_pkg::SOC_MGMT_ROT_AO_ST_ADDR    [KSE3_JTAG_HAW-1:0];
  parameter int unsigned      OTP_ADDR_SPACE_W = 16;
  parameter int unsigned      AOR_ADDR_SPACE_W = 16;

endpackage
