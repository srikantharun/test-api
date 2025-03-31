// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>


/// Package for AIC Infra
///
package aic_infra_pkg;
  //////////////////////////////////
  // Convert cid to CVA6V hart_id //
  //////////////////////////////////
  function automatic aic_cva6v_pkg::aic_cva6v_xwidth_t cid_to_hart_id(
    logic [aic_common_pkg::AIC_CID_WIDTH-1:0] cid
  );
    // See: https://git.axelera.ai/prod/europa/-/issues/1174
    // Put here more complex mapping if needed.
    return aic_cva6v_pkg::aic_cva6v_xwidth_t'(cid + 4'd5);
  endfunction

  /////////////////////////////////////
  // Number of SRAM impl connections //
  /////////////////////////////////////
  parameter int unsigned NUM_SRAM_IMPL = 7;
  parameter int unsigned SramImplIndexWidth = cc_math_pkg::index_width(NUM_SRAM_IMPL);
  typedef logic [SramImplIndexWidth-1:0] sram_impl_index_t;
  typedef enum logic [SramImplIndexWidth-1:0] {
    SRAM_IMPL_IDX_CVA6V            = sram_impl_index_t'(0),
    SRAM_IMPL_IDX_SPM              = sram_impl_index_t'(1),
    SRAM_IMPL_IDX_HT_AIC_DMA       = sram_impl_index_t'(2),
    SRAM_IMPL_IDX_LT_AIC_DMA       = sram_impl_index_t'(3),
    SRAM_IMPL_IDX_TIMESTAMP_LOGGER = sram_impl_index_t'(4),
    SRAM_IMPL_IDX_AIC_CD_INSTR     = sram_impl_index_t'(5),
    SRAM_IMPL_IDX_AIC_CD_COPY      = sram_impl_index_t'(6)
  } sram_impl_index_e;

  ////////////////////////////////////////////////////////////////////
  // Observability enum definition, synced with CSR data definition //
  ////////////////////////////////////////////////////////////////////
  // Note: This needs to be held manualöly in sync with `OBS_CTRL` definition in aic_csr.hjson!
  parameter int unsigned ObsMuxCtrlWidth = 3;
  typedef logic [ObsMuxCtrlWidth-1:0] obs_mux_ctrl_t;
  typedef enum obs_mux_ctrl_t {
    OBS_SW          = obs_mux_ctrl_t'(0),
    OBS_IDLE        = obs_mux_ctrl_t'(1),
    OBS_BUSY        = obs_mux_ctrl_t'(2),
    OBS_ACTIVITY    = obs_mux_ctrl_t'(3),
    OBS_THROTTLE    = obs_mux_ctrl_t'(4)
  } obs_mux_ctrl_e;

  ////////////////////////////////////////////////////////
  // AIC_CD Enumeration with the destination ID mapping //
  ////////////////////////////////////////////////////////
  typedef enum aic_cd_pkg::destination_id_t {
    AIC_CD_IDX_M_IDF_0   = aic_cd_pkg::destination_id_t'(0),
    AIC_CD_IDX_M_IDF_1   = aic_cd_pkg::destination_id_t'(1),
    AIC_CD_IDX_M_IDF_2   = aic_cd_pkg::destination_id_t'(2),
    AIC_CD_IDX_M_IDF_W   = aic_cd_pkg::destination_id_t'(3),
    AIC_CD_IDX_M_ODR     = aic_cd_pkg::destination_id_t'(4),
    AIC_CD_IDX_D_IDF_0   = aic_cd_pkg::destination_id_t'(5),
    AIC_CD_IDX_D_IDF_1   = aic_cd_pkg::destination_id_t'(6),
    AIC_CD_IDX_D_ODR     = aic_cd_pkg::destination_id_t'(7),
    AIC_CD_IDX_M_MVM_EXE = aic_cd_pkg::destination_id_t'(8),
    AIC_CD_IDX_M_MVM_PRG = aic_cd_pkg::destination_id_t'(9),
    AIC_CD_IDX_M_IAU     = aic_cd_pkg::destination_id_t'(10),
    AIC_CD_IDX_M_DPU     = aic_cd_pkg::destination_id_t'(11),
    AIC_CD_IDX_D_DWPU    = aic_cd_pkg::destination_id_t'(12),
    AIC_CD_IDX_D_IAU     = aic_cd_pkg::destination_id_t'(13),
    AIC_CD_IDX_D_DPU     = aic_cd_pkg::destination_id_t'(14),
    AIC_CD_IDX_DMA_0     = aic_cd_pkg::destination_id_t'(15),
    AIC_CD_IDX_DMA_1     = aic_cd_pkg::destination_id_t'(16)
  } destination_id_e;

  ////////////////////////////////////////////////////////////////////
  // Mapping from interrupt source to index in interrupt controller //
  ////////////////////////////////////////////////////////////////////
  parameter int unsigned IrqIndexWidth = cc_math_pkg::index_width(aic_rv_plic_reg_pkg::NumSrc);
  typedef logic [IrqIndexWidth-1:0] irq_index_t;
  typedef enum irq_index_t {
    IRQ_IDX_MID_MVM          = irq_index_t'( 0),
    IRQ_IDX_MID_IAU          = irq_index_t'( 1),
    IRQ_IDX_MID_DPU          = irq_index_t'( 2),

    IRQ_IDX_DID_DWPU         = irq_index_t'( 3),
    IRQ_IDX_DID_IAU          = irq_index_t'( 4),
    IRQ_IDX_DID_DPU          = irq_index_t'( 5),

    IRQ_IDX_M_IFD_0          = irq_index_t'( 6),
    IRQ_IDX_M_IFD_1          = irq_index_t'( 7),
    IRQ_IDX_M_IFD_2          = irq_index_t'( 8),
    IRQ_IDX_M_IFDW           = irq_index_t'( 9),
    IRQ_IDX_D_IFD_0          = irq_index_t'(10),
    IRQ_IDX_D_IFD_1          = irq_index_t'(11),

    IRQ_IDX_M_ODR            = irq_index_t'(12),
    IRQ_IDX_D_ODR            = irq_index_t'(13),

    IRQ_IDX_TOKEN_MGR        = irq_index_t'(14),

    IRQ_IDX_DMA_LT_COMMON    = irq_index_t'(15),
    IRQ_IDX_DMA_LT_CHANNEL_0 = irq_index_t'(16),

    IRQ_IDX_DMA_HT_CHANNEL_0 = irq_index_t'(17),
    IRQ_IDX_DMA_HT_CHANNEL_1 = irq_index_t'(18),

    IRQ_IDX_THERMAL_WARNING  = irq_index_t'(19),

    IRQ_IDX_MAILBOX          = irq_index_t'(20),

    IRQ_IDX_AIC_CD           = irq_index_t'(21),

    IRQ_IDX_SPM              = irq_index_t'(22),

    IRQ_IDX_MID_GEN          = irq_index_t'(23),
    IRQ_IDX_MID_TU_WRN       = irq_index_t'(24),
    IRQ_IDX_MID_TU_CRIT      = irq_index_t'(25)
  } irq_index_e;

  /////////////
  // Mailbox //
  /////////////
  parameter int unsigned MailboxDepth = 8;

  ///////////////////
  // Token Manager //
  ///////////////////
  parameter int unsigned TokenManagerCounterWidth = 8;

  //////////////////////////////////////////
  // Address Translation Unit Definitions //
  //////////////////////////////////////////
  typedef logic [(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-aic_csr_reg_pkg::LT_DMA_ATU_PO_SIZE)-1:0] lt_atu_entry_addr_t;
  typedef logic [(aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-aic_csr_reg_pkg::TIMELOG_ATU_PO_SIZE)-1:0] timelog_atu_entry_addr_t;

  typedef struct packed {
    // First page number of the input range of the tlb entry
    lt_atu_entry_addr_t first;
    // Last page number of the input range of the tlb entry
    lt_atu_entry_addr_t last;
    // Number of output base page of the tlb entry
    lt_atu_entry_addr_t base;
    // "Whether tlb entry is valid and should be mapped
    logic               valid;
    // Whether tlb entry maps to a read-only range
    logic               read_only;
  } lt_atu_entry_t;

  typedef struct packed {
    // First page number of the input range of the tlb entry
    lt_atu_entry_addr_t first;
    // Last page number of the input range of the tlb entry
    lt_atu_entry_addr_t last;
    // Number of output base page of the tlb entry
    lt_atu_entry_addr_t base;
    // "Whether tlb entry is valid and should be mapped
    logic               valid;
    // Whether tlb entry maps to a read-only range
    logic               read_only;
  } timelog_atu_entry_t;

  ////////////////////////////
  // AXI Fabric Definitions //
  ////////////////////////////

  parameter int unsigned AxiMaxReadTxns  = 8; // TODO: Can we optimize this?
  parameter int unsigned AxiMaxWriteTxns = 8; // TODO: Can we optimize this?
  parameter int unsigned AxiMaxTxns      = (AxiMaxReadTxns > AxiMaxWriteTxns) ? AxiMaxReadTxns : AxiMaxWriteTxns;

  /// The ID width increase from the AXI Crossbars between Subordinate and Manager Ports
  parameter int unsigned AxiConfigXbarWidthIncrease  = 1;
  parameter int unsigned AxiControlXbarWidthIncrease = 1;

  parameter int unsigned AIC_INFRA_CONFIG_AXI_S_IDW  = aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH + AxiConfigXbarWidthIncrease;
  parameter int unsigned AIC_INFRA_CONTROL_AXI_S_IDW = AIC_INFRA_CONFIG_AXI_S_IDW            + AxiControlXbarWidthIncrease;
  parameter int unsigned AIC_INFRA_ACD_AXI_S_IDW = aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH;


  typedef logic [AIC_INFRA_CONFIG_AXI_S_IDW -1:0] axi_lt_config_s_id_t;
  typedef logic [AIC_INFRA_CONTROL_AXI_S_IDW-1:0] axi_lt_control_s_id_t;
  typedef logic [AIC_INFRA_ACD_AXI_S_IDW-1:0] axi_lt_acd_s_id_t;

  // config
  typedef struct packed {
    aic_common_pkg::aic_lt_axi_m_id_t id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
    axi_pkg::axi_atop_t               atop; // Not used, some axi infrastructure IPs access this
                                            // Configuration does not use it, however SV demands that this is defined anyways....
  } axi_lt_config_m_aw_t;

  typedef struct packed {
    axi_lt_config_s_id_t              id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
  } axi_lt_config_s_aw_t;

  typedef struct packed {
    aic_common_pkg::aic_lt_axi_m_id_t id;
    axi_pkg::axi_resp_t               resp;
  } axi_lt_config_m_b_t;

  typedef struct packed {
    axi_lt_config_s_id_t              id;
    axi_pkg::axi_resp_t               resp;
  } axi_lt_config_s_b_t;

  typedef struct packed {
    aic_common_pkg::aic_lt_axi_m_id_t id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
  } axi_lt_config_m_ar_t;

  typedef struct packed {
    axi_lt_config_s_id_t              id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
  } axi_lt_config_s_ar_t;

  typedef struct packed {
    aic_common_pkg::aic_lt_axi_m_id_t id;
    aic_common_pkg::aic_lt_axi_data_t data;
    axi_pkg::axi_resp_t               resp;
    logic                             last;
  } axi_lt_config_m_r_t;

  typedef struct packed {
    axi_lt_config_s_id_t              id;
    aic_common_pkg::aic_lt_axi_data_t data;
    axi_pkg::axi_resp_t               resp;
    logic                             last;
  } axi_lt_config_s_r_t;


  // ht
  typedef struct packed {
    aic_common_pkg::aic_ht_axi_m_id_t id;
    aic_common_pkg::aic_ht_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
    axi_pkg::axi_atop_t               atop; // Not used, some axi infrastructure IPs access this
                                            // Configuration does not use it, however SV demands that this is defined anyways....
  } axi_ht_m_aw_t;

  typedef struct packed {
    aic_common_pkg::aic_ht_axi_data_t data;
    aic_common_pkg::aic_ht_axi_strb_t strb;
    logic                             last;
  } axi_ht_w_t;

  typedef struct packed {
    aic_common_pkg::aic_ht_axi_m_id_t id;
    axi_pkg::axi_resp_t               resp;
  } axi_ht_m_b_t;

  typedef struct packed {
    aic_common_pkg::aic_ht_axi_m_id_t id;
    aic_common_pkg::aic_ht_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
  } axi_ht_m_ar_t;

  typedef struct packed {
    aic_common_pkg::aic_ht_axi_m_id_t id;
    aic_common_pkg::aic_ht_axi_data_t data;
    axi_pkg::axi_resp_t               resp;
    logic                             last;
  } axi_ht_m_r_t;

  // lt
  typedef struct packed {
    aic_common_pkg::aic_lt_axi_s_id_t id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
  } axi_lt_s_aw_t;

  typedef struct packed {
    aic_common_pkg::aic_lt_axi_data_t data;
    aic_common_pkg::aic_lt_axi_strb_t strb;
    logic                             last;
  } axi_lt_w_t;

  typedef struct packed {
    aic_common_pkg::aic_lt_axi_s_id_t id;
    axi_pkg::axi_resp_t               resp;
  } axi_lt_s_b_t;

  typedef struct packed {
    aic_common_pkg::aic_lt_axi_s_id_t id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
  } axi_lt_s_ar_t;

  typedef struct packed {
    aic_common_pkg::aic_lt_axi_s_id_t id;
    aic_common_pkg::aic_lt_axi_data_t data;
    axi_pkg::axi_resp_t               resp;
    logic                             last;
  } axi_lt_s_r_t;

  // control
  typedef struct packed {
    axi_lt_control_s_id_t             id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
    axi_pkg::axi_atop_t               atop; // Not used, some axi infrastructure IPs access this
                                            // Configuration does not use it, however SV demands that this is defined anyways....
  } axi_lt_control_s_aw_t;

  typedef struct packed {
    axi_lt_control_s_id_t             id;
    axi_pkg::axi_resp_t               resp;
  } axi_lt_control_s_b_t;

  typedef struct packed {
    axi_lt_control_s_id_t             id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
  } axi_lt_control_s_ar_t;

  typedef struct packed {
    axi_lt_control_s_id_t             id;
    aic_common_pkg::aic_lt_axi_data_t data;
    axi_pkg::axi_resp_t               resp;
    logic                             last;
  } axi_lt_control_s_r_t;

  // acd
  typedef struct packed {
    axi_lt_acd_s_id_t                 id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
  } axi_lt_acd_s_aw_t;

  typedef struct packed {
    axi_lt_acd_s_id_t                 id;
    axi_pkg::axi_resp_t               resp;
  } axi_lt_acd_s_b_t;

  typedef struct packed {
    axi_lt_acd_s_id_t                 id;
    aic_common_pkg::aic_lt_axi_addr_t addr;
    axi_pkg::axi_len_t                len;
    axi_pkg::axi_size_t               size;
    axi_pkg::axi_burst_t              burst;
    logic                             lock;
    axi_pkg::axi_cache_t              cache;
    axi_pkg::axi_prot_t               prot;
  } axi_lt_acd_s_ar_t;

  typedef struct packed {
    axi_lt_acd_s_id_t                 id;
    aic_common_pkg::aic_lt_axi_data_t data;
    axi_pkg::axi_resp_t               resp;
    logic                             last;
  } axi_lt_acd_s_r_t;

  // HT DMA param:
  parameter int AIC_HT_DMA_NUM_PORTS = 2;
  parameter int AIC_HT_DMA_NUM_CHNLS = 2;

    // HP DMA endpoints:
  parameter int unsigned AIC_HT_DMA_NUM_REGIONS = 1 + 3*AIC_HT_DMA_NUM_CHNLS;
  typedef enum int {
    common_csr_idx       = dma_pkg::common_csr_idx,
    ch0_mmu_base_idx     = dma_pkg::mmu_base_idx     + 3*0,
    ch0_ch_cmdb_base_idx = dma_pkg::ch_cmdb_base_idx + 3*0,
    ch0_ch_csr_base_idx  = dma_pkg::ch_csr_base_idx  + 3*0,
    ch1_mmu_base_idx     = dma_pkg::mmu_base_idx     + 3*1,
    ch1_ch_cmdb_base_idx = dma_pkg::ch_cmdb_base_idx + 3*1,
    ch1_ch_csr_base_idx  = dma_pkg::ch_csr_base_idx  + 3*1
  } dma_ep_idx;
  parameter longint AIC_LOC_HP_DMA_REGION_ST_ADDR[AIC_HT_DMA_NUM_REGIONS] = '{
    0 /*common_csr_idx*/       : aic_addr_map_pkg::AIC_LOC_HP_DMA_COMMON_CSR_ST_ADDR,
    1 /*ch0_mmu_base_idx*/     : aic_addr_map_pkg::AIC_LOC_HP_DMA_MMU_CSR_ST_ADDR + 0*dma_pkg::DmaMmuCsrOffset, // MMU CSR lie in the same region
    2 /*ch0_ch_cmdb_base_idx*/ : aic_addr_map_pkg::AIC_LOC_HP_DMA_0_CMD_ST_ADDR,
    3 /*ch0_ch_csr_base_idx*/  : aic_addr_map_pkg::AIC_LOC_HP_DMA_0_CSR_ST_ADDR,
    4 /*ch1_mmu_base_idx*/     : aic_addr_map_pkg::AIC_LOC_HP_DMA_MMU_CSR_ST_ADDR + 1*dma_pkg::DmaMmuCsrOffset,
    5 /*ch1_ch_cmdb_base_idx*/ : aic_addr_map_pkg::AIC_LOC_HP_DMA_1_CMD_ST_ADDR,
    6 /*ch1_ch_csr_base_idx*/  : aic_addr_map_pkg::AIC_LOC_HP_DMA_1_CSR_ST_ADDR
  };
  parameter longint AIC_LOC_HP_DMA_REGION_END_ADDR[AIC_HT_DMA_NUM_REGIONS] = '{
    0 /*common_csr_idx*/       : aic_addr_map_pkg::AIC_LOC_HP_DMA_COMMON_CSR_END_ADDR,
    1 /*ch0_mmu_base_idx*/     : aic_addr_map_pkg::AIC_LOC_HP_DMA_MMU_CSR_ST_ADDR + 0*dma_pkg::DmaMmuCsrOffset + 'hfff, // MMU CSR lie in the same region
    2 /*ch0_ch_cmdb_base_idx*/ : aic_addr_map_pkg::AIC_LOC_HP_DMA_0_CMD_END_ADDR,
    3 /*ch0_ch_csr_base_idx*/  : aic_addr_map_pkg::AIC_LOC_HP_DMA_0_CSR_END_ADDR,
    4 /*ch1_mmu_base_idx*/     : aic_addr_map_pkg::AIC_LOC_HP_DMA_MMU_CSR_ST_ADDR + 1*dma_pkg::DmaMmuCsrOffset + 'hfff,
    5 /*ch1_ch_cmdb_base_idx*/ : aic_addr_map_pkg::AIC_LOC_HP_DMA_1_CMD_END_ADDR,
    6 /*ch1_ch_csr_base_idx*/  : aic_addr_map_pkg::AIC_LOC_HP_DMA_1_CSR_END_ADDR
  };

  //////////////////////////////////////////////
  // Generic Performance Counters Definitions //
  //////////////////////////////////////////////

  parameter int unsigned AIC_INFRA_PERF_CNT_NUM   = 16;
  parameter int unsigned AIC_INFRA_PERF_CNT_WIDTH = 32;
  parameter int unsigned AIC_INFRA_PERF_CNT_MODE  = 4;

endpackage
