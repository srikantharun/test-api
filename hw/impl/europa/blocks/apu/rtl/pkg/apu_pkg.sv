// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Abhishek Maringanti <abhishek.maringanti@axelera.ai>


/// Description: Package file containing top level parameter definitions for the APU Subsystem
///
package apu_pkg;
  /// LT AXI Manager parameters
  parameter int unsigned APU_XBAR_LT_S_PORTS = 3;
  parameter int unsigned APU_XBAR_LT_M_PORTS = 11;

  /// AXI ID Width
  parameter int unsigned APU_AXI_LT_M_ID_W = 8;
  typedef logic [APU_AXI_LT_M_ID_W-1:0] apu_axi_lt_m_id_t;

  /// LT AXI Subordinate parameters
  /// AXI ID Width
  parameter int unsigned AX65_AXI_LT_S_ID_W = 13;
  typedef logic [AX65_AXI_LT_S_ID_W-1:0] ax65_axi_lt_s_id_t;

  parameter int unsigned APU_AXI_LT_S_ID_W = APU_AXI_LT_M_ID_W + unsigned'($clog2(APU_XBAR_LT_S_PORTS));
  typedef logic [APU_AXI_LT_S_ID_W-1:0] apu_axi_lt_s_id_t;

  /// AX65 LT AXI Data Width
  parameter int unsigned AX65_AXI_LT_DATA_W = 256;
  typedef logic [AX65_AXI_LT_DATA_W-1:0] ax65_axi_lt_data_t;
  /// AX65 LT AXI Data Strobe Width
  parameter int unsigned AX65_AXI_LT_STRB_W = AX65_AXI_LT_DATA_W / 8;
  typedef logic [AX65_AXI_LT_STRB_W-1:0] ax65_axi_lt_wstrb_t;

  /// MT AXI Manager parameters
  parameter int unsigned APU_MUX_MT_NB_PORTS = 2;

  /// AXI ID Width
  parameter int unsigned AX65_AXI_MT_M_ID_W = 8;
  typedef logic [AX65_AXI_MT_M_ID_W-1:0] ax65_axi_mt_m_id_t;

  parameter int unsigned APU_AXI_MT_M_ID_W = AX65_AXI_MT_M_ID_W + 1;
  typedef logic [APU_AXI_MT_M_ID_W-1:0] apu_axi_mt_m_id_t;

  /// MT AXI Data Width
  parameter int unsigned APU_AXI_MT_DATA_W = 256;
  typedef logic [APU_AXI_MT_DATA_W-1:0] apu_axi_mt_data_t;
  /// MT AXI Data Strobe Width
  parameter int unsigned APU_AXI_MT_STRB_W = APU_AXI_MT_DATA_W / 8;
  typedef logic [APU_AXI_MT_STRB_W-1:0] apu_axi_mt_wstrb_t;

  parameter int unsigned APU_HART_ID_OFFSET = 0;

  // AX65 parameters
  parameter int unsigned CORE_WIDTH = 6;
  parameter int unsigned AX65_L2C_BANK_WIDTH = 4;
  parameter int unsigned AX65_L2C_BANK_DATA_WIDTH = 8;
  parameter int unsigned AX65_L2C_BANK_TAG_WIDTH = 64;
  parameter int unsigned AX65_SINK_WIDTH = 6;
  parameter int unsigned AX65_BHT_WIDTH = 7;
  parameter int unsigned AX65_DCACHE_WIDTH = 16;
  parameter int unsigned AX65_ICACHE_WIDTH = 8;
  parameter int unsigned AX65_L2_WIDTH = 4;
  parameter int unsigned AX65_SOURCE_WIDTH = 5;
  parameter int unsigned AX65_MAX_CORE_WIDTH = 8;
  parameter int unsigned AX65_CTRL_IN_WIDTH = $bits(axe_tcl_sram_pkg::impl_inp_t);
  parameter int unsigned AX65_CTRL_OUT_WIDTH = $bits(axe_tcl_sram_pkg::impl_oup_t);

  parameter int unsigned APU_FAST_CLK_WIDTH = 2 + CORE_WIDTH;

  // Interrupt parameters
  parameter int unsigned APU_SW_INTERRUPT_WIDTH = 256;

  parameter int unsigned APU_INTERRUPT_MAX_PRIORITY = 15;
  parameter int unsigned APU_SW_INTERRUPT_MAX_PRIORITY = 15;

  // TODO(@vincent.morillon) recover value from top in some ways
  parameter int unsigned APU_AIC_WIDTH = 8;

  // Mailbox parameters
  parameter int unsigned APU_MAILBOX_DEPTH = 8;

  // Fabric global parameters
  parameter int unsigned APU_FABRIC_IDLE_DELAY_WIDTH = 8; // keep in sync with AO CSR
  parameter bit APU_SUPPORT_ATOPS = 0;

  // Mux MT parameters
  parameter int unsigned APU_MUX_MT_PORT_IDX_W = cc_math_pkg::index_width(APU_MUX_MT_NB_PORTS);
  typedef bit [APU_MUX_MT_PORT_IDX_W - 1:0] apu_mux_mt_port_idx_t;

  parameter apu_mux_mt_port_idx_t APU_MUX_MT_PORT_IDX_AX65 = apu_mux_mt_port_idx_t'(0);
  parameter apu_mux_mt_port_idx_t APU_MUX_MT_PORT_IDX_DMA  = apu_mux_mt_port_idx_t'(1);

  // Xbar LT parameters
  parameter int unsigned APU_XBAR_LT_S_PORT_IDX_W = cc_math_pkg::index_width(APU_XBAR_LT_S_PORTS);
  typedef bit [APU_XBAR_LT_S_PORT_IDX_W - 1:0] apu_xbar_lt_s_port_idx_t;
  parameter int unsigned APU_XBAR_LT_M_PORT_IDX_W = cc_math_pkg::index_width(APU_XBAR_LT_M_PORTS);
  typedef bit [APU_XBAR_LT_M_PORT_IDX_W - 1:0] apu_xbar_lt_m_port_idx_t;

  parameter apu_xbar_lt_s_port_idx_t APU_XBAR_LT_S_PORT_IDX_AX65  = apu_xbar_lt_s_port_idx_t'(0);
  parameter apu_xbar_lt_s_port_idx_t APU_XBAR_LT_S_PORT_IDX_TRACE = apu_xbar_lt_s_port_idx_t'(1);
  parameter apu_xbar_lt_s_port_idx_t APU_XBAR_LT_S_PORT_IDX_EXT   = apu_xbar_lt_s_port_idx_t'(2);

  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_AX65   = apu_xbar_lt_m_port_idx_t'(0);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_BOOT   = apu_xbar_lt_m_port_idx_t'(1);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_CSRS   = apu_xbar_lt_m_port_idx_t'(2);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_DMA    = apu_xbar_lt_m_port_idx_t'(3);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_MAIL   = apu_xbar_lt_m_port_idx_t'(4);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_PLIC   = apu_xbar_lt_m_port_idx_t'(5);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_SWPLIC = apu_xbar_lt_m_port_idx_t'(6);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_TOKEN  = apu_xbar_lt_m_port_idx_t'(7);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_TRACE  = apu_xbar_lt_m_port_idx_t'(8);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_ERR    = apu_xbar_lt_m_port_idx_t'(9);
  parameter apu_xbar_lt_m_port_idx_t APU_XBAR_LT_M_PORT_IDX_EXT    = apu_xbar_lt_m_port_idx_t'(10);

  parameter bit [APU_XBAR_LT_S_PORTS - 1:0][APU_XBAR_LT_M_PORTS - 1:0] APU_XBAR_LT_CONNECTIVITY = {
    11'b011_1111_1111,
    11'b110_0000_0000,
    11'b111_1111_1110
  };

  typedef struct packed {
    apu_xbar_lt_m_port_idx_t  index;
    chip_pkg::chip_axi_addr_t addr_start;
    chip_pkg::chip_axi_addr_t addr_end;
  } apu_xbar_lt_rule_t;

  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_BOOT = '{
    index:      APU_XBAR_LT_M_PORT_IDX_BOOT,
    addr_start: aipu_addr_map_pkg::APU_BOOTROM_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_BOOTROM_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_CSRS = '{
    index:      APU_XBAR_LT_M_PORT_IDX_CSRS,
    addr_start: aipu_addr_map_pkg::APU_CSRS_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_CSRS_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_DMA = '{
    index:      APU_XBAR_LT_M_PORT_IDX_DMA,
    addr_start: aipu_addr_map_pkg::APU_DMA_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_DMA_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_MAIL = '{
    index:      APU_XBAR_LT_M_PORT_IDX_MAIL,
    addr_start: aipu_addr_map_pkg::APU_MAILBOX_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_MAILBOX_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_PLMT = '{
    index:      APU_XBAR_LT_M_PORT_IDX_AX65,
    addr_start: aipu_addr_map_pkg::APU_PLMT_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_PLMT_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_L2C_REGISTER = '{
    index:      APU_XBAR_LT_M_PORT_IDX_AX65,
    addr_start: aipu_addr_map_pkg::APU_AX65_L2C_REGISTER_BASE_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_AX65_L2C_REGISTER_BASE_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_PLIC = '{
    index:      APU_XBAR_LT_M_PORT_IDX_PLIC,
    addr_start: aipu_addr_map_pkg::APU_PLIC_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_PLIC_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_SWPLIC = '{
    index:      APU_XBAR_LT_M_PORT_IDX_SWPLIC,
    addr_start: aipu_addr_map_pkg::APU_SW_PLIC_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_SW_PLIC_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_TOKEN = '{
    index:      APU_XBAR_LT_M_PORT_IDX_TOKEN,
    addr_start: aipu_addr_map_pkg::APU_TOKEN_MANAGER_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_TOKEN_MANAGER_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_ERR = '{
    index:      APU_XBAR_LT_M_PORT_IDX_ERR,
    addr_start: aipu_addr_map_pkg::APU_ST_ADDR,
    addr_end:   aipu_addr_map_pkg::APU_END_ADDR
  };
  parameter apu_xbar_lt_rule_t APU_XBAR_LT_RULE_EXT = '{
    index:      APU_XBAR_LT_M_PORT_IDX_EXT,
    addr_start: '0,
    addr_end:   '1
  };

  parameter int unsigned APU_XBAR_LT_NB_ADDR_RULES = 11;

  // ATU LT parameters
  parameter int unsigned APU_ATU_NUM_ENTRIES [APU_XBAR_LT_M_PORTS] = {
    0,1,1,1,1,1,1,1,1,0,0
  };
  parameter int unsigned APU_ATU_MAX_NUM_ENTRIES = 1;
  parameter int unsigned APU_ATU_PAGE_OFFSET_W = 12;

  typedef logic [(chip_pkg::CHIP_AXI_ADDR_W-APU_ATU_PAGE_OFFSET_W)-1:0] apu_atu_entry_addr_t;

  typedef struct packed {
    apu_atu_entry_addr_t first;
    apu_atu_entry_addr_t last;
    apu_atu_entry_addr_t base;
    logic                valid;
    logic                read_only;
  } apu_atu_entry_t;

  parameter apu_atu_entry_t APU_ATU_ENTRY_BOOT = '{
    first: aipu_addr_map_pkg::APU_BOOTROM_ST_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    last:  aipu_addr_map_pkg::APU_BOOTROM_END_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    base:  apu_atu_entry_addr_t'(0),
    valid: 1'b1,
    read_only: 1'b1
  };
  parameter apu_atu_entry_t APU_ATU_ENTRY_CSRS = '{
    first: aipu_addr_map_pkg::APU_CSRS_ST_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    last:  aipu_addr_map_pkg::APU_CSRS_END_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    base:  apu_atu_entry_addr_t'(0),
    valid: 1'b1,
    read_only: 1'b0
  };
  parameter apu_atu_entry_t APU_ATU_ENTRY_DMA = '{
    first: aipu_addr_map_pkg::APU_DMA_ST_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    last:  aipu_addr_map_pkg::APU_DMA_END_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    base:  apu_atu_entry_addr_t'(0),
    valid: 1'b1,
    read_only: 1'b0
  };
  parameter apu_atu_entry_t APU_ATU_ENTRY_MAIL = '{
    first: aipu_addr_map_pkg::APU_MAILBOX_ST_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    last:  aipu_addr_map_pkg::APU_MAILBOX_END_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    base:  apu_atu_entry_addr_t'(0),
    valid: 1'b1,
    read_only: 1'b0
  };
  parameter apu_atu_entry_t APU_ATU_ENTRY_PLIC = '{
    first: aipu_addr_map_pkg::APU_PLIC_ST_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    last:  aipu_addr_map_pkg::APU_PLIC_END_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    base:  apu_atu_entry_addr_t'(0),
    valid: 1'b1,
    read_only: 1'b0
  };
  parameter apu_atu_entry_t APU_ATU_ENTRY_SWPLIC = '{
    first: aipu_addr_map_pkg::APU_SW_PLIC_ST_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    last:  aipu_addr_map_pkg::APU_SW_PLIC_END_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    base:  apu_atu_entry_addr_t'(0),
    valid: 1'b1,
    read_only: 1'b0
  };
  parameter apu_atu_entry_t APU_ATU_ENTRY_TOKEN = '{
    first: aipu_addr_map_pkg::APU_TOKEN_MANAGER_ST_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    last:  aipu_addr_map_pkg::APU_TOKEN_MANAGER_END_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
    base:  apu_atu_entry_addr_t'(0),
    valid: 1'b1,
    read_only: 1'b0
  };
  // parameter apu_atu_entry_t APU_ATU_ENTRY_TRACE = '{
  //   first: aipu_addr_map_pkg::APU_TRACE_IP_ST_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
  //   last:  aipu_addr_map_pkg::APU_TRACE_IP_END_ADDR[chip_pkg::CHIP_AXI_ADDR_W-1:APU_ATU_PAGE_OFFSET_W],
  //   base:  apu_atu_entry_addr_t'(0),
  //   valid: 1'b1,
  //   read_only: 1'b0
  // };

  // AXI structs and typedef
  // LT IOCP
  typedef struct packed {
    ax65_axi_lt_s_id_t             id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    axi_pkg::axi_cache_t           cache;
    logic                          lock;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    axi_pkg::axi_atop_t            atop;
    chip_pkg::chip_axi_lt_awuser_t user;
  } ax65_axi_lt_s_aw_t;

  typedef struct packed {
    apu_axi_lt_s_id_t              id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    axi_pkg::axi_cache_t           cache;
    logic                          lock;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    axi_pkg::axi_atop_t            atop;
    chip_pkg::chip_axi_lt_awuser_t user;
  } apu_axi_lt_s_aw_t;

  typedef struct packed {
    ax65_axi_lt_data_t            data;
    ax65_axi_lt_wstrb_t           strb;
    logic                         last;
    chip_pkg::chip_axi_lt_wuser_t user;
  } ax65_axi_lt_w_t;

  typedef struct packed {
    chip_pkg::chip_axi_lt_data_t  data;
    chip_pkg::chip_axi_lt_wstrb_t strb;
    logic                         last;
    chip_pkg::chip_axi_lt_wuser_t user;
  } apu_axi_lt_w_t;

  typedef struct packed {
    ax65_axi_lt_s_id_t            id;
    axi_pkg::axi_resp_e           resp;
    chip_pkg::chip_axi_lt_buser_t user;
  } ax65_axi_lt_s_b_t;

  typedef struct packed {
    apu_axi_lt_s_id_t             id;
    axi_pkg::axi_resp_e           resp;
    chip_pkg::chip_axi_lt_buser_t user;
  } apu_axi_lt_s_b_t;

  typedef struct packed {
    ax65_axi_lt_s_id_t             id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    logic                          lock;
    axi_pkg::axi_cache_t           cache;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    chip_pkg::chip_axi_lt_aruser_t user;
  } ax65_axi_lt_s_ar_t;

  typedef struct packed {
    apu_axi_lt_s_id_t              id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    logic                          lock;
    axi_pkg::axi_cache_t           cache;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    chip_pkg::chip_axi_lt_aruser_t user;
  } apu_axi_lt_s_ar_t;

  typedef struct packed {
    ax65_axi_lt_s_id_t            id;
    ax65_axi_lt_data_t            data;
    axi_pkg::axi_resp_e           resp;
    logic                         last;
    chip_pkg::chip_axi_lt_ruser_t user;
  } ax65_axi_lt_s_r_t;

  typedef struct packed {
    apu_axi_lt_s_id_t             id;
    ax65_axi_lt_data_t            data;
    axi_pkg::axi_resp_e           resp;
    logic                         last;
    chip_pkg::chip_axi_lt_ruser_t user;
  } apu_ax65_axi_lt_s_r_t;

  typedef struct packed {
    apu_axi_lt_s_id_t             id;
    chip_pkg::chip_axi_lt_data_t  data;
    axi_pkg::axi_resp_e           resp;
    logic                         last;
    chip_pkg::chip_axi_lt_ruser_t user;
  } apu_axi_lt_s_r_t;


  // LT MMIO
  typedef struct packed {
    apu_axi_lt_m_id_t              id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    axi_pkg::axi_cache_t           cache;
    logic                          lock;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    axi_pkg::axi_atop_t            atop;
    chip_pkg::chip_axi_lt_awuser_t user;
  } apu_axi_lt_m_aw_t;

  typedef struct packed {
    apu_axi_lt_m_id_t             id;
    axi_pkg::axi_resp_e           resp;
    chip_pkg::chip_axi_lt_buser_t user;
  } apu_axi_lt_m_b_t;

  typedef struct packed {
    apu_axi_lt_m_id_t              id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    logic                          lock;
    axi_pkg::axi_cache_t           cache;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    chip_pkg::chip_axi_lt_aruser_t user;
  } apu_axi_lt_m_ar_t;

  typedef struct packed {
    apu_axi_lt_m_id_t             id;
    ax65_axi_lt_data_t            data;
    axi_pkg::axi_resp_e           resp;
    logic                         last;
    chip_pkg::chip_axi_lt_ruser_t user;
  } ax65_axi_lt_m_r_t;

  typedef struct packed {
    apu_axi_lt_m_id_t             id;
    chip_pkg::chip_axi_lt_data_t  data;
    axi_pkg::axi_resp_e           resp;
    logic                         last;
    chip_pkg::chip_axi_lt_ruser_t user;
  } apu_axi_lt_m_r_t;


  // MT mux <-> (AX65 and DMA)
  typedef struct packed {
    ax65_axi_mt_m_id_t             id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    axi_pkg::axi_cache_t           cache;
    logic                          lock;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    axi_pkg::axi_atop_t            atop;
    chip_pkg::chip_axi_mt_awuser_t user;
  } ax65_axi_mt_m_aw_t;

  typedef struct packed {
    ax65_axi_mt_m_id_t            id;
    axi_pkg::axi_resp_e           resp;
    chip_pkg::chip_axi_mt_buser_t user;
  } ax65_axi_mt_m_b_t;

  typedef struct packed {
    ax65_axi_mt_m_id_t             id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    logic                          lock;
    axi_pkg::axi_cache_t           cache;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    chip_pkg::chip_axi_mt_aruser_t user;
  } ax65_axi_mt_m_ar_t;

  typedef struct packed {
    ax65_axi_mt_m_id_t            id;
    apu_axi_mt_data_t             data;
    axi_pkg::axi_resp_e           resp;
    logic                         last;
    chip_pkg::chip_axi_mt_ruser_t user;
  } ax65_axi_mt_m_r_t;

  // MT mux <-> APU
  typedef struct packed {
    apu_axi_mt_m_id_t              id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    axi_pkg::axi_cache_t           cache;
    logic                          lock;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    axi_pkg::axi_atop_t            atop;
    chip_pkg::chip_axi_mt_awuser_t user;
  } apu_axi_mt_m_aw_t;

  typedef struct packed {
    apu_axi_mt_m_id_t             id;
    axi_pkg::axi_resp_e           resp;
    chip_pkg::chip_axi_mt_buser_t user;
  } apu_axi_mt_m_b_t;

  typedef struct packed {
    apu_axi_mt_m_id_t              id;
    chip_pkg::chip_axi_addr_t      addr;
    axi_pkg::axi_len_t             len;
    axi_pkg::axi_size_e            size;
    axi_pkg::axi_burst_e           burst;
    logic                          lock;
    axi_pkg::axi_cache_t           cache;
    axi_pkg::axi_prot_t            prot;
    axi_pkg::axi_qos_t             qos;
    axi_pkg::axi_region_t          region;
    chip_pkg::chip_axi_mt_aruser_t user;
  } apu_axi_mt_m_ar_t;

  typedef struct packed {
    apu_axi_mt_m_id_t             id;
    apu_axi_mt_data_t             data;
    axi_pkg::axi_resp_e           resp;
    logic                         last;
    chip_pkg::chip_axi_mt_ruser_t user;
  } apu_axi_mt_m_r_t;

  typedef struct packed {
    apu_axi_mt_data_t             data;
    apu_axi_mt_wstrb_t            strb;
    logic                         last;
    chip_pkg::chip_axi_mt_wuser_t user;
  } apu_axi_mt_w_t;

endpackage
