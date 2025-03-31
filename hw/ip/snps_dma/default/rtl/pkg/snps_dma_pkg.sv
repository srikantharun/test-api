// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>


/// Few parameters used in the DMA. As the IP is generated with hardcoded values most can't be freely changed
///

package snps_dma_pkg;

  typedef struct {
    int unsigned axi_port_aw;
    int unsigned axi_port_dw;
    int unsigned axi_port_idw;
    int unsigned axi_port_len;

    bit          dma_external_ram;
    int unsigned dma_macro_width;
    int unsigned dma_nbr_channels;
    int unsigned dma_channel_fifo_depth;
    int unsigned dma_nbr_ports;
    bit          dma_has_uid;

    bit          cmdblock_present;
    int unsigned cmdblock_fifo_depth;
    int unsigned cmdblock_max_outst_cmds;
  } snps_dma_cfg_t;

  parameter snps_dma_cfg_t SNPS_DMA_AIC_HT_CFG = '{
    axi_port_aw: aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH,
    axi_port_dw: aic_common_pkg::AIC_HT_AXI_DATA_WIDTH,
    axi_port_idw: aic_common_pkg::AIC_HT_AXI_M_ID_WIDTH,
    axi_port_len: aic_common_pkg::AIC_HT_AXI_LEN_WIDTH,

    dma_external_ram: 1,
    dma_macro_width: 128,
    dma_nbr_channels: 2,
    dma_channel_fifo_depth: 128,
    dma_nbr_ports: 2,
    dma_has_uid: 1,

    cmdblock_present: 1,
    cmdblock_fifo_depth: aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH,
    cmdblock_max_outst_cmds: aic_common_pkg::AIC_GEN_CMDB_MAX_OUTST_CMDS
  };

  parameter snps_dma_cfg_t SNPS_DMA_AIC_LT_CFG = '{
    axi_port_aw: aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH,
    axi_port_dw: aic_common_pkg::AIC_LT_AXI_DATA_WIDTH,
    axi_port_idw: aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH,
    axi_port_len: aic_common_pkg::AIC_LT_AXI_LEN_WIDTH,

    dma_external_ram: 1,
    dma_macro_width: 64,
    dma_nbr_channels: 1,
    dma_channel_fifo_depth: 128,
    dma_nbr_ports: 1,
    dma_has_uid: 0,

    cmdblock_present: 0,
    cmdblock_fifo_depth: 0, // NA
    cmdblock_max_outst_cmds: 0 // NA
  };

  parameter snps_dma_cfg_t SNPS_DMA_APU_CFG = '{
    axi_port_aw: chip_pkg::CHIP_AXI_ADDR_W,
    axi_port_dw: apu_pkg::APU_AXI_MT_DATA_W,
    axi_port_idw: apu_pkg::AX65_AXI_MT_M_ID_W,
    axi_port_len: axi_pkg::AXI_LEN_WIDTH,

    dma_external_ram: 1,
    dma_macro_width: 128,
    dma_nbr_channels: 2,
    dma_channel_fifo_depth: 256,
    dma_nbr_ports: 1,
    dma_has_uid: 0,

    cmdblock_present: 0,
    cmdblock_fifo_depth: 0, // NA
    cmdblock_max_outst_cmds: 0 // NA
  };

  typedef enum logic[1:0] {
    legacy_idx = 2'd0,
    csr_base_idx = 2'd1, // base, every channel is at base + 2*CH_NR
    cmd_base_idx = 2'd2  // base, every channel is at base + 2*CH_NR
  } dma_dev_select_e;

endpackage
