// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Leonidas Katselas <leonidas.katselas@axelera.ai>


/// TODO:__one_line_summary_of_codec_pkg__
///
package allegro_codec_pkg;

  // AXI
  parameter int unsigned CODEC_AXI_DATA_WIDTH = 128;
  parameter int unsigned CODEC_AXI_LEN_WIDTH = 8;
  parameter int unsigned CODEC_AXI_WSTRB_WIDTH = CODEC_AXI_DATA_WIDTH / 8;
  parameter int unsigned CODEC_AXI_ADDR_WIDTH = 40;
  parameter int unsigned CODEC_AXI_ID_WIDTH = 5;
  parameter int unsigned CODEC_AXI_SIZE_WIDTH = 3;
  parameter int unsigned CODEC_AXI_BURST_TYPE_WIDTH = 2;
  parameter int unsigned CODEC_AXI_RESP_WIDTH = 2;
  parameter int unsigned CODEC_AXI_PROT_WIDTH = 3;
  // APB Target - Cfg
  parameter int unsigned DCD_TARG_CFG_APB_ADDR_W = 20;
  typedef logic [DCD_TARG_CFG_APB_ADDR_W-1:0] dcd_targ_cfg_apb_addr_t;
  parameter int unsigned DCD_TARG_CFG_APB_DATA_W = 32;
  typedef logic [DCD_TARG_CFG_APB_DATA_W-1:0] dcd_targ_cfg_apb_data_t;
  parameter int unsigned DCD_TARG_CFG_APB_STRB_W = DCD_TARG_CFG_APB_DATA_W/8;
  typedef logic [DCD_TARG_CFG_APB_STRB_W-1:0] dcd_targ_cfg_apb_strb_t;


endpackage
