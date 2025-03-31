// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Anonymous <anonymous@axelera.ai>


/// TODO:__one_line_summary_of_dcd_pkg__
///
package dcd_pkg;
    // AXI Dec 0 - Init - MT
    parameter int unsigned DCD_DEC_0_INIT_MT_AXI_DATA_W = 128;
    typedef logic [DCD_DEC_0_INIT_MT_AXI_DATA_W-1:0] dcd_dec_0_init_mt_axi_data_t;
    parameter int unsigned DCD_DEC_0_INIT_MT_AXI_STRB_W = DCD_DEC_0_INIT_MT_AXI_DATA_W/8;
    typedef logic [DCD_DEC_0_INIT_MT_AXI_STRB_W-1:0] dcd_dec_0_init_mt_axi_strb_t;
    parameter int unsigned DCD_DEC_0_INIT_MT_AXI_ID_W = 5;
    typedef logic [DCD_DEC_0_INIT_MT_AXI_ID_W-1:0] dcd_dec_0_init_mt_axi_id_t;
    // AXI Dec 1 - Init - MT
    parameter int unsigned DCD_DEC_1_INIT_MT_AXI_DATA_W = 128;
    typedef logic [DCD_DEC_1_INIT_MT_AXI_DATA_W-1:0] dcd_dec_1_init_mt_axi_data_t;
    parameter int unsigned DCD_DEC_1_INIT_MT_AXI_STRB_W = DCD_DEC_1_INIT_MT_AXI_DATA_W/8;
    typedef logic [DCD_DEC_1_INIT_MT_AXI_STRB_W-1:0] dcd_dec_1_init_mt_axi_strb_t;
    parameter int unsigned DCD_DEC_1_INIT_MT_AXI_ID_W = 5;
    typedef logic [DCD_DEC_1_INIT_MT_AXI_ID_W-1:0] dcd_dec_1_init_mt_axi_id_t;
    // AXI Dec 2 - Init - MT
    parameter int unsigned DCD_DEC_2_INIT_MT_AXI_DATA_W = 128;
    typedef logic [DCD_DEC_2_INIT_MT_AXI_DATA_W-1:0] dcd_dec_2_init_mt_axi_data_t;
    parameter int unsigned DCD_DEC_2_INIT_MT_AXI_STRB_W = DCD_DEC_2_INIT_MT_AXI_DATA_W/8;
    typedef logic [DCD_DEC_2_INIT_MT_AXI_STRB_W-1:0] dcd_dec_2_init_mt_axi_strb_t;
    parameter int unsigned DCD_DEC_2_INIT_MT_AXI_ID_W = 5;
    typedef logic [DCD_DEC_2_INIT_MT_AXI_ID_W-1:0] dcd_dec_2_init_mt_axi_id_t;
    // AXI MCU Init - MT
    parameter int unsigned DCD_MCU_INIT_LT_AXI_DATA_W = 128;
    typedef logic [DCD_MCU_INIT_LT_AXI_DATA_W-1:0] dcd_mcu_init_lt_axi_data_t;
    parameter int unsigned DCD_MCU_INIT_LT_AXI_STRB_W = DCD_MCU_INIT_LT_AXI_DATA_W/8;
    typedef logic [DCD_MCU_INIT_LT_AXI_STRB_W-1:0] dcd_mcu_init_lt_axi_strb_t;
    parameter int unsigned DCD_MCU_INIT_LT_AXI_ID_W = 5;
    typedef logic [DCD_MCU_INIT_LT_AXI_ID_W-1:0] dcd_mcu_init_lt_axi_id_t;
    // APB Target - Cfg
    parameter int unsigned DCD_TARG_CFG_APB_ADDR_W = 20;
    typedef logic [DCD_TARG_CFG_APB_ADDR_W-1:0] dcd_targ_cfg_apb_addr_t;
    parameter int unsigned DCD_TARG_CFG_APB_DATA_W = 32;
    typedef logic [DCD_TARG_CFG_APB_DATA_W-1:0] dcd_targ_cfg_apb_data_t;
    parameter int unsigned DCD_TARG_CFG_APB_STRB_W = DCD_TARG_CFG_APB_DATA_W/8;
    typedef logic [DCD_TARG_CFG_APB_STRB_W-1:0] dcd_targ_cfg_apb_strb_t;
endpackage
