// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Anonymous <anonymous@axelera.ai>


/// TODO:__one_line_summary_of_lpddr_pkg__
///
package lpddr_pkg;
    parameter int unsigned LPDDR_TARG_AXI_ID_W = 8;
    parameter int unsigned LPDDR_TARG_AXI_ADDR_W  =  33;
    parameter int unsigned LPDDR_TARG_AXI_DATA_W = 256;
    parameter int unsigned LPDDR_TARG_AXI_STRB_W = LPDDR_TARG_AXI_DATA_W/8;

    // AXI Targ
    typedef logic [LPDDR_TARG_AXI_ID_W-1:0] lpddr_targ_axi_id_t;
    typedef logic [LPDDR_TARG_AXI_ADDR_W-1:0] lpddr_targ_axi_addr_t;
    typedef logic [LPDDR_TARG_AXI_DATA_W-1:0] lpddr_targ_axi_data_t;
    typedef logic [LPDDR_TARG_AXI_STRB_W-1:0] lpddr_targ_axi_strb_t;

    // AXI Graph Targ - HT (same as above, but NoC wrapping uses different types in its release)
    typedef logic [LPDDR_TARG_AXI_ID_W-1:0] lpddr_graph_targ_ht_axi_id_t;
    typedef logic [LPDDR_TARG_AXI_ADDR_W-1:0] lpddr_graph_targ_ht_axi_addr_t;
    typedef logic [LPDDR_TARG_AXI_DATA_W-1:0] lpddr_graph_targ_ht_axi_data_t;
    typedef logic [LPDDR_TARG_AXI_STRB_W-1:0] lpddr_graph_targ_ht_axi_strb_t;
    // AXI PPP Targ - MT (same as above, but NoC wrapping uses different types in its release)
    typedef logic [LPDDR_TARG_AXI_ID_W-1:0] lpddr_ppp_targ_mt_axi_id_t;
    typedef logic [LPDDR_TARG_AXI_ADDR_W-1:0] lpddr_ppp_targ_mt_axi_addr_t;
    typedef logic [LPDDR_TARG_AXI_DATA_W-1:0] lpddr_ppp_targ_mt_axi_data_t;
    typedef logic [LPDDR_TARG_AXI_STRB_W-1:0] lpddr_ppp_targ_mt_axi_strb_t;

    // APB Targ - PHY CFG
    parameter int unsigned LPDDR_TARG_PHY_CFG_APB3_DATA_W = 32;
    typedef logic [LPDDR_TARG_PHY_CFG_APB3_DATA_W-1:0] lpddr_targ_phy_cfg_apb3_data_t;
    parameter int unsigned LPDDR_TARG_PHY_CFG_APB3_ADDR_W = 32;
    typedef logic [LPDDR_TARG_PHY_CFG_APB3_ADDR_W-1:0] lpddr_targ_phy_cfg_apb3_addr_t;

    parameter int unsigned LPDDR_PERF_COUNTER_WIDTH = 32;

    // Number of sync stages in all synchronisers used between ao clk and lpddr clk
    parameter int unsigned LPDDR_SYNC_STAGES = 3;
endpackage
