// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Anonymous <anonymous@axelera.ai>


/// TODO:__one_line_summary_of_ai_core_pkg__
///
package ai_core_pkg;
    // AXI Init - HT
    parameter int unsigned AI_CORE_INIT_HT_AXI_ID_W = 9;
    typedef logic [AI_CORE_INIT_HT_AXI_ID_W-1:0] ai_core_init_ht_axi_id_t;
    // AXI Init - LT
    parameter int unsigned AI_CORE_INIT_LT_AXI_ID_W = 9;
    typedef logic [AI_CORE_INIT_LT_AXI_ID_W-1:0] ai_core_init_lt_axi_id_t;
    // AXI Targ - LT
    parameter int unsigned AI_CORE_TARG_LT_AXI_ID_W = 6;
    typedef logic [AI_CORE_TARG_LT_AXI_ID_W-1:0] ai_core_targ_lt_axi_id_t;
endpackage
