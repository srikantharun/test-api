// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Anonymous <anonymous@axelera.ai>


/// TODO:__one_line_summary_of_l2_pkg__
///
package l2_p_pkg;
    // AXI Targ - HT
    parameter int unsigned L2_TARG_HT_AXI_ID_W = 4;
    typedef logic [L2_TARG_HT_AXI_ID_W-1:0] l2_targ_ht_axi_id_t;

    parameter int unsigned L2_ADDR_WD = cc_math_pkg::index_width(l2_cfg_pkg::L2_MEM_SIZE);
    typedef logic [L2_ADDR_WD-1:0] l2_addr_t;
endpackage
