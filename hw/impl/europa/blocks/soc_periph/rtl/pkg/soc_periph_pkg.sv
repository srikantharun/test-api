// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Stefan Linz <stefan.linz@axelera.ai>


/// TODO:__one_line_summary_of_soc_periph_pkg__
///
package soc_periph_pkg;
    // AXI Init - LT
    parameter int unsigned SOC_PERIPH_INIT_LT_AXI_ID_W = 4;
    typedef logic [SOC_PERIPH_INIT_LT_AXI_ID_W-1:0] soc_periph_init_lt_axi_id_t;
    // AXI Targ - LT
    parameter int unsigned SOC_PERIPH_TARG_LT_AXI_ID_W = 4;
    typedef logic [SOC_PERIPH_TARG_LT_AXI_ID_W-1:0] soc_periph_targ_lt_axi_id_t;

    parameter int unsigned N_THROTTLE_PINS = 0;
endpackage
