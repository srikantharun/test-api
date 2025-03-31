// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

// Package: axe_dma_channel_pkg
package axe_dma_channel_pkg;

    `include "uvm_macros.svh"

    import uvm_pkg::*;
    import axe_uvm_scoreboard_pkg::*;
    import axe_uvm_resource_allocator_pkg::*;
    import axe_uvm_incrementor_pkg::*;
    import axe_dma_cmd_pkg::*;

    // Master Select
    typedef enum bit[1:0] {MS_1=0, MS_2=1, MS_3=2, MS_4=3} axe_dma_ms_t;

    // Outstanding Request Limit
    typedef bit[5:0]                                       axe_dma_ost_lmt_t;

    `include "axe_dma_channel_config.svh"
    `include "axe_dma_channel_sequencer.svh"
    `include "axe_dma_channel_driver.svh"
    `include "axe_dma_channel_coverage.svh"
    `include "axe_dma_channel_model.svh"
    `include "axe_dma_channel_scoreboard.svh"
    `include "axe_dma_channel_agent.svh"
    `include "axe_dma_channel_seq_lib.svh"

endpackage : axe_dma_channel_pkg
