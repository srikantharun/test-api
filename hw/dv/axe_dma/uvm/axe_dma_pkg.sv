// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

// Package: axe_dma_pkg
package axe_dma_pkg;

    `include "uvm_macros.svh"

    import uvm_pkg::*;
    import axe_dma_cmd_pkg::*;
    import axe_dma_channel_pkg::*;

    `include "axe_dma_config.svh"
    `include "axe_dma_agent.svh"
    `include "axe_dma_seq_lib.svh" 
endpackage : axe_dma_pkg
