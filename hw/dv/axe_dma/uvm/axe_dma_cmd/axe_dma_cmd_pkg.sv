// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

// Package: axe_dma_cmd_pkg
package axe_dma_cmd_pkg;

  `include "uvm_macros.svh"

  import uvm_pkg::*;

  // Command Format
  typedef enum bit[2:0] {CMD_1D      = 0,
                         CMD_1D_INC  = 1,
                         CMD_1D_FULL = 2,
                         CMD_2D      = 3,
                         CMD_2D_FULL = 4,
                         CMD_LL      = 5} axe_dma_cmd_fmt_t;


  `include "axe_dma_cmd.svh"
endpackage : axe_dma_cmd_pkg
