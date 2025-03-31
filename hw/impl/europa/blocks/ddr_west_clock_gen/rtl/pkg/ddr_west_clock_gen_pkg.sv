// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>


// Package for the ddr_west clock gen block
//
package ddr_west_clock_gen_pkg;
  import ddr_west_clock_gen_csr_reg_pkg::*;

  // number of sync stages
  parameter int unsigned STAGE_NUM = 3   ;

  // pll dividers register width
  parameter int unsigned PLLM_W    = 10  ;
  parameter int unsigned PLLP_W    =  6  ;
  parameter int unsigned PLLS_W    =  3  ;

  parameter int unsigned CLKSEL_W  =  1  ;

  // type declarations
  // PLL Divider types
  typedef logic [PLLM_W  -1:0] pllm_t    ;
  typedef logic [PLLP_W  -1:0] pllp_t    ;
  typedef logic [PLLS_W  -1:0] plls_t    ;

  typedef logic [CLKSEL_W-1:0] clksel_t  ;

  // pll reserved pin value
  // PLL reserved input width
  parameter int unsigned PLL_RESW  = 4   ;

  // pll reserved value type
  typedef logic [PLL_RESW-1:0] pll_res_t ;
  // PLL _ICP input pin
  typedef logic [         1:0] pll_icp_t ;

  parameter pll_res_t    PLL_RSEL = 4'h8 ;

  // pll icp pin value
  parameter pll_icp_t    PLL_ICP  = 2'h1 ;

endpackage
