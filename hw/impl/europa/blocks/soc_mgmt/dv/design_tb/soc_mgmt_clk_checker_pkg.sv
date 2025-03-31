// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>

// Package for soc_mgmt testbench
package soc_mgmt_clk_checker_pkg;

parameter int unsigned PLLM_W       = 10;
parameter int unsigned PLLP_W       =  6;
parameter int unsigned PLLS_W       =  3;

parameter int unsigned NUM_DIV_CLK  =  6;

typedef logic                                                         pll_port_t;
typedef logic                                            [PLLM_W-1:0] pllm_port_t;
typedef logic                                            [PLLP_W-1:0] pllp_port_t;
typedef logic                                            [PLLS_W-1:0] plls_port_t;

typedef logic [soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL-1:0]             pll_t;
typedef logic [soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL-1:0][PLLM_W-1:0] pllm_t;
typedef logic [soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL-1:0][PLLP_W-1:0] pllp_t;
typedef logic [soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL-1:0][PLLS_W-1:0] plls_t;

typedef logic                                            [$clog2(soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL)-1:0]clk_sel_port_t;
typedef logic [soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL-1:0][$clog2(soc_mgmt_clk_gen_csr_reg_pkg::NUM_PLL)-1:0]clk_sel_t;

typedef real freq_t;

typedef logic [NUM_DIV_CLK-1:0] div_clk_t               ;
typedef int unsigned            div_value_t[NUM_DIV_CLK];

typedef bit   [NUM_DIV_CLK-1:0] div_fail_t              ;

    //.o_slow_clk                   ( o_slow_clk                 ),

    // ddr_aix_clk

endpackage

