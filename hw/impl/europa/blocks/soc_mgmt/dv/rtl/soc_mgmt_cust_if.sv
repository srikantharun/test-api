/**
 * Abstract:
 * Defines an interface that provides access to a reset signal.  This
 * interface can be used to write sequences to drive the reset logic.
 */
`ifndef GUARD_SOC_MGMT_IF_SVI
`define GUARD_SOC_MGMT_IF_SVI

interface soc_mgmt_if(input bit clk,input bit rst_n);

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_axi_uvm_pkg::*;

  //Asynchroonous Always On state reset to all partitions, active low.
  logic o_ao_rst_n;
  logic o_global_rst_n;
  logic fast_clk_check_en;
  logic apu_clk_check_en;
  logic codec_clk_check_en;
  logic emmc_clk_check_en;
  logic periph_clk_check_en;
  logic pvt_clk_check_en;
  logic ddr_clk_check_en;

  // TO ADD
endinterface

`endif // GUARD_SOC_MGMT_IF_SVI
