`ifndef AIC_DMC_IF
`define AIC_DMC_IF

interface aic_ls_if (input clk);
  import aic_ls_agent_pkg::*;
  logic reset_an_i;
  logic [CID_WIDTH-1:0] cid;
  logic l1_cg_enable;
  logic dmc_cg_enable;
  logic [1:0] l1_sw_cfg_fabric_sel;
  logic l1_mem_ls;
  logic l1_mem_ds;
  logic l1_mem_sd;
  logic l1_mem_rop;
  logic l1_mem_daisy_chain_bypass_sd;
  logic l1_mem_daisy_chain_bypass_ds;
  logic[ OBS_DW-1:0] aic_ls_obs;
  logic[ 6:0] l1_lc_fabric_dlock;
  logic sram_sw_test1;
  logic sram_sw_test_rnm;
  logic sram_sw_rme;
  logic [3:0] sram_sw_rm;
  logic [2:0] sram_sw_wa;
  logic [2:0] sram_sw_wpulse;
  logic sram_sw_fiso;
  logic ls_cg_en;
  logic [IRQ_W-1:0] irq_out;
  logic disable_decomp_assertion;
  logic disable_rdataX_aserrtion;


  clocking mon @(posedge clk);
    input reset_an_i;
    input cid;
    input l1_cg_enable;
    input dmc_cg_enable;
    input l1_sw_cfg_fabric_sel;
    input l1_mem_ls;
    input l1_mem_ds;
    input l1_mem_sd;
    input l1_mem_rop;
    input l1_mem_daisy_chain_bypass_sd;
    input l1_mem_daisy_chain_bypass_ds;
    input aic_ls_obs;
    input l1_lc_fabric_dlock;
    input sram_sw_test1;
    input sram_sw_test_rnm;
    input sram_sw_rme;
    input sram_sw_rm;
    input sram_sw_wa;
    input sram_sw_wpulse;
    input sram_sw_fiso;
    input ls_cg_en;
    input irq_out;
  endclocking

  clocking drv @(posedge clk);
    output disable_decomp_assertion;
    output disable_rdataX_aserrtion;
  endclocking

  initial begin
    disable_decomp_assertion = 0;
    disable_rdataX_aserrtion = 0;
  end


endinterface

`endif

