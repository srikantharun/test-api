/**
 * Abstract:
 * Defines an interface that provides access to a reset signal.  This
 * interface can be used to write sequences to drive the reset logic.
 */
`ifndef GUARD_MVM_IF_SVI
 `define GUARD_MVM_IF_SVI
interface mvm_if(input bit clk,input bit rst_n);
   
  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import mvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_axi_uvm_pkg::*;

  logic mvm_flush_oprt; 
  logic mvm_int_clk;

  imc_bist_pkg::aic_csr_hw2reg_t aic_csr_hw2reg;
  imc_bist_pkg::aic_csr_reg2hw_t aic_csr_reg2hw;

  logic imc_bist_busy;
  logic imc_bist_done;
  logic imc_bist_pass; 
  logic broadcast_mode;
  mvm_pkg::prog_mode_e prgmode;
  
  int cmdblk_cmd_done_count;
   
  
  initial begin
    aic_csr_reg2hw.imc_bist_cmd = '0;
    aic_csr_reg2hw.imc_bist_cfg = '0;
  end

  function disable_axi4_errs_rdata_x_assert;
    //currently wrapper for mvm subsytem is not in rep      
    //$assertoff(0, hdl_top.dut.AXI_AIP_AI_CORE_MVM_PROTOCOL_CHECKER.axi4_errs_rdata_x);
  endfunction 

   
endinterface

`endif // GUARD_MVM_IF_SVI
