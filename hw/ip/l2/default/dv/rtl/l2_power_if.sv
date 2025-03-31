/**
 * Abstract:
 * Defines an interface that provides access to a power signal.  This
 * interface can be used to write sequences to drive the pwer signals(ls,ds,sd).
 */
`ifndef GUARD_L2_POWER_IF_SV
`define GUARD_L2_POWER_IF_SV
interface l2_power_if();

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  logic clk;
  logic rst_n;
  logic apb_rst; 
  logic ref_clk; 

  logic ls;
  logic ds;
  logic sd;
  logic bypass_chain_ds;
  logic bypass_chain_sd;
  logic [7:0] bank_rop;
  logic cg_bypass;
  logic reset_toggle;
  logic toggle_ready;
  logic rop;

  `ifndef TARGET_GLS
  function disable_axi4_errs_rdata_x_assert;
   // $assertoff(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errs_rdata_x);    
  endfunction

  function enable_axi4_errs_rdata_x_assert;
    //$asserton(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errs_rdata_x);    
  endfunction
  
  function disable_axi4_errm_araddr_boundary;
   // $assertoff(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errm_araddr_boundary);
  endfunction 

  function disable_axi4_errm_awaddr_boundary;
   //$assertoff(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errm_awaddr_boundary);
  endfunction

  function enable_axi4_errm_araddr_boundary;
    //$asserton(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errm_araddr_boundary);
  endfunction 

  function enable_axi4_errm_awaddr_boundary;
   //$asserton(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errm_awaddr_boundary);
  endfunction
  `endif
  
endinterface
`endif
