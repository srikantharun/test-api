 /* Abstract:
 * Defines an interface that provides access to a reset signal.  This
 * interface can be used to write sequences to drive the reset logic.
 */
`ifndef GUARD_SPM_IF_SVI
`define GUARD_SPM_IF_SVI
`timescale 1ps/1ps

interface spm_if();
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;


  logic clk;
  logic rst_n;

  logic [22:0]  waddr;
  logic [22:0]  raddr;
  logic inv_addr=0;
  logic crpt_flg=0;
  logic trsct_cmplt=0;
  logic rd_crpt_data=0;

  assign spm_error_disable = $urandom_range(0,1);
 
  real clk_period = 833;

  property T_clk(real _clk_period);
  time current_time;
  disable iff(!rst_n)
  (1'b1,current_time=$realtime) |=> ( (_clk_period <= $realtime-(current_time-10))  && (_clk_period >= $realtime-(current_time + 10 )) );
  endproperty
   
  assert_period:assert property (@(posedge clk)T_clk(clk_period))
  `uvm_info("clk_asertion","clk is having 1.2GHz and it is passing",UVM_DEBUG)
  else
  `uvm_error("CLOCK_PERIOD_MEAS_FAILED = ", $sformatf("%5.3f TB_INFO : clk not correct",$time))

endinterface
`endif // GUARD_SPM_IF_SVI
 
