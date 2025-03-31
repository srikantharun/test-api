/**
 * Abstract:
 * Defines an interface that provides access to a power signal.  This
 * interface can be used to write sequences to drive the pwer signals(ls,ds,sd).
 */
interface l2_power_if();

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  logic clk;
  logic rst_n;

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

    //To check the ref clock frequency @1.2GHz

 real clk_period = 0.833ns;
 property T_clk(real clk_period);
 time current_time;
 disable iff(!rst_n)
 (1'b1,current_time=$realtime, $display("current time is when assertion getting triggered is ", current_time)) |=> ( (clk_period <= $realtime-(current_time-1))  &&   (clk_period >= $realtime-(current_time + 1 )) ,$display("real time in assetion is %0f",$time));
 endproperty

 assert_period:assert property (@(posedge clk)T_clk(clk_period));
 `uvm_info("clk_asertion","ref clk is having  1.2 GHz and it is passing",UVM_NONE)
 else
 `uvm_error("%t TB_INFO : ref clk is not running at correct freq",$time);
 

  `ifndef TARGET_GLS
  function disable_axi4_errs_rdata_x_assert;
    $assertoff(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errs_rdata_x);    
  endfunction

  function enable_axi4_errs_rdata_x_assert;
    $asserton(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errs_rdata_x);    
  endfunction
  
  function disable_axi4_errm_araddr_boundary;
    $assertoff(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errm_araddr_boundary);
  endfunction 

  function disable_axi4_errm_awaddr_boundary;
   $assertoff(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errm_awaddr_boundary);
  endfunction

  function enable_axi4_errm_araddr_boundary;
    $asserton(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errm_araddr_boundary);
  endfunction 

  function enable_axi4_errm_awaddr_boundary;
   $asserton(0,hdl_top.dut.u_l2.AXI_AIP_L2.axi4_errm_awaddr_boundary);
  endfunction
  `endif
  
endinterface
