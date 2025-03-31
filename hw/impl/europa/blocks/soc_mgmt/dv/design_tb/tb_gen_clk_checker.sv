module tb_gen_clk_checker #(
  parameter int unsigned CH                = 0,
  parameter bit          PLL_OR_DIVN_CHECK = 1
) (
  input  wire                              i_ref_clk        ,
  input  wire                              i_rst_n          ,
  input  wire                              i_gen_clk        ,
  soc_mgmt_clk_checker_pkg::pll_port_t     i_mon_pll_lock   ,
  soc_mgmt_clk_checker_pkg::pllm_port_t    i_mon_pll_m      ,
  soc_mgmt_clk_checker_pkg::pllp_port_t    i_mon_pll_p      ,
  soc_mgmt_clk_checker_pkg::plls_port_t    i_mon_pll_s      ,
  soc_mgmt_clk_checker_pkg::clk_sel_port_t i_mon_clk_sel    ,
  input  int unsigned                      i_div            ,
  output bit                               o_fail
);


timeunit      1ps;
timeprecision 1ps;

import uvm_pkg::*;
`include "uvm_macros.svh"

localparam real FIN = 50.0e6;

real         meas_freq;
real         exp_pll_freq;
real         div_ref_freq;
real         pll_freq_diff;
real         div_freq_diff;
real         div_ratio;
int unsigned fail_cnt;
bit          do_check;
event        ev_pll;
event        ev_div;
int unsigned debug_cnt;

real         fvco;
real         fdenom;

initial begin
  o_fail   = 0;
  do_check = 0;
  @ (posedge i_rst_n);
  wait(i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_clk_gen.gen_plls[0].u_pll_wrapper.i_pll_resetb);

  forever begin
    meas_clk_freq();
    exp_pll_freq = pll_calc_fout(FIN, i_mon_pll_m, i_mon_pll_p, i_mon_pll_s);
    pll_freq_diff = meas_freq - exp_pll_freq;

    //==========================================================================
    // PLL Checks
    if (PLL_OR_DIVN_CHECK) begin
      // start checking after after measurement completes so that idf register
      // changes mid measurement. result will not be checked.
      if (do_check) begin
        check_pll_clk(meas_freq, exp_pll_freq);
        ->ev_pll;
      end
    end else begin
      meas_ref_clk_freq();
      meas_clk_freq();
      div_ratio = div_ref_freq / meas_freq;

      if (i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_clk_gen.gen_plls[0].u_pll_wrapper.i_pll_resetb) begin
        if (do_check) begin
          check_div_clk(div_ratio, real'(i_div));
          ->ev_div;
        end
      end
    end

    if (i_mon_pll_lock && i_mon_clk_sel==CH) begin
      do_check = 1;
      // delay for clock switch
      #30us;
    end
  end
end

//==============================================================================
// check the divider clock ratio matches expected
function void check_div_clk(real act, exp);
  real exp_min;
  real exp_max;

  exp_min = exp - 0.2;
  exp_max = exp + 0.2;

  if (!(act inside {[exp_min:exp_max]})) begin
    fail_cnt++;
    o_fail = 1;
    `uvm_error("DIV_CLK_CHECK", $sformatf("ERROR Div Clock CLK: %0d Act: %f Exp: %f", CH, act, exp))
  end
endfunction

//==============================================================================
// check pll clock frequency matches calculation freq
function void check_pll_clk(real act, exp);
  real exp_min;
  real exp_max;

  exp_min = exp - 1.0e6;
  exp_max = exp + 1.0e6;

  if (!(act inside {[exp_min:exp_max]})) begin
    fail_cnt++;
    o_fail = 1;
    `uvm_error("PLL_CLK_CHECK", $sformatf("ERROR PLL Clock CLK: %0d Act: %f Exp: %f Diff: %f", CH-1, act, exp, pll_freq_diff))
  end
endfunction

//==============================================================================
// measure the frequency
task automatic meas_clk_freq(int unsigned meas_cycles = 1000);
  realtime time_start;
  realtime time_end  ;
  real     period    ;

  @(posedge i_gen_clk);
  time_start = $realtime;

  debug_cnt = 0;
  for (int i=0; i<meas_cycles; i++) begin
    @ (posedge i_gen_clk);
    debug_cnt++;
  end
  time_end = $realtime;

  period        = real'((time_end - time_start)) / real'(meas_cycles);
  meas_freq     = 1.0e12 / real'(period);
endtask

//==============================================================================
// measure the frequency
task automatic meas_ref_clk_freq(int unsigned meas_cycles = 1000);
  realtime time_start;
  realtime time_end  ;
  real     period    ;

  @(posedge i_ref_clk);
  time_start = $realtime;

  for (int i=0; i<meas_cycles; i++) begin
    @ (posedge i_ref_clk);
  end
  time_end = $realtime;

  period       = real'((time_end - time_start)) / real'(meas_cycles);
  div_ref_freq = 1.0e12 / real'(period);
endtask

//==============================================================================
function real pll_calc_fout(real fref, m, p, s);
   // debug calcs
   fvco   = fref * m     ;
   fdenom = p    * 2.0**s;
   // set output freq
   if (p != 0)
      return (fref * m) / (p * 2.0**s);
   else
      return (0);
endfunction

endmodule
