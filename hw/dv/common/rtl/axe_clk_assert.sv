// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// SV Assertions for clk freq check
// Owner: Pchapala

module axe_clk_assert(input bit clk, input bit rst_n,int freq_mhz,time tol_ps = 10);

     
  // Time unit and precision
  timeunit      1ps;
  timeprecision 1ps;   

   
   
  property T_clk;
  time current_time;
  disable iff(!rst_n)
  (1'b1,current_time=$realtime) |=> (((1e6/freq_mhz) <= $realtime-(current_time-tol_ps))  && ((1e6/freq_mhz) >= $realtime-(current_time + tol_ps)) );
  endproperty

  assert_period : assert property (@(posedge clk) T_clk) else $fatal("Freqency is not expected ",freq_mhz); 
   
endmodule : axe_clk_assert
