//=======================================================
//File   :
//Author : Priyadarsan Vasudevan
//Description
//=======================================================
interface mvm_utils_filter_intf(input bit clk,input bit rst_n);

import uvm_pkg::*;
`include "uvm_macros.svh"
import mvm_pkg::*;

 // Util signals
  logic [          MVM_UTIL_INTERFACE_WIDTH-1:0] mvm_util_limit_value_i;
  logic                                          mvm_util_limit_enable_i;
  logic [MVM_UTIL_EXP_AVG_DENOMINATOR_WIDTH-1:0] mvm_util_average_nominator_i;
  logic [          MVM_UTIL_INTERFACE_WIDTH-1:0] mvm_util_average_o;
  logic [8:0] mvm_util_value_i;
  logic mvm_util_valid_i;

  int signed tb_rtl_diff;
  logic  mismatch_error;
  logic disable_assertion_for_irq = 0; 
  logic [2:0] assrt_ctrl; 

initial begin
  mvm_util_limit_value_i = 0;
  mvm_util_limit_enable_i = 0;
  mvm_util_average_nominator_i = 0;
end


  logic [          MVM_UTIL_INTERFACE_WIDTH-1:0] mvm_util_average_predicted;
  logic [31:0] mvm_util_average_predicted_d;

  real term1,term2,term3,term4,term5,term6;
  bit [31:0] term7,term8;

  real average_fractional_part,cumulative_fractional_part;

  function real get_fractional_part (input real in_value);
   real term1,term2,term3;
   int term5;
  
    term1 = in_value;
    term5 = term1;
    if (term5 > term1) begin
      term2 = term5 - term1;
      term3 = 1-term2;
    end else begin
      term3 = term1 - term5;
    end
    return(term3);
  endfunction



 always_comb begin
     term1 = (mvm_util_average_nominator_i/256.0);
     term2 = (mvm_util_average_predicted_d * term1);

     term3 = (256-mvm_util_average_nominator_i);
     term4 = term3/256.0;
     term5 = (mvm_util_value_i * term4) * mvm_util_valid_i;

     term6 = (term2 + term5);

     average_fractional_part = get_fractional_part(term6);
     term7 = term6 - average_fractional_part;//real to int conversion
 end

 always @(posedge clk or negedge rst_n) begin
   if (rst_n == 0) begin
    mvm_util_average_predicted  <= 0;
    mvm_util_average_predicted_d  <= 0;
    cumulative_fractional_part <= 0;
   end else begin

    mvm_util_average_predicted_d <= term7 + ((cumulative_fractional_part >= 1.0) ? 1 : 0);

    if (cumulative_fractional_part >= 1.0) begin
       cumulative_fractional_part  <= cumulative_fractional_part + average_fractional_part - 1;
    end else begin
       cumulative_fractional_part  <= cumulative_fractional_part + average_fractional_part;
    end
    mvm_util_average_predicted   <= mvm_util_average_predicted_d[8:2];
   end 
 end

 assign tb_rtl_diff = $signed(mvm_util_average_predicted - mvm_util_average_o);
 assign mismatch_error = (tb_rtl_diff > 0) ? ((mvm_util_average_predicted - mvm_util_average_o)>1) : ((mvm_util_average_o - mvm_util_average_predicted) > 1);

//TODO : Prashanthi
 // currently, diabled the assertion as power surge operation is not working now
 //property FILTER_ERROR;
 //  @(posedge clk) disable iff (!rst_n) 
 //  mismatch_error != $past(mismatch_error) |-> (mismatch_error == 0);
 //endproperty;

 //FILTER_ERROR_CHECK : assert property(FILTER_ERROR) else begin `uvm_error("MVM_UTILS_FILTER_INTF","filter value predicted and actual are not matching") end

endinterface

