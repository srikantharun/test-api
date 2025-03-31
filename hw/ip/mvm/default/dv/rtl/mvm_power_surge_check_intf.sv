//=======================================================
//File   :
//Author : Priyadarsan Vasudevan
//Description
//=======================================================

`define MVM_MAX_IMC_BANKS 16
`define BANK_TRANSTION_TOLERANCE 2
`define BANK_TRANSTION_TOLERANCE_IAU_ASSERTED 1
`define POWER_SURGE_INTERVAL 1000
interface mvm_power_surge_check_intf(input bit clk,input bit rst_n);

import uvm_pkg::*;
`include "uvm_macros.svh"

 logic [(`MVM_MAX_IMC_BANKS-1):0]compute_gate_clock;
 logic [(`MVM_MAX_IMC_BANKS-1):0]compute_block_enable;
 int num_active_banks_by_compute_gate_clock;
 int num_active_banks_by_compute_gate_clock_d;
 int num_bank_state_changed_by_compute_gate_clock;

 int num_active_banks_by_compute_block_enable;
 int num_active_banks_by_compute_block_enable_d;
 int num_bank_state_changed_by_compute_block_enable;

 bit power_smooth_dummy_ops;
 logic static_mvm_iau_axis_m_tready;
 
 logic unexpcted_power_surge_by_compute_gate_clock;
 logic unexpcted_power_surge_by_compute_block_enable;

 initial begin
  power_smooth_dummy_ops = 0;
  static_mvm_iau_axis_m_tready = 0;
 end


 always_comb begin
   num_active_banks_by_compute_gate_clock = (`MVM_MAX_IMC_BANKS - $countones(compute_gate_clock));
   num_active_banks_by_compute_block_enable = $countones(compute_block_enable);
 end

 always @(posedge clk or negedge rst_n) begin
   if (rst_n == 0) begin
     num_active_banks_by_compute_gate_clock_d <= 0;  
     num_active_banks_by_compute_block_enable_d <= 0;  
   end else begin
     num_active_banks_by_compute_gate_clock_d <= num_active_banks_by_compute_gate_clock;
     num_bank_state_changed_by_compute_gate_clock = (num_active_banks_by_compute_gate_clock - num_active_banks_by_compute_gate_clock_d) > 0 ? (num_active_banks_by_compute_gate_clock - num_active_banks_by_compute_gate_clock_d) : (num_active_banks_by_compute_gate_clock_d - num_active_banks_by_compute_gate_clock);

     num_active_banks_by_compute_block_enable_d <= num_active_banks_by_compute_block_enable;
     num_bank_state_changed_by_compute_block_enable = (num_active_banks_by_compute_block_enable - num_active_banks_by_compute_block_enable_d) > 0 ? (num_active_banks_by_compute_block_enable - num_active_banks_by_compute_block_enable_d) : (num_active_banks_by_compute_block_enable_d - num_active_banks_by_compute_block_enable);
   end
 end


 always_comb begin
   if (power_smooth_dummy_ops == 0)begin
     unexpcted_power_surge_by_compute_gate_clock   =  (num_bank_state_changed_by_compute_gate_clock > `BANK_TRANSTION_TOLERANCE);
     unexpcted_power_surge_by_compute_block_enable =  (num_bank_state_changed_by_compute_block_enable > `BANK_TRANSTION_TOLERANCE);
   end else begin
     if (static_mvm_iau_axis_m_tready == 1) begin
        unexpcted_power_surge_by_compute_gate_clock   =  (num_bank_state_changed_by_compute_gate_clock > `BANK_TRANSTION_TOLERANCE_IAU_ASSERTED);
        unexpcted_power_surge_by_compute_block_enable =  (num_bank_state_changed_by_compute_block_enable > `BANK_TRANSTION_TOLERANCE_IAU_ASSERTED);
     end else begin
        unexpcted_power_surge_by_compute_gate_clock   =  (num_bank_state_changed_by_compute_gate_clock > `BANK_TRANSTION_TOLERANCE);
        //unexpcted_power_surge_by_compute_block_enable =  (num_bank_state_changed_by_compute_block_enable > 1);// See issue #2430
        unexpcted_power_surge_by_compute_block_enable =  (num_bank_state_changed_by_compute_block_enable > `BANK_TRANSTION_TOLERANCE);
     end
   end
 end

//As per discussion with Architect,
//Updated the assertion such that there is
//no unexpeted power surge for two conseutive cycles
//num_bank_state_changed_by_compute_gate_clock transition : 5->2->3 --- valid scenario
//num_bank_state_changed_by_compute_gate_clock transition : 5->2->5 --- invlaid sceanrio
//Currently disabling assertion when power smooth operation is inactive
// as we are observing banks getting active/inactive not in linear manner.
property POWER_SURGE_BY_COMPUTE_GATE_CLOCK;
    @(posedge clk) disable iff(!rst_n)
    (num_bank_state_changed_by_compute_gate_clock != $past(num_bank_state_changed_by_compute_gate_clock)) |-> !(unexpcted_power_surge_by_compute_gate_clock && $past(unexpcted_power_surge_by_compute_gate_clock));
endproperty

property POWER_SURGE_BY_COMPUTE_BLOCK_ENABLE;
    @(posedge clk) disable iff(!rst_n)
    (num_bank_state_changed_by_compute_block_enable != $past(num_bank_state_changed_by_compute_block_enable)) |-> (unexpcted_power_surge_by_compute_block_enable == 0);
endproperty

property UNEXPETED_POWER_SURGE_BY_COMPUTE_GATE_CLOCK_LARGE_TIME_INTERVAL(n);
    @(posedge clk) disable iff(!rst_n)
     unexpcted_power_surge_by_compute_gate_clock |=> !unexpcted_power_surge_by_compute_gate_clock [*n];
endproperty

POWER_SURGE_CHECK_BY_GATE_CLOCK   : assert property (POWER_SURGE_BY_COMPUTE_GATE_CLOCK) else begin `uvm_error("MVM_POWER_SURGE_CHEKC_INTF","Power Surge Detected when checked at compute_gate_clock if") end 
POWER_SURGE_CHECK_BY_BLOCK_ENABLE : assert property (POWER_SURGE_BY_COMPUTE_BLOCK_ENABLE) else begin `uvm_error("MVM_POWER_SURGE_CHEKC_INTF","Power Surge Detected when checked at compute_block_enable if") end
UNEXPETED_POWER_SURGE_CHECK : assert property (UNEXPETED_POWER_SURGE_BY_COMPUTE_GATE_CLOCK_LARGE_TIME_INTERVAL(`POWER_SURGE_INTERVAL)) else  begin `uvm_error("MVM_POWER_SURGE_CHEKC_INTF","Power Surge Detected multiple times within 1000 cycles") end


endinterface
