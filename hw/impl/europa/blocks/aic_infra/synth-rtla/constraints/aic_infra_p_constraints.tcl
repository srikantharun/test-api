# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Luyi <yi.lu@axelera.ai>

set clock_period 0.83

create_clock -name clk -period $clock_period [get_ports {i_clk}]

set_false_path -from [get_ports {i_rst_n}]

set async_inputs [get_ports { test_mode i_cid i_reserved i_irq_* i_sram_* i_*_obs i_cva6v_debug_req_async i_cva6v_debug_rst_halt_req_async } ]
set async_outputs [get_ports { o_reserved o_aic_obs o_cva6v_debug_stop_time_async o_cva6v_hart_unavail_async o_cva6v_hart_under_reset_async } ]

set sync_inputs [remove_from_collection [remove_from_collection [all_inputs] [ get_object_name [get_clocks {clk}]]] $async_inputs]

#[remove_from_collection [all_inputs] [get_ports {i_clk}] $async_inputs ]

set sync_outputs [remove_from_collection [all_outputs] $async_outputs]

set_false_path -from $async_inputs
set_false_path -to $async_outputs

# I/O timing
set DelayInpMin [ expr 0.05*${clock_period} ]
set DelayInpMax [ expr 0.7*${clock_period}  ]
set DelayOupMin [ expr 0.05*${clock_period} ]
set DelayOupMax [ expr 0.7*${clock_period}  ]

set_input_delay -min ${DelayInpMin} -clock clk $sync_inputs
set_input_delay -max ${DelayInpMax} -clock clk $sync_inputs

set_output_delay -min ${DelayOupMin} -clock clk $sync_outputs
set_output_delay -max ${DelayOupMax} -clock clk $sync_outputs


# Estimated loads seen externally by ports.
set_load -pin_load 0.030 [all_outputs]
set_port_fanout_number 3 [all_outputs]

set_driving_cell -lib_cell BUF_D4_N_S6TR_C54L08 -input_transition_rise 0.03 -input_transition_fall 0.03  [all_inputs]


# Reset
set ResetPort i_rst_n
set_ideal_network -no_propagate [get_ports $ResetPort]
set_max_delay [expr 3.00*${clock_period}] -from [get_ports $ResetPort]

# Settings for funtional read and write on memory macros
# Sideband

set_multicycle_path -setup 3 -from [get_ports i_cva6v_boot_addr* ]

set_case_analysis 0 [get_ports i_cid[0]]
set_case_analysis 0 [get_ports i_cid[1]]
set_case_analysis 0 [get_ports i_cid[2]]
set_case_analysis 0 [get_ports i_cid[3]]
set_case_analysis 0 [get_ports i_cid[4]]
set_case_analysis 0 [get_ports i_cid[5]]
set_case_analysis 0 [get_ports i_cid[6]]
set_case_analysis 0 [get_ports i_cid[7]]

set_case_analysis 1 [get_ports i_sram_mcs[0]]
set_case_analysis 0 [get_ports i_sram_mcs[1]]

set_case_analysis 0 [get_ports i_sram_mcsw]
set_case_analysis 0 [get_ports i_sram_ret]
set_case_analysis 0 [get_ports i_sram_pde]

set_case_analysis 0 [get_ports i_sram_adme[0]]
set_case_analysis 0 [get_ports i_sram_adme[1]]
set_case_analysis 1 [get_ports i_sram_adme[2]]


set all_rf2 [get_cells -hier -filter { is_memory_cell ==true && ref_name =~ *rf2*}]
foreach_in_collection rf2 $all_rf2 {
  set_disable_timing -from  RCK  -to WCK $rf2
}


#set all_rfs [get_cells -hier  * -filter {is_memory_cell==true && full_name =~*rf*p*}]
#foreach_in_collection rf $all_rfs {
#
#   set rfname [get_object_name $rf]
#   set_case_analysis 1 [get_pins ${rfname}/ADME[2]]
#   set_case_analysis 0 [get_pins ${rfname}/ADME[1]]
#   set_case_analysis 0 [get_pins ${rfname}/ADME[0]]
#
#   set ref_name [get_attribute $rf ref_name]
#
#   if {![regexp "ra1rw" $rfname]} {
#      set_case_analysis 0 [get_pins ${rfname}/PDE]
#   }
#   set_case_analysis 0 [get_pins ${rfname}/RET]
#   set_case_analysis 0 [get_pins ${rfname}/DFTRAM]
#   set_case_analysis 0 [get_pins ${rfname}/SE]
#}
#
## Settings for funtional read and write on memory macros
#set all_srams [get_cells -hier  * -filter {is_memory_cell==true && full_name =~*ra*p*}]
#foreach_in_collection srams $all_srams {
#   set sramname [get_object_name $srams]
#   set_case_analysis 1 [get_pins ${sramname}/ADME[2]]
#   set_case_analysis 0 [get_pins ${sramname}/ADME[1]]
#   set_case_analysis 0 [get_pins ${sramname}/ADME[0]]
#   set_case_analysis 0 [get_pins ${sramname}/PDE]
#   set_case_analysis 0 [get_pins ${sramname}/RET]
#   set_case_analysis 0 [get_pins ${sramname}/DFTRAM]
#   set_case_analysis 0 [get_pins ${sramname}/SE]
#}
#
#set all_srams [get_cells -hier  * -filter {is_memory_cell==true && full_name =~*ra1*p*}]
#foreach_in_collection srams $all_srams {
#   set sramname [get_object_name $srams]
#   set_case_analysis 0 [get_pins ${sramname}/MCS[1]]
#   set_case_analysis 1 [get_pins ${sramname}/MCS[0]]
#   set_case_analysis 0 [get_pins ${sramname}/MCSW]
#}
#
#set all_rf1s [get_cells -hier  * -filter {is_memory_cell==true && full_name =~*rf1*p*}]
#foreach_in_collection rf1 $all_rf1s {
#   set rf1name [get_object_name $rf1]
#   set_case_analysis 0 [get_pins ${rf1name}/MCS[1]]
#   set_case_analysis 1 [get_pins ${rf1name}/MCS[0]]
#   set_case_analysis 0 [get_pins ${rf1name}/MCSW]
#}
#
## Settings for funtional read and write on memory macros
#set all_rf2s [get_cells -hier  * -filter {is_memory_cell==true && full_name =~*rf2*p*}]
#foreach_in_collection rf2 $all_rf2s {
#   set rf2name [get_object_name $rf2]
#   set_case_analysis 0 [get_pins ${rf2name}/MCSRD[1]]
#   set_case_analysis 1 [get_pins ${rf2name}/MCSRD[0]]
#   set_case_analysis 0 [get_pins ${rf2name}/MCSWR[1]]
#   set_case_analysis 1 [get_pins ${rf2name}/MCSWR[0]]
#   set_case_analysis 0 [get_pins ${rf2name}/KCS]
#}
#
##set_dont_touch [get_cells cva6v_unread]
