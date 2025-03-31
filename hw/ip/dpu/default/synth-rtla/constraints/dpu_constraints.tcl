######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Constraints for dpu
# Constraint Mode: func
######################################

#################
# Clock Domains #
#################
###############
# "fast_clk"
###############
puts "INFO: Adding clock: 'fast_clk' (1200 MHz)"
create_clock -add -name fast_clk -period 0.833 -waveform "0 0.417" [get_ports i_clk]
set_clock_uncertainty -setup [expr 0.833 * 0.10 ] [get_clocks fast_clk]
set_clock_uncertainty -hold 0.010 [get_clocks fast_clk]

# Synchronous Ports

puts "INFO: constraining '{i_*_axi* i_*_tok_*}' against 'fast_clk'"
set_input_delay -min 0.042 -clock fast_clk [get_ports {i_*_axi* i_*_tok_*}]
set_input_delay -max 0.583 -clock fast_clk [get_ports {i_*_axi* i_*_tok_*}]

puts "INFO: constraining '{o_*_axi* o_*_tok_* o_obs o_irq o_ts_* o_acd_sync}' against 'fast_clk'"
set_output_delay -min 0.042 -clock fast_clk [get_ports {o_*_axi* o_*_tok_* o_obs o_irq o_ts_* o_acd_sync}]
set_output_delay -max 0.583 -clock fast_clk [get_ports {o_*_axi* o_*_tok_* o_obs o_irq o_ts_* o_acd_sync}]


########################
# All clocks are ideal #
########################
set_ideal_network  [get_ports -filter {defined(clocks)}]




################
# Clock Groups #
################



##########
# Resets #
##########

set_ideal_network -no_propagate [get_ports i_rst_n]


################################
# Set Case Analysis Statements #
################################

set_case_analysis 0 [get_ports i_cid[0]]
set_case_analysis 0 [get_ports i_cid[1]]
set_case_analysis 0 [get_ports i_cid[2]]
set_case_analysis 1 [get_ports {i_sram_impl[mcs][0]}]
set_case_analysis 0 [get_ports {i_sram_impl[mcs][1]}]
set_case_analysis 0 [get_ports {i_sram_impl[mcsw]}]
set_case_analysis 0 [get_ports {i_sram_impl[ret]}]
set_case_analysis 0 [get_ports {i_sram_impl[pde]}]
set_case_analysis 0 [get_ports {i_sram_impl[adme][0]}]
set_case_analysis 0 [get_ports {i_sram_impl[adme][1]}]
set_case_analysis 1 [get_ports {i_sram_impl[adme][2]}]


#############################
# Set False Path Statements #
#############################

set_false_path  -from [get_ports {i_*rst*}] 
set_false_path  -to [get_ports {o_sram_impl[prn]}] 


##################################
# Set Multicycle Path Statements #
##################################

set_multicycle_path 3  -setup -to [get_flat_pins -filter "full_name=~*i_dpu*_irq_status_err_*D"] 
set_multicycle_path 2  -hold -to [get_flat_pins -filter "full_name=~*i_dpu*_irq_status_err_*D"] 


#######################
# Define the IO Delay #
#######################



################################
# Define additional max Delays #
################################



################################
# Define additional min Delays #
################################



#########################
# Data Check Statements #
#########################



####################
# Stop Propagation #
####################



#################################
# Set Disable Timing Statements #
#################################



##################
# Apply Retiming #
##################

set_optimize_registers -modules [get_modules *dpu_dp_sfu*] true


#############################################
# Estimated loads seen externally by ports. #
#############################################
set_load -pin_load 0.030 [all_outputs]
set_port_fanout_number 3 [all_outputs]

set_driving_cell -lib_cell BUF_D4_N_S6TR_C54L08 -input_transition_rise 0.03 -input_transition_fall 0.03  [all_inputs]
