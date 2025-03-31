######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Constraints for aic_did_p
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

puts "INFO: constraining '{i_axi* i_token_* i_destination_cmd_done*}' against 'fast_clk'"
set_input_delay -min 0.042 -clock fast_clk [get_ports {i_axi* i_token_* i_destination_cmd_done*}]
set_input_delay -max 0.583 -clock fast_clk [get_ports {i_axi* i_token_* i_destination_cmd_done*}]

puts "INFO: constraining '{o_axi* o_token_* o_irq o_timestamp_*}' against 'fast_clk'"
set_output_delay -min 0.042 -clock fast_clk [get_ports {o_axi* o_token_* o_irq o_timestamp_*}]
set_output_delay -max 0.583 -clock fast_clk [get_ports {o_axi* o_token_* o_irq o_timestamp_*}]


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

set_case_analysis 0 [get_ports {i_aic_base_addr[*]}]
set_case_analysis 1 [get_ports {i_instr_ram_impl[mcs][0]}]
set_case_analysis 0 [get_ports {i_instr_ram_impl[mcs][1]}]
set_case_analysis 0 [get_ports {i_instr_ram_impl[mcsw]}]
set_case_analysis 0 [get_ports {i_instr_ram_impl[ret]}]
set_case_analysis 0 [get_ports {i_instr_ram_impl[pde]}]
set_case_analysis 0 [get_ports {i_instr_ram_impl[adme][0]}]
set_case_analysis 0 [get_ports {i_instr_ram_impl[adme][1]}]
set_case_analysis 1 [get_ports {i_instr_ram_impl[adme][2]}]
set_case_analysis 1 [get_ports {i_copy_ram_impl[mcs][0]}]
set_case_analysis 0 [get_ports {i_copy_ram_impl[mcs][1]}]
set_case_analysis 0 [get_ports {i_copy_ram_impl[mcsw]}]
set_case_analysis 0 [get_ports {i_copy_ram_impl[ret]}]
set_case_analysis 0 [get_ports {i_copy_ram_impl[pde]}]
set_case_analysis 0 [get_ports {i_copy_ram_impl[adme][0]}]
set_case_analysis 0 [get_ports {i_copy_ram_impl[adme][1]}]
set_case_analysis 1 [get_ports {i_copy_ram_impl[adme][2]}]


#############################
# Set False Path Statements #
#############################

set_false_path  -from [get_ports {i_*rst*}]
set_false_path  -to [get_ports {o_instr_ram_impl[prn]}]
set_false_path  -to [get_ports {o_copy_ram_impl[prn]}]


##################################
# Set Multicycle Path Statements #
##################################



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



#############################################
# Estimated loads seen externally by ports. #
#############################################
set_load -pin_load 0.030 [all_outputs]
set_port_fanout_number 3 [all_outputs]

set_driving_cell -lib_cell BUF_D4_N_S6TR_C54L08 -input_transition_rise 0.03 -input_transition_fall 0.03  [all_inputs]
