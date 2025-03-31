######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Constraints for aic_ls_p
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

puts "INFO: constraining '{i_*_axi_* i_*_axis_* i_rvv_* i_*_tok_*         i_mid_* i_did_* }' against 'fast_clk'"
set_input_delay -min 0.042 -clock fast_clk [get_ports {i_*_axi_* i_*_axis_* i_rvv_* i_*_tok_*         i_mid_* i_did_* }]
set_input_delay -max 0.583 -clock fast_clk [get_ports {i_*_axi_* i_*_axis_* i_rvv_* i_*_tok_*         i_mid_* i_did_* }]

puts "INFO: constraining '{o_*_axi_* o_*_axis_* o_rvv_* o_*_tok_* o_dmc_* o_mid_* o_did_* }' against 'fast_clk'"
set_output_delay -min 0.042 -clock fast_clk [get_ports {o_*_axi_* o_*_axis_* o_rvv_* o_*_tok_* o_dmc_* o_mid_* o_did_* }]
set_output_delay -max 0.583 -clock fast_clk [get_ports {o_*_axi_* o_*_axis_* o_rvv_* o_*_tok_* o_dmc_* o_mid_* o_did_* }]


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

set_ideal_network -no_propagate [get_ports *_rst_n]

################################
# Set Case Analysis Statements #
################################

set_case_analysis 0 [get_ports *ret]
set_case_analysis 0 [get_ports *pde]
set_case_analysis 0 [get_ports scan_en]
set_case_analysis 0 [get_ports test_mode]
set_case_analysis 0 [get_ports i_cid*]

#############################
# Set False Path Statements #
#############################

set_false_path  -from [get_ports {i_rst_n}] 

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

set_optimize_registers -modules [get_modules *ring_buffer*] true

#############################################
# Estimated loads seen externally by ports. #
#############################################
set_load -pin_load 0.030 [all_outputs]
set_port_fanout_number 3 [all_outputs]

set_driving_cell -lib_cell BUF_D4_N_S6TR_C54L08 -input_transition_rise 0.03 -input_transition_fall 0.03  [all_inputs]
