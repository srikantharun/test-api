######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Constraints for ddr_west_clock_gen_p
# Constraint Mode: func
######################################

#################
# Clock Domains #
#################
###############
# "ddr_west_clk"
###############
puts "INFO: Adding clock: 'ddr_west_clk' (800 MHz)"
create_clock -add -name ddr_west_clk -period 1.250 -waveform "0 0.625" [get_pins u_ddr_west_clock_gen/u_pll_wrapper/u_tu_pll0519a01_ln05lpe_4007002/FOUT]
set_clock_uncertainty -setup [expr 1.250 * 0.10 ] [get_clocks ddr_west_clk]
set_clock_uncertainty -hold 0.010 [get_clocks ddr_west_clk]

# Synchronous Ports



###############
# "ref_clk"
###############
puts "INFO: Adding clock: 'ref_clk' (50 MHz)"
create_clock -add -name ref_clk -period 20.000 -waveform "0 10.000" [get_ports i_ref_clk]
set_clock_uncertainty -setup [expr 20.000 * 0.10 ] [get_clocks ref_clk]
set_clock_uncertainty -hold 0.010 [get_clocks ref_clk]

# Synchronous Ports

puts "INFO: constraining 'i_syscfg_apb4_*' against 'ref_clk'"
set_input_delay -min 1.000 -clock ref_clk [get_ports i_syscfg_apb4_*]
set_input_delay -max 14.000 -clock ref_clk [get_ports i_syscfg_apb4_*]

puts "INFO: constraining 'o_syscfg_apb4_*' against 'ref_clk'"
set_output_delay -min 1.000 -clock ref_clk [get_ports o_syscfg_apb4_*]
set_output_delay -max 14.000 -clock ref_clk [get_ports o_syscfg_apb4_*]


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

set_case_analysis 0 [get_ports scan_en]
set_case_analysis 0 [get_ports test_mode]


#############################
# Set False Path Statements #
#############################



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

