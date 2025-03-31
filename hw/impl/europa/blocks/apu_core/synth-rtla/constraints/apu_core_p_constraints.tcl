######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Note: auto-generated with "hw/scripts/synth_constraints", do not manually edit
# Constraints for apu_core_p
# Constraint Mode: func
######################################

#################
# Clock Domains #
#################
###############
# "fast_clk"
###############
puts "INFO: Adding clock: 'fast_clk' (1000 MHz)"
create_clock -add -name fast_clk -period 1.000 -waveform "0 0.500" [get_ports i_clk]
set_clock_uncertainty -setup [expr 1.000 * 0.10 ] [get_clocks fast_clk]
set_clock_uncertainty -hold 0.010 [get_clocks fast_clk]

# Synchronous Ports

puts "INFO: constraining '{i_dcu_* i_icu_* i_mpipe_axi_* i_coherent_state}' against 'fast_clk'"
set_input_delay -min 0.050 -clock fast_clk [get_ports {i_dcu_* i_icu_* i_mpipe_axi_* i_coherent_state}]
set_input_delay -max 0.700 -clock fast_clk [get_ports {i_dcu_* i_icu_* i_mpipe_axi_* i_coherent_state}]

puts "INFO: constraining '{o_dcu_* o_icu_* o_mpipe_axi_* o_coherent_enable o_wfi_mode}' against 'fast_clk'"
set_output_delay -min 0.050 -clock fast_clk [get_ports {o_dcu_* o_icu_* o_mpipe_axi_* o_coherent_enable o_wfi_mode}]
set_output_delay -max 0.700 -clock fast_clk [get_ports {o_dcu_* o_icu_* o_mpipe_axi_* o_coherent_enable o_wfi_mode}]


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

set_case_analysis 0 [get_ports scan_en]
set_case_analysis 0 [get_ports test_mode]


#############################
# Set False Path Statements #
#############################

set_false_path  -from [get_ports {i_rst_n}]
set_false_path  -from [get_ports {i_core_ctrl}]
set_false_path  -to [get_ports {o_core_ctrl}]
set_false_path  -from [get_ports {i_*cache_disable_init}]
set_false_path  -from [get_ports {i_debugint i_hart_id i_reset_vector i_resethaltreq}]
set_false_path  -to [get_ports {o_hart_unavail o_hart_under_reset}]
set_false_path  -from [get_ports {i_meip i_msip i_mtip i_nmi i_seip}]
set_false_path  -to [get_ports {o_stoptime}]


##################################
# Set Multicycle Path Statements #
##################################



#######################
# Define the IO Delay #
#######################

puts "INFO: constraining '{i_icu_*}' against 'fast_clk'"
set_input_delay  -max 0.5 -clock fast_clk [get_ports {i_icu_*}]
puts "INFO: constraining '{o_icu_*}' against 'fast_clk'"
set_output_delay -max 0.5 -clock fast_clk [get_ports {o_icu_*}]
puts "INFO: constraining '{i_dcu_*}' against 'fast_clk'"
set_input_delay  -max 0.25 -clock fast_clk [get_ports {i_dcu_*}]
puts "INFO: constraining '{o_dcu_*}' against 'fast_clk'"
set_output_delay -max 0.25 -clock fast_clk [get_ports {o_dcu_*}]


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
