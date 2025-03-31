######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Note: auto-generated with "hw/scripts/synth_constraints", do not manually edit
# Constraints for apu_p
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

puts "INFO: constraining '{i_cores_* i_*_axi_* i_tok_*}' against 'fast_clk'"
set_input_delay -min 0.050 -clock fast_clk [get_ports {i_cores_* i_*_axi_* i_tok_*}]
set_input_delay -max 0.700 -clock fast_clk [get_ports {i_cores_* i_*_axi_* i_tok_*}]

puts "INFO: constraining '{o_cores_* o_*_axi_* o_tok_*}' against 'fast_clk'"
set_output_delay -min 0.050 -clock fast_clk [get_ports {o_cores_* o_*_axi_* o_tok_*}]
set_output_delay -max 0.700 -clock fast_clk [get_ports {o_cores_* o_*_axi_* o_tok_*}]

###############
# "ref_clk"
###############
puts "INFO: Adding clock: 'ref_clk' (50 MHz)"
create_clock -add -name ref_clk -period 20.000 -waveform "0 10.000" [get_ports i_ref_clk]
set_clock_uncertainty -setup [expr 20.000 * 0.10 ] [get_clocks ref_clk]
set_clock_uncertainty -hold 0.010 [get_clocks ref_clk]

# Synchronous Ports

puts "INFO: constraining 'i_cfg_apb4_*' against 'ref_clk'"
set_input_delay -min 1.000 -clock ref_clk [get_ports i_cfg_apb4_*]
set_input_delay -max 14.000 -clock ref_clk [get_ports i_cfg_apb4_*]

puts "INFO: constraining 'o_cfg_apb4_*' against 'ref_clk'"
set_output_delay -min 1.000 -clock ref_clk [get_ports o_cfg_apb4_*]
set_output_delay -max 14.000 -clock ref_clk [get_ports o_cfg_apb4_*]


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

set_ideal_network -no_propagate [get_ports i_ao_rst_n]
set_ideal_network -no_propagate [get_ports i_global_rst_n]


################################
# Set Case Analysis Statements #
################################

set_case_analysis 0 [get_ports test_mode]
set_case_analysis 1 [get_pins *u_pctl/g_clkdiv[*].u_clkdiv/u_clk_gate/u_tc_lib_clk_en/ECK ]


#############################
# Set False Path Statements #
#############################

set_false_path  -from [get_ports {i_ao_rst_n i_global_rst_n}]
set_false_path  -from [get_ports {i_clock_throttle i_thermal_throttle i_cores_nmi i_aic_stoptime i_irq__*}]
set_false_path  -to [get_ports {o_aic_msip o_aic_mtip}]
set_false_path  -from [get_ports {i_noc_async_*}]
set_false_path  -to [get_ports {o_noc_async_* o_noc_clken o_noc_rst_n}]


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
