######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Constraints for aic_mid_p
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

puts "INFO: constraining '{i_*_tok_* i_cfg_* i_*_axis_*}' against 'fast_clk'"
set_input_delay -min 0.042 -clock fast_clk [get_ports {i_*_tok_* i_cfg_* i_*_axis_*}]
set_input_delay -max 0.583 -clock fast_clk [get_ports {i_*_tok_* i_cfg_* i_*_axis_*}]

puts "INFO: constraining '{o_imc* o_*_obs o_ts o_acd_sync o_irq o_*_tok_* o_cfg_* o_*_axis_*}' against 'fast_clk'"
set_output_delay -min 0.042 -clock fast_clk [get_ports {o_imc* o_*_obs o_ts o_acd_sync o_irq o_*_tok_* o_cfg_* o_*_axis_*}]
set_output_delay -max 0.583 -clock fast_clk [get_ports {o_imc* o_*_obs o_ts o_acd_sync o_irq o_*_tok_* o_cfg_* o_*_axis_*}]

###############
# "pll_clk"
###############
puts "INFO: Adding clock: 'pll_clk' (1200 MHz)"
create_clock -add -name pll_clk -period 0.833 -waveform "0 0.417" [get_ports i_c2c_clk]
set_clock_uncertainty -setup [expr 0.833 * 0.10 ] [get_clocks pll_clk]
set_clock_uncertainty -hold 0.010 [get_clocks pll_clk]

# Synchronous Ports



###############
# "ref_clk"
###############
puts "INFO: Adding clock: 'ref_clk' (50 MHz)"
create_clock -add -name ref_clk -period 20.000 -waveform "0 10.000" [get_ports i_ref_clk]
set_clock_uncertainty -setup [expr 20.000 * 0.10 ] [get_clocks ref_clk]
set_clock_uncertainty -hold 0.010 [get_clocks ref_clk]

# Synchronous Ports



###############
# "jtag_clk"
###############
puts "INFO: Adding clock: 'jtag_clk' (100 MHz)"
create_clock -add -name jtag_clk -period 10.000 -waveform "0 5.000" [get_ports ijtag_tck]
set_clock_uncertainty -setup [expr 10.000 * 0.10 ] [get_clocks jtag_clk]
set_clock_uncertainty -hold 0.010 [get_clocks jtag_clk]

# Synchronous Ports




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

set_ideal_network -no_propagate [get_ports {i_rst_n i_ref_rst_n ijtag_reset}]


################################
# Set Case Analysis Statements #
################################

set_case_analysis 0 [get_ports scan_en]
set_case_analysis 0 [get_ports test_mode]
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

