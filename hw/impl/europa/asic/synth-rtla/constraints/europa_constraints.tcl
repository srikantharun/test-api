######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Note: auto-generated with "hw/scripts/synth_constraints", do not manually edit
# Constraints for europa
# Constraint Mode: func
######################################

#################
# Clock Domains #
#################
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
create_clock -add -name jtag_clk -period 10.000 -waveform "0 5.000" [get_ports i_tck]
set_clock_uncertainty -setup [expr 10.000 * 0.10 ] [get_clocks jtag_clk]
set_clock_uncertainty -hold 0.010 [get_clocks jtag_clk]

# Synchronous Ports



###############
# "spi_clk"
###############
puts "INFO: Adding clock: 'spi_clk' (50 MHz)"
create_clock -add -name spi_clk -period 20.000 -waveform "0 10.000" [get_ports i_spi_clk_in]
set_clock_uncertainty -setup [expr 20.000 * 0.10 ] [get_clocks spi_clk]
set_clock_uncertainty -hold 0.010 [get_clocks spi_clk]

# Synchronous Ports



###############
# "scan_0_clk"
###############
puts "INFO: Adding clock: 'scan_0_clk' (100 MHz)"
create_clock -add -name scan_0_clk -period 10.000 -waveform "0 5.000" [get_ports i_ssn_bus_0_clk]
set_clock_uncertainty -setup [expr 10.000 * 0.10 ] [get_clocks scan_0_clk]
set_clock_uncertainty -hold 0.010 [get_clocks scan_0_clk]

# Synchronous Ports



###############
# "scan_1_clk"
###############
puts "INFO: Adding clock: 'scan_1_clk' (100 MHz)"
create_clock -add -name scan_1_clk -period 10.000 -waveform "0 5.000" [get_ports i_ssn_bus_1_clk]
set_clock_uncertainty -setup [expr 10.000 * 0.10 ] [get_clocks scan_1_clk]
set_clock_uncertainty -hold 0.010 [get_clocks scan_1_clk]

# Synchronous Ports



###############
# "pcie_diff_m_clk"
###############
puts "INFO: Adding clock: 'pcie_diff_m_clk' (100 MHz)"
create_clock -add -name pcie_diff_m_clk -period 10.000 -waveform "0 5.000" [get_ports i_ref_pad_clk_m]
set_clock_uncertainty -setup [expr 10.000 * 0.10 ] [get_clocks pcie_diff_m_clk]
set_clock_uncertainty -hold 0.010 [get_clocks pcie_diff_m_clk]

# Synchronous Ports



###############
# "pcie_diff_p_clk"
###############
puts "INFO: Adding clock: 'pcie_diff_p_clk' (100 MHz)"
create_clock -add -name pcie_diff_p_clk -period 10.000 -waveform "0 5.000" [get_ports i_ref_pad_clk_p]
set_clock_uncertainty -setup [expr 10.000 * 0.10 ] [get_clocks pcie_diff_p_clk]
set_clock_uncertainty -hold 0.010 [get_clocks pcie_diff_p_clk]

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

set_ideal_network -no_propagate [get_ports i_por_rst_n]
set_ideal_network -no_propagate [get_ports i_trst_n]


################################
# Set Case Analysis Statements #
################################



#############################
# Set False Path Statements #
#############################

set_false_path  -from [get_ports {i_por_rst_n i_trst_n}] 


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
