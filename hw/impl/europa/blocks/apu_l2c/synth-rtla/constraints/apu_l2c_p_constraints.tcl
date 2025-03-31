######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Note: auto-generated with "hw/scripts/synth_constraints", do not manually edit
# Constraints for apu_l2c_p
# Constraint Mode: func
######################################

#################
# Clock Domains #
#################
###############
# "l2c_clk"
###############
puts "INFO: Adding clock: 'l2c_clk' (1000 MHz)"
create_clock -add -name l2c_clk -period 1.000 -waveform "0 0.500" [get_ports i_clk]
set_clock_uncertainty -setup [expr 1.000 * 0.10 ] [get_clocks l2c_clk]
set_clock_uncertainty -hold 0.010 [get_clocks l2c_clk]

# Synchronous Ports

puts "INFO: constraining '{i_core*_m0_* i_core*_m2_* i_core*_coherent_*}' against 'l2c_clk'"
set_input_delay -min 0.050 -clock l2c_clk [get_ports {i_core*_m0_* i_core*_m2_* i_core*_coherent_*}]
set_input_delay -max 0.700 -clock l2c_clk [get_ports {i_core*_m0_* i_core*_m2_* i_core*_coherent_*}]

puts "INFO: constraining '{o_core*_m0_* o_core*_m2_* o_core*_coherent_*}' against 'l2c_clk'"
set_output_delay -min 0.050 -clock l2c_clk [get_ports {o_core*_m0_* o_core*_m2_* o_core*_coherent_*}]
set_output_delay -max 0.700 -clock l2c_clk [get_ports {o_core*_m0_* o_core*_m2_* o_core*_coherent_*}]

###############
# "l2c_banks_clk"
###############
puts "INFO: Adding clock: 'l2c_banks_clk' (500 MHz)"
create_clock -add -name l2c_banks_clk -period 2.000 -waveform "0 1.000" [get_ports i_l2c_banks_clk]
set_clock_uncertainty -setup [expr 2.000 * 0.10 ] [get_clocks l2c_banks_clk]
set_clock_uncertainty -hold 0.010 [get_clocks l2c_banks_clk]

# Synchronous Ports



###############
# "bus_clk"
###############
puts "INFO: Adding clock: 'bus_clk' (1000 MHz)"
create_clock -add -name bus_clk -period 1.000 -waveform "0 0.500" [get_ports i_aclk]
set_clock_uncertainty -setup [expr 1.000 * 0.10 ] [get_clocks bus_clk]
set_clock_uncertainty -hold 0.010 [get_clocks bus_clk]

# Synchronous Ports

puts "INFO: constraining '{i_iocp_* i_mem_* i_mmio_* i_plmt_* i_core*_m1_axi_*}' against 'bus_clk'"
set_input_delay -min 0.050 -clock bus_clk [get_ports {i_iocp_* i_mem_* i_mmio_* i_plmt_* i_core*_m1_axi_*}]
set_input_delay -max 0.700 -clock bus_clk [get_ports {i_iocp_* i_mem_* i_mmio_* i_plmt_* i_core*_m1_axi_*}]

puts "INFO: constraining '{o_iocp_* o_mem_* o_mmio_* o_plmt_* o_core*_m1_axi_*}' against 'bus_clk'"
set_output_delay -min 0.050 -clock bus_clk [get_ports {o_iocp_* o_mem_* o_mmio_* o_plmt_* o_core*_m1_axi_*}]
set_output_delay -max 0.700 -clock bus_clk [get_ports {o_iocp_* o_mem_* o_mmio_* o_plmt_* o_core*_m1_axi_*}]


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
set_ideal_network -no_propagate [get_ports i_arst_n]


################################
# Set Case Analysis Statements #
################################

set_case_analysis 0 [get_ports scan_en]
set_case_analysis 0 [get_ports test_mode]


#############################
# Set False Path Statements #
#############################

set_false_path  -from [get_ports {i_rst_n i_arst_n}]
set_false_path  -from [get_ports {i_l2c_ctrl i_l2c_disable_init}]
set_false_path  -to [get_ports {o_l2c_ctrl o_l2c_err_int}]


##################################
# Set Multicycle Path Statements #
##################################

set_multicycle_path 2 -start  -from [get_clocks "l2c_clk"] -to [get_clocks "l2c_banks_clk"]
set_multicycle_path 2 -end  -from [get_clocks "l2c_banks_clk"] -to [get_clocks "l2c_clk"]


#######################
# Define the IO Delay #
#######################

puts "INFO: constraining '{i_core*_m1_axi_*}' against 'bus_clk'"
set_input_delay  -max 0.25 -clock bus_clk [get_ports {i_core*_m1_axi_*}]
puts "INFO: constraining '{o_core*_m1_axi_*}' against 'bus_clk'"
set_output_delay -max 0.25 -clock bus_clk [get_ports {o_core*_m1_axi_*}]
puts "INFO: constraining '{i_core*_m0_* i_core*_m2_*}' against 'l2c_clk'"
set_input_delay  -max 0.25 -clock l2c_clk [get_ports {i_core*_m0_* i_core*_m2_*}]
puts "INFO: constraining '{o_core*_m0_* o_core*_m2_*}' against 'l2c_clk'"
set_output_delay -max 0.25 -clock l2c_clk [get_ports {o_core*_m0_* o_core*_m2_*}]


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
