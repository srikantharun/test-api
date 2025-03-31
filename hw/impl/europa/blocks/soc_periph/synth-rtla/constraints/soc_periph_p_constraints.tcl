######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Note: auto-generated with "hw/scripts/synth_constraints", do not manually edit
# Constraints for soc_periph_p
# Constraint Mode: func
######################################

#################
# Clock Domains #
#################
###############
# "periph_clk"
###############
puts "INFO: Adding clock: 'periph_clk' (100 MHz)"
create_clock -add -name periph_clk -period 10.000 -waveform "0 5.000" [get_ports i_periph_clk]
set_clock_uncertainty -setup [expr 10.000 * 0.10 ] [get_clocks periph_clk]
set_clock_uncertainty -hold 0.010 [get_clocks periph_clk]

# Synchronous Ports

puts "INFO: constraining 'i_lt_axi_s_*' against 'periph_clk'"
set_input_delay -min 0.500 -clock periph_clk [get_ports i_lt_axi_s_*]
set_input_delay -max 7.000 -clock periph_clk [get_ports i_lt_axi_s_*]
puts "INFO: constraining 'i_gpio*' against 'periph_clk'"
set_input_delay -min 0.500 -clock periph_clk [get_ports i_gpio*]
set_input_delay -max 7.000 -clock periph_clk [get_ports i_gpio*]
puts "INFO: constraining 'i_i2c_*' against 'periph_clk'"
set_input_delay -min 0.500 -clock periph_clk [get_ports i_i2c_*]
set_input_delay -max 7.000 -clock periph_clk [get_ports i_i2c_*]

puts "INFO: constraining 'o_lt_axi_s_*' against 'periph_clk'"
set_output_delay -min 0.500 -clock periph_clk [get_ports o_lt_axi_s_*]
set_output_delay -max 7.000 -clock periph_clk [get_ports o_lt_axi_s_*]
puts "INFO: constraining 'o_gpio*' against 'periph_clk'"
set_output_delay -min 0.500 -clock periph_clk [get_ports o_gpio*]
set_output_delay -max 7.000 -clock periph_clk [get_ports o_gpio*]
puts "INFO: constraining 'o_i2c_*' against 'periph_clk'"
set_output_delay -min 0.500 -clock periph_clk [get_ports o_i2c_*]
set_output_delay -max 7.000 -clock periph_clk [get_ports o_i2c_*]

###############
# "emmc_clk"
###############
puts "INFO: Adding clock: 'emmc_clk' (200 MHz)"
create_clock -add -name emmc_clk -period 5.000 -waveform "0 2.500" [get_ports i_emmc_clk]
set_clock_uncertainty -setup [expr 5.000 * 0.10 ] [get_clocks emmc_clk]
set_clock_uncertainty -hold 0.010 [get_clocks emmc_clk]

# Synchronous Ports

puts "INFO: constraining 'i_lt_axi_m_*' against 'emmc_clk'"
set_input_delay -min 0.250 -clock emmc_clk [get_ports i_lt_axi_m_*]
set_input_delay -max 3.500 -clock emmc_clk [get_ports i_lt_axi_m_*]

puts "INFO: constraining 'o_lt_axi_m_*' against 'emmc_clk'"
set_output_delay -min 0.250 -clock emmc_clk [get_ports o_lt_axi_m_*]
set_output_delay -max 3.500 -clock emmc_clk [get_ports o_lt_axi_m_*]

###############
# "ref_clk"
###############
puts "INFO: Adding clock: 'ref_clk' (50 MHz)"
create_clock -add -name ref_clk -period 20.000 -waveform "0 10.000" [get_ports i_ref_clk]
set_clock_uncertainty -setup [expr 20.000 * 0.10 ] [get_clocks ref_clk]
set_clock_uncertainty -hold 0.010 [get_clocks ref_clk]

# Synchronous Ports

puts "INFO: constraining 'i_cfg_apb4_s_*' against 'ref_clk'"
set_input_delay -min 1.000 -clock ref_clk [get_ports i_cfg_apb4_s_*]
set_input_delay -max 14.000 -clock ref_clk [get_ports i_cfg_apb4_s_*]

puts "INFO: constraining 'o_cfg_apb4_s_*' against 'ref_clk'"
set_output_delay -min 1.000 -clock ref_clk [get_ports o_cfg_apb4_s_*]
set_output_delay -max 14.000 -clock ref_clk [get_ports o_cfg_apb4_s_*]

###############
# "spi_clk"
###############
puts "INFO: Adding generated clock: 'spi_clk' from 'i_periph_clk' : divisor 2"
create_generated_clock -add -name spi_clk -divide_by 2 -source [get_ports i_periph_clk] -master_clock [get_clocks periph_clk] [get_ports o_spi_clk]


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

