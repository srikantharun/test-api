######################################
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
######################################
# Constraints for ai_core_p
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

# Synchronous Ports

puts "INFO: constraining '{i_noc_* i_tok_* i_reserved}' against 'fast_clk'"
set_input_delay -min 0.042 -clock fast_clk [get_ports {i_noc_* i_tok_* i_reserved}]
set_input_delay -max 0.583 -clock fast_clk [get_ports {i_noc_* i_tok_* i_reserved}]

puts "INFO: constraining '{o_noc_* o_tok_* o_reserved o_aic_obs o_irq}' against 'fast_clk'"
set_output_delay -min 0.042 -clock fast_clk [get_ports {o_noc_* o_tok_* o_reserved o_aic_obs o_irq}]
set_output_delay -max 0.583 -clock fast_clk [get_ports {o_noc_* o_tok_* o_reserved o_aic_obs o_irq}]

###############
# "ref_clk"
###############
puts "INFO: Adding clock: 'ref_clk' (50 MHz)"
create_clock -add -name ref_clk -period 20.000 -waveform "0 10.000" [get_ports i_ref_clk]

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

set_ideal_network -no_propagate [get_ports *_rst_n]

################################
# Set Case Analysis Statements #
################################

set_case_analysis 0 [get_ports i_cid*]
set_case_analysis 0 [get_pins u_pctl/u_ao_csr/u_mem_power_mode*ret*/q]
set_case_analysis 0 [get_pins u_pctl/u_ao_csr/u_mem_power_mode*pde*/q]
set_case_analysis 0 [get_ports test_mode]

#############################
# Set False Path Statements #
#############################

set_false_path  -from [get_ports {io_*_ts}] 
set_false_path  -from [get_ports {i_*rst* i_*async* i_inter_core_sync}] 
set_false_path  -to [get_ports {o_*rst* o_*async*}] 
set_false_path  -through [get_pins -of_objects [get_cell -hier  *tc_lib_seq_sync* -filter full_name=~*tc_lib_seq_sync*] -filter "full_name=~*/D"] 
set_false_path  -from [get_ports i_ref_clk] -to [get_ports i_clk] 

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


#############################################
# Estimated loads seen externally by ports. #
#############################################
set_load -pin_load 0.030 [all_outputs]
set_port_fanout_number 3 [all_outputs]

set_driving_cell -lib_cell BUF_D4_N_S6TR_C54L08 -input_transition_rise 0.03 -input_transition_fall 0.03  [all_inputs]
