# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

# Sanity i/o constraints for the iau ip

# Clock and reset
# 1.25 GHz
set ClockPeriodInternal 0.80
set ClockPort i_clk
set ClockName i_clk

set ResetPort i_rst_n

set AsyncInputs  " "
set AsyncOutputs " "


create_clock -add [get_ports ${ClockPort}] -name ${ClockName} -period ${ClockPeriodInternal} -waveform "0 [expr ${ClockPeriodInternal}/2]"
set_clock_uncertainty -setup [expr ${ClockPeriodInternal} * 0.05 ] [get_clocks ${ClockName}]
set_clock_uncertainty -hold 0.010 [get_clocks ${ClockName}]
set_ideal_network  [get_ports -filter {defined(clocks)}]

# I/O timing
set DelayInpMin [ expr 0.05*${ClockPeriodInternal} ]
set DelayInpMax [ expr 0.7*${ClockPeriodInternal}  ]
set DelayOupMin [ expr 0.05*${ClockPeriodInternal} ]
set DelayOupMax [ expr 0.7*${ClockPeriodInternal}  ]

set sync_inputs  [remove_from_collection [remove_from_collection [all_inputs] [ get_object_name [get_clocks {*}]]] ${AsyncInputs}]
set sync_outputs [remove_from_collection [all_outputs] ${AsyncOutputs}]

puts "INFO: constraining [get_object_name $sync_inputs] against ${ClockName}"
set_input_delay -min ${DelayInpMin} -clock ${ClockName} $sync_inputs
set_input_delay -max ${DelayInpMax} -clock ${ClockName} $sync_inputs

puts "INFO: constraining [get_object_name $sync_outputs] against ${ClockName}"
set_output_delay -min ${DelayOupMin} -clock ${ClockName} $sync_outputs
set_output_delay -max ${DelayOupMax} -clock ${ClockName} $sync_outputs

# Estimated loads seen externally by ports.
set_load -pin_load 0.030 [all_outputs]
set_port_fanout_number 3 [all_outputs]

set_driving_cell -lib_cell BUF_D4_N_S6TR_C54L08 -input_transition_rise 0.03 -input_transition_fall 0.03  [all_inputs]

# Reset
set_ideal_network -no_propagate [get_ports $ResetPort]
set_max_delay [expr 3.00*${ClockPeriodInternal}] -from [get_ports $ResetPort]

# Sideband

set_case_analysis 0 [get_ports i_cid[0]]
set_case_analysis 0 [get_ports i_cid[1]]
set_case_analysis 0 [get_ports i_cid[2]]

set_case_analysis 0 [get_ports i_block_id[0]]
set_case_analysis 0 [get_ports i_block_id[1]]
set_case_analysis 0 [get_ports i_block_id[2]]
set_case_analysis 0 [get_ports i_block_id[3]]
set_case_analysis 0 [get_ports i_block_id[4]]
set_case_analysis 0 [get_ports i_block_id[5]]
set_case_analysis 0 [get_ports i_block_id[6]]
set_case_analysis 0 [get_ports i_block_id[7]]
