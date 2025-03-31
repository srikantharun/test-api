# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

# Sanity I/O constraints for the PVE_L1 partition

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

set_driving_cell -lib_cell BUF_D4_N_S6TR_C54L08 -input_transition_rise 0.03 -input_transition_fall 0.03  [all_inputs]

# Specifies a maximum transition time of 150ps for the clock paths of all_clocks
set_max_transition 0.150 -clock_path [all_clocks]

# Reset
set_ideal_network -no_propagate [get_ports $ResetPort]
set_max_delay [expr 3.00*${ClockPeriodInternal}] -from [get_ports $ResetPort]

# Sideband
set_case_analysis 0 [get_ports scan_en]

set_case_analysis 1 [get_pins -hier */MCS[0]]
set_case_analysis 0 [get_pins -hier */MCS[1]]

set_case_analysis 1 [get_pins -hier */ADME[2]]
set_case_analysis 0 [get_pins -hier */ADME[1]]
set_case_analysis 0 [get_pins -hier */ADME[0]]

set_case_analysis 0 [get_pins -hier */PDE]



