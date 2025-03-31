# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

# Sanity i/o constraints for the L2 partition

# Fast Clock
# 1.2 GHz
set ClockPeriodInternal 0.833
set ClockPort i_clk
set ClockName i_clk

create_clock -add [get_ports ${ClockPort}] -name ${ClockName} -period ${ClockPeriodInternal} -waveform "0 [expr ${ClockPeriodInternal}/2]"
set_clock_uncertainty -setup [expr ${ClockPeriodInternal} * 0.05 ] [get_clocks ${ClockName}]
set_clock_uncertainty -hold 0.010 [get_clocks ${ClockName}]
set_ideal_network  [get_ports -filter {defined(clocks)}]

set DelayInpMin [ expr 0.05*${ClockPeriodInternal} ]
set DelayInpMax [ expr 0.3*${ClockPeriodInternal}  ]
set DelayOupMin [ expr 0.05*${ClockPeriodInternal} ]
set DelayOupMax [ expr 0.7*${ClockPeriodInternal}  ]

# Ref Clock
# 50 MHz
set RefClockPeriodInternal 20
set RefClockPort i_ref_clk
set RefClockName i_ref_clk

create_clock -add [get_ports ${RefClockPort}] -name ${RefClockName} -period ${RefClockPeriodInternal} -waveform "0 [expr ${RefClockPeriodInternal}/2]"
set_clock_uncertainty -setup [expr ${RefClockPeriodInternal} * 0.05 ] [get_clocks ${RefClockName}]
set_clock_uncertainty -hold 0.010 [get_clocks ${RefClockName}]
set_ideal_network  [get_ports -filter {defined(clocks)}]

# TODO: @(manuel.oliveira): APB constraints are relaxed since we have a feedthrough on AO CSRs, once fixed, we can apply 70% rule
set RefDelayInpMin [ expr 0.05*${RefClockPeriodInternal} ]
set RefDelayInpMax [ expr 0.2*${RefClockPeriodInternal}  ]
set RefDelayOupMin [ expr 0.05*${RefClockPeriodInternal} ]
set RefDelayOupMax [ expr 0.2*${RefClockPeriodInternal}  ]

# Resets
set AOResetPort i_rst_n
set GlobalResetPort i_global_rst_n

# I/O timing
# Fast clock sync
set fast_sync_inputs [get_ports "i_ht_axi_*"]
append_to_collection fast_sync_inputs [get_ports "i_noc_*"]

set fast_sync_outputs [get_ports "o_ht_axi_*"]
append_to_collection fast_sync_outputs [get_ports "o_noc_*"]

puts "INFO: constraining [get_object_name $fast_sync_inputs] against ${ClockName}"
set_input_delay -min ${DelayInpMin} -clock ${ClockName} $fast_sync_inputs
set_input_delay -max ${DelayInpMax} -clock ${ClockName} $fast_sync_inputs

puts "INFO: constraining [get_object_name $fast_sync_outputs] against ${ClockName}"
set_output_delay -min ${DelayOupMin} -clock ${ClockName} $fast_sync_outputs
set_output_delay -max ${DelayOupMax} -clock ${ClockName} $fast_sync_outputs

# Ref clock sync
set ref_sync_inputs [get_ports "i_cfg_apb4_*"]

set ref_sync_outputs [get_ports "o_cfg_apb4_*"]

puts "INFO: constraining [get_object_name $ref_sync_inputs] against ${RefClockName}"
set_input_delay -min ${RefDelayInpMin} -clock ${RefClockName} $ref_sync_inputs
set_input_delay -max ${RefDelayInpMax} -clock ${RefClockName} $ref_sync_inputs

puts "INFO: constraining [get_object_name $ref_sync_outputs] against ${RefClockName}"
set_output_delay -min ${RefDelayOupMin} -clock ${RefClockName} $ref_sync_outputs
set_output_delay -max ${RefDelayOupMax} -clock ${RefClockName} $ref_sync_outputs

# Estimated loads seen externally by ports.
set_load -pin_load 0.030 [all_outputs]
set_port_fanout_number 3 [all_outputs]

set_driving_cell -lib_cell BUF_D4_N_S6TR_C54L08 -input_transition_rise 0.03 -input_transition_fall 0.03  [all_inputs]

# Reset
set_ideal_network -no_propagate [get_ports $AOResetPort]
set_max_delay [expr 60] -from [get_ports $AOResetPort]

set_ideal_network -no_propagate [get_ports $GlobalResetPort]
set_max_delay [expr 60] -from [get_ports $GlobalResetPort]

# Async ports
set async_inputs  [get_ports "i_*rst*"]
append_to_collection async_inputs [get_ports "i_*async*"]
set async_outputs [get_ports "o_*rst*"]
append_to_collection async_outputs [get_ports "o_*async*"]
append_to_collection async_outputs [get_ports "o_noc_clken"]

set_false_path -from $async_inputs
set_false_path -to $async_outputs

set_false_path -through [get_pins -of_objects [get_cell -hier  *tc_lib_seq_sync* -filter full_name=~*tc_lib_seq_sync*] -filter "full_name=~*/D"]
set_false_path -from $RefClockName -to $ClockName

# Sideband
set_case_analysis 0 [get_ports scan_en]
set_case_analysis 0 [get_ports test_mode]

set_case_analysis 0 [get_pins -hier */RET]
set_case_analysis 0 [get_pins -hier */PDE]

set_case_analysis 1 [get_pins {*u_pppmu/g_clkdiv[*].u_clkdiv/u_clk_gate/u_tc_lib_clk_en/E}]
set_case_analysis 1 [get_pins {*u_l2_impl/u_l2_gdr/u_l2_mem/g_bank[*].u_l2_bank/g_ram[*].u_l2_ram/g_sram[*].u_l2_ram_wrapper/u_clk_gate_pwr/u_tc_lib_clk_en/E}]
