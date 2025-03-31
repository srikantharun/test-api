# Helper script to create a vectorless activity file (VAF)
# written by Helmut Biederbick @ANSYS, July 2016 to May 2020
# This script extracts its values from 2 sources:
# - frequency of clock roots from the setup (either via SDC or 'SetClockNet'
# - average activity (or frequency) and duty cycle of other nets from settings below.
#  ==> These can be extracted from a script 'extract_average_activity.tcl' from
#      an average power analysis PDB.
#
# !! It is important that the highest frequencies match between:
# - the current clock definitions
# and
# - the (extracted/specified) average activity values (if the activity is used)
# as activity values are related/normalized to the highest frequency.
# The net with the highest frequency (usually a clock net) receives an activity of "2",
# and the activity of other nets are scaled accordingly.
# ==> If these don't match then the activity values need to be scaled accordingly.

# ##############################################################################
# ####################### Setting up Vectorless approach #######################
# ##############################################################################

# Activity scaling factor; defaults to "1". It only scales activity values, not frequency!
set activity_scaling_factor 1 ; # default is '1'

# These values for activity and duty_cycle need to be customized
# A value of "-1" for activity and frequency skips the annotation for that net type.
# If both values "activity" and "frequency" are specified (i.e. not "-1"), then the
# activity value is being chosen.

set primary_input_activity 0
set primary_input_frequency -1
set primary_input_duty_cycle 0

set flop_output_activity 0
set flop_output_frequency -1
set flop_output_duty_cycle 0

set memory_output_activity 0
set memory_output_frequency -1
set memory_output_duty_cycle 0

set blackbox_output_activity 0
set blackbox_output_frequency -1
set blackbox_output_duty_cycle 0

set cg_enable_activity 0
set cg_enable_frequency  -1
set cg_enable_duty_cycle 0

set other_net_activity 0
set other_net_frequency -1
set other_net_duty_cycle 0

puts "\nGenerating vectorless activity file based on clock definitions and provided activity/frequency/duty cycle values..."

# Target file containing vectorless stimulus data.
set vaf_file [open [pa_set vectorless_input_file] w]

source ${script_dir}/base/generate_vaf_file.tcl

# Additional settings for the vectorless activity file.
# To add specific overrides, for example to enforce a certain mode of operation.

puts $vaf_file "\n# specific overrides: enforce functional mode"
puts $vaf_file "SetStimulus -net {*g_clkdiv*u_clkdiv*enable_clock} -duty 1 -override true"

if { [info exists vaf_idle_directive] } {
  foreach l ${vaf_idle_directive} {
    puts $vaf_file $l
  }
}

close $vaf_file

puts "Vectorless activity file successfully generated.\n"

return
