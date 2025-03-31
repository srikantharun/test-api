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

# Target file containing vectorless stimulus data.
puts $vaf_file "#Generate Vectorless Activity File (VAF)\n "

# Default activity.
if { $other_net_activity != -1 } {
  if { $other_net_frequency != -1 } {
    puts "Warning: both 'activity' and 'frequency' values specified for other nets. Assigning 'activity' value to the VAF file."
  }
  puts $vaf_file "SetStimulus -net * -exclude_type \"clock cg_enable primary_input\" -activity [expr $other_net_activity * $activity_scaling_factor] -duty $other_net_duty_cycle"
} elseif { $other_net_frequency != -1 } {
  puts $vaf_file "SetStimulus -net * -exclude_type \"clock cg_enable primary_input\" -frequency $other_net_frequency -duty $other_net_duty_cycle"
}

# Primary inputs.
if { $primary_input_activity != -1 } {
  if { $primary_input_frequency != -1 } {
    puts "Warning: both 'activity' and 'frequency' values specified for primary input nets. Assigning 'activity' value to the VAF file."
  }
  puts $vaf_file "SetStimulus -net * -signal_type primary_input -exclude_type clock -activity [expr $primary_input_activity * $activity_scaling_factor] -duty $primary_input_duty_cycle"
} elseif { $primary_input_frequency != -1 } {
  puts $vaf_file "SetStimulus -net * -signal_type primary_input -exclude_type clock -frequency $primary_input_frequency -duty $primary_input_duty_cycle"
}

# Register outputs.
if { $flop_output_activity != -1 } {
  if { $flop_output_frequency != -1 } {
    puts "Warning: both 'activity' and 'frequency' values specified for register output nets. Assigning 'activity' value to the VAF file."
  }
  puts $vaf_file "SetStimulus -instance_type register -signal_type output -exclude_type clock -activity [expr $flop_output_activity * $activity_scaling_factor] -duty $flop_output_duty_cycle"
} elseif { $flop_output_frequency != -1 } {
  puts $vaf_file "SetStimulus -instance_type register -signal_type output -exclude_type clock -frequency $flop_output_frequency -duty $flop_output_duty_cycle"
}

# Memory outputs.
if { $memory_output_activity != -1 } {
  if { $memory_output_frequency != -1 } {
    puts "Warning: both 'activity' and 'frequency' values specified for memory output nets. Assigning 'activity' value to the VAF file."
  }
  puts $vaf_file "SetStimulus -instance_type memory -signal_type output -exclude_type clock -activity [expr $memory_output_activity * $activity_scaling_factor] -duty $memory_output_duty_cycle"
} elseif { $memory_output_frequency != -1 } {
  puts $vaf_file "SetStimulus -instance_type memory -signal_type output -exclude_type clock -frequency $memory_output_frequency -duty $memory_output_duty_cycle"
}

# Blackbox outputs.
if { $blackbox_output_activity != -1 } {
  if { $blackbox_output_frequency != -1 } {
    puts "Warning: both 'activity' and 'frequency' values specified for blackbox output nets. Assigning 'activity' value to the VAF file."
  }
  puts $vaf_file "SetStimulus -instance_type black_box -signal_type output -exclude_type clock -activity [expr $blackbox_output_activity * $activity_scaling_factor] -duty $blackbox_output_duty_cycle"
} elseif { $blackbox_output_frequency != -1 } {
  puts $vaf_file "SetStimulus -instance_type black_box -signal_type output -exclude_type clock -frequency $blackbox_output_frequency -duty $blackbox_output_duty_cycle"
}

# Clock gate enables.
if { $cg_enable_activity != -1 } {
  if { $cg_enable_frequency != -1 } {
    puts "Warning: both 'activity' and 'frequency' values specified for clock gate enable nets. Assigning 'activity' value to the VAF file."
  }
  puts $vaf_file "SetStimulus -instance_type icgc -signal_type cg_enable -exclude_type clock -activity [expr $cg_enable_activity * $activity_scaling_factor] -duty $cg_enable_duty_cycle"
} elseif { $cg_enable_frequency != -1 } {
  puts $vaf_file "SetStimulus -instance_type icgc -signal_type cg_enable -exclude_type clock -frequency $cg_enable_frequency -duty $cg_enable_duty_cycle"
}

# Clock net modeling.
puts $vaf_file "\n#Set activity on clock nets"
if { $use_sdc_input_for_clocks } {
  # Clocks are defined via SDC file ==> include VAF file with clock net frequencies.
  puts $vaf_file "source ${WORK_DIR}/${filename}_ReadSDC${elab_suffix}.vaf"
} else {
  # Extract clock information and frequency from '$CLOCK_LIST' from 'config.tcl'.
  set clocks_freq ""
  foreach clock_def $CLOCK_LIST {
    set clock_name [lindex $clock_def 0]
    set clock_freq [lindex $clock_def 1]
    if { $clock_freq != 1 } {
      # Skip all clocks without a clock frequency for 'SetStimumus'.
      puts $vaf_file "SetStimulus -net $clock_name -frequency $clock_freq"
      lappend clocks_freq [list $clock_name $clock_freq]
    }
  }
  if { $clocks_freq == "" } {
    # at least one clock with a frequency is required.
    puts "Error: All clocks are defined without a frequency! We need at least 1 clock with defined frequency! Exiting ..."
    close $vaf_file
    exit 1
  }
}
