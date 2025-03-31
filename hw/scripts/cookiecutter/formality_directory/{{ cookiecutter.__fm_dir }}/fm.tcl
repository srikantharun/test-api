# common setup
source run.tcl

#TODO: update PD release comparison values after discussion
#set GFTECH cln12ffc/tsmc
set GFVAR_DESIGN(name) {{ cookiecutter.block_name }}_p
set DESIGN_NAME ${GFVAR_DESIGN(name)}  ;#  The name of the top-level design

set CUR_PATH [ file dirname [ file normalize [ info script ] ] ]

set REPO_ROOT [exec git rev-parse --show-toplevel]
set RTL_PATH $::env(REPO_ROOT)

set REPORTS_DIR "$fm_work_path/reports"
set RESULTS_DIR "$fm_work_path/results"
set RELEASE_DIR "$fm_work_path/../release"
set RELEASE_DIR_SIGN "$@release_path_ini@"

file mkdir ${REPORTS_DIR}
file mkdir ${RESULTS_DIR}
#file mkdir ${RELEASE_DIR}

set IP_PATH $RTL_PATH/hw/impl/europa/blocks/{{ cookiecutter.block_name }}/
set MEM_IP {{ cookiecutter.block_name }}

set eda_tool formality

set NETLIST_TYPE $::env(NETLIST_TYPE)
puts "-> The netlist type is $NETLIST_TYPE"

#TODO: DFT flow
set DFT 0

################
# Bender setup #
################
set BENDER_MANI_LOC [list -d $IP_PATH/rtl]
set BENDER_ARGS [list template --template ${RTL_PATH}/hw/scripts/bender_templates/formality_tcl.tera -t synopsys -t formality -t synthesis -t rtl -t asic -t sf5a]

if {$DFT == 1} {
  if {$NETLIST_TYPE == "rtl_dft"} {
    puts "WARNING: DFT=1 argument ignored for the specification design because NETLIST_TYPE=rtl_dft"
  } else {
    lappend BENDER_ARGS -t dft
  }
}

if {$NETLIST_TYPE == "rtl_dft"} {
  lappend BENDER_IMPL_ARGS -t dft
}

##############
# Bender run #
##############
exec bender update {*}$BENDER_MANI_LOC
# Call the program "bender" and generate a TCL script

set analyze_script [exec bender script {*}$BENDER_MANI_LOC {*}$BENDER_ARGS]

# Open the file for writing

set fh [open $REPORTS_DIR/analyze.tcl "w"]
# Write the content to the file and to stdout
puts $fh $analyze_script
puts $analyze_script
# Close the file
close $fh

# RTL-to-RTL impl analyze script
if {$NETLIST_TYPE == "rtl_dft"} {
  set analyze_script_impl [exec bender script formality {*}$BENDER_MANI_LOC {*}$BENDER_ARGS {*}$BENDER_IMPL_ARGS | sed s/\ \-r\ /\ \-i\ /]
  # Open the file for writing
  set fh_impl [open $REPORTS_DIR/analyze_rtl2rtl_impl.tcl "w"]
  # Write the content to the file and to stdout
  puts $fh_impl $analyze_script_impl
  puts $analyze_script_impl
  # Close the file
  close $fh_impl
}

if {$NETLIST_TYPE == "rtl"} {
  # Open the file for writing
  set fh_impl [open $RELEASE_DIR/$DESIGN_NAME.read_rtl_formality_impl.tcl "r"]
  # Write the content to the file and to stdout
  set analyze_script_impl_temp [read $fh_impl]
  set analyze_script_impl [string map [list $RELEASE_DIR_SIGN $RELEASE_DIR] $analyze_script_impl_temp]
  puts $analyze_script_impl
  # Close the file
  close $fh_impl
}

#TODO: update PD release comparison values after discussion
#source /home/projects/FLOW/project_setup/${GFTECH}/project_setup.tcl
#source /home/projects/FLOW/project_setup/${GFTECH}/project_setup_toplevel.tcl

set DESIGN_REF_DATA_PATH          ""  ;#  Absolute path prefix variable for library/design data.
                                       #  Use this variable to prefix the common absolute path
                                       #  to the common variables defined below.
                                       #  Absolute paths are mandatory for hierarchical
                                       #  reference methodology flow.

##########################################################################################
# Hierarchical Flow Design Variables
##########################################################################################

set HIERARCHICAL_DESIGNS           "" ;# List of hierarchical block design names "DesignA DesignB" ...
set HIERARCHICAL_CELLS             "" ;# List of hierarchical block cell instance names "u_DesignA u_DesignB" ...

##########################################################################################
# Tools setup
##########################################################################################
set_host_options -max_cores 4

##########################################################################################
# Library Setup Variables
##########################################################################################
source $::env(REPO_ROOT)/hw/ip/tech_cell_library/default/rtl/sf5a/tc_techlib.tcl
#################################################################################
# Read in the libraries
#################################################################################
foreach path [split $MEM_LIBS] {
  puts $path
  foreach file [glob -nocomplain -directory $path *.db*] {
    read_db -technology_library $file
  }
}

foreach path [split $REG_FILES] {
  puts $path
  foreach file [glob -nocomplain -directory $path *.db*] {
    read_db -technology_library $file
  }
}

set VAR1 "/data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_flk_rvt_c54_a00_V3.10/BE-Common/fusion_ref_library/ln05lpe_sc_s6t_flk_rvt_c54l08_c/ln05lpe_sc_s6t_flk_rvt_c54l08_ffpg_nominal_min_0p6050v_125c.db_ccs_tn_lvf"
set VAR2 "/data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_flk_lvt_c54_a00_V3.10/BE-Common/fusion_ref_library/ln05lpe_sc_s6t_flk_lvt_c54l08_c/ln05lpe_sc_s6t_flk_lvt_c54l08_ffpg_nominal_min_0p6050v_125c.db_ccs_tn_lvf"

foreach tech_lib "${VAR1} ${VAR2}" {
    read_db ${tech_lib}
}
##########################################################################################
# Implementation netlist selection
##########################################################################################
if { $NETLIST_TYPE == "rtla" } {
  set SVF_FILE          ${CUR_PATH}/../synth-rtla/build_rtla_latest_out/{{ cookiecutter.block_name }}_p.svf
  set COMPARE_NETLIST   ${CUR_PATH}/../synth-rtla/build_rtla_latest_out/{{ cookiecutter.block_name }}_p.elab.v
} elseif { $NETLIST_TYPE == "pdsyn" } {
  #TODO: update PD release comparison values after discussion
  set SVF_FILE        ""
  set COMPARE_NETLIST ""
} elseif { $NETLIST_TYPE == "rtl_dft" } {
  #TODO update DFT flow
  set SVF_FILE        ""
  set COMPARE_NETLIST ""
} elseif { $NETLIST_TYPE == "rtl" } {
  #TODO update DFT flow
  set SVF_FILE        ""
  set COMPARE_NETLIST ""
} else {
  puts "ERROR: given netlist type $NETLIST_TYPE not supported."
  exit
}

set_app_var search_path "$fm_work_path $search_path"
define_design_lib WORK -path "$fm_work_path/WORK"
#################################################################################
# Formality Verification Script for
# Design Compiler Reference Methodology Script for Top-Down MCMM Flow
# Script: fm.tcl
# Version: P-2019.03-SP4
# Copyright (C) 2007-2019 Synopsys, Inc. All rights reserved.
#################################################################################

#################################################################################
# Synopsys Auto Setup Mode
#################################################################################

set_app_var synopsys_auto_setup true

# Note: The Synopsys Auto Setup mode is less conservative than the Formality default
# mode, and is more likely to result in a successful verification out-of-the-box.
#
# Using the Setting this variable will change the default values of the variables
# listed here below. You may change any of these variables back to their default
# settings to be more conservative. Uncomment the appropriate lines below to revert
# back to their default settings:

  # set_app_var hdlin_ignore_parallel_case true
  # set_app_var hdlin_ignore_full_case true
  # set_app_var verification_verify_directly_undriven_output true
  # set_app_var hdlin_ignore_embedded_configuration false
  # set_app_var svf_ignore_unqualified_fsm_information true
  # set_app_var signature_analysis_allow_subset_match true

# Other variables with changed default values are described in the next few sections.

#################################################################################
# Setup for handling undriven signals in the design
#################################################################################

# The Synopsys Auto Setup mode sets undriven signals in the reference design to
# "0" or "BINARY" (as done by DC), and the undriven signals in the impl design are
# forced to "BINARY".  This is done with the following setting:

  # set_app_var verification_set_undriven_signals synthesis

# Uncomment the next line to revert back to the more conservative default setting:

  # set_app_var verification_set_undriven_signals BINARY:X

#################################################################################
# Setup for simulation/synthesis mismatch messaging
#################################################################################

# The Synopsys Auto Setup mode will produce warning messages, not error messages,
# when Formality encounters potential differences between simulation and synthesis.
# Uncomment the next line to revert back to the more conservative default setting:

  # remove_mismatch_message_filter -all

#################################################################################
# Setup for Clock-gating
#################################################################################

# The Synopsys Auto Setup mode, along with the SVF file, will appropriately set
# the clock-gating variable. Otherwise, the user will need to notify Formality
# of clock-gating by uncommenting the next line:

  # set_app_var verification_clock_gate_hold_mode any

#################################################################################
# Setup for instantiated DesignWare or function-inferred DesignWare components
#################################################################################

# The Synopsys Auto Setup mode, along with the SVF file, will automatically set
# the hdlin_dwroot variable to the top-level of the Design Compiler tree used for
# synthesis.  Otherwise, the user will need to set this variable if the design
# contains instantiated DW or function-inferred DW.

  # set_app_var hdlin_dwroot "" ;# Enter the pathname to the top-level of the DC tree

#################################################################################
# Setup for handling missing design modules
#################################################################################

# If the design has missing blocks or missing components in both the reference and
# implementation designs, uncomment the following variable so that Formality can
# complete linking each design:

  set_app_var hdlin_unresolved_modules black_box

#################################################################################
# Read in the SVF file(s)
#################################################################################

# Set this variable to point to individual SVF file(s) or to a directory containing SVF files.

if { ${SVF_FILE} != "" } {
  set_svf ${SVF_FILE}
}
#################################################################################
# Read in the Reference Design as verilog/vhdl source code
#################################################################################
# evaluate the generated TCL script
if [catch {eval $analyze_script} result] {
  puts "Error: $result"
}
set_top r:/WORK/${DESIGN_NAME}
#################################################################################
# Read in the Implementation Design from DC-RM results
#
# Choose the format that is used in your flow.
#################################################################################

if [string match "rtl*" ${NETLIST_TYPE}] {
  if [catch {eval $analyze_script_impl} result] {
    puts "Error: $result"
  }
} else {
  read_verilog -i ${COMPARE_NETLIST}
}
set_top i:/WORK/${DESIGN_NAME}


#################################################################################
# Configure constant ports
#
# When using the Synopsys Auto Setup mode, the SVF file will convey information
# automatically to Formality about how to disable scan.
#
# Otherwise, manually define those ports whose inputs should be assumed constant
# during verification.
#
# Example command format:
#
#   set_constant -type port i:/WORK/${DESIGN_NAME}/<port_name> <constant_value>
#
#################################################################################

current_design ${DESIGN_NAME}
if {[file exist fm_constraints.tcl]} {
   source fm_constraints.tcl
}


#################################################################################
# Report design statistics, design read warning messages, and user specified setup
#################################################################################

# report_setup_status will create a report showing all design statistics,
# design read warning messages, and all user specified setup.  This will allow
# the user to check all setup before proceeding to run the more time consuming
# commands "match" and "verify".

report_setup_status > ${REPORTS_DIR}/setup_status.rpt
report_constants > ${REPORTS_DIR}/constants_before_match.rpt
#################################################################################
# Match compare points and report unmatched points
#################################################################################

match

if { $NETLIST_TYPE == "rtl_dft" } {
  # Mbist post-match constraint
  if {[file exist ${DESIGN_NAME}_all_test_pins.fms]} {
    set bbox_list [report_matched_points -point_type bbox -list]
    source ${DESIGN_NAME}_all_test_pins.fms
  }
}

report_unmatched_points > ${REPORTS_DIR}/unmatched_points.rpt
report_constants > ${REPORTS_DIR}/constants_after_match.rpt
#################################################################################
# Verify and Report
#
# If the verification is not successful, the session will be saved and reports
# will be generated to help debug the failed or inconclusive verification.
#################################################################################

if { ![verify] }  {
  save_session -replace ${REPORTS_DIR}/${DESIGN_NAME}
  report_failing_points > ${REPORTS_DIR}/${DESIGN_NAME}.fmv_failing_points.rpt
  report_aborted > ${REPORTS_DIR}/${DESIGN_NAME}.fmv_aborted_points.rpt
  report_constants > ${REPORTS_DIR}/constants_on_failure.rpt
  # Use analyze_points to help determine the next step in resolving verification
  # issues. It runs heuristic analysis to determine if there are potential causes
  # other than logical differences for failing or hard verification points.
  analyze_points -all > ${REPORTS_DIR}/${DESIGN_NAME}.fmv_analyze_points.rpt
}

exit
