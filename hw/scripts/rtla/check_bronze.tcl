# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Get the macro's in the design, this can be used for bronze requirement checking
# Owner: Matt Morris <matt.morris@axelera.ai>

set RUN_DIR_TOP [pwd]
set SYNTH_DIR  $env(MAKEFILE_DIR)
set IP_DIR     [file normalize ${SYNTH_DIR}/../]
set GIT_REPO   [exec git -C $IP_DIR rev-parse --show-toplevel]
set REL_SYNTH_DIR [string map [list "$GIT_REPO" ""] $SYNTH_DIR]

set LIST_DIR   [file join $SYNTH_DIR $env(BUILD_DIR)]
set RTL_DIR    [file normalize [file join $IP_DIR rtl]]

set BENDER_MANI_LOC    ${RTL_DIR}
set BENDER_TARGETS { rtl asic sf5a }
set BENDER_WORK_DIR   [file normalize [file join $RUN_DIR_TOP bender_work_dir]]

# Use this proc to read in block specific commands are various points in the flow
proc block_specific_commands {FNAME} {
  if {[file exists ${FNAME}] == 1} {
    echo "Sourcing ${FNAME}"
    source ${FNAME}
  }
}
if {[info exists env(DESIGN)]} {
  set DESIGN $env(DESIGN)
}
if {![info exists DESIGN] || ${DESIGN} eq ""} {
  # Exit immediately
  puts "Error: DESIGN variable is not set, please set via env: DESIGN={...} make ..."
  exit 1
}
puts "Running RTL-Architect on the Design ${DESIGN} step"

# Set current timestamp and create outname
set OUTNAME_BASE ${DESIGN}_synthesis

# Create log, report and out directory
set RUN_DIR    ${RUN_DIR_TOP}/${OUTNAME_BASE}
set LOG_DIR    ${RUN_DIR}/logs
set OUT_DIR    ${RUN_DIR}/out

exec mkdir -p $RUN_DIR
exec mkdir -p $LOG_DIR
exec mkdir -p $OUT_DIR

puts "Synthesizing Design ${DESIGN}"

# Multi core processing
set_host_options -max_cores $env(GRID_NUM_CPUS)

set_app_options -name hdlin.elaborate.evaluate_complex_parameter_expressions -value true

###################
## Library Setup ##
###################

# MEM_IP is used to source the memories based on the info in the common tc_techlib.tcl file.
# Edit this name to match the memories to bepicked up for this IP.
set MEM_IP ${DESIGN}
set eda_tool rtl_shell
# The following tech libs file contains all the common paths to tech information
source ${GIT_REPO}/hw/ip/tech_cell_library/default/rtl/sf5a/tc_techlib.tcl

set RTLA_LIB ${OUT_DIR}/${DESIGN}_lib
set PARAS_RC nominal
set TEMPERATURE 125
set VOLTAGE 0.765

redirect -tee -file ${LOG_DIR}/setup_lib.log {

  block_specific_commands ${SYNTH_DIR}/rtla_lib_setup_pre.tcl

  # Delete library if it already exists
  if {[file exists $RTLA_LIB]} {
    file delete -force $RTLA_LIB
  }

  # Create design library and open it
  create_lib $RTLA_LIB -technology $TECH_LIB -ref_libs $STD_CELL_NDM_LIBS$MEM_LIBS$REG_FILES -scale_factor 4000

  block_specific_commands ${SYNTH_DIR}/rtla_lib_setup_post.tcl
}

#################
## Elaboration ##
#################

set BENDER_STRING "bender -d ${BENDER_MANI_LOC} script template --template ${GIT_REPO}/hw/scripts/bender_templates/synopsys_tcl.tera "
foreach TARGET ${BENDER_TARGETS} {
  set BENDER_STRING "${BENDER_STRING} -t ${TARGET} "
}
set BENDER_STRING "${BENDER_STRING} > ${BENDER_WORK_DIR}/analyze.tcl"

redirect -tee -file ${LOG_DIR}/analyze.log {
  exec mkdir -p ${BENDER_WORK_DIR}
  eval exec ${BENDER_STRING}

  # Analyze all sources
  source ${BENDER_WORK_DIR}/analyze.tcl
}

redirect -tee -file ${LOG_DIR}/elaborate.log {
  # There should be an error when there is a port width mismatch
  set_app_options -name link.error_on_net_port_width_mismatch -value true

  # Elaborate design
  elaborate $DESIGN

  # Set the top module
  set_top_module $DESIGN
}

## The actual checking can start:
# Macros:
set all_macros [sort_collection [get_cells -hier  * -filter {is_hard_macro==true}] {full_name}]
set all_ports [sort_collection [get_ports] {full_name}]

redirect -tee -file ${LIST_DIR}/${DESIGN}_bronze_freeze.lst {
  puts "$DESIGN $REL_SYNTH_DIR"
  puts "\nAll macros:"
  foreach_in_collection macro $all_macros {
      puts "[get_attribute $macro ref_name]: [get_object_name $macro]"
  }
  puts "\nAll ports:"
  foreach_in_collection port $all_ports {
      puts "[get_object_name $port]: [get_attribute $port direction]"
  }
}
# Finish
exit 0
