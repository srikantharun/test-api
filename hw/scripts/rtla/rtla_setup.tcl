# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Samsung SF5A 5nm RTL-Architect flat setup script
# Owner: Matt Morris <matt.morris@axelera.ai>


set RTLA_FLOW_STEP $env(RTLA_FLOW)
set RUN_DIR_TOP [pwd]
set SYNTH_DIR  $env(MAKEFILE_DIR)
set CONSTR_DIR [file normalize [file join $SYNTH_DIR constraints]]
set RTL_DIR    [file normalize [file join $IP_DIR rtl]]
if { $env(DFT) } {
  set RTL_DIR  [file normalize [file join $RTL_DIR dft]]
  lappend BENDER_TARGETS dft
}
set BENDER_MANI_LOC    ${RTL_DIR}
set BENDER_WORK_DIR   [file normalize [file join $RUN_DIR_TOP bender_work_dir]]
puts "Running RTL-Architect on the Design ${DESIGN} till ${RTLA_FLOW_STEP} step"

# Use this proc to read in block specific commands are various points in the flow
proc block_specific_commands {FNAME} {
  if {[file exists ${FNAME}] == 1} {
    echo "Sourcing ${FNAME}"
    source ${FNAME}
  }
}

if {![info exists DESIGN] || ${DESIGN} eq ""} {
  # Exit immediately
  puts "Error: DESIGN variable is not set"
  exit 1
}

# Set current timestamp and create outname
set OUTNAME_BASE ${DESIGN}_synthesis

# Create log, report and out directory
set RUN_DIR    ${RUN_DIR_TOP}/${OUTNAME_BASE}
set LOG_DIR    ${RUN_DIR}/logs
set REPORT_DIR ${RUN_DIR}/reports
set OUT_DIR    ${RUN_DIR}/out
exec mkdir -p $RUN_DIR
exec mkdir -p $LOG_DIR
exec mkdir -p $REPORT_DIR
exec mkdir -p $OUT_DIR

puts "Synthesizing Design ${DESIGN}"

# Multi core processing
set_host_options -max_cores $env(GRID_NUM_CPUS)

set_app_options -name hdlin.elaborate.evaluate_complex_parameter_expressions -value true

# Setting Report Fields
# The number of reported paths per group
set MAX_TIMING_PATHS 50

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

if {
  ([string equal ${RTLA_FLOW_STEP}  "analyze"]) ||
  ([string equal ${RTLA_FLOW_STEP}  "elaboration"]) ||
  ([string equal ${RTLA_FLOW_STEP}  "conditioning"]) ||
  ([string equal ${RTLA_FLOW_STEP}  "estimation"])
} {
  redirect -tee -file ${LOG_DIR}/setup_lib.log {

    block_specific_commands ${SYNTH_DIR}/rtla_lib_setup_pre.tcl

    # Delete library if it already exists
    if {[file exists $RTLA_LIB]} {
      file delete -force $RTLA_LIB
    }

    # Create design library and open it
    create_lib $RTLA_LIB -technology $TECH_LIB -ref_libs $STD_CELL_NDM_LIBS$MEM_LIBS$REG_FILES -scale_factor 4000

    # Read in parasitics information along with the layer map information
    set_app_options -name file.tlup.max_preservation_size -value 30
    read_parasitic_tech -tlup $TLUP_LIB -name $PARAS_RC

    # Set svf file
    set_svf ${OUT_DIR}/${DESIGN}.svf

    block_specific_commands ${SYNTH_DIR}/rtla_lib_setup_post.tcl

  }

  #############
  ## Analyze ##
  #############

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
} else {
  puts "Bypassing analyze step"
}

if {
  ([string equal ${RTLA_FLOW_STEP}  "elaboration"]) ||
  ([string equal ${RTLA_FLOW_STEP}  "conditioning"]) ||
  ([string equal ${RTLA_FLOW_STEP}  "estimation"])
} {
  set_app_options -name hdlin.elaborate.black_box -value ${BBOX_MODULES}

  redirect -tee -file ${LOG_DIR}/elaborate.log {
    # There should be an error when there is a port width mismatch
    set_app_options -name link.error_on_net_port_width_mismatch -value true

    # Elaborate design
    elaborate $DESIGN

    # Set the top module
    set_top_module $DESIGN

    block_specific_commands ${SYNTH_DIR}/rtla_elab_post.tcl

    # Output elaborated verilog netlist
    set_app_options -name file.verilog.write_non_pg_net_assigns -value true
    set_app_options -name file.verilog.write_pg_net_assigns     -value true
    # Writing elab file is an optional step. Can be commented out if we are not using it.
    write_verilog -top_module_first -hierarchy design $OUT_DIR/${DESIGN}.elab.v

    # Save current block in library
    save_block -as ${DESIGN}/elaboration
  }

  if {[string equal ${RTLA_FLOW_STEP}  "elaboration"]} {
    # Report results
    write_qor_data -label ${RTLA_FLOW_STEP} -output ${REPORT_DIR} -report_group mapped
    report_pvt > ${REPORT_DIR}/pvt_info.rpt
    compare_qor_data -run_locations ${REPORT_DIR} -output ${RUN_DIR}/qor_summary_data

    # Save design library to disk
    save_lib $RTLA_LIB

    # Link directories
    exec ln -sfn ${OUT_DIR} ${SYNTH_DIR}/build_rtla_latest_out
  }
} else {
  puts "Bypassing elaboration step"
}

#################
## Constraints ##
#################

if {
  ([string equal ${RTLA_FLOW_STEP}  "conditioning"]) ||
  ([string equal ${RTLA_FLOW_STEP}  "estimation"])
} {
  redirect -tee -file ${LOG_DIR}/constraints.log {
    # Set scenarios and scenario specific constraints
    # Default handling of impl specific signals for SRAM macros
    set all_rfs [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*rf*p*}]
    foreach_in_collection rf $all_rfs {
       set rfname [get_object_name $rf]
       set_case_analysis 1 [get_pins ${rfname}/ADME[2]]
       set_case_analysis 0 [get_pins ${rfname}/ADME[1]]
       set_case_analysis 0 [get_pins ${rfname}/ADME[0]]
       set_case_analysis 0 [get_pins ${rfname}/PDE]
       set_case_analysis 0 [get_pins ${rfname}/RET]
       set_case_analysis 0 [get_pins ${rfname}/DFTRAM]
       set_case_analysis 0 [get_pins ${rfname}/SE]
    }
    set all_srams [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*ra*p*}]
    foreach_in_collection srams $all_srams {
       set sramname [get_object_name $srams]
       set_case_analysis 1 [get_pins ${sramname}/ADME[2]]
       set_case_analysis 0 [get_pins ${sramname}/ADME[1]]
       set_case_analysis 0 [get_pins ${sramname}/ADME[0]]
       set_case_analysis 0 [get_pins ${sramname}/PDE]
       set_case_analysis 0 [get_pins ${sramname}/RET]
       set_case_analysis 0 [get_pins ${sramname}/DFTRAM]
       set_case_analysis 0 [get_pins ${sramname}/SE]
    }
    set all_srams [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*ra1*p*}]
    foreach_in_collection srams $all_srams {
       set sramname [get_object_name $srams]
       set_case_analysis 0 [get_pins ${sramname}/MCS[1]]
       set_case_analysis 1 [get_pins ${sramname}/MCS[0]]
       set_case_analysis 0 [get_pins ${sramname}/MCSW]
    }
    set all_rf1s [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*rf1*p*}]
    foreach_in_collection rf1 $all_rf1s {
       set rf1name [get_object_name $rf1]
       set_case_analysis 0 [get_pins ${rf1name}/MCS[1]]
       set_case_analysis 1 [get_pins ${rf1name}/MCS[0]]
       set_case_analysis 0 [get_pins ${rf1name}/MCSW]
    }
    set all_rf2s [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*rf2*p*}]
    foreach_in_collection rf2 $all_rf2s {
       set rf2name [get_object_name $rf2]
       set_case_analysis 0 [get_pins ${rf2name}/MCSRD[1]]
       set_case_analysis 1 [get_pins ${rf2name}/MCSRD[0]]
       set_case_analysis 0 [get_pins ${rf2name}/MCSWR[1]]
       set_case_analysis 1 [get_pins ${rf2name}/MCSWR[0]]
       set_case_analysis 0 [get_pins ${rf2name}/KCS]
    }

    block_specific_commands ${SYNTH_DIR}/rtla_constraints_pre.tcl

    source ${CONSTR_DIR}/${DESIGN}_constraints.tcl

    # Disable auto-ungrouping - This is needed to retain hierarchies.
    # Should be commented if you want to flatten the module for better synthesis optimization.
    set_app_options -name compile.flow.autoungroup -value false
    # Disable multi-bit signal merging
    set_app_options -name compile.flow.enable_multibit -value false
    # Disable CTS - This can be enabled if power analysis is being done.
    set_app_option -name rtl_opt.flow.enable_cts -value false
    # Enable global routing - This has no impact on front-end RTL synthesis. It is primarily used for congestion analysis
    # set_app_options -name cts.compile.enable_global_route -value true
    set_app_options -name place_opt.flow.enable_ccd -value false
    set_app_options -name compile.flow.enable_ccd -value false
    set_app_options -name clock_opt.flow.enable_ccd -value false
    set_app_options -name route_opt.flow.enable_ccd -value false

    block_specific_commands ${SYNTH_DIR}/rtla_constraints_post.tcl
  }

  ##################
  ## Conditioning ##
  ##################

  redirect -tee -file ${LOG_DIR}/conditioning.log {
    block_specific_commands ${SYNTH_DIR}/rtla_conditioning_pre.tcl

    # Rest of conditioning
    set_voltage $VOLTAGE
    set_temperature $TEMPERATURE
    set_parasitic_parameters -early_spec $PARAS_RC -early_temperature $TEMPERATURE -late_spec $PARAS_RC -late_temperature $TEMPERATURE
    rtl_opt -from conditioning -to conditioning

    # Save current block
    save_block -as ${DESIGN}/conditioning

    # Report timing
    report_timing -nosplit -scenarios [all_scenarios] -delay_type max -input_pins -include_hierarchical_pins -nets \
      -transition_time -capacitance -attributes -physical -derate -report_by group \
      -variation -max_paths ${MAX_TIMING_PATHS} > ${REPORT_DIR}/timing_max.cond.rpt
    report_timing -nosplit -scenarios [all_scenarios] -delay_type min -input_pins -include_hierarchical_pins -nets \
      -transition_time -capacitance -attributes -physical -derate -report_by group \
      -variation -max_paths ${MAX_TIMING_PATHS} > ${REPORT_DIR}/timing_min.cond.rpt

    block_specific_commands ${SYNTH_DIR}/rtla_conditioning_post.tcl

  }
  if {[string equal ${RTLA_FLOW_STEP}  "conditioning"]} {
    # Report results
    write_qor_data -label ${RTLA_FLOW_STEP} -output ${REPORT_DIR} -report_group mapped
    report_pvt > ${REPORT_DIR}/pvt_info.cond.rpt
    compare_qor_data -run_locations ${REPORT_DIR} -output ${RUN_DIR}/qor_summary_data

    # Save design library to disk
    save_lib $RTLA_LIB

    # Link directories
    exec ln -sfn ${OUT_DIR} ${SYNTH_DIR}/build_rtla_latest_out
  }
} else {
  puts "Bypassing conditioning step"
}


################
## Estimation ##
################

if {
  ([string equal ${RTLA_FLOW_STEP}  "estimation"])
} {
  redirect -tee -file ${LOG_DIR}/estimation.log {
    block_specific_commands ${SYNTH_DIR}/rtla_estimation_pre.tcl

    # Placement and physical aware synthesis
    rtl_opt -from estimation -to estimation

    block_specific_commands ${SYNTH_DIR}/rtla_estimation_post.tcl

    # Save current block
    save_block -as ${DESIGN}/estimation
  }

  #############
  ## Metrics ##
  #############

  redirect -tee -file ${LOG_DIR}/metrics.log {
    block_specific_commands ${SYNTH_DIR}/rtla_metrics_pre.tcl

    # Set computation options
    # ZWL is no longer required in RTLA as it conflicts with the newer inbuilt predictable models
    set_app_options -name metrics.timing.enable_zwl_violations -value false

    # Compute timing and congestion metrics
    compute_metrics -timing -congestion

    block_specific_commands ${SYNTH_DIR}/rtla_metrics_post.tcl

    # Report results
    write_qor_data -label ${RTLA_FLOW_STEP} -output ${REPORT_DIR}
    report_pvt > ${REPORT_DIR}/pvt_info.finish.rpt
    compare_qor_data -run_locations ${REPORT_DIR} -output ${RUN_DIR}/qor_summary_data

    # Report Registers
    report_transformed_registers > ${REPORT_DIR}/report_transformed_registers.finish.rpt

    # Report timing
    report_timing -nosplit -scenarios [all_scenarios] -delay_type max -input_pins -include_hierarchical_pins -nets \
      -transition_time -capacitance -attributes -physical -derate -report_by group \
      -variation -max_paths ${MAX_TIMING_PATHS} > ${REPORT_DIR}/timing_max.finish.rpt
    report_timing -nosplit -scenarios [all_scenarios] -delay_type min -input_pins -include_hierarchical_pins -nets \
      -transition_time -capacitance -attributes -physical -derate -report_by group \
      -variation -max_paths ${MAX_TIMING_PATHS} > ${REPORT_DIR}/timing_min.finish.rpt

    # Save current block
    save_block -as ${DESIGN}/finish
  }

  # Save design library to disk
  save_lib $RTLA_LIB

  # Also have a link to the current run in an easy location for formality to pick up
  exec ln -sfn ${OUT_DIR} ${SYNTH_DIR}/build_rtla_latest_out
} else {
  puts "Bypassing estimation step"
}
