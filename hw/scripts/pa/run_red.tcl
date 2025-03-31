variable script_dir [file dirname  [file normalize [info script]]]

# Source the common config file for all major flow steps.
source ${script_dir}/base/config.tcl

# Only run reduction on RTL design stage.
if { [pa_set gate_level_netlist] } {
  return -code error "Error: Power Reduction is run on gate-level netlist! This flow is not supported! Exiting ..."
}

# Perform GAF processing only in case a VCD or FSDB is present.
if { $source_of_activity_data == "vcd_fsdb" } {
  # ############################################################################
  # ################### Generate GAF from simulation activity ##################
  # ############################################################################

  # Use one common GAF for power analysis and reduction.
  pa_set gaf_file $WORK_DIR/${filename}${suffix}.gaf.gz

  # IF clause controls if reduction step should create its own GAF (value "1"),
  # or take the one from average power analysis (value "0").
  # If the GAF file is not present and the value below is "0", then
  # ReducePower below will automatically run GAF generation under-the-hood.
  if {1} {

    # Compress GAF file with gzip to save disk space. Also change gaf_file to ".gz".
    pa_set compress_gaf true

    # Required for the reduction step to create additional .sgaf and .stcl files.
    pa_set gaf_enable_reduction_data true

    # Output file to store the list of floating nets of the design.
    # Will only be reported when "gaf_enable_reduction_data" above is set to 'true'.
    pa_set ftn_report_file $RPT_DIR/${filename}_gaf_red${suffix}_ftn.rpt

    pa_set gaf_log $LOG_DIR/${filename}_gaf_red${suffix}.log
    GenerateGAF
  }

# ##############################################################################
# ############################# REDUCTION SETTINGS #############################
# ##############################################################################

  # Declare that PA should use GAF, which was created above by "GenerateGAF",
  # or during the average power analysis step.
  pa_set use_existing_gaf true
}

# Power Reduction configuration settings.
# ####################
# # Need to review
# ####################
pa_set reduction_effort medium

# Optional ODC settings to reduce runtime.
# ####################
# # Need to review
# ####################
pa_set reduction_odc_max_gcf_bucket_size 64 ; # this one is recommended
#pa_set reduction_odc_max_precompute_inputs 1024 ; # default 1048576
#pa_set reduction_odc_max_xor_count <number> ; # for SODC; default 16

# Optional ODC setting to prune enables which don't contribute significantly to
# the CGE improvement. Consequence: ODC suggestions are dependent on simulation.
#pa_set reduction_odc_activity_optimization true

# Optional for SplitMemoryWords: Number of clock cycles with stable address bus
# ####################
# # Need to review
# ####################
DefineMemActivityThreshold -num_clocks 2
DefineHalfMemScalingFactor -dynamic_scale_factor 0.7 -static_scale_factor 0.7 -area_penalty_factor 0.7

# Optional setting for MacroPowerLinter.
# ####################
# # Need to review
# ####################
#SetMacroPowerLinterReportFile $RPT_DIR/${filename}_red${suffix}_mpl_analysis.rpt
#DefineMacroMode -name <mode_name> -cell <cell_name> -clock_pin <cell_clock_pin> \
#  -clock_edge posedge -when <boolean_condition for mode> \
#  -input_pins <TCL list of input pins which are relevant for this mode> \
#  [-redundant_pins <optional TCL list of redundant input pins for this mode>]

# Optional setting to add a memory access report (in CSV format).
# Only works if activity data comes from FSDB or VCD (cycle-based information available).
if { $source_of_activity_data == "vcd_fsdb" } {
  # ####################
  # # Need to review
  # ####################
  pa_set memory_access_report $CSV_DIR/${filename}_red${suffix}_memory_access.csv
}

# Optionally skip certain reductions.
# ####################
# # Need to review
# ####################
#pa_set skip_reduction_list ""

# Write a PDB to store the power reduction results.
pa_set power_db_name $PDB_DIR/${filename}_red${suffix}.pdb

# Activate Block Activity Ranking analysis with additional "total_dynamic_power" column.
# ####################
# # Need to review
# ####################
SetBAR -output_file $CSV_DIR/${filename}_red${suffix}_BAR -format both -levels 7 \
  -cols "total_power total_power_prcnt clock_power total_dynamic_power clock_activity data_activity"

# Vertical report with cell details; uses 'traceInstancesList' from 'config.tcl'.
pa_set detailed_vertical_report true
pa_set vertical_report_instances $traceInstancesList

# Reduction calculation options.
pa_set reduction_time_based_dacge true

# Report and log options.
pa_set reduction_report_file $RPT_DIR/${filename}_red${suffix}.rpt
pa_set reduction_report_clock_gating_enable_efficiency true
pa_set reduction_report_hierarchical_clock_efficiency true
pa_set reduction_report_clock_gating_by_instance true
pa_set reduction_log $LOG_DIR/${filename}_red${suffix}.log

# If default settings from "reduction_effort" should be overwritten,
# then this setting should to be declared as an option for "ReducePower".
# "pa_set" will not overwrite the "reduction_effort" settings, unless set to "manual".
ReducePower

# Move optional PowerBot specific report files (which are stored in the main dir)
# into the report directory (with correct naming).
if { [file exists "mpl.analysis.red"] } {
  file rename -force "mpl.analysis.red" $RPT_DIR/${filename}_red${suffix}_mpl_analysis.rpt
}
if { [file exists "msm.analysis.red"] } {
  file rename -force "msm.analysis.red" $RPT_DIR/${filename}_red${suffix}_msm_analysis.rpt
}
if { [file exists "smw.reduction.analysis.red"] } {
  file rename -force "smw.reduction.analysis.red" $RPT_DIR/${filename}_red${suffix}_smw_analysis.rpt
}
if { [file exists "memory_linter_report.csv"] } {
  file rename -force "memory_linter_report.csv" $CSV_DIR/${filename}_red${suffix}_memory_linter.csv
}

# Perform textual report of power reductions.
# Add option "-detail true" if detailed enable conditions should be added to the report.
ReportReductions -csv $CSV_DIR/${filename}_red${suffix}.csv -power_db_name $PDB_DIR/${filename}_red${suffix}.pdb \
  -log $LOG_DIR/${filename}_red${suffix}_rpt.log

exit
