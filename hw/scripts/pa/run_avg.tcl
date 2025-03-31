variable script_dir [file dirname  [file normalize [info script]]]

# Source the common config file for all major flow steps.
source ${script_dir}/base/config.tcl

# Perform GAF processing only in case a VCD or FSDB is present.
if { $source_of_activity_data == "vcd_fsdb" } {
  # ############################################################################
  # ################### Generate GAF from simulation activity ##################
  # ############################################################################

  # Use one common GAF for power analysis and reduction.
  pa_set gaf_file $WORK_DIR/${filename}${suffix}.gaf.gz

  # IF clause controls if reduction step should create its own GAF (value "1"),
  # or take the one from a former power analysis run (value "0").
  # If the GAF file is not present and the value below is "0", then
  # CalculatePower below will automatically run GAF generation under-the-hood.
  if {1} {

    # Compress GAF file with gzip to save disk space. Also change gaf_file to ".gz".
    pa_set compress_gaf true

    # If GAF file should be generated only once for power analysis and reduction,
    # then it should also contain reduction information (.sgaf and .stcl files).
    # ####################
    # # Need to review
    # ####################
    #pa_set gaf_enable_reduction_data true

    # Output file to store the list of floating nets of the design.
    # Will only be reported when "gaf_enable_reduction_data" above is set to 'true'.
    #pa_set ftn_report_file $RPT_DIR/${filename}_gaf${suffix}_ftn.rpt

    # Report missing nets and X nets inside VCD/FSDB.
    pa_set print_missing_sim_nets true
    # ####################
    # # Need to change
    # ####################
    # pa_set allowed_x_time <time, for example 20ns> ; # allow x time for 1 clock cycle
    pa_set save_x_nets_file $RPT_DIR/${filename}_gaf${suffix}_xnets.rpt

    pa_set gaf_log $LOG_DIR/${filename}_gaf${suffix}.log
    GenerateGAF
  }

# ##############################################################################
# ########################### POWER ANALYSIS SETTINGS ##########################
# ##############################################################################

  # Declare that PA should use GAF, which was created above by "GenerateGAF".
  pa_set use_existing_gaf true

}

# Perform average power analysis.
pa_set analysis_type average

# Write a PDB to store the average power results.
pa_set average_write_power_db true
pa_set power_db_name $PDB_DIR/${filename}_avg${suffix}.pdb

# Activate Block Activity Ranking analysis with additional "total_dynamic_power" column.
# ####################
# # Need to review
# ####################
SetBAR -output_file $CSV_DIR/${filename}_avg${suffix}_BAR -format both -levels 7 \
  -cols "total_power total_power_prcnt clock_power total_dynamic_power clock_activity data_activity"

# Write out cell selection report.
pa_set cell_selection_report $RPT_DIR/${filename}_avg${suffix}_cell_selection.rpt

# Write out logic optimization report.
pa_set logic_optimization_report $RPT_DIR/${filename}_avg${suffix}_opt.rpt

# Vertical report with cell details; uses 'traceInstancesList' from 'config.tcl'.
pa_set detailed_vertical_report true
pa_set vertical_report_instances $traceInstancesList

# Detailed (debug) report for clock tree/mesh buffering.
# Only available in PACE-based flow and if "pa_set enable_advanced_cts true"
# is activated in "common.tcl".
if { $use_pace_based_flow  && [pa_set enable_advanced_cts] } {
  pa_set clock_tree_debug_report ${RPT_DIR}/${filename}_avg_clock_tree${suffix}.rpt
}

# Report and log options.
pa_set average_report_file $RPT_DIR/${filename}_avg${suffix}.rpt
# ####################
# # Need to review
# ####################
pa_set average_report_options agipmVc ; # additional options: "a" for area; "g" for frequency/glitch; c for PP comparison
pa_set calculate_log $LOG_DIR/${filename}_avg${suffix}.log

CalculatePower

# Cleanup of files.
if {[file exists "pa_sld"]} { file delete -force pa_sld }

# ##############################################################################
# #################### Generate custom reports using Tcl API ###################
# ##############################################################################

# First open the average Power results PDB.
openPDB "$PDB_DIR/${filename}_avg${suffix}.pdb"

# Report summary for power and components/insts.
reportSummary -out $RPT_DIR/${filename}_avg${suffix}_report_summary.rpt

# Report Power for hierarchies (here: up to 5 levels deep).
# ####################
# # Need to review
# ####################
reportPower -out $RPT_DIR/${filename}_avg${suffix}_report_power.rpt -levels 5 -rc

# Report average activity and annotation. Only supported from version 2020 R1 onwards.
if { [lindex [split $wwVersion "."] 0] >= "2020" } {
  report_activity -primary_inputs -out $RPT_DIR/${filename}_avg${suffix}_activity.rpt
}

# Close the opened PDB.
closePDB

exit
