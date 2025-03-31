variable script_dir [file dirname  [file normalize [info script]]]

# Configure "flow_step" and source the common config file for all major flow steps.
set flow_step "WriteTechnologyFile"
# overwrite design stage to gate:
set design_stage "gate"
source ${script_dir}/base/config.tcl


# PACE generation requires a gate-level netlist; stop the run for RTL data.
if { $design_stage == "rtl" } {
  return -code error "Error! Flow is configured to run an RTL flow! For PACE generation we need either 'post_syn' or (better) 'gate' level flow!"
}
# PACE generation requires PACE flow setup; stop the run for non-PACE flow.
if { !$use_pace_based_flow } {
  return -code error "Error! Flow is configured for non-PACE usage! Enable 'use_pace_based_flow' for PACE generation!"
}

# Generate a PACE model for all (cap, cell, clock) types.
pa_set generate_pace_model_category all
# Ignore nets with no annotated capacitance.
pa_set no_module_net_capacitances true
# Threshold for SPEF net annotation, ideal annotation is >99.9%.
pa_set pace_spef_annotation_threshold 95
# Log file.
pa_set tech_file_log $LOG_DIR/${filename}_pace_gen.log

# Run PACE tech file generation.
WriteTechnologyFile

# Create report and capacitance plot from created PACE tech file.
reportPaceInfo -in [pa_set power_tech_file] -out $RPT_DIR/${filename}_pace_info.rpt
pacePlotCapTables -png $RPT_DIR/${filename}_pace.png -in [pa_set power_tech_file]

# Cleanup of files.
if { [file exists "ptInspector.log"] } { exec rm "ptInspector.log" }

exit
