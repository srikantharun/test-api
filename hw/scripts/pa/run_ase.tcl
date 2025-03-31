variable script_dir [file dirname  [file normalize [info script]]]

# Configure "flow_step" and source the common config file for all major flow steps.
set flow_step "AnalyzeStaticEfficiency"
source ${script_dir}/base/config.tcl

# This target is only supported from release 2020 R1 onwards.
if { [lindex [split $wwVersion "."] 0] < 2020 } {
  return -code error "Error: AnalyzeStaticEfficiency is only supported from release 2020 R1 onwards! Exiting ..."
}

# ignore pctl clock division clock-gates:
SetDesignClockGates -instance {*u_pctl*g_clkdiv*u_tc_lib_clk_en*} -ignore yes
if { [info exists ASE_INST_IGNORE ] } {
  SetDesignClockGates -instance ${ASE_INST_IGNORE} -ignore yes
}

# Write a PDB to store the static efficiency analysis results.
pa_set static_efficiency_write_power_db true
pa_set power_db_name $PDB_DIR/${filename}_ase${elab_suffix}.pdb

# Write out logic optimization report.
pa_set logic_optimization_report $RPT_DIR/${filename}_ase${elab_suffix}_opt.rpt

# Report and log options.
pa_set static_efficiency_log $LOG_DIR/${filename}_ase${elab_suffix}.log

pa_set clock_gating_decision_report $LOG_DIR/${filename}_ase${elab_suffix}_clk_decision.log

AnalyzeStaticEfficiency

# Report creation
# ---------------
# open PDB (created above).
openPDB [pa_set power_db_name] -silent
# check if (potentially updated) script is part of tool installation
if { [file exists $env(POWERARTIST_ROOT)/utils/atcl/atcl_generate_static_efficiency_report.tcl] } {
  source $env(POWERARTIST_ROOT)/utils/atcl/atcl_generate_static_efficiency_report.tcl
  atcl_generate_static_efficiency_report -detailed \
    -out $RPT_DIR/${filename}_static_efficiency_detailed${elab_suffix}
  # atcl_generate_static_efficiency_report -detailed -with_filename \
  #   -out $RPT_DIR/${filename}_static_efficiency_detailed_with_filename${elab_suffix}
} else {
  return -code error "Error: script 'atcl_generate_static_efficiency_report.tcl' not part of the tool installation! Please use newer tool version (2020 R1.4 or newer, or 2020 R2, or newer release)."
}
closePDB

# Cleanup of files.
if { [file exists "true"] } { exec rm "true" }

exit
