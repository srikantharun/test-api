#-------------------------------------------------------
# General Procedures
#-------------------------------------------------------
proc proc_run_proves {} {
  # Validate
  set_fml_appmode FPV
  check_fv -block
  report_fv -verbose
  report_fv -verbose > report_fv.log
}
proc proc_property_density {} {
  # Property Density
  report_assertion_density
  report_assertion_density -list_uncovered > pd_uncovered_report.txt
  save_property_density_results -db_name COI.vdb
  #view_coverage -cov_input COI -mode PD -reload
}

proc proc_over_constraint {} {
  # Over Constraint
  set_fml_appmode FPV
  compute_bounded_cov -par_task FPV -max_proof_depth -1 -block
  save_bounded_cov_results -db_name OC.vdb
  report_fv
  #view_coverage -cov_input OC -mode OA+BA -reload -elfiles  FPV_OA_BA_unr.el_wo_constraints.el
}

proc proc_formal_core {} {
  # Formal Core
  set_fml_appmode FPV
  compute_formal_core -block
  report_formal_core -verbose
  compute_formal_core_coverage -par_task FPV -block
  save_formal_core_results -db_name FC.vdb
  #view_coverage -cov_input FC -mode FC -reload -elfiles { FPV_COV_FCORE_w_fcore.el }
}

proc proc_signoff {} {
  #signoff_check -effort med -signoff_bound -1 -signoff_dashboard -block
  signoff_check -effort med -signoff_bound -1 -block
}

#Configure host file
set_grid_usage -file $::env(REPO_ROOT)/hw/scripts/fv/fpv/host.qsub

#-------------------------------------------------------
# Read configuraton file
#-------------------------------------------------------
source ../settings.tcl

#-------------------------------------------------------
# Compile & Setup
#-------------------------------------------------------
# Setting Application
set_fml_appmode FPV

# Enabling witness
set_fml_var fml_witness_on true

# Seeting variables
# Enable coverage mapping for COI analysis
set_fml_var fml_enable_prop_density_cov_map true

# Include reset branches for coverage
set_fml_var fml_reset_property_check true
set_fml_var fml_track_loc_reset true

# Preserve source location of constant selects
set_fml_var fml_track_loc_const_select true

# Preserve source location of expression values
set_app_var keep_source_loc_expr true

# If branch coverage has been enabled
# Include branch coverage in analysis
# set_fml_var fml_cov_enable_branch_cov true

# If toggle coverage is enabled
# Include toggle of primary inputs in coverage analysis
set_app_var fml_cov_tgl_input_port true

# Enable formal core computation for proven + inconclusive at the same time
set_fml_var fml_formal_core_incremental true

# Enable formal core computation for liveness assertions
set_fml_var fml_formal_core_liveness true

# Enable Formal Core collection during proof
check_config -formal_core both

# Avoid constraint minimzation step in Formal Core computation to improve performance
set_fml_var fml_formal_core_reduced_constraints false

# If toggle coverage is enabled
# Treat toggle coverage of undriven signals/inputs as unreachable
set_fml_var fml_cov_tgl_undriven_as_unr true

# Downgrade CFC_NO_FC_SUB error to warning
set_message_severity -names CFC_NO_FC_SUB warning

# Disable dumping simulation centric assertion coverage info in VDB
set_app_var fml_disable_assert_shape_dump true

# Auto-merge COI+FC+FTA VDBs
set_fml_var fml_signoff_auto_merge true

# signoff_config -type "line cond toggle branch"
signoff_config -type "line cond toggle"

# Define max mem and timeout
proc_set_mem_timeout

# Including AIP
proc_enable_AIP

# Define Blackboxes
proc_set_design_blackboxes

# Reading design
source rtl.analyze.tcl
#elaborate $design -cov line+cond+tgl+branch -sva -vcs "-cm_tgl mda"
elaborate $design -cov line+cond+tgl -sva -vcs "-cm_tgl mda"

# Reporting read violations, and blackboxes and formal results
report_read_violations -verbose -file report_read_violations.txt
report_blackbox -verbose > blackbox.txt

# Defining clocks
proc_set_clks

# Defining resets
proc_set_rsts

# Disabing assertions and assumes in the rtl_file
fvdisable -usage {assert assume} { * }
fvenable -usage {assert assume} { *.*sva*.* }

# Initialisation commands
sim_run -stable
sim_save_reset

# snip driver
proc_set_snip_drivers

# Checking setup
check_fv_setup -block
report_fv_setup -list > fv_setup.log

#-------------------------------------------------------
# Running Verification
#-------------------------------------------------------

run
