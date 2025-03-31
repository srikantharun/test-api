#-------------------------------------------------------
# General Procedures
#-------------------------------------------------------
proc proc_run_proves {} {
  # Running Formal Verification
  check_fv -run_finish {report_fv -verbose} -block
  report_fv -verbose > report_fv.log

  ### Getting Coverage results
  compute_cc_cov -structural
  save_cc_cov_results -elfile
}

#Configure host file
set_grid_usage -file $::env(REPO_ROOT)/hw/scripts/fv/fpv/host.qsub -global

# Default start line on CSV file
set start_line 2

source ../settings.tcl

# Setting Application
set_fml_appmode CC

set_fml_var fml_max_time 30M

set_app_var fml_cc_coverage_analyzer true
set_app_var fml_cov_tgl_input_port true

proc_set_design_blackboxes

# Reading design
source rtl.analyze.tcl
elaborate $design -cov tgl -vcs "-cm_tgl portsonly"

# Reporting read violations, and blackboxes and formal results
report_read_violations -verbose -file report_read_violations.txt
report_blackbox -verbose > blackbox.txt

# csv parameters
load_cc_set_param csv_prop_name "%1%"
load_cc_set_param csv_src "%2%"
load_cc_set_param csv_dest "%3%"
load_cc_set_param csv_enable "%4%"

load_cc_set_param csv_start_line "${start_line}"

# load csv file
proc_load_csv

#-------------------------------------------------------
# Running Verification
#-------------------------------------------------------

run
