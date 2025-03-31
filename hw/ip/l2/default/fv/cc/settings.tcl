#-------------------------------------------------------
# Setup Specific to DUT
#-------------------------------------------------------
set design l2

proc proc_set_design_blackboxes {} {
  # Set blackboxes if needed
  set_blackbox -designs {axi2reg tc_* cc_*}
  # Set design hierarchy at level N and below as black box
  # set_blackbox -level <N>
}

proc proc_load_csv {} {
  # Load csv file
  load_cc -format csv ../connections.csv
}

proc run {} {
  proc_run_proves
  
  # Saving session
  save_session
}
