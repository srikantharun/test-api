#-------------------------------------------------------
# Setup Specific to DUT
#-------------------------------------------------------
set design ai_core_p

# Define new start line for top-level CC
global start_line
set start_line 9

proc proc_set_design_blackboxes {} {
  # Set blackboxes if needed
  set_blackbox -designs { aic_mid_p aic_did_p aic_infra_p aic_ls_p pctl ai_core_cfg_csr_reg_top axe_tcl_seq_sync }
  # Set design hierarchy at level N and below as black box
  # set_blackbox -level N
}

proc proc_load_csv {} {
  # Load csv file
  load_cc -format csv ../build_cc/connections.csv
}

proc run {} {
  proc_run_proves
  
  # Saving session
  save_session
}
