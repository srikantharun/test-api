#-------------------------------------------------------
# Setup Specific to DUT
#-------------------------------------------------------
set design europa

# Define new start line for top-level CC
global start_line
set start_line 9

proc proc_set_design_blackboxes {} {
  # Set blackboxes if needed
  set_blackbox -designs { ai_core_p apu_p dcd_p l2_p lpddr_p noc_top pcie_p pve_p soc_mgmt_p soc_periph_p sys_spm_p axe_tcl_pad_inout ddr_west_clock_gen_p }
  # Set design hierarchy at level N and below as black box
  # set_blackbox -level <N>
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
