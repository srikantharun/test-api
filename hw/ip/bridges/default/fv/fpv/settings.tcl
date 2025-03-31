#-------------------------------------------------------
# Setup Specific to DUT
#-------------------------------------------------------
set design axe_ahb_to_apb

proc proc_set_mem_timeout {} {
  set_fml_var fml_max_time 1H
  set_fml_var fml_max_mem 16GB
}

proc proc_enable_AIP {} {
  # Enabling AIP like AXI4, AXIS, etc
  aip_load -protocol "AHB"
  aip_load -protocol "APB"
}

proc proc_set_design_blackboxes {} {
  # Set blackboxes if needed
  # set_blackbox -designs {axe_tcl_ram_1rwp axi2reg}
}

proc proc_set_clks {} {
  # Defining clocks
  create_clock -period 10 i_clk
}

proc proc_set_rsts {} {
  # Defining resets
  create_reset i_rst_n -async -type load -sense low -disable_assertions_db
}

proc proc_set_snip_drivers {} {
  # Adding snip drivers if applicable
}

proc run {} {
  proc_run_proves

  # proc_property_density
  # proc_over_constraint
  # proc_formal_core

  # Saving session
  save_session
}
