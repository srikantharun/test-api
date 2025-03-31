#-------------------------------------------------------
# Setup Specific to DUT
#-------------------------------------------------------
set design {{ cookiecutter.design_name }}

set ipxact __xml_location

proc proc_set_mem_timeout {} {
  set_fml_var fml_max_time 1H
  set_fml_var fml_max_mem 16GB
}

proc proc_enable_AIP {} {
  # Enabling AIP like AXI4, AXIS, etc
  # aip_load -protocol "APB"
}

proc proc_set_design_blackboxes {} {
  # Set blackboxes if needed
  # set_blackbox -designs {axe_tcl_sram axi2reg}
}

proc proc_set_clks {} {
  # Defining clocks
  create_clock -period 10 i_clk
}

proc proc_set_rsts {} {
  # Defining resets
  create_reset u_pppmu.o_ao_rst_sync_n -async -type load -sense low -disable_assertions_db
}

proc proc_set_snip_drivers {} {
  # Adding snip drivers if applicable
  # snip_driver -verdi { { mem_req } }
  # snip_driver [get_nets u_l2_mem.g_bank[*].u_l2_bank.ram_rsp]
}
