#-------------------------------------------------------
# Setup Specific to DUT
#-------------------------------------------------------
set design_spec {{ cookiecutter.design_name }}
set design_impl {{ cookiecutter.design_name }}

proc proc_set_mem_timeout {} {
  set_fml_var fml_max_time 1H
  set_fml_var fml_max_mem 16GB
  # set_fml_var fml_witness_on true
}

proc proc_set_abstraction {} {
  # type can be {mem, mult, add, sub, div, mod}
  #set_compile_abstractions -construct {mem=256}
}

proc proc_mapping {} {
  map_by_name
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
  create_clock -period 10 spec.i_clk
}

proc proc_set_rsts {} {
  # Defining resets
  create_reset spec.i_rst_n -async -type load -sense low -disable_assertions_db
}

proc proc_set_snip_drivers {} {
  # Adding snip drivers if applicable
  # snip_driver -verdi { { mem_req } }
  # snip_driver [get_nets u_l2_mem.g_bank[*].u_l2_bank.ram_rsp]
}
