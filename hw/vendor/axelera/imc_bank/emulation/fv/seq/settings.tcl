#-------------------------------------------------------
# Setup specfic to DUT
#-------------------------------------------------------
set design_spec imc_bank
set design_impl imc_bank

proc proc_set_mem_timeout {} {
  set_fml_var fml_max_time 1H
  set_fml_var fml_max_mem 16GB
  # set_fml_var fml_witness_on true
}

proc proc_set_abstraction {} {
  # type can be {mem, mult, add, sub, div, mod}
  # set_compile_abstractions {mem}
}

proc proc_mapping {} {
  map_by_name
  seqmap -regex impl.*OUT spec.*OUT
  seqmap -regex impl.*WEIGHTS spec.*WEIGHTS
  seqmap -regex impl.*compute_block_enable_q spec.*compute_block_enable_q
  seqmap -regex impl.*compute_enable_q spec.*compute_enable_q
  seqmap -regex impl.*compute_inp_q spec.*compute_inp_q
  seqmap -regex impl.*compute_weight_format_q spec.*compute_weight_format_q
  seqmap -regex impl.*compute_wss_q spec.*compute_wss_q
  seqmap -regex impl.*concurrent_compute_write_conflict spec.*concurrent_compute_write_conflict
  seqmap -regex impl.*pipeline_stall_write_conflict spec.*pipeline_stall_write_conflict
  seqmap -regex impl.*write_enable_q spec.*write_enable_q
  seqmap -regex impl.*write_wss_q spec.*write_wss_q
  seqmap -regex impl.*REPAIR spec.*REPAIR
  seqmap -regex impl.*reset_used_reg spec.*reset_used_reg
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
  create_clock -period 10 spec.clock
}

proc proc_set_rsts {} {
  # Defining resets
  create_reset spec.rst_n -async -type load -sense low -disable_assertions_db
}

proc proc_set_snip_drivers {} {
  # Adding snip drivers if applicable
  # snip_driver -verdi { { mem_req } }
  # snip_driver [get_nets u_l2_mem.g_bank[*].u_l2_bank.ram_rsp]
}
