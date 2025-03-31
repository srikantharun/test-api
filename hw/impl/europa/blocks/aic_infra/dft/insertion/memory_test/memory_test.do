# Settings
set DESIGN            aic_infra_p
set DESIGN_ID         rtl1
set BLACKBOXES        {  }

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
read_mem_libs

# Error: Enum can only be assigned to same enum type or enum member.
# When set to “on”, instructs the tool to bypass specified LRM Verilog rules.
set_read_verilog_options -allow_enum_relaxation on

dofile ${DEPENDENCIES_DIR}/read_rtl.do

set_current_design ${DESIGN}
set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}

add_clock 0 i_clk -period 1ns
add_input_constraints i_rst_n -c1

add_dft_signals ltest_en -source test_mode -make_ijtag_port
add_dft_signals async_set_reset_static_disable
add_dft_signals control_test_point_en observe_test_point_en
add_dft_signals test_clock -source test_clk
add_dft_signals edt_update -source edt_update
add_dft_signals tck_occ_en
add_dft_signals scan_en -source scan_en
add_dft_signals edt_clock -create_from_other_signals
add_dft_signals shift_capture_clock -create_from_other_signals

report_memory_instances -limit 128

set_dft_specification_requirements -memory_test on

if { [file exists ${DESIGN}.bisr_segment_order] } {
  set_dft_specification_requirements -memory_test on -bisr_segment_order_file ${DESIGN}.bisr_segment_order
}

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [file exists ${DESIGN}.def ] } {
  read_def ${DESIGN}.def
}

add_config_tdr

set_system_mode analysis

if { [file exists dftSpec.${DESIGN}.${DESIGN_ID}.memory_test]} {
  puts "Sourcing DFT Specification file"
  read_config_data dftSpec.${DESIGN}.${DESIGN_ID}.memory_test
  set dftSpec /DftSpecification(${DESIGN},${DESIGN_ID})
} else {
  puts "WARNING: Using default DFT Specification"
  set dftSpec [create_dft_specification]
  write_config_data dftSpec.${DESIGN}.${DESIGN_ID}.memory_test -wrappers $dftSpec -original_hierarchy -no_banner
}

proc process_dft_specification.post_insertion {[get_current_design] args} {
  global DESIGN
  global DESIGN_ID

  puts "post processing script to connect scan control pins"
  create_instance -of_module axe_tcl_std_inverter inst_i_rst_n_scan_inverter
  create_connection i_rst_n inst_i_rst_n_scan_inverter/i_a

  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable
  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable inst_i_rst_n_scan_inverter/o_z

#  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_static_clock_control_mode
#  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_static_clock_control_mode test_mode

  set icg_se_pins [get_pins -hierarchical tessent_persistent_cell_GATING_BIST_CLK/i_test_en]
  foreach_in_collection pin $icg_se_pins {
    echo [get_name_list $pin] >> rpt/icg_se_pins.rpt
    delete_connection [get_name_list $pin]
    create_connection [get_name_list $pin] scan_en
  }
}

report_config_data $dftSpec
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

extract_icl

set patSpec [create_patterns_specification]
report_config_data $patSpec
process_patterns_specification

exit
