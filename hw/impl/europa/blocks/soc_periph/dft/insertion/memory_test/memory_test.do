# Settings
set DESIGN            soc_periph_p
set DESIGN_ID         rtl1
set BLACKBOXES        {  }
set USE_PREPROCESSING  0

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
read_mem_libs

#define macro
set_design_macros COMBO_PHY_R06_SDEMMC AXE_SDHC_EXTERNAL_PADS CDNSSYNTHESIS CDNS_SYNTHESIS

dofile ${DEPENDENCIES_DIR}/read_rtl.do

set_current_design ${DESIGN}

set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}


if { $USE_PREPROCESSING } {
  
  set_context dft -rtl -design_id ${DESIGN_ID}a
  
  set_system_mode insertion

  write_design -tsdb

  set_system_mode setup
  set_context dft -rtl -design_id ${DESIGN_ID}
}



add_clock 0 i_emmc_clk  -period 5ns
add_clock 0 i_periph_clk -period 10ns 
#add_clock 0 i_spi_clk_in -period 10ns 
#add_clock 0 i_i2c_0_clk -period 1ns -pulse_always
#add_clock 0 i_i2c_1_clk -period 1ns -pulse_always 


add_input_constraints i_global_rst_n -c1
add_input_constraints i_ao_rst_n -c1


#add_dft_signals shift_capture_clock -source_nodes i_periph_clk
add_dft_signals scan_en -source scan_en

report_memory_instances -limit 128

set_dft_specification_requirements -memory_test on -host_scan_interface_type tap

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [file exists ${DESIGN}.def ] } {
  read_def ${DESIGN}.def
}

add_config_tdr

set_system_mode analysis

#if { [file exists dftSpec.${DESIGN}.${DESIGN_ID}.memory_test]} {
#  puts "Sourcing DFT Specification file"
#  read_config_data dftSpec.${DESIGN}.${DESIGN_ID}.memory_test
#  set dftSpec /DftSpecification(${DESIGN},${DESIGN_ID})
#} else {
#  puts "WARNING: Using default DFT Specification"
#  set dftSpec [create_dft_specification]
#  write_config_data dftSpec.${DESIGN}.${DESIGN_ID}.memory_test -wrappers $dftSpec -original_hierarchy -no_banner
#}
  
set dftSpec [create_dft_specification]
write_config_data dftSpec.${DESIGN}.${DESIGN_ID}.memory_test -wrappers $dftSpec -original_hierarchy -no_banner -replace

report_config_data $dftSpec


proc process_dft_specification.post_insertion {[get_current_design] args} {
  global DESIGN
  global DESIGN_ID

  puts "post processing script to connect scan control pins"
  create_instance -of_module axe_tcl_std_inverter inst_i_global_rst_n_scan_inverter
  create_connection i_global_rst_n inst_i_global_rst_n_scan_inverter/i_a

  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable
  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable inst_i_global_rst_n_scan_inverter/o_z

#  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_static_clock_control_mode
#  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_static_clock_control_mode test_mode

}
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

extract_icl

set patSpec [create_patterns_specification]
report_config_data $patSpec
process_patterns_specification

exit
