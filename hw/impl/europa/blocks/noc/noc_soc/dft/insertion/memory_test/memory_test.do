# Settings
set DESIGN            noc_soc_p
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

dofile ${DEPENDENCIES_DIR}/read_rtl.do

set_current_design ${DESIGN}
set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}

add_clock 0 i_apu_aon_clk -period 20.000ns
add clock 0 i_apu_x_clk -period 1.000ns
add_clock 0 i_dcd_aon_clk -period 20.000ns
add_clock 0 i_dcd_codec_clk -period 1.667ns
add_clock 0 i_dcd_mcu_clk -period 0.833ns
add_clock 0 i_noc_clk -period 0.833ns
add_clock 0 i_pcie_aon_clk -period 20.000ns
add_clock 0 i_pcie_init_mt_clk -period 1.667ns
add_clock 0 i_pcie_targ_cfg_clk -period 10ns
add_clock 0 i_pcie_targ_cfg_dbi_clk -period 10ns
add_clock 0 i_pcie_targ_mt_clk -period 1.667ns
add_clock 0 i_pve_0_aon_clk -period 20.000ns
add_clock 0 i_pve_0_clk -period 0.833ns
add_clock 0 i_pve_1_aon_clk -period 20.000ns
add_clock 0 i_pve_1_clk -period 0.833ns
add_clock 0 i_soc_mgmt_aon_clk -period 20.000ns
add_clock 0 i_soc_mgmt_clk -period 0.833ns
add_clock 0 i_sys_spm_aon_clk -period 20.000ns
add_clock 0 i_sys_spm_clk -period 0.833ns

add_input_constraints i_apu_aon_rst_n -C1
add_input_constraints i_apu_x_rst_n -C1
add_input_constraints i_dcd_aon_rst_n -C1
add_input_constraints i_dcd_codec_rst_n -C1
add_input_constraints i_dcd_mcu_rst_n -C1
add_input_constraints i_noc_rst_n -C1
add_input_constraints i_pcie_aon_rst_n -C1
add_input_constraints i_pcie_init_mt_rst_n -C1
add_input_constraints i_pcie_targ_cfg_dbi_rst_n -C1
add_input_constraints i_pcie_targ_cfg_rst_n -C1
add_input_constraints i_pcie_targ_mt_rst_n -C1
add_input_constraints i_pve_0_aon_rst_n -C1
add_input_constraints i_pve_0_rst_n -C1
add_input_constraints i_pve_1_aon_rst_n -C1
add_input_constraints i_pve_1_rst_n -C1
add_input_constraints i_soc_mgmt_aon_rst_n -C1
add_input_constraints i_soc_mgmt_rst_n -C1
add_input_constraints i_sys_spm_aon_rst_n -C1
add_input_constraints i_sys_spm_rst_n -C1
add_input_constraints i_pcie_init_mt_rst_n -C1
add_input_constraints i_pcie_targ_mt_rst_n  -C1
add_input_constraints i_pcie_targ_cfg_dbi_rst_n -C1
add_input_constraints i_pcie_targ_cfg_rst_n -C1

add_dft_signals scan_en -source scan_en

report_memory_instances -limit 128

set_dft_specification_requirements -memory_test on -host_scan_interface_type tap

if { [file exists ${DESIGN}.bisr_segment_order] } {
  set_dft_specification_requirements -memory_test on -host_scan_interface_type tap -bisr_segment_order_file ${DESIGN}.bisr_segment_order
}

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [info exists env(PD_HOME)] } {
  if { [file exists $env(PD_HOME)/floorplan/${DESIGN}.def ] } {
    read_def $env(PD_HOME)/floorplan/${DESIGN}.def
  }
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

  create_instance -of_module axe_tcl_std_inverter inst_i_noc_rst_n_scan_inverter
  create_connection i_noc_rst_n inst_i_noc_rst_n_scan_inverter/i_a 

  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable
  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable inst_i_noc_rst_n_scan_inverter/o_z 

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
