# Settings
set DESIGN            pve_p
set DESIGN_ID         rtl1
set BLACKBOXES        { process1_monitor process2_monitor svs_monitor tu_tem0501ar01_ln05lpe_4007002 }

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

open_tsdb $env(DFT_HOME)/pve_cva6v/Latest/tsdb/memory_test/tsdb_outdir
open_tsdb $env(DFT_HOME)/pve_l1/Latest/tsdb/memory_test/tsdb_outdir
open_tsdb $env(DFT_HOME)/pve_cva6v/Latest/tsdb/logic_test/tsdb_outdir
open_tsdb $env(DFT_HOME)/pve_l1/Latest/tsdb/logic_test/tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
read_mem_libs

# Error: Enum can only be assigned to same enum type or enum member. 
# When set to on, instructs the tool to bypass specified LRM Verilog rules.
set_read_verilog_options -allow_enum_relaxation on

dofile ${DEPENDENCIES_DIR}/read_rtl.do

read_design pve_cva6v_p -verbose -design_id rtl2 -no_hdl
read_verilog -format sv2009 $env(DFT_HOME)/pve_cva6v/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/pve_cva6v_p_rtl2.dft_inserted_design/pve_cva6v_p.sv09_interface
read_design pve_l1_p -verbose -design_id rtl2 -no_hdl
read_verilog -format sv2009 $env(DFT_HOME)/pve_l1/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/pve_l1_p_rtl2.dft_inserted_design/pve_l1_p.sv09_interface

set_current_design ${DESIGN}
set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}

add_clocks 0 i_ref_clk -period 20ns
add_clocks 0 i_clk -period 0.833ns

# define pi constraints
add_input_constraints i_global_rst_n -c1
add_input_constraints i_ao_rst_n -c1
add_primary_inputs u_pve/\g_cluster[0].u_cluster/\g_cpu[0].u_cva6v/i_rst_n -pseudo_port_name cva6v_rstn0
add_primary_inputs u_pve/\g_cluster[1].u_cluster/\g_cpu[0].u_cva6v/i_rst_n -pseudo_port_name cva6v_rstn1
add_primary_inputs u_pve/\g_cluster[2].u_cluster/\g_cpu[0].u_cva6v/i_rst_n -pseudo_port_name cva6v_rstn2
add_primary_inputs u_pve/\g_cluster[3].u_cluster/\g_cpu[0].u_cva6v/i_rst_n -pseudo_port_name cva6v_rstn3
add_primary_inputs u_pve/\g_cluster[0].u_cluster/\g_cpu[1].u_cva6v/i_rst_n -pseudo_port_name cva6v_rstn4
add_primary_inputs u_pve/\g_cluster[1].u_cluster/\g_cpu[1].u_cva6v/i_rst_n -pseudo_port_name cva6v_rstn5
add_primary_inputs u_pve/\g_cluster[2].u_cluster/\g_cpu[1].u_cva6v/i_rst_n -pseudo_port_name cva6v_rstn6
add_primary_inputs u_pve/\g_cluster[3].u_cluster/\g_cpu[1].u_cva6v/i_rst_n -pseudo_port_name cva6v_rstn7
add_primary_inputs u_pve/\g_cluster[0].u_cluster/u_pve_l1/i_rst_n -pseudo_port_name l1_rstn0
add_primary_inputs u_pve/\g_cluster[1].u_cluster/u_pve_l1/i_rst_n -pseudo_port_name l1_rstn1
add_primary_inputs u_pve/\g_cluster[2].u_cluster/u_pve_l1/i_rst_n -pseudo_port_name l1_rstn2
add_primary_inputs u_pve/\g_cluster[3].u_cluster/u_pve_l1/i_rst_n -pseudo_port_name l1_rstn3

add_input_constraints cva6v_rstn0 -c1
add_input_constraints cva6v_rstn1 -c1
add_input_constraints cva6v_rstn2 -c1
add_input_constraints cva6v_rstn3 -c1
add_input_constraints cva6v_rstn4 -c1
add_input_constraints cva6v_rstn5 -c1
add_input_constraints cva6v_rstn6 -c1
add_input_constraints cva6v_rstn7 -c1
add_input_constraints l1_rstn0 -c1
add_input_constraints l1_rstn1 -c1
add_input_constraints l1_rstn2 -c1
add_input_constraints l1_rstn3 -c1

report_memory_instances -limit 128

# add MBIST and TAP controller
set_dft_specification_requirements -memory_test on -host_scan_interface_type tap

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [info exists env(PD_HOME)] } {
  if { [file exists $env(PD_HOME)/floorplan/${DESIGN}.def ] } {
    read_def $env(PD_HOME)/floorplan/${DESIGN}.def
  }
}

add_config_tdr
add_dft_control_points [get_pin u_pctl/i_test_mode] -dft_signal_source_name all_test

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

  create_instance -of_module axe_tcl_std_inverter inst_i_global_rst_n_scan_inverter
  create_connection i_global_rst_n inst_i_global_rst_n_scan_inverter/i_a 

  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable
  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable inst_i_global_rst_n_scan_inverter/o_z 

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
