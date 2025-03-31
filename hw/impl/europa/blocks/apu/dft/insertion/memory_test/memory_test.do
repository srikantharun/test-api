# Settings
set DESIGN            apu_p
set DESIGN_ID         rtl1
set USE_PREPROCESSING 0
set DFT_HOME [getenv DFT_HOME]
set READ_LOCAL_TSDB 0

set BLACKBOXES        { tu_tem0501ar01_ln05lpe_4007002 }
lappend BLACKBOXES    {process1_monitor}
lappend BLACKBOXES    {process2_monitor}
lappend BLACKBOXES    {svs_monitor}

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

# read sub-partitions tsdb
if {$READ_LOCAL_TSDB} {
  set APU_L2C_TSDB  ../../../../apu_l2c/dft/insertion
  set APU_CORE_TSDB ../../../../apu_core/dft/insertion
} else {
  set APU_L2C_TSDB  ${DFT_HOME}/apu_l2c/Latest/tsdb
  set APU_CORE_TSDB ${DFT_HOME}/apu_core/Latest/tsdb
}

open_tsdb ${APU_L2C_TSDB}/memory_test/tsdb_outdir
open_tsdb ${APU_CORE_TSDB}/memory_test/tsdb_outdir
open_tsdb ${APU_L2C_TSDB}/logic_test/tsdb_outdir
open_tsdb ${APU_CORE_TSDB}/logic_test/tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
read_mem_libs
#set_read_verilog_options -vcs_compatibility on
dofile ${DEPENDENCIES_DIR}/read_rtl.do

read_design apu_core_p -design_identifier rtl2 -no_hdl
read_design apu_l2c_p  -design_identifier rtl2 -no_hdl

set_current_design ${DESIGN}
set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}


if { $USE_PREPROCESSING } {
  
  set_context dft -rtl -design_id rtl_fix_mbist
  set_system_mode insertion
  delete_connection u_apu/i_test_mode
  create_connection i_test_mode u_apu/i_test_mode
  create_port bisr_clk
  write_design -tsdb

  set_system_mode setup
  set_context dft -rtl -design_id ${DESIGN_ID}
}


# DFT Signal used for logic test
add_dft_signals ltest_en  -source test_mode -make_ijtag_port
#add_dft_signals ltest_en  -create_with_tdr

# define clocka
add_clock   0 i_clk     -period 0.8ns
add_clock   0 i_ref_clk -period 20ns -pulse_always
add_clock     u_apu/u_axe_ax65_cluster/u_apu_pmu/u_l2c_clk_div_by_2/o_clk -REFERENCE i_clk -FREQ_Divider 2
add_clock     g_mtime_clk_div2[1].u_mtime_clk_div2/o_clk                  -REFERENCE i_ref_clk -FREQ_Divider 4

# define pi constraints
add_input_constraints i_global_rst_n -c1
add_input_constraints i_ao_rst_n     -c1

report_memory_instances -limit 128

# add MBIST and TAP controller
set_dft_specification_requirements -memory_test on -host_scan_interface_type tap

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [file exists ${DESIGN}.def ] } {
  read_def ${DESIGN}.def
}

add_config_tdr

set_system_mode analysis

# create dft spec
set dftSpec [create_dft_specification -replace]

# specify rom content file
foreach_in_collection item [get_config_elements rom_content_file -hier ] {
   set element [get_attribute_value_list $item -name name]
   set element_value [get_config_value $element]

   if {$element_value ne ""} {
     set parent [get_config_value $element -parent_name]
     set module [get_attribute_value_list [get_modules -of_instances [get_config_value $parent/instance_name]\/u_mem] -name name]
     #MEM_LIBS_PATH defined in setup tcl file
     set index [lsearch -glob $MEM_LIBS_PATH *$module*]
     set rom_path [lindex $MEM_LIBS_PATH $index]
     set_config_value $parent/rom_content_file $rom_path/$module.romcode   
   } else {
     puts "$element isn't of type rom"
   }
}

write_config_data dftSpec.${DESIGN}.${DESIGN_ID}.memory_test -wrappers $dftSpec -original_hierarchy -no_banner -replace

proc process_dft_specification.post_insertion {[get_current_design] args} {

  global DESIGN
  global DESIGN_ID

  puts "post processing script to connect scan control pins"

  create_instance -of_module axe_tcl_std_inverter inst_i_global_rst_n_scan_inverter
  create_connection i_global_rst_n inst_i_global_rst_n_scan_inverter/i_a 

  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable
  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable inst_i_global_rst_n_scan_inverter/o_z 

  # fix reset in mbist mode
  create_instance -of_module axe_tcl_std_or2 u_pctl/dft_fix_scan_or_mbist_mode
  create_connection ${DESIGN}_rtl1_tessent_tdr_sri_ctrl_inst/all_test u_pctl/dft_fix_scan_or_mbist_mode/i_a
  create_connection u_pctl/i_test_mode u_pctl/dft_fix_scan_or_mbist_mode/i_b
  delete_connections [get_pins u_pctl/g_ppmu[*].u_ppmu/i_test_mode]
  delete_connections u_pctl/u_rst_sync_global/i_test_mode
  create_connection u_pctl/dft_fix_scan_or_mbist_mode/o_z [get_pins u_pctl/g_ppmu[*].u_ppmu/i_test_mode]
  create_connection u_pctl/dft_fix_scan_or_mbist_mode/o_z u_pctl/u_rst_sync_global/i_test_mode

#  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_static_clock_control_mode
#  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_static_clock_control_mode test_mode
#
#  set N_icg_se [sizeof_collection [get_pins -hierarchical tessent_persistent_cell_GATING_BIST_CLK/i_test_en]]
#  set icg_se_pins  [get_pins -hierarchical tessent_persistent_cell_GATING_BIST_CLK/i_test_en]
#  foreach_in_collection pin $icg_se_pins {
#      echo [get_name_list $pin] >> rpt/icg_se_pins.rpt
#  }
#  for {set i 0} {$i < $N_icg_se} {incr i} { 
#  delete_connections [get_name_list [index_collection $icg_se_pins $i]]
#  create_connection [get_name_list [index_collection $icg_se_pins $i]] i_scan_enable
#  }
#
}

report_config_data $dftSpec
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

# masking drc errors
set_drc_handling I5 warn

extract_icl

set patSpec [create_patterns_specification]
report_config_data $patSpec
process_patterns_specification

exit
