# Settings
set DESIGN            soc_mgmt_p
set DESIGN_ID         rtl1
set USE_PREPROCESSING 0
set USE_TAP_TSDB      0
set BLACKBOXES        { c2c_monitor kse3_ip \
                       sf_efuse10kbx40_a100_ln05lpe_4006000 \
                       sf_otp16kb_cp_a100_ln05lpe_4006000 \
                       tu_pll0519a01_ln05lpe_4007002 \
                       tu_pvt0501a01_ln05lpe_4007002}

set_context dft -rtl -design_id ${DESIGN_ID}

set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
read_mem_libs

if { $USE_TAP_TSDB } {
    open_tsdb ../tap_test/tsdb_outdir
    read_design ${DESIGN} -design_id rtl0
} else {
    dofile ${DEPENDENCIES_DIR}/read_rtl.do
}

#read_verilog -format sv2009  /opt/synopsys/syn2/T-2022.03-SP3/dw/dw04/src_ver/DW_tap.v

read_icl ../../../../../dft/icl/icl_models.icl

#set_module_matching_options -module_name_map_list {DW_tap DW_tap@PV1}

set_current_design ${DESIGN}
set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}

if { $USE_PREPROCESSING } {
  set_context dft -rtl -design_id ${DESIGN_ID}_a
  
  set_system_mode insertion
  

  #create_instance tessent_fake_tdo_en_or_gate -of_module axe_tcl_std_or3
  #create_connection u_soc_mgmt/u_soc_mgmt_clk_gen/u_dw_tap_clkgen/tdo_en tessent_fake_tdo_en_or_gate/i_a
  #create_connection u_soc_mgmt/u_ncejdtm200/ncejdtm200_tap/tdo_out_en tessent_fake_tdo_en_or_gate/i_a
  #delete_connections u_soc_mgmt/u_ncejdtm200/tdo_out_en
   
  write_design -tsdb
  set_system_mode setup
  set_context dft -rtl -design_id ${DESIGN_ID}
}

# DFT Signal used for logic test
add_dft_signals ltest_en  -source test_mode -make_ijtag_port

add_clock 0 i_ref_clk	    -period 20ns -pulse_always
# this is a func jtag clk
#add_clock 0 i_jtag_tck      -period 20ns -pulse_always
    
# add internal clocks for drc check
#add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_clk_int_2_freq_meter[3]		    -period 20ns -pulse_always
#add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_clk_int_2_freq_meter[2]		    -period 20ns -pulse_always
#add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_clk_int_2_freq_meter[1]		    -period 20ns -pulse_always
#add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_clk_int_2_freq_meter[0]		    -period 20ns -pulse_always
add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_fast_clk_int       -period 20ns -pulse_always
add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_pvt_clk	       -period 20ns -pulse_always
add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_periph_clk_int     -period 20ns -pulse_always

# add reset signals
add_input_constraints [get_ports i*_rst_n] -c1

report_memory_instances -limit 128

set_dft_specification_requirements -memory_test on -host_scan_interface_type tap

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [file exists ${DESIGN}.def ] } {
  read_def ${DESIGN}.def
}

add_config_tdr

set_system_mode analysis

set dftSpec [create_dft_specification -rep]

delete_config_element [get_config_elements -hier HostBscan -in_wrapper $dftSpec]

#set_config_value Interface/tdo_en -in_wrapper [get_config_elements -hier HostScanInterface(tap)] tessent_fake_tdo_en_or_gate/i_b

report_config_data $dftSpec


write_config_data dftSpec.${DESIGN}.${DESIGN_ID}.memory_test -wrappers $dftSpec -original_hierarchy -no_banner -replace

proc process_dft_specification.post_insertion {[get_current_design] args} {

  global DESIGN
  global DESIGN_ID

  puts "post processing script to connect scan control pins"

#  create_instance -of_module axe_tcl_std_inverter inst_i_por_rst_n_scan_inverter
#  create_connection i_por_rst_n inst_i_por_rst_n_scan_inverter/i_a 

#  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable
#  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable inst_i_por_rst_n_scan_inverter/o_z 

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
#}

report_config_data $dftSpec

process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

# temp ignore ncejdtm200_tap during extraction
set_attribute_value [get_pins  pwr_rst_n -of_instances [get_instances -of_modules ncejdtm200_tap*]] -name ignore_during_icl_extraction -value true
#set_attribute_value [get_instance -of_modules DW_tap*] -name ignore_during_icl_extraction -value true

extract_icl

set patSpec [create_patterns_specification]
report_config_data $patSpec
process_patterns_specification

exit
