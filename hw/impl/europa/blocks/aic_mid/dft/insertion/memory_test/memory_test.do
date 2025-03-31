# Settings
set DESIGN            aic_mid_p
set DESIGN_ID         rtl1
set BLACKBOXES        { \
                        imc_bank \
                        tu_tem0501ar01_ln05lpe_4007002 \
                        svs_monitor \
                        process1_monitor \
                        process2_monitor \
                        c2c_monitor \
                      }

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
read_mem_libs

dofile ${DEPENDENCIES_DIR}/read_rtl.do

# Create custom BISR hookups
create_custom_bisr_register imc_bisr_reg -size 32 -repl -output_directory tsdb_outdir/instruments
#system "sed -i '/D\[31:0\]/s/allowed_tied/allowed_no_source/g' tsdb_outdir/instruments/imc_bisr_reg.icl"
file copy -force imc_bisr_reg.v imc_bisr_reg.icl tsdb_outdir/instruments
read_verilog tsdb_outdir/instruments/imc_bisr_reg.v
read_icl     tsdb_outdir/instruments/imc_bisr_reg.icl

set_current_design ${DESIGN}
set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}

# Insert custom BISR hookups
set_context dft -rtl -design_id ${DESIGN_ID}a
set_system_mode insertion

create_instance u_bisr_hook_core -of imc_bisr_reg -below [get_name_list [index_collection [get_instances -of_modules imc_bisr_hook] 0]]

write_design -tsdb
set_system_mode setup
set_context dft -rtl -design_id ${DESIGN_ID}

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

proc get_hook_path { pair_id side_id wrapper_id } {
  return "u_aic_mid/u_mvm/i_mvm_dp/inst_mvm_imc_acc/g_imc_acc_pairs\[${pair_id}\].inst_mvm_imc_acc_pair/inst_imc_bank_acc_${side_id}/inst_imc_w_acc/u_mvm_imc_bank_combiner/g_imc_bank_wrapper\[${wrapper_id}\].u_mvm_imc_bank_wrapper/u_imc_bisr_hook"
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

  # AIC_MID specific
  # Connect IMC BIST DataOutPorts
  set MVM_JTAG_TDR u_aic_mid/u_mvm/i_mvm_jtag_tdr
  set data_out_pins [get_pins -bundle ${MVM_JTAG_TDR}/i_mvm_jtag_tdr_core/o_*]
  foreach_in_collection pin $data_out_pins {
    set leaf_name [get_attribute_value_list $pin -name leaf_name]
    create_connection ${MVM_JTAG_TDR}/i_mvm_jtag_tdr_core/${leaf_name} ${MVM_JTAG_TDR}/[regsub ^o_ ${leaf_name} core_]
  }

  # Connect IMC BISR chain
  set bisr_hooks [get_instances -of_modules imc_bisr_hook]
  foreach_in_collection bisr_hook $bisr_hooks {
    set hook_path [lindex [get_name_list $bisr_hook] 0]
    # Unused signals
    create_connection ${hook_path}/u_bisr_hook_core/MSEL -constant 0
    create_connection ${hook_path}/u_bisr_hook_core/MSO -constant 0
  }
  # Single create_connections produces a much cleaner RTL output, it allows Tessent to recognize the connections do not need to traverse hierarchies or be uniquified
  # (at the obvious cost of a verbose doscript)
  set cmd " \
  create_connections { \
    [get_hook_path 0 a 0]/hook_core_d [get_hook_path 0 a 1]/hook_core_d [get_hook_path 0 b 0]/hook_core_d [get_hook_path 0 b 1]/hook_core_d \
    [get_hook_path 1 a 0]/hook_core_d [get_hook_path 1 a 1]/hook_core_d [get_hook_path 1 b 0]/hook_core_d [get_hook_path 1 b 1]/hook_core_d \
    [get_hook_path 2 a 0]/hook_core_d [get_hook_path 2 a 1]/hook_core_d [get_hook_path 2 b 0]/hook_core_d [get_hook_path 2 b 1]/hook_core_d \
    [get_hook_path 3 a 0]/hook_core_d [get_hook_path 3 a 1]/hook_core_d [get_hook_path 3 b 0]/hook_core_d [get_hook_path 3 b 1]/hook_core_d \
    [get_hook_path 4 a 0]/hook_core_d [get_hook_path 4 a 1]/hook_core_d [get_hook_path 4 b 0]/hook_core_d [get_hook_path 4 b 1]/hook_core_d \
    [get_hook_path 5 a 0]/hook_core_d [get_hook_path 5 a 1]/hook_core_d [get_hook_path 5 b 0]/hook_core_d [get_hook_path 5 b 1]/hook_core_d \
    [get_hook_path 6 a 0]/hook_core_d [get_hook_path 6 a 1]/hook_core_d [get_hook_path 6 b 0]/hook_core_d [get_hook_path 6 b 1]/hook_core_d \
    [get_hook_path 7 a 0]/hook_core_d [get_hook_path 7 a 1]/hook_core_d [get_hook_path 7 b 0]/hook_core_d [get_hook_path 7 b 1]/hook_core_d \
    \
    [get_hook_path 0 a 0]/u_bisr_hook_core/Q [get_hook_path 0 a 1]/u_bisr_hook_core/Q [get_hook_path 0 b 0]/u_bisr_hook_core/Q [get_hook_path 0 b 1]/u_bisr_hook_core/Q \
    [get_hook_path 1 a 0]/u_bisr_hook_core/Q [get_hook_path 1 a 1]/u_bisr_hook_core/Q [get_hook_path 1 b 0]/u_bisr_hook_core/Q [get_hook_path 1 b 1]/u_bisr_hook_core/Q \
    [get_hook_path 2 a 0]/u_bisr_hook_core/Q [get_hook_path 2 a 1]/u_bisr_hook_core/Q [get_hook_path 2 b 0]/u_bisr_hook_core/Q [get_hook_path 2 b 1]/u_bisr_hook_core/Q \
    [get_hook_path 3 a 0]/u_bisr_hook_core/Q [get_hook_path 3 a 1]/u_bisr_hook_core/Q [get_hook_path 3 b 0]/u_bisr_hook_core/Q [get_hook_path 3 b 1]/u_bisr_hook_core/Q \
    [get_hook_path 4 a 0]/u_bisr_hook_core/Q [get_hook_path 4 a 1]/u_bisr_hook_core/Q [get_hook_path 4 b 0]/u_bisr_hook_core/Q [get_hook_path 4 b 1]/u_bisr_hook_core/Q \
    [get_hook_path 5 a 0]/u_bisr_hook_core/Q [get_hook_path 5 a 1]/u_bisr_hook_core/Q [get_hook_path 5 b 0]/u_bisr_hook_core/Q [get_hook_path 5 b 1]/u_bisr_hook_core/Q \
    [get_hook_path 6 a 0]/u_bisr_hook_core/Q [get_hook_path 6 a 1]/u_bisr_hook_core/Q [get_hook_path 6 b 0]/u_bisr_hook_core/Q [get_hook_path 6 b 1]/u_bisr_hook_core/Q \
    [get_hook_path 7 a 0]/u_bisr_hook_core/Q [get_hook_path 7 a 1]/u_bisr_hook_core/Q [get_hook_path 7 b 0]/u_bisr_hook_core/Q [get_hook_path 7 b 1]/u_bisr_hook_core/Q \
  } { \
    [get_hook_path 0 a 0]/u_bisr_hook_core/D [get_hook_path 0 a 1]/u_bisr_hook_core/D [get_hook_path 0 b 0]/u_bisr_hook_core/D [get_hook_path 0 b 1]/u_bisr_hook_core/D \
    [get_hook_path 1 a 0]/u_bisr_hook_core/D [get_hook_path 1 a 1]/u_bisr_hook_core/D [get_hook_path 1 b 0]/u_bisr_hook_core/D [get_hook_path 1 b 1]/u_bisr_hook_core/D \
    [get_hook_path 2 a 0]/u_bisr_hook_core/D [get_hook_path 2 a 1]/u_bisr_hook_core/D [get_hook_path 2 b 0]/u_bisr_hook_core/D [get_hook_path 2 b 1]/u_bisr_hook_core/D \
    [get_hook_path 3 a 0]/u_bisr_hook_core/D [get_hook_path 3 a 1]/u_bisr_hook_core/D [get_hook_path 3 b 0]/u_bisr_hook_core/D [get_hook_path 3 b 1]/u_bisr_hook_core/D \
    [get_hook_path 4 a 0]/u_bisr_hook_core/D [get_hook_path 4 a 1]/u_bisr_hook_core/D [get_hook_path 4 b 0]/u_bisr_hook_core/D [get_hook_path 4 b 1]/u_bisr_hook_core/D \
    [get_hook_path 5 a 0]/u_bisr_hook_core/D [get_hook_path 5 a 1]/u_bisr_hook_core/D [get_hook_path 5 b 0]/u_bisr_hook_core/D [get_hook_path 5 b 1]/u_bisr_hook_core/D \
    [get_hook_path 6 a 0]/u_bisr_hook_core/D [get_hook_path 6 a 1]/u_bisr_hook_core/D [get_hook_path 6 b 0]/u_bisr_hook_core/D [get_hook_path 6 b 1]/u_bisr_hook_core/D \
    [get_hook_path 7 a 0]/u_bisr_hook_core/D [get_hook_path 7 a 1]/u_bisr_hook_core/D [get_hook_path 7 b 0]/u_bisr_hook_core/D [get_hook_path 7 b 1]/u_bisr_hook_core/D \
    \
    [get_hook_path 0 a 0]/hook_core_q [get_hook_path 0 a 1]/hook_core_q [get_hook_path 0 b 0]/hook_core_q [get_hook_path 0 b 1]/hook_core_q \
    [get_hook_path 1 a 0]/hook_core_q [get_hook_path 1 a 1]/hook_core_q [get_hook_path 1 b 0]/hook_core_q [get_hook_path 1 b 1]/hook_core_q \
    [get_hook_path 2 a 0]/hook_core_q [get_hook_path 2 a 1]/hook_core_q [get_hook_path 2 b 0]/hook_core_q [get_hook_path 2 b 1]/hook_core_q \
    [get_hook_path 3 a 0]/hook_core_q [get_hook_path 3 a 1]/hook_core_q [get_hook_path 3 b 0]/hook_core_q [get_hook_path 3 b 1]/hook_core_q \
    [get_hook_path 4 a 0]/hook_core_q [get_hook_path 4 a 1]/hook_core_q [get_hook_path 4 b 0]/hook_core_q [get_hook_path 4 b 1]/hook_core_q \
    [get_hook_path 5 a 0]/hook_core_q [get_hook_path 5 a 1]/hook_core_q [get_hook_path 5 b 0]/hook_core_q [get_hook_path 5 b 1]/hook_core_q \
    [get_hook_path 6 a 0]/hook_core_q [get_hook_path 6 a 1]/hook_core_q [get_hook_path 6 b 0]/hook_core_q [get_hook_path 6 b 1]/hook_core_q \
    [get_hook_path 7 a 0]/hook_core_q [get_hook_path 7 a 1]/hook_core_q [get_hook_path 7 b 0]/hook_core_q [get_hook_path 7 b 1]/hook_core_q \
  }"
  puts $cmd
  eval $cmd
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
