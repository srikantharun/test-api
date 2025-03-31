# Settings
set DESIGN            noc_soc_p
set DESIGN_ID         rtl2
set USE_MBIST_TSDB    1
set USE_PREPROCESSING 0
set BLACKBOXES        { }

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
read_mem_libs

if { $USE_MBIST_TSDB } {
    open_tsdb ../memory_test/tsdb_outdir
    read_design ${DESIGN} -design_id rtl1
} else {
    dofile ${DEPENDENCIES_DIR}/read_rtl.do
}

set_current_design ${DESIGN}
set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
} else {
  add_black_boxes -auto
}

add_dft_signals ltest_en -source test_mode -make_ijtag_port
add_dft_signals async_set_reset_static_disable
add_dft_signals control_test_point_en observe_test_point_en
add_dft_signals test_clock -source test_clk
add_dft_signals edt_update -source edt_update
add_dft_signals scan_en -source scan_en
add_dft_signals edt_clock -create_from_other_signals
add_dft_signals shift_capture_clock -create_from_other_signals
add_dft_signals tck_occ_en -create_with_tdr

add_input_constraints test_mode -C1

if { $USE_MBIST_TSDB == 0 } {
    add_clock 0 i_apu_aon_clk -period 20.000ns
    add_clock 0 i_apu_x_clk -period 1.000ns
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
}

report_dft_signals

set_dft_specification_requirements -logic_test on 


if { $USE_PREPROCESSING } {
  set_context dft -rtl -design_id ${DESIGN_ID}a
  set_system_mode insertion
  delete_ports {scan_in scan_out}
  write_design -tsdb

  set_system_mode setup
  set_context dft -rtl -design_id ${DESIGN_ID}
}

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [info exists env(PD_HOME)] } {
  if { [file exists $env(PD_HOME)/floorplan/${DESIGN}.def ] } {
    read_def $env(PD_HOME)/floorplan/${DESIGN}.def
  }
}

set_drc_handling dft_c9 -auto_fix off

set_system_mode analysis

set dftSpec [create_dft_specification -sri_sib_list {edt} ]
report_config_data $dftSpec

read_config_data -in_wrapper $dftSpec -from_string {

  EDT {
    ijtag_host_interface : Sib(edt);
    Controller (c1_int) {
      longest_chain_range    : 280, 300;
      scan_chain_count       : 2750;
      input_channel_count    : 30;
      output_channel_count   : 30;

      ShiftPowerOptions {
        present                            : on  ;
        full_control                       : on ;
        min_switching_threshold_percentage : 25 ;
      }
      Connections +{
        EdtChannelsIn(1) { port_pin_name : scan_in[0]; }
        EdtChannelsIn(2) { port_pin_name : scan_in[1]; }
        EdtChannelsIn(3) { port_pin_name : scan_in[2]; }
        EdtChannelsIn(4) { port_pin_name : scan_in[3]; }
        EdtChannelsIn(5) { port_pin_name : scan_in[4]; }
        EdtChannelsIn(6) { port_pin_name : scan_in[5]; }
        EdtChannelsIn(7) { port_pin_name : scan_in[6]; }
        EdtChannelsIn(8) { port_pin_name : scan_in[7]; }
        EdtChannelsIn(9) { port_pin_name : scan_in[8]; }
        EdtChannelsIn(10) { port_pin_name : scan_in[9]; }
        EdtChannelsIn(11) { port_pin_name : scan_in[10]; }
        EdtChannelsIn(12) { port_pin_name : scan_in[11]; }
        EdtChannelsIn(13) { port_pin_name : scan_in[12]; }
        EdtChannelsIn(14) { port_pin_name : scan_in[13]; }
        EdtChannelsIn(15) { port_pin_name : scan_in[14]; }
        EdtChannelsIn(16) { port_pin_name : scan_in[15]; }
        EdtChannelsIn(17) { port_pin_name : scan_in[16]; }
        EdtChannelsIn(18) { port_pin_name : scan_in[17]; }
        EdtChannelsIn(19) { port_pin_name : scan_in[18]; }
        EdtChannelsIn(20) { port_pin_name : scan_in[19]; }
        EdtChannelsIn(21) { port_pin_name : scan_in[20]; }
        EdtChannelsIn(22) { port_pin_name : scan_in[21]; }
        EdtChannelsIn(23) { port_pin_name : scan_in[22]; }
        EdtChannelsIn(24) { port_pin_name : scan_in[23]; }
        EdtChannelsIn(25) { port_pin_name : scan_in[24]; }
        EdtChannelsIn(26) { port_pin_name : scan_in[25]; }
        EdtChannelsIn(27) { port_pin_name : scan_in[26]; }
        EdtChannelsIn(28) { port_pin_name : scan_in[27]; }
        EdtChannelsIn(29) { port_pin_name : scan_in[28]; }
        EdtChannelsIn(30) { port_pin_name : scan_in[29]; }

        EdtChannelsOut(1) { port_pin_name : scan_out[0];}
        EdtChannelsOut(2) { port_pin_name : scan_out[1];}
        EdtChannelsOut(3) { port_pin_name : scan_out[2];}
        EdtChannelsOut(4) { port_pin_name : scan_out[3];}
        EdtChannelsOut(5) { port_pin_name : scan_out[4];}
        EdtChannelsOut(6) { port_pin_name : scan_out[5];}
        EdtChannelsOut(7) { port_pin_name : scan_out[6];}
        EdtChannelsOut(8) { port_pin_name : scan_out[7];}
        EdtChannelsOut(9) { port_pin_name : scan_out[8];}
        EdtChannelsOut(10) { port_pin_name : scan_out[9];}
        EdtChannelsOut(11) { port_pin_name : scan_out[10];}
        EdtChannelsOut(12) { port_pin_name : scan_out[11];}
        EdtChannelsOut(13) { port_pin_name : scan_out[12];}
        EdtChannelsOut(14) { port_pin_name : scan_out[13];}
        EdtChannelsOut(15) { port_pin_name : scan_out[14];}
        EdtChannelsOut(16) { port_pin_name : scan_out[15];}
        EdtChannelsOut(17) { port_pin_name : scan_out[16];}
        EdtChannelsOut(18) { port_pin_name : scan_out[17];}
        EdtChannelsOut(19) { port_pin_name : scan_out[18];}
        EdtChannelsOut(20) { port_pin_name : scan_out[19];}
        EdtChannelsOut(21) { port_pin_name : scan_out[20];}
        EdtChannelsOut(22) { port_pin_name : scan_out[21];}
        EdtChannelsOut(23) { port_pin_name : scan_out[22];}
        EdtChannelsOut(24) { port_pin_name : scan_out[23];}
        EdtChannelsOut(25) { port_pin_name : scan_out[24];}
        EdtChannelsOut(26) { port_pin_name : scan_out[25];}
        EdtChannelsOut(27) { port_pin_name : scan_out[26];}
        EdtChannelsOut(28) { port_pin_name : scan_out[27];}
        EdtChannelsOut(29) { port_pin_name : scan_out[28];}
        EdtChannelsOut(30) { port_pin_name : scan_out[29];}
      }
    }
  }
}

proc process_dft_specification.post_insertion {[get_current_design] args} {
  global DESIGN
  global DESIGN_ID
  set pattern {edt_scan_in\[(\d+)\]}
  foreach_in_collection pin [get_pins ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/edt_scan_in] {
       set leaf [get_attribute_value_list $pin -name name]
       set pin_leaf [get_attribute_value_list $pin -name leaf_name]
       puts "${pin_leaf}"
       regexp $pattern $leaf match index
       create_instance tessent_scan_buf_i_${index} -of_module axe_tcl_std_buffer
       create_connection ${leaf} tessent_scan_buf_i_${index}/i_a

  }

  set pattern {edt_scan_out\[(\d+)\]}
  #create_instance tessent_tie0_cell -of_module TIELO_D1_N_S6TR_C54L08
  foreach_in_collection pin [get_pins ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/edt_scan_out] {
       set leaf [get_attribute_value_list $pin -name name]
       set pin_leaf [get_attribute_value_list $pin -name leaf_name]
       regexp $pattern $leaf match index
       create_instance tessent_scan_buf_o_${index} -of_module axe_tcl_std_buffer
       delete_connection ${leaf}
       create_connection tessent_scan_buf_o_${index}/o_z ${leaf}
       #create_connection tessent_tie0_cell/Y tessent_scan_buf_o_${index}/i_a
  }
}

report_config_data $dftSpec
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

set_system_mode setup
delete_input_constraints i_apu_aon_rst_n
delete_input_constraints i_apu_x_rst_n
delete_input_constraints i_dcd_aon_rst_n
delete_input_constraints i_dcd_codec_rst_n
delete_input_constraints i_dcd_mcu_rst_n
delete_input_constraints i_noc_rst_n
delete_input_constraints i_pcie_aon_rst_n
delete_input_constraints i_pcie_init_mt_rst_n
delete_input_constraints i_pcie_targ_cfg_dbi_rst_n
delete_input_constraints i_pcie_targ_cfg_rst_n
delete_input_constraints i_pcie_targ_mt_rst_n
delete_input_constraints i_pve_0_aon_rst_n
delete_input_constraints i_pve_0_rst_n
delete_input_constraints i_pve_1_aon_rst_n
delete_input_constraints i_pve_1_rst_n
delete_input_constraints i_soc_mgmt_aon_rst_n
delete_input_constraints i_soc_mgmt_rst_n
delete_input_constraints i_sys_spm_aon_rst_n
delete_input_constraints i_sys_spm_rst_n

add_clock 1 i_apu_aon_rst_n
add_clock 1 i_apu_x_rst_n
add_clock 1 i_dcd_aon_rst_n
add_clock 1 i_dcd_codec_rst_n
add_clock 1 i_dcd_mcu_rst_n
add_clock 1 i_noc_rst_n
add_clock 1 i_pcie_aon_rst_n
add_clock 1 i_pcie_init_mt_rst_n
add_clock 1 i_pcie_targ_cfg_dbi_rst_n
add_clock 1 i_pcie_targ_cfg_rst_n
add_clock 1 i_pcie_targ_mt_rst_n
add_clock 1 i_pve_0_aon_rst_n
add_clock 1 i_pve_0_rst_n
add_clock 1 i_pve_1_aon_rst_n
add_clock 1 i_pve_1_rst_n
add_clock 1 i_soc_mgmt_aon_rst_n
add_clock 1 i_soc_mgmt_rst_n
add_clock 1 i_sys_spm_aon_rst_n
add_clock 1 i_sys_spm_rst_n

extract_icl

# ICLNetwork
source ../../init_mbist.tcl
set patSpec [create_patterns_specification]

###Add reset proc in MemoryBist_P1 and MemoryBist_ParallelRetentionTest_P1 patterns
###TODO Add retention configuration
set mbist_pat [get_config_element Patterns(MemoryBist_P*) -in $patSpec]
foreach_in_collection pat $mbist_pat {
  read_config_data -in $pat -first -from_string {
      ProcedureStep(chip_reset) {
          run_before_dft_control_settings  : on;
          iCall(pulse_resets_noc_soc){
              iProcArguments {
              }
          }
      }
  }
}

report_config_data $patSpec
process_patterns_specification

exit
