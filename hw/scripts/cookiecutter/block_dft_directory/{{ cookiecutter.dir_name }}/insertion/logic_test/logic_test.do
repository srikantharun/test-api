# Settings
set DESIGN            {{ cookiecutter.design_name }}_p
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

add_input_constraints test_mode -C1

if { $USE_MBIST_TSDB == 0 } {
    add_clock 0 i_clk -period 1ns -pulse_always
    add_input_constraints i_rst_n -c1
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

set_system_mode analysis

set dftSpec [create_dft_specification -sri_sib_list {edt} ]
report_config_data $dftSpec

read_config_data -in_wrapper $dftSpec -from_string {

  EDT {
    ijtag_host_interface : Sib(edt);
    Controller (c1_int) {
      longest_chain_range    : 280, 300;
      scan_chain_count       : 330;
      input_channel_count    : 8;
      output_channel_count   : 8;

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

        EdtChannelsOut(1) { port_pin_name : scan_out[0];}
        EdtChannelsOut(2) { port_pin_name : scan_out[1];}
        EdtChannelsOut(3) { port_pin_name : scan_out[2];}
        EdtChannelsOut(4) { port_pin_name : scan_out[3];}
        EdtChannelsOut(5) { port_pin_name : scan_out[4];}
        EdtChannelsOut(6) { port_pin_name : scan_out[5];}
        EdtChannelsOut(7) { port_pin_name : scan_out[6];}
        EdtChannelsOut(8) { port_pin_name : scan_out[7];}
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

# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/tck         ijtag_tck
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/reset       ijtag_resetn
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/select      ijtag_sel
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/update_en   ijtag_ue
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/shift_en    ijtag_se
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/capture_en  ijtag_ce
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/scan_in     ijtag_tdi
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/scan_out    ijtag_tdo

report_config_data $dftSpec
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

extract_icl

# ICLNetwork
set patSpec [create_patterns_specification]
report_config_data $patSpec
process_patterns_specification

exit
