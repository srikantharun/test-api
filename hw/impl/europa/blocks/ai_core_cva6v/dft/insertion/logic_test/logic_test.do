# Settings
set TSDB_DIR          tsdb_outdir
set DESIGN            ai_core_cva6v
set DESIGN_ID         rtl2
set USE_MBIST_TSDB    0
set USE_PREPROCESSING 0
set BLACKBOXES        { axe_tcl_sram }
# set BLACKBOXES        { \
#                         cva6v_acc_dispatcher \
#                         cva6v_raptor_elem_dataflow \
#                         cva6v_raptor_vfpu \
#                       }

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./${TSDB_DIR}

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

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
}

add_dft_signals ltest_en -source test_mode -make_ijtag_port
add_dft_signals async_set_reset_static_disable
add_dft_signals control_test_point_en observe_test_point_en
add_dft_signals test_clock -source test_clk
add_dft_signals edt_update -source edt_update
add_dft_signals scan_en -source scan_en
add_dft_signals edt_clock -create_from_other_signals

if { $USE_MBIST_TSDB == 0 } {
    add_clock 0 i_clk -period 1ns -pulse_always
    add_input_constraints i_rst_n -c1
}

report_dft_signals

set_dft_specification_requirements -logic_test on

if { $USE_PREPROCESSING } {
  set_system_mode insertion
  delete_ports {scan_in scan_out}
  write_design -tsdb

  set_system_mode setup
  set DESIGN_ID rtl3
  set_context dft -rtl -design_id ${DESIGN_ID}
  set_insertion_options -edited_module_prefix ${DESIGN}
}

set_drc_handling dft_c9 -auto_fix off

set_system_mode analysis

set spec [create_dft_specification -sri_sib_list {edt} ]
report_config_data $spec

read_config_data -in_wrapper $spec -from_string {

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

# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/tck         ijtag_tck
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/reset       ijtag_resetn
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/select      ijtag_sel
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/update_en   ijtag_ue
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/shift_en    ijtag_se
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/capture_en  ijtag_ce
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/scan_in     ijtag_tdi
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/scan_out    ijtag_tdo

# set_config_value [get_config_elements *parent_instance -hierarchical -in $spec] u_dft_physblock_top

report_config_data $spec
process_dft_specification

# Print modified files list to shell and to listfile
set filemap [get_instrument_dictionary DftSpecification file_map_list]
while {[set t [join $filemap]] ne $filemap} {set filemap $t}
set fd [open "${TSDB_DIR}/modified_files.lst" w]
set i 0
foreach f $filemap {
  # Print source and modified files to shell
  puts $f
  # Print only modified files to listfile
  if { [expr $i % 2] == 1 } {
    puts $fd $f
  }
  incr i
}
close $fd

extract_icl

# ICLNetwork
create_patterns_specification
process_patterns_specification

exit
