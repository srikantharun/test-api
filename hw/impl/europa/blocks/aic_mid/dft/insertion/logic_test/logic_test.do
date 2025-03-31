# Settings
set DESIGN            aic_mid_p
set DESIGN_ID         rtl2
set USE_MBIST_TSDB    1
set USE_PREPROCESSING 1
set BLACKBOXES        { \
                        imc_bank \
                        tu_tem0501ar01_ln05lpe_4007002 \
                        svs_monitor \
                        process1_monitor \
                        process2_monitor \
                        c2c_monitor \
                      }

# Test Point to be inserted
set RTL_TP 400
set RTL_TP_INS 1

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
}

if { $USE_MBIST_TSDB == 0 } {
    add_clock 0 i_clk -period 1ns -pulse_always
    add_input_constraints i_rst_n -c1
}
add_clock 0 i_c2c_clk -period 1ns
add_clock 0 i_ref_clk -period 1ns

# x bounding optional control signal
#add_dft_signals x_bounding_en

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

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN} -open_input_pins tie0

if { [info exists env(PD_HOME)] } {
  if { [file exists $env(PD_HOME)/floorplan/${DESIGN}.def ] } {
    read_def $env(PD_HOME)/floorplan/${DESIGN}.def
  }
}

set_drc_handling dft_c9 -auto_fix off

# black boxes outputs control points
add_dft_control_points  [get_pins o_* -direction output -of_instances [get_instance -hier *_monitor]] -dft_signal_source_name all_test

set_system_mode analysis

set dftSpec [create_dft_specification -sri_sib_list {edt} ]
report_config_data $dftSpec

# compressed chains increased to 960 from 840 to increase test coverage
read_config_data -in_wrapper $dftSpec -from_string {

  EDT {
    ijtag_host_interface : Sib(edt);
    Controller (c1_int) {
      longest_chain_range    : 260, 280;
      scan_chain_count       : 960;
      input_channel_count    : 12;
      output_channel_count   : 12;

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
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/scan_in     ijtag_si
# set_config_value /DftSpecification(${DESIGN},${DESIGN_ID})/IjtagNetwork/HostScanInterface(ijtag)/Interface/scan_out    ijtag_so

report_config_data $dftSpec
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

set_system_mode setup
delete_input_constraints i_rst_n
add_icl_ports i_rst_n -type reset_n

extract_icl

add_input_constraints i_aic_throttle_async -c0
add_input_constraints i_thermal_throttle_async -c0
add_input_constraints i_aic_boost_ack_async -c0
add_input_constraints i_mvm_exe_tok_prod_rdy -c0
add_input_constraints i_mvm_exe_tok_cons_vld -c0
add_input_constraints i_mvm_prg_tok_prod_rdy -c0
add_input_constraints i_mvm_prg_tok_cons_vld -c0
add_input_constraints i_m_iau_tok_prod_rdy -c0
add_input_constraints i_m_iau_tok_cons_vld -c0
add_input_constraints i_m_dpu_tok_prod_rdy -c0
add_input_constraints i_m_dpu_tok_cons_vld -c0
add_input_constraints i_cfg_s_awvalid -c0
add_input_constraints i_cfg_s_wvalid -c0
add_input_constraints i_cfg_s_arvalid -c0
add_input_constraints i_m_ifdw_axis_s_tvalid -c0
add_input_constraints i_m_ifd0_axis_s_tvalid -c0
add_input_constraints i_m_ifd1_axis_s_tvalid -c0
add_input_constraints i_m_ifd2_axis_s_tvalid -c0
add_input_constraints i_sram_ret -c0
add_input_constraints i_sram_adme[2] -c1
add_input_constraints i_sram_adme[1] -c0
add_input_constraints i_sram_adme[0] -c0

set patSpec [create_patterns_specification]

# Add custom patterns to pat spec
source ../../pdl/imc_bist.pdl

read_config_data -in_wrapper $patSpec -from_string {
  Patterns (test_imc_mbist) {
    ClockPeriods { i_clk: 1.0ns; }
    ProcedureStep (test_imc_mbist) { iCall(test_imc_mbist) { iProcArguments { } } }
  }
  Patterns (test_imc_cbist) {
    ClockPeriods { i_clk: 1.0ns; }
    ProcedureStep (test_imc_cbist) { iCall(test_imc_cbist) { iProcArguments { } } }
  }
  Patterns (test_imc_mbist_bira_mode) {
    ClockPeriods { i_clk: 1.0ns; }
    ProcedureStep (test_imc_mbist_bira_mode) { iCall(test_imc_mbist_bira_mode) { iProcArguments { } } }
  }
  Patterns (test_imc_cbist_bira_mode) {
    ClockPeriods { i_clk: 1.0ns; }
    ProcedureStep (test_imc_cbist_bira_mode) { iCall(test_imc_cbist_bira_mode) { iProcArguments { } } }
  }
  Patterns (test_imc_cbist_bira_bisr_rotate) {
    ClockPeriods { i_clk: 1.0ns; }
    ProcedureStep (test_imc_bira_bisr_prod_mode) { iCall(test_imc_bira_bisr_prod_mode) { iProcArguments { } } }
    ProcedureStep (clear_imc_bist_cmd) { iCall(clear_imc_bist_cmd) { iProcArguments { } } }
    TestStep(unload_imc_bist_bisr_chain) {
      MemoryBisr {
        run_mode : bisr_chain_access;
        Controller(.) {
          power_domain_group_labels : imc;
          BisrChainAccessOptions {
            enable_bira_capture : on ;
            default_write_value : all_zero ;
          }
        }
      }
    }
  }
}

# test_imc_cbist_bira_bisr_rotate:
# It would be functionally safer to enable rotation to loop the shifted-out repair settings back to the BISR:
#
# enable_rotation : on ;
#
# However, the generated TB implementation for the loopback is hacky and does not compile.
# Since it is not necessary for the current pattern, the option was not included.
#
# This just means we must recapture BIRA between successive unloads.

# test_imc_mbist_bira_mode_burn_fuses:
# For chip-level we would leverage the toplevel controller autonomous function:
#
#     TestStep(self_fuse_box_program) {
#       MemoryBisr {
#         run_mode: autonomous ;
#         Controller(.) {
#           power_domain_group_labels : imc;
#           AutonomousOptions {
#             operation : self_fuse_box_program ;
#           }
#         }
#       }
#     }
#

report_config_data $patSpec
process_patterns_specification

if { $RTL_TP_INS } {

    #needed to overwrite insertion dft_specpost_insertion 
    proc process_dft_specification.post_insertion {[get_current_design] args} {
      global DESIGN
      global DESIGN_ID
      puts "   === TP insertion stage === "
    }  

    set_quick_synthesis_options -skip_synthesis_of_two_dimensional_arrays_larger_than 15360

    set_context dft -test_points -rtl -design_id rtl2_tp 
    
    set_test_point_types {edt_pattern_count lbist_test_coverage}
    
    set_rtl_dft_analysis_options -preserve_x_propagation off 
    
    set_drc_handling dft_c9 -auto_fix off
    
    if { [llength $BLACKBOXES] > 0 } {
      add_black_boxes -modules $BLACKBOXES
    }

    set_test_point_insertion_options -test_point_clock tclk_as_needed 
    report_dft_signals
    
    set_system_mode analysis

    set_test_point_analysis_options  -observe_blocked_faults on \
                                     -test_coverage_target 98.9 \
				     -shared_control_points_per_flop 8 \
				     -shared_observe_points_per_flop 8 \
                                     -total $RTL_TP \
                                     -pattern_count_target 8000

    add_observe_points -location [get_nets [list mux_target mux_enable mux_use_ro*] -hier]
    
    # additional control points can be added here
    #add_control_point -location gc[1] -type OR
    #add_control_point -location gd[1] -type AND -clock gclk4

    report_rtl_complexity -summary > rpt/rtl_complexity_summary.rpt

    # optional list of blocks to be excluded from TP insertion  
    #add_notest_points u_aic_mid/u_dpu u_aic_mid/u_iau
    report_notest_points

    analyze_test_points 
    report_test_points                                     > rpt/tp_rtl2.rpt
    report_test_point_statistics                           > rpt/tp_rtl2_stats.rpt

    report_rtl_complexity -columns {instance file_path_name tp_total tp_visible tp_expression tp_observe tp_control tp_editable tp_non_editable} > rpt/rtl_complexity_test_points_location.rpt

    set_defaults_value DftSpecification/use_rtl_cells on
    set dftSpec [create_dft_specification -replace]
    set_defaults_value DftSpecification/persistent_cell_prefix AXE_TP_RTL_
    report_config_data $dftSpec
    
    write_design -tsdb
    
    process_dft_specification -transcript_insertion_commands
    
    write_filemap ./tsdb_outdir/modified_files_tp.lst
}

exit
