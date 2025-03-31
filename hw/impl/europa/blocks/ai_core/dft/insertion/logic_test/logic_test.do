# Settings
set DESIGN            ai_core_p
set DESIGN_ID         rtl2
set USE_MBIST_TSDB    1
set USE_PREPROCESSING 0
set BLACKBOXES        { }

# Test Point to be inserted
set RTL_TP 400
set RTL_TP_INS 0

set DFT_RELEASE_aic_did    "$env(DFT_HOME)/aic_did/Latest" ;# 202501270741

set DFT_RELEASE_aic_infra  "$env(DFT_HOME)/aic_infra/Latest" ;# 202501270747

set DFT_RELEASE_aic_ls     "$env(DFT_HOME)/aic_ls/Latest" ;# 202501270744

set DFT_RELEASE_aic_mid    "$env(DFT_HOME)/aic_mid/Latest" ;# 202501291601

set cmd "ls -la /data/releases/europa/dft/bronze/aic_*/Latest"
eval $cmd

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

open_tsdb $DFT_RELEASE_aic_infra/tsdb/memory_test/tsdb_outdir
open_tsdb $DFT_RELEASE_aic_mid/tsdb/memory_test/tsdb_outdir
open_tsdb $DFT_RELEASE_aic_did/tsdb/memory_test/tsdb_outdir
open_tsdb $DFT_RELEASE_aic_ls/tsdb/memory_test/tsdb_outdir

open_tsdb $DFT_RELEASE_aic_infra/tsdb/logic_test/tsdb_outdir
open_tsdb $DFT_RELEASE_aic_mid/tsdb/logic_test/tsdb_outdir
open_tsdb $DFT_RELEASE_aic_did/tsdb/logic_test/tsdb_outdir
open_tsdb $DFT_RELEASE_aic_ls/tsdb/logic_test/tsdb_outdir

read_design aic_infra_p -verbose -design_id rtl2  -no_hdl
read_design aic_mid_p -verbose -design_id rtl2 -no_hdl
read_design aic_did_p -verbose -design_id rtl2 -no_hdl
read_design aic_ls_p -verbose -design_id rtl2 -no_hdl

# Mem lib
read_mem_libs

set_read_verilog_options -allow_enum_relaxation on
dofile ${DEPENDENCIES_DIR}/read_rtl.do

set_current_design ${DESIGN}
set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
} else {
  add_black_boxes -auto
}

add_clock 0 i_clk     -period 1ns -pulse_always
add_clock 0 i_ref_clk -period 10ns -pulse_always

# DFT Signal used for logic test
add_dft_signals ltest_en -source test_mode -make_ijtag_port
# DFT Signal used for Scan Tested network to be tested during logic test
add_dft_signals tck_occ_en
# DFT Signals used for hierarchical DFT
add_dft_signals int_ltest_en ext_ltest_en int_mode ext_mode int_edt_mode ext_edt_mode

report_dft_signals

add_input_constraints i_ao_rst_n       -c1
add_input_constraints i_global_rst_n   -c1
add_input_constraints test_mode        -c1

# x bounding optional control signal
#add_dft_signals x_bounding_en

set_dft_specification_requirements -logic_test on -memory_test on -add_test_clock_on_ssh on -host_scan_interface_type tap

if { $USE_PREPROCESSING } {
  set_context dft -rtl -design_id ${DESIGN_ID}a
  set_system_mode insertion
  delete_ports {scan_in scan_out}
  write_design -tsdb

  set_system_mode setup
  set_context dft -rtl -design_id ${DESIGN_ID}
}

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [file exists ${DESIGN}.def ] } {
  read_def ${DESIGN}.def
}

set_drc_handling dft_c9 -auto_fix off

add_dft_control_points  [get_pin u_pctl/i_test_mode] -dft_signal_source_name all_test

set_system_mode analysis

report_dft_control_points

#analyze_xbounding
#report_xbounding -verbose			       > rpt/xb_rtl2.rpt

set wrapper_excluded_ports [list \
  i_global_rst_n \
  i_ao_rst_n \
  i_clk \
  i_ref_clk \
  bisr_clk \
  bisr_reset \
  bisr_shift_en \
  bisr_si \
  bisr_so \
  imc_bisr_clk \
  imc_bisr_reset \
  imc_bisr_shift_en \
  imc_bisr_si \
  imc_bisr_so \
  tck \
  trst \
  tms \
  tdi \
  tdo_en \
  tdo \
  test_mode \
  ssn_bus_clk \
  ssn_bus_data_in \
  ssn_bus_data_out \
  io_ibias_ts \
  io_vsense_ts \
]

set_dedicated_wrapper_cell_options on -ports [get_ports * ]
set_wrapper_analysis_options -exclude_ports ${wrapper_excluded_ports}

analyze_wrapper_cells
report_wrapper_cells

set dftSpec [create_dft_specification -sri_sib_list {edt occ ssn} ]
report_config_data $dftSpec

read_config_data -in_wrapper $dftSpec -from_string {
  Occ {
    ijtag_host_interface : Sib(occ);
    include_clocks_in_icl_model : on;
    capture_window_size : 5;
    Controller(i_clk) {
      clock_intercept_node : u_pctl/o_partition_clk[0];
    }
    Controller(i_ref_clk) {
      clock_intercept_node : i_ref_clk;
    }
  }
  SSN {
    ijtag_host_interface : Sib(ssn);
    Datapath (d1) {
      output_bus_width : 24;
      Connections {
        bus_clock_in : ssn_bus_clk;
        bus_data_in  : ssn_bus_data_in[23:0];
        bus_data_out : ssn_bus_data_out[23:0];
      }
      //OutputPipeline (po) {}
      ScanHost (sh) {
        use_clock_shaper_cell : off;
        OnChipCompareMode {
          present: on;
        }
        ChainGroup (gi_mid) {
          input_chain_count : 12;
          output_chain_count : 12;
          output_chain_count_in_on_chip_compare_mode: 12;
        }
        ChainGroup (gi_did) {
          input_chain_count : 12;
          output_chain_count : 12;
          output_chain_count_in_on_chip_compare_mode: 12;
        }
        ChainGroup (gi_infra) {
          input_chain_count : 12;
          output_chain_count : 12;
          output_chain_count_in_on_chip_compare_mode: 12;
        }
        ChainGroup (gi_ls) {
          input_chain_count : 12;
          output_chain_count : 12;
          output_chain_count_in_on_chip_compare_mode: 12;
        }
        ChainGroup (gx) {
        }
        ChainGroup (gi) {
        }
        Interface {
          ChainGroup {
            test_clock_present : on;
          }
        }
        Connections {
          ChainGroup (gi_mid) {
            to_scan_in : u_ai_core/u_aic_mid_p/scan_in;
            from_scan_out : u_ai_core/u_aic_mid_p/scan_out;
          }
          ChainGroup (gi_did) {
            to_scan_in : u_ai_core/u_aic_did_p/scan_in;
            from_scan_out : u_ai_core/u_aic_did_p/scan_out;
          }
          ChainGroup (gi_infra) {
            to_scan_in : u_ai_core/u_aic_infra_p/scan_in;
            from_scan_out : u_ai_core/u_aic_infra_p/scan_out;
          }
          ChainGroup (gi_ls) {
            to_scan_in : u_ai_core/u_aic_ls_p/scan_in;
            from_scan_out : u_ai_core/u_aic_ls_p/scan_out;
          }
        }
      }
      Receiver1xPipeline (pi) {
      }
    }
  }
  EDT {
    ijtag_host_interface : Sib(edt);
    Controller (c1_int) {
      longest_chain_range  : 280, 300;
      scan_chain_count     : 46; 
      input_channel_count  : 12;
      output_channel_count : 12;
      ShiftPowerOptions {
        present                            : on  ;
        full_control                       : on ;
        min_switching_threshold_percentage : 25 ;
      }
      Connections {
        ssh_chain_group : gi;
      }
    }
    Controller (cx) {
      longest_chain_range  : 180, 200;
      scan_chain_count     : 10;
      input_channel_count  : 5;
      output_channel_count : 5;
      Connections {
        ssh_chain_group : gx;
      }
    }
  }
}

proc process_dft_specification.post_insertion {[get_current_design] args} {
  global DESIGN
  global DESIGN_ID

  # Extest chain connectivity
  set cx_scan_in_list [list ]
  set pattern {edt_scan_in\[(\d+)\]}
  foreach_in_collection item [get_pins ${DESIGN}_${DESIGN_ID}_tessent_edt_cx_inst/edt_scan_in] {
    set leaf [get_attribute_value_list $item -name name]
    set pin_leaf [get_attribute_value_list $item -name leaf_name]
    set pin [string trim $pin_leaf "{}"]
    lappend cx_scan_in_list "$pin"
    regexp $pattern $leaf match index
    # preserve bit0 for occ scan chain
    if {[regexp {edt_scan_in\[0\]} $pin]} {
      create_instance tessent_scan_mux_i_${index} -of_module axe_tcl_std_mux2
      create_connection ${leaf} tessent_scan_mux_i_${index}/i_b
      create_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin} tessent_scan_mux_i_${index}/i_a
      create_instance tessent_occ_scan_buf_i_${index} -of_module axe_tcl_std_buffer
      create_connection tessent_scan_mux_i_${index}/o_z tessent_occ_scan_buf_i_${index}/i_a
      create_connection ${DESIGN}_rtl2_tessent_tdr_sri_ctrl_inst/ext_mode tessent_scan_mux_i_${index}/i_sel
   } else {
      create_instance tessent_scan_mux_i_${index} -of_module axe_tcl_std_mux2
      create_connection ${leaf} tessent_scan_mux_i_${index}/i_b
      create_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin} tessent_scan_mux_i_${index}/i_a
      create_instance tessent_cx_scan_buf_i_${index} -of_module axe_tcl_std_buffer
      create_connection tessent_scan_mux_i_${index}/o_z tessent_cx_scan_buf_i_${index}/i_a
      create_connection ${DESIGN}_rtl2_tessent_tdr_sri_ctrl_inst/ext_mode tessent_scan_mux_i_${index}/i_sel

   }
  }

  # Intest chain connectivity
  set pattern {edt_scan_out\[(\d+)\]}
  set cx_scan_out_list {}
  foreach_in_collection item [get_pins ${DESIGN}_${DESIGN_ID}_tessent_edt_cx_inst/edt_scan_out] {
    set leaf [get_attribute_value_list $item -name name]
    set pin_leaf [get_attribute_value_list $item -name leaf_name]
    set pin [string trim $pin_leaf "{}"]
    puts "${pin}"
    lappend cx_scan_out_list "$pin"
    regexp $pattern $leaf match index
    # preserve bit0 for occ scan chain
    if {[regexp {edt_scan_out\[0\]} $pin]} {
      create_instance tessent_cx_and_gate_i_${index} -of_module axe_tcl_std_and2
      delete_connection ${leaf}
      create_connection tessent_cx_and_gate_i_${index}/o_z ${leaf}
      create_connection ${DESIGN}_rtl2_tessent_tdr_sri_ctrl_inst/ext_mode tessent_cx_and_gate_i_${index}/i_a
      create_instance tessent_intest_and_gate_i_${index} -of_module axe_tcl_std_and2
      delete_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
      create_connection tessent_intest_and_gate_i_${index}/o_z ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
      create_connection ${DESIGN}_rtl2_tessent_tdr_sri_ctrl_inst/int_mode tessent_intest_and_gate_i_${index}/i_a
      create_instance tessent_occ_scan_buf_o_${index} -of_module axe_tcl_std_buffer
      create_connection tessent_occ_scan_buf_o_${index}/o_z tessent_intest_and_gate_i_${index}/i_b
      create_connection tessent_occ_scan_buf_o_${index}/o_z tessent_cx_and_gate_i_${index}/i_b
    } else {
      create_instance tessent_cx_and_gate_i_${index} -of_module axe_tcl_std_and2
      delete_connection ${leaf}
      create_connection tessent_cx_and_gate_i_${index}/o_z ${leaf}
      create_connection ${DESIGN}_rtl2_tessent_tdr_sri_ctrl_inst/ext_mode tessent_cx_and_gate_i_${index}/i_a
      create_instance tessent_intest_and_gate_i_${index} -of_module axe_tcl_std_and2
      delete_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
      create_connection tessent_intest_and_gate_i_${index}/o_z ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
      create_connection ${DESIGN}_rtl2_tessent_tdr_sri_ctrl_inst/int_mode tessent_intest_and_gate_i_${index}/i_a
      create_instance tessent_cx_scan_buf_o_${index} -of_module axe_tcl_std_buffer
      create_connection tessent_cx_scan_buf_o_${index}/o_z tessent_intest_and_gate_i_${index}/i_b
      create_connection tessent_cx_scan_buf_o_${index}/o_z tessent_cx_and_gate_i_${index}/i_b
    }
  }

  set edt_scan_in_pins {}
  set pattern {edt_scan_in\[(\d+)\]}
  foreach_in_collection item [get_pins ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/edt_scan_in] {
    set leaf [get_attribute_value_list $item -name name]
    lappend edt_scan_in_pins $leaf
  }

  set edt_scan_out_pins {}
  set pattern {edt_scan_in\[(\d+)\]}
  foreach_in_collection item [get_pins ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/edt_scan_out] {
    set leaf [get_attribute_value_list $item -name name]
    lappend edt_scan_out_pins $leaf
  }

  # scan_in hookups
  set pattern {edt_scan_in\[(\d+)\]}
  foreach  pin  $edt_scan_in_pins {
    set full_pin_name [string trim $pin "{}"]
    regexp {[^/]+$} $full_pin_name pin_name

    if {[lsearch -exact $cx_scan_in_list $pin_name] == -1} {
      regexp $pattern $pin match index
      create_instance tessent_scan_buf_i_${index} -of_module axe_tcl_std_buffer
      create_connection ${pin} tessent_scan_buf_i_${index}/i_a
    }
  }

  # scan_out hookups
  set pattern {edt_scan_out\[(\d+)\]}
  foreach  pin  $edt_scan_out_pins {
    set full_pin_name [string trim $pin "{}"]
    regexp {[^/]+$} $full_pin_name pin_name
    if {[lsearch -exact $cx_scan_out_list $pin_name] == -1} {
      regexp $pattern $pin match index
      delete_connection ${pin}
      create_instance tessent_scan_buf_o_${index} -of_module axe_tcl_std_buffer
      create_connection tessent_scan_buf_o_${index}/o_z ${pin}
    }
  }

  # connect OCC scan chains
  connect_occ_scan_chain

  # move wrapper cells to OCC clock
  set wrapper_cells [get_fanouts i_clk -stop_on pin]
  foreach_in_collection cell $wrapper_cells {
    set leaf [get_attribute_value_list $cell -name name]
    if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
      echo $leaf
      delete_connection $leaf
      create_connection ${DESIGN}_${DESIGN_ID}_tessent_occ_i_clk_inst/clock_out $leaf
    }
  }

  # AIC specific
  delete_connection u_ai_core/scan_en
  create_connection ai_core_p_rtl2_tessent_ssn_scan_host_sh_inst/scan_en u_ai_core/scan_en
}

report_config_data $dftSpec
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

set_system_mode setup
delete_input_constraints i_global_rst_n
add_icl_ports i_global_rst_n -type reset_n
delete_input_constraints i_ao_rst_n
add_icl_ports i_ao_rst_n -type reset_n

set_drc_handling i5 warn

extract_icl

add_input_constraints i_thermal_throttle_async -c0
add_input_constraints i_clock_throttle_async -c0
add_input_constraints i_aic_throttle_async -c0
add_input_constraints i_thermal_warning_async -c0
add_input_constraints i_aic_boost_ack_async -c0
add_input_constraints i_tok_prod_ocpl_m_scmdaccept -c0
add_input_constraints i_tok_cons_ocpl_s_mcmd -c0
add_input_constraints i_msip_async -c0
add_input_constraints i_mtip_async -c0
add_input_constraints i_debug_int_async -c0
add_input_constraints i_resethaltreq_async -c0
add_input_constraints i_noc_ht_axi_m_awready -c0
add_input_constraints i_noc_ht_axi_m_wready -c0
add_input_constraints i_noc_ht_axi_m_bvalid -c0
add_input_constraints i_noc_ht_axi_m_arready -c0
add_input_constraints i_noc_ht_axi_m_rvalid -c0
add_input_constraints i_noc_lt_axi_m_awready -c0
add_input_constraints i_noc_lt_axi_m_wready -c0
add_input_constraints i_noc_lt_axi_m_bvalid -c0
add_input_constraints i_noc_lt_axi_m_arready -c0
add_input_constraints i_noc_lt_axi_m_rvalid -c0
add_input_constraints i_noc_lt_axi_s_awvalid -c0
add_input_constraints i_noc_lt_axi_s_wvalid -c0
add_input_constraints i_noc_lt_axi_s_bready -c0
add_input_constraints i_noc_lt_axi_s_arvalid -c0
add_input_constraints i_noc_lt_axi_s_rready -c0
add_input_constraints i_cfg_apb4_s_psel -c0
add_input_constraints i_cfg_apb4_s_penable -c0
add_input_constraints i_noc_async_idle_ack -c0
add_input_constraints i_noc_async_idle_val -c0

# Block and all subblock patterns
set_defaults_value PatternsSpecification/SignOffOptions/simulate_instruments_in_lower_physical_instances on
set patSpec [create_patterns_specification]

set ClockPeriods_wrappers [get_config_elements ClockPeriods -in $patSpec -hier]
foreach_in_collection ClockPeriods_wrapper $ClockPeriods_wrappers {
  add_config_element i_ref_clk -in $ClockPeriods_wrapper -value "10ns"
}

report_config_data $patSpec
process_patterns_specification

if { $RTL_TP_INS } {

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

    report_attributes { u_ai_core/u_aic_mid_p/u_aic_mid/u_mvm/i_mvm_dp/inst_mvm_imc_acc \
                        u_ai_core/u_aic_mid_p/u_aic_mid/u_mvm/i_mvm_dp/inst_mvm_imc_acc/\g_imc_acc_pairs[1].inst_mvm_imc_acc_pair }
    report_attributes { mvm_imc_acc@PV1 mvm_imc_acc_pair@PV1}

    set_system_mode analysis

    set_test_point_analysis_options  -observe_blocked_faults on \
                                     -test_coverage_target 98.9 \
                                     -total 750 \
                                     -pattern_count_target 18000

    report_rtl_complexity -summary > rpt/rtl_complexity_summary.rpt

    add_notest_points u_ai_core/u_aic_mid_p u_ai_core/u_aic_did_p u_ai_core/u_aic_infra_p u_ai_core/u_aic_ls_p
    report_notest_points

    analyze_test_points 
    report_test_points                                     > rpt/tp_rtl2.rpt
    report_test_point_statistics                           > rpt/tp_rtl2_stats.rpt
    
    write_test_point_dofile insertTP.do -all  -replace
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
