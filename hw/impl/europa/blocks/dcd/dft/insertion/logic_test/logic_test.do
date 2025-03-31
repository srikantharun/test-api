# Settings
set DESIGN            dcd_p
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

open_tsdb $env(DFT_HOME)/dcd_core/Latest/tsdb/memory_test/tsdb_outdir
open_tsdb $env(DFT_HOME)/dcd_core/Latest/tsdb/logic_test/tsdb_outdir
read_design alg_core_wrapper -verbose -design_id rtl2 -no_hdl

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

# DFT Signal used for logic test
add_dft_signals ltest_en  -source test_mode -make_ijtag_port
# DFT Signal used to test memories with multi-load ATPG patterns
add_dft_signals memory_bypass_en 
# DFT Signal used for Scan Tested network to be tested during logic test
add_dft_signals tck_occ_en 
# DFT Signals used for hierarchical DFT 
add_dft_signals int_ltest_en ext_ltest_en int_mode ext_mode int_edt_mode ext_edt_mode

add_input_constraints test_mode -C1

add_primary_inputs u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[0].I_CORE/rstn -pseudo_port_name rstn0
add_primary_inputs u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[0].I_CORE/al_apb.rstn -pseudo_port_name al_apb_rstn0
add_primary_inputs u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[0].I_CORE/al_axi.rstn -pseudo_port_name al_axi_rstn0
add_primary_inputs u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[1].I_CORE/rstn -pseudo_port_name rstn1
add_primary_inputs u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[1].I_CORE/al_apb.rstn -pseudo_port_name al_apb_rstn1
add_primary_inputs u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[1].I_CORE/al_axi.rstn -pseudo_port_name al_axi_rstn1
add_input_constraints rstn0 -c1
add_input_constraints al_apb_rstn0 -c1
add_input_constraints al_axi_rstn0 -c1
add_input_constraints rstn1 -c1
add_input_constraints al_apb_rstn1 -c1
add_input_constraints al_axi_rstn1 -c1

report_dft_signals

set_dft_specification_requirements -logic_test on -add_test_clock_on_ssh on

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

## TODO remove once it's clarified. https://tickets.allegrodvt.com/issues/5759
set_quick_synthesis_options -skip_synthesis_of_two_dimensional_arrays_larger_than 8000

set_system_mode analysis

set wrapper_excluded_ports [list \
  i_global_rst_n \
  i_ao_rst_n \
  i_ref_clk \
  i_clk \
  i_mcu_clk \
  bisr_clk \
  bisr_reset \
  bisr_shift_en \
  bisr_si \
  bisr_so \
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
  i_jtag_clk \
  i_jtag_rst_n \
]

set_dedicated_wrapper_cell_options on -ports [get_ports * ]
set_wrapper_analysis_options -exclude_ports ${wrapper_excluded_ports}

analyze_wrapper_cells
report_wrapper_cells

set dftSpec [create_dft_specification -sri_sib_list {edt occ ssn} ]
report_config_data $dftSpec

read_config_data -in_wrapper $dftSpec -from_string {
  OCC {
    ijtag_host_interface : Sib(occ);
    include_clocks_in_icl_model : on;
    capture_window_size : 5;
    Controller(i_mcu_clk) {
      clock_intercept_node      : u_pctl/o_partition_clk[0];
    }

    Controller(i_clk) {
      clock_intercept_node      : u_pctl/o_partition_clk[1];
    }

    Controller(i_ref_clk) {
      clock_intercept_node      : i_ref_clk;
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
        ChainGroup (gi_dcd_core_0) {
	        input_chain_count : 12;
	        output_chain_count : 12;
	      }
        ChainGroup (gi_dcd_core_1) {
	        input_chain_count : 12;
	        output_chain_count : 12;
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
          ChainGroup (gi_dcd_core_0) {
            to_scan_in : "u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[0].I_CORE /scan_in";
            from_scan_out : "u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[0].I_CORE /scan_out";
          }
          ChainGroup (gi_dcd_core_1) {
            to_scan_in : "u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[1].I_CORE /scan_in";
            from_scan_out : "u_dcd/u_codec/u_alg_vcu_dec_top/\g_itu_core_num[1].I_CORE /scan_out";
          }
        }
      }
      Receiver1xPipeline (pi) {}
    }
  }


  EDT {
    ijtag_host_interface : Sib(edt);
    Controller (c1_int) {
      longest_chain_range    : 280, 300;
      scan_chain_count       : 450;
      input_channel_count    : 12;
      output_channel_count   : 12;
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
      longest_chain_range    : 180, 200;
      scan_chain_count       : 11;
      input_channel_count    : 5;
      output_channel_count   : 5;
      Connections {
        ssh_chain_group : gx;
      }
    }
  }
}

proc process_dft_specification.post_insertion {[get_current_design] args} {
  global DESIGN
  global DESIGN_ID
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

  # Connect occ scan chain 
  connect_occ_scan_chain

  set wrapper_cells [get_fanouts i_mcu_clk -stop_on pin]
  foreach_in_collection cell $wrapper_cells {
    set leaf [get_attribute_value_list $cell -name name]
    if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
      echo $leaf
      delete_connection $leaf
      create_connection dcd_p_rtl2_tessent_occ_i_mcu_clk_inst/clock_out $leaf
    }
  }

  set wrapper_cells [get_fanouts i_clk -stop_on pin]
  foreach_in_collection cell $wrapper_cells {
    set leaf [get_attribute_value_list $cell -name name]
    if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
      echo $leaf  
      delete_connection $leaf
      create_connection dcd_p_rtl2_tessent_occ_i_mcu_clk_inst/clock_out $leaf    }
  }
  delete_connection u_dcd/i_scan_en
  create_connection dcd_p_rtl2_tessent_ssn_scan_host_sh_inst/scan_en u_dcd/i_scan_en
}

report_config_data $dftSpec
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

# masking drc errors
set_drc_handling I5 warn

set_system_mode setup
delete_input_constraints i_ao_rst_n
delete_input_constraints i_global_rst_n
add_clock 1 i_ao_rst_n 
add_clock 1 i_global_rst_n

extract_icl

# ICLNetwork
source ../../init_mbist.tcl


# Block and all subblock patterns
set_defaults_value PatternsSpecification/SignOffOptions/simulate_instruments_in_lower_physical_instances on
set patSpec [create_patterns_specification]

set ClockPeriods_wrappers [get_config_elements ClockPeriods -in $patSpec -hier]
foreach_in_collection ClockPeriods_wrapper $ClockPeriods_wrappers {
  add_config_element i_ref_clk -in $ClockPeriods_wrapper -value "10ns"
}

###Add reset proc in MemoryBist_P1 and MemoryBist_ParallelRetentionTest_P1 patterns
###TODO Add retention configuration
set mbist_pat [get_config_element Patterns(MemoryBist_P*) -in $patSpec]
foreach_in_collection pat $mbist_pat {
  read_config_data -in $pat -first -from_string {
      ProcedureStep(chip_reset) {
          run_before_dft_control_settings  : on;
          iCall(pulse_resets){
              iProcArguments {
              }
          }
      }
  }
}

report_config_data $patSpec
process_patterns_specification

exit
