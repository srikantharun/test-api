# Settings
set DESIGN            apu_p
set DESIGN_ID         rtl2
set USE_MBIST_TSDB    1
set USE_PREPROCESSING 0
set DFT_HOME [getenv DFT_HOME]
set READ_LOCAL_TSDB 0 

set BLACKBOXES        { tu_tem0501ar01_ln05lpe_4007002 }
lappend BLACKBOXES    {process1_monitor}
lappend BLACKBOXES    {process2_monitor}
lappend BLACKBOXES    {svs_monitor}

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
read_mem_libs

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

if { $USE_MBIST_TSDB } {
    open_tsdb ../memory_test/tsdb_outdir
    read_design ${DESIGN} -design_id rtl1
} else {
    dofile ${DEPENDENCIES_DIR}/read_rtl.do
}

read_design apu_core_p -design_identifier rtl2 -no_hdl
read_design apu_l2c_p -design_identifier rtl2 -no_hdl

set_current_design ${DESIGN}

set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
} else {
  add_black_boxes -auto
}

# DFT Signal used for logic test
#add_dft_signals ltest_en  -source test_mode -make_ijtag_port
# DFT Signal used to test memories with multi-load ATPG patterns
add_dft_signals memory_bypass_en 
# DFT Signal used for Scan Tested network to be tested during logic test
add_dft_signals tck_occ_en 
# DFT Signals used for hierarchical DFT 
add_dft_signals int_ltest_en ext_ltest_en int_mode ext_mode int_edt_mode ext_edt_mode
add_dft_signals shift_capture_clock -create_from_other_signals


if { $USE_MBIST_TSDB == 0 } {
    add_clock 0 i_clk -period 1ns -pulse_always
    add_input_constraints i_rst_n -c1
}

add_input_constraints test_mode -c1
#add_clock 0 bisr_clk -period 20ns -pulse_always

if { $USE_PREPROCESSING } {
  set_context dft -rtl -design_id rtl_fix
  set_system_mode insertion
  #delete_ports {scan_in scan_out}
  #create_port i_por_rst_n
  #create_port i_mtime_clk
  #create_connections i_mtime_clk u_apu/u_axe_ax65_cluster/i_mtime_clk
  #create_connections i_por_rst_n u_apu/u_axe_ax65_cluster/i_por_rst_n
  
  delete_connection u_apu_ao_csr/clk_i
  create_connection i_ref_clk u_apu_ao_csr/clk_i
  
  write_design -tsdb

  set_system_mode setup
  set_context dft -rtl -design_id ${DESIGN_ID}
}

report_dft_signals

set_dft_specification_requirements -logic_test on -add_test_clock_on_ssh on

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [file exists ${DESIGN}.def ] } {
  read_def ${DESIGN}.def
}


set_drc_handling dft_c9 -auto_fix off

add_nonscan_instances -modules axe_ccl_clk_div_by_*

#add_dft_control_point -type async_set_reset  u_apu/u_axe_ax65_cluster/u_bridge_wrapper/u_ax65_brg_top/u_brg0/u_mmio_rst_sync/q
#add_dft_control_point -type async_set_reset  u_apu/u_axe_ax65_cluster/u_bridge_wrapper/u_ax65_brg_top/u_brg1/u_mmio_rst_sync/q
#add_dft_control_point -type async_set_reset  u_apu/u_axe_ax65_cluster/u_bridge_wrapper/u_ax65_brg_top/u_brg2/u_mmio_rst_sync/q
#add_dft_control_point -type async_set_reset  u_apu/u_axe_ax65_cluster/u_bridge_wrapper/u_ax65_brg_top/u_brg3/u_mmio_rst_sync/q
#add_dft_control_point -type async_set_reset  u_apu/u_axe_ax65_cluster/u_bridge_wrapper/u_ax65_brg_top/u_brg4/u_mmio_rst_sync/q
#add_dft_control_point -type async_set_reset  u_apu/u_axe_ax65_cluster/u_bridge_wrapper/u_ax65_brg_top/u_brg5/u_mmio_rst_sync/q
#add_dft_control_point -type async_set_reset  u_apu/u_axe_ax65_cluster/u_peripheral_wrapper/u_ax65_peripheral_top/u_plmt/nds_sync_por_rst_mtime/resetn_out

set_system_mode analysis

set wrapper_excluded_ports [list \
  i_ref_clk \
  i_global_rst_n \
  i_ao_rst_n \
  i_clk \
  bisr_clk \
  bisr_reset \
  bisr_shift_en \
  bisr_si \
  bisr_so \
  *test_mode \
  io_vsense_ts \
  io_ibias_ts \
  ssn_bus_clk \
  ssn_bus_data_in \
  ssn_bus_data_out \
]

#
set_dedicated_wrapper_cell_options on -ports [get_ports * ]
set_wrapper_analysis_options -exclude_ports ${wrapper_excluded_ports}

analyze_wrapper_cells
report_wrapper_cells

set dftSpec [create_dft_specification -sri_sib_list {edt occ ssn} -replace ]

#upstream_parent_occ         : allow; 
read_config_data -in_wrapper $dftSpec -from_string {
  OCC {
    ijtag_host_interface        : Sib(occ);
    include_clocks_in_icl_model : on;
    capture_window_size         : 5;
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
        
	ChainGroup (gi_core_0) {
	  input_chain_count : 12;
	  output_chain_count : 12;
	}
        ChainGroup (gi_core_1) {
	  input_chain_count : 12;
	  output_chain_count : 12;
	}
        ChainGroup (gi_core_2) {
	  input_chain_count : 12;
	  output_chain_count : 12;
	}
        ChainGroup (gi_core_3) {
	  input_chain_count : 12;
	  output_chain_count : 12;
	}
        ChainGroup (gi_core_4) {
	  input_chain_count : 12;
	  output_chain_count : 12;
	}
        ChainGroup (gi_core_5) {
	  input_chain_count : 12;
	  output_chain_count : 12;
	}
        ChainGroup (gi_l2c) {
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
         
	  ChainGroup (gi_core_0) {
	    to_scan_in : u_apu/u_axe_ax65_cluster/g_cores[0].u_core_p/scan_in;
	    from_scan_out : u_apu/u_axe_ax65_cluster/g_cores[0].u_core_p/scan_out;
	  }
	  ChainGroup (gi_core_1) {
	    to_scan_in : u_apu/u_axe_ax65_cluster/g_cores[1].u_core_p/scan_in;
	    from_scan_out : u_apu/u_axe_ax65_cluster/g_cores[1].u_core_p/scan_out;
	  }
	  ChainGroup (gi_core_2) {
	    to_scan_in :u_apu/u_axe_ax65_cluster/g_cores[2].u_core_p/scan_in;
	    from_scan_out :u_apu/u_axe_ax65_cluster/g_cores[2].u_core_p/scan_out;
	  }
	  ChainGroup (gi_core_3) {
	    to_scan_in :u_apu/u_axe_ax65_cluster/g_cores[3].u_core_p/scan_in;
	    from_scan_out :u_apu/u_axe_ax65_cluster/g_cores[3].u_core_p/scan_out;
	  }
	  ChainGroup (gi_core_4) {
	    to_scan_in :u_apu/u_axe_ax65_cluster/g_cores[4].u_core_p/scan_in;
	    from_scan_out :u_apu/u_axe_ax65_cluster/g_cores[4].u_core_p/scan_out;
	  }
	  ChainGroup (gi_core_5) {
	    to_scan_in :u_apu/u_axe_ax65_cluster/g_cores[5].u_core_p/scan_in;
	    from_scan_out :u_apu/u_axe_ax65_cluster/g_cores[5].u_core_p/scan_out;
	  }
	  ChainGroup (gi_l2c) {
	    to_scan_in : u_apu/u_axe_ax65_cluster/u_l2c_p/scan_in;
	    from_scan_out : u_apu/u_axe_ax65_cluster/u_l2c_p/scan_out;
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
      scan_chain_count       : 460;
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

# define OCC structures
##########clk_id#########clk_src########
set occ_clk_list [list \
  apu_top_aclk      u_aclk_occ_hookup_buf/o_clk \
  apu_l2c_banks_clk u_apu/u_axe_ax65_cluster/u_apu_pmu/u_l2c_banks_clk_occ_buf/o_clk \
  apu_l2c_clk       u_apu/u_axe_ax65_cluster/u_apu_pmu/u_l2c_clk_occ_buf/o_clk \
  apu_cores0_clk    u_pctl/o_partition_clk[2] \
  apu_cores1_clk    u_pctl/o_partition_clk[3] \
  apu_cores2_clk    u_pctl/o_partition_clk[4] \
  apu_cores3_clk    u_pctl/o_partition_clk[5] \
  apu_cores4_clk    u_pctl/o_partition_clk[6] \
  apu_cores5_clk    u_pctl/o_partition_clk[7] \
  apu_top_ref_clk   u_ref_clk_occ_buf/o_clk \
  apu_mtime_clk     g_mtime_clk_div2[1].u_mtime_clk_div2/o_clk \
]

foreach {id clk} $occ_clk_list {
  set occ [add_config_element OCC/Controller($id) -in $dftSpec]
  set_config_value clock_intercept_node -in $occ $clk
}

##### Hookup process monitors to TDRs ###############

set Sib monitors

add_config_element       Sib($Sib) -in_wrapper [get_config_elements -hier HostScanInterface -in_wrappers $dftSpec]

add_tdr_process_monitors $Sib      p1_monitor  u_p1_monitor/u_process1_monitor_jtag_tdr_core
add_tdr_process_monitors $Sib      p2_monitor  u_p2_monitor/u_process2_monitor_jtag_tdr_core
add_tdr_process_monitors $Sib      svs_monitor u_svs_monitor/u_svs_monitor_jtag_tdr_core

###############

report_config_data $dftSpec

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
           create_connection apu_p_rtl2_tessent_tdr_sri_ctrl_inst/ext_mode tessent_scan_mux_i_${index}/i_sel
	 } else {
           create_instance tessent_scan_mux_i_${index} -of_module axe_tcl_std_mux2
           create_connection ${leaf} tessent_scan_mux_i_${index}/i_b
           create_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin} tessent_scan_mux_i_${index}/i_a
           create_instance tessent_cx_scan_buf_i_${index} -of_module axe_tcl_std_buffer
           create_connection tessent_scan_mux_i_${index}/o_z tessent_cx_scan_buf_i_${index}/i_a
           create_connection apu_p_rtl2_tessent_tdr_sri_ctrl_inst/ext_mode tessent_scan_mux_i_${index}/i_sel
	 
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
           create_connection apu_p_rtl2_tessent_tdr_sri_ctrl_inst/ext_mode tessent_cx_and_gate_i_${index}/i_a
           
	   create_instance tessent_intest_and_gate_i_${index} -of_module axe_tcl_std_and2
	   delete_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
           create_connection tessent_intest_and_gate_i_${index}/o_z ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
           create_connection apu_p_rtl2_tessent_tdr_sri_ctrl_inst/int_mode tessent_intest_and_gate_i_${index}/i_a
           
           create_instance tessent_occ_scan_buf_o_${index} -of_module axe_tcl_std_buffer
           create_connection tessent_occ_scan_buf_o_${index}/o_z tessent_intest_and_gate_i_${index}/i_b
           create_connection tessent_occ_scan_buf_o_${index}/o_z tessent_cx_and_gate_i_${index}/i_b
	   
	 } else {
	   create_instance tessent_cx_and_gate_i_${index} -of_module axe_tcl_std_and2
           delete_connection ${leaf}
	   create_connection tessent_cx_and_gate_i_${index}/o_z ${leaf}
           create_connection apu_p_rtl2_tessent_tdr_sri_ctrl_inst/ext_mode tessent_cx_and_gate_i_${index}/i_a
           
	   create_instance tessent_intest_and_gate_i_${index} -of_module axe_tcl_std_and2
	   delete_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
           create_connection tessent_intest_and_gate_i_${index}/o_z ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
           create_connection apu_p_rtl2_tessent_tdr_sri_ctrl_inst/int_mode tessent_intest_and_gate_i_${index}/i_a
           
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
       #puts $pin_name
       
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
       #puts $pin_name
       
       if {[lsearch -exact $cx_scan_out_list $pin_name] == -1} {
          regexp $pattern $pin match index
          delete_connection ${pin}
          create_instance tessent_scan_buf_o_${index} -of_module axe_tcl_std_buffer
          create_connection tessent_scan_buf_o_${index}/o_z ${pin}
	}
  }

  # Connect occ scan chain 
  connect_occ_scan_chain

  # reconnect wrapper cells to OCC clock
  
    set wrapper_cells [get_fanouts i_clk -stop_on pin]
  foreach_in_collection cell $wrapper_cells {
    set leaf [get_attribute_value_list $cell -name name]
    if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
      echo $leaf
      delete_connection $leaf
      create_connection apu_p_rtl2_tessent_occ_apu_top_aclk_inst/clock_out $leaf
    }
  }

  set wrapper_cells [get_fanouts i_ref_clk -stop_on pin]
  foreach_in_collection cell $wrapper_cells {
    set leaf [get_attribute_value_list $cell -name name]
    if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
      echo $leaf
      delete_connection $leaf
      create_connection apu_p_rtl2_tessent_occ_apu_top_ref_clk_inst/clock_out $leaf    }
  }

############# tessent is not connecting scan-in signals correctly during process_dft ### temporary fix
  delete_connection [get_pins u_apu/u_axe_ax65_cluster/to_scan_in_gi_core_*]
  delete_connection [get_pins u_apu/u_axe_ax65_cluster/to_scan_in_gi_core_*]
  delete_connection [get_pins u_apu/u_axe_ax65_cluster/g_cores[*].u_core_p/scan_in[*]]
  delete_connection [get_pins apu_p_rtl2_tessent_ssn_scan_host_sh_inst/to_scan_in_gi_core_*]
  
  for {set j 0} {$j < 6} {incr j} {
    for {set i 0} {$i < 12} {incr i} {
    create_connection apu_p_rtl2_tessent_ssn_scan_host_sh_inst/to_scan_in_gi_core_${j}[$i] u_apu/u_axe_ax65_cluster/g_cores[$j].u_core_p/scan_in[$i]
      
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

# set_config_value [get_config_elements *parent_instance -hierarchical -in $dftSpec] u_dft_physblock_top

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

source ../../init_mbist.tcl

# Block and all subblock patterns
set_defaults_value PatternsSpecification/SignOffOptions/simulate_instruments_in_lower_physical_instances on
set patSpec [create_patterns_specification -replace]

set ClockPeriods_wrappers [get_config_elements ClockPeriods -in $patSpec -hier]
foreach_in_collection ClockPeriods_wrapper $ClockPeriods_wrappers {
  add_config_element i_ref_clk -in $ClockPeriods_wrapper -value "10ns"
}

###Add reset proc in MemoryBist_P* and MemoryBist_ParallelRetentionTest_P* patterns
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
