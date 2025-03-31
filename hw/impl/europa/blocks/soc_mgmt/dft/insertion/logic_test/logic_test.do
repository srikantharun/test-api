# Settings
set DESIGN            soc_mgmt_p
set DESIGN_ID         rtl2
set USE_MBIST_TSDB    1
set USE_PREPROCESSING 1
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
if { [llength $MEM_LIBS_MEMLIB] == 0 && [llength $REG_FILES_MEMLIB] == 0 } {
  set USE_MBIST_TSDB    0
} else {
  read_mem_libs
}

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
#add_dft_signals ltest_en  -source test_mode -make_ijtag_port
# DFT Signal used to test memories with multi-load ATPG patterns
add_dft_signals memory_bypass_en 
# DFT Signal used for Scan Tested network to be tested during logic test
add_dft_signals tck_occ_en 
# DFT Signals used for hierarchical DFT 
add_dft_signals int_ltest_en ext_ltest_en int_mode ext_mode int_edt_mode ext_edt_mode
add_dft_signals shift_capture_clock -create_from_other_signals

add_input_constraints test_mode -C1

if { $USE_PREPROCESSING } {
  set_context dft -rtl -design_id ${DESIGN_ID}_a
  set_system_mode insertion
  #delete_connections u_noc_pctl/g_clkdiv[0].u_clkdiv/i_clk
  #create_connections u_soc_mgmt/u_soc_mgmt_clk_gen/o_fast_clk_ext u_noc_pctl/g_clkdiv[0].u_clkdiv/i_clk
    
  delete_connections u_soc_mgmt/u_soc_mgmt_reset_gen/i_dft_clk_rst_ctrl
  create_connections test_mode u_soc_mgmt/u_soc_mgmt_reset_gen/i_dft_clk_rst_ctrl
  
  delete_connections u_soc_mgmt/u_soc_mgmt_reset_gen/i_test_rst_n
  create_connections i_por_rst_n u_soc_mgmt/u_soc_mgmt_reset_gen/i_test_rst_n
  
  #delete_connections u_soc_mgmt/u_ncejdtm200/tdo_out_en
      
  write_design -tsdb

  set_system_mode setup
  set_context dft -rtl -design_id ${DESIGN_ID}
}

if { $USE_MBIST_TSDB == 0 } {
    add_clock 0 i_ref_clk 	-period 20ns -pulse_always
    # this is a func jtag clk
    add_clock 0 i_jtag_tck 	-period 20ns -pulse_always
    
    add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_fast_clk_int    -period 20ns -pulse_always
    add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_pvt_clk        	-period 20ns -pulse_always
    add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_periph_clk_int 	-period 20ns -pulse_always
    #add_clock 0 u_soc_mgmt/u_soc_mgmt_clk_gen/o_rtc_clk            -period 20ns -pulse_always
    # add reset signals
    add_input_constraints [get_ports i*_rst_n] -c1
}

report_dft_signals

add_nonscan_instances -instances u_soc_mgmt/u_soc_mgmt_clk_gen
add_nonscan_instances -instances u_soc_mgmt/u_freq_meter
add_nonscan_instances -instances u_noc_pctl/g_clkdiv[0].u_clkdiv
#add_nonscan_instances -module    [get_modules DW_tap*]


add_dft_control_point [get_fanin u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[0].u_reset_gen_basic_block_rst/i_rst_n -stop_on net]   -type async_set_reset

add_dft_control_point [get_fanin u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[1].u_reset_gen_basic_block_rst/i_rst_n -stop_on net]   -type async_set_reset

add_dft_control_point [get_fanin u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[*].u_reset_gen_basic_block_rst/gen_rst_stretcher_exist.u_axe_ccl_rst_n_sync/i_rst_n -stop_on net]   -type async_set_reset

#add_dft_control_point [get_fanin u_soc_mgmt/u_soc_mgmt_reset_gen/gen_reset_stages[2].u_reset_gen_basic_block_rst/gen_rst_stretcher_exist.u_axe_ccl_rst_n_sync/i_rst_n -stop_on net]  -type async_set_reset

set_dft_specification_requirements -logic_test on

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [file exists ${DESIGN}.def ] } {
  read_def ${DESIGN}.def
}

#set_drc_handling DFT_C9 war

set_system_mode analysis


set dftSpec [create_dft_specification -sri_sib_list {edt occ ssn sri_tdr_pll_0 sri_tdr_pll_1 sri_tdr_pll_2} -replace ]

report_config_data $dftSpec

################################### ADD PLL TDR ############
  
set pll_0_inst "u_soc_mgmt/u_soc_mgmt_clk_gen/gen_plls[0].u_pll_wrapper" 
set pll_1_inst "u_soc_mgmt/u_soc_mgmt_clk_gen/gen_plls[1].u_pll_wrapper" 
set pll_2_inst "u_soc_mgmt/u_soc_mgmt_clk_gen/gen_plls[2].u_pll_wrapper" 

# add_pll_tdr proc defined in tessent_setup.tcl
add_pll_tdr sri_tdr_pll_0 pll_0 $pll_0_inst
add_pll_tdr sri_tdr_pll_1 pll_1 $pll_1_inst
add_pll_tdr sri_tdr_pll_2 pll_2 $pll_2_inst

############################### ADD SSN EDT OCC ###################

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
        
        ChainGroup (gi) {
	}
	Interface {
	  ChainGroup {
	    test_clock_present : on;
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
      scan_chain_count       : 70;
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
  }
}

# define occ hookups
set occ_clk_list [list \
  soc_mgmt_ref_clk           i_ref_clk \
  soc_mgmt_fast_clk          u_soc_mgmt/u_soc_mgmt_clk_gen/o_fast_clk_int \
  soc_mgmt_pvt_clk           u_soc_mgmt/u_soc_mgmt_clk_gen/o_pvt_clk \
  soc_mgmt_periph_clk_int    u_soc_mgmt/u_soc_mgmt_clk_gen/o_periph_clk_int \
]

foreach {id clk} $occ_clk_list {
  set occ [add_config_element OCC/Controller($id) -in $dftSpec]
  set_config_value clock_intercept_node -in $occ $clk
}

################################### ADD kse3 TAP ############
read_config_data -in_wrapper $dftSpec/IjtagNetwork -first -from_string {
    HostScanInterface(tap) {
      Interface {
        tck : tck;
        trst : trst;
        tms : tms;
        tdi : tdi;
        tdo : tdo;
      }
      Tap(kse3) {
      }
   }
}

#set_config_value Interface/tdo_en -in_wrapper [get_config_elements -hier HostScanInterface(tap)] tessent_fake_tdo_en_or_gate/i_c

add_config_element HostIjtag(kse3) -in_wrapper [get_config_elements -hier Tap(kse3) -in_wrappers $dftSpec]
add_config_element Sib(kse3)       -in_wrapper [get_config_elements -hier HostIjtag(kse3) -in_wrappers $dftSpec]

report_config_data $dftSpec

################################### ADD kse3 TDRs ############

add_config_element Tdr(kse3)       -in_wrapper [get_config_elements -hier Sib(kse3) -in_wrappers $dftSpec]

set SecTdr [get_attribute_value_list [get_config_elements -hier Tdr(kse3) -in_wrappers $dftSpec] -name name]

set tdr_core_inst "u_soc_mgmt/u_soc_mgmt_secu_enclave/u_kse_jtag_tdr/u_kse_jtag_tdr_core"

set_config_value parent_instance          -in_wrapper [get_config_elements -hier Tdr(kse3)] $tdr_core_inst  
set_config_value extra_bits_capture_value -in_wrapper [get_config_elements -hier Tdr(kse3)] self  


add_config_element $SecTdr/DataInPorts

add_config_element $SecTdr/DataOutPorts

set_config_value multiplexing -in_wrapper $SecTdr/DataOutPorts off
  
  
  add_config_element $SecTdr/DataInPorts/connection(0)  -value $tdr_core_inst/i_jtag_ready
  add_config_element $SecTdr/DataInPorts/connection(1)  -value $tdr_core_inst/i_jtag_kse_error
  add_config_element $SecTdr/DataInPorts/connection(2)  -value $tdr_core_inst/i_jtag_ahb_error
  add_config_element $SecTdr/DataInPorts/connection(3)  -value $tdr_core_inst/i_jtag_cmd_ignored
  
  set pin_sz [sizeof_collection [get_pins "$tdr_core_inst/i_ahb_hrdata"]]

  for {set i 0} {$i < $pin_sz } {incr i } { 
    set j [expr {$i + 4}]
    add_config_element $SecTdr/DataInPorts/connection($j) -value $tdr_core_inst/i_ahb_hrdata[$i] 
  }
  
  # DataOutPorts
  add_config_element $SecTdr/DataOutPorts/connection(0) -value $tdr_core_inst/o_init_kse3_adac_itf 
  add_config_element $SecTdr/DataOutPorts/connection(1) -value $tdr_core_inst/o_enter_jtag_access_mode 
  add_config_element $SecTdr/DataOutPorts/connection(2) -value $tdr_core_inst/o_ahb_valid 
  add_config_element $SecTdr/DataOutPorts/connection(3) -value $tdr_core_inst/o_ahb_hwrite 
  add_config_element $SecTdr/DataOutPorts/connection(4) -value $tdr_core_inst/o_transaction_id 
  add_config_element $SecTdr/DataOutPorts/connection(5) -value $tdr_core_inst/o_jtag_dbg 

  set pin_sz [sizeof_collection [get_pins "$tdr_core_inst/o_ahb_hwdata"]]
  
  for {set i 0} {$i < $pin_sz } {incr i } { 
    set j [expr {$i + 6}]
    add_config_element $SecTdr/DataOutPorts/connection($j) -value $tdr_core_inst/o_ahb_hwdata[$i] 
  }

  set init $pin_sz
  set pin_sz [sizeof_collection [get_pins "$tdr_core_inst/o_ahb_haddr"]]
  
  for {set i 0} {$i < $pin_sz } {incr i } { 
    set j [expr {$i + $init + 6}]
    add_config_element $SecTdr/DataOutPorts/connection($j) -value $tdr_core_inst/o_ahb_haddr[$i] 
  }

################ ADD TAP kse3 bypass #########

set_config_value [get_config_elements -hier daisy_chain_with_existing_client -in_wrapper $dftSpec] off
#add_config_element HostIjtag(security)   -in_wrapper [get_config_elements -hier Tap(security) -in_wrappers $dftSpec]
add_config_element Tdr(mux_control_tdr)  -in_wrapper [get_config_elements -hier HostIjtag(kse3) -in_wrappers $dftSpec]

set MuxTdr [get_attribute_value_list [get_config_elements -hier Tdr(mux_control_tdr) -in_wrappers $dftSpec] -name name]
add_config_element $MuxTdr/DataOutPorts
set_config_value $MuxTdr/DataOutPorts/count 2
set_config_value $MuxTdr/DataOutPorts/port_naming {dft_security_mux_ctrl[%d]}

set hsi [get_config_element HostScanInterface(tap) -in $dftSpec -hier]

set sec_tap  [get_config_element Tap(kse3) -in $dftSpec -hier]

read_config_data -in_wrapper $hsi -from_string {
  ScanMux(dbg_tap_bypass) {
    select : tdr(mux_control_tdr)/DataOut(0);
    leaf_instance_name : dbg_tap_bypass_inst;
    Input(0) {
      DesignInstance(soc_mgmt_p_rtl1_tessent_tap_main_inst) {
      }
    }
    Input(1) {
      DesignInstance(u_soc_mgmt/u_ncejdtm200/ncejdtm200_tap) {
      }
    }
  }
}

read_config_data -in_wrapper $hsi -from_string {
  ScanMux(sec_tap_bypass) {
    select : tdr(mux_control_tdr)/DataOut(1);
    leaf_instance_name : sec_tap_bypass_inst;
    Input(0) {
    }
    Input(1) {
    }
  }
}

set dbg_mux [get_config_element ScanMux(dbg_tap_bypass) -hier]

move_config_element $sec_tap -in [get_config_element ScanMux(sec_tap_bypass)/Input(1) -in $hsi -hier]
move_config_element $dbg_mux -in [get_config_element ScanMux(sec_tap_bypass)/Input(0) -in $hsi -hier]

################################################# POST-DFT INSERTION ##############

report_config_data $dftSpec

# post-insertion process
# 1- add scan hookup buffers
# 2- connect occ chain
proc process_dft_specification.post_insertion {[get_current_design] args} {

  global DESIGN
  global DESIGN_ID

  set pattern {edt_scan_in\[(\d+)\]}
  foreach_in_collection item [get_pins ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/edt_scan_in] {
       set leaf [get_attribute_value_list $item -name name]
       set pin_leaf [get_attribute_value_list $item -name leaf_name]
       set pin [string trim $pin_leaf "{}"]
       #puts "${pin}"
       regexp $pattern $leaf match index
       	 if {[regexp {edt_scan_in\[0\]} $pin]} {
           create_instance tessent_occ_scan_buf_i_${index} -of_module axe_tcl_std_buffer
           create_connection ${leaf} tessent_occ_scan_buf_i_${index}/i_a
	 } else {
           create_instance tessent_scan_buf_i_${index} -of_module axe_tcl_std_buffer
           create_connection ${leaf} tessent_scan_buf_i_${index}/i_a
	 }

  }

  set pattern {edt_scan_out\[(\d+)\]}
  #create_instance tessent_tie0_cell -of_module TIELO_D1_N_S6TR_C54L08
  foreach_in_collection item [get_pins ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/edt_scan_out] {
       set leaf [get_attribute_value_list $item -name name]
       set pin_leaf [get_attribute_value_list $item -name leaf_name]
       set pin [string trim $pin_leaf "{}"]
       #puts "${pin}"
       regexp $pattern $leaf match index
       
       	 if {[regexp {edt_scan_out\[0\]} $pin]} {
           
           create_instance tessent_occ_scan_buf_o_${index} -of_module axe_tcl_std_buffer
           delete_connection ${leaf}
           create_connection tessent_occ_scan_buf_o_${index}/o_z ${leaf}
	   
	 } else {
          
	  create_instance tessent_scan_buf_o_${index} -of_module axe_tcl_std_buffer
          delete_connection ${leaf}
          create_connection tessent_scan_buf_o_${index}/o_z ${leaf}
	  
	}
    }

  # Connect occ scan chain 
  connect_occ_scan_chain
  
  # reconnect clk_gen ref clock to pre-occ source
  delete_connection u_soc_mgmt/u_soc_mgmt_clk_gen/i_clk
  create_connection i_ref_clk u_soc_mgmt/u_soc_mgmt_clk_gen/i_clk

 ################# ADD TAP KSE3 MUX BYPASS ###################
  #create_instance dft_kse3_tap_bypass_mux -of_module axe_tcl_std_mux2
  #create_connections soc_mgmt_p_rtl2_tessent_tap_kse3_inst/tdo dft_kse3_tap_bypass_mux/i_b
  #create_connections u_soc_mgmt/u_soc_mgmt_clk_gen/u_dw_tap_clkgen/tdo  dft_kse3_tap_bypass_mux/i_a
  #create_connections u_soc_mgmt/u_soc_mgmt_secu_enclave/o_aor_tap_config[0] dft_kse3_tap_bypass_mux/i_sel
  #delete_connections tdo
  #create_connections dft_kse3_tap_bypass_mux/o_z tdo


  delete_connections soc_mgmt_p_rtl1_tessent_tap_main_inst/tdi
  create_connections u_soc_mgmt/u_ncejdtm200/ncejdtm200_tap/tdo soc_mgmt_p_rtl1_tessent_tap_main_inst/tdi
  delete_connections u_soc_mgmt/u_ncejdtm200/ncejdtm200_tap/tdi 
  create_connections soc_mgmt_p_rtl2_tessent_tap_kse3_inst/tdo u_soc_mgmt/u_ncejdtm200/ncejdtm200_tap/tdi

  # ijtag_si internal pins disconnected during dft process, reconnect them
  foreach_in_collection item [get_pins soc_mgmt_p_rtl1_*/ijtag_si] {
       set leaf [get_attribute_value_list $item -name name]
       #create_connections u_soc_mgmt/u_ncejdtm200/ncejdtm200_tap/tdo $leaf
       
   }
  
  delete_connections u_soc_mgmt/u_soc_mgmt_clk_gen/soc_mgmt_p_rtl2_tessent_tdr_pll_2_inst/ijtag_si
  delete_connections soc_mgmt_p_rtl2_tessent_sib_sri_tdr_pll_2_inst/ijtag_si

  create_connections soc_mgmt_p_rtl1_tessent_sib_sri_ctrl_inst/ijtag_so u_soc_mgmt/u_soc_mgmt_clk_gen/soc_mgmt_p_rtl2_tessent_tdr_pll_2_inst/ijtag_si
  create_connections soc_mgmt_p_rtl1_tessent_sib_sri_ctrl_inst/ijtag_so soc_mgmt_p_rtl2_tessent_sib_sri_tdr_pll_2_inst/ijtag_si
}

############################### PROCESS DFT SPEC ##############

process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

extract_icl

# ICLNetwork
set patSpec [create_patterns_specification]
report_config_data $patSpec
process_patterns_specification

exit
