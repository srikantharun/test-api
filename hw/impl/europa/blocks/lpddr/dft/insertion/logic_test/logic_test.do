# Settings
set DESIGN            lpddr_p
set DESIGN_ID         rtl2
set GENERATION        1
set USE_MBIST_TSDB    1
set USE_PREPROCESSING 0
set BLACKBOXES        { }

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}



if { $GENERATION } {

    set_context dft -rtl -design_id ${DESIGN_ID}
    set_tsdb_output_directory ./tsdb_outdir
    # Mem lib
    read_mem_libs
    
    dofile ${DEPENDENCIES_DIR}/read_rtl.do

    if { $USE_MBIST_TSDB } {
        open_tsdb ../memory_test/tsdb_outdir
        read_design snps_ddr_subsystem -design_id rtl1 -force
    }
    
    read_icl ${GIT_ROOT}/hw/impl/europa/blocks/lpddr/dft/icl/dwc_ddrphy_jtag_dfttdrs.icl

    set_current_design ${DESIGN}
    set_design_level physical_block

    if { [llength $BLACKBOXES] > 0 } {
        add_black_boxes -modules $BLACKBOXES
    } else {
        add_black_boxes -auto
    }

    add_dft_signals ltest_en -create_with_tdr 
    add_dft_signals async_set_reset_static_disable
    add_dft_signals control_test_point_en observe_test_point_en
    add_dft_signals edt_clock -create_from_other_signals
    add_dft_signals shift_capture_clock -source_nodes i_lpddr_clk
    add_dft_signals occ_kill_clock_en -create_with_tdr 
    add_dft_signals int_ltest_en ext_ltest_en int_mode ext_mode int_edt_mode ext_edt_mode
    # DFT Signal used to test memories with multi-load ATPG patterns
    add_dft_signals memory_bypass_en 


    if { $USE_MBIST_TSDB } {
        #add_dft_signals shift_capture_clock -create_from_other_signals
    }

    add_clock 0 i_lpddr_clk -period 1ns -pulse_always
    add_clock 0 i_ao_clk    -period 100ns -pulse_always

    add_clock 1 i_ao_rst_n 
    add_clock 1 i_global_rst_n 

    add_clock tck ; # needed for init.testproc

    report_dft_signals

    set_dft_specification_requirements -logic_test on \
        -add_test_clock_on_ssh on \
        -host_scan_interface_type tap 
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


    add_clocks u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/i_DWC_lpddr5x_phy/u_DWC_DDRPHYMASTER_topX/PLL/pllout_clk -label pllout_clk \
        -reference u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/i_DWC_lpddr5x_phy/u_DWC_DDRPHYMASTER_topX/PLL/pllin_x1 -freq_multiplier 4 
    set_drc_handling DFT_C6 warn
    set_drc_handling DFT_C9 warn
    set_drc_handling dft_c9 -auto_fix off

    ####################
    ## Added to prevent auto-dft inserting gates
    add_dft_control_points  [get_pin u_pctl/i_test_mode] -dft_signal_source_name all_test
    ##
    ####################

    set_procfile_name ../../common/init.testproc

    set_system_mode analysis

    report_dft_control_points

    set wrapper_excluded_ports [list \
                                    i_ao_rst_n \
                                    i_global_rst_n \
                                    o_ao_rst_sync_n \
                                    o_noc_rst_n \
                                    i_lpddr_clk \
                                    i_ao_clk \
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
                                    ssn_bus_clk \
                                    ssn_bus_data_in \
                                    ssn_bus_data_out \
				    BP_MEMRESET_L \
                                   ]


    set_dedicated_wrapper_cell_options on -ports [get_ports -direction input ]
    set_dedicated_wrapper_cell_options on -ports [get_ports -direction output ]

    set_wrapper_analysis_options -exclude_ports ${wrapper_excluded_ports}

    analyze_wrapper_cells
    report_wrapper_cells

    set dftSpec [create_dft_specification -sri_sib_list {edt occ ssn} -replace ]


    ##Control the embeddedscan with the internal tap
    set ebscan [add_config_element EmbeddedBoundaryScan -in $dftSpec]
    set etap   [add_config_element HostBscanInterface(tap) -in $ebscan]
    set ifce   [add_config_element Interface -in $etap]
    set_config_value ijtag_host_interface   -in $ifce Tap(main)/HostBscan
    set subs_top [get_instance -of_module [get_module snps_ddr_subsystem]]
    add_config_element EBScanInstance([get_name $subs_top]) -in $etap

    ##Add BISR sections
    set mbisr [add_config_element MemoryBisr -in $dftSpec]
    set_config_value bisr_segment_order_file -in $mbisr ./lpddr_p.bisr_segment_order

    
    set sri [get_config_element sib(sri) -in $dftSpec -hier]
    set top [get_instance -of_module [get_module snps_ddr_subsystem]]
    set sib [add_config_element Sib(scan_cfg) -in $sri]
    foreach {name pin_regex } [list \
                                      scan_shift_cg            scan_shift_cg    \
                                      scan_shift_async         scan_shift_async \
                                      scan_asst_mode           scan_asst_mode   \
                                      scan_occ_bypass          scan_occ_bypass  \
                                      scan_occ_reset           scan_occ_reset   \
                                      scan_ucclk_mode          scan_ucclk_mode  \
                                      burnIn                   BurnIn           \
                                      iddq_mode                Iddq_mode        \
                                      scan_mode                scan_mode        \
                                     ] {
        
        set tdr [add_config_element Tdr($name) -in $sib]
        set_config_value extra_bits_capture_value -in $tdr self
        set oup [add_config_element DataOutPorts -in $tdr]
        set i 0
        foreach_in_collection pin [get_pins $pin_regex  -of_inst $top] {
            add_config_element connection($i) -in $oup -value [get_name $pin]
            incr i            
        }  
    }


    set sri [get_config_element Sib(sri) -in $dftSpec -hier]
    
    set sib [add_config_element sib(tdr) -in $sri]
    set mux [add_config_element ScanMux(tdr) -in $sib]
    set_config_value  parent_instance -in $mux .
    set sel [add_config_element tdr(phy)     -in $sib]
    set outp [add_config_element DataOutPorts -in $sel]
    set_config_value count -in $outp 1
    set_config_value select -in $mux Tdr(phy)/DataOut(0)
    set j 0
    foreach i [list Cmd RdData] {
        set inst [get_config_element DesignInstance(dwc_ddrphy_jtag_dfttdrs_${i}_inst) -in $dftSpec -hier]
        set inp [add_config_element Input($j) -in $mux]
        incr j
        move_config_element $inst -in $inp
    } 

    set sib [add_config_element sib(subs) -in $sri]
    set inst [get_config_element DesignInstance(u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst) -in $dftSpec -hier]
    move_config_element $inst -in $sib


    foreach_in_collection i [get_config_element Sib(*) -in $dftSpec -hier] {
      set_config_value  parent_instance -in $i .
    }
    foreach_in_collection i [get_config_element tdr(*) -in $dftSpec -hier] {
      set_config_value  parent_instance -in $i .
    }
    

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
                OutputPipeline (po) {}
                ScanHost (sh) {
                    OnChipCompareMode {
                        present: on;
                    }
                    use_clock_shaper_cell : off;

                    ChainGroup (gx) {
                    }
                    ChainGroup (gi) {
                    }
                    ChainGroup (uncompressed) {
		    input_chain_count : 1;
		    output_chain_count : 1;
		    output_chain_count_in_on_chip_compare_mode : 1;
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
                scan_chain_count       : 1800;
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
                scan_chain_count       : 10;
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
  #Modifications are not allowed on module 'snps_ddr_subsystem', because it has the 'is_hard_module' attribut
  #delete_connection u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/snps_ddr_subsystem_rtl1_tessent_sib_sti_inst/ltest_occ_en
  #create_connection lpddr_p_rtl2_tessent_tdr_sri_ctrl_inst/tck_occ_en u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/snps_ddr_subsystem_rtl1_tessent_sib_sti_inst/ltest_occ_en

  # Connect occ scan chain 
  connect_occ_scan_chain

  # reconnect wrapper cells to OCC clock
  
    set wrapper_cells [get_fanouts i_lpddr_clk -stop_on pin]
  foreach_in_collection cell $wrapper_cells {
    set leaf [get_attribute_value_list $cell -name name]
    if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
      echo $leaf
      delete_connection $leaf
      create_connection lpddr_p_rtl2_tessent_occ_lpddr_clk_inst/clock_out $leaf
    }
  }

  set wrapper_cells [get_fanouts i_ao_clk -stop_on pin]
  foreach_in_collection cell $wrapper_cells {
    set leaf [get_attribute_value_list $cell -name name]
    if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
      echo $leaf
      delete_connection $leaf
      create_connection lpddr_p_rtl2_tessent_occ_ao_clk_inst/clock_out $leaf    }
  }

        ##############################
        set subs_top [get_name [get_instance -of_module [get_module snps_ddr_subsystem]]]
        foreach tdr [list Cmd RdData] {
            foreach con [list \
                             DdrPhyCsr${tdr}TdrCaptureEn        \
                             DdrPhyCsr${tdr}TdrShiftEn          \
                             DdrPhyCsr${tdr}TdrUpdateEn         \
                            ] {
                delete_connection ${subs_top}/$con
                delete_connection dwc_ddrphy_jtag_dfttdrs_${tdr}_inst/to_${con}
                
                create_connection dwc_ddrphy_jtag_dfttdrs_${tdr}_inst/to_${con} ${subs_top}/$con
            }

            delete_connection ${subs_top}/DdrPhyCsr${tdr}Tdr_Tdo
            delete_connection dwc_ddrphy_jtag_dfttdrs_${tdr}_inst/from_DdrPhyCsr${tdr}Tdr_Tdo
            create_connection ${subs_top}/DdrPhyCsr${tdr}Tdr_Tdo  dwc_ddrphy_jtag_dfttdrs_${tdr}_inst/from_DdrPhyCsr${tdr}Tdr_Tdo
        }

        foreach {from to} [list \
                               tck                                                             TDRCLK                          \
                               ${DESIGN}_${DESIGN_ID}_tessent_tap_main_inst/test_logic_reset   WRSTN                           \
                              ] {
            delete_connection ${subs_top}/$to
            create_connection $from ${subs_top}/$to
            
        }

        delete_connection ${subs_top}/WSI
        create_connection dwc_ddrphy_jtag_dfttdrs_Cmd_inst/to_WSI ${subs_top}/WSI
        
       

        ##############################
        foreach con [list  \
                         scan_DlyTestClk \
                         scan_UcClk] { 
            delete_connection ${subs_top}/${con}
            create_connection ${DESIGN}_${DESIGN_ID}_tessent_occ_lpddr_clk_inst/clock_out  ${subs_top}/${con}
        }

        
        foreach con [list  scan_clk] { 
            delete_connection ${subs_top}/${con}
            create_connection tessent_persistent_cell_shift_capture_clock/o_clk ${subs_top}/${con}
        }

delete_connection i_axi_low_power_interface/u_clk_gate/i_test_en
delete_connection i_ddrc_low_power_interface/u_clk_gate/i_test_en
create_connection lpddr_p_rtl2_tessent_tdr_sri_ctrl_inst/all_test i_axi_low_power_interface/u_clk_gate/i_test_en
create_connection lpddr_p_rtl2_tessent_tdr_sri_ctrl_inst/all_test i_ddrc_low_power_interface/u_clk_gate/i_test_en
delete_connection u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[0]
delete_connection u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[1]
delete_connection u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[2]
delete_connection u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[3]
delete_connection u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[4]
delete_connection u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[5]
create_connection lpddr_p_rtl2_tessent_ssn_scan_host_sh_inst/scan_en u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[0]
create_connection lpddr_p_rtl2_tessent_ssn_scan_host_sh_inst/scan_en u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[1]
create_connection lpddr_p_rtl2_tessent_ssn_scan_host_sh_inst/scan_en u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[2]
create_connection lpddr_p_rtl2_tessent_ssn_scan_host_sh_inst/scan_en u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[3]
create_connection lpddr_p_rtl2_tessent_ssn_scan_host_sh_inst/scan_en u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[4]
create_connection lpddr_p_rtl2_tessent_ssn_scan_host_sh_inst/scan_en u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/scan_shift_i[5]

}

    
    set subs_top [get_name [get_instance -of_module [get_module snps_ddr_subsystem]]]
    # define OCC structures
    ##########clk_id#########clk_src########
    set occ_clk_list [list \
                          lpddr_clk        i_lpddr_clk                    i_lpddr_clk \
                          ao_clk           i_ao_clk                       i_ao_clk    \
                         ]

    foreach {id clk fclk } $occ_clk_list {
        set occ [add_config_element OCC/Controller($id) -in $dftSpec]
        set_config_value clock_intercept_node -in $occ $clk
        set cons [get_config_element connections -in $occ ]
        set_config_value fast_clock -in $cons $fclk
    }


    report_config_data $dftSpec
    process_dft_specification

    # Print modified files list to shell and to listfile
    write_filemap ./tsdb_outdir/modified_files.lst
    extract_icl

} else {
    set_context patterns -ijtag -rtl

    open_tsdb ../memory_test/tsdb_outdir
    read_design snps_ddr_subsystem -design_id rtl1 -force
    
    open_tsdb ./tsdb_outdir
    read_design $DESIGN -design_id $DESIGN_ID 

    
    set_current_design ${DESIGN}
    

    set_procfile_name ../../common/init.testproc
    
    add_black_box -auto

    check_design_rules
}


# ICLNetwork
set patSpec [create_patterns_specification]

source ../../../../pcie/dft/pdl/masked_val.tcl
source ../../pdl/lpddr.pdl
foreach_in_collection mbist_pat [get_config_element Patterns(MemoryBist*) -in $patSpec] {
    set dcs       [get_config_element DftControlSettings -in $mbist_pat]
    
    set cps       [get_config_element AdvancedOptions/ConstantPortSettings -in $mbist_pat]
    foreach_in_collection p [get_ports {i_lpddr_axi* i_lpddr_sys* i_lpddr_cfg* i_noc_*} -bundle] {
        set pn [get_name $p]
        add_config_element -in $cps $pn -value 0
    }

    set ao [get_config_element AdvancedOptions -in $mbist_pat]
    set_config_value procfile_name             -in $ao ../../common/init.testproc
    set_config_value no_initialization         -in $ao on

    set cp       [get_config_element ClockPeriods -in $mbist_pat]
    add_config_element -in $cp ssn_bus_clk -value 10ns

    read_config_data -in $mbist_pat -first -from_string {
        ProcedureStep(init) {
            iCall(pll_init){
                iProcArguments {
                }
            }
        }
    }
    read_config_data -in $mbist_pat -first -from_string {
        ProcedureStep(reset) {
            run_before_dft_control_settings  : on;
            iCall(pulse_resets){
                iProcArguments {
                }
            }
        }
    }
}


############################################
##Low voltage test with read-margin adjusted

set orig_mbist_pat [get_config_element Patterns(MemoryBist_P1) -in $patSpec]
set mbist_pat [add_config_element Patterns(MemoryBist_P1_low_voltage) -in $patSpec -copy_from $orig_mbist_pat]
set dcs       [get_config_element DftControlSettings -in $mbist_pat]
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.adme_control0_ra1_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.adme_control0_rf1_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.adme_control0_rf2_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.adme_control1_ra1_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.adme_control1_rf1_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.adme_control1_rf2_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.adme_control2_ra1_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.adme_control2_rf1_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.adme_control2_rf2_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.kcs_control0_rf2_hs   -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcs_control0_ra1_hs   -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcs_control0_rf1_hs   -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcs_control1_ra1_hs   -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcs_control1_rf1_hs   -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcsrd_control0_rf2_hs -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcsrd_control1_rf2_hs -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcsw_control0_ra1_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcsw_control0_rf1_hs  -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcswr_control0_rf2_hs -value 0
add_config_element -in $dcs u_lpddr_subsys_wrapper_snps_ddr_subsystem_inst.mcswr_control1_rf2_hs -value 0



set cp       [get_config_element ClockPeriods -in $mbist_pat]
set_config_value i_lpddr_clk -in $cp 100ns  ;# 10MHz 
set_config_value ssn_bus_clk -in $cp 100ns

##Set the PLL into bypass mode to allow slower testing due to read-margin-adjust ram timing
delete_config_element ProcedureStep(init) -in $mbist_pat
read_config_data  -before [index_collection [get_config_element TestStep(*) -in $mbist_pat] 0] -from_string {
    ProcedureStep(init) {
        iCall(pll_bypass){
            iProcArguments {
            }
        }
    }
}
#The ClockPeriods have been increased from what the test was created with
#this accounts for the extra time taken to carry out the tasks as a result
foreach_in_collection step [get_config_element TestStep(*) -in $mbist_pat] {
    if {[get_config_element MemoryBist -in $step -count -silent]} {
        set mbist [get_config_element MemoryBist -in $step ]
        foreach_in_collection ctrl [get_config_element Controller(*)/ -in $mbist -silent] {
            set ao [get_config_element  AdvancedOptions -in $ctrl]
            set_config_value test_time_multiplier -in $ao 200
        }
    }
}


############################################
## Done for all mbist pattern simulations
foreach_in_collection pat [get_config_element Patterns(MemoryBist_*) -in $patSpec] {
    #very first thing to be called.  To set the simulation power pins
    read_config_data -in $pat -first -from_string {
	ProcedureStep(sim_init) {
	    run_before_dft_control_settings : on;
	    iCall(simulation_only_init){
		iProcArguments {
		}
	    } 
	}
    }
}

if { 1 } {

    foreach patf [glob -directory ../../pdl/ "ate_*.pdl"] {
        source ${patf}
        set patn [file tail [file rootname $patf]] 

        set pat [add_config_element Patterns($patn) -in $patSpec]

        ##clocks are needed for phy to boot.
        set cp       [get_config_element ClockPeriods -in $pat]
        add_config_element -in $cp  i_lpddr_clk -value 1ns
        add_config_element -in $cp  i_ao_clk    -value 100ns

        #Enable the clocks 
        set dcs       [get_config_element DftControlSettings -in $pat]
        add_config_element -in $dcs all_test -value 1

        ## For block level sims only
        set cps       [get_config_element AdvancedOptions/ConstantPortSettings -in $pat]
        foreach_in_collection p [get_ports {i_lpddr_axi* i_lpddr_sys* i_lpddr_cfg* i_noc_*} -bundle] {
            set pn [get_name $p]
            add_config_element -in $cps $pn -value 0
        }

        set ao [get_config_element AdvancedOptions -in $pat]
        set_config_value procfile_name             -in $ao ../../common/init.testproc
        set_config_value no_initialization         -in $ao on


        read_config_data -in $pat -from_string {
	ProcedureStep(sim_init) {
	    run_before_dft_control_settings : on;
	    iCall(simulation_only_init){
		iProcArguments {
		}
	    } 
	}
            ProcedureStep(reset) {
                run_before_dft_control_settings  : on;
                iCall(pulse_resets){
                    iProcArguments {
                    }
                }
            }
        }

        read_config_data -in $pat -from_string "
        ProcedureStep($patn) {
            iCall($patn){
                iProcArguments {
                }
            }
        }
    "
   
    }
}


report_config_data $patSpec
process_patterns_specification

exit
