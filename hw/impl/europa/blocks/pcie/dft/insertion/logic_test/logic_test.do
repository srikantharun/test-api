# Settings
set DESIGN            pcie_p
set DESIGN_ID         rtl2
set GENERATE          1  ; # if setting to zero remove the rm -f tsdb_outdir from run.sh
set USE_MBIST_TSDB    1
set USE_PREPROCESSING 0
set BLACKBOXES        { }

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}


if { $GENERATE } {

    set_context dft -rtl -design_id ${DESIGN_ID}
    set_tsdb_output_directory ./tsdb_outdir

    set_ijtag_retargeting_options -tck_period 10ns
    
				
    # Mem lib
    read_mem_libs

    if { $USE_MBIST_TSDB } {
        open_tsdb ../memory_test/tsdb_outdir
        read_design DWC_pcie_subsystem -design_id rtl1
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
    report_black_boxes

    add_input_constraint -equivalent i_ref_pad_clk_p -invert i_ref_pad_clk_m
    add_clock 0 i_ref_pad_clk_p -period 10ns -label ref_clk_p

    set rx_ports [get_ports {i_pcie_rx*}]
    foreach_in_collection p $rx_ports {
        add_input_constraints $p -cx
    }
    add_input_constraints io_pcie_resref -CTZ

    set inputs {}
    set outputs {}

    for {set i 0 } {$i < [expr [sizeof_collection $rx_ports]/2]} { incr i} {
        foreach p [list m p] {
            append_to_collection inputs  [get_port i_pcie_rx${p}_0${i}]
            append_to_collection outputs [get_port o_pcie_tx${p}_0${i}]
        }
    }
    add_loadboard_loopback_pairs -inputs $inputs -outputs $outputs  -ac_delay_to_z 10ns
    set_flat_model_options -emulate_loadboard_loopback_pairs on

    # TBC if needed
    #add_clock 0 u_pcie_subsys/ltest_clk       -period 10ns ; #dynamic_dft_control  shift_capture_clock

    add_clock 0 i_ref_clk                     -period 20ns

    add_clock 0 i_ref_alt_clk_p               -period 10ns

    add_clock 0 i_pcie_aux_clk                -period 10ns
    add_clock 0 i_pcie_targ_cfg_dbi_axi_clk   -period 10ns
    add_clock 0 i_apb_pclk                    -period 10ns

    add_clock 0 i_pcie_init_mt_axi_clk        -period 1.67ns
    add_clock 0 i_pcie_targ_mt_axi_clk        -period 1.67ns

    add_clock 0 u_phy0_mplla_word_fr_clk_d2/i_clk -period 1ns
    add_clock u_phy0_mplla_word_fr_clk_d2/o_clk -reference u_phy0_mplla_word_fr_clk_d2/i_clk -freq_divide 2  -label scan_atspeed_clk_500

    add_clock u_pcie_fast_axi_clk_d2/o_clk -reference i_pcie_init_mt_axi_clk -freq_divide 2  -label pcie_phy_fw_clk

    foreach div [list \
                     u_pcie_muxd_aux_clk_d2\
                     u_pcie_muxd_aux_clk_d4\
                     u_pcie_muxd_aux_clk_d8\
                     u_pcie_core_clk_d2    \
                     u_pcie_core_clk_d4    \
                     u_pcie_core_clk_d8    \
                    ] {

        add_clock ${div}/o_clk -reference ${div}/i_clk  -freq_divide 2
    }
    

    
    add_clocks u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0_rom_clk     -period 10ns
    add_clocks u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0_sram_clk    -period 10ns

    #these clocks will be hooked up later
    set phy_core_period 1

    set scan_clks [list    \
                       phy0_scan_rx_dword_clk    "${phy_core_period}ns" \
                       phy0_mplla_word_fr_clk    "${phy_core_period}ns" \
                       pcs_scan_clk              "${phy_core_period}ns" \
                       pcs_scan_pclk             "${phy_core_period}ns" \
                       pcs_scan_pcs_clk          "${phy_core_period}ns" \
                       pcs_scan_pma_clk          "${phy_core_period}ns" \
                       phy0_scan_mpll_dword_clk  "[expr ${phy_core_period} * 2]ns" \
                       phy0_scan_mpll_qword_clk  "[expr ${phy_core_period} * 4]ns" \
                       phy0_scan_clk              10ns \
                       phy0_scan_cr_clk           10ns \
                       phy0_scan_occ_clk          10ns \
                       phy0_scan_ref_clk          10ns \
                       phy0_ref_dig_fr_clk        20ns \
                      ]
    foreach {scan_clk period} $scan_clks {
        add_clocks u_pcie_subsys/$scan_clk -period $period
    }


    set rsts [list \
                  i_ao_rst_n              \
                  i_global_rst_n          \
                  ]
    foreach rst $rsts {
        add_clock 1 $rst
        add_dft_control_point $rst  -type async_set_reset ;# for DFT_C6 checking
    }


    set_attribute_value -name function -value trst trst
    set_attribute_value -name function -value tdi  tdi
    set_attribute_value -name function -value tms  tms
    set_attribute_value -name function -value tck  tck
    set_attribute_value -name function -value tdo  tdo


    add_dft_signals ltest_en -create_with_tdr
    add_dft_signals async_set_reset_static_disable
    add_dft_signals control_test_point_en observe_test_point_en
    add_dft_signals edt_clock -create_from_other_signals
    add_dft_signals shift_capture_clock -create_from_other_signals
    #add_dft_signals scan_en -source scan_en
    add_dft_signals occ_kill_clock_en -create_with_tdr
    add_dft_signals int_ltest_en ext_ltest_en int_mode ext_mode int_edt_mode ext_edt_mode
    ## DFT Signal used to test memories with multi-load ATPG patterns
    add_dft_signals memory_bypass_en 

    report_dft_signals

    set_dft_specification_requirements -logic_test on \
        -add_test_clock_on_ssh on \
        -host_scan_interface_type tap

    if { $USE_PREPROCESSING } {
        set_context dft -rtl -design_id ${DESIGN_ID}
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

    set mods [get_modules axe_tcl_clk_gating]
    add_dft_clock_enables [get_ports i_en      -of_modules $mods] -usage func_en
    add_dft_clock_enables [get_ports i_test_en -of_modules $mods] -usage test_en

    set_drc_handling DFT_C6 warn
    set_drc_handling DFT_C9 warn
    set_drc_handling dft_c9 -auto_fix off
    set_drc_handling i5 warn ; #needed because forced_port_high ports are not controlled by an all_test signals


    #Force clocks and reset control under test
    foreach test_mode_pin [list \
                               u_pctl/i_test_mode \
                               u_phy0_mplla_word_fr_clk_d2/i_enable \
                              ] {
        add_dft_control_points  [get_pin $test_mode_pin] -dft_signal_source_name all_test
    }

    #AM: fixing I2/I5 violations TBC -dft_signal_source_name all_test
    add_dft_control_points {u_pcie_fast_axi_clk_d2/i_test_mode} -dft_signal_source_name ltest_en
    
    add_nonscan_instances u_phy0_mplla_word_fr_clk_d2    

    #AM: fixing I2/I5 violations 
    add_nonscan_instances u_pcie_fast_axi_clk_d2


    #TODO these are AND scan enable in post_process.
    foreach {name test_mode_pin} [list \
                                      mac_scan_shift_cg    u_pcie_subsys/mac_scan_shift_cg  \
                                      pcs_scan_shift_cg    u_pcie_subsys/pcs_scan_shift_cg  \
                                      phy0_scan_shift_cg   u_pcie_subsys/phy0_scan_shift_cg \
                                      pcs_scan_shift       u_pcie_subsys/pcs_scan_shift     \
                                      phy0_scan_shift      u_pcie_subsys/phy0_scan_shift    \
                                      mac_scan_shift       u_pcie_subsys/mac_scan_shift     \
                                      mac_scan_mode        u_pcie_subsys/mac_scan_mode  \
                                      pcs_scan_mode        u_pcie_subsys/pcs_scan_mode  \
                                      phy0_scan_mode       u_pcie_subsys/phy0_scan_mode \
                                      ate_test_mode        u_pcie_subsys/ate_test_mode  \
                                     ] {
        register_static_dft_signal_names $name -reset_value 0 -default_value_in_all_test 1
        add_dft_signals $name -create_with_tdr
        add_dft_control_points [get_pin $test_mode_pin] -dft_signal_source_name $name
    }

    ## Use these to force the clock gaters on
    foreach name [list \
                      mac_scan_force_cg    \
                      pcs_scan_force_cg    \
                      phy0_scan_force_cg   \

                 ] {
        register_static_dft_signal_names $name -reset_value 0 -default_value_in_all_test 1
        add_dft_signals $name -create_with_tdr
    }

    ## TDR to allow CSR access via the JTAG interface
    set name phy_apb0_if_sel
    register_static_dft_signal_names ${name} -reset_value 1  -default_value_in_all_test 1 ; # 1 == APB 0 == JTAG
    add_dft_signals ${name}  -create_with_tdr
    add_dft_control_points [get_pin u_pcie_subsys/${name}] -dft_signal_source_name ${name}


    #################################
    set_system_mode analysis

    report_drc_rules -fails_summary > rpt/drc_fails_summary.rpt
    report_drc_rules -all_fails > rpt/drc_fails.rpt
    report_dft_control_points

    set wrapper_excluded_ports [list \
                                    i_ao_rst_n                  \
                                    i_global_rst_n              \
                                    i_ref_clk                   \
                                    i_ref_alt_clk_p             \
                                    i_pcie_aux_clk              \
                                    i_pcie_targ_cfg_dbi_axi_clk \
                                    i_apb_pclk                  \
                                    i_pcie_init_mt_axi_clk      \
                                    i_pcie_targ_mt_axi_clk      \
                                    io_pcie_resref              \
                                    i_ref_pad_clk_p             \
                                    i_ref_pad_clk_m             \
                                    i_pcie_rxm_00               \
                                    i_pcie_rxm_01               \
                                    i_pcie_rxm_02               \
                                    i_pcie_rxm_03               \
                                    i_pcie_rxp_00               \
                                    i_pcie_rxp_01               \
                                    i_pcie_rxp_02               \
                                    i_pcie_rxp_03               \
                                    o_pcie_txm_00               \
                                    o_pcie_txm_01               \
                                    o_pcie_txm_02               \
                                    o_pcie_txm_03               \
                                    o_pcie_txp_00               \
                                    o_pcie_txp_01               \
                                    o_pcie_txp_02               \
                                    o_pcie_txp_03               \
                                    tms trst tck tdi tdo tdo_en \
                                    ssn_bus_*                   \
                                    bisr_*                      \
                                   ]

    set_dedicated_wrapper_cell_options on -ports [get_ports * ]
    set_wrapper_analysis_options -exclude_ports ${wrapper_excluded_ports}

    #Using ref_clk for the non-timed signals
    foreach {p clk} [list \
                         o_pcie_targ_cfg_apb*   i_apb_pclk \
                         i_pcie_targ_*          i_apb_pclk \
                         o_pcie_obs             i_ref_clk  \
                         o_noc_rst_n            i_ref_clk  \
                         o_pcie_int             i_ref_clk  \
                        ] {
        set_dedicated_wrapper_cell_options -ports [get_ports $p ] -clock_source $clk
    }

    
    report_wrapper_analysis_options

    analyze_wrapper_cells
    report_wrapper_cells -verbose > rpt/wrapper_cells.rpt

    set dftSpec [create_dft_specification -sri_sib_list {edt occ ssn} -replace ]
    report_config_data $dftSpec

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
                    OnChipCompareMode {
                        present: on;
                    }
                    use_clock_shaper_cell : off;

                    ChainGroup (gx) {
                    }
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
    ; #read_config_data

    set sri [get_config_element sib(sri) -in $dftSpec -hier]
    set top [get_instance -of_module [get_module DWC_pcie_subsystem]]

    set sib [add_config_element Sib(test_cfg) -in $sri]
    foreach { name } [list \
                          phy_test_burnin        \
                          phy_test_powerdown     \
                          phy_test_stop_clk_en   \
                          phy_test_tx_ref_clk_en \
                          tap_phy0_ref_use_pad   \
                          pcs_scan_clk_sel       \
                          phy0_scan_clk_sel      \
                          phy0_scan_pma_occ_en   \
                         ] {

        set tdr [add_config_element Tdr($name) -in $sib]
        set_config_value extra_bits_capture_value -in $tdr self
        set oup [add_config_element DataOutPorts -in $tdr]
        set i 0
        foreach_in_collection pin [get_pins $name  -of_inst $top] {
            add_config_element connection($i) -in $oup -value [get_name $pin]
            incr i
        }
    }
    set sib [add_config_element Sib(phy) -in $sri]
    move_config_element [get_config_element DesignInstance(u_pcie_subsys) -in $sri] -in $sib
    set di [get_config_element DesignInstance(u_pcie_subsys) -in $sib]
    set_config_value scan_interface -in $di ijtag

    set hsi [get_config_element  HostScanInterface(tap) -in $dftSpec -hier]
    set ifce [get_config_element Interface -in $hsi]

    set_config_value daisy_chain_with_existing_client -in $ifce off


    # define OCC structures
    ##########clk_id#########clk_src########
    #FIXME TBC with Jon abot additional OCC location
    #init_mt_axi_clk            i_pcie_init_mt_axi_clk                   \
    #targ_mt_axi_clk            i_pcie_targ_mt_axi_clk                   
    set occ_clk_list [list \
                          ref_alt_clk_p              i_ref_alt_clk_p                          \
                          ref_clk                    u_pctl/i_clk                             \
                          aux_clk                    u_pcie_subsys/aux_clk                    \
                          apb_pclk                   u_pcie_subsys/apb_pclk                   \
                          pcs_scan_pclk              u_pcie_subsys/pcs_scan_pclk              \
                          pcs_scan_pcs_clk           u_pcie_subsys/pcs_scan_pcs_clk           \
                          pcs_scan_pma_clk           u_pcie_subsys/pcs_scan_pma_clk           \
                          pcs_scan_clk               u_pcie_subsys/pcs_scan_clk               \
                          phy0_scan_clk              u_pcie_subsys/phy0_scan_clk              \
                          phy0_scan_cr_clk           u_pcie_subsys/phy0_scan_cr_clk           \
                          phy0_scan_mpll_dword_clk   u_pcie_subsys/phy0_scan_mpll_dword_clk   \
                          phy0_scan_mpll_qword_clk   u_pcie_subsys/phy0_scan_mpll_qword_clk   \
                          phy0_scan_rx_dword_clk     u_pcie_subsys/phy0_scan_rx_dword_clk     \
                          phy0_scan_occ_clk          u_pcie_subsys/phy0_scan_occ_clk          \
                          phy0_scan_ref_clk          u_pcie_subsys/phy0_scan_ref_clk          \
                          phy_fw_clk                 u_pcie_subsys/phy_fw_clk                 \
                          mac_scan_coreclk           u_pcie_subsys/mac_scan_coreclk           \
                          mstr_aclk                  u_pcie_subsys/mstr_aclk                  \
                          dbi_aclk                   u_pcie_subsys/dbi_aclk                   \
                          slv_aclk                   u_pcie_subsys/slv_aclk                   \
                         ]

    foreach {id clk} $occ_clk_list {
        set occ [add_config_element OCC/Controller($id) -in $dftSpec]
        set_config_value clock_intercept_node -in $occ $clk
    }

    ###############################################
    ## Setup tap user bits to control the phys BSCAN config ports
    set tap [get_config_element Tap(main) -in $dftSpec -hier]
    set op  [add_config_element DataOutPorts -in $tap]

    set i 1 ;# index 0 to be used for scanmux below
    set port_name "tap_mux_sel"

    foreach pin [ list phy_bs_ce phy_bs_tx_lowswing phy_bs_rx_bigswing phy_bs_rx_level  ] {

        set pins [get_pin u_pcie_subsys/$pin ]
        set pins_sz [sizeof_collection $pins]
        set port_name "${pin} ${port_name}"

        if { $pins_sz > 1 }  {
            add_config_element connection([expr $i+$pins_sz-1]:$i) -in $op -value [get_name [get_pin u_pcie_subsys/$pin -bundle ]]
            incr i $pins_sz
        } else {
            add_config_element connection($i) -in $op -value [get_name $pins]
            incr i
        }
    }

    #set_config_value count -in $op $i
    set_config_value port_naming -in $op $port_name

    #cant use this as it produces invalid verilog adding an inverter below
    #set result "${i}'b"
    #for {} {$i >0} {incr i -1} {
    #    append result "0"
    #}
    #set_config_value reset_value -in $op $result



    #################
    #put the phy jtag interface into scan mux
    set mux [add_config_element ScanMux(phy) -in $hsi]
    set_config_value select -in $mux Tap(main)/DataOut(0) ; # when set both tap(main) and the phy_csr TAP will be in series
    set inp [add_config_element Input(0) -in $mux]
    set di  [add_config_element DesignInstance(u_pcie_subsys) -in $inp]
    set_config_value scan_interface -in $di PHY_CSR

    ##Control the embeddedscan with the internal tap
    set ebscan [add_config_element EmbeddedBoundaryScan -in $dftSpec]
    set etap   [add_config_element HostBscanInterface(tap) -in $ebscan]
    set ifce   [add_config_element Interface -in $etap]
    set_config_value ijtag_host_interface -in $ifce Tap(main)/HostBscan
    set subs_top [get_instance -of_module [get_module DWC_pcie_subsystem]]
    add_config_element EBScanInstance([get_name $subs_top]) -in $etap

    #
    ##Add BISR sections
    set mbisr [add_config_element MemoryBisr -in $dftSpec]
    set_config_value bisr_segment_order_file -in $mbisr ./pcie_p.bisr_segment_order


    foreach_in_collection i [get_config_element Sib(*) -in $dftSpec -hier] {
        set_config_value  parent_instance -in $i .
    }
    foreach_in_collection i [get_config_element tdr(*) -in $dftSpec -hier] {
        set_config_value  parent_instance -in $i .
    }

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
                create_connection ${DESIGN}_${DESIGN_ID}_tessent_tdr_sri_ctrl_inst/ext_mode tessent_scan_mux_i_${index}/i_sel
            } else {
                create_instance tessent_scan_mux_i_${index} -of_module axe_tcl_std_mux2
                create_connection ${leaf} tessent_scan_mux_i_${index}/i_b
                create_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin} tessent_scan_mux_i_${index}/i_a
                create_instance tessent_cx_scan_buf_i_${index} -of_module axe_tcl_std_buffer
                create_connection tessent_scan_mux_i_${index}/o_z tessent_cx_scan_buf_i_${index}/i_a
                create_connection ${DESIGN}_${DESIGN_ID}_tessent_tdr_sri_ctrl_inst/ext_mode tessent_scan_mux_i_${index}/i_sel
                
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
                create_connection ${DESIGN}_${DESIGN_ID}_tessent_tdr_sri_ctrl_inst/ext_mode tessent_cx_and_gate_i_${index}/i_a
                create_instance tessent_intest_and_gate_i_${index} -of_module axe_tcl_std_and2
                delete_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
                create_connection tessent_intest_and_gate_i_${index}/o_z ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
                create_connection ${DESIGN}_${DESIGN_ID}_tessent_tdr_sri_ctrl_inst/int_mode tessent_intest_and_gate_i_${index}/i_a
                create_instance tessent_occ_scan_buf_o_${index} -of_module axe_tcl_std_buffer
                create_connection tessent_occ_scan_buf_o_${index}/o_z tessent_intest_and_gate_i_${index}/i_b
                create_connection tessent_occ_scan_buf_o_${index}/o_z tessent_cx_and_gate_i_${index}/i_b
            } else {
                create_instance tessent_cx_and_gate_i_${index} -of_module axe_tcl_std_and2
                delete_connection ${leaf}
                create_connection tessent_cx_and_gate_i_${index}/o_z ${leaf}
                create_connection ${DESIGN}_${DESIGN_ID}_tessent_tdr_sri_ctrl_inst/ext_mode tessent_cx_and_gate_i_${index}/i_a
                create_instance tessent_intest_and_gate_i_${index} -of_module axe_tcl_std_and2
                delete_connection ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
                create_connection tessent_intest_and_gate_i_${index}/o_z ${DESIGN}_${DESIGN_ID}_tessent_edt_c1_int_inst/${pin}
                create_connection ${DESIGN}_${DESIGN_ID}_tessent_tdr_sri_ctrl_inst/int_mode tessent_intest_and_gate_i_${index}/i_a
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

        # Connect occ scan chain TBC whether it really does the job
        connect_occ_scan_chain

        set subs_top [get_name_list [get_instance -of_module [get_module DWC_pcie_subsystem]]]


        set clk ltest_clk
        delete_connection ${subs_top}/${clk}
        create_connection tessent_persistent_cell_shift_capture_clock/o_clk  ${subs_top}/${clk}


        #And signals with scan_enable for coverage
        set scan_enables [list \
                              u_pcie_subsys/mac_scan_shift_cg  \
                              u_pcie_subsys/pcs_scan_shift_cg  \
                              u_pcie_subsys/phy0_scan_shift_cg \
                              u_pcie_subsys/mac_scan_shift  \
                              u_pcie_subsys/pcs_scan_shift  \
                              u_pcie_subsys/phy0_scan_shift \
                              ]

        set ssh [get_instance -of_module [get_module ${DESIGN}_${DESIGN_ID}_tessent_ssn_scan_host_sh]]
        set ssh_scan_en_pin [get_pin scan_en -of_instance $ssh]

        foreach scan_enable $scan_enables {
            intercept_connection $scan_enable -cell_function_name and  -input2 $ssh_scan_en_pin
        }

        #Force the clocks on
        set force_clocks [list \
                              u_pcie_subsys/mac_scan_shift_cg  mac_scan_force_cg  \
                              u_pcie_subsys/pcs_scan_shift_cg  pcs_scan_force_cg  \
                              u_pcie_subsys/phy0_scan_shift_cg phy0_scan_force_cg \
                              ]
        foreach {pin name} $force_clocks {
            intercept_connection $pin -cell_function_name or  -input2 [get_dft_signal $name ]
        }


        ############
        #Missing clocks so add them here
        set occ_list [list \
                              phy0_mplla_word_fr_clk pcs_scan_pclk              \
                              phy0_mplla_word_fr_clk pcs_scan_pcs_clk           \
                              phy0_mplla_word_fr_clk pcs_scan_pma_clk           \
                              phy0_mplla_word_fr_clk phy0_scan_mpll_dword_clk   \
                              phy0_mplla_word_fr_clk phy0_scan_rx_dword_clk     \
                             ]
        foreach {clk occ} $occ_list {

            set inst [get_instance ${DESIGN}_${DESIGN_ID}_tessent_occ_${occ}_inst]
	    puts "AM debug: clk $clk"
	    puts "AM debug: occ instance [get_name $inst]"
            set fast_clk [get_pin fast_clock -of_inst $inst]
	    puts "AM debug:   fast_clock [get_name $fast_clk]"
            delete_connection $fast_clk
	    puts "AM debug:   connecting u_pcie_subsys/$clk to [get_name $fast_clk]"
            create_connection u_pcie_subsys/$clk $fast_clk

        }
        delete_connection u_phy0_mplla_word_fr_clk_d2/i_clk
        create_connection u_pcie_subsys/phy0_mplla_word_fr_clk u_phy0_mplla_word_fr_clk_d2/i_clk


        #Correct the connection here, i_ref_alt_clk_p has an occ
        set clk_cor [list \
                         pcs_scan_clk               \
                         phy0_scan_clk              \
                         phy0_scan_cr_clk           \
                         phy0_scan_occ_clk          \
                         phy0_scan_ref_clk          \
                        ]

        foreach clk $clk_cor {
            set inst [get_instance ${DESIGN}_${DESIGN_ID}_tessent_occ_${clk}_inst]
            set fast_clk [get_pin fast_clock -of_inst $inst]
            delete_connection $fast_clk
            create_connection i_ref_alt_clk_p $fast_clk
        }

        
        

        #there is a bug in tessent preventing the uses of reset_value
        intercept_connection u_pcie_subsys/phy_bs_ce -cell_function_name inverter
        
        ## connecting the i_clk of u_axi_m_cut u_axi_s_cut u_dbi_cut to the clock_out of the respective OCC
        set occ_list [list \
                              u_axi_m_cut   mstr_aclk \
                              u_axi_s_cut   slv_aclk  \
                              u_dbi_cut     dbi_aclk  \
                             ]
        foreach {blk occ} $occ_list {                   
	    puts "AM debug: blk [get_name [get_instances $blk]]"
	    puts "AM debug: occ instance [get_name [get_instance ${DESIGN}_${DESIGN_ID}_tessent_occ_${occ}_inst]]"
            delete_connection [get_pin i_clk -of_instance [get_instances $blk]]
            create_connection [get_pin clock_out -of_inst [get_instance ${DESIGN}_${DESIGN_ID}_tessent_occ_${occ}_inst]] [get_pin i_clk -of_instance [get_instances $blk]]
        }

        set wrapper_cells [get_fanouts i_pcie_targ_mt_axi_clk -stop_on pin]
        foreach_in_collection cell $wrapper_cells {
          set leaf [get_attribute_value_list $cell -name name]
          if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
            puts "AM debug: i_pcie_targ_mt_axi_clk $leaf"
            delete_connection $leaf
            create_connection pcie_p_rtl2_tessent_occ_slv_aclk_inst/clock_out $leaf    }
        }
      
        set wrapper_cells [get_fanouts i_pcie_targ_cfg_dbi_axi_clk -stop_on pin]
        foreach_in_collection cell $wrapper_cells {
          set leaf [get_attribute_value_list $cell -name name]
          if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
            puts "AM debug: i_pcie_targ_cfg_dbi_axi_clk $leaf"
            delete_connection $leaf
            create_connection pcie_p_rtl2_tessent_occ_dbi_aclk_inst/clock_out $leaf    }
        }
      
        set wrapper_cells [get_fanouts i_pcie_init_mt_axi_clk -stop_on pin]
        foreach_in_collection cell $wrapper_cells {
          set leaf [get_attribute_value_list $cell -name name]
          if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
            puts "AM debug: i_pcie_init_mt_axi_clk $leaf"
            delete_connection $leaf
            create_connection pcie_p_rtl2_tessent_occ_phy_fw_clk_inst/clock_out $leaf    }
        }
      
        set wrapper_cells [get_fanouts i_pcie_aux_clk -stop_on pin]
        foreach_in_collection cell $wrapper_cells {
          set leaf [get_attribute_value_list $cell -name name]
          if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
            puts "AM debug: i_pcie_aux_clk $leaf"
            delete_connection $leaf
            create_connection pcie_p_rtl2_tessent_occ_aux_clk_inst/clock_out $leaf    }
        }
      
        set wrapper_cells [get_fanouts i_ref_clk -stop_on pin]
        foreach_in_collection cell $wrapper_cells {
          set leaf [get_attribute_value_list $cell -name name]
          if {[regexp {tessent_persistent_cell_0_d*} $leaf]} {
            puts "AM debug: i_ref_clk $leaf"
            delete_connection $leaf
            create_connection pcie_p_rtl2_tessent_occ_ref_clk_inst/clock_out $leaf    }
        }

    }
    ;#proc process_dft_specification.post_insertion


    process_dft_specification

    # Print modified files list to shell and to listfile
    write_filemap ./tsdb_outdir/modified_files.lst
    write_librarymap ./tsdb_outdir/library_files.lst
    #report_wrapper_cells -verbose > rpt/wrapper_cells_post_insertion.rpt


    extract_icl

} else {
    set_context patterns -ijtag -rtl
    set_ijtag_retargeting_options -tck_period 10ns

    # Mem lib
    read_mem_libs

    open_tsdb ../memory_test/tsdb_outdir
    read_design DWC_pcie_subsystem -design_id rtl1 -force

    open_tsdb ./tsdb_outdir
    read_design $DESIGN -design_id $DESIGN_ID

    set_current_design ${DESIGN}

    add_black_box -auto

    check_design_rules


}


# ICLNetwork
set patSpec [create_patterns_specification]



#####################
## Add loopback information for BIST tests

set loadb [add_config_element  LoadBoardInfo(external_loopback_bist) -in $patSpec]
set loopb [add_config_element Loopbacks -in $loadb]

set rx_ports [get_ports {i_pcie_rx*}]
for {set i 0 } {$i < [expr [sizeof_collection $rx_ports]/2]} { incr i} {
    foreach p [list m p] {
        add_config_element [get_name [get_port i_pcie_rx${p}_0${i}]] -in $loopb -value [get_name [get_port o_pcie_tx${p}_0${i}]]
    }
}


source ../../pdl/masked_val.tcl
source ../../pdl/pcie.pdl
foreach_in_collection mbist_pat [get_config_element Patterns(MemoryBist*) -in $patSpec] {

    #########################
    set cps [get_config_element AdvancedOptions/ConstantPortSettings -in $mbist_pat]
    foreach_in_collection p [get_ports {i_pcie_clkreq_n i_pcie_init_mt_axi* i_pcie_targ_mt_axi* i_pcie_targ_cfg_dbi_axi* i_pcie_targ_cfg_apb* i_pcie_targ_syscfg_apb* i_pcie_*int i_noc_async* } -bundle -filter {name !~ *_clk} ] {
        set pn [regsub {(\[[0-9]+\])} [get_name $p] ""]
        if {[get_config_elements -in $cps $pn -count]==0} {
            add_config_element -in $cps $pn -value 0
        }
    }
    

    #########################
    set dcs [get_config_element DftControlSettings -in $mbist_pat]
    set_config_value  -in $dcs mac_scan_force_cg    1
    set_config_value  -in $dcs pcs_scan_force_cg    1
    set_config_value  -in $dcs phy0_scan_force_cg   1
    set_config_value  -in $dcs ate_test_mode        0
    set_config_value  -in $dcs phy0_scan_mode       1
    set_config_value  -in $dcs pcs_scan_mode        1
    set_config_value  -in $dcs mac_scan_mode        1
    set_config_value  -in $dcs mac_scan_shift       0
    set_config_value  -in $dcs phy0_scan_shift      0
    set_config_value  -in $dcs pcs_scan_shift       0
    set_config_value  -in $dcs phy0_scan_shift_cg   0
    set_config_value  -in $dcs pcs_scan_shift_cg    0
    set_config_value  -in $dcs mac_scan_shift_cg    1

    add_config_element -in $dcs phy_apb0_if_sel   -value     0 ;# allow jtag CR access

    #Set the default values under all_test
    #########################
    set ao [get_config_element AdvancedOptions -in $mbist_pat]
    set_config_value procfile_name             -in $ao ../../common/init.testproc
    set_config_value no_initialization         -in $ao on

    #########################
    set cp [get_config_element ClockPeriods -in $mbist_pat]
    add_config_element -in $cp ssn_bus_clk                    -value 10ns
    add_config_element -in $cp i_ref_clk                      -value 20ns
    add_config_element -in $cp i_pcie_init_mt_axi_clk         -value 10ns
    add_config_element -in $cp i_ref_alt_clk_p                -value 10ns
    add_config_element -in $cp i_ref_pad_clk_p                -value 10ns
    add_config_element -in $cp i_pcie_aux_clk                 -value 10ns
    add_config_element -in $cp i_pcie_targ_cfg_dbi_axi_clk    -value 10ns
    add_config_element -in $cp i_apb_pclk                     -value 10ns


    #########################



    read_config_data -in $mbist_pat -first -from_string {
        ProcedureStep(pll_init) {
            run_before_dft_control_settings  : on;
            iCall(pll_init){
                iProcArguments {
                }
            }
        }
    }
    read_config_data -in $mbist_pat -first -from_string {
        ProcedureStep(ate_init) {
            run_before_dft_control_settings  : on;
            iCall(ate_init){
                iProcArguments {
                }
            }
        }
    }
    read_config_data -in $mbist_pat -first -from_string {
        ProcedureStep(chip_reset) {
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
set mbist_lv_pat [add_config_element Patterns(MemoryBist_P1_low_voltage) -in $patSpec \
                      -copy_from [get_config_element Patterns(MemoryBist_P1) -in $patSpec]]

set dcs       [get_config_element DftControlSettings -in $mbist_lv_pat]
add_config_element -in $dcs u_pcie_subsys.adme_control0_ra1_hs    -value   1
add_config_element -in $dcs u_pcie_subsys.adme_control1_ra1_hs    -value   1
add_config_element -in $dcs u_pcie_subsys.adme_control2_ra1_hs    -value   1

add_config_element -in $dcs u_pcie_subsys.adme_control0_rf1_hs    -value   1
add_config_element -in $dcs u_pcie_subsys.adme_control1_rf1_hs    -value   1
add_config_element -in $dcs u_pcie_subsys.adme_control2_rf1_hs    -value   1

add_config_element -in $dcs u_pcie_subsys.adme_control0_rf2_hs    -value   1
add_config_element -in $dcs u_pcie_subsys.adme_control1_rf2_hs    -value   1
add_config_element -in $dcs u_pcie_subsys.adme_control2_rf2_hs    -value   1

add_config_element -in $dcs u_pcie_subsys.kcs_control0_rf2_hs     -value   1

add_config_element -in $dcs u_pcie_subsys.kcs_control0_vrom_hd    -value   1

add_config_element -in $dcs u_pcie_subsys.mcs_control0_ra1_hs     -value   1
add_config_element -in $dcs u_pcie_subsys.mcs_control1_ra1_hs     -value   1

add_config_element -in $dcs u_pcie_subsys.mcs_control0_rf1_hs     -value   1
add_config_element -in $dcs u_pcie_subsys.mcs_control1_rf1_hs     -value   1

add_config_element -in $dcs u_pcie_subsys.mcs_control0_vrom_hd    -value   1

add_config_element -in $dcs u_pcie_subsys.mcsw_control0_ra1_hs    -value   1
add_config_element -in $dcs u_pcie_subsys.mcsw_control0_rf1_hs    -value   1

add_config_element -in $dcs u_pcie_subsys.mcswr_control0_rf2_hs   -value   1
add_config_element -in $dcs u_pcie_subsys.mcswr_control1_rf2_hs   -value   1

add_config_element -in $dcs u_pcie_subsys.mcsrd_control0_rf2_hs   -value   1
add_config_element -in $dcs u_pcie_subsys.mcsrd_control1_rf2_hs   -value   1


#TODO check u_pcie_subsys.nonscan_test


set cp       [get_config_element ClockPeriods -in $mbist_lv_pat]
set_config_value i_ref_clk                   -in $cp 100ns  ;# 10MHz
set_config_value i_pcie_init_mt_axi_clk      -in $cp 100ns  ;# 10MHz
set_config_value i_pcie_targ_mt_axi_clk      -in $cp 100ns  ;# 10MHz
set_config_value i_pcie_aux_clk              -in $cp 100ns  ;# 10MHz
set_config_value i_ref_alt_clk_p             -in $cp 100ns  ;# 10MHz
set_config_value i_apb_pclk                  -in $cp 100ns  ;# 10MHz
set_config_value i_pcie_targ_cfg_dbi_axi_clk -in $cp 100ns  ;# 10MHz
set_config_value ssn_bus_clk                 -in $cp 100ns

##Set the PLL into bypass mode to allow slower testing due to read-margin-adjust ram timing
delete_config_element ProcedureStep(pll_init) -in $mbist_lv_pat
read_config_data  -before [index_collection [get_config_element TestStep(*) -in $mbist_lv_pat] 0] -from_string {
    ProcedureStep(pll_init) {
        iCall(pll_bypass){
            iProcArguments {
            }
        }
    }
}
#The ClockPeriods have been increased from what the test was created with
#this accounts for the extra time taken to carry out the tasks as a result
foreach_in_collection step [get_config_element TestStep(*) -in $mbist_lv_pat] {
    if {[get_config_element MemoryBist -in $step -count -silent]} {
        set mbist [get_config_element MemoryBist -in $step ]
        foreach_in_collection ctrl [get_config_element Controller(*)/ -in $mbist -silent] {
            set ao [get_config_element  AdvancedOptions -in $ctrl]
            # orginal test expected the bist clock (pllout_clk) to be 1GHz but the bypass is
            # causing it to run at 10MHz.  Extend the test time to accomodate this
            set_config_value test_time_multiplier -in $ao 100
        }
    }
}

#
#
#############################################################
if { 1 } {

foreach patf [glob -directory ../../pdl/ "ate_*.pdl"] {
    source ${patf}
    set patn [file tail [file rootname $patf]] 

    set pat [add_config_element Patterns($patn) -in $patSpec]

    #if {[regexp _ELB_ $patn] } {
        set_config_value load_board_info -in $pat external_loopback_bist
   # }

    #########################
    set cps [get_config_element AdvancedOptions/ConstantPortSettings -in $pat]
    foreach_in_collection p [get_ports {i_pcie_clkreq_n i_pcie_init_mt_axi* i_pcie_targ_mt_axi* i_pcie_targ_cfg_dbi_axi* i_pcie_targ_cfg_apb* i_pcie_targ_syscfg_apb* i_pcie_*int i_noc_async* } -bundle -filter {name !~ *_clk} ] {
        set pn [regsub {(\[[0-9]+\])} [get_name $p] ""]
        if {[get_config_elements -in $cps $pn -count]==0} {
            add_config_element -in $cps $pn -value 0
        }
    }


    #########################
    set dcs [get_config_element DftControlSettings -in $pat]
    add_config_element  -in $dcs mac_scan_force_cg    -value 0
    add_config_element  -in $dcs pcs_scan_force_cg    -value 0
    add_config_element  -in $dcs phy0_scan_force_cg   -value 0
    add_config_element  -in $dcs ate_test_mode        -value 0
    add_config_element  -in $dcs phy0_scan_mode       -value 0
    add_config_element  -in $dcs pcs_scan_mode        -value 0
    add_config_element  -in $dcs mac_scan_mode        -value 1
    add_config_element  -in $dcs mac_scan_shift       -value 0
    add_config_element  -in $dcs phy0_scan_shift      -value 0
    add_config_element  -in $dcs pcs_scan_shift       -value 0
    add_config_element  -in $dcs phy0_scan_shift_cg   -value 0
    add_config_element  -in $dcs pcs_scan_shift_cg    -value 0
    add_config_element  -in $dcs mac_scan_shift_cg    -value 1
    add_config_element  -in $dcs phy_apb0_if_sel      -value 0 ;# allow jtag CR access


    #########################
    set ao [get_config_element AdvancedOptions -in $pat]
    set_config_value procfile_name             -in $ao ../../common/init.testproc
    set_config_value no_initialization         -in $ao on

    #########################
    set cp [get_config_element ClockPeriods -in $pat]
    add_config_element -in $cp ssn_bus_clk                    -value 10ns
    add_config_element -in $cp i_ref_clk                      -value 20ns
    add_config_element -in $cp i_pcie_init_mt_axi_clk         -value 10ns
    add_config_element -in $cp i_pcie_targ_mt_axi_clk         -value 10ns
    add_config_element -in $cp i_ref_alt_clk_p                -value 10ns
    add_config_element -in $cp i_ref_pad_clk_p                -value 10ns
    add_config_element -in $cp i_pcie_aux_clk                 -value 10ns
    add_config_element -in $cp i_pcie_targ_cfg_dbi_axi_clk    -value 10ns
    add_config_element -in $cp i_apb_pclk                     -value 10ns


    #########################



    read_config_data -in $pat -first -from_string "
        ProcedureStep($patn) {
            iCall($patn){
                iProcArguments {
                }
            }
        }
    "
    read_config_data -in $pat -first -from_string {
        ProcedureStep(ate_init) {
            run_before_dft_control_settings  : on;
            iCall(ate_init){
                iProcArguments {
                }
            }
        }
    }
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
}

############################################################
# ROM
# ROM is built using the normal image but for simulation the "fast" version is used
# Normal == /data/foundry/LIB/synopsys/pcie4/ip/phy/phy/firmware/dwc_c20pcie4_phy_x4_ns_pcs_raw_ref_100m_ext_rom.bin
# Fast   == /data/foundry/LIB/synopsys/pcie4/ip/phy/phy/firmware/dwc_c20pcie4_phy_x4_ns_pcs_raw_ref_100m_ext_rom.fastsim

#ONLY do this for simulation
if {[regexp "signoff" $patSpec]} {
    foreach_in_collection mbist_pat [get_config_element Patterns(MemoryBist*) -in $patSpec] {
        foreach_in_collection mc [get_config_element TestStep(*)/MemoryBist/Controller(*) -in $mbist_pat] {
            foreach_in_collection mi [get_config_elements MemoryInterface(*) -in $mc -silent] {
                if {[get_config_element  expected_rom_signature -in $mi -count]} {
                    set_config_value rom_content_file -in $mi /data/foundry/LIB/synopsys/pcie4/ip/phy/phy/firmware/dwc_c20pcie4_phy_x4_ns_pcs_raw_ref_100m_ext_rom.fastsim

                    #as the normal fw signature is part of the RTL the GO will fail
                    set_config_value compare_go -in [get_config_element DiagnosisOptions -in $mc] off

                }
            }
        }
    }
}

#############################################################

report_config_data $patSpec
process_patterns_specification

exit
