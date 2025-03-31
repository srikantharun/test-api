# Settings
set DESIGN            DWC_pcie_subsystem
set DESIGN_ID         rtl1
set BLACKBOXES        {  }

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
read_mem_libs


set_design_sources \
    -V /data/foundry/LIB/synopsys/pcie4/ip/phy/phy/include/dwc_c20pcie4_phy_x4_ns_macros.v \
    -V /data/foundry/LIB/synopsys/pcie4/ip/phy/phy/include/dwc_c20pcie4_phy_x4_ns_pcs_raw_macros.v \
    -V /data/foundry/LIB/synopsys/pcie4/ip/phy/upcs/include/dwc_c20pcie4_upcs_x4_ns_pipe_defines.v

set_design_macros DWC_C20PCIE4_X4NS_PCS_DTB_SUPPORT
dofile ${DEPENDENCIES_DIR}/read_rtl.do

read_icl ./../../icl/dwc_c20pcie4_upcs_x4_ns_x4_x4_pipe.icl
read_core_description ../../tcd/dwc_c20pcie4_upcs_x4_ns_x4_x4_pipe.tcd_bscan
read_verilog /data/foundry/LIB/synopsys/pcie4/ip/phy/macro/interface/dwc_c20pcie4_upcs_x4_ns_x4_x4_pipe_interface.v

set_current_design ${DESIGN}
set_design_level sub_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}
add_black_boxes -auto


add_input_constraint -equivalent ref_pad_clk_p -invert ref_pad_clk_m
add_clock ref_pad_clk_p -period 10ns -label ref_clk

add_clock 0 apb_pclk   -period 10ns
add_clock 0 mstr_aclk  -period 1.67ns
add_clock 0 slv_aclk   -period 1.67ns
add_clock 0 dbi_aclk   -period 10ns

add_clock 0 phy_fw_clk -period 10ns
add_clock 0 aux_clk    -period 10ns


add_clock 1 apb_presetn
add_clock 1 power_up_rst_n
add_clock 1 perst_n


set phy_core_period 1
                                                                              ; # at  shift sa
add_clocks mac_scan_coreclk         -period  "${phy_core_period}ns"           ; #
add_clocks pcs_scan_clk             -period  "${phy_core_period}ns"           ; #
add_clocks pcs_scan_pclk            -period  "${phy_core_period}ns"           ; #
add_clocks pcs_scan_pcs_clk         -period  "${phy_core_period}ns"           ; #
add_clocks pcs_scan_pma_clk         -period  "${phy_core_period}ns"           ; #
add_clocks phy0_scan_mpll_dword_clk -period  "[expr ${phy_core_period} * 2]ns"; #
add_clocks phy0_scan_mpll_qword_clk -period  "[expr ${phy_core_period} * 4]ns"; #
add_clocks phy0_scan_rx_dword_clk   -period  "${phy_core_period}ns"           ; #
add_clocks phy0_scan_clk            -period  10ns                             ; # na  200   100
add_clocks phy0_scan_cr_clk         -period  10ns                             ; # 400 200   100
add_clocks phy0_scan_occ_clk        -period  10ns                             ; # na  200   100
add_clocks phy0_scan_ref_clk        -period  10ns                             ; # 200 200   100

add_clocks u_pcie_phy_top/u_pcie_pipe/phy0_sram_clk -period 10ns
add_clocks u_pcie_phy_top/u_pcie_pipe/phy0_rom_clk  -period 10ns

add_clock 1 pcs_scan_rst
add_clock 1 phy0_scan_set_rst
add_clock 1 mac_scan_rst_n

add_dft_signals ltest_en  -source_nodes ltest_en -make_ijtag_port
add_dft_signals shift_capture_clock -source_nodes ltest_clk


report_memory_instances -limit 128

set_dft_specification_requirements -memory_test on -boundary_scan on

set_boundary_scan_port_options -pad_io_ports [get_ports {rxp rxm txp txm}]

set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN} -open_input_pins tie0

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

#needed to propagate the clocks
foreach {name val } [list \
                         mac_scan_shift_cg       1 \
                         mac_scan_mode           1 \
                        ] {
    add_input_constraints $name -c${val}
}


add_config_tdr

set_system_mode analysis


set dftSpec [create_dft_specification]

##to be able to control the phy during BIST tests and debug without
## needing to program through APB
set pipe_overrides [list \
                        1   phy_reset                      pipe_cfg0  \
                        1   upcs_pwr_stable                pipe_cfg0  \
                        1   phy0_ana_pwr_en                pipe_cfg0  \
                        1   phy0_pma_pwr_stable            pipe_cfg0  \
                        1   phy0_pcs_pwr_stable            pipe_cfg0  \
                        1   pg_mode_en                     pipe_cfg0  \
                        1   ext_pclk_req                   pipe_cfg0  \
                        1   phy0_ref_use_pad               pipe_cfg0  \
                        1   phy0_ref_alt_clk_lp_sel        pipe_cfg0  \
                        2   phy0_sram_bypass_mode          pipe_cfg0  \
                        2   phy0_sram_bootload_bypass_mode pipe_cfg0  \
                        1   phy0_sram_ext_ld_done          pipe_cfg0  \
                        1   phy0_fw_clk_ack                pipe_cfg0  \
                        1   phy0_mplla_force_en            pipe_cfg0  \
                        1   phy0_mplla_ssc_en              pipe_cfg0  \
                        1   phy0_mpllb_force_en            pipe_cfg0  \
                        1   phy0_mpllb_ssc_en              pipe_cfg0  \
                        32  upcs_pipe_config               pipe_cfg0  \
                        1   phy_ext_ref_ovrd_sel           pipe_cfg1  \
                        1   protocol0_ext_ref_clk_div2_en  pipe_cfg1  \
                        3   protocol0_ext_ref_range        pipe_cfg1  \
                        24  protocol0_ext_tx_eq_main_g1    pipe_cfg1  \
                        24  protocol0_ext_tx_eq_main_g2    pipe_cfg1  \
                        24  protocol0_ext_tx_eq_main_g3    pipe_cfg1  \
                        24  protocol0_ext_tx_eq_main_g4    pipe_cfg1  \
                        4   protocol0_ext_tx_eq_ovrd_g1    pipe_cfg1  \
                        4   protocol0_ext_tx_eq_ovrd_g2    pipe_cfg1  \
                        4   protocol0_ext_tx_eq_ovrd_g3    pipe_cfg1  \
                        4   protocol0_ext_tx_eq_ovrd_g4    pipe_cfg1  \
                        24  protocol0_ext_tx_eq_post_g1    pipe_cfg1  \
                        24  protocol0_ext_tx_eq_post_g2    pipe_cfg1  \
                        24  protocol0_ext_tx_eq_post_g3    pipe_cfg1  \
                        24  protocol0_ext_tx_eq_post_g4    pipe_cfg1  \
                        24  protocol0_ext_tx_eq_pre_g1     pipe_cfg1  \
                        24  protocol0_ext_tx_eq_pre_g2     pipe_cfg1  \
                        24  protocol0_ext_tx_eq_pre_g3     pipe_cfg1  \
                        24  protocol0_ext_tx_eq_pre_g4     pipe_cfg1  \
                        1   protocol1_ext_ref_clk_div2_en  pipe_cfg1  \
                        3   protocol1_ext_ref_range        pipe_cfg1  \
                        24  protocol1_ext_tx_eq_main_g1    pipe_cfg1  \
                        24  protocol1_ext_tx_eq_main_g2    pipe_cfg1  \
                        4   protocol1_ext_tx_eq_ovrd_g1    pipe_cfg1  \
                        4   protocol1_ext_tx_eq_ovrd_g2    pipe_cfg1  \
                        24  protocol1_ext_tx_eq_post_g1    pipe_cfg1  \
                        24  protocol1_ext_tx_eq_post_g2    pipe_cfg1  \
                        24  protocol1_ext_tx_eq_pre_g1     pipe_cfg1  \
                        24  protocol1_ext_tx_eq_pre_g2     pipe_cfg1  \
                        1   protocol2_ext_ref_clk_div2_en  pipe_cfg1  \
                        3   protocol2_ext_ref_range        pipe_cfg1  \
                        24  protocol2_ext_tx_eq_main_g1    pipe_cfg1  \
                        24  protocol2_ext_tx_eq_main_g2    pipe_cfg1  \
                        24  protocol2_ext_tx_eq_main_g3    pipe_cfg1  \
                        4   protocol2_ext_tx_eq_ovrd_g1    pipe_cfg1  \
                        4   protocol2_ext_tx_eq_ovrd_g2    pipe_cfg1  \
                        4   protocol2_ext_tx_eq_ovrd_g3    pipe_cfg1  \
                        24  protocol2_ext_tx_eq_post_g1    pipe_cfg1  \
                        24  protocol2_ext_tx_eq_post_g2    pipe_cfg1  \
                        24  protocol2_ext_tx_eq_post_g3    pipe_cfg1  \
                        24  protocol2_ext_tx_eq_pre_g1     pipe_cfg1  \
                        24  protocol2_ext_tx_eq_pre_g2     pipe_cfg1  \
                        24  protocol2_ext_tx_eq_pre_g3     pipe_cfg1  \
                        1   protocol3_ext_ref_clk_div2_en  pipe_cfg1  \
                        3   protocol3_ext_ref_range        pipe_cfg1  \
                        1   protocol7_ext_ref_clk_div2_en  pipe_cfg1  \
                        3   protocol7_ext_ref_range        pipe_cfg1  \
                        1   protocol9_ext_ref_clk_div2_en  pipe_cfg1  \
                        3   protocol9_ext_ref_range        pipe_cfg1  \
                        1   pipe_lane0_reset_n             pipe_cfg2  \
                        1   pipe_lane1_reset_n             pipe_cfg2  \
                        1   pipe_lane2_reset_n             pipe_cfg2  \
                        1   pipe_lane3_reset_n             pipe_cfg2  \
                        4   pipe_lane0_powerdown           pipe_cfg2  \
                        4   pipe_lane1_powerdown           pipe_cfg2  \
                        4   pipe_lane2_powerdown           pipe_cfg2  \
                        4   pipe_lane3_powerdown           pipe_cfg2  \
                        4   pipe_lane0_protocol            pipe_cfg2  \
                        4   pipe_lane1_protocol            pipe_cfg2  \
                        4   pipe_lane2_protocol            pipe_cfg2  \
                        4   pipe_lane3_protocol            pipe_cfg2  \
                        2   pipe_lane0_phy_src_sel         pipe_cfg2  \
                        2   pipe_lane1_phy_src_sel         pipe_cfg2  \
                        2   pipe_lane2_phy_src_sel         pipe_cfg2  \
                        2   pipe_lane3_phy_src_sel         pipe_cfg2  \
                       ]

set sri [get_config_element sib(sri) -in $dftSpec -hier]

set pn ""
foreach {sz po tdr} $pipe_overrides {

    if {[get_config_element Sib($tdr) -in $sri -count ]==0} {

        #execute if the loop has completed
        if {[string length $pn]} {
            set pn "mux_sel${pn}"
            set_config_value port_naming -in $oup $pn
        }

        set sib [add_config_element Sib($tdr) -in $sri]
        set tdr [add_config_element Tdr($tdr) -in $sib]
        set_config_value extra_bits_capture_value -in $tdr self
        set oup [add_config_element DataOutPorts -in $tdr]
        set i 0
        set pn ""
    }
    if {$sz == 1} {
        set idx $i
        set pn " ${po}${pn}"
    } else {
        set idx "[expr $i+$sz-1]:$i"
        set pn " ${po}\[[expr $sz-1]:0\]${pn}"
    }



    add_config_element connection($idx) -in $oup -value u_pcie_phy_top/u_pcie_pipe/$po
    incr i $sz
}
#execute if the loop has completed
if {[string length $pn]} {
    set pn "mux_sel${pn}"
    set_config_value port_naming -in $oup $pn
}

## do the inputs WARNING, this code is not general as it currently doesn't need to be.

set pipe_inputs     [ list \
                         1 phy0_fw_clk_req      pipe_cfg0   \
                         1 phy0_sram_init_done  pipe_cfg0   \
                         ]

set pn ""
set i 0
foreach {sz po tdr} $pipe_inputs {

    set sib [get_config_element Sib($tdr) -in $sri]
    set tdr [get_config_element Tdr($tdr) -in $sib]
    set inp [add_config_element DataInPorts -in $tdr]
    set idx $i
    set pn " ${po}${pn}"
    add_config_element connection($idx) -in $inp -value u_pcie_phy_top/u_pcie_pipe/$po
    incr i $sz
}
set_config_value port_naming -in $inp $pn
#################################


foreach_in_collection i [get_config_element Sib(*) -in $dftSpec -hier] {
    set_config_value  parent_instance -in $i .
}
foreach_in_collection i [get_config_element tdr(*) -in $dftSpec -hier] {
    set_config_value  parent_instance -in $i .
}

set_config_value [get_name [get_config_element rom_content_file -in $dftSpec -hier]] "/data/foundry/LIB/synopsys/pcie4/ip/phy/phy/firmware/dwc_c20pcie4_phy_x4_ns_pcs_raw_ref_100m_ext_rom.bin"

proc process_dft_specification.post_insertion {[get_current_design] args} {

  global DESIGN
  global DESIGN_ID

  puts "post processing script to connect scan control pins"

  create_instance -of_module axe_tcl_std_inverter inst_apb_presetn_scan_inverter
  create_connection apb_presetn inst_apb_presetn_scan_inverter/i_a 

  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable
  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable inst_apb_presetn_scan_inverter/o_z 

  echo "" > rpt/icg_se_pins.rpt
  set icg_se_pins [get_pins -hierarchical tessent_persistent_cell_GATING_BIST_CLK/i_test_en]
  foreach_in_collection pin $icg_se_pins {
      echo [get_name_list $pin] >> rpt/icg_se_pins.rpt
      delete_connection [get_name_list $pin]
      create_connection [get_name_list $pin] phy0_scan_shift ;# CHECKME is this the correct scan-enable?
  }

  #There is a mux and inverted which is preventing ICL extraction
  delete_connection u_pcie_phy_top/u_pcie_pipe/phy0_jtag_trst_n
  create_connection u_pcie_phy_top/u_pcie_pipe/phy0_jtag_trst_n  phy0_jtag_trst_n


  # I need these clocks to be able to reuse the internal PLL
  set missing_clock_outputs [list \
                                 phy0_ref_dig_fr_clk     \
                                 phy0_mplla_word_fr_clk  \
                                 ]
  foreach pin $missing_clock_outputs {
      create_port $pin -direction output
      delete_connection u_pcie_phy_top/$pin
      create_connection u_pcie_phy_top/u_pcie_pipe/$pin $pin
  }






}

report_config_data $dftSpec
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst
write_librarymap ./tsdb_outdir/library_files.lst


add_icl_scan_interfaces {PHY_CSR}
set_icl_scan_interface_ports -name PHY_CSR -ports {phy0_jtag_tck phy0_jtag_tdi phy0_jtag_tdo phy0_jtag_tms phy0_jtag_trst_n}

extract_icl

set patSpec [create_patterns_specification]

#done at next level up
delete_config_element [get_config_element Patterns(MemoryBis*) -in $patSpec]
delete_config_element [get_config_element Patterns(ICLNetwork*) -in $patSpec]

#for bscan to operate bs_ce_pin must be high
set bscan_pat [get_config_element Patterns(JtagBscanPatterns) -in $patSpec]
set ao        [get_config_element AdvancedOptions -in $bscan_pat]
set cps       [get_config_element ConstantPortSettings -in $ao]
add_config_element -in $cps phy_bs_ce          -value 1
add_config_element -in $cps phy_bs_tx_lowswing -value 0
add_config_element -in $cps phy_bs_rx_bigswing -value 0
add_config_element -in $cps {phy_bs_rx_level[0]} -value 1
add_config_element -in $cps {phy_bs_rx_level[1]} -value 0
add_config_element -in $cps {phy_bs_rx_level[2]} -value 1
add_config_element -in $cps {phy_bs_rx_level[3]} -value 0
add_config_element -in $cps {phy_bs_rx_level[4]} -value 0

##rename all the patterns as this is not following the correct process
set orig_pats [get_config_element Patterns(*) -in $patSpec]
foreach_in_collection pat $orig_pats {
    set name [get_attribute_value $pat -name leaf_name]
    regexp "Patterns\\((.*)\\)" $name -> name
    set new_name ${DESIGN}_${name}
    add_config_element Patterns(${new_name}) -in $patSpec -copy_from $pat
}
delete_config_element $orig_pats


report_config_data $patSpec
process_patterns_specification

exit
