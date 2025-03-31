# Settings
set DESIGN            snps_ddr_subsystem
set DESIGN_ID         rtl1
set BLACKBOXES        {  }

set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}
read_cell_library /data/foundry/samsung/sf5a/ip/samsung/io/gpio_1p8v/v2.16/FE-Common/ATPG/FastScan/ln05lpe_gpio_lib_t18.mdt
#read_cell_library /home/projects_2/workspace/fkih/europa_lpddr/hw/impl/europa/blocks/lpddr/dft/libcomp.atpglib
#read_cell_library /home/projects_2/workspace/fkih/europa_lpddr/hw/impl/europa/blocks/lpddr/dft/dwc_lpddr5xphy_txbecs/libcomp.atpglib
#read_cell_library /home/projects_2/workspace/fkih/europa_lpddr4/hw/impl/europa/blocks/lpddr/dft/dwc_lpddr5xphy_txbecs/test.libcomp



read_core_descriptions ${GIT_ROOT}/hw/impl/europa/blocks/lpddr/dft/stil2tessent/dwc_lpddr5xphyacx2_top_ew.tcd_scan
read_core_descriptions ${GIT_ROOT}/hw/impl/europa/blocks/lpddr/dft/stil2tessent/dwc_lpddr5xphyckx2_top_ew.tcd_scan
read_core_descriptions ${GIT_ROOT}/hw/impl/europa/blocks/lpddr/dft/stil2tessent/dwc_lpddr5xphycmosx2_top_ew.tcd_scan
read_core_descriptions ${GIT_ROOT}/hw/impl/europa/blocks/lpddr/dft/stil2tessent/dwc_lpddr5xphycsx2_top_ew.tcd_scan
read_core_descriptions ${GIT_ROOT}/hw/impl/europa/blocks/lpddr/dft/stil2tessent/dwc_lpddr5xphydx4_top_ew.tcd_scan
read_core_descriptions ${GIT_ROOT}/hw/impl/europa/blocks/lpddr/dft/stil2tessent/dwc_lpddr5xphydx5_top_ew.tcd_scan
read_core_descriptions ${GIT_ROOT}/hw/impl/europa/blocks/lpddr/dft/stil2tessent/dwc_lpddr5xphymaster_top_ew.tcd_scan
read_core_descriptions ${GIT_ROOT}/hw/impl/europa/blocks/lpddr/dft/stil2tessent/dwc_lpddr5xphyzcal_top_ew.tcd_scan

# Mem lib
read_mem_libs
#set_read_verilog_options -vcs_compatibility  on

##Warning do not read this during other steps as it will hide information.
read_cell_library ../../libcomp/dwc_lpddr5xphy_top.atpglib

dofile ${DEPENDENCIES_DIR}/read_rtl.do

read_icl /home/projects_2/workspace/fkih/europa_lpddr4/hw/impl/europa/blocks/lpddr/dft/insertion/logic_test/dwc_ddrphy_jtag_dfttdrs.icl
read_icl  /home/projects_2/workspace/fkih/europa_lpddr4/hw/impl/europa/blocks/lpddr/dft/insertion/logic_test/lpddr_p_snps_ddr_subsystem.icl


read_verilog /data/foundry/LIB/synopsys/lpddr5x/v_roel/Europa_lpddr_phy_config/dx4_ew/0.50a/behavior/dwc_lpddr5xphy_rtl_syn_stdlib.v
read_verilog /data/foundry/LIB/synopsys/lpddr5x/v_roel/Europa_lpddr_phy_config/dx4_ew/0.50a/behavior/dwc_lpddr5xphy_cdc_syn_stdlib.v

set_current_design ${DESIGN}
set_design_level sub_block
add_black_boxes -auto
if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
}

add_clock 0 pclk -period 1ns
add_clock 0 pclk_apbrw -period 1ns
add_clock 0 aclk_0 -period 1ns
add_clock 0 core_ddrc_core_clk -period 1ns
add_clock 0 core_ddrc_core_clk_apbrw -period 1ns
add_clock 0 DfiClk -period 1ns
add_clock 0 sbr_clk -period 1ns

add_clock 1  presetn 
add_clock 1  aresetn_0 
add_clock 1  core_ddrc_rstn
add_clock 1  sbr_resetn


add_clocks i_DWC_lpddr5x_phy/iccm0_bank0_clk -period 1ns
add_clocks i_DWC_lpddr5x_phy/iccm0_bank1_clk -period 1ns
add_clocks i_DWC_lpddr5x_phy/gs_ram0_clk -period 1ns
add_clocks i_DWC_lpddr5x_phy/gs_ram1_clk -period 1ns
add_clocks i_DWC_lpddr5x_phy/clk_dccm_bank0_lo -period 1ns
add_clocks i_DWC_lpddr5x_phy/clk_dccm_bank0_hi -period 1ns
add_clocks i_DWC_lpddr5x_phy/clk_dccm_bank1_lo -period 1ns
add_clocks i_DWC_lpddr5x_phy/clk_dccm_bank1_hi -period 1ns
add_clocks i_DWC_lpddr5x_phy/bc_ram0_clk -period 1ns
add_clocks i_DWC_lpddr5x_phy/bc_ram1_clk -period 1ns

add_clocks i_DWC_lpddr5x_phy/pie_data_clk -period 1ns
add_clocks i_DWC_lpddr5x_phy/acsm_data_clk -period 1ns

add_dft_signals shift_capture_clock -source_nodes pclk
add_dft_signals scan_en    -source_nodes scan_en
add_dft_signals ltest_en   -source_nodes ltest_en -make_ijtag_port

add_dft_signals async_set_reset_static_disable -create_with_tdr
add_dft_signals async_set_reset_dynamic_disable -create_from_other_signals
    # DFT Signal used for Scan Tested network to be tested during logic test
    add_dft_signals tck_occ_en 

#register_static_dft_signal_names static_clock_control_mode -reset_value 0
#add_dft_signals static_clock_control_mode -create_with_tdr

report_memory_instances -limit 128

set_dft_specification_requirements -memory_test on \
                                   -boundary_scan on 
####################
## BSCAN 
#This order is extracted from the bump map, if that changes then so should this
set_boundary_scan_port_options -pad_io_ports [get_ports {BP_B3_D[0] BP_B3_D[1] BP_B3_D[2] BP_B3_D[3] BP_B3_D[9] BP_B3_D[8] BP_B3_D[10] BP_B3_D[11] BP_B3_D[12] BP_B3_D[7] BP_B3_D[5] BP_B3_D[6] BP_B3_D[4] BP_B2_D[0] BP_B2_D[1] BP_B2_D[2] BP_B2_D[3] BP_B2_D[9] BP_B2_D[8] BP_B2_D[10] BP_B2_D[12] BP_B2_D[11] BP_B2_D[6] BP_B2_D[7] BP_B2_D[4] BP_B2_D[5] BP_A[18] BP_A[19] BP_A[16] BP_A[17] BP_A[12] BP_A[13] BP_A[10] BP_A[11] BP_CK1_T BP_CK1_C BP_A[14] BP_A[15] BP_A[4] BP_MEMRESET_L BP_A[5] BP_CK0_C BP_CK0_T BP_A[0] BP_A[1] BP_A[3] BP_A[2] BP_A[6] BP_A[7] BP_A[9] BP_A[8] BP_B0_D[5] BP_B0_D[4] BP_B0_D[6] BP_B0_D[7] BP_B0_D[12] BP_B0_D[11] BP_B0_D[10] BP_B0_D[8] BP_B0_D[9] BP_B0_D[2] BP_B0_D[3] BP_B0_D[0] BP_B0_D[1] BP_B1_D[4] BP_B1_D[5] BP_B1_D[6] BP_B1_D[12] BP_B1_D[7] BP_B1_D[11] BP_B1_D[10] BP_B1_D[9] BP_B1_D[8] BP_B1_D[3] BP_B1_D[2] BP_B1_D[1] BP_B1_D[0] }]
##
####################


set_insertion_options -edited_module_prefix ${DESIGN} -edited_file_prefix ${DESIGN}

if { [file exists ${DESIGN}.def ] } {
  read_def ${DESIGN}.def
}

add_config_tdr

####Add some DFT control signals 
##set phy_top [get_instance -of_module [get_module dwc_lpddr5xphy_top]]
##foreach name [list \
##                 ] {
##    register_static_dft_signal_names $name -reset_value 0
##    add_dft_signals $name -create_with_tdr
##    add_dft_control_points [get_pin $pin_regex -of_inst $phy_top] -dft_signal_source_name $name
##}


set_system_mode analysis

if { [file exists dftSpec.${DESIGN}.${DESIGN_ID}.memory_test]} {
  puts "Sourcing DFT Specification file"
  read_config_data dftSpec.${DESIGN}.${DESIGN_ID}.memory_test
  set dftSpec /DftSpecification(${DESIGN},${DESIGN_ID})
} else {
  puts "WARNING: Using default DFT Specification"
  set dftSpec [create_dft_specification]
  write_config_data dftSpec.${DESIGN}.${DESIGN_ID}.memory_test -wrappers $dftSpec -original_hierarchy -no_banner
}


####################
## BSCAN 
#PUB databook  9.8.2.1 Selecting VREF Source
#
#The output of each receiver is sent out in RxBypassDataRcv_* pin of the PHY and it is expected to be
#captured through boundary scan or shifted in to a TDR outside the PHY for observability
set phy_top [get_instance -of_module [get_module dwc_lpddr5xphy_top]]
set sri [get_config_element sib(sri) -in $dftSpec -hier]

foreach {name pin_regexs} [list rx_data_rcv [list \
                                                 RxBypassDataRcv_A* \
                                                 RxBypassDataRcv_B* \
                                                 RxBypassDataRcv_CK*
                                                ] \
                             ] {
    set sib [add_config_element sib($name)   -in $sri]
    set tdr [add_config_element Tdr($name)   -in $sib]
    set inp [add_config_element DataInPorts  -in $tdr]
    set i 0
    foreach pin_regex $pin_regexs {
        foreach_in_collection pin [get_pins $pin_regex  -of_inst $phy_top] {
            add_config_element connection($i) -in $inp -value [get_name $pin]
            incr i            
        }
    }
}

foreach {name pin_regex} [list \
                              tx_mode                  TxBypassMode_* \
                              rx_pad_en                RxBypassPadEn_* \
                              rx_rcv_en                RxBypassRcvEn_* \
                             ] {
    set sib [add_config_element Sib($name) -in $sri]
    set tdr [add_config_element Tdr($name) -in $sib]
    set_config_value extra_bits_capture_value -in $tdr self
    set oup [add_config_element DataOutPorts -in $tdr]
    set i 0
    foreach_in_collection pin [get_pins $pin_regex  -of_inst $phy_top] {
        add_config_element connection($i) -in $oup -value [get_name $pin]
        incr i            
    }  
}


##
#####################################

proc process_dft_specification.post_insertion {[get_current_design] args} {

  global DESIGN
  global DESIGN_ID

  create_instance -of_module axe_tcl_std_inverter inst_core_ddrc_rstn_scan_inverter
  create_connection core_ddrc_rstn inst_core_ddrc_rstn_scan_inverter/i_a 
  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable
  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_async_set_reset_dynamic_enable inst_core_ddrc_rstn_scan_inverter/o_z 

  ##Use dedicated TDR to give flexibility
##  delete_connections ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_static_clock_control_mode
##  create_connection ${DESIGN}_${DESIGN_ID}_tessent_sib_sti_inst/ltest_static_clock_control_mode [get_dft_signal static_clock_control_mode]

  set N_icg_se [sizeof_collection [get_pins -hierarchical tessent_persistent_cell_GATING_BIST_CLK/i_test_en]]
  set icg_se_pins  [get_pins -hierarchical tessent_persistent_cell_GATING_BIST_CLK/i_test_en]
  foreach_in_collection pin $icg_se_pins {
      echo [get_name_list $pin] >> rpt/icg_se_pins.rpt
  }
  for {set i 0} {$i < $N_icg_se} {incr i} { 
  delete_connections [get_name_list [index_collection $icg_se_pins $i]]
  create_connection [get_name_list [index_collection $icg_se_pins $i]] scan_mode
  
  }
  
  set phy_top [get_instance -of_module [get_module dwc_lpddr5xphy_top]]
  foreach port [list scan_UcClk scan_ucclk_mode ] {
      create_port $port 
      set pin [get_pins $port  -of_inst $phy_top] 
  
      delete_connection $pin
      create_connection $port $pin
  }

#Manually fixing floating clock gate enables
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm0[0].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm0[1].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm0[2].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm0[3].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm1[0].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm1[1].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm1[2].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm1[3].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm2[0].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm2[1].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm2[2].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm2[3].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm3[0].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm3[1].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm3[2].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm3[3].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm0[0].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm0[1].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm0[2].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm0[3].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm1[0].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm1[1].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm1[2].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm1[3].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3
delete_connection i_DWC_ddrphy_mem_wrap/genblock_acsm[0].i_acsm_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x72m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_acsm[1].i_acsm_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x72m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm0[0].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm0[1].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm0[2].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm0[3].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm1[0].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm1[1].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm1[2].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm1[3].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm2[0].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm2[1].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm2[2].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm2[3].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm3[0].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm3[1].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm3[2].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_dccm3[3].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm0[0].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm0[1].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm0[2].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm0[3].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm1[0].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm1[1].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm1[2].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_iccm1[3].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_pie0[0].i_pie_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x56m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
delete_connection i_DWC_ddrphy_mem_wrap/genblock_pie0[1].i_pie_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x56m4b4c1r2_wrapper_interface_inst/scan_mode_ts1

create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm0[0].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm0[1].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm0[2].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm0[3].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm1[0].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm1[1].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm1[2].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm1[3].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm2[0].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm2[1].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm2[2].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm2[3].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm3[0].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm3[1].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm3[2].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm3[3].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm0[0].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm0[1].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm0[2].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm0[3].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm1[0].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm1[1].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm1[2].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm1[3].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts3
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_acsm[0].i_acsm_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x72m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_acsm[1].i_acsm_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x72m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm0[0].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm0[1].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm0[2].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm0[3].i_dccm0_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm1[0].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm1[1].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm1[2].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm1[3].i_dccm1_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm2[0].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm2[1].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm2[2].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm2[3].i_dccm2_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm3[0].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm3[1].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm3[2].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_dccm3[3].i_dccm3_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm0[0].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm0[1].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm0[2].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm0[3].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm1[0].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm1[1].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm1[2].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_iccm1[3].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_pie0[0].i_pie_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x56m4b4c1r2_wrapper_interface_inst/scan_mode_ts1 
create_connection i_DWC_ddrphy_mem_wrap/scan_mode i_DWC_ddrphy_mem_wrap/genblock_pie0[1].i_pie_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x56m4b4c1r2_wrapper_interface_inst/scan_mode_ts1

 
}

report_config_data $dftSpec
process_dft_specification

# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst


extract_icl

set patSpec [create_patterns_specification]

source ./bscan.pdl
set bscan_pat [get_config_element Patterns(JtagBscanPatterns) -in $patSpec]
set ao        [get_config_element AdvancedOptions -in $bscan_pat]
set cps       [get_config_element ConstantPortSettings -in $ao]
add_config_element -in $cps Iddq_mode        -value 0
add_config_element -in $cps BurnIn           -value 0
add_config_element -in $cps scan_mode        -value 1 
add_config_element -in $cps BP_PWROK         -value 1
add_config_element -in $cps scan_shift_cg    -value 0
add_config_element -in $cps scan_asst_mode   -value 0
add_config_element -in $cps scan_occ_bypass  -value 0
add_config_element -in $cps scan_shift_async -value 0
read_config_data -in $bscan_pat -first -from_string {
    ProcedureStep(init) {
        iCall(enable_bscan){
            iProcArguments {
            }
        } 
    }
}
##very first thing to be called.  To set the simulation power pins
read_config_data -in $bscan_pat -first -from_string {
    ProcedureStep(sim_init) {
        run_before_dft_control_settings : on;
        iCall(simulation_only_init){
            iProcArguments {
            }
        } 
    }
}
#####
source ./mbist.pdl
set orig_mbist_pat [get_config_element Patterns(MemoryBist_P1) -in $patSpec]
set mbist_pat [add_config_element Patterns(MemoryBist_P1_lowV) -in $patSpec -copy_from $orig_mbist_pat]
set ao        [get_config_element AdvancedOptions -in $mbist_pat]
set cps       [get_config_element ConstantPortSettings -in $ao]
add_config_element -in $cps Iddq_mode        -value 0
add_config_element -in $cps BurnIn           -value 0
add_config_element -in $cps scan_mode        -value 0
add_config_element -in $cps scan_shift_cg    -value 0
add_config_element -in $cps scan_asst_mode   -value 0
add_config_element -in $cps scan_occ_bypass  -value 0
add_config_element -in $cps scan_shift_async -value 0

add_config_element -in $cps BP_PWROK         -value 1


set dcs       [get_config_element DftControlSettings -in $mbist_pat]

add_config_element -in $dcs adme_control0_ra1_hs   -value 1
add_config_element -in $dcs adme_control0_rf1_hs   -value 1
add_config_element -in $dcs adme_control0_rf2_hs   -value 1
add_config_element -in $dcs adme_control1_ra1_hs   -value 1
add_config_element -in $dcs adme_control1_rf1_hs   -value 1
add_config_element -in $dcs adme_control1_rf2_hs   -value 1
add_config_element -in $dcs adme_control2_ra1_hs   -value 1
add_config_element -in $dcs adme_control2_rf1_hs   -value 1
add_config_element -in $dcs adme_control2_rf2_hs   -value 1
add_config_element -in $dcs kcs_control0_rf2_hs    -value 1
add_config_element -in $dcs mcs_control0_ra1_hs    -value 1
add_config_element -in $dcs mcs_control0_rf1_hs    -value 1
add_config_element -in $dcs mcs_control1_ra1_hs    -value 1
add_config_element -in $dcs mcs_control1_rf1_hs    -value 1
add_config_element -in $dcs mcsrd_control0_rf2_hs  -value 1
add_config_element -in $dcs mcsrd_control1_rf2_hs  -value 1
add_config_element -in $dcs mcsw_control0_ra1_hs   -value 1
add_config_element -in $dcs mcsw_control0_rf1_hs   -value 1
add_config_element -in $dcs mcswr_control0_rf2_hs  -value 1
add_config_element -in $dcs mcswr_control1_rf2_hs  -value 1


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
