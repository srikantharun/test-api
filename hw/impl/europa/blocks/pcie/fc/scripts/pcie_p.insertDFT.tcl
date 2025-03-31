##########################################################################################
# Script: insert_scan.tcl
#
# Description: 
# Owner:        <axelera.ai>
#
##########################################################################################

puts "AX-DFT-info: Sourcing scan insertion script dft_script.tcl ..."

source /data/europa/pd/europa/project_setup/dev/memory_macros.tcl

global AXVAR_MACRO_LIST AXVAR_MACRO_DIR

set macro_list_ctl ""

foreach macro $AXVAR_MACRO_LIST {
    set macro_dir [lindex [array get AXVAR_MACRO_DIR $macro] 1]
    append macro_list_ctl "$macro_dir/$macro "

}

set_scan_configuration -internal_clocks multi
set_scan_configuration -clock_mixing mix_clocks
set_app_options -name dft.scan.enable_general_multimode_support -value true
set_app_options -name dft.test_default_period -value 100
set_app_options -name dft.test_default_delay -value 0
set_app_options -name dft.test_default_strobe -value 40
set_dft_drc_configuration -internal_pins enable
set_dft_configuration -scan enable

set_dft_signal -type Reset     -active_state 0 -port i_ao_rst_n             -view spec
set_dft_signal -type Reset     -active_state 0 -port i_global_rst_n         -view spec

#define OCC clocks
foreach_in_collection pin [get_pins -hier *_tessent_occ_*/clock_out] {
    set pin_name [get_object_name $pin]
    set_dft_signal -type ScanClock  -hookup_pin $pin_name -timing {45 55}    -view exis
    set_dft_signal -type ScanClock  -hookup_pin $pin_name -timing {45 55}    -view spec
}
#debug
foreach_in_collection pin [get_pins -hierarchical *_ck_gt*/clk_out] {
    set pin_name [get_object_name $pin]
    set_dft_signal -type ScanClock  -hookup_pin $pin_name -timing {45 55}    -view exis
    set_dft_signal -type ScanClock  -hookup_pin $pin_name -timing {45 55}    -view spec
}
foreach_in_collection pin [get_pins -hierarchical *clk_gate*/clk_out] {
    set pin_name [get_object_name $pin]
    set_dft_signal -type ScanClock  -hookup_pin $pin_name -timing {45 55}    -view exis
    set_dft_signal -type ScanClock  -hookup_pin $pin_name -timing {45 55}    -view spec
}
#check if we still need this?
set_dft_signal -type Constant  -active_state 1 -hookup_pin u_pcie_subsys/DWC_pcie_subsystem_rtl1_tessent_sib_sti_inst/ltest_to_reset_reg/Q -view existing_dft
set_dft_signal -type Constant  -active_state 1 -hookup_pin u_pcie_subsys/DWC_pcie_subsystem_rtl1_tessent_sib_sti_inst/ltest_to_reset_reg/Q -view spec

# define ssn generated clock only as existing
set_dft_signal -type ScanClock  -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_scan_host_sh_inst/test_clock -timing {45 55}      -view exis

set_dft_signal -type ScanEnable  -view spec -hookup ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_scan_host_sh_inst/scan_en
set_dft_signal -type ScanEnable  -view exis -hookup ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_scan_host_sh_inst/scan_en

set_dft_signal -type ScanEnable  -view spec -hookup u_pcie_subsys/u_pcie_ctrl_top_0/phy0_scan_shift
set_dft_signal -type ScanEnable  -view exis -hookup u_pcie_subsys/u_pcie_ctrl_top_0/phy0_scan_shift

#set_dft_signal -type Constant  -active_state 1 -port test_mode     -view existing_dft

set_dft_signal -type Constant  -active_state 1 -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/all_test_latch_reg/Q   -view existing_dft
set_dft_signal -type Constant  -active_state 1 -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/all_test_latch_reg/Q   -view spec


set_dft_signal -type Constant  -active_state 0 -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/ate_test_mode_latch_reg/Q   -view existing_dft
set_dft_signal -type Constant  -active_state 1 -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/mac_scan_mode_latch_reg/Q   -view existing_dft
set_dft_signal -type Constant  -active_state 1 -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/pcs_scan_mode_latch_reg/Q   -view existing_dft
set_dft_signal -type Constant  -active_state 1 -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/phy0_scan_mode_latch_reg/Q   -view existing_dft
set_dft_signal -type Constant  -active_state 1 -hookup_pin pcie_p_rtl2_tessent_tdr_pcs_scan_clk_sel_inst/ijtag_data_out_0_latch_reg/Q   -view existing_dft

set_dft_signal -type Constant  -active_state 0 -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/ate_test_mode_latch_reg/Q   -view spec
set_dft_signal -type Constant  -active_state 1 -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/mac_scan_mode_latch_reg/Q   -view spec
set_dft_signal -type Constant  -active_state 1 -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/pcs_scan_mode_latch_reg/Q   -view spec
set_dft_signal -type Constant  -active_state 1 -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/phy0_scan_mode_latch_reg/Q   -view spec
set_dft_signal -type Constant  -active_state 1 -hookup_pin pcie_p_rtl2_tessent_tdr_pcs_scan_clk_sel_inst/ijtag_data_out_0_latch_reg/Q   -view spec

set_dft_signal -type TestMode  -active_state 1  -view exis -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/ltest_en
set_dft_signal -type TestMode  -active_state 1  -view spec -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/ltest_en

set_dft_signal -type TestMode  -active_state 1  -view exis -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/ltest_en_latch_reg/Q
set_dft_signal -type TestMode  -active_state 1  -view spec -hookup_pin pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/ltest_en_latch_reg/Q

set_dft_signal -type Constant  -active_state 0 -hookup ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_scan_host_sh_inst/edt_update    -view exist 

set_dft_signal -type Constant  -active_state 0  -view spec -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/async_set_reset_static_disable
#set_dft_signal -type Constant  -active_state 0  -view spec -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/control_test_point_en
#set_dft_signal -type Constant  -active_state 0  -view spec -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/observe_test_point_en

#config intest_mode
#set_dft_signal -type Constant  -active_state 1  -view spec -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/tessent_persistent_cell_int_mode/u_tc_lib_std_buf/Y

###
#set_dft_signal -type Constant  -active_state 1  -view exis -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/tessent_persistent_cell_int_ltest_en/u_tc_lib_std_buf/Y
#set_dft_signal -type Constant  -active_state 1  -view exis -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/tessent_persistent_cell_ext_ltest_en/u_tc_lib_std_buf/Y


foreach_in_collection pin [get_pins tessent_scan_buf_i_*/u_tc_lib_std_buf/Y] {
    set pin_name [get_object_name $pin] 
    set_dft_signal -type ScanDataIn  -hookup_pin  $pin_name -view spec
}

foreach_in_collection pin [get_pins tessent_scan_buf_o_*/u_tc_lib_std_buf/A] {
    set pin_name [get_object_name $pin] 
    set_dft_signal -type ScanDataOut  -hookup_pin  $pin_name -view spec
}


###################### OCC shiftReg
if {0} {
foreach_in_collection pin [get_pins tessent_occ_scan_buf_i_*/o_z] {
    set pin_name [get_object_name $pin] 
    set_dft_signal -type ScanDataIn  -hookup_pin  $pin_name -view spec 
}

foreach_in_collection pin [get_pins tessent_occ_scan_buf_o_*/i_a] {
    set pin_name [get_object_name $pin] 
    set_dft_signal -type ScanDataOut  -hookup_pin  $pin_name -view spec 
}

set occ_shift_regs [list ]
foreach_in_collection cell [get_cells -hier *occ_control/ShiftReg/FF_reg] {
    set cell_name [get_object_name $cell]
    lappend occ_shift_regs "$cell_name"
}

set_scan_path occ_chain  -complete true -include_elements $occ_shift_regs  \
    					-scan_data_in tessent_occ_scan_buf_i_0/o_z \
    					-scan_data_out tessent_occ_scan_buf_o_0/i_a

}
##################### handle wrapper cells
# define wrapper scan in/out
set wrp_scan_buf_i [list ]
foreach_in_collection pin [get_pins tessent_cx_scan_buf_i_*/u_tc_lib_std_buf/Y] {
    set pin_name [get_object_name $pin] 
    lappend wrp_scan_buf_i "$pin_name"
}

set wrp_scan_buf_o [list ]
#foreach_in_collection pin [get_pins ${AXVAR_DESIGN_NAME}_rtl2_tessent_edt_cx_inst/tessent_persistent_cell_edt_scan_out_*_buf/u_tc_lib_std_buf/A] {
foreach_in_collection pin [get_pins tessent_cx_scan_buf_o_*/u_tc_lib_std_buf/A] {
    set pin_name [get_object_name $pin] 
    lappend wrp_scan_buf_o "$pin_name"
}


for {set i 0} {$i < [llength $wrp_scan_buf_i]} {incr i} {
    set wrp_scan_in($i) [lindex $wrp_scan_buf_i $i]
}

for {set i 0} {$i < [llength $wrp_scan_buf_o]} {incr i} {
    set wrp_scan_out($i) [lindex $wrp_scan_buf_o $i]
}


for {set i 0} {$i < [llength $wrp_scan_buf_i]} {incr i} {
  #puts "set_dft_signal -type ScanDataIn  -hookup_pin  $wrp_scan_in($i) -view spec"   
  set_dft_signal -type ScanDataIn  -hookup_pin  $wrp_scan_in($i) -view spec    
}

for {set i 0} {$i < [llength $wrp_scan_buf_o]} {incr i} {
  #puts "set_dft_signal -type ScanDataOut  -hookup_pin  $wrp_scan_out($i) -view spec"   
  set_dft_signal -type ScanDataOut  -hookup_pin  $wrp_scan_out($i) -view spec      
}

set extest_ch_count [sizeof_collection [get_pins tessent_cx_scan_buf_o_*/u_tc_lib_std_buf/A]]

set num_sub_wrapper_chains_i [expr {$extest_ch_count / 2}]

# create list of output wrapper cells
set wrapper_cells_o [list ]
foreach_in_collection cell [get_cells tessent_persistent_cell_0_dohw_*/tessent_persistent_cell_dwc_dff] {
    set cell_name [get_object_name $cell]
    lappend wrapper_cells_o "$cell_name"
}


# create list of input wrapper cells
set wrapper_cells_i [list ]
foreach_in_collection cell [get_cells tessent_persistent_cell_0_dihw_*/tessent_persistent_cell_dwc_dff] {
    set cell_name [get_object_name $cell]
    lappend wrapper_cells_i "$cell_name"
}

# Initialize the sub-wrapper_cells_i as empty lists
for {set i 0} {$i < $num_sub_wrapper_chains_i} {incr i} {
    set sub_wrapper_cells_i($i) {}
    set sub_wrapper_cells_o($i) {}
}

# Get the size of the collection
set N [llength $wrapper_cells_i]

# Distribute the elements among sub-wrapper_cells_i
for {set i 0} {$i < $N} {incr i} {
    # Determine the target sub-collection index
    set target_index [expr {$i % $num_sub_wrapper_chains_i}]
    
    # Append the element to the target sub-collection
    lappend sub_wrapper_cells_i($target_index) [lindex $wrapper_cells_i $i]
}

# Get the size of the collection
set M [llength $wrapper_cells_o]

# Distribute the elements among sub-wrapper_cells_i
for {set i 0} {$i < $M} {incr i} {
    # Determine the target sub-collection index
    set target_index [expr {$i % $num_sub_wrapper_chains_i}]
    
    # Append the element to the target sub-collection
    lappend sub_wrapper_cells_o($target_index) [lindex $wrapper_cells_o $i]
}

for {set i 0; set j $num_sub_wrapper_chains_i } {$i < $num_sub_wrapper_chains_i && $j < $extest_ch_count} {incr i; incr j} {
    
    set_scan_path wrapper_chain_i_${i}  -complete true -include_elements $sub_wrapper_cells_i($i)  \
    					-scan_data_in $wrp_scan_in($i) \
    					-scan_data_out $wrp_scan_out($i)
    
    set_scan_path wrapper_chain_o_${i}  -complete true -include_elements $sub_wrapper_cells_o($i)   \
    					-scan_data_in $wrp_scan_in($j) \
    					-scan_data_out $wrp_scan_out($j)
    
}

# read ctl models
foreach item $macro_list_ctl { 
  if { [file exists ${item}.ctl] } {
    read_test_model ${item}.ctl
  }
}

#read_test_model /data/foundry/LIB/synopsys/dwc_pcie4phy_sssf5a_x4ns/2.00a_pre4/pma/atpg/13M_4Mx_7Dx_2Iz_LB/ctl/dwc_c20pcie4_pma_x4_ns_scan.ctl
read_test_model -format ctl -design dwc_c20pcie4_pma_x4_ns  /data/foundry/LIB/synopsys/dwc_pcie4phy_sssf5a_x4ns/2.00a_pre4/pma/atpg/13M_4Mx_7Dx_2Iz_LB/ctl/dwc_c20pcie4_pma_x4_ns_scan.ctl
#################################


#exclude Tessent IP from scan chains
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_sib_*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_tdr_*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_edt_*]
set_scan_element false  [get_cells -hier *_tessent_tap_main_inst*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_scan_host_sh_inst*]
set_scan_element false  [get_cells -hier *_bisr_inst*ShiftReg_reg*]
set_scan_element false  [get_cells -hier *_bisr_inst*retime_reg*]
#set_scan_element false  [get_cells -hier *_tessent_occ_*]
set_scan_element false  [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl2_tessent_ssn_receiver_1x_pipe_pi_inst*]
#set_scan_element false  [get_cells  ${AXVAR_DESIGN_NAME}_rtl*_tessent_*_inst]

# dont scan wrapper cells in step1
#set_scan_configuration -exclude_elements [[get_cells -hier tessent_persistent_cell_dwc_dff]


create_test_protocol 

dft_drc


redirect -file ../rpt/${AXVAR_DESIGN_NAME}.dft_drc_pre.rpt {dft_drc -verbose}
redirect -file ../rpt/${AXVAR_DESIGN_NAME}.scan_config.rpt {report_scan_configuration}
redirect -file ../rpt/${AXVAR_DESIGN_NAME}.preview_dft.rpt {preview_dft}

insert_dft

dft_drc

redirect -file ../rpt/${AXVAR_DESIGN_NAME}.dft_drc_post.rpt {dft_drc -verbose}

redirect -file ../rpt/${AXVAR_DESIGN_NAME}.scan_path.rpt {report_scan_path}


####################
if {0} {
proc connect_occ_scan_chain { } {
  set first_occ 1
  set prev_occ ""

  # Iterate using foreach
  foreach_in_collection item [get_cells -hier *_tessent_occ_*] {
    set occ [get_attribute $item -name name]
    
    if {$first_occ} {
        # connect scan_in of the first occ in the chain to scan buf
	puts "connect_pins tessent_occ_scan_buf_i_0/o_z $occ/scan_in"
	disconnect_net [get_pins $occ/scan_in]
	connect_net tessent_occ_scan_buf_i_0/o_z $occ/scan_in
        set first_occ 0
    } else {
        # connect scan_out to scan_in of OCCs in the midle
	puts "connect_pins $prev_occ/scan_out $occ/scan_in"
	disconnect_net [get_pins $occ/scan_in]
	connect_net $prev_occ/scan_out $occ/scan_in
    }
    set prev_occ $occ
  }

  # Connect scan_out of last occ in the chain to the scan buf
  puts "connect_pins $prev_occ/scan_out tessent_occ_scan_buf_o_0/i_a" 
  disconnect_net [get_pins tessent_occ_scan_buf_o_0/i_a]
  connect_net $prev_occ/scan_out tessent_occ_scan_buf_o_0/i_a 

}

#connect_occ_scan_chain

}


#axTclRun "change_names -rules verilog -hierarchy -skip_physical_only_cells -dont_touch [get_ports]"
axTclRun "write_verilog -exclude { pg_objects end_cap_cells well_tap_cells filler_cells pad_spacer_cells physical_only_cells cover_cells flip_chip_pad_cells} -top_module_first -hierarchy design ../results/${AXVAR_DESIGN_NAME}.insert_dft.v"
axTclRun "save_block -as ${AXVAR_DESIGN_NAME}/compile_insert_dft_intest"


puts "AX-DFT-info: Scan insertion script completed ..."
#exit
