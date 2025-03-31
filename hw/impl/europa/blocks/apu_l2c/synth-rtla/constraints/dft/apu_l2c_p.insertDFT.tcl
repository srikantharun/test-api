##########################################################################################
# Script: insert_scan.tcl
#
# Description: updated to match Triton database structure
# Owner:        <redouan_tahraoui@axelera.ai>
#
##########################################################################################


#axTclRun "open_block ../results/${AXVAR_DESIGN_NAME}.ndm:${AXVAR_DESIGN_NAME}/compile_logic_opto.design"

puts "AX-DFT-info: Sourcing scan insertion script dft_script.tcl ..."

source /data/europa/pd/europa/project_setup/dev/memory_macros.tcl

global AXVAR_MACRO_LIST AXVAR_MACRO_DIR

set macro_list_ctl ""

foreach macro $AXVAR_MACRO_LIST {
    set macro_dir [lindex [array get AXVAR_MACRO_DIR $macro] 1]
    append macro_list_ctl "$macro_dir/$macro "

}

# fix to be implemented in rtl
disconnect_net ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_static_clock_control_mode
connect_net [get_nets -of_objects [get_pins ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_mcp_bounding_en]] ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_static_clock_control_mode
######

## -----------------------------------------------------------------------------
## Tool variables.
## -----------------------------------------------------------------------------
#

puts "AX-DFT-info: Sourcing scan insertion script dft_script.tcl ..."

set_app_options -name dft.scan.enable_general_multimode_support -value true

set_app_options -name dft.scan.lockup_latch_prefix -value AXE_DFT_LOCKUP

set_app_options -name dft.test_default_period -value 100
set_app_options -name dft.test_default_delay -value 0
set_app_options -name dft.test_default_strobe -value 40


set_dft_drc_configuration -internal_pins enable
set_scan_configuration -internal_clocks multi
set_scan_configuration -clock_mixing mix_clocks

set_dft_configuration -scan enable

set_dft_signal -type Reset     -active_state 0 -port i_rst_n        -view spec
set_dft_signal -type Reset     -active_state 0 -port i_arst_n  -view spec
#set_dft_signal -type Reset     -active_state 0 -port ijtag_reset  -view spec
#set_dft_signal -type Reset     -active_state 0 -port bisr_reset   -view spec

#set_dft_signal -type Reset     -active_state 0  -hookup_pin u_ax65_l2_wrapper/u_ax65_l2_top/u_l2_logic/u_mem/gen_mem_rst_sync.u_mem_rst_sync/u_seq_sync/gen_stages_3.gen_rst_val_0.u_tc_lib_seq_sync/Q

set_dft_signal -type ScanClock -port i_clk     -timing {45 55}    -view spec
set_dft_signal -type ScanClock -port i_clk     -timing {45 55}    -view exist

set_dft_signal -type ScanClock -port i_aclk     -timing {45 55}    -view spec
set_dft_signal -type ScanClock -port i_aclk     -timing {45 55}    -view exist

set_dft_signal -type ScanClock -port i_l2c_banks_clk -timing {45 55}    -view spec
set_dft_signal -type ScanClock -port i_l2c_banks_clk -timing {45 55}    -view exist


set_dft_signal -type ScanClock -hook ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/tessent_persistent_cell_occ_clock_gate/u_tc_lib_clk_en/ECK     -timing {45 55}    -view exist
set_dft_signal -type ScanClock -hook ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/tessent_persistent_cell_occ_clock_gate/u_tc_lib_clk_en/ECK     -timing {45 55}    -view spec

set_dft_signal -type ScanClock -hook tessent_persistent_cell_shift_capture_clock/u_tc_lib_clk_en/ECK -timing {45 55} -view spec
set_dft_signal -type ScanClock -hook tessent_persistent_cell_shift_capture_clock/u_tc_lib_clk_en/ECK -timing {45 55} -view exist

set_dft_signal -type ScanEnable  -port scan_en -view spec 
set_dft_signal -type ScanEnable  -port scan_en -view exist 
#set_dft_signal -type ScanEnable  -port i_scan_enable -view spec 
#set_dft_signal -type ScanEnable  -port i_scan_enable -view exist 

set_dft_signal -type TestMode  -active_state 1 -port test_mode     -view spec
set_dft_signal -type TestMode  -active_state 1 -port test_mode     -view existing_dft

#set_dft_signal -type TestMode  -active_state 1 -port test_mode -view spec -hookup_pin ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_to_en

set_dft_signal -type Constant  -active_state 0 -port edt_update    -view exist 
set_dft_signal -type Constant  -active_state 0 -port ijtag_sel     -view exist 
set_dft_signal -type Constant  -active_state 0 -port ijtag_ue      -view exist 
#set_dft_signal -type Constant  -active_state 1 -port bisr_shift_en -view exist

set_dft_signal -type Constant  -active_state 0  -view spec -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/async_set_reset_static_disable
set_dft_signal -type Constant  -active_state 0  -view spec -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/control_test_point_en
set_dft_signal -type Constant  -active_state 0  -view spec -hookup_pin ${AXVAR_DESIGN_NAME}_rtl2_tessent_tdr_sri_ctrl_inst/observe_test_point_en

#foreach_in_collection pin [get_pins tessent_scan_buf_i_*/o_z] {
foreach_in_collection pin [get_pins tessent_scan_buf_i_*/u_tc_lib_std_buf/Y] {
    set pin_name [get_object_name $pin] 
    set_dft_signal -type ScanDataIn  -hookup_pin  $pin_name -view spec
}

#foreach_in_collection pin [get_pins tessent_scan_buf_o_*/i_a] {
foreach_in_collection pin [get_pins tessent_scan_buf_o_*/u_tc_lib_std_buf/A] {
    set pin_name [get_object_name $pin] 
    set_dft_signal -type ScanDataOut  -hookup_pin  $pin_name -view spec
}

set scan_grp_cmd "set_scan_group sib_sti_occ  -include_elements { \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_to_sel_reg \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_so_retiming_reg \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_ce_se_ue_reg[1] \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_ce_se_ue_reg[0] \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_to_si_reg \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/retiming_ltest_to_si_reg \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_to_reset_reg \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/occ_ctrl_reg[0] \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/occ_ctrl_so_retimed_reg \
			${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/occ_ctrl_reg[1]} \
  		-serial_routed true \
  		-access {ScanDataIn ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_si \
			 ScanDataOut ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_so \
			 ScanEnable ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_scan_en}"                                                                                                   

eval $scan_grp_cmd

#exclude Tessent IP from scan chains
set_scan_element false [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_sib_*]
set_scan_element false [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_tdr_*]
set_scan_element false [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_edt_*]
set_scan_element false [get_cells -hier *_bisr_inst*ShiftReg_reg*]
set_scan_element false [get_cells -hier *_bisr_inst*retime_reg*]


# read ctl models
foreach item $macro_list_ctl { 
  if { [file exists ${item}.ctl] } {
    read_test_model ${item}.ctl
  }
}

create_test_protocol 

dft_drc

redirect -file ../rpt/${AXVAR_DESIGN_NAME}.dft_drc_pre.rpt {dft_drc -verbose}
redirect -file ../rpt/${AXVAR_DESIGN_NAME}.scan_config.rpt {report_scan_configuration}
redirect -file ../rpt/${AXVAR_DESIGN_NAME}.preview_dft_summary.rpt {preview_dft}

insert_dft

dft_drc

redirect -file ../rpt/${AXVAR_DESIGN_NAME}.dft_drc_post.rpt {dft_drc}

redirect -file ../rpt/${AXVAR_DESIGN_NAME}.scan_path.rpt {report_scan_path}

#axTclRun "change_names -rules verilog -hierarchy -skip_physical_only_cells -dont_touch [get_ports]"
axTclRun "write_verilog -exclude { pg_objects end_cap_cells well_tap_cells filler_cells pad_spacer_cells physical_only_cells cover_cells flip_chip_pad_cells} -top_module_first -hierarchy design ../results/${AXVAR_DESIGN_NAME}.insert_dft.v"
axTclRun "save_block -as ${AXVAR_DESIGN_NAME}/compile_insert_dft"

puts "AX-DFT-info: Scan insertion script completed ..."
