##########################################################################################
# Script: l2_p.insertDFT.tcl
#
# Description: PD FC script to stitch scan chains.
#              Run in compile step, after logic_opto.
#
# Maintainer:        <leonidas.katselas@axelera.ai>
#
##########################################################################################


#axTclRun "open_block ../results/${AXVAR_DESIGN_NAME}.ndm:${AXVAR_DESIGN_NAME}/compile_logic_opto.design"
redirect -file ../rpt/${AXVAR_DESIGN_NAME}.scan_config_pre.rpt {report_scan_configuration}

axTclMsg info "AX-DFT-info: Sourcing scan insertion script ..."

source /data/europa/pd/europa/project_setup/dev/memory_macros.tcl

## -----------------------------------------------------------------------------
## Tool variables.
## -----------------------------------------------------------------------------

# Nonscannable macros
set NONSCAN_MACRO_LIST {esd_lib cdmm}
# Scannable macros (to be calculated)
set AXVAR_MACRO_CTL_LIST {}

# Build the scannable macro list
foreach macro $AXVAR_MACRO_LIST {
    if {[lsearch -exact $NONSCAN_MACRO_LIST $macro] == -1 } {
        append AXVAR_MACRO_CTL_LIST "$AXVAR_MACRO_DIR($macro)/$macro.ctl "
    }
}


set_app_options -name dft.scan.enable_general_multimode_support -value true
set_app_options -name dft.scan.lockup_latch_prefix -value AXE_DFT_LOCKUP

set_app_options -name dft.test_default_period -value 100
set_app_options -name dft.test_default_delay -value 0
set_app_options -name dft.test_default_strobe -value 40


set_dft_drc_configuration -internal_pins enable
set_scan_configuration -internal_clocks multi

set_scan_configuration -clock_mixing mix_clocks

set_dft_configuration -scan enable

# Resets
set_dft_signal -type Reset -active_state 0 -port i_ao_rst_n -view spec
set_dft_signal -type Reset -active_state 0 -port i_ao_rst_n -view exist
set_dft_signal -type Reset -active_state 0 -port i_global_rst_n -view spec
set_dft_signal -type Reset -active_state 0 -port i_global_rst_n -view exist
set_dft_signal -type Reset -active_state 0 -hook ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/tessent_persistent_cell_ltest_reset_mux/u_tc_lib_std_mux/Y -view spec
set_dft_signal -type Reset -active_state 0 -hook ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/tessent_persistent_cell_ltest_reset_mux/u_tc_lib_std_mux/Y -view exist
# Clocks
set_dft_signal -type ScanClock -port i_clk -timing {45 55} -view spec
set_dft_signal -type ScanClock -port i_clk -timing {45 55} -view exist
set_dft_signal -type ScanClock -hook tessent_persistent_cell_shift_capture_clock/u_tc_lib_clk_en/ECK -timing {45 55} -view spec
set_dft_signal -type ScanClock -hook tessent_persistent_cell_shift_capture_clock/u_tc_lib_clk_en/ECK -timing {45 55} -view exist
set_dft_signal -type ScanClock -hook ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/tessent_persistent_cell_occ_clock_gate/u_tc_lib_clk_en/ECK -timing {45 55} -view spec
set_dft_signal -type ScanClock -hook ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/tessent_persistent_cell_occ_clock_gate/u_tc_lib_clk_en/ECK -timing {45 55} -view exist
# Scan Enable
set_dft_signal -type ScanEnable -port scan_en -view spec
set_dft_signal -type ScanEnable -port scan_en -view exist
# Test Mode
set_dft_signal -type TestMode -active_state 1 -port test_mode -view spec
set_dft_signal -type TestMode -active_state 1 -port test_mode -view exist
# Constant Port
set_dft_signal -type Constant -active_state 0 -port edt_update -view exist
set_dft_signal -type Constant -active_state 1 -hookup ${AXVAR_DESIGN_NAME}_rtl1_tessent_sib_sti_inst/ltest_to_en -view exist

# Scan chain data hookups
foreach_in_collection pin [get_pins tessent_scan_buf_i_*/u_tc_lib_std_buf/Y] {
    set pin_name [get_object_name $pin]
    set_dft_signal -type ScanDataIn  -hookup_pin  $pin_name -view spec
}

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

# Exclude Tessent IP from scan chains
set_scan_element false [get_cells -hier ${AXVAR_DESIGN_NAME}_rtl*_tessent_sib_*]
set_scan_element false [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_tdr_*]
set_scan_element false [get_cells -hier ${AXVAR_DESIGN_NAME}_*_tessent_edt_*]
set_scan_element false [get_cells -hier *_bisr_inst]
set_scan_element false [get_cells -hier *_tessent_tap_main_inst*]

foreach macro_ctl $AXVAR_MACRO_CTL_LIST {
    read_test_model $macro_ctl
}

# Insert DFT

create_test_protocol

dft_drc

redirect -file ../rpt/${AXVAR_DESIGN_NAME}.dft_drc_pre.rpt {dft_drc -verbose}
redirect -file ../rpt/${AXVAR_DESIGN_NAME}.scan_config.rpt {report_scan_configuration}
redirect -file ../rpt/${AXVAR_DESIGN_NAME}.preview_dft_summary.rpt {preview_dft}

insert_dft

redirect -file ../rpt/${AXVAR_DESIGN_NAME}.dft_drc_post.rpt {dft_drc -verbose}
redirect -file ../rpt/${AXVAR_DESIGN_NAME}.scan_path.rpt {report_scan_path}

axTclRun "write_verilog -exclude { pg_objects end_cap_cells well_tap_cells filler_cells pad_spacer_cells physical_only_cells cover_cells flip_chip_pad_cells} -top_module_first -hierarchy design ../results/${AXVAR_DESIGN_NAME}.insert_dft.v"
axTclRun "save_block -as ${AXVAR_DESIGN_NAME}/compile_insert_dft"

axTclMsg info "AX-DFT-info: Scan insertion script completed ..."
