##########################################################################################
# Script: sdc_gen_shift.tcl
#
# Description: PT script to process DFT constraints for APU.
#              Script is for advanced users only. For more info contact maintainer.
#
#              shift mode
#
# Maintainer: <redouan.tahraoui@axelera.ai>
#
##########################################################################################

source ./pt_setup.tcl

if { $CHECK_MANUAL_CHANGES == 0 } {

    source /data/europa/pd/europa/constraints/dev/export/clocks/${DESIGN}_shift_port_clocks.tcl
        
    #source $env(DFT_HOME)/apu/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${DESIGN}_rtl2.dft_inserted_design/${DESIGN}.hierfix.sdc
    source ${DESIGN}.hierfix.sdc
    
    #call the proper TCL procs for scan shift mode
    
    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0
    set tessent_slow_clock_period 10
    
    #Get the name of the clock for i_clk pin from the design
    set i_clk [get_attribute -objects [get_ports i_clk] -name clocks]
    set i_ref_clk [get_attribute -objects [get_ports i_ref_clk] -name clocks]
    set tessent_clock_mapping(i_clk) $i_clk
    set tessent_clock_mapping(i_ref_clk) $i_ref_clk
    set tessent_clock_mapping(tessent_bisr_clock_bisr_clk) bisr_clk
    set tessent_clock_mapping(ts_tck_tck) ijtag_tck
    
    tessent_set_ltest_modal_shift

    set_clock_groups -asynchronous -name clk_1 -group [get_clocks {ssn_clk}] -group [get_clocks {ijtag_tck}]
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}] -group [get_clocks $i_clk]
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}] -group [get_clocks $i_ref_clk]
    
    #add case analysis on scan shift and test mode
    set_case_analysis 1 [get_ports test_mode]
    set_case_analysis 1 ${DESIGN}_rtl2_tessent_ssn_scan_host_sh_inst/tessent_persistent_cell_scan_en_buf/u_tc_lib_std_buf/Y
    #set_case_analysis 1 [get_pins apu_p_rtl1_tessent_tdr_sri_ctrl_inst/tessent_persistent_cell_ltest_en/u_tc_lib_std_buf/Y]
    
    # force occ clk mux selector to 1
    set_case_analysis 1 [get_pins -hier *test_mode_reg/Q]
    
    # the following exceptions helps to cleanup timing violations on memories, should be part of PD flow, no need to enable them her, only for debugging.
    #set_case_analysis 1 [get_pins -hier */MCS[*]]
    #set_case_analysis 1 [get_pins -hier */ADME[*]]
    #set_case_analysis 0 [get_pins -hier */PDE]
    #set_false_path  -to [get_pins -hier */RET]
    #set_false_path  -to [get_pins -hier */DFTRAM]

} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsShift.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsShift.sdc

exit
