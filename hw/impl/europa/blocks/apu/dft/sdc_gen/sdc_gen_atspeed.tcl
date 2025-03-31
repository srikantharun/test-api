##########################################################################################
# Script: sdc_gen_atspeed.tcl
#
# Description: PT script to process DFT constraints for APU.
#              Script is for advanced users only. For more info contact maintainer.
#
#              atspeed mode
#
# Maintainer: <redouan.tahraoui@axelera.ai>
#
##########################################################################################

source ./pt_setup.tcl

if { $CHECK_MANUAL_CHANGES == 0 } {
    source /data/europa/pd/europa/constraints/dev/export/clocks/${DESIGN}_func_port_clocks.tcl

    #source $env(DFT_HOME)/apu/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${DESIGN}_rtl2.dft_inserted_design/${DESIGN}.hierfix.sdc
    source ./${DESIGN}.hierfix.sdc

    #reset signals are static in scan mode
    set_false_path -from [get_ports i_*rst_n]
    set_case_analysis 1 [get_ports test_mode]
    #set_case_analysis 1 [get_pins apu_p_rtl1_tessent_tdr_sri_ctrl_inst/tessent_persistent_cell_ltest_en/u_tc_lib_std_buf/Y]
    
    tessent_set_default_variables

    set_ijtag_retargeting_options -tck_period 10.0

    #Get the name of the clock for i_clk pin from the design
    set i_clk [get_attribute -objects [get_ports i_clk] -name clocks]
    set i_ref_clk [get_attribute -objects [get_ports i_ref_clk] -name clocks]
    set tessent_clock_mapping(i_clk) $i_clk
    set tessent_clock_mapping(i_ref_clk) $i_ref_clk
    set tessent_clock_mapping(tessent_bisr_clock_bisr_clk) bisr_clk
    set tessent_clock_mapping(ts_tck_tck) ijtag_tck

    # apply atspeed exceptions
    tessent_set_ltest_modal_edt_fast_capture
    
    # if partition has memories, read mbist sdc as well
    set tessent_mbist_create_bap_tck_generated_clock 0
    tessent_set_memory_bist_non_modal
    tessent_set_ijtag_non_modal

    #usually these clocks are asynchronous, please check your partition
    set_clock_groups -asynchronous -name clk_1 -group [get_clocks $i_clk] \
						-group  [get_clocks $i_ref_clk] \
						-group  [get_clocks {ijtag_tck}] \
						-group  [get_clocks {ssn_clk}]
    
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}] \
						-group [get_clocks * -filter {full_name != bisr_clk}]
    
    # the following exceptions helps to cleanup timing violations on memories, should be part of PD flow, no need to enable them her, only for debugging.
    #set_case_analysis 1 [get_pins -hier */MCS[*]]
    #set_case_analysis 1 [get_pins -hier */ADME[*]]
    #set_case_analysis 0 [get_pins -hier */PDE]
    #set_false_path  -to [get_pins -hier */RET]
    #set_false_path  -to [get_pins -hier */DFTRAM]


} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsAtspeed.sdc
}

#sanity check of timin    set_case_analysis 1 [get_ports test_mode]
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsAtspeed.sdc

exit
