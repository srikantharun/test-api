##########################################################################################
# Script: sdc_gen_atspeed.tcl
#
# Description: PT script to process DFT constraints for APU_L2C.
#              Script is for advanced users only. For more info contact maintainer.
#
#              atspeed mode
#
# Maintainer: <redouan.tahraoui@axelera.ai>
#
##########################################################################################

source ./pt_setup.tcl

if { $CHECK_MANUAL_CHANGES == 0 } {
    source /data/europa/pd/europa/constraints/dev/export/clocks/${DESIGN}_atspeed_port_clocks.tcl

    #source $env(DFT_HOME)/apu_l2c/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${DESIGN}_rtl2.dft_inserted_design/${DESIGN}.hierfix.sdc
    source ./${DESIGN}.hierfix.sdc

    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0

    #Get the name of the clock for i_clk pin from the design
    set i_clk [get_attribute -objects [get_ports i_clk] -name clocks]
    set i_aclk [get_attribute -objects [get_ports i_aclk] -name clocks]
    set i_l2c_banks_clk [get_attribute -objects [get_ports i_l2c_banks_clk] -name clocks]
    set tessent_clock_mapping(i_clk) $i_clk
    set tessent_clock_mapping(i_aclk) $i_aclk
    set tessent_clock_mapping(i_l2c_banks_clk) $i_l2c_banks_clk
    set tessent_clock_mapping(tessent_bisr_clock_bisr_clk) bisr_clk
    set tessent_clock_mapping(ts_tck_ijtag_tck) ijtag_tck
    
    set_case_analysis 1 [get_ports test_mode]
    set_case_analysis 0 [get_ports scan_en]
    set_case_analysis 0 [get_ports edt_update]
    
    #reset signals are static in scan mode
    set_false_path -from [get_ports i_*rst_n]
    
    tessent_set_ltest_modal_edt_fast_capture
    
    # if partition has memories, read mbist sdc as well
    set tessent_mbist_create_bap_tck_generated_clock 0
    tessent_set_memory_bist_non_modal
    tessent_set_ijtag_non_modal
    
    #usually these clocks are asynchronous, please check your partition
    set_clock_groups -asynchronous -name clk_1 -group [get_clocks $i_clk] -group [get_clocks $i_aclk]  -group [get_clocks $i_l2c_banks_clk]  -group [get_clocks {ijtag_tck}]  -group [get_clocks {test_clk}]
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}]

} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsAtspeed.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsAtspeed.sdc

exit
