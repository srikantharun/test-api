##########################################################################################
# Script: sdc_gen_shift.tcl
#
# Description: PT script to process DFT constraints for SOC_PERIPH.
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
    
    #test_clk will be defined by tessent sdc
    remove_clock test_clk
    
    source $env(DFT_HOME)/soc_periph/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${DESIGN}_rtl2.dft_inserted_design/${DESIGN}.hierfix.sdc
    
    #call the proper TCL procs for scan shift mode
    
    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0
    set tessent_slow_clock_period 10
    

    #Get the name of the clock for i_clk pin from the design
    set ijtag_tck [get_attribute -objects [get_ports tck] -name clocks]
    set i_emmc_clk [get_attribute -objects [get_ports i_emmc_clk] -name clocks]
    set i_periph_clk [get_attribute -objects [get_ports i_periph_clk] -name clocks]
    #set i_spi_clk_in [get_attribute -objects [get_ports i_spi_clk_in] -name clocks]
    set test_clk [get_attribute -objects [get_ports test_clk] -name clocks]

    set tessent_clock_mapping(ijtag_tck) $ijtag_tck
    set tessent_clock_mapping(i_emmc_clk) $i_emmc_clk
    set tessent_clock_mapping(i_periph_clk) $i_periph_clk
    set tessent_clock_mapping(tessent_test_clock) $test_clk
    set tessent_clock_mapping(tessent_bisr_clock_bisr_clk) bisr_clk
    set tessent_clock_mapping(ts_tck_tck) ijtag_tck


    tessent_set_ltest_modal_shift

    set_clock_groups -asynchronous -name clk_1 -group [get_clocks {tessent_test_clock emmc_clk periph_clk}] -group [get_clocks ijtag_tck]
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}]

    #add case analysis on scan shift and test mode
    set_case_analysis 1 [get_ports test_mode]
    set_case_analysis 1 [get_ports scan_en]
} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsShift.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsShift.sdc

exit
