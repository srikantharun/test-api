##########################################################################################
# Script: sdc_gen_mbist.tcl
#
# Description: PT script to process DFT constraints for APU_L2C.
#              Script is for advanced users only. For more info contact maintainer.
#
#              mbist mode
#
# Maintainer: <redouan.tahraoui@axelera.ai>
#
##########################################################################################

source ./pt_setup.tcl

if { $CHECK_MANUAL_CHANGES == 0 } {
    source /data/europa/pd/europa/constraints/dev/export/clocks/${DESIGN}_func_port_clocks.tcl
    #test_clk will be defined by tessent sdc
    remove_clock test_clk

    source $env(DFT_HOME)/apu_l2c/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${DESIGN}_rtl2.dft_inserted_design/${DESIGN}.hierfix.sdc
    
    set_case_analysis 0 [get_ports test_mode]
    set_case_analysis 0 [get_ports scan_en]

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
    set tessent_slow_clock_period 10
    set BisrCKPeriod 20

    tessent_set_non_modal off ;# logictest off/on , disable scan logic

} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsMbist.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsMbist.sdc

exit
