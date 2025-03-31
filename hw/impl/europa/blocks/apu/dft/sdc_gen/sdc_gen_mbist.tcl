##########################################################################################
# Script: sdc_gen_mbist.tcl
#
# Description: PT script to process DFT constraints for APU.
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
    remove_clock ssn_clk

    #source $env(DFT_HOME)/apu/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${DESIGN}_rtl2.dft_inserted_design/${DESIGN}.hierfix.sdc
    source ./${DESIGN}.hierfix.sdc

    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0

    #Get the name of the clock for i_clk pin from the design
    set i_clk [get_attribute -objects [get_ports i_clk] -name clocks]
    set i_ref_clk [get_attribute -objects [get_ports i_ref_clk] -name clocks]
    set tessent_clock_mapping(i_clk) $i_clk
    set tessent_clock_mapping(i_ref_clk) $i_ref_clk
    set tessent_clock_mapping(tessent_bisr_clock_bisr_clk) bisr_clk
    set tessent_clock_mapping(ts_tck_tck) ijtag_tck
    set tessent_slow_clock_period 10
    set BisrCKPeriod 20

    
    #tessent_set_memory_bist_non_modal
    tessent_set_non_modal off ;# logictest off/on , disable scan logic

    # the following exceptions helps to cleanup timing violations on memories, should be part of PD flow, no need to enable them her, only for debugging.
    #set_case_analysis 1 [get_pins -hier */MCS[*]]
    #set_case_analysis 1 [get_pins -hier */ADME[*]]
    #set_case_analysis 0 [get_pins -hier */PDE]
    #set_false_path  -to [get_pins -hier */RET]
    #set_false_path  -to [get_pins -hier */DFTRAM]

} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsMbist.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsMbist.sdc

exit
