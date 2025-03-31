##########################################################################################
# Script: sdc_gen_shift.tcl
#
# Description: PT script to process DFT constraints for DCD_CORE.
#              Script is for advanced users only. For more info contact maintainer.
#
#              shift mode
#
# Maintainer: <leonidas.katselas@axelera.ai>
#
##########################################################################################

set CHECK_MANUAL_CHANGES 0
set DESIGN alg_core_wrapper
set MEM_IP ${DESIGN}
set GIT_ROOT [exec git rev-parse --show-toplevel]
source ${GIT_ROOT}/hw/ip/tech_cell_library/default/rtl/sf5a/tc_mbist_techlib.tcl

set glob_paths {}
foreach mem_lib [split $MEM_LIBS_PATH$REG_FILES_PATH " "] {
    if { $mem_lib == "" } {
        # Trailing whitespace, skip
        continue
    }
    lappend glob_paths "${mem_lib}/fusion_ref_library/*"
}
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*c54/*/FE-Common/LIBERTY/*/*c54l08_tt_nominal_max_0p7500v_125c.db_ccs_tn_lvf"
set link_paths {}
foreach glob_path $glob_paths {
    lappend link_paths [glob $glob_path]
}

set_app_var link_path "* [join $link_paths]"

read_verilog /data/europa/pd/alg_core_wrapper/block_build/dev_bronze5_run2/build/fc/compile/results/alg_core_wrapper.insert_dft.v.gz

link_design ${DESIGN}

set_app_var sdc_write_unambiguous_names false

if { $CHECK_MANUAL_CHANGES == 0 } {
    #source /data/europa/pd/europa/constraints/dev/export/clocks/${DESIGN}_shift_port_clocks.tcl
    #test_clk will be defined by tessent sdc
    #remove_clock test_clk
create_clock -add -name codec_clk -period 10.000 -waveform {0 5.0000} [get_ports "clk"]
create_clock -add -name ijtag_tck -period 10.000 -waveform {0 5.0000} [get_ports "ijtag_tck"]
create_clock -add -name test_clk -period 10.000 -waveform {0 5.0000} [get_ports "test_clk"]
create_clock -add -name bisr_clk -period 20.000 -waveform {0 10.0000} [get_ports "bisr_clk"]

    source /data/releases/europa/dft/bronze/dcd_core/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/alg_core_wrapper_rtl2.dft_inserted_design/alg_core_wrapper.hierfix.sdc

    #call the proper TCL procs for scan shift mode

    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0
    set tessent_slow_clock_period 10
    
    tessent_set_ltest_modal_shift

    set_clock_groups -asynchronous -name clk_1 -group [get_clocks {tessent_test_clock codec_clk}] -group [get_clocks {ijtag_tck}]
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}]
    
    #add case analysis on scan shift and test mode
    set_case_analysis 1 [get_ports test_mode]
    set_case_analysis 1 [get_ports scan_en]

} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsAtspeed.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsAtspeed.sdc

exit
