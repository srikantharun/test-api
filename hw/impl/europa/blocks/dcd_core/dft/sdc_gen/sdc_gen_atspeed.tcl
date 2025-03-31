##########################################################################################
# Script: sdc_gen_atspeed.tcl
#
# Description: PT script to process DFT constraints for DCD_CORE.
#              Script is for advanced users only. For more info contact maintainer.
#
#              atspeed mode
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
    #source /data/europa/pd/europa/constraints/dev/export/clocks/${DESIGN}_atspeed_port_clocks.tcl

create_clock -add -name codec_clk -period 0.833 -waveform {0 0.4165} [get_ports "clk"]
create_clock -add -name ijtag_tck -period 10.000 -waveform {0 5.0000} [get_ports "ijtag_tck"]
create_clock -add -name test_clk -period 10.000 -waveform {0 5.0000} [get_ports "test_clk"]
create_clock -add -name bisr_clk -period 20.000 -waveform {0 10.0000} [get_ports "bisr_clk"]

    #usually these clocks are asynchronous, please check your partition
    set_clock_groups -asynchronous -name clk_1 -group [get_clocks {codec_clk}] -group [get_clocks {ijtag_tck}] -group [get_clocks {test_clk}]
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}]

    #reset signals are static in scan mode
    set_false_path -from [get_ports rstn]
    

    source /data/releases/europa/dft/bronze/dcd_core/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/alg_core_wrapper_rtl2.dft_inserted_design/alg_core_wrapper.hierfix.sdc

    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0

    #Get the name of the clock for i_clk pin from the design
    #set i_clk [get_attribute -objects [get_ports i_clk] -name clocks]
    #set tessent_clock_mapping(i_clk) $i_clk
    set tessent_clock_mapping(clk) codec_clk
    set tessent_clock_mapping(tessent_bisr_clock_bisr_clk) bisr_clk
    set tessent_clock_mapping(ts_tck_ijtag_tck) ijtag_tck

    set_case_analysis 1 [get_ports test_mode]
    set_case_analysis 0 [get_ports scan_en]
    set_case_analysis 0 [get_ports edt_update]
    
    tessent_set_ltest_modal_edt_fast_capture
    
    # if partition has memories, read mbist sdc as well
    set tessent_mbist_create_bap_tck_generated_clock 0
    tessent_set_memory_bist_non_modal
    tessent_set_ijtag_non_modal

} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsAtspeed.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsAtspeed.sdc

exit
