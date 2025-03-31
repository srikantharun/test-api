##########################################################################################
# Script: sdc_gen_atspeed.tcl
#
# Description: PT script to process DFT constraints for ai_core.
#              Script is for advanced users only. For more info contact maintainer.
#
#              atspeed mode
#
# Maintainer: <tiago.campos@axelera.ai>
#
##########################################################################################


set CHECK_MANUAL_CHANGES 0
set DESIGN ai_core_p
set MEM_IP ${DESIGN}
set GIT_ROOT [exec git rev-parse --show-toplevel]

set DFT_RELEASE "/data/releases/europa/dft/bronze/ai_core/202412111202"
set SI_NETLIST  "/home/projects_2/workspace/amarco/europa091224/hw/impl/europa/blocks/ai_core/dft/atpg/scan_netlist/ai_core_p.insert_dft.v"

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

read_verilog ${SI_NETLIST}

link_design ${DESIGN}

set_app_var sdc_write_unambiguous_names false

if { $CHECK_MANUAL_CHANGES == 0 } {
    source /data/europa/pd/europa/constraints/dev/export/clocks/${DESIGN}_atspeed_port_clocks.tcl
    source ${DFT_RELEASE}/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/ai_core_p_rtl2.dft_inserted_design/ai_core_p.hierfix.sdc

    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0

    #Get the name of the clock for i_clk pin from the design
    set i_clk [get_attribute -objects [get_ports i_clk] -name clocks]
    set i_ref_clk [get_attribute -objects [get_ports i_ref_clk] -name clocks]
    set tck [get_attribute -objects [get_ports tck] -name clocks]

    set tessent_clock_mapping(i_clk) $i_clk
    set tessent_clock_mapping(tessent_bisr_clock_bisr_clk) bisr_clk
    set tessent_clock_mapping(ts_tck_tck) ijtag_tck
    set tessent_slow_clock_period 10
    set BisrCKPeriod 20

    set_clock_groups -asynchronous -name clk_1 -group [get_clocks $i_ref_clk] -group [get_clocks $tck] -group [get_clocks {ssn_clk}] -group [get_clocks $i_clk]
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}]
    # -group [get_clocks {imc_bisr_clk}]
    
    set_false_path -from [get_ports i_*rst_n]
    set_case_analysis 1 [get_ports test_mode]
    
    tessent_set_ltest_modal_edt_fast_capture
    
    # ai_core has no memories, but still have to add ijtag exceptions
    set tessent_mbist_create_bap_tck_generated_clock 0
    #tessent_set_memory_bist_non_modal
    tessent_set_ijtag_non_modal

    #set_case_analysis 0 [get_ports scan_en]
} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsAtspeed.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsAtspeed.sdc

exit
